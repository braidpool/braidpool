#!/bin/bash
#
# Build the cpuminer CPU miner (`minerd`) used as a downstream mining device
# for the node's Stratum port on mainnet, testnet4 and signet.
#
# The built binary is printed at the end: <CPUMINER_DIR>/minerd

set -euo pipefail

REPO_URL="https://github.com/pooler/cpuminer.git"
# Pinned to a commit instead of the v2.5.1 tag. v2.5.1 predates upstream's
# "Fix build on Aarch64" (5f02105) and does not link on Apple Silicon unless it
# is configured with --disable-assembly.
CPUMINER_REF="${CPUMINER_REF:-5f02105940edb61144c09a7eb960bba04a10d5b7}"
CONFIGURE_ARGS="${CONFIGURE_ARGS:-}"
REBUILD="${REBUILD:-0}"
REQUIRED_TOOLS=(git automake autoconf make perl cc curl-config)
# Records what the current minerd was built from. It lives in the checkout and
# is excluded from `git clean`.
STAMP_NAME=".built-ref"

log() {
  printf '==> %s\n' "$*"
}

die() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

# Resolve a path to an absolute one. The path itself may not exist yet, so its
# parent directory is created and resolved and the basename is appended.
absolute_path() {
  local path="$1" parent base
  while [ "${#path}" -gt 1 ] && [ "${path%/}" != "$path" ]; do
    path="${path%/}"
  done
  base="$(basename "$path")"
  parent="$(dirname "$path")"
  mkdir -p "$parent"
  parent="$(cd "$parent" && pwd)"
  if [ "$parent" = "/" ]; then
    printf '/%s' "$base"
  else
    printf '%s/%s' "$parent" "$base"
  fi
}

# Print the tools from REQUIRED_TOOLS that are not on PATH.
missing_tools() {
  local missing=() tool
  for tool in "${REQUIRED_TOOLS[@]}"; do
    if ! command -v "$tool" >/dev/null 2>&1; then
      missing+=("$tool")
    fi
  done
  # Expanding an empty array fails under `set -u` in bash 3.2 (macOS).
  if [ "${#missing[@]}" -gt 0 ]; then
    printf '%s' "${missing[*]}"
  fi
}

unsupported_system() {
  die "$1
Install these yourself, then run this script again: ${REQUIRED_TOOLS[*]}
(curl-config comes with the libcurl development package.)"
}

as_root() {
  if [ "$(id -u)" -eq 0 ]; then
    "$@"
  else
    sudo "$@"
  fi
}

install_dependencies_linux() {
  local missing
  missing="$(missing_tools)"
  if [ -z "$missing" ]; then
    log "Build tools already installed, skipping package installation"
    return
  fi
  log "Missing build tools: $missing"

  if ! command -v apt-get >/dev/null 2>&1; then
    unsupported_system "No supported package manager found (only apt is handled)."
  fi
  if [ "$(id -u)" -ne 0 ] && ! command -v sudo >/dev/null 2>&1; then
    die "sudo is required to install packages. Run as root or install sudo."
  fi

  log "Installing build dependencies with apt"
  # `env` runs as root, so the variable is set even if sudoers resets the
  # environment.
  as_root env DEBIAN_FRONTEND=noninteractive apt-get update
  as_root env DEBIAN_FRONTEND=noninteractive apt-get install -y \
    git automake autoconf build-essential libcurl4-openssl-dev
}

# Homebrew's curl is keg-only. It is the only place libcurl.m4 is installed,
# which cpuminer's configure.ac needs (LIBCURL_CHECK_CONFIG). The build links
# against Apple's libcurl.
macos_aclocal_dir() {
  printf '%s/share/aclocal' "$(brew --prefix curl)"
}

install_dependencies_macos() {
  if ! xcode-select -p >/dev/null 2>&1; then
    die "Xcode command line tools are required. Run: xcode-select --install"
  fi
  # Apple ships git, make, perl, cc and libcurl with the command line tools.
  # automake, autoconf and libcurl.m4 come from Homebrew.
  command -v brew >/dev/null 2>&1 || die "Homebrew is required to install automake, autoconf and curl. See https://brew.sh"

  local packages="" tool
  for tool in automake autoconf; do
    if ! command -v "$tool" >/dev/null 2>&1; then
      packages="$packages $tool"
    fi
  done
  if [ ! -f "$(macos_aclocal_dir)/libcurl.m4" ]; then
    packages="$packages curl"
  fi

  if [ -z "$packages" ]; then
    log "Build tools already installed, skipping package installation"
    return
  fi
  log "Installing build dependencies with Homebrew:$packages"
  # shellcheck disable=SC2086 # intentional word splitting of the package list
  brew install $packages
}

install_dependencies() {
  case "$(uname -s)" in
    Linux) install_dependencies_linux ;;
    Darwin) install_dependencies_macos ;;
    *)
      if [ -n "$(missing_tools)" ]; then
        unsupported_system "Unsupported system: $(uname -s). Missing: $(missing_tools)."
      fi
      ;;
  esac

  if [ -n "$(missing_tools)" ]; then
    die "Still missing after installation: $(missing_tools)"
  fi
}

# nomacro.pl rewrites the .S assembly files in place for assemblers that do not
# support macros. Only macOS and Clang need it; on Linux with GCC it would only
# dirty the checkout.
needs_nomacro() {
  local version
  if [ "$(uname -s)" = "Darwin" ]; then
    return 0
  fi
  version="$(cc --version 2>/dev/null || true)"
  case "$version" in
    *[Cc]lang*) return 0 ;;
  esac
  return 1
}

# Clone if needed, then put the checkout on exactly CPUMINER_REF with no local
# changes (for example the rewritten .S files nomacro.pl leaves behind).
prepare_checkout() {
  local origin
  if [ -d "$CPUMINER_DIR/.git" ]; then
    origin="$(git -C "$CPUMINER_DIR" remote get-url origin 2>/dev/null || true)"
    if [ "${origin%.git}" != "${REPO_URL%.git}" ]; then
      die "$CPUMINER_DIR is a git checkout of '${origin:-no origin}', not $REPO_URL. Refusing to reset it. Remove it or set CPUMINER_DIR."
    fi
    log "Using existing checkout in $CPUMINER_DIR"
  elif [ -e "$CPUMINER_DIR" ]; then
    die "$CPUMINER_DIR exists but is not a cpuminer checkout. Remove it or set CPUMINER_DIR."
  else
    log "Cloning cpuminer into $CPUMINER_DIR"
    git clone --quiet "$REPO_URL" "$CPUMINER_DIR"
  fi

  # Keep the stamp file out of `git status` without touching tracked files.
  local exclude_file="$CPUMINER_DIR/.git/info/exclude"
  mkdir -p "$(dirname "$exclude_file")"
  if ! grep -qxF "$STAMP_NAME" "$exclude_file" 2>/dev/null; then
    printf '%s\n' "$STAMP_NAME" >>"$exclude_file"
  fi

  git -C "$CPUMINER_DIR" fetch --tags --quiet origin
  git -C "$CPUMINER_DIR" reset --hard --quiet
  git -C "$CPUMINER_DIR" clean -fdq -e "$STAMP_NAME"
  if ! git -C "$CPUMINER_DIR" checkout --quiet "$CPUMINER_REF"; then
    die "Cannot check out CPUMINER_REF '$CPUMINER_REF'. Use a tag or commit that exists in $REPO_URL."
  fi
}

# Runs in $CPUMINER_DIR. Every step returns on failure explicitly, because
# `set -e` does not apply inside a function that is called from an `if`.
run_build() {
  local configure_args=() jobs
  read -r -a configure_args <<<"$CONFIGURE_ARGS"
  jobs="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 2)"

  if [ "$(uname -s)" = "Darwin" ]; then
    # autogen.sh calls a bare `aclocal`, which honors ACLOCAL_PATH.
    local aclocal_dir
    aclocal_dir="$(macos_aclocal_dir)" || return 1
    export ACLOCAL_PATH="$aclocal_dir${ACLOCAL_PATH:+:$ACLOCAL_PATH}"
  fi

  ./autogen.sh || return 1
  if needs_nomacro; then
    ./nomacro.pl || return 1
  fi
  # ${arr[@]+...} keeps an empty array valid under `set -u` in bash 3.2.
  ./configure CFLAGS="-O3" ${configure_args[@]+"${configure_args[@]}"} || return 1
  make -j"$jobs" || return 1
}

build_failed() {
  if [ "$(uname -s)" = "Darwin" ]; then
    die "The cpuminer build failed. On Apple Silicon (arm64) the assembly routines may not build; try again with CONFIGURE_ARGS=--disable-assembly. Otherwise see the output above."
  fi
  die "The cpuminer build failed. See the output above."
}

build_cpuminer() {
  local resolved_ref stamp stamp_file
  prepare_checkout

  resolved_ref="$(git -C "$CPUMINER_DIR" rev-parse HEAD)"
  stamp="$resolved_ref|$CONFIGURE_ARGS"
  stamp_file="$CPUMINER_DIR/$STAMP_NAME"

  if [ "$REBUILD" != "1" ] && [ -x "$CPUMINER_DIR/minerd" ] && [ -f "$stamp_file" ] \
    && [ "$(cat "$stamp_file")" = "$stamp" ]; then
    log "minerd is already built from $resolved_ref, skipping the build (use --rebuild to build again)"
    return
  fi

  log "Building cpuminer $resolved_ref"
  rm -f "$stamp_file"
  # Drop build products of any earlier ref or configure arguments.
  git -C "$CPUMINER_DIR" clean -fdxq -e "$STAMP_NAME"
  if ! (cd "$CPUMINER_DIR" && run_build); then
    build_failed
  fi
  printf '%s\n' "$stamp" >"$stamp_file"
}

for arg in "$@"; do
  case "$arg" in
    --rebuild) REBUILD=1 ;;
    *) die "Unknown argument: $arg (the only option is --rebuild)" ;;
  esac
done

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CPUMINER_DIR="$(absolute_path "${CPUMINER_DIR:-$SCRIPT_DIR/cpuminer}")"

install_dependencies
build_cpuminer

log "Built: $CPUMINER_DIR/minerd"
log "Run it against the node's Stratum port, for example:"
log "  $CPUMINER_DIR/minerd -a sha256d -o stratum+tcp://127.0.0.1:3333 -u <MAINNET_ADDRESS>.worker1 -p x -t 1"
log "The node reads the username as a mainnet payout address and rejects shares from any other value."
log "Add -D -P to that command when debugging the Stratum handshake."
