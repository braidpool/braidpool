"""Print logs from a Braidpool functional test temp directory."""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Iterator

from test_framework.constants import LOG_NAMES


def iter_logs(root: Path) -> Iterator[Path]:
    for path in sorted(root.rglob("*")):
        if path.is_file() and path.name in LOG_NAMES:
            yield path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tmpdir", type=Path, help="Functional test temp directory")
    args = parser.parse_args()

    if not args.tmpdir.exists():
        parser.error(f"{args.tmpdir} does not exist")

    for path in iter_logs(args.tmpdir):
        print(f"\n===== {path.relative_to(args.tmpdir)} =====")
        try:
            print(path.read_text(encoding="utf8", errors="replace"), end="")
        except OSError as exc:
            print(f"<failed to read {path}: {exc}>")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

