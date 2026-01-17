# .github/scripts/save-review.sh
# Saves and validates an AI review JSON file
#
# Usage: echo '{"branch":...}' | .github/scripts/save-review.sh
#    or: .github/scripts/save-review.sh < review.json
#
# The script:
# 1. Reads JSON from stdin
# 2. Validates against schema
# 3. Checks workflow version compatibility
# 4. Saves to .reviews/<branch>-<persona>-<timestamp>.json
# 5. Exits 0 on success, 1 on validation failure
#
# Note: Date/time is derived from system clock, not from JSON

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
REVIEWS_DIR="$REPO_ROOT/.reviews"
VALIDATOR="$SCRIPT_DIR/validate-review.py"
VERSION_FILE="$SCRIPT_DIR/../WORKFLOW_VERSION"

# Source common functions
source "$SCRIPT_DIR/common.sh"

# Read current version from single source of truth
if [ -f "$VERSION_FILE" ]; then
    CURRENT_VERSION=$(cat "$VERSION_FILE")
else
    CURRENT_VERSION="1.0"
fi

# Read JSON from stdin
JSON=$(cat)

if [ -z "$JSON" ]; then
    echo "Error: No JSON provided on stdin" >&2
    exit 1
fi

# Check workflow version
REVIEW_VERSION=$(echo "$JSON" | jq -r '.workflow_version // empty')
if [ -n "$REVIEW_VERSION" ]; then
    REVIEW_MAJOR=$(echo "$REVIEW_VERSION" | cut -d. -f1)
    CURRENT_MAJOR=$(echo "$CURRENT_VERSION" | cut -d. -f1)
    if [ "$REVIEW_MAJOR" != "$CURRENT_MAJOR" ]; then
        echo "Error: Review workflow version $REVIEW_VERSION incompatible with current $CURRENT_VERSION" >&2
        exit 1
    fi
fi

# Extract required fields for filename
BRANCH=$(echo "$JSON" | jq -r '.branch // empty')
PERSONA_FULL=$(echo "$JSON" | jq -r '.persona // empty')

if [ -z "$BRANCH" ] || [ -z "$PERSONA_FULL" ]; then
    echo "Error: Missing required fields (branch, persona)" >&2
    exit 1
fi

# Map persona to short name
case "$PERSONA_FULL" in
    "Security Researcher") PERSONA="security" ;;
    "Cryptographer") PERSONA="cryptographer" ;;
    "Senior Rust Developer") PERSONA="rust" ;;
    "Senior TypeScript Developer") PERSONA="typescript" ;;
    "Senior Software Architect") PERSONA="architect" ;;
    "Senior Database Engineer") PERSONA="database" ;;
    "Performance Engineer") PERSONA="performance" ;;
    *)
        echo "Error: Unknown persona '$PERSONA_FULL'" >&2
        exit 1
        ;;
esac

# Sanitize branch name for safe filename
BRANCH_SAFE=$(sanitize_branch "$BRANCH")

# Generate timestamp for filename (YYYYMMDD-HHMMSS)
TIMESTAMP=$(date +%Y%m%d-%H%M%S)

# Create output path
mkdir -p "$REVIEWS_DIR"
OUTPUT_FILE="$REVIEWS_DIR/${BRANCH_SAFE}-${PERSONA}-${TIMESTAMP}.json"

# Write to temp file first for validation
TEMP_FILE=$(mktemp)
echo "$JSON" > "$TEMP_FILE"

# Validate
if ! "$VALIDATOR" "$TEMP_FILE" 2>&1; then
    rm -f "$TEMP_FILE"
    exit 1
fi

# Move to final location
mv "$TEMP_FILE" "$OUTPUT_FILE"
echo "✅ Review saved: $OUTPUT_FILE"
