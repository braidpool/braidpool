#!/bin/bash
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
# 4. Saves to .reviews/<branch>-<persona>-<date>-<time>.json
# 5. Exits 0 on success, 1 on validation failure

set -e

# Current workflow version - update when making breaking changes
CURRENT_VERSION="1.0"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
REVIEWS_DIR="$REPO_ROOT/.reviews"
SCHEMA="$SCRIPT_DIR/../schemas/review.schema.json"
VALIDATOR="$SCRIPT_DIR/validate-review.py"

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
DATE=$(echo "$JSON" | jq -r '.date // empty')

if [ -z "$BRANCH" ] || [ -z "$PERSONA_FULL" ] || [ -z "$DATE" ]; then
    echo "Error: Missing required fields (branch, persona, date)" >&2
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
    *)
        echo "Error: Unknown persona '$PERSONA_FULL'" >&2
        exit 1
        ;;
esac

# Create output path with timestamp to allow multiple reviews per day
mkdir -p "$REVIEWS_DIR"
TIMESTAMP=$(date +%H%M%S)
OUTPUT_FILE="$REVIEWS_DIR/${BRANCH}-${PERSONA}-${DATE}-${TIMESTAMP}.json"

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
