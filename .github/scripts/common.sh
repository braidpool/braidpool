#!/bin/bash
# .github/scripts/common.sh
# Common helper functions used by git hooks and scripts

# Sanitize branch name for safe filename usage
# Replaces special characters with dashes, collapses multiple dashes, and trims
#
# Usage: sanitize_branch "feature/my-branch"
# Returns: feature-my-branch
sanitize_branch() {
    echo "$1" | tr -c '[:alnum:]-_.' '-' | tr -s '-' | sed 's/^-//;s/-$//'
}
