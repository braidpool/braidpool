#!/usr/bin/env python3
"""
Validate AI review JSON files against the schema.

Usage:
    ./scripts/validate-review.py .reviews/*.json
    ./scripts/validate-review.py --all
    ./scripts/validate-review.py --branch <branch-name>
"""

import argparse
import json
import re
import sys
from pathlib import Path

# Try to use jsonschema if available, fall back to basic validation
try:
    import jsonschema
    HAS_JSONSCHEMA = True
except ImportError:
    HAS_JSONSCHEMA = False


SCHEMA_PATH = Path(__file__).parent.parent / "schemas" / "review.schema.json"
REVIEWS_DIR = Path(".reviews")

# Required fields for basic validation
REQUIRED_FIELDS = ["branch", "persona", "model", "date", "grade", "findings"]
VALID_PERSONAS = [
    "Security Researcher",
    "Cryptographer", 
    "Senior Rust Developer",
    "Senior TypeScript Developer",
    "Senior Software Architect",
    "Senior Database Engineer"
]
VALID_GRADES = ["PASS", "PASS-WITH-NOTES", "NEEDS-WORK"]
VALID_SEVERITIES = ["critical", "high", "medium", "low"]
VALID_STATUSES = ["open", "resolved", "wont-fix", "regressed"]


def load_schema():
    """Load the JSON schema file."""
    if not SCHEMA_PATH.exists():
        print(f"Warning: Schema file not found at {SCHEMA_PATH}", file=sys.stderr)
        return None
    with open(SCHEMA_PATH) as f:
        return json.load(f)


def basic_validate(data: dict, filepath: str) -> list[str]:
    """Basic validation without jsonschema library."""
    errors = []
    
    # Check required fields
    for field in REQUIRED_FIELDS:
        if field not in data:
            errors.append(f"Missing required field: {field}")
    
    if errors:
        return errors  # Can't continue without required fields
    
    # Validate persona
    if data["persona"] not in VALID_PERSONAS:
        errors.append(f"Invalid persona: {data['persona']}. Must be one of: {VALID_PERSONAS}")
    
    # Validate grade
    if data["grade"] not in VALID_GRADES:
        errors.append(f"Invalid grade: {data['grade']}. Must be one of: {VALID_GRADES}")
    
    # Validate date format (YYYY-MM-DD)
    if not re.match(r"^\d{4}-\d{2}-\d{2}$", data["date"]):
        errors.append(f"Invalid date format: {data['date']}. Must be YYYY-MM-DD")
    
    # Validate findings
    if not isinstance(data["findings"], list):
        errors.append("findings must be an array")
    else:
        for i, finding in enumerate(data["findings"]):
            if not isinstance(finding, dict):
                errors.append(f"Finding {i} must be an object")
                continue
            
            # Check required finding fields
            for field in ["severity", "file", "description", "status"]:
                if field not in finding:
                    errors.append(f"Finding {i} missing required field: {field}")
            
            if "severity" in finding and finding["severity"] not in VALID_SEVERITIES:
                errors.append(f"Finding {i} has invalid severity: {finding['severity']}")
            
            if "status" in finding and finding["status"] not in VALID_STATUSES:
                errors.append(f"Finding {i} has invalid status: {finding['status']}")
            
            if "description" in finding and len(finding["description"]) < 10:
                errors.append(f"Finding {i} description too short (min 10 chars)")
    
    # Validate grade consistency
    if data["grade"] == "NEEDS-WORK":
        has_critical_or_high = any(
            f.get("severity") in ["critical", "high"] 
            for f in data["findings"] 
            if isinstance(f, dict)
        )
        if not has_critical_or_high:
            errors.append("Grade is NEEDS-WORK but no critical/high severity findings")
    
    return errors


def validate_file(filepath: Path, schema: dict = None) -> tuple[bool, list[str]]:
    """Validate a single review file."""
    errors = []
    
    # Check file exists
    if not filepath.exists():
        return False, [f"File not found: {filepath}"]
    
    # Parse JSON
    try:
        with open(filepath) as f:
            data = json.load(f)
    except json.JSONDecodeError as e:
        return False, [f"Invalid JSON: {e}"]
    
    # Validate with jsonschema if available
    if HAS_JSONSCHEMA and schema:
        try:
            jsonschema.validate(data, schema)
        except jsonschema.ValidationError as e:
            errors.append(f"Schema validation error: {e.message}")
            # Also show path to error
            if e.absolute_path:
                errors.append(f"  at: {'.'.join(str(p) for p in e.absolute_path)}")
    else:
        # Fall back to basic validation
        errors = basic_validate(data, str(filepath))
    
    return len(errors) == 0, errors


def main():
    parser = argparse.ArgumentParser(description="Validate AI review JSON files")
    parser.add_argument("files", nargs="*", help="Review files to validate")
    parser.add_argument("--all", action="store_true", help="Validate all files in .reviews/")
    parser.add_argument("--branch", help="Validate all reviews for a specific branch")
    parser.add_argument("--quiet", "-q", action="store_true", help="Only output errors")
    args = parser.parse_args()
    
    # Determine files to validate
    files = []
    if args.all:
        if REVIEWS_DIR.exists():
            files = list(REVIEWS_DIR.glob("*.json"))
    elif args.branch:
        if REVIEWS_DIR.exists():
            files = list(REVIEWS_DIR.glob(f"{args.branch}-*.json"))
    elif args.files:
        files = [Path(f) for f in args.files]
    else:
        parser.print_help()
        sys.exit(1)
    
    if not files:
        print("No review files found to validate")
        sys.exit(0)
    
    # Load schema
    schema = load_schema()
    if not HAS_JSONSCHEMA:
        print("Note: jsonschema not installed, using basic validation", file=sys.stderr)
        print("  Install with: pip install jsonschema", file=sys.stderr)
    
    # Validate each file
    all_valid = True
    for filepath in sorted(files):
        valid, errors = validate_file(filepath, schema)
        
        if valid:
            if not args.quiet:
                print(f"✅ {filepath}")
        else:
            all_valid = False
            print(f"❌ {filepath}")
            for error in errors:
                print(f"   {error}")
    
    # Summary
    if not args.quiet:
        print()
        print(f"Validated {len(files)} file(s): ", end="")
        if all_valid:
            print("All valid ✅")
        else:
            print("Some invalid ❌")
    
    sys.exit(0 if all_valid else 1)


if __name__ == "__main__":
    main()
