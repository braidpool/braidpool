#!/usr/bin/env python3
"""
Tests for .github/scripts/validate-review.py, in particular its basic_validate()
fallback, which is what runs when the jsonschema package is not installed.
"""

import importlib.util
import json
import os
import unittest

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
SCRIPT_PATH = os.path.join(REPO_ROOT, '.github', 'scripts', 'validate-review.py')
SCHEMA_PATH = os.path.join(REPO_ROOT, '.github', 'schemas', 'review.schema.json')

# The script name contains a hyphen, so load it by path
spec = importlib.util.spec_from_file_location("validate_review", SCRIPT_PATH)
validate_review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(validate_review)

with open(SCHEMA_PATH, encoding='utf8') as f:
    SCHEMA = json.load(f)


def make_review(**overrides):
    review = {
        "branch": "fix-something",
        "persona": "Performance Engineer",
        "model": "claude-sonnet-4.5",
        "grade": "PASS-WITH-NOTES",
        "findings": [{
            "severity": "medium",
            "file": "node/src/braid/mod.rs",
            "description": "Cohort recomputation is quadratic in the hot path",
            "status": "open",
        }],
    }
    review.update(overrides)
    return review


class TestFallbackMatchesSchema(unittest.TestCase):
    """The hard-coded fallback lists must stay in sync with review.schema.json."""

    def test_required_fields(self):
        self.assertEqual(set(validate_review.REQUIRED_FIELDS), set(SCHEMA["required"]))

    def test_personas(self):
        self.assertEqual(set(validate_review.VALID_PERSONAS),
                         set(SCHEMA["properties"]["persona"]["enum"]))

    def test_grades(self):
        self.assertEqual(set(validate_review.VALID_GRADES),
                         set(SCHEMA["properties"]["grade"]["enum"]))

    def test_finding_severities_and_statuses(self):
        finding = SCHEMA["properties"]["findings"]["items"]["properties"]
        self.assertEqual(set(validate_review.VALID_SEVERITIES), set(finding["severity"]["enum"]))
        self.assertEqual(set(validate_review.VALID_STATUSES), set(finding["status"]["enum"]))

    def test_date_pattern(self):
        """date is optional in both, and checked against the same pattern."""
        self.assertNotIn("date", SCHEMA["required"])
        self.assertEqual(validate_review.DATE_PATTERN, SCHEMA["properties"]["date"]["pattern"])


class TestSchemaAndFallbackAgree(unittest.TestCase):
    """With jsonschema installed, both validators must accept and reject the same dates."""

    def setUp(self):
        try:
            import jsonschema
        except ImportError:
            self.skipTest("jsonschema not installed")
        self.jsonschema = jsonschema

    def schema_accepts(self, review):
        try:
            self.jsonschema.validate(review, SCHEMA)
            return True
        except self.jsonschema.ValidationError:
            return False

    def test_dates(self):
        for review in (make_review(), make_review(date="2026-10-24"), make_review(date="24/10/2026")):
            fallback_accepts = validate_review.basic_validate(review, "review.json") == []
            self.assertEqual(self.schema_accepts(review), fallback_accepts, msg=review.get("date"))


class TestBasicValidate(unittest.TestCase):

    def test_performance_engineer_review_without_date_is_valid(self):
        """Schema-valid review: Performance Engineer persona and no optional date."""
        self.assertEqual(validate_review.basic_validate(make_review(), "review.json"), [])

    def test_valid_date_is_accepted(self):
        self.assertEqual(validate_review.basic_validate(make_review(date="2026-10-24"), "review.json"), [])

    def test_bad_date_is_rejected(self):
        errors = validate_review.basic_validate(make_review(date="24/10/2026"), "review.json")
        self.assertTrue(any("date" in e for e in errors), errors)

    def test_unknown_persona_is_rejected(self):
        errors = validate_review.basic_validate(make_review(persona="Intern"), "review.json")
        self.assertTrue(any("persona" in e for e in errors), errors)

    def test_missing_required_field_is_rejected(self):
        review = make_review()
        del review["model"]
        errors = validate_review.basic_validate(review, "review.json")
        self.assertIn("Missing required field: model", errors)


if __name__ == '__main__':
    unittest.main()
