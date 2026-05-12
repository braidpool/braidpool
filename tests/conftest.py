import os
import pytest
from braid import load_braid

# directory containing JSON braid fixture files
BRAIDS_DIR = os.path.join(os.path.dirname(__file__), "braids")


def _collect_fixture_files():
    """Return a sorted list of .json filenames in the braids/ directory."""
    return sorted(f for f in os.listdir(BRAIDS_DIR) if f.endswith(".json"))


# Parametrized fixture: yields (filename, dag) for every JSON test case
_FIXTURE_FILES = _collect_fixture_files()


@pytest.fixture(params=_FIXTURE_FILES, ids=[os.path.splitext(f)[0] for f in _FIXTURE_FILES], scope="session")
def braid_fixture(request):
    """
    Load a single JSON braid fixture and return (filename, dag dict).
    Scoped to *session* so each JSON file is parsed only once for the entire test suite.
    """
    filename = request.param
    dag = load_braid(os.path.join(BRAIDS_DIR, filename))
    return filename, dag


# Common inline topologies for unit tests
@pytest.fixture
def blockchain_parents():
    """Simple linear chain: 0 -> 1 -> 2 -> 3"""
    return {0: set(), 1: {0}, 2: {1}, 3: {2}}


@pytest.fixture
def two_genesis_parents():
    """Two genesis beads with shared children: 0, 1 are geneses; 2,3 descend from 1."""
    return {0: set(), 1: set(), 2: {1}, 3: {1}}


@pytest.fixture
def three_genesis_parents():
    """Three genesis beads with independent children."""
    return {0: set(), 1: set(), 2: set(), 3: {1}, 4: {0}}


@pytest.fixture
def fan_out_parents():
    """Three geneses that fan into three shared children."""
    return {0: set(), 1: set(), 2: set(), 3: {0, 1, 2}, 4: {0, 1, 2}, 5: {0, 1, 2}}


@pytest.fixture
def diamond_parents():
    """Classic diamond DAG: 0 -> {1,2} -> 3 -> 4"""
    return {0: set(), 1: {0}, 2: {0}, 3: {1, 2}, 4: {3}}
