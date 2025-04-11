import pytest
from flask.testing import FlaskClient
from simulator_api import app


@pytest.fixture
def client():
    with app.test_client() as client:
        yield client


def test_hello(client: FlaskClient):
    """Test the /hello endpoint returns correct response."""
    response = client.get("/hello")
    assert response.status_code == 200
    assert b"Hello Braidpool" in response.data


def test_test_data_empty(client: FlaskClient):
    """Test the /test_data endpoint returns correct structure with empty braid_data."""
    response = client.get("/test_data")
    assert response.status_code == 200
    data = response.get_json()

    # As braid_data might be empty at startup, we validate it's a dictionary
    assert isinstance(data, dict)


def test_test_data_structure(client: FlaskClient):
    """Test the /test_data endpoint returns valid structure when braid_data is populated."""
    # Mocking braid_data for test
    from simulator_api import braid_data

    braid_data.update(
        {
            "highest_work_path": ["1", "2"],
            "parents": {"1": ["0"], "2": ["1"]},
            "children": {"0": ["1"], "1": ["2"]},
            "work": {"0": 1, "1": 2, "2": 3},
            "cohorts": [["0"], ["1", "2"]],
            "bead_count": 3,
        }
    )

    response = client.get("/test_data")
    assert response.status_code == 200
    data = response.get_json()

    assert "highest_work_path" in data
    assert isinstance(data["highest_work_path"], list)

    assert "parents" in data
    assert isinstance(data["parents"], dict)

    assert "children" in data
    assert isinstance(data["children"], dict)

    assert "work" in data
    assert isinstance(data["work"], dict)

    assert "cohorts" in data
    assert isinstance(data["cohorts"], list)

    assert "bead_count" in data
    assert isinstance(data["bead_count"], int)
