"""Repository pytest options and execution-only runtime fixtures."""

import json
from pathlib import Path

import pytest

pytest_plugins = ["tests.runtime_fixtures"]


def pytest_addoption(parser: pytest.Parser) -> None:
    """Select the runtime under test; reports come from pytest's own --junitxml."""
    group = parser.getgroup("sqlite-verifier")
    group.addoption("--runtime-root", type=Path, help="Built runtime root, such as the conformance runtime")
    group.addoption("--source-checks", action="store_true", help="Exclude suites delegated to Nix")


def pytest_ignore_collect(collection_path: Path, config: pytest.Config) -> bool | None:
    """Keep host checks fresh without repeating the exact suites owned by Nix."""
    if config.getoption("source_checks") and collection_path.is_file():
        suites = json.loads((config.rootpath / "tests/nix_suites.json").read_text())
        delegated = {name for files in suites.values() for name in files}
        relative = collection_path.relative_to(config.rootpath).as_posix()
        return relative in delegated
    return None


@pytest.fixture(scope="session")
def runtime_root(pytestconfig: pytest.Config) -> Path:
    """Resolve the selected artifact root lazily, without checking unrelated prerequisites."""
    root = pytestconfig.getoption("runtime_root") or pytestconfig.rootpath
    if not root.is_dir():
        pytest.fail(f"Runtime directory is missing: {root}; build the selected runtime first")
    return root.resolve()
