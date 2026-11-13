"""Repository pytest options; the runtime fixtures are in `tests/runtime_fixtures.py`."""

import json
from pathlib import Path

import pytest

pytest_plugins = ["tests.runtime_fixtures", "tools.observability_pytest"]


def pytest_addoption(parser: pytest.Parser) -> None:
    """Select the runtime under test; reports come from pytest's own --junitxml."""
    group = parser.getgroup("belay")
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

