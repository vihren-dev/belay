"""The conformance Nix suites declare every frontend module that their tests import.

`build-support/tests.nix` gives the conformance suites only the frontend modules in
`tests/conformance_frontend.json`, so that a change to another frontend module leaves
their cached results valid. The Nix sandbox would reject a missing module, but
only after a long build; this check finds it on the host in less than a second.
"""

import json
from pathlib import Path

import pytest

from tests.python_imports import import_closure

ROOT = Path(__file__).resolve().parents[1]
CONFORMANCE_SUITES = ("model", "coverageStatements", "coverageFeatures", "frozen", "harness", "sample", "upstream", "writers")
"""The Nix suites that receive the narrowed frontend inputs."""
pytestmark = [pytest.mark.unit]


def declared_frontend() -> set[str]:
    """The frontend modules that the conformance suites receive, which the closure must not exceed."""
    return set(json.loads((ROOT / "tests/conformance_frontend.json").read_text(encoding="utf-8")))


def test_declared_frontend_modules_exist() -> None:
    """A stale entry fails here instead of as a Nix evaluation error."""
    missing = {name for name in declared_frontend() if not (ROOT / (name.replace(".", "/") + ".py")).is_file()}
    assert not missing, f"tests/conformance_frontend.json names missing modules: {sorted(missing)}"


def test_closure_follows_submodules_imported_from_a_package(tmp_path: Path) -> None:
    """`from conformance import helper` reaches the frontend modules that helper imports."""
    for name, text in {"tests/example_test.py": "from conformance import helper\n",
                       "conformance/helper.py": "from . import other\n",
                       "conformance/other.py": "from tools.secret import value\n",
                       "tools/secret.py": "value = 1\n"}.items():
        (tmp_path / name).parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / name).write_text(text, encoding="utf-8")
    assert "tools.secret" in import_closure(["tests/example_test.py"], tmp_path)


def test_closure_follows_nested_frontend_relative_imports(tmp_path: Path) -> None:
    """A relative frontend import resolves inside belay.sqlite and exposes its dependencies outside it."""
    for name, text in {"tests/example_test.py": "from belay.sqlite.sql_model import Table\n",
                       "belay/sqlite/sql_model.py": "from . import helper\n",
                       "belay/sqlite/helper.py": "from tools.secret import value\n",
                       "tools/secret.py": "value = 1\n"}.items():
        (tmp_path / name).parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / name).write_text(text, encoding="utf-8")
    assert "tools.secret" in import_closure(["tests/example_test.py"], tmp_path)


@pytest.mark.parametrize("suite", CONFORMANCE_SUITES)
def test_suite_imports_only_declared_frontend_modules(suite: str) -> None:
    """Add a module that a conformance test starts to import to tests/conformance_frontend.json."""
    files = json.loads((ROOT / "tests/nix_suites.json").read_text(encoding="utf-8"))[suite]
    closure = import_closure(files)
    used = {name for name in closure if name.startswith("belay.sqlite.")}
    undeclared = used - declared_frontend()
    assert not undeclared, (f"Suite {suite} imports frontend modules that its Nix inputs omit: "
                            f"{sorted(undeclared)}; add them to tests/conformance_frontend.json")
