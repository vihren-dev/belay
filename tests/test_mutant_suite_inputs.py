"""Each mutant suite declares exactly the Python modules that its tests import (#330).

`build-support/tests.nix` gives each suite of `tests/nix_mutant_suites.json` only the modules
that `tests/nix_mutant_inputs.json` lists for it, so that a change to another module, a corpus
or the judge leaves the suite's derivation and its accepted report (#328) valid. A missing
module would fail only in the scheduled CI run, and an extra one reruns the suite for nothing;
the unit test finds both on the host.
"""

import json
from pathlib import Path

import pytest

from tests.python_imports import import_closure
from tests.runtime_support import run_command

ROOT = Path(__file__).resolve().parents[1]
SUITES: list[str] = json.loads((ROOT / "tests/nix_mutant_suites.json").read_text(encoding="utf-8"))
"""The mutant suites, which run on their own CI runners."""


def declared_modules() -> dict[str, list[str]]:
    """The modules of each mutant suite in `tests/nix_mutant_inputs.json`, which Nix reads."""
    return json.loads((ROOT / "tests/nix_mutant_inputs.json").read_text(encoding="utf-8"))


def suite_files(suite: str) -> list[str]:
    """The test files that the suite runs (`tests/nix_suites.json`)."""
    return json.loads((ROOT / "tests/nix_suites.json").read_text(encoding="utf-8"))[suite]


def required_modules(files: list[str], root: Path = ROOT) -> set[str]:
    """The import closure of `files`, with the `__init__` module of each package on the path of a
    closure module, because Python runs it before the module."""
    closure = import_closure(files, root)
    packages = {".".join(name.split(".")[:end]) for name in closure for end in range(1, name.count(".") + 1)}
    return closure | {f"{package}.__init__" for package in packages
                      if (root / package.replace(".", "/") / "__init__.py").is_file()}


@pytest.mark.unit
def test_package_initializers_join_the_closure(tmp_path: Path) -> None:
    """`required_modules` adds `belay/sqlite/__init__.py` for `belay.sqlite.errors`, and nothing for
    `conformance`, which has no initializer."""
    for name, text in {"tests/example_test.py": "from belay.sqlite.errors import E\nimport conformance.helper\n",
                       "belay/sqlite/__init__.py": "", "belay/sqlite/errors.py": "E = 1\n",
                       "conformance/helper.py": ""}.items():
        (tmp_path / name).parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / name).write_text(text, encoding="utf-8")
    assert required_modules(["tests/example_test.py"], tmp_path) == {
        "belay.sqlite.errors", "belay.sqlite.__init__", "conformance.helper"}


@pytest.mark.unit
@pytest.mark.parametrize("suite", SUITES)
def test_suite_declares_exactly_the_modules_that_its_tests_import(suite: str) -> None:
    """The declared modules of the suite equal the import closure of its test files."""
    declared = set(declared_modules()[suite])
    required = required_modules(suite_files(suite))
    assert declared == required, (
        f"Update {suite} in tests/nix_mutant_inputs.json: add {sorted(required - declared)}, "
        f"remove {sorted(declared - required)}")


@pytest.mark.unit
def test_every_mutant_suite_has_a_module_list() -> None:
    """A new mutant suite gets a list, and a removed one loses it."""
    assert sorted(declared_modules()) == sorted(SUITES)


@pytest.mark.integration
@pytest.mark.environment
@pytest.mark.requires_nix
def test_mutant_suite_sources_hold_only_their_modules_and_the_lean_packages() -> None:
    """The Nix source tree of each mutant suite holds the Python files of the `packages` suite
    (the shared harness files), its own test files and its declared modules, and no judge,
    corpus or other data file outside the two Lean packages."""
    names = " ".join(json.dumps(name) for name in ["packages", *SUITES])
    expression = ("let builds = import ./build-support/default.nix {}; tests = builds.tests // builds.scheduledTests; in "
                  f"builtins.listToAttrs (map (name: {{ inherit name; value = toString tests.${{name}}.src; }}) [ {names} ])")
    result = run_command(["nix-instantiate", "--eval", "--strict", "--json", "--read-write-mode",
                          "--extra-experimental-features", "nix-command flakes", "--expr", expression],
                         cwd=ROOT, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    sources = {name: Path(path) for name, path in json.loads(result.stdout).items()}
    common = {str(path.relative_to(sources["packages"])) for path in sources["packages"].rglob("*")
              if path.is_file()} - set(suite_files("packages"))
    for suite in SUITES:
        files = {str(path.relative_to(sources[suite])) for path in sources[suite].rglob("*") if path.is_file()}
        outside = {name for name in files if not name.startswith("packages/")}
        modules = {name.replace(".", "/") + ".py" for name in declared_modules()[suite]}
        assert outside == common | set(suite_files(suite)) | modules, (
            suite, sorted(outside ^ (common | set(suite_files(suite)) | modules)))
        lean = {name.split("/")[1] for name in files if name.startswith("packages/")}
        assert lean == {"belay-sqlite-model", "verifier-conformance"}, (suite, lean)
