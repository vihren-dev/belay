"""The standalone model and codec build independently, and the core imports only Lean's prelude."""

import os
from pathlib import Path
import re
import tomllib

import pytest

from tests.runtime_support import run_command

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "packages/belay-sqlite-model"
ROOT_MODULE = "Belay.Sqlite.Model"
CORE_LIBRARY = "Belay.Sqlite.Model"
"""The Lake library of `lakefile.toml` whose modules, except the examples, form the core."""
CODEC_PREFIX = "Belay.Sqlite.Model.Codec"
ALLOWED_EXTERNAL_IMPORT_ROOTS = {"Init"}
"""The core uses only Lean's prelude; `Std` and the Lean compiler API add import cost it does not need."""


def module_path(module: str) -> Path:
    """The source file of a model module."""
    return PACKAGE / (module.replace(".", "/") + ".lean")


def all_package_modules() -> set[str]:
    """Every module that has a source file in the model package."""
    return {".".join(path.relative_to(PACKAGE).with_suffix("").parts)
            for path in (PACKAGE / "Belay").rglob("*.lean")}


def lake_glob_modules(pattern: str, modules: set[str]) -> set[str]:
    """The modules that a Lake glob selects: `X` is X, `X.*` is X and its submodules, `X.+` its submodules."""
    if pattern.endswith((".*", ".+")):
        prefix = pattern[:-2]
        below = {module for module in modules if module.startswith(prefix + ".")}
        return below | ({prefix} & modules if pattern.endswith(".*") else set())
    assert pattern in modules, f"lakefile.toml names {pattern}, which has no source file"
    return {pattern}


def is_example_module(module: str) -> bool:
    """Compiled examples and their helpers: Lake builds and checks them, and the root does not import them."""
    name = module.rsplit(".", 1)[-1]
    return name.endswith("Examples") or name == "ExampleSupport"


def core_library_modules() -> set[str]:
    """The modules of the core library in `lakefile.toml`, without the examples."""
    configuration = tomllib.loads((PACKAGE / "lakefile.toml").read_text())
    library = next(entry for entry in configuration["lean_lib"] if entry["name"] == CORE_LIBRARY)
    modules = all_package_modules()
    selected: set[str] = set()
    for pattern in library["roots"] + library["globs"]:
        selected |= lake_glob_modules(pattern, modules)
    return {module for module in selected if not is_example_module(module)}


def root_import_closure() -> tuple[set[str], list[tuple[str, str]]]:
    """The model modules that the root reaches through imports, and each import from outside the model."""
    pending = [ROOT_MODULE]
    reached: set[str] = set()
    external: list[tuple[str, str]] = []
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        for line in re.findall(r"(?m)^import (.+)$", module_path(module).read_text()):
            for dependency in line.split():
                if dependency == ROOT_MODULE or dependency.startswith(ROOT_MODULE + "."):
                    pending.append(dependency)
                else:
                    external.append((module, dependency))
    return reached, external


@pytest.mark.unit
def test_root_imports_the_core_and_only_the_prelude() -> None:
    """The model's boundary (ADR 0006): `import Belay.Sqlite.Model` gives every core module, and only them.

    Each module of the core library in `lakefile.toml`, except the compiled examples, is reached
    from the root. The root reaches no example and no codec module, and no module outside the
    model except Lean's prelude (`Init`). The test reads the sources only, so it runs with the
    source checks of each pull request.
    """
    reached, external = root_import_closure()
    outside_prelude = [(module, dependency) for module, dependency in external
                       if dependency.split(".")[0] not in ALLOWED_EXTERNAL_IMPORT_ROOTS]
    assert not outside_prelude, f"core modules import more than Lean's prelude: {outside_prelude}"
    examples = sorted(module for module in reached if is_example_module(module))
    assert not examples, f"the root imports compiled examples: {examples}"
    codec = sorted(module for module in reached if module.startswith(CODEC_PREFIX))
    assert not codec, f"the root imports the codec: {codec}"
    core = core_library_modules()
    assert not reached - core, f"the root imports modules outside the core library: {sorted(reached - core)}"
    assert not core - reached, (f"core modules that `import Belay.Sqlite.Model` does not give; "
                                f"import them in Belay/Sqlite/Model.lean: {sorted(core - reached)}")


@pytest.fixture(scope="module")
def model_artifact() -> Path:
    """Build the real component with its isolated fileset, pinned compiler and hardened sandbox."""
    result = run_command(["nix-build", "build-support/default.nix", "-A", "modelPackage",
        "--no-out-link", "--option", "sandbox", "true", "--option", "sandbox-fallback", "false",
        "--extra-experimental-features", "nix-command flakes"], cwd=ROOT, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    return Path(result.stdout.strip())


@pytest.mark.integration
@pytest.mark.requires_nix
@pytest.mark.requires_lean("compiler")
def test_installed_core_and_codec_consumer(model_artifact: Path, lean_sysroot: Path,
                                           tmp_path: Path) -> None:
    """An unrelated consumer imports both libraries and checks a syntax roundtrip and a refusal."""
    source = tmp_path / "Consumer.lean"
    source.write_text('''import Belay.Sqlite.Model
import Belay.Sqlite.Model.Codec.Resolution
open Belay.Sqlite.Model
#check Conforms.setRows
#check TableExtends.project
#check Conformance.statement_atomicity
#eval match (Lean.fromJson? (Lean.toJson Syntax.Statement.commit) : Except String Syntax.Statement) with
  | .ok statement => statement == Syntax.Statement.commit
  | .error _ => false
#eval match (Lean.fromJson? (Lean.toJson (256 : Nat)) : Except String UInt8) with
  | .ok _ => false
  | .error _ => true
''')
    library = model_artifact / ".lake/build/lib/lean"
    result = run_command([str(lean_sysroot / "bin/lean"), str(source)], cwd=tmp_path,
        environment={**os.environ, "LEAN_PATH": str(library), "LEAN_SRC_PATH": str(model_artifact)}, timeout=30)
    assert result.returncode == 0, result.diagnostic()
    assert result.stdout.splitlines().count("true") == 2, result.diagnostic()
