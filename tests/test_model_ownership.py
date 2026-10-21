"""Structural model facts compile from the model's own sources and Lean's prelude alone."""

import os
from pathlib import Path
import re
import shutil

import pytest

from tests.runtime_support import run_command

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "packages/belay-sqlite-model"
MODEL_ROOTS = ("Belay.Sqlite.Model.SchemaExtensionLaws", "Belay.Sqlite.Model.SchemaPreservationLaws",
               "Belay.Sqlite.Model.LiteralPreservationLaws", "Belay.Sqlite.Model.ModelProjectionLaws",
               "Belay.Sqlite.Model.Laws")
"""Mixed-file facts and conformance laws must have a structural import closure."""
ALLOWED_EXTERNAL_IMPORT_ROOTS = {"Init"}
"""The core model uses only Lean's prelude, without `Std` or the Lean compiler API."""
PROJECT_MODULE_PREFIXES = ("Belay.Sqlite.Model",)
"""Follow the model package namespace only."""
pytestmark = [pytest.mark.integration, pytest.mark.requires_lean("compiler")]


def model_closure() -> list[str]:
    """Order actual imports for compilation and reject Lean dependencies beyond the prelude."""
    ordered: list[str] = []
    active: set[str] = set()

    def visit(module: str) -> None:
        """Follow source imports once and fail on a cycle instead of truncating the closure."""
        if module in ordered:
            return
        assert module not in active, f"Model import cycle: {module}"
        active.add(module)
        source = PACKAGE / (module.replace(".", "/") + ".lean")
        for line in re.findall(r"(?m)^import (.+)$", source.read_text()):
            for dependency in line.split():
                if dependency.startswith(PROJECT_MODULE_PREFIXES):
                    visit(dependency)
                else:
                    assert dependency.split(".")[0] in ALLOWED_EXTERNAL_IMPORT_ROOTS, (module, dependency)
        active.remove(module)
        ordered.append(module)

    for module in MODEL_ROOTS:
        visit(module)
    return ordered


@pytest.fixture(scope="module")
def isolated_model(tmp_path_factory: pytest.TempPathFactory,
                   lean_sysroot: Path) -> Path:
    """Compile copied model sources with only their own artifacts and the pinned sysroot."""
    directory = tmp_path_factory.mktemp("model-ownership") / "model"
    directory.mkdir()
    environment = {**os.environ, "LEAN_PATH": str(directory), "LEAN_SRC_PATH": str(directory)}
    for module in model_closure():
        relative = Path(module.replace(".", "/") + ".lean")
        source = directory / relative
        source.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(PACKAGE / relative, source)
        result = run_command([str(lean_sysroot / "bin/lean"), "-o", str(source.with_suffix(".olean")),
                              str(source)], cwd=directory, environment=environment, timeout=30)
        assert result.returncode == 0, result.diagnostic()
    return directory


def test_neutral_consumer_uses_structural_facts(isolated_model: Path,
                                              lean_sysroot: Path) -> None:
    """Lookup, updates, projections and conformance laws remain usable without a logical contract."""
    source = isolated_model / "Consumer.lean"
    source.write_text("\n".join(f"import {module}" for module in MODEL_ROOTS) + "\n" +
        "#check Belay.Sqlite.Model.Conforms.setRows\n#check Belay.Sqlite.Model.Database.setRows_comm\n"
        "#check Belay.Sqlite.Model.TableExtends.project\n#check Belay.Sqlite.Model.Database.table_addColumn\n"
        "#check Belay.Sqlite.Model.Table.project_newColumn\n"
        "#check Belay.Sqlite.Model.Conformance.statement_atomicity\n")
    result = run_command([str(lean_sysroot / "bin/lean"), str(source)], cwd=isolated_model,
        environment={**os.environ, "LEAN_PATH": str(isolated_model), "LEAN_SRC_PATH": str(isolated_model)},
        timeout=15)
    assert result.returncode == 0, result.diagnostic()
