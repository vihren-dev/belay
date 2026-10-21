"""The standalone model and codec build independently, and the core imports only Lean's prelude."""

import os
from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "packages/belay-sqlite-model"
MODEL_MODULE_PREFIX = "Belay.Sqlite.Model"
"""Only the standalone package namespace supplies project modules to the core."""
ALLOWED_EXTERNAL_IMPORT_ROOTS = {"Init"}
"""The core uses only Lean's prelude; `Std` and the Lean compiler API add import cost it does not need."""
EXPECTED_CORE_MODULE_COUNT = 203
"""The public root reaches two hundred and three core modules, including identifiers, keys, resolution, index terms, collations, CHECK constraints, foreign keys with their parent keys and enforced checks and actions, generated columns, the source list, query evaluation, joins,
UPSERT, number conversions, store-time affinity, JSON reading, defaults, the clock, the date and time functions with
their modifiers, triggers, and the results that SQLite may give; its compiled examples are not imported."""
pytestmark = [pytest.mark.integration, pytest.mark.requires_nix, pytest.mark.requires_lean("compiler")]


def test_core_import_closure_excludes_codec() -> None:
    """Follow the actual public root; no model import may reach Lean or codec modules."""
    pending = ["Belay.Sqlite.Model"]
    reached: set[str] = set()
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        assert module != "Belay.Sqlite.Model.Codec", module
        source = PACKAGE / (module.replace(".", "/") + ".lean")
        for line in re.findall(r"(?m)^import (.+)$", source.read_text()):
            for dependency in line.split():
                if dependency.startswith(MODEL_MODULE_PREFIX):
                    pending.append(dependency)
                else:
                    assert dependency.split(".")[0] in ALLOWED_EXTERNAL_IMPORT_ROOTS, (module, dependency)
    assert len(reached) == EXPECTED_CORE_MODULE_COUNT


@pytest.fixture(scope="module")
def model_artifact() -> Path:
    """Build the real component with its isolated fileset, pinned compiler and hardened sandbox."""
    result = run_command(["nix-build", "build-support/default.nix", "-A", "modelPackage",
        "--no-out-link", "--option", "sandbox", "true", "--option", "sandbox-fallback", "false",
        "--extra-experimental-features", "nix-command flakes"], cwd=ROOT, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    return Path(result.stdout.strip())


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
