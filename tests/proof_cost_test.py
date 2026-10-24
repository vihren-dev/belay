"""S7 prototype: completed native body costs, persistence, coverage and measured overhead."""

from collections.abc import Callable
from decimal import Decimal
import json
from pathlib import Path
from typing import cast

import pytest

from tests.proof_cost_support import Compiler, checked, counts, pair, payload, records
from tests.runtime_support import CommandTimeout
from tests.surface_support import FIXTURES

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


@pytest.fixture(scope="module")
def collector(runtime_root: Path, tmp_path_factory: pytest.TempPathFactory) -> Path:
    """Compile the imported test plugin once against the installed compiler."""
    directory = tmp_path_factory.mktemp("proof-cost-plugin")
    compiler = Compiler(runtime_root, directory, directory / "ProofCostCollector.olean")
    for name in ("ProofCostRecords", "ProofCostCollector"):
        checked(compiler.compile(name, (FIXTURES / f"{name}.lean").read_text()))
    return compiler.artifact("ProofCostCollector")


@pytest.mark.parametrize("asynchronous", [True, False])
def test_completed_costs_follow_bodies_and_growth(runtime_root: Path, tmp_path: Path,
                                                 collector: Path, asynchronous: bool,
                                                 record_testsuite_property: Callable[[str, object], None]) -> None:
    """Our collector retains native async work, attributes both orders, and detects changed proof work."""
    compiler = Compiler(runtime_root, tmp_path, collector)
    observations = []
    cheap_proofs = []
    for size, reverse in ((30, False), (30, False), (30, False), (30, True), (100, False)):
        result = compiler.compile("Pair", pair(size, reverse), asynchronous=asynchronous)
        checked(result)
        measured = counts(result)
        assert measured.keys() == {"cheap", "costly"}, result.diagnostic()
        assert measured["costly"] > 10 * measured["cheap"] > 0, measured
        mode = "async" if asynchronous else "sync"
        assert all(value["scheme"] == f"native-definition-value-v1-{mode}"
                   for value in records(result))
        declarations = cast(list[dict[str, object]], payload(result, "DECLARATIONS"))
        cheap_proofs.append([value for value in declarations if value["name"] == "cheap"])
        commands = cast(list[dict[str, object]], payload(result, "COMMAND_COSTS"))
        descriptions = str([value["snapshots"] for value in commands])
        assert ("elaborating proof of" in descriptions) == asynchronous, descriptions
        observations.append(measured)
    assert all(proof == cheap_proofs[0] and len(proof) == 1 for proof in cheap_proofs)
    assert observations[-1]["costly"] > 2 * max(value["costly"] for value in observations[:-1]), observations
    shown = {name: str(Decimal(value) / 1000) for name, value in observations[0].items()}
    assert all(Decimal(shown[name]) * 1000 == value for name, value in observations[0].items())
    record_testsuite_property(f"proof_cost.attribution.{asynchronous}", json.dumps(observations))
    print("ATTRIBUTION", asynchronous, json.dumps(observations), "BUDGET_UNITS", shown)


def test_records_survive_import_replacement_and_relocation(runtime_root: Path, tmp_path: Path,
                                                          collector: Path) -> None:
    """Our exported data needs no proof source, deduplicates diamond imports and replaces recompiles."""
    compiler = Compiler(runtime_root, tmp_path / "first", collector)
    original = compiler.compile("Pair", pair(30))
    checked(original)
    (compiler.directory / "Pair.lean").unlink()
    imports = {"Pair": compiler.artifact("Pair")}
    for name in ("Left", "Right"):
        checked(compiler.compile(name, "import Pair\n", imports=imports))
        imports[name] = compiler.artifact(name)
    read = compiler.compile("Reader", "import Left\nimport Right\n#proof_cost_records\n", imports=imports)
    checked(read)
    assert records(read) == records(original)
    updated = compiler.compile("Pair", pair(100))
    checked(updated)
    read = compiler.compile("Reader", "import Pair\n#proof_cost_records\n", imports=imports)
    checked(read)
    assert records(read) == records(updated)
    other = Compiler(runtime_root, tmp_path / "relocated", collector)
    relocated = other.compile("Pair", pair(100))
    checked(relocated)
    # Identity must survive relocation; native allocation counts can vary between compiles.
    assert [{key: value for key, value in record.items() if key != "heartbeats"}
            for record in records(relocated)] == [
                {key: value for key, value in record.items() if key != "heartbeats"}
                for record in records(updated)]


def test_coverage_preserves_claims_and_identifies_gaps(runtime_root: Path, tmp_path: Path,
                                                     collector: Path,
                                                     record_testsuite_property: Callable[[str, object], None]) -> None:
    """Our wrapper preserves checked expressions while exposing anonymous and generated-helper limits."""
    compiler = Compiler(runtime_root, tmp_path, collector)
    source = (FIXTURES / "ProofCostCases.lean").read_text()
    measured = compiler.compile("Coverage", source)
    checked(measured)
    control = compiler.compile("Coverage", source, enabled=False)
    checked(control)
    assert payload(measured, "DECLARATIONS") == payload(control, "DECLARATIONS")
    names = counts(measured)
    assert len(names) == 9 and len([name for name in names if "_example@" in name]) == 2, names
    assert {"Coverage.tactic", "Coverage.term", "Coverage.proofDefinition", "Coverage.predicate",
            "Coverage.embedded",
            "Coverage.recursive", "_private.Coverage.0.Coverage.hidden"} <= names.keys(), names
    declarations = cast(list[dict[str, object]], payload(measured, "DECLARATIONS"))
    missing = sorted(str(value["name"]) for value in declarations if value["name"] not in names)
    assert "Coverage.embedded._proof_1" in missing and any("recursive." in name for name in missing)
    assert records(control) == []
    observation = json.dumps({"counts": names, "unmeasured": missing})
    record_testsuite_property("proof_cost.coverage", observation)
    print("COVERAGE", observation)


def test_failures_and_precision_do_not_become_zero(runtime_root: Path, tmp_path: Path,
                                                   collector: Path) -> None:
    """Our collector distinguishes failed/missing bodies and rejects inexact Float endpoints."""
    compiler = Compiler(runtime_root, tmp_path, collector)
    failed = compiler.compile("Failed", "import ProofCostCollector\n"
                              "theorem broken : False := by trivial\n#proof_cost_records\n")
    assert failed.returncode != 0 and not compiler.artifact("Failed").exists(), failed.diagnostic()
    assert len(records(failed)) == 1 and records(failed)[0]["status"] == "failed"
    missing = compiler.compile("Missing", "import ProofCostRecords\n"
                               "theorem unmeasured : True := True.intro\n#proof_cost_records\n")
    checked(missing)
    assert records(missing) == [], missing.diagnostic()
    precision = compiler.compile("Precision", "import ProofCostCollector\nopen Lean ProofCostExperiment\n"
        '#eval IO.println ("PRECISION " ++ (toJson ([count { cls := `test, startTime := 0, stopTime := 0 },\n'
        'count { cls := `test, startTime := 10, stopTime := 1011 },\n'
        'count { cls := `test, startTime := 0.5, stopTime := 1 },\n'
        'count { cls := `test, startTime := 0, stopTime := 9007199254740992 }])).compress)\n'
        '#eval IO.println ("ZERO " ++ (toJson (collect "Precision" (.trace\n'
        '  { cls := `Elab.definition.value, result? := some .success } m!"zero" #[]))).compress)\n')
    checked(precision)
    assert payload(precision, "PRECISION") == [0, 1001, None, None]
    zero = cast(list[dict[str, object]], payload(precision, "ZERO"))[0]
    assert zero["heartbeats"] == 0 and zero["status"] == "completed"


def test_interrupted_compilation_has_no_completed_record(runtime_root: Path, tmp_path: Path,
                                                        collector: Path) -> None:
    """Cancellation of our collector's compiler process leaves unavailable data, never a zero record."""
    compiler = Compiler(runtime_root, tmp_path, collector)
    source = ("import ProofCostCollector\ntheorem interrupted : True := by\n"
              '  run_tac do\n    IO.FS.writeFile "proof-started" "started"\n'
              "    IO.sleep 60000\n  exact True.intro\n#proof_cost_records\n")
    with pytest.raises(CommandTimeout) as interrupted:
        compiler.compile("Interrupted", source, timeout=10)
    result = interrupted.value.result
    assert (tmp_path / "proof-started").read_text() == "started", result.diagnostic()
    assert result.timed_out and "PROOF_COSTS" not in result.stdout, result.diagnostic()
    assert not compiler.artifact("Interrupted").exists()


def test_surface_sample_reports_overhead_without_changing_proofs(
        runtime_root: Path, tmp_path: Path, collector: Path,
        record_testsuite_property: Callable[[str, object], None]) -> None:
    """Compare our hook with the native elaborator over the same three surface proof commands."""
    compiler = Compiler(runtime_root, tmp_path, collector)
    source = (FIXTURES / "ProofCostSurface.lean").read_text()
    observations: dict[str, list[dict[str, object]]] = {"False": [], "True": []}
    snapshots = []
    # The first pair warms the imports; keep four measured compiles in balanced order.
    for iteration, enabled in enumerate((False, True, False, True, True, False)):
        result = compiler.compile("Surface", source, enabled=enabled, asynchronous=False)
        checked(result)
        snapshots.append(payload(result, "DECLARATIONS"))
        window = payload(result, "WINDOW_HEARTBEATS")
        assert isinstance(window, int) and window > 0, result.diagnostic()
        if iteration >= 2:
            observations[str(enabled)].append({"elapsed_seconds": result.elapsed,
                "window_heartbeats": window, "body_counts": counts(result)})
    assert all(snapshot == snapshots[0] for snapshot in snapshots)
    record_testsuite_property("proof_cost.overhead", json.dumps(observations, sort_keys=True))
    print("OVERHEAD", json.dumps(observations, sort_keys=True))
