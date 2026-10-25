"""S7 `belay-sql-check --costs`: the report, the baseline comparison and the stale-file check, on a real Lake package."""

import json
from pathlib import Path

import pytest

from tests.runtime_support import CommandResult
from tests.sql_file_support import installed_layout, lake_build, run_checker, write_lean_package

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

MEASURED = '''import Belay.Sqlite.ProofCost

/-- A cheap proof. -/
theorem cheap : True := True.intro

/-- A costly proof. -/
theorem costly : (List.range 40).length = 40 := by decide

/-- A private theorem, whose name changes with edits. -/
private theorem hidden : True := True.intro

example : True := True.intro
'''
"""A library module compiled with collection on by the library option."""
PLAIN = '''import Belay

/-- A theorem that nothing measured. -/
theorem unmeasured : True := True.intro

/-- The proof of the helper belongs to the parent theorem, and the structure's generated lemmas are
not theorems of the author. -/
theorem withHelper : True := helper
where
  helper : True := True.intro

structure Pair where
  first : Nat
'''
"""A library module compiled without collection."""
COLLECTION_ON = "  leanOptions := #[⟨`weak.belay.proofCosts, true⟩]"
"""The setting that a library uses to turn collection on for all its modules."""


def make_consumer(runtime_root: Path, tmp_path: Path) -> tuple[Path, Path]:
    """A package with the library Measured (collection on) and the library Plain (collection off), both built."""
    installed = installed_layout(runtime_root, tmp_path)
    package = tmp_path / "consumer"
    write_lean_package(package, "Costs", installed, ["Measured"], needs=COLLECTION_ON)
    with (package / "lakefile.lean").open("a") as lakefile:
        lakefile.write('\nlean_lib Plain where\n  srcDir := "lean"\n  roots := #[`Plain]\n')
    (package / "lean/Measured.lean").write_text(MEASURED)
    (package / "lean/Plain.lean").write_text(PLAIN)
    for library in ("Measured", "Plain"):
        result = lake_build(installed, package, library)
        assert result.returncode == 0, result.diagnostic()
    return installed, package


def baseline_of(installed: Path, package: Path) -> dict[str, list[dict[str, object]]]:
    """The `--json` report of both libraries, as the baseline file that a user saves."""
    result = run_checker(installed, package, "--costs", "--json")
    assert result.returncode == 0, result.diagnostic()
    return json.loads(result.stdout)


def compare(installed: Path, package: Path, baseline: object, allowance: str = "0") -> CommandResult:
    """Save `baseline` in the package and compare with it."""
    (package / "baseline.json").write_text(json.dumps(baseline))
    return run_checker(installed, package, "--costs", "--baseline", "baseline.json", "--allowance", allowance)


def measured_records(baseline: dict[str, list[dict[str, object]]]) -> list[dict[str, object]]:
    """The records of the library Measured in a baseline."""
    return next(library for library in baseline["libraries"] if library["name"] == "Measured")["records"]


def test_report_lists_proofs_and_unmeasured_theorems(runtime_root: Path, tmp_path: Path) -> None:
    """`runCosts` (`ProofCostRun.lean`): the report shows stable proofs, marks private and anonymous names, and lists a
    module compiled without collection as unmeasured, without generated helpers; a repeat is byte-identical and no
    artifact changes."""
    installed, package = make_consumer(runtime_root, tmp_path)
    before = {path: path.stat().st_mtime_ns for path in (package / ".lake/build").rglob("*") if path.is_file()}
    result = run_checker(installed, package, "--costs")
    assert result.returncode == 0, result.diagnostic()
    text = result.stdout
    assert "Library Measured: 2 measured proofs" in text and "theorem  cheap" in text and "theorem  costly" in text
    assert "Unstable names, which a baseline does not compare" in text and "hidden" in text and "example" in text
    assert "Library Plain: 0 measured proofs" in text and "Plain  unmeasured" in text and "Plain  withHelper" in text
    assert "helper" not in text.replace("withHelper", "") and "sizeOf" not in text and "eq_" not in text, text
    assert run_checker(installed, package, "--costs").stdout == text
    selected = run_checker(installed, package, "--costs", "--library", "Plain")
    assert "Library Measured" not in selected.stdout and "Library Plain" in selected.stdout
    assert {path: path.stat().st_mtime_ns for path in (package / ".lake/build").rglob("*") if path.is_file()} == before


def test_json_report_is_the_baseline(runtime_root: Path, tmp_path: Path) -> None:
    """`costsJson` (`ProofCostReport.lean`): the JSON has the unit, exact integer counts and the data that makes counts
    comparable; comparing a library with its own report finds nothing, whatever the allowance."""
    installed, package = make_consumer(runtime_root, tmp_path)
    baseline = baseline_of(installed, package)
    assert baseline["unit"] == "internal-heartbeat"
    records = measured_records(baseline)
    assert {record["declaration"] for record in records if record["identity"] == "stable"} == {"cheap", "costly"}
    assert all(isinstance(record["heartbeats"], int) and record["compiler"] and record["scheme"] for record in records)
    for allowance in ("0", "2.5", "0.001"):
        result = compare(installed, package, baseline, allowance)
        assert result.returncode == 0, result.diagnostic()
    assert {path.name for path in package.iterdir()} >= {"baseline.json"}
    assert json.loads((package / "baseline.json").read_text()) == baseline, "the tool wrote the baseline"


def test_growth_at_the_allowance_boundary(runtime_root: Path, tmp_path: Path) -> None:
    """`compareLibrary` (`ProofCostCompare.lean`): a count exactly at baseline plus allowance passes and one internal
    unit more is growth that fails the run."""
    installed, package = make_consumer(runtime_root, tmp_path)
    baseline = baseline_of(installed, package)
    next(record for record in measured_records(baseline) if record["declaration"] == "costly")["heartbeats"] -= 1000
    assert compare(installed, package, baseline, "1").returncode == 0
    result = compare(installed, package, baseline, "0.999")
    assert result.returncode == 1 and "Grew by more than the allowance" in result.stdout, result.diagnostic()
    assert "costly" in result.stdout.split("Grew by more than the allowance")[1]


def test_allowance_is_validated(runtime_root: Path, tmp_path: Path) -> None:
    """`parseUnits` and `parseArguments` (`ProofCostUnits.lean`, `ProofCostArguments.lean`): an allowance with more than three
    places, a negative one, a missing one, and options of the wrong mode are usage errors that name what to change."""
    installed, package = make_consumer(runtime_root, tmp_path)
    (package / "baseline.json").write_text(json.dumps(baseline_of(installed, package)))
    for arguments, message in [(("--costs", "--baseline", "baseline.json", "--allowance", "0.0001"), "at most three decimal places"),
                               (("--costs", "--baseline", "baseline.json", "--allowance", "-1"), "at most three decimal places"),
                               (("--costs", "--baseline", "baseline.json"), "--baseline needs --allowance"),
                               (("--costs", "--allowance", "1"), "--allowance needs --baseline"),
                               (("--json",), "work only with --costs"),
                               (("--costs", "--json", "--baseline", "baseline.json", "--allowance", "1"), "cannot be combined")]:
        result = run_checker(installed, package, *arguments)
        assert result.returncode == 2 and message in result.stderr, (arguments, result.diagnostic())


def test_baseline_sections_are_separate(runtime_root: Path, tmp_path: Path) -> None:
    """`compareLibrary` and `runCosts`: another compiler is incompatible (exit 2), an entry that is gone or whose module
    was compiled without collection has no completed count (exit 1), a new entry is only reported (exit 0), and an unusable baseline
    is an error."""
    installed, package = make_consumer(runtime_root, tmp_path)
    baseline = baseline_of(installed, package)
    cheap = next(record for record in measured_records(baseline) if record["declaration"] == "cheap")
    foreign = json.loads(json.dumps(baseline))
    next(record for record in measured_records(foreign) if record["declaration"] == "cheap")["compiler"] = "0.0.0"
    result = compare(installed, package, foreign)
    assert result.returncode == 2 and "Not comparable" in result.stdout, result.diagnostic()
    removed = json.loads(json.dumps(baseline))
    measured_records(removed).append({**cheap, "declaration": "gone"})
    result = compare(installed, package, removed)
    assert result.returncode == 1 and "no such theorem now" in result.stdout, result.diagnostic()
    unmeasured = json.loads(json.dumps(baseline))
    plain = next(library for library in unmeasured["libraries"] if library["name"] == "Plain")
    plain["records"].append({**cheap, "module": "Plain", "declaration": "unmeasured"})
    result = compare(installed, package, unmeasured)
    assert result.returncode == 1 and "compiled without collection" in result.stdout, result.diagnostic()
    added = json.loads(json.dumps(baseline))
    added_records = measured_records(added)
    added_records.remove(next(record for record in added_records if record["declaration"] == "cheap"))
    result = compare(installed, package, added)
    assert result.returncode == 0 and "Added, not in the baseline" in result.stdout, result.diagnostic()
    for text, message in [("not json", "is not JSON"), ("{}", "unexpected shape")]:
        (package / "baseline.json").write_text(text)
        result = run_checker(installed, package, "--costs", "--baseline", "baseline.json", "--allowance", "0")
        assert result.returncode == 2 and message in result.stderr, result.diagnostic()
    result = run_checker(installed, package, "--costs", "--baseline", "absent.json", "--allowance", "0")
    assert result.returncode == 2 and "does not exist" in result.stderr


def test_changed_source_is_stale_and_a_failed_recompile_leaves_nothing_to_read(runtime_root: Path, tmp_path: Path) -> None:
    """`readModuleCosts` (`ProofCostModuleData.lean`) and `libraryCosts` (`ProofCostRun.lean`): a module whose Lean file
    changed after its compile is an error with the build command. When the recompile fails, Lake deletes the compiled
    file, so the error is a missing compiled file with the same advice; the old counts are never reported."""
    installed, package = make_consumer(runtime_root, tmp_path)
    source = package / "lean/Measured.lean"
    source.write_text(MEASURED + "\n-- an edit\n")
    result = run_checker(installed, package, "--costs", "--library", "Measured")
    assert result.returncode == 2 and "module Measured changed after it was compiled" in result.stderr, result.diagnostic()
    assert "run lake build Measured" in result.stderr
    source.write_text(MEASURED + "theorem broken : False := by trivial\n")
    assert lake_build(installed, package, "Measured").returncode != 0
    result = run_checker(installed, package, "--costs", "--library", "Measured")
    assert result.returncode == 2 and "has no compiled file" in result.stderr and "cheap" not in result.stdout, result.diagnostic()
    assert "run lake build Measured" in result.stderr
    source.write_text(MEASURED)
    assert lake_build(installed, package, "Measured").returncode == 0
    assert run_checker(installed, package, "--costs", "--library", "Measured").returncode == 0
