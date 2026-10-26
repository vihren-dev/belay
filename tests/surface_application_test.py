"""Application interfaces, translation and the two simulation theorems (ADR 0017, S8)."""

import json
from pathlib import Path
import re
import shutil

import pytest

from tests.runtime_support import run_command
from tests.surface_assertion_examples_test import check_module_chain
from tests.surface_replay_test import model_cell, native_replay, native_rows
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_interfaces_translation_and_simulations_hold_for_applications(runtime_root: Path, tmp_path: Path) -> None:
    """The installed S8 primitives apply to a shop whose calls have different argument lists, one
    call of two statements and two calls with one script. The program of an application is the
    hand-written program, translation replaces each call by its partner, two witnesses of one
    program translate differently, and the full-state and the scoped theorems hold for an application
    that chooses its later call from an earlier result. The scoped agreement fails for a different
    output, a different value and an unrelated final context. Every theorem uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("ApplicationShop", 5), ("ApplicationSimulations", 7)))


def test_restricted_domain_needs_the_domain_condition(runtime_root: Path, tmp_path: Path) -> None:
    """The domain condition of the full-state simulation is needed. A migration that stores the clock
    of its statement commutes with one read at the start context, because the clock is the same at
    statements 0 and 1. The read leaves the start context, so no simulation exists over it, and the
    application with two reads does not commute with the migration. Every theorem uses only logical
    axioms."""
    check_module_chain(runtime_root, tmp_path, (("ApplicationRestrictedDomain", 4),))


def test_application_branches_keep_choices_errors_stops_and_snapshots(runtime_root: Path, tmp_path: Path) -> None:
    """The branches of an application are the branches of its program. A raw choice between results
    leads to the default call, and each concrete alternative leads to another call. A modeled error is
    an output followed by the next call. A stop ends the application before the next call. A relation
    that names the transaction snapshot tells apart two programs with equal outputs, and a relation
    that ignores it does not. Every theorem uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("ApplicationBranchKinds", 7),))


def test_weak_query_translation_needs_frame_facts_to_become_a_simulation(runtime_root: Path,
                                                                        tmp_path: Path) -> None:
    """A constant query translates weakly across a migration that stores the clock of its statement, and
    still no full-state simulation exists under a clock that changes with the index, because the read
    moves the statement index (fixture ApplicationWeakBridges). When the clock
    gives one date at every index, the read meets the frame facts of the installed query bridge, the
    bridge gives a simulation, and the application with two reads commutes with the migration at every
    admitted context (fixture ApplicationConstantClock). Every theorem uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (
        ("ApplicationRestrictedDomain", 4), ("ApplicationWeakBridges", 2), ("ApplicationConstantClock", 4)))


def lines_after(stdout: str, tag: str) -> list[object]:
    """Decode the JSON that a fixture logged after the tag, one value for each line."""
    return [json.loads(line.removeprefix(tag)) for line in stdout.splitlines() if line.startswith(tag)]


@pytest.mark.requires_native("sqlite3")
def test_expansion_lookups_agree_and_counter_or_clock_calls_break_the_relation(runtime_root: Path,
                                                                               tmp_path: Path) -> None:
    """The lookup theorem of the lowercase-field expansion applies to the customers database and to an
    application that chooses its second lookup from the first result (fixture ApplicationExpansion).
    In fixture ApplicationCounterCalls, the shared write does not commute
    fully with the expansion, a call that reads the total changes breaks the scoped condition of every
    relation that relates the start to its migrated context, and so does a clock read under a clock that
    changes with the index. Pinned SQLite gives the total changes 1 before and 2 after the expansion,
    which are the values the kernel finds. Every theorem uses only logical axioms."""
    stdout = check_module_chain(runtime_root, tmp_path,
                                (("ApplicationExpansion", 3), ("ApplicationCounterCalls", 5)))
    [evidence] = lines_after(stdout, "EXPANSION-TOTALS:")
    assert isinstance(evidence, dict)
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=tmp_path, timeout=5)
    assert version.returncode == 0 and version.stdout.startswith("3.51.0 "), version.diagnostic()
    for name, expected, steps in (("old", evidence["old"], ("setup", "read")),
                                  ("new", evidence["new"], ("setup", "migration", "read"))):
        script = tmp_path / f"{name}.sql"
        script.write_text(";\n".join(evidence[step] for step in steps) + ";\n")
        native = run_command([sqlite, "-batch", "-bail", "-json", ":memory:", f'.read "{script}"'],
                             cwd=tmp_path, timeout=10)
        assert native.returncode == 0 and not native.stderr, native.diagnostic()
        assert [list(row.values()) for row in json.loads(native.stdout)] == [[expected]], (name, native.stdout)
    assert (evidence["old"], evidence["new"]) == (1, 2)


@pytest.mark.requires_native("sqlite3")
def test_missing_trigger_witness_is_checked_by_kernel_and_native_replay(runtime_root: Path,
                                                                        tmp_path: Path) -> None:
    """The expansion without its triggers loses a lookup after a write: the kernel finds the stale result,
    and the relation that names the stored field holds at the start and breaks after the write. The
    full expansion does not have the bug on the same application. Both replays of the witness are
    emitted by the S5 path, and pinned SQLite gives the outputs that the model gives. Every theorem uses
    only logical axioms."""
    stdout = check_module_chain(runtime_root, tmp_path,
                                (("ApplicationExpansion", 3), ("ApplicationMissingTrigger", 8)))
    reports = {str(report["name"]): report for report in lines_after(stdout, "REPLAY:")
               if isinstance(report, dict)}
    assert set(reports) == {"old", "buggy"}, stdout
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    for name, inspect in (("old", ""), ("buggy", "SELECT email_lower FROM customers ORDER BY id;\n")):
        report = reports[name]
        result = native_replay(sqlite, report["sql"], tmp_path, name, inspect)
        assert result.returncode == 0 and not result.stderr, result.diagnostic()
        actual = native_rows(result.stdout)
        outputs = report["outputs"]
        assert isinstance(outputs, list)
        expected = [[model_cell(cell) for cell in row] for output in outputs for row in output.get("rows", [])]
        assert actual[:len(expected)] == expected, (name, actual, expected)
        if name == "old":
            assert expected == [[2]], expected
        else:
            assert expected == [] and actual == [["alpha@x"], [None]], (actual, expected)


@pytest.mark.requires_native("sqlite3")
def test_rollback_loses_the_written_email_in_kernel_and_native_replay(runtime_root: Path,
                                                                       tmp_path: Path) -> None:
    """The reverse direction of the scoped simulation (library theorem ScopedSimulation.reverse) is
    separate from the forward claim. In fixture ApplicationRollback, the forward read agrees at the
    migrated start, the write of the new interface is lost by a rollback that drops the new table, and
    no relation that holds at the rolled-back context makes the reverse pairing a scoped simulation.
    Pinned SQLite gives the two reads that the kernel gives. Every theorem uses only logical axioms."""
    stdout = check_module_chain(runtime_root, tmp_path, (
        ("ApplicationExpansion", 3), ("ApplicationMissingTrigger", 8), ("ApplicationRollback", 4)))
    [report] = [item for item in lines_after(stdout, "REPLAY:") if isinstance(item, dict)]
    assert report["name"] == "rollback"
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    result = native_replay(sqlite, report["sql"], tmp_path, "rollback", "")
    assert result.returncode == 0 and not result.stderr, result.diagnostic()
    outputs = report["outputs"]
    assert isinstance(outputs, list)
    expected = [[model_cell(cell) for cell in row] for output in outputs for row in output.get("rows", [])]
    assert expected == [["b@x"], ["a@x"]], expected
    assert native_rows(result.stdout)[:2] == expected, result.stdout


def test_simulation_syntax_elaborates_to_the_claims_and_explains_the_difference(runtime_root: Path,
                                                                                tmp_path: Path) -> None:
    """The syntax of ApplicationSyntax elaborates each of its forms to the public claim that it names
    (Simulation, or ScopedClaim with a relation), the guard becomes the context predicate, and the
    actual #explain command tells the two claims apart: the full-state claim compares complete final
    contexts, and the scoped claim names the relation and never claims equal final contexts."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ApplicationSyntaxExamples.lean", tmp_path),
                         cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    reports = re.findall(r"depends on axioms: \[([^]]*)\]", result.stdout)
    assert len(reports) == 3, result.diagnostic()
    for report in reports:
        assert set(filter(None, map(str.strip, report.split(",")))) <= {
            "propext", "Classical.choice", "Quot.sound"}, result.diagnostic()
    for written in ("migration simulates samePairing", "migration simulates samePairing where sqlGuard",
                    "migration simulates samePairing scoped by sameClock",
                    "migration simulates samePairing scoped by sameClock where sqlGuard"):
        assert f"Claim: {written}\n" in result.stdout, result.diagnostic()
    assert result.stdout.count("Full-state simulation claim.") == 2, result.diagnostic()
    assert result.stdout.count("Scoped simulation claim.") == 2, result.diagnostic()
    assert result.stdout.count("complete final connection, clock and raw next-statement index exactly") == 2
    assert result.stdout.count("Context relation: sameClock.") == 2, result.diagnostic()
    assert result.stdout.count("Admitted contexts: every execution context") == 2, result.diagnostic()
    assert result.stdout.count("Holds.inContext sqlGuard context") == 2, result.diagnostic()
    assert result.stdout.count("never claims that the final contexts are equal") == 2, result.diagnostic()
    assert "sorryAx" not in result.stdout, result.diagnostic()


@pytest.mark.parametrize("claim,at,message", [
    ('#check (Sql.pure ()) simulates (1 : Nat)', "(1 : Nat)", "type mismatch"),
    ('#check (Sql.pure ()) simulates pairing where sql r"DELETE FROM t"', 'sql r"DELETE', "one read-only statement"),
    ('#check (Sql.pure ()) simulates pairing scoped by 5', "5", "failed to synthesize"),
    ('#explain (Sql.pure ()) simulates pairing scoped by (fun a b => a = b) where sql r"SELECT 1; SELECT 2"',
     'sql r"SELECT', "one read-only statement"),
])
def test_simulation_syntax_reports_mistakes_where_they_are_written(
    runtime_root: Path, tmp_path: Path, claim: str, at: str, message: str,
) -> None:
    """The simulation syntax reports a non-pairing, a guard that is not one read-only query, and a
    relation that is not a relation, each at its own source position, and #explain explains nothing
    for a claim that does not elaborate."""
    source = tmp_path / "SimulationFailure.lean"
    source.write_text("import Belay\nopen Belay.Sqlite Belay.Sqlite.Calls\n"
                      "def pairing : Pairing ({ Argument := fun _ => Unit, Result := fun _ => Unit } : "
                      "Signature Unit) := ⟨fun _ => { script := fun _ => sql r\"SELECT 1\", result := fun _ => () },"
                      " fun _ => { script := fun _ => sql r\"SELECT 1\", result := fun _ => () }⟩\n"
                      f"{claim}\n")
    result = run_command(surface_command(runtime_root, source, tmp_path), cwd=tmp_path, timeout=120)
    assert result.returncode != 0, result.diagnostic()
    assert message.lower() in result.stdout.lower(), result.diagnostic()
    assert f":4:{claim.index(at)}:" in result.stdout, result.diagnostic()
    assert "Full-state simulation claim" not in result.stdout, result.diagnostic()


def test_interface_mistakes_are_diagnosed_where_they_are_written(runtime_root: Path, tmp_path: Path) -> None:
    """Lean rejects each mistake of an interface, pairing or application at its own line: a call
    outside the interface, an argument of the wrong type, a missing entry, an entry with another
    argument type, and a pairing over another signature. The type of a signature is what makes a
    partner exist with the same argument type, so no separate pairing check runs."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ApplicationInterfaceErrors.lean", tmp_path),
                         cwd=tmp_path, timeout=120)
    assert result.returncode != 0, result.diagnostic()
    errors = re.findall(r"ApplicationInterfaceErrors\.lean:(\d+):\d+: error[^:]*: (.*)", result.stdout)
    assert [line for line, _ in errors] == ["31", "34", "38", "43", "55"], result.diagnostic()
    text = {int(line): message for line, message in errors}
    assert "Unknown constant `ApplicationInterfaceErrors.Call.remove`" in text[31]
    assert "Application type mismatch" in text[34] and "expected to have type" in result.stdout
    assert "Missing cases" in text[38] and "Call.find" in result.stdout
    assert "Type mismatch" in text[43]
    assert "Application type mismatch" in text[55] and "Interface otherSignature" in result.stdout
