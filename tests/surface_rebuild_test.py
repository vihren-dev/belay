"""The table rebuild of the guide: tactic rules for schema statements and the three claims about the rebuild
(ADR 0017, S6, part 2)."""

from pathlib import Path
import re
import shutil

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import CHAIN_TEST_TIMEOUT_SECONDS
from tests.surface_assertion_examples_test import check_module_chain, lines_after
from tests.surface_replay_test import model_cell, native_replay, native_rows

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.timeout(CHAIN_TEST_TIMEOUT_SECONDS)]

EXPECTED_ROWS: dict[str, list[list[object]]] = {
    "right": [[10, 1, 100]],
    "wrong-enforced": [],
    "without-name": [["sessions", 10, "customers", 0], [10, 1, 100]],
    "dangling": [["sessions", 11, "customers", 0], [10, 1, 100], [11, 99, 200]],
}
"""The rows that the model gives for each replay, which pinned SQLite must give too: the rows of the pragma
foreign_key_check, if any, and then the sessions after the rebuild."""

EXPECTED_ERRORS: dict[str, list[str]] = {
    "right": [], "wrong-enforced": [], "without-name": ["NOT NULL constraint failed"], "dangling": [],
}
"""The refusal that pinned SQLite gives for each error output of the model, in order."""

CHAIN_TIMEOUT_SECONDS = 400
"""The time limit of one fixture module, in seconds."""


def test_sql_run_rules_for_schema_and_transaction_statements(runtime_root: Path, tmp_path: Path) -> None:
    """`sql_run` applies its rules for CREATE TABLE, DROP TABLE, a rename, a pragma setting, BEGIN and COMMIT
    (the modules SchemaStepRules and ControlStepRules) to one program on a database with the schema of the
    guide, for every complete environment. The fixture SchemaRuleExamples closes every premise except the final
    claim, which says that the program leaves no open transaction and foreign keys on, and uses only logical
    axioms."""
    check_module_chain(runtime_root, tmp_path, (("RebuildGuide", 0), ("SchemaRuleExamples", 1)),
                       timeout=CHAIN_TIMEOUT_SECONDS)


def test_rebuild_replays_agree_with_pinned_sqlite(runtime_root: Path, tmp_path: Path) -> None:
    """The fixture RebuildReplays runs the rebuild of the guide on four databases of the guide's schema, and
    emits the SQL text with the outputs that the model gives. Pinned SQLite 3.51.0 gives the same rows and
    refusals, in the same order. This checks the model against SQLite for the three facts that the guide's
    rebuild claims rest on: the right order keeps the sessions, foreign keys on before the transaction lose
    them, and a customer without a name makes the copy fail (the rebuilt table stays empty, and the pragma
    foreign_key_check then reports the session, but the commit does not stop). The last replay has a session of a
    customer that does not exist: the pragma reports it and the rebuild still commits."""
    stdout = check_module_chain(runtime_root, tmp_path, (("RebuildGuide", 0), ("RebuildReplays", 0)),
                                timeout=CHAIN_TIMEOUT_SECONDS)
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=tmp_path, timeout=5)
    assert version.returncode == 0 and version.stdout.startswith("3.51.0 "), version.diagnostic()
    reports = {str(report["name"]): report for report in lines_after(stdout, "REPLAY:") if isinstance(report, dict)}
    assert set(reports) == set(EXPECTED_ROWS), stdout
    for name, report in reports.items():
        result = native_replay(sqlite, report["sql"], tmp_path, name)
        outputs = report["outputs"]
        assert isinstance(outputs, list)
        modeled = [[model_cell(cell) for cell in row] for output in outputs for row in output.get("rows", [])]
        assert native_rows(result.stdout) == modeled == EXPECTED_ROWS[name], (name, result.stdout, modeled)
        refusals = re.findall(r"error near line \d+: (.*)", result.stderr)
        modeled_errors = [output for output in outputs if "error" in output]
        assert len(refusals) == len(modeled_errors) == len(EXPECTED_ERRORS[name]), (name, result.stderr)
        for line, expected in zip(refusals, EXPECTED_ERRORS[name], strict=True):
            assert expected in line, (name, line, expected)


def test_sql_refute_refutes_the_wrong_rebuild(runtime_root: Path, tmp_path: Path) -> None:
    """`sql_refute` certifies that the wrong rebuild of the guide, started on a connection with foreign keys on,
    does not preserve the sessions: it finds the sample database in which the rebuild succeeds and the sessions
    change from one row to none (the fixture RebuildRefutation). The proof uses only logical axioms. The test
    test_rebuild_replays_agree_with_pinned_sqlite shows the same loss on pinned SQLite."""
    check_module_chain(runtime_root, tmp_path, (("RebuildGuide", 0), ("RebuildRefutation", 1)),
                       timeout=CHAIN_TIMEOUT_SECONDS)


def test_rebuild_preserves_all_sessions_on_every_database_of_the_schema(runtime_root: Path, tmp_path: Path) -> None:
    """The right rebuild preserves the read of all sessions on every database whose catalog is the guide's schema,
    for every complete environment (claim 1 of the guide). The rebuild is an INSERT from a query, so its branches
    can reach different connections; the fixtures show that every execution of every step keeps the resolution
    state of the sample run and the table of the sessions, which moves from position 1 to position 0
    (RebuildKeepsInvariant, RebuildKeepsFinish), and the certificate of the read (RebuildKeepsRead) turns that into
    the preservation claim (RebuildKeeps). The final proof uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (
        ("RebuildGuide", 0), ("RebuildKeepsInvariant", 0), ("RebuildKeepsFinish", 0), ("RebuildKeepsRead", 0),
        ("RebuildKeeps", 1)), timeout=CHAIN_TIMEOUT_SECONDS)


def test_rebuild_succeeds_when_no_customer_lacks_a_name(runtime_root: Path, tmp_path: Path) -> None:
    """The right rebuild succeeds on every database whose catalog is the guide's schema and in which no customer
    lacks a name, for every complete environment and on every branch of the INSERT from a query (claim 2 of the
    guide). The fixtures show that each of the nine steps continues without an error in every execution and keeps
    the facts of the rebuild (RebuildSucceedsSteps, RebuildSucceedsFinish); the copy needs the old customers to
    hold no NULL name and uses the success law of INSERT from a query (RebuildCopyFacts, RebuildSucceedsCopy). The
    final proof (RebuildSucceeds) uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (
        ("RebuildGuide", 0), ("RebuildKeepsInvariant", 0), ("RebuildCopyFacts", 0), ("RebuildSucceedsCopy", 0),
        ("RebuildSucceedsSteps", 0), ("RebuildKeepsFinish", 0), ("RebuildSucceedsFinish", 0),
        ("RebuildKeepsRead", 0), ("RebuildKeeps", 1), ("RebuildSucceeds", 1)), timeout=CHAIN_TIMEOUT_SECONDS)
