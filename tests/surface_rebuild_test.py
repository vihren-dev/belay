"""The table rebuild of the guide: tactic rules for schema statements and the three claims about the rebuild
(ADR 0017, S6, part 2)."""

from pathlib import Path
import re
import shutil

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import CHAIN_TEST_TIMEOUT_SECONDS
from tests.sql_file_support import installed_layout, toolchain_environment
from tests.surface_support import EXAMPLE
from tests.surface_assertion_examples_test import check_module_chain, lines_after
from tests.surface_replay_test import model_cell, native_replay, native_rows

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.timeout(CHAIN_TEST_TIMEOUT_SECONDS)]

EXPECTED_ROWS: dict[str, list[list[object]]] = {
    "right": [[10, 1, 100]],
    "wrong-enforced": [],
    "with-blob": [["sessions", 10, "customers", 0], [10, 1, 100]],
    "dangling": [["sessions", 11, "customers", 0], [10, 1, 100], [11, 99, 200]],
    "copy-audit": [[7]],
    "copy-foreign-key": [[0]],
    "copy-implicit": [[20], [30]],
}
"""The rows from the rebuild or copy replay that Belay and pinned SQLite must both return."""

EXPECTED_ERRORS: dict[str, list[tuple[int, str]]] = {
    "right": [], "wrong-enforced": [], "with-blob": [(19, "cannot store BLOB value in TEXT column")], "dangling": [],
    "copy-audit": [], "copy-foreign-key": [(19, "FOREIGN KEY constraint failed")],
    "copy-implicit": [],
}
"""The shared constraint code and pinned SQLite message for each model error, in output order."""

CHAIN_TIMEOUT_SECONDS = 400
"""The time limit of one fixture module, and of the Lake build of the example project, in seconds."""

PROOF_MODULES = ("RebuildGuide", "RebuildKeepsInvariant", "RebuildCopyFacts", "RebuildSucceedsCopy",
                 "RebuildKeeps", "RebuildSucceeds")
"""The modules of the example's folder `Proof`, which Lake compiles in a build of the example."""


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
    them, and a customer whose email is a blob makes the copy into the STRICT table fail (the rebuilt table stays
    empty, and the pragma foreign_key_check then reports the session, but the commit does not stop). The last replay has a session of a
    customer that does not exist: the pragma reports it and the rebuild still commits. Two further replays
    check that a copy fires its audit trigger and that a missing parent rejects the copy with error 19.
    The implicit-rowid replay checks the stored values and inspects the rowids that SQLite assigned."""
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
        for error, line, (code, message) in zip(modeled_errors, refusals, EXPECTED_ERRORS[name], strict=True):
            assert error == {"error": code} and line.endswith(f"({code})") and message in line, (name, error, line)
    rowids = run_command([sqlite, "-json", str(tmp_path / "copy-implicit.db"),
                          "SELECT rowid FROM old ORDER BY rowid; SELECT rowid FROM fresh ORDER BY rowid"],
                         cwd=tmp_path, timeout=10)
    assert rowids.returncode == 0 and native_rows(rowids.stdout) == [[2], [3], [1], [2]], rowids.diagnostic()


def test_sql_refute_refutes_the_wrong_rebuild(runtime_root: Path, tmp_path: Path) -> None:
    """`sql_refute` certifies that the wrong rebuild of the guide, started on a connection with foreign keys on,
    does not preserve the sessions: it finds the sample database in which the rebuild succeeds and the sessions
    change from one row to none (the fixture RebuildRefutation). The proof uses only logical axioms. The test
    test_rebuild_replays_agree_with_pinned_sqlite shows the same loss on pinned SQLite."""
    check_module_chain(runtime_root, tmp_path, (("RebuildGuide", 0), ("RebuildRefutation", 1)),
                       timeout=CHAIN_TIMEOUT_SECONDS)


def test_example_project_of_the_readme_builds_checks_and_proves_its_claims(runtime_root: Path, tmp_path: Path) -> None:
    """The README's rebuild example is the Lake project `examples/table-rebuild`, which requires Belay by the path
    `../../packages/belay`. Lake builds it from the installed packages without compiling them again. Its claims use
    `on shop`, and the check takes the schema from the premise of each claim (`CheckDomain.domainSchemas`): in
    TableRebuild, `badMigration preserves allSessions on shop` answers false with one customer and one session of
    that customer; in FixedSucceeds, `fixedMigration succeeds on shop` answers false with a customer whose email is a
    blob, which the STRICT copy refuses with error 19. The replays build those databases from SQL text. The two
    theorems reuse the proofs of RebuildKeeps and RebuildSucceeds in the folder `Proof` and use only logical axioms.
    The test pins the answers that the README prints, and keeps the example's lakefile from breaking."""
    installed = installed_layout(runtime_root, tmp_path)
    example = installed / "examples/table-rebuild"
    shutil.copytree(EXAMPLE, example, ignore=shutil.ignore_patterns(".lake", "lake-manifest.json"))
    result = run_command([str(installed / "lean/bin/lake"), "build", "--no-ansi"], cwd=example,
                         timeout=CHAIN_TIMEOUT_SECONDS, environment=toolchain_environment(installed))
    assert result.returncode == 0, result.diagnostic()
    output = result.stdout
    assert {*PROOF_MODULES, "TableRebuild", "FixedSucceeds"} <= set(re.findall(r"Built (\S+)", output)), output
    assert "sorryAx" not in output and "error:" not in output, output
    lost, refused = output.split("SQL check: false.\n")[1:3]
    assert lost.startswith("Database:\ncustomers:\n  id | name | email\n  1  | NULL | ''\nsessions:\n"
                           "  id | customer_id | expires_at\n  1  | 1           | 0\n"), output
    assert "allSessions: rows [[1, 1, 0]]" in lost, output
    assert "badMigration, statement 5: done 1\n" in lost, output
    assert 'INSERT INTO "sessions" ("id", "customer_id", "expires_at") VALUES (1, 1, 0);' in \
        lost.split("SQLite replay:\n", 1)[1], output
    assert refused.startswith("Database:\ncustomers:\n  id | name | email\n  1  | NULL | X''\nsessions:\n"
                              "  id | customer_id | expires_at\n  (no rows)\n"), output
    assert "fixedMigration, statement 4: error 19\n" in refused, output
    assert 'INSERT INTO "customers" ("id", "name", "email") VALUES (1, NULL, X\'\');' in \
        refused.split("SQLite replay:\n", 1)[1], output
    for theorem in ("fixed_keeps_sessions", "fixed_succeeds"):
        assert f"'{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]" in output, output


def test_rebuild_preserves_all_sessions_on_every_database_of_the_schema(runtime_root: Path, tmp_path: Path) -> None:
    """KeptRead proves that the rebuild preserves the sessions read on the guide's schema.
    RebuildTableFrames checks the moving table. KeptReadChecks rejects the cascading rebuild
    and a final read redirected to another table. The proof uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (
        ("RebuildGuide", 0), ("RebuildKeepsInvariant", 0), ("RebuildTableFrames", 0), ("KeptReadChecks", 0),
        ("RebuildKeeps", 1)), timeout=CHAIN_TIMEOUT_SECONDS)


def test_rebuild_succeeds_when_every_customer_fits_the_strict_types(runtime_root: Path, tmp_path: Path) -> None:
    """The schema success check discharges every rebuild statement except the copy.
    SchemaSuccessChecks covers whole scripts and the transaction and foreign-key boundaries.
    RebuildCopyChecks checks the allowed NOT NULL weakening and incompatible source and target columns.
    It also compares the table and partial-index scans of a copying SELECT.
    RebuildSucceeds supplies the STRICT row premise for the copy and proves success on every branch.
    The final proof uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (
        ("RebuildGuide", 0), ("RebuildKeepsInvariant", 0), ("RebuildCopyFacts", 0), ("RebuildCopyChecks", 0),
        ("RebuildSucceedsCopy", 0),
        ("SchemaSuccessChecks", 0),
        ("RebuildKeeps", 1), ("RebuildSucceeds", 1)), timeout=CHAIN_TIMEOUT_SECONDS)
