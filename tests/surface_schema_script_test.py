"""The step, frame and success laws of the schema, transaction and pragma statements (ADR 0017, S6)."""

from pathlib import Path
import re
import shutil

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import CHAIN_TEST_TIMEOUT_SECONDS
from tests.surface_assertion_examples_test import check_module_chain, lines_after
from tests.surface_replay_test import model_cell, native_replay, native_rows

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.requires_native("sqlite3")]

EXPECTED_ROWS: dict[str, list[list[object]]] = {
    "drop-off": [[10, 1, "a"], [11, 2, "b"], [12, 2, "c"]],
    "drop-on": [],
    "refusals": [[0], [1], [3]],
    "inserts": [[1, "a"], [2, "b"]],
    "literals": [[1, "a"], [2, "b"], [9, "a"], [10, "b"], [12, None]],
}
"""The rows that the model gives for each replay, which pinned SQLite must give too."""

EXPECTED_ERRORS: dict[str, list[str]] = {
    "drop-off": [],
    "drop-on": [],
    "refusals": ["already exists", "no such table", "no transaction is active",
                 "cannot start a transaction within a transaction"],
    "literals": ["UNIQUE constraint failed", "UNIQUE constraint failed", "UNIQUE constraint failed"],
    "inserts": ["NOT NULL constraint failed", "UNIQUE constraint failed", "CHECK constraint failed",
                "cannot store TEXT value in INTEGER column"],
}
"""The refusal that pinned SQLite gives for each error output of the model, in order."""


def test_schema_laws_on_concrete_databases_agree_with_pinned_sqlite(runtime_root: Path, tmp_path: Path) -> None:
    """The fixtures SchemaDropExamples, SchemaCreateExamples, ControlStepExamples, CertificateAfterDrop and
    InsertSelectExamples and PlainInsertStepCases (with the helpers of SchemaStepLaws) apply the
    step, frame and success laws of CREATE TABLE, DROP TABLE, BEGIN, COMMIT, the pragmas foreign_keys and
    foreign_key_check, and INSERT from a query or literal rows to concrete databases. The literal insert
    derives success from validity, and checks an allocated rowid, a secondary UNIQUE key,
    the change count, the last rowid, stored values and two new names that conflict under NOCASE. DROP TABLE with foreign keys on
    cascades into the observed table. Other fixtures cover a read certificate that survives the drop of an earlier table and
    a failing case for each premise of the success law of INSERT from a query. Every theorem uses only logical
    axioms. The fixture SchemaScriptReplays emits scripts of the same statements. Pinned SQLite 3.51.0 gives the
    rows that the model gives, and refuses the statements that the model refuses, in the same order."""
    stdout = check_module_chain(runtime_root, tmp_path, (
        ("SchemaStepLaws", 0), ("SchemaDropExamples", 4), ("SchemaCreateExamples", 3), ("ControlStepExamples", 7),
        ("CertificateAfterDrop", 2), ("InsertSelectExamples", 6), ("PlainInsertStepCases", 2), ("SchemaScriptReplays", 0)))
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


@pytest.mark.timeout(CHAIN_TEST_TIMEOUT_SECONDS)
def test_replaced_laws_follow_from_the_kind_rules(runtime_root: Path, tmp_path: Path) -> None:
    """The fixtures ReplacedStepLaws and ReplacedSendLaws restate seven model laws and three surface laws with their
    old statements. The task file of the statement rule pilot lists these laws in "Replaced laws". The proofs
    use the kind rules runScriptStep_createTable_eq and runScriptStep_plainInsert_eq, the data facts of CREATE TABLE
    and plain INSERT, and the bridge Sql.check_send_of_rule. The check shows that the replacement of the
    old laws loses no fact. Every theorem uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("ReplacedGeneralSend", 3), ("ReplacedFailureFrames", 2), ("ReplacedStepLaws", 7), ("ReplacedSendLaws", 3)))


@pytest.mark.timeout(CHAIN_TEST_TIMEOUT_SECONDS)
def test_client_claims_on_items_follow_from_the_kind_rules(runtime_root: Path, tmp_path: Path) -> None:
    """The fixtures ItemInsertSite, ItemInsertOutcomes, ItemInsertClaims and ItemInsertAnyClaims prove client
    claims about a table with an INTEGER PRIMARY KEY alias. The proofs use the kind rules of CREATE TABLE and plain
    INSERT through the bridge Sql.check_send_of_rule. On arbitrary valid rows, a new key inserts one row, and an
    existing key fails with code 19 and keeps the database. CREATE TABLE on an empty catalog then INSERT gives a
    table with exactly the new row. sql_run proves that the insert keeps the condition that every stored item has a
    name that is not NULL. For each id, the insert has the output done 1 and the new row after the old rows, or one
    error output and the database before. The chain compiles each module once. Every theorem uses only logical
    axioms."""
    check_module_chain(runtime_root, tmp_path, (("ItemInsertSite", 0), ("ItemInsertOutcomes", 0),
                                                ("ItemInsertClaims", 4), ("ItemInsertAnyClaims", 1)))


def test_exact_plain_write_rules_retain_the_deleted_laws(runtime_root: Path, tmp_path: Path) -> None:
    """The exact UPDATE and DELETE rules prove both former database effects and all four former
    send rules with their original premises and ordinary logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("ReplacedGeneralSend", 3), ("ReplacedFailureFrames", 2), ("ReplacedPlainWriteLaws", 2),
                       ("ReplacedDeleteSendLaws", 2), ("ReplacedUpdateSendLaws", 2)))


def test_exact_control_rules_retain_the_deleted_laws(runtime_root: Path, tmp_path: Path) -> None:
    """The exact transaction and pragma rules imply the original step and send statements
    and prove client claims about an arbitrary valid connection, using ordinary logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("ReplacedGeneralSend", 3), ("ReplacedTransaction", 4), ("ReplacedControlFrame", 3),
                       ("ReplacedSetting", 2), ("ReplacedControlContinuation", 6), ("ReplacedControlSend", 3),
                       ("ControlSendClaims", 4)))


@pytest.mark.timeout(CHAIN_TEST_TIMEOUT_SECONDS)
def test_exact_schema_rules_retain_the_deleted_laws(runtime_root: Path, tmp_path: Path) -> None:
    """The former schema laws follow with their original premises and only logical axioms.
    Eight clients check the effect of each schema kind on variable databases, including
    refused preparations, colliding unique indexes and restricted defaults."""
    check_module_chain(runtime_root, tmp_path, (
        ("ReplacedGeneralSend", 3), ("ReplacedPlainDrop", 3), ("ReplacedCatalogRewrite", 1), ("ReplacedCatalogContinuation", 6),
        ("ReplacedConditionalCreation", 3), ("ReplacedAddColumn", 2), ("ReplacedCatalogSend", 2),
        ("ReplacedColumnSend", 1), ("ReplacedColumnIfOk", 1), ("SchemaSendClaims", 8)))


def test_row_write_send_observes_every_production(runtime_root: Path, tmp_path: Path) -> None:
    """Check the UPSERT and INSERT SELECT equations through sql_run on a variable connection,
    including each admitted source production's count or error and its entry in the trace."""
    check_module_chain(runtime_root, tmp_path, (("RowWriteSendClaims", 2),), timeout=90)


def test_insert_with_rules_reports_its_count_or_error(runtime_root: Path, tmp_path: Path) -> None:
    """Exercise runScriptStep_insertWithRules_eq through sql_run on a variable database
    and check that the client proof uses only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("InsertWithRulesClaim", 1),), timeout=90)


def test_all_returning_and_program_write_modes(runtime_root: Path, tmp_path: Path) -> None:
    """Check the remaining resolved write equations via sql_run, covering the trace of each
    successful and refused write and each production of INSERT SELECT with RETURNING."""
    check_module_chain(runtime_root, tmp_path, (
        ("ProgramWriteClaims", 7), ("ReturningWriteClaims", 4), ("SourceWriteClaims", 4)
    ), timeout=180)


def test_replaced_write_mode_laws(runtime_root: Path, tmp_path: Path) -> None:
    """Check the original DROP program, single-source INSERT SELECT and UPDATE/DELETE
    no-choice declarations using their original premises and only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (
        ("ReplacedProgramDrop", 2), ("ReplacedProductionSuccess", 2), ("ReplacedWriteChoices", 4)
    ), timeout=120)


def test_replaced_group_frames(runtime_root: Path, tmp_path: Path) -> None:
    """The original CREATE and DROP frames use runScriptStep_createTable_eq, runScriptStep_dropPlain_eq and
    runScriptStep_prepareError_eq. The pragma frame uses resolveStatementPragma_readOnly and runScriptStep_readOnly_keeps.
    ReplacedOrdinaryFrames checks runScriptStep_continued_spec, Output.ofStep_isError_of_noHalt,
    runScriptStep_effect and runScriptStep_congr_resolve on nonquery errors, state frames and conditional creation."""
    check_module_chain(runtime_root, tmp_path, (("ReplacedOrdinaryFrames", 5), ("ReplacedSchemaFailures", 2), ("ReplacedReadPragma", 1)))
