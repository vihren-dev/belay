"""Native SQLite checks ADD COLUMN of a NOT NULL column with each spelling of a NULL default.

SQLite 3.51.0 refuses the column on a nonempty table ("Cannot add a NOT NULL column with default value
NULL") only when the written default is the literal NULL: `NULL` and `(NULL)`, and the bare `+NULL`, whose
grammar drops the plus. A sign or a cast of NULL (`-NULL`, `(+NULL)`, `(-NULL)`, `(CAST(NULL AS INT))`) is an
expression that evaluates to NULL: SQLite adds the column and stores NULL in the existing rows. The model
decides only the spelling `NULL`; every other spelling is outside the model, which the harness reports as
unsupported instead of agreeing or disagreeing, so no claim rests on them (task
`plans/20261024-foreign-key-atoms.task.md`, the ADD COLUMN default correction).
"""

import json
from pathlib import Path

import pytest

from conformance.authored_resolution import profile
from conformance.model_check import compiled_many, prove_all
from conformance.native_record import record_sql
from conformance.native_replay import prepare
from conformance.sql_text import runtime_translator

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.kernel,
              pytest.mark.requires_lean, pytest.mark.requires_native("translation-program", "sqlite3")]

EMPTY = "CREATE TABLE t(a);"
POPULATED = EMPTY + "INSERT INTO t VALUES(1);"
READ_BACK = "SELECT a, b FROM t;"
"""The rows after the statement: they show the stored NULL, or the unchanged table."""

FORMS: list[tuple[str, bool, bool]] = [
    ("NULL", True, True), ("+NULL", True, False), ("-NULL", False, False), ("(NULL)", True, False),
    ("(+NULL)", False, False), ("(-NULL)", False, False), ("(CAST(NULL AS INT))", False, False)]
"""Each written default with whether SQLite 3.51.0 refuses it on a populated table, and whether the
model decides it. The empty table accepts every form."""


@pytest.mark.parametrize("default,refused,decided", FORMS, ids=[form[0] for form in FORMS])
def test_null_default_spelling_matches_native(default: str, refused: bool, decided: bool, runtime_root: Path,
                                              tmp_path: Path) -> None:
    """Native SQLite refuses a populated table exactly for the literal spellings; the model agrees with
    the native run of the spelling that it decides, on both tables, and leaves the others unsupported."""
    translator = runtime_translator(runtime_root)
    add = f"ALTER TABLE t ADD COLUMN b INT NOT NULL DEFAULT {default}; {READ_BACK}"
    prepared, refusals = [], []
    for table, setup, rejects in (("empty", EMPTY, False), ("populated", POPULATED, refused)):
        record = record_sql(setup, add, name=f"not-null-default-{table}", outputs=True, profile=profile(()),
                            run_on=True)
        assert (record["trace"][0]["primaryCode"] == 1) is rejects, (default, table, record["trace"][0])
        case, error = prepare(record, translator)
        if case is None:
            refusals.append(error["verdict"])
        else:
            prepared.append(case)
    answers = compiled_many(prepared, runtime_root, emit_lean=True) if prepared else []
    verdicts = refusals + [answer["verdict"] for answer in answers]
    if not decided:
        assert verdicts == ["MODEL_UNSUPPORTED"] * 2, (default, verdicts)
        return
    for answer in answers:
        if answer["verdict"] != "AGREE":
            diagnostic = tmp_path / "disagreement.json"
            diagnostic.write_text(json.dumps({"default": default, "answer": answer}, indent=2))
            pytest.fail(f"NOT NULL default {default} disagrees; details: {diagnostic}")
    prove_all([answer["caseLean"] for answer in answers], runtime_root, tmp_path, cases=prepared, name="NotNullDefault")
