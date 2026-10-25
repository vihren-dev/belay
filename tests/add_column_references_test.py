"""Native SQLite checks ADD COLUMN with REFERENCES and a default, with foreign keys on and off."""

import json
from dataclasses import replace
from pathlib import Path

import pytest

from conformance.authored_resolution import profile
from conformance.model_check import compiled_many, prove_all
from conformance.native_record import record_sql
from conformance.native_replay import prepare
from conformance.sql_text import runtime_translator

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.kernel,
              pytest.mark.requires_lean, pytest.mark.requires_native("translation-program", "sqlite3")]

PARENT = "CREATE TABLE p(k PRIMARY KEY); INSERT INTO p VALUES(1),(99);"
EMPTY = PARENT + "CREATE TABLE c(a);"
POPULATED = EMPTY + "INSERT INTO c VALUES(5),(6);"
STRICT_POPULATED = PARENT + "CREATE TABLE c(a INTEGER) STRICT; INSERT INTO c VALUES(5),(6);"

DEFAULTS: list[tuple[str, bool]] = [
    ("", False), ("DEFAULT NULL", False), ("DEFAULT null", False),
    ("DEFAULT 5 DEFAULT NULL", False), ("DEFAULT 99", True), ("DEFAULT 5", True),
    ("DEFAULT 'x'", True), ("DEFAULT TRUE", True),
    ("DEFAULT NULL DEFAULT 99", True), ("NOT NULL DEFAULT 99", True),
]
"""Each default clause after the written REFERENCES, with whether SQLite 3.51.0 rejects it on a
nonempty table while foreign keys are enforced: only a last DEFAULT that is the bare literal NULL
or no default is accepted."""
UNSUPPORTED: list[tuple[str, bool]] = [
    ("DEFAULT (NULL)", False), ("DEFAULT (+NULL)", True), ("DEFAULT (1)", True), ("DEFAULT +NULL", False),
    ("DEFAULT -NULL", True)]
"""Defaults that the model does not decide, with native SQLite's refusal: parenthesized defaults other
than a parameter are not translated, and a unary sign before NULL has no column default value in the
model (also without REFERENCES). Native accepts the bare `+NULL`, unlike the expression `(+NULL)`."""


def contract_cases() -> list[tuple[str, str, bool, bool, str]]:
    """The (name, setup, enforcement, expected refusal, ADD COLUMN SQL) of every compared case."""
    cases: list[tuple[str, str, bool, bool, str]] = []
    for default, rejects in DEFAULTS:
        add = f"ALTER TABLE c ADD COLUMN y REFERENCES p(k) {default}"
        for enforced in (True, False):
            cases.append(("populated", POPULATED, enforced, enforced and rejects, add))
        cases.append(("empty", EMPTY, True, False, add))
    check = "ALTER TABLE c ADD COLUMN y REFERENCES p(k) CHECK(y IS NULL) DEFAULT 99"
    cases.extend([("check-populated", POPULATED, True, True, check), ("check-populated-off", POPULATED, False, True, check),
                  ("check-empty", EMPTY, True, False, check)])
    clock = "ALTER TABLE c ADD COLUMN y REFERENCES p(k) DEFAULT CURRENT_TIMESTAMP"
    cases.extend([("clock-populated", POPULATED, True, True, clock), ("clock-populated-off", POPULATED, False, True, clock),
                  ("clock-empty", EMPTY, True, False, clock), ("clock-empty-off", EMPTY, False, False, clock)])
    reordered = "ALTER TABLE c ADD COLUMN y DEFAULT 99 REFERENCES p(k) ON DELETE CASCADE DEFERRABLE INITIALLY DEFERRED"
    cases.append(("reordered", POPULATED, True, True, reordered))
    cases.append(("missing-parent", POPULATED, True, True, "ALTER TABLE c ADD COLUMN y REFERENCES nope DEFAULT 5"))
    cases.append(("missing-parent-null", POPULATED, True, False, "ALTER TABLE c ADD COLUMN y REFERENCES nope"))
    cases.append(("no-reference", POPULATED, True, False, "ALTER TABLE c ADD COLUMN y DEFAULT 99"))
    cases.append(("strict", STRICT_POPULATED, True, True, "ALTER TABLE c ADD COLUMN y INTEGER REFERENCES p(k) DEFAULT 99"))
    cases.append(("strict-null", STRICT_POPULATED, True, False, "ALTER TABLE c ADD COLUMN y INTEGER REFERENCES p(k)"))
    cases.append(("not-null-null", POPULATED, True, True, "ALTER TABLE c ADD COLUMN y REFERENCES p(k) NOT NULL DEFAULT NULL"))
    return cases


def run_script(add: str) -> str:
    """The migration: the ADD COLUMN, a control column after it and the rows."""
    return f"{add}; ALTER TABLE c ADD COLUMN z INTEGER DEFAULT 7; SELECT * FROM c;"


def test_add_references_matches_native(runtime_root: Path, tmp_path: Path) -> None:
    """The model refuses the ADD COLUMN exactly when native SQLite does, and keeps the table, rows and
    the next statement's result: it checks the resolver flag, the refusal in `step`, the output column
    name and the frame after a refused statement against native SQLite as oracle."""
    translator = runtime_translator(runtime_root)
    prepared, expected = [], []
    for index, (name, setup, enforced, refused, add) in enumerate(contract_cases()):
        record = record_sql(setup, run_script(add), name=f"add-references-{index}", outputs=True,
                            profile=replace(profile(()), foreign_keys=enforced), run_on=True)
        assert (record["trace"][0]["primaryCode"] == 1) is refused, (name, add, enforced, record["trace"][0])
        case, error = prepare(record, translator)
        assert case is not None, (add, error)
        prepared.append(case)
        expected.append((name, enforced, add))
    answers = compiled_many(prepared, runtime_root, emit_lean=True)
    for answer, label in zip(answers, expected, strict=True):
        if answer["verdict"] != "AGREE":
            diagnostic = tmp_path / "disagreement.json"
            diagnostic.write_text(json.dumps({"case": label, "answer": answer}, indent=2))
            pytest.fail(f"ADD COLUMN REFERENCES disagrees for {label}; details: {diagnostic}")
    prove_all([answer["caseLean"] for answer in answers], runtime_root, tmp_path, cases=prepared, name="AddReferences")


@pytest.mark.parametrize("default,rejects", UNSUPPORTED, ids=[default for default, _ in UNSUPPORTED])
def test_unsupported_default_is_outside_the_model(default: str, rejects: bool, runtime_root: Path) -> None:
    """Native SQLite treats `(NULL)` and the bare `+NULL` as the literal and `(+NULL)` as an expression.
    The model decides none of these spellings: the harness reports them as unsupported instead of
    agreeing or disagreeing, so no claim rests on them."""
    add = f"ALTER TABLE c ADD COLUMN y REFERENCES p(k) {default}"
    record = record_sql(POPULATED, add, name="add-references-paren", outputs=True,
                        profile=replace(profile(()), foreign_keys=True), run_on=True)
    assert (record["trace"][0]["primaryCode"] == 1) is rejects, record["trace"][0]
    case, error = prepare(record, runtime_translator(runtime_root))
    verdict = error["verdict"] if case is None else compiled_many([case], runtime_root)[0]["verdict"]
    assert verdict == "MODEL_UNSUPPORTED", (default, verdict)
