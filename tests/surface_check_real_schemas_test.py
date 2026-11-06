"""`#sql_check` finds the counterexamples of issues #318 and #293 on the tables that a developer has."""

import shutil
from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import split_blocks
from tests.surface_replay_test import native_replay
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

LABELS = ("one-plain", "one-checked", "two-plain", "two-checked", "two-checked-db", "primary-key", "altered")
"""The labelled claims of the fixture; each one is false at the default budget."""


@pytest.mark.timeout(400)
@pytest.mark.requires_native("sqlite3")
def test_claims_on_real_schemas_are_false(runtime_root: Path, tmp_path: Path) -> None:
    """Sampling.suppliedVariants gives the row that collides with the supplied row under NOCASE, and
    Replay.schemaRowsSql builds the generated database from the schema's text with its key and CHECK, so
    every claim of the fixture is false at the default budget. With (db := twoChecked) alone, the
    counterexample has the supplied schema and row. Native SQLite builds the table from the replay and
    fails on the unique index."""
    result = run_command(surface_command(runtime_root, FIXTURES / "CheckRealSchemas.lean", tmp_path),
                         cwd=tmp_path, timeout=380)
    assert result.returncode == 0, result.diagnostic()
    blocks = split_blocks(result.stdout)
    for label in LABELS:
        assert blocks[label].startswith("SQL check: false."), (label, blocks[label])
    block = blocks["two-checked-db"]
    assert "'ann@x.io'" in block and "'Ann@x.io'" in block, block
    script = block.split("SQLite replay:\n", 1)[1]
    assert "CHECK (instr(email, '@') > 1 AND length(email) >= 5)" in script, script
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    replay = native_replay(sqlite, script, tmp_path, "two-checked-db")
    assert replay.stdout.split() == ['[{"1":1}]'], replay.diagnostic()
    assert "UNIQUE constraint failed: customers.email" in replay.stderr, replay.diagnostic()


@pytest.mark.timeout(400)
@pytest.mark.requires_native("sqlite3")
def test_altered_schema_replay_inserts_rows_with_the_triggers_off(runtime_root: Path, tmp_path: Path) -> None:
    """Replay.schemaRowsSql and CheckReplayData.constructionWithoutTriggersMatches: a candidate on a schema
    text with a trigger and an ALTER TABLE is built from the text without its INSERT, then its rows with
    `.dbconfig enable_trigger off`. Native SQLite builds the same rows, so the trigger adds no audit row, and
    the replay fails on the unique index."""
    result = run_command(surface_command(runtime_root, FIXTURES / "CheckRealSchemas.lean", tmp_path),
                         cwd=tmp_path, timeout=380)
    assert result.returncode == 0, result.diagnostic()
    block = split_blocks(result.stdout)["altered"]
    assert block.startswith("SQL check: false."), block
    script = block.split("SQLite replay:\n", 1)[1]
    assert "ALTER TABLE customers ADD COLUMN name TEXT;" in script, script
    assert ".dbconfig enable_trigger off\n" in script and ".dbconfig enable_trigger on\n" in script, script
    assert "INSERT INTO customers VALUES (1, 'ann@x.io', 'Ann')" not in script, script
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    construction = script.split("\n;\n", 1)[0] + "\n"
    audit = native_replay(sqlite, construction + "SELECT count(*) AS n FROM audit;\n", tmp_path, "altered-audit")
    assert audit.returncode == 0 and not audit.stderr, audit.diagnostic()
    # Native SQLite has the audit rows of the counterexample (its text has one line per row, or
    # "(no rows)"); with the triggers on, each customer row would add one more.
    audit_rows = block.split("audit:\n  note\n", 1)[1].split("\nnoDuplicateEmails", 1)[0].split("\n")
    expected = 0 if audit_rows == ["  (no rows)"] else len(audit_rows)
    # The shell prints each `.dbconfig` setting that it changes, then the count.
    lines = audit.stdout.split("\n")
    assert lines[0].split() == ["enable_trigger", "off"], audit.diagnostic()
    assert lines[-2] == f'[{{"n":{expected}}}]', (expected, audit.diagnostic())
    replay = native_replay(sqlite, script, tmp_path, "altered")
    assert "UNIQUE constraint failed: customers.email" in replay.stderr, replay.diagnostic()
