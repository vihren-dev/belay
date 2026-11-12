"""The counterexample text of `#sql_check` is one readable block (issue #316)."""

import shutil
from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import split_blocks
from tests.surface_replay_test import native_replay
from tests.surface_support import fixture_file, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

UNIQUE_EMAIL_HEAD = """SQL check: false.
Database:
customers:
  email
  'a'
  'A'
noDuplicateEmails: rows [[1]]
uniqueEmail: error 19
Construction:
CREATE TABLE "customers" ("email" COLLATE BINARY);
INSERT INTO "customers" ("email") VALUES ('a');
INSERT INTO "customers" ("email") VALUES ('A');

SQLite replay:
"""
"""The block up to the replay script: the tables, the output of each statement and one construction."""


@pytest.mark.timeout(300)
@pytest.mark.requires_native("sqlite3")
def test_counterexample_is_one_readable_block(runtime_root: Path, tmp_path: Path) -> None:
    """CheckDisplay, CheckWitnessText and ReplayValues give the counterexample of the launch's first claim
    as tables of SQL literals, one line for each statement, one construction and one replay script, with no
    environment line for the default candidate. Native SQLite runs the one script: the query gives 1 and
    the index fails on the two emails. A non-default environment shows its clock and counters."""
    result = run_command(surface_command(runtime_root, fixture_file("CounterexampleReadable.lean"), tmp_path),
                         cwd=tmp_path, timeout=280)
    assert result.returncode == 0, result.diagnostic()
    blocks = split_blocks(result.stdout)
    block = blocks["unique-email"]
    assert block.startswith(UNIQUE_EMAIL_HEAD), block
    assert block.count("Construction:") == 1 and block.count("SQLite replay:") == 1, block
    for absent in ("valid :=", "bytes :=", "candidateEnvironment", "Environment:", "Bindings:", "CAST("):
        assert absent not in block, (absent, block)
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    replay = native_replay(sqlite, block.split("SQLite replay:\n", 1)[1], tmp_path, "unique-email")
    assert replay.stdout.split() == ['[{"1":1}]'], replay.diagnostic()
    assert "UNIQUE constraint failed: customers.email" in replay.stderr, replay.diagnostic()
    environment = blocks["environment"]
    assert ("Environment: clock 2026-10-20 12:00:00 at the first statement; changes() 3, "
            "total_changes() unknown, last_insert_rowid() unknown") in environment, environment
    assert "Database: empty" in environment, environment
