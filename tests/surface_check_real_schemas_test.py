"""`#sql_check` finds the counterexamples of issues #318 and #293 on the tables that a developer has."""

import shutil
from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import split_blocks
from tests.surface_replay_test import native_replay
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

LABELS = ("one-plain", "one-checked", "two-plain", "two-checked", "two-checked-db", "primary-key")
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
