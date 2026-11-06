"""`#sql_check` refutes a claim on a schema of a consumer application's size (ADR 0031, D9)."""

import re
import shutil
from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import split_blocks
from tests.surface_replay_test import native_replay
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

CHECK_ERROR = "CHECK constraint failed: conversation_id IS NOT NULL"
"""The error of the delete trigger's log row, which native SQLite gives in the replay."""


def table_rows(block: str) -> dict[str, list[str]]:
    """The row lines of each table of the counterexample's database text."""
    database = block.split("Database:\n", 1)[1].split("\nid: ", 1)[0]
    tables = re.findall(r"^(\w+):\n  [^\n]*\n((?:  [^\n]*\n?)*)", database, re.MULTILINE)
    return {name: [line for line in rows.splitlines() if line != "  (no rows)"] for name, rows in tables}


@pytest.mark.timeout(300)
@pytest.mark.requires_native("sqlite3")
def test_consumer_size_claim_is_false_and_replays(runtime_root: Path, tmp_path: Path) -> None:
    """CheckDomain.domainSchemas, SampleTouched and SampleConstraints with the data limits of
    CheckBudget: on a schema of more than 8,192 data nodes, the premise `HasCatalog consumer`
    gives the schema of the search, which finds a message whose delete trigger breaks a CHECK at
    the default options, with at most two rows in each table. The construction inserts the rows
    with the triggers off; native SQLite rebuilds them and fails on the same CHECK. A
    counterexample supplied with `db!` is also reported."""
    result = run_command(surface_command(runtime_root, FIXTURES / "CheckConsumerSize.lean", tmp_path),
                         cwd=tmp_path, timeout=280)
    assert result.returncode == 0, result.diagnostic()
    nodes = int(re.search(r"consumer schema nodes: (\d+)", result.stdout).group(1))
    assert nodes > 8192, nodes
    blocks = split_blocks(result.stdout)
    block = blocks["consumer"]
    assert block.startswith("SQL check: false."), block
    rows = table_rows(block)
    assert set(rows) == {"users", "conversations", "members", "messages", "attachments", "message_log"}, rows
    assert all(len(lines) <= 2 for lines in rows.values()), rows
    assert rows["messages"], rows
    script = block.split("SQLite replay:\n", 1)[1]
    assert "ALTER TABLE messages ADD COLUMN pinned" in script, script
    assert ".dbconfig enable_trigger off\n" in script and ".dbconfig enable_trigger on\n" in script, script
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    construction = script.split("\n;\n", 1)[0] + "\n"
    built = native_replay(sqlite, construction + "SELECT count(*) AS n FROM messages;\n", tmp_path, "built")
    assert built.returncode == 0 and not built.stderr, built.diagnostic()
    assert built.stdout.split("\n")[-2] == f'[{{"n":{len(rows["messages"])}}}]', built.diagnostic()
    replay = native_replay(sqlite, script, tmp_path, "consumer")
    assert CHECK_ERROR in replay.stderr, replay.diagnostic()
    supplied = blocks["supplied"]
    assert supplied.startswith("SQL check: false."), supplied
    assert "id: 7" in supplied and "deleteMessage (parameters 7): error 19" in supplied, supplied
