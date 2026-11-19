"""The SQL checker recovers a construction from source runs or from a computed catalog.
The fixture exercises both routes through public claims. The catalog case also checks
the printed constraints, view, index and trigger with the model and native SQLite."""

import json
from pathlib import Path
import shutil

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import false_answer, split_blocks
from tests.sql_file_support import configured_command
from tests.surface_support import fixture_file

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

INDEX = "CREATE INDEX customers_by_email ON customers(email);"
"""The statement that the replay of each counterexample must contain."""


@pytest.mark.timeout(300)
@pytest.mark.requires_native("sqlite3")
def test_run_schemas_give_replayable_counterexamples(runtime_root: Path, tmp_path: Path) -> None:
    """A schema from `sql_file`, given with `with (schema := ...)` or with `on`, a `db!` schema followed by
    a run of `sql`, and two runs whose first text has no final semicolon give false with a replay that
    builds the index; a schema after a run of Lean code yields the same replay from its computed catalog."""
    result = run_command(configured_command(runtime_root, fixture_file("CheckRunSchemas.lean"), tmp_path),
                         cwd=tmp_path, timeout=280)
    assert result.returncode == 0, result.diagnostic()
    blocks = split_blocks(result.stdout)
    for label in ("file-schema", "file-on", "two-runs-on", "unterminated-on"):
        false_answer(blocks[label])
        assert INDEX in blocks[label].split("SQLite replay:\n", 1)[1], blocks[label]
    computed = blocks["without-text"]
    false_answer(computed)
    replay = computed.split("SQLite replay:\n", 1)[1]
    assert 'CREATE INDEX "customers_by_email" ON "customers"' in replay, replay
    sql, = [json.loads(line.split("CATALOG-SQL ", 1)[1]) for line in result.stdout.splitlines() if "CATALOG-SQL " in line]
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    native = run_command([sqlite, ":memory:", sql + "SELECT label FROM via_cte; "
                          "INSERT INTO items(id,parent,v) VALUES(3,2,7); SELECT id FROM parents ORDER BY id;"],
                         cwd=tmp_path, timeout=10)
    assert native.returncode == 0 and native.stdout.splitlines() == ["6", "1", "2"], native.diagnostic()
