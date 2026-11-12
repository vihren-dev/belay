"""Search schemas that are the database at the end of a run of SQL text (issue #371).

The test checks `CheckData.schemaText?` and `CheckData.runParts?`, which recover the SQL text of such
a schema; `CheckClaim.querySites`, which gives a `Database.HasCatalog` premise no query; the reason
that `CheckSamples.visitCandidates` records for a schema without SQL text; and `commandCheckShare`,
which keeps that reason when the search uses its budget. Each schema of the fixture has an index, so
a counterexample is replayable only when the replay builds the schema from its text.
"""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import split_blocks
from tests.sql_file_support import configured_command
from tests.surface_support import fixture_file

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

INDEX = "CREATE INDEX customers_by_email ON customers(email);"
"""The statement that the replay of each counterexample must contain."""


@pytest.mark.timeout(300)
def test_run_schemas_give_replayable_counterexamples(runtime_root: Path, tmp_path: Path) -> None:
    """A schema from `sql_file`, given with `with (schema := ...)` or with `on`, and a `db!` schema
    followed by a run of `sql` give false with a replay that builds the index; a schema after a run of
    Lean code gives unknown with the reason that it has no SQL text."""
    result = run_command(configured_command(runtime_root, fixture_file("CheckRunSchemas.lean"), tmp_path),
                         cwd=tmp_path, timeout=280)
    assert result.returncode == 0, result.diagnostic()
    blocks = split_blocks(result.stdout)
    for label in ("file-schema", "file-on", "two-runs-on"):
        assert blocks[label].startswith("SQL check: false."), blocks[label]
        assert INDEX in blocks[label].split("SQLite replay:\n", 1)[1], blocks[label]
    assert blocks["without-text"].startswith("SQL check: unknown; the schema of the search has no SQL text"), \
        blocks["without-text"]
    assert "(Database.empty.run (sql_file \"db/schema.sql\")).db" in blocks["without-text"], blocks["without-text"]
