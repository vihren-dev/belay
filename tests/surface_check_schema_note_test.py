"""The note of `#sql_check` for a search schema that only directs the search (issue #375).

The test checks `schemaOnlyDirectsNote` and its use in `elabSqlCheckCommand`
(`Belay/Sqlite/Tooling/Counterexamples/SqlCheckCommand.lean`). An unknown answer to a claim about every
database can hide that the claim is false as written; the note tells the user how to state the claim for
the databases of the schema.
"""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import split_blocks
from tests.sql_file_support import configured_command
from tests.surface_support import fixture_file

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

NOTE = "Note: (schema := shop) only directs the search."
"""The first sentence of the note."""


@pytest.mark.timeout(300)
def test_unknown_answer_with_a_search_schema_gets_the_note(runtime_root: Path, tmp_path: Path) -> None:
    """An unknown answer with `with (schema := shop)` and no `HasCatalog` premise gets the note, which names
    the schema and the two forms of the claim about its databases. The claim with `on shop`, a false answer
    and a search schema from `(db := shop)` get no note."""
    result = run_command(configured_command(runtime_root, fixture_file("CheckSchemaNote.lean"), tmp_path),
                         cwd=tmp_path, timeout=280)
    assert result.returncode == 0, result.diagnostic()
    blocks = split_blocks(result.stdout)
    noted = blocks["with-schema"]
    assert noted.startswith("SQL check: unknown;"), noted
    assert NOTE in noted, noted
    assert "write `on shop` after `preserves` or `succeeds`, or add the premise (·.HasCatalog shop)" in noted, noted
    for label in ("on-schema", "with-db"):
        assert "Note:" not in blocks[label], (label, blocks[label])
    assert blocks["false"].startswith("SQL check: false."), blocks["false"]
    assert NOTE not in blocks["false"], blocks["false"]
