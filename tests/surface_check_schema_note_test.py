"""The note of `#sql_check` for a search schema that only directs the search (issue #375).

The test checks `schemaOnlyDirectsNote` and its use in `elabSqlCheckCommand`
(`Belay/Sqlite/Tooling/Counterexamples/SqlCheckCommand.lean`). An unknown answer to a claim about every
database can hide that the claim is false as written; the note tells the user how to state the claim for
the databases of the schema.
"""

from pathlib import Path
import shutil

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import false_answer, final_rows, replays, split_blocks
from tests.sql_file_support import configured_command
from tests.surface_support import fixture_file

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

NOTE = "Note: (schema := shop) only directs the search."
"""The first sentence of the note."""


@pytest.mark.timeout(300)
def test_unknown_answer_with_a_search_schema_gets_the_note(runtime_root: Path, tmp_path: Path) -> None:
    """An unknown answer with `with (schema := shop)` and no `HasCatalog` premise gets the note, which names
    the schema and the two forms of the claim about its databases. The claim with `on shop`, a false answer
    and a search schema from `(db := shop)` get no note. The three schema-scoped derived-column
    claims have checked proof scripts, and sql_auto closes the same goals."""
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
    for label, law in (("on-schema", "preserves_of_check"), ("on-schema-lookup", "preserves_of_check_forall"),
                       ("on-schema-succeeds", "succeeds_of_check")):
        assert blocks[label].startswith("SQL check: proved."), blocks[label]
        assert f"DerivedColumnMigration.{law}" in blocks[label], blocks[label]
    scoped = false_answer(blocks["false-on-schema"])
    before, after = replays(scoped)
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    old_rows = final_rows(sqlite, tmp_path, "before", before, "")
    # The second program runs the final read in Lean. Read the migrated table in SQLite.
    new_rows = final_rows(sqlite, tmp_path, "after", after, "\nSELECT * FROM customers;\n")
    assert old_rows and [row[:-1] for row in new_rows] == old_rows and new_rows != old_rows, scoped
    false_answer(blocks["false"])
    assert NOTE not in blocks["false"], blocks["false"]
