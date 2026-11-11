import Belay.Sqlite.Model.Shared.Execution.SqlExecution
import Belay.Sqlite.Model.Schema.Dispatch.QueryFunctions
import Belay.Sqlite.Model.Schema.Columns.ReadDefaults

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Output names of ADD COLUMN's empty-table check. SQLite's
{lit}`sqlite3AlterFinishAddColumn` calls {lit}`sqlite3ErrorIfNotEmpty` first for a statement that
resolution marked {lit}`refusesPopulated` (checked natively: its name is the one reported, also
for an empty table, before any later check's name), then for a column with a
time default ({name}`CatalogColumn.clockDefault`), and for a NOT NULL column without a
non-NULL default. That helper compiles a SELECT of a RAISE expression (pinned SQLite
{lit}`alter.c`), whose name is exposed even when the table is empty. Otherwise a column with
a CHECK constraint, and a column of a {lit}`STRICT` table ({name}`CatalogColumn.strictType`),
has the column of SQLite's SELECT over {lit}`pragma_quick_check`, which checks the existing
rows (ADR 0014, slices 4 and 6; checked natively). Other modeled additions
have no output columns. -/
def addColumnOutputNames (column : CatalogColumn) (refusesPopulated : Bool) : List String :=
  if refusesPopulated then ["raise(ABORT,'Cannot add a REFERENCES column with non-NULL default value')"]
  else if column.clockDefault then ["raise(ABORT,'Cannot add a column with non-constant default')"]
  else if column.notNull && (readDefaultValue column).toOption == some .null then
    ["raise(ABORT,'Cannot add a NOT NULL column with default value NULL')"]
  else if !column.checks.isEmpty || column.strictType.isSome then
    ["CASE WHEN quick_check GLOB 'CHECK*' THEN raise(ABORT,'CHECK constraint failed') " ++
      "WHEN quick_check GLOB 'non-* value in*' THEN raise(ABORT,'type mismatch on DEFAULT') " ++
      "ELSE raise(ABORT,'NOT NULL constraint failed') END"]
  else []

end Belay.Sqlite.Model
