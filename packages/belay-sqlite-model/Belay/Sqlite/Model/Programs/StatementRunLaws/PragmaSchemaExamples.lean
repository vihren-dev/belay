import Belay.Sqlite.Model.Programs.Scripts.ScriptRun
import Belay.Sqlite.Model.Schema.Columns.PragmaSchemaExamples

set_option doc.verso true

/-! Examples of the pragmas that report facts of the schema (ADR 0019, D2), each checked by the
kernel: {lit}`PRAGMA table_info` and {lit}`PRAGMA foreign_key_list`, and their table-valued forms
{lit}`pragma_table_info('t')` and {lit}`pragma_foreign_key_list('t')` in {lit}`FROM`. The rows are
SQLite's (3.51.0, checked natively with the {lit}`sqlite3` shell); a query without
{lit}`ORDER BY` gives them in normal form. -/

namespace Belay.Sqlite.Model.PragmaSchemaExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- The outputs of a run of the statements from the empty database, with the default profile. -/
def outputs (script : List Syntax.Statement) : List Output :=
  (runScriptFrom { profile := defaults, mode := .execution } none 0 { state := { database := {} } }
    (script.map (·, []))).outputs

-- One row for each column that is not generated; cid counts only them. The type is as
-- written, and a standard type is in capitals; the rowid alias is pk 1.
example : outputs [createT, .pragma (.tableInfo (name! "T"))] = [.done 0, .rows [
    [.integer 0, textValue "a", textValue "INTEGER", .integer 0, .null, .integer 1],
    [.integer 1, textValue "b", textValue "x\"y", .integer 1, textValue "'q'", .integer 0],
    [.integer 2, textValue "c", textValue "INT", .integer 0, textValue "5", .integer 0],
    [.integer 3, textValue "d", textValue "", .integer 0, textValue "null", .integer 0]]] := by
  decide +kernel

-- The key columns of a WITHOUT ROWID table are NOT NULL; pk is the position in the key.
example : outputs [createW, .pragma (.tableInfo (name! "w"))] = [.done 0, .rows [
    [.integer 0, textValue "a", textValue "", .integer 1, .null, .integer 2],
    [.integer 1, textValue "b", textValue "", .integer 1, .null, .integer 1]]] := by
  decide +kernel

-- A missing table gives no rows; a table of SQLite's own that the catalog does not have ends the run.
example : outputs [.pragma (.tableInfo (name! "missing")), .pragma (.foreignKeyList (name! "missing"))] =
    [.rows [], .rows []] := by decide +kernel
example : (outputs [.pragma (.tableInfo (name! "sqlite_schema"))]).map Output.endsRun = [true] := by decide +kernel

-- The ids count the keys newest first: the table constraint is id 0. Without a column list,
-- to is NULL.
example : outputs [createC, .pragma (.foreignKeyList (name! "c"))] = [.done 0, .rows [
    keyRow 0 0 "q" "y" (textValue "a") "CASCADE", keyRow 0 1 "q" "z" (textValue "b") "CASCADE",
    keyRow 1 0 "p" "x" .null "NO ACTION"]] := by
  decide +kernel

-- The table-valued form gives the same rows; * does not show the hidden arg and schema.
example : outputs [createW, selectFrom [.star] "pragma_table_info" "w"] = [.done 0, .rows [
    [.integer 0, textValue "a", textValue "", .integer 1, .null, .integer 2],
    [.integer 1, textValue "b", textValue "", .integer 1, .null, .integer 1]]] := by
  decide +kernel
example : outputs [createW, selectFrom [named "name"] "pragma_table_info" "w"
    (some (.compare .eq (name "pk") (.numeric "1")))] = [.done 0, .rows [[textValue "b"]]] := by
  decide +kernel

-- A cell has no affinity: the text '5' of dflt_value is not the integer 5.
example : outputs [createT, selectFrom [named "name"] "pragma_table_info" "t"
    (some (.compare .eq (name "dflt_value") (.numeric "5")))] = [.done 0, .rows []] := by
  decide +kernel
example : outputs [createC, selectFrom [named "from"] "pragma_foreign_key_list" "c"
    (some (.compare .eq (name "id") (.numeric "1")))] = [.done 0, .rows [[textValue "x"]]] := by
  decide +kernel

-- Another table-valued pragma ends the run.
example : (outputs [selectFrom [.star] "pragma_index_list" "t"]).map Output.endsRun = [true] := by decide +kernel

end Belay.Sqlite.Model.PragmaSchemaExamples
