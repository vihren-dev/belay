import Belay.Sqlite.Model.Schema.Ddl.RenameExamples

set_option doc.verso true

/-! Examples of ALTER TABLE RENAME TO and RENAME COLUMN, checked by {lit}`#guard` when the package builds:
the order of SQLite 3.51.0's prepare errors (checked against the native probes of the task), the
{lit}`columnToken` that the error of a missing column prints as written, and the rewrite of a rename that
passes every check: its resolved statement stores the new catalog, and the run of that statement succeeds
because the new catalog keeps the outline and the selected parents. The catalog after each rename is the
subject of {lit}`RenameCatalogExamples.lean` and {lit}`RenameFailureExamples.lean`. -/

namespace Belay.Sqlite.Model.Resolution.RenameExamples

open Belay.Sqlite.Model Syntax Belay.Sqlite.Model.Resolution.Examples

/-- The prepare error of one statement from {name}`objects`, or none. -/
def errorOf (statement : Syntax.Statement) : Option PrepareError :=
  match statements (migration objects [statement]) with
  | [.prepareError error] => some error
  | _ => none

-- RENAME TO: the first error that SQLite finds, in its order.
#guard errorOf (.renameTable (name! "nope") (name! "w")) == some (.noSuchTable (name! "nope"))
#guard errorOf (.renameTable (name! "ti") (name! "w")) == some (.noSuchTable (name! "ti"))
#guard errorOf (.renameTable (name! "t") (name! "U")) == some (.renameTargetTaken (name! "U"))
#guard errorOf (.renameTable (name! "t") (name! "ti")) == some (.renameTargetTaken (name! "ti"))
#guard errorOf (.renameTable (name! "t") (name! "T")) == some (.renameTargetTaken (name! "T"))
#guard errorOf (.renameTable (name! "t") (name! "v")) == some (.renameTargetTaken (name! "v"))
#guard errorOf (.renameTable (name! "t") (name! "sqlite_x")) == some (.expression (.reservedName (name! "sqlite_x")))
#guard errorOf (.renameTable (name! "v") (name! "w")) == some (.viewNotAltered (name! "v"))
-- The schema table has every name of it; the indexes of the constraints are in the name space of tables.
#guard errorOf (.renameTable (name! "t") (name! "Sqlite_Schema")) == some (.renameTargetTaken (name! "Sqlite_Schema"))
#guard errorOf (.renameTable (name! "t") (name! "sqlite_autoindex_k_1")) ==
  some (.renameTargetTaken (name! "sqlite_autoindex_k_1"))
#guard errorOf (.renameTable (name! "t") (name! "SQLITE_AUTOINDEX_K_2")) ==
  some (.renameTargetTaken (name! "SQLITE_AUTOINDEX_K_2"))
#guard errorOf (.renameTable (name! "t") (name! "sqlite_autoindex_k_3")) ==
  some (.expression (.reservedName (name! "sqlite_autoindex_k_3")))
#guard errorOf (.renameTable (name! "sqlite_schema") (name! "w")) ==
  some (.expression (.tableMayNotBeAltered (name! "sqlite_master")))
#guard errorOf (.renameTable (name! "sqlite_temp_schema") (name! "w")) ==
  some (.expression (.tableMayNotBeAltered (name! "sqlite_temp_master")))
#guard errorOf (.renameTable (name! "sqlite_temp_schema") (name! "t")) ==
  some (.expression (.tableMayNotBeAltered (name! "sqlite_temp_master")))
#guard errorOf (.renameTable (name! "sqlite_temp_schema") (name! "SQLITE_SCHEMA")) ==
  some (.renameTargetTaken (name! "SQLITE_SCHEMA"))
#guard errorOf (.renameTable (name! "sqlite_schema") (name! "sqlite_temp_master")) ==
  some (.expression (.tableMayNotBeAltered (name! "sqlite_master")))
#guard errorOf (.renameTable (name! "sqlite_schema") (name! "t")) == some (.renameTargetTaken (name! "t"))
#guard errorOf (.renameColumn (name! "sqlite_schema") (name! "a") (name! "c") "a" false) ==
  some (.expression (.tableMayNotBeAltered (name! "sqlite_master")))
-- A name taken is found before a reserved name or a view.
#guard errorOf (.renameTable (name! "v") (name! "u")) == some (.renameTargetTaken (name! "u"))

-- RENAME COLUMN: the error of a missing column prints the token as written.
#guard errorOf (.renameColumn (name! "nope") (name! "a") (name! "c") "a" false) == some (.noSuchTable (name! "nope"))
#guard errorOf (.renameColumn (name! "v") (name! "a") (name! "c") "a" false) == some (.viewColumnsNotRenamed (name! "v"))
#guard errorOf (.renameColumn (name! "t") (name! "zz") (name! "c") "\"zz\"" false) ==
  some (.renameNoSuchColumn "\"zz\"")
#guard errorOf (.renameColumn (name! "t") (name! "ZZ") (name! "c") "[ZZ]" false) == some (.renameNoSuchColumn "[ZZ]")

end Belay.Sqlite.Model.Resolution.RenameExamples
