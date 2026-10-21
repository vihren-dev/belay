import Belay.Sqlite.Identifier

set_option doc.verso true

/-! The names that SQLite reserves or treats apart: the {lit}`sqlite_` prefix of its own
tables, the names of its eponymous table-valued functions, the columns of its statistics
tables, and the rowid names. -/

namespace Belay.Sqlite

/-- Whether the folded name starts with {lit}`sqlite_`, which SQLite reserves. -/
def reservedName (name : Identifier) : Bool := (bytes! "sqlite_").isPrefixOf name.folded

/-- The folded names of the eponymous table-valued functions of the pinned SQLite build and
of its shell (checked natively: {lit}`SELECT count(*) FROM jsonb_each` gives 0, and
{lit}`pragma_module_list` lists the others). A name of the shell's functions is included, so
the model never predicts {lit}`no such table` where a build of SQLite may have the function. -/
def eponymousNames : List (List UInt8) :=
  [bytes! "json_each", bytes! "json_tree", bytes! "jsonb_each", bytes! "jsonb_tree", bytes! "dbstat",
   bytes! "bytecode", bytes! "tables_used", bytes! "generate_series", bytes! "completion", bytes! "fsdir"]

/-- Whether a name that names no table of the schema can name one of SQLite's eponymous
table-valued functions: one of {name}`eponymousNames`, or a name with the prefix
{lit}`pragma_`, after ASCII folding. -/
def eponymousName (name : Identifier) : Bool :=
  eponymousNames.contains name.folded || (bytes! "pragma_").isPrefixOf name.folded

/-- The column names of SQLite's statistics tables, which a schema may contain, by the
folded table name ({name}`Identifier.folded`). -/
def statisticsColumns (folded : List UInt8) : Option (List Identifier) :=
  if folded == bytes! "sqlite_stat1" then some [name! "tbl", name! "idx", name! "stat"]
  else if folded == bytes! "sqlite_stat4" then
    some [name! "tbl", name! "idx", name! "neq", name! "nlt", name! "ndlt", name! "sample"]
  else none

/-- Whether a column name is one of SQLite's rowid names, which the model keeps
for the physical rowid. -/
def rowidName (name : Identifier) : Bool :=
  [bytes! "rowid", bytes! "_rowid_", bytes! "oid"].contains name.folded

end Belay.Sqlite
