import Belay.Sqlite.Identifier

set_option doc.verso true

/-! The names that SQLite reserves or treats apart: the {lit}`sqlite_` prefix of its own
tables, the names of its eponymous table-valued functions, the columns of its statistics
tables, and the rowid names. -/

namespace Belay.Sqlite

/-- Whether the folded name starts with {lit}`sqlite_`, which SQLite reserves. -/
def reservedName (name : Identifier) : Bool := (bytes! "sqlite_").isPrefixOf name.folded

/-- Whether a name that names no table of the schema can name one of SQLite's eponymous
table-valued functions of the pinned build (checked natively: {lit}`SELECT count(*) FROM json_each`
gives 0): {lit}`json_each`, {lit}`json_tree`, {lit}`dbstat`, or a name with the prefix
{lit}`pragma_`, after ASCII folding. -/
def eponymousName (name : Identifier) : Bool :=
  name.folded == bytes! "json_each" || name.folded == bytes! "json_tree" || name.folded == bytes! "dbstat" ||
    (bytes! "pragma_").isPrefixOf name.folded

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
