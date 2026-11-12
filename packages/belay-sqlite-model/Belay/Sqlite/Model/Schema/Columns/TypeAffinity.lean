import Belay.Sqlite.Model.Shared.Catalog.TypeAffinity

set_option doc.verso true

/-! Declared type text: SQLite's affinity of a declared type, the type that SQLite reports
for it, and whether it makes a primary key an alias for the rowid. -/

namespace Belay.Sqlite.Model

/-- The standard type names that SQLite recognizes in a declared type, in capitals
({lit}`sqlite3StdType`). -/
def standardTypeNames : List String := ["ANY", "BLOB", "INT", "INTEGER", "REAL", "TEXT"]

/-- A declared type as SQLite keeps and reports it: a type that is exactly one of
{name}`standardTypeNames`, with ASCII case ignored, becomes that name in capitals
({lit}`sqlite3AddColumn`); any other type text stays as written, so {lit}`int` is
{lit}`INT` and {lit}`VarChar(10)` keeps its case. The frontend gives the type as SQLite's
tokens leave it: without a trailing {lit}`GENERATED ALWAYS`, and dequoted. -/
def reportedType : Option String → Option String
  | none => none
  | some text => some ((standardTypeNames.find? fun standard =>
      normalizeIdentifier standard == normalizeIdentifier text).getD text)

/-- Whether a declared type makes a single-column primary key an alias for the
rowid: the text equals {lit}`INTEGER` with ASCII case ignored ({lit}`lang_createtable.html`,
R-56094-57830). {lit}`INT` and {lit}`BIGINT` do not. -/
def aliasesRowid (declaredType : Option String) : Bool :=
  declaredType.map String.toUpper == some "INTEGER"

end Belay.Sqlite.Model
