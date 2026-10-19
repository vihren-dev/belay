import Belay.Sqlite.Declarations

set_option doc.verso true

/-! Declared type text: SQLite's affinity of a declared type, the type that SQLite reports
for it, and whether it makes a primary key an alias for the rowid. -/

namespace Belay.Sqlite

/-- Whether the characters of {lit}`needle` occur contiguously in {lit}`haystack`. -/
def containsChars (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | first :: rest => needle.isPrefixOf (first :: rest) || containsChars needle rest

/-- Whether {lit}`needle` occurs as a contiguous part of {lit}`haystack`. -/
def containsText (haystack needle : String) : Bool :=
  containsChars needle.toList haystack.toList

/-- SQLite's column affinity of a declared type ({lit}`datatype3.html`, section 3.1),
with ASCII case ignored, in the documented order (R-14349-34154):
1. The text contains {lit}`INT`: INTEGER (R-07051-38416).
2. Else it contains {lit}`CHAR`, {lit}`CLOB` or {lit}`TEXT`: TEXT (R-00243-07929).
3. Else it contains {lit}`BLOB`, or there is no type: BLOB (R-63063-00748).
4. Else it contains {lit}`REAL`, {lit}`FLOA` or {lit}`DOUB`: REAL (R-59153-45869).
5. Otherwise: NUMERIC. -/
def affinityOf : Option String → Affinity
  | none => .blob
  | some text =>
    let upper := String.ofList (text.toList.map Char.toUpper)
    if containsText upper "INT" then .integer
    else if ["CHAR", "CLOB", "TEXT"].any (containsText upper) then .text
    else if containsText upper "BLOB" then .blob
    else if ["REAL", "FLOA", "DOUB"].any (containsText upper) then .real
    else .numeric

/-- The standard type names that SQLite recognizes in a declared type, in capitals
({lit}`sqlite3StdType`). -/
def standardTypeNames : List String := ["ANY", "BLOB", "INT", "INTEGER", "REAL", "TEXT"]

/-- A declared type as SQLite keeps and reports it: a type that is exactly one of
{name}`standardTypeNames`, with ASCII case ignored, becomes that name in capitals
({lit}`sqlite3AddColumn`); any other type text stays as written, so {lit}`int` is
{lit}`INT` and {lit}`VarChar(10)` keeps its case. -/
def reportedType : Option String → Option String
  | none => none
  | some text => some ((standardTypeNames.find? fun standard =>
      normalizeIdentifier standard == normalizeIdentifier text).getD text)

/-- Whether a declared type makes a single-column primary key an alias for the
rowid: the text equals {lit}`INTEGER` with ASCII case ignored ({lit}`lang_createtable.html`,
R-56094-57830). {lit}`INT` and {lit}`BIGINT` do not. -/
def aliasesRowid (declaredType : Option String) : Bool :=
  declaredType.map String.toUpper == some "INTEGER"

end Belay.Sqlite
