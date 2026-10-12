import Belay.Sqlite.Resolution.Context

set_option doc.verso true

/-! The key domain of the model. The execution semantics checks a unique key by
comparing integer and NULL cells exactly, which is SQLite's comparison only when
no affinity converts the values. So a write is a model restriction when a unique
key of its table has a column that is not integer-comparable, or when it writes a
value other than an integer or NULL into a key column. -/

namespace Belay.Sqlite

/-- Whether the model compares a stored value with an integer without a
conversion: the column has INTEGER, NUMERIC or BLOB affinity, and the execution
semantics requires its stored values to be integers or NULL. -/
def integerComparable : Affinity → Bool
  | .integer | .numeric | .blob => true
  | .text | .real => false

/-- Whether a value is in the model's key domain: NULL or an integer. -/
def keyValue : Value → Bool
  | .null | .integer _ => true
  | .real _ | .text _ | .blob _ => false

/-- The affinity of the column at a position, or BLOB for a position outside the list. -/
def columnAffinity (columns : List CatalogColumn) (position : Nat) : Affinity :=
  (columns[position]?.map CatalogColumn.affinity).getD .blob

/-- The first key-domain restriction of a write, with the path of the node: a
unique key column that is not {name}`integerComparable` (path empty), or else the
first written row (path from {lit}`rowPath`) that has a value outside
{name}`keyValue` in a key column. Each row lists column positions and values. -/
def keyDomainRestriction (columns : List CatalogColumn) (keys : List (List Nat))
    (rowPath : Nat → List Nat) (rows : List (List (Nat × Value))) : Option (List Nat × String) :=
  let keyColumns := keys.flatten
  if keyColumns.any (fun position => !integerComparable (columnAffinity columns position)) then
    some ([], "unique keys over TEXT or REAL columns are not modeled; write only to tables whose key columns have INTEGER, NUMERIC or BLOB affinity")
  else (findPosition (·.any fun (position, value) => keyColumns.contains position && !keyValue value) rows).map
    fun (row, _) => (rowPath row, "only integer and NULL values are modeled in unique key columns; write an integer or NULL key value")

end Belay.Sqlite
