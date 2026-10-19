import Belay.Sqlite.Resolution.ExprAny

set_option doc.verso true

/-! The keys of tables and indexes (ADR 0014, D1): key terms, which are columns or
expressions over a row, the key terms of an index with their sort orders and its filter,
and the unique keys that writes keep. The catalog stores the indexes; execution compares
rows on the unique keys ({lit}`LiteralData.keyEqual`). -/

namespace Belay.Sqlite

/-- One term of a key (ADR 0014, D1): a column of the table, or an expression over the
table's row. For example {lean}`KeyTerm.column 0` is the first column. -/
inductive KeyTerm where
  /-- The column at a table position. -/
  | column (position : Nat)
  /-- An expression over the row; it reads no clock and calls no JSON function. -/
  | expression (value : Resolved.Expr)
  deriving Repr, DecidableEq

/-- The positions that a term reads, below the width of the table. -/
def KeyTerm.reads (width : Nat) : KeyTerm → List Nat
  | .column position => [position]
  | .expression value => value.reads width

/-- One key term with its sort order and its collation (ADR 0014, D3), under which two
values of the term are equal. The sort order changes no result that the model observes;
the catalog keeps it to describe an index. -/
structure IndexKey where
  /-- The term. -/
  term : KeyTerm
  /-- Whether the term is {lit}`DESC`; {lean}`false` for {lit}`ASC` or no order. -/
  descending : Bool := false
  /-- The collation of the term; {lit}`BINARY` without one. -/
  collation : Collation := .binary
  deriving Repr, DecidableEq

/-- One index entry: the catalog position of its table, its key terms, whether it is
unique, and its {lit}`WHERE` filter, none for an index of every row. -/
structure CatalogIndex where
  /-- The catalog position of the indexed table. -/
  table : Nat
  /-- The key terms in key order. -/
  keys : List IndexKey
  /-- Whether the index requires unique keys. -/
  unique : Bool
  /-- The filter of a partial index, over the table's row; none for a full index. -/
  filter : Option Resolved.Expr := none
  deriving Repr, DecidableEq

/-- One unique key of a table: its terms with their collations, and the filter of a partial
unique index, none for a key of every row. Two rows conflict on it when the filter is true
for both and every term is equal under its collation ({lit}`LiteralData.keyEqual`). -/
structure UniqueKey where
  /-- The terms in key order. -/
  terms : List IndexKey
  /-- The filter of a partial unique index; none for a key of every row. -/
  filter : Option Resolved.Expr := none
  deriving Repr, DecidableEq

/-- The column positions of a key of columns without filter, the only keys that an
{lit}`ON CONFLICT` target can name; none for any other key. -/
def UniqueKey.columns? (key : UniqueKey) : Option (List Nat) :=
  if key.filter.isSome then none
  else key.terms.mapM fun key => match key.term with
    | .column position => some position
    | .expression _ => none

/-- The positions below the width that the key's terms and filter read. -/
def UniqueKey.reads (width : Nat) (key : UniqueKey) : List Nat :=
  (key.terms.flatMap (·.term.reads width) ++ (key.filter.map (·.reads width)).getD []).eraseDups

/-- The unique key of a unique index. -/
def CatalogIndex.uniqueKey (index : CatalogIndex) : UniqueKey :=
  { terms := index.keys, filter := index.filter }

/-- Whether an index is admitted for a table of the width: at least one key term, column
terms below the width, and expression terms and the filter that read only columns below
the width. A column may appear in two terms, as SQLite allows. -/
def CatalogIndex.supported (index : CatalogIndex) (width : Nat) : Bool :=
  let positions := index.keys.filterMap fun key => match key.term with
    | .column position => some position
    | .expression _ => none
  !index.keys.isEmpty && positions.all (· < width) &&
    index.keys.all (fun key => match key.term with
      | .column _ => true
      | .expression value => value.readsBelow width) &&
    index.filter.all (·.readsBelow width)

end Belay.Sqlite
