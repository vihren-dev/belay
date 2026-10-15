import Belay.Sqlite.RowUpdate
import Belay.Sqlite.Resolution.ConflictForm
import Belay.Sqlite.Execution

set_option doc.verso true

/-! The execution of INSERT with {lit}`ON CONFLICT` clauses (ADR 0012, amendment 4,
slice 5c), checked on native SQLite 3.51.0. The rows are processed one at a time, in
order, so a later row sees the rows that earlier ones inserted or updated. For each row:
a rowid alias that is no integer is {lit}`datatype mismatch`; a NULL in a NOT NULL
column fails before any conflict handling; the first clause whose target key has a
conflicting row handles the row, and the other keys are not checked for it; without
such a clause the row is inserted and checked against every key. Each failure is the
ABORT error of the statement. -/

namespace Belay.Sqlite
namespace LiteralData

/-- The row that INSERT proposes for the cells: the rowid of {name}`newRowid` and the
cells of {name}`newCells`, which {name}`insertRow` appends. It is also the row that
{lit}`excluded` reads, so a NULL alias reads the new rowid. -/
def proposedRow (table : Table) (values : List Value) : Row :=
  { rowid := newRowid table values, values := newCells table values (newRowid table values) }

/-- Whether no cell is NULL in a NOT NULL column. -/
def notNullCells (columns : List CatalogColumn) (values : List Value) : Bool :=
  (columns.zip values).all fun (column, value) => !column.notNull || value != .null

/-- The first row of the table that conflicts with the proposed row on one of the keys
({name}`keyEqual`), or none. -/
def conflictingRow (keys : List (List Nat)) (table : Table) (proposed : Row) : Option Row :=
  table.rows.find? fun row => keys.any fun key => keyEqual key row proposed

/-- The keys that a clause checks: its target key, or every key for a clause without
target. -/
def clauseKeys (keys : List (List Nat)) (clause : Resolved.ConflictClause) : List (List Nat) :=
  match clause.target with
  | some key => [key]
  | none => keys

/-- The first clause, in written order, whose keys ({name}`clauseKeys`) have a row that
conflicts with the proposed row, with that row; none when no clause has one. -/
def handlingClause (keys : List (List Nat)) (clauses : List Resolved.ConflictClause) (table : Table)
    (proposed : Row) : Option (Resolved.ConflictClause × Row) :=
  clauses.findSome? fun clause => (conflictingRow (clauseKeys keys clause) table proposed).map (clause, ·)

/-- The table with each row of the old row's rowid replaced by the new row. Rowids are
distinct in a valid table, so one row changes; the order of rows stays. -/
def replaceRow (table : Table) (old new : Row) : Table :=
  { table with rows := table.rows.map fun row => if row.rowid == old.rowid then new else row }

/-- Whether an updated row has a rowid alias cell that SQLite refuses with
{lit}`datatype mismatch`: the table has an alias and the row has no integer there. -/
def aliasCellMismatch (alias : Option Nat) (row : Row) : Bool :=
  match alias with
  | none => false
  | some position => match row.values[position]? with
    | some (.integer _) => false
    | some .null | some (.real _) | some (.text _) | some (.blob _) | none => true

/-- The table after a write of one row, with the row that {lit}`RETURNING` reads, when
the table passes {name}`constraints` and {name}`rowidsDistinct`; otherwise the unique or
NOT NULL failure. -/
def checkedRow (keys : List (List Nat)) (next : Table) (written : Row) :
    Except ExecutionError (Table × Option Row) :=
  if constraints keys next && rowidsDistinct next then .ok (next, some written) else .error .constraintViolation

/-- The {lit}`DO UPDATE` of an existing row: the assignments and the filter read the
existing row followed by the proposed row. A filter that is not true skips the row; the
new row takes the rowid of {name}`movedRowid`, and a non-integer alias is
{lit}`datatype mismatch`; the result is checked by {name}`checkedRow`. -/
def updateExisting (keys : List (List Nat)) (table : Table) (assignments : List (Nat × Resolved.Expr))
    (filter : Option Resolved.Expr) (existing proposed : Row) : Except ExecutionError (Table × Option Row) :=
  let context := existing.values ++ proposed.values
  if !(filter.all fun condition => Resolved.truthy (condition.eval context)) then .ok (table, none) else
  let changed := movedRowid table.shape.rowidAlias (assignFrom table.shape.columns assignments context existing)
  if aliasCellMismatch table.shape.rowidAlias changed then .error .datatypeMismatch
  else checkedRow keys (replaceRow table existing changed) changed

/-- One row of an UPSERT: the table after it and the row that it inserted or updated,
none for a skipped row; or the error of the statement. -/
def upsertRow (keys : List (List Nat)) (clauses : List Resolved.ConflictClause) (table : Table)
    (values : List Value) : Except ExecutionError (Table × Option Row) :=
  if aliasMismatch table.shape values then .error .datatypeMismatch else
  let proposed := proposedRow table values
  if !notNullCells table.shape.columns proposed.values then .error .constraintViolation else
  match handlingClause keys clauses table proposed with
  | none => checkedRow keys (insertRow table values) proposed
  | some (clause, existing) => match clause.action with
    | .nothing => .ok (table, none)
    | .update assignments filter => updateExisting keys table assignments filter existing proposed

/-- The rows of an UPSERT in order ({name}`upsertRow`): the final table and the inserted
and updated rows in row order, or the first error. -/
def upsertRun (keys : List (List Nat)) (clauses : List Resolved.ConflictClause) (table : Table) :
    List (List Value) → Except ExecutionError (Table × List Row)
  | [] => .ok (table, [])
  | values :: rest => match upsertRow keys clauses table values with
    | .error reason => .error reason
    | .ok (next, written) => match upsertRun keys clauses next rest with
      | .error reason => .error reason
      | .ok (final, later) => .ok (final, written.toList ++ later)

/-- Whether every reached row of an UPSERT has a bounded proposed rowid, and every table
after a row has bounded rowids. SQLite chooses a random rowid after the largest one,
which the model does not describe. -/
def upsertBounded (keys : List (List Nat)) (clauses : List Resolved.ConflictClause) (table : Table) :
    List (List Value) → Bool
  | [] => true
  | values :: rest => boundedInteger (newRowid table values) && match upsertRow keys clauses table values with
    | .error _ => true
    | .ok (next, _) => next.rows.all (fun row => boundedInteger row.rowid) && upsertBounded keys clauses next rest

/-- Require {name}`tableReady` before the write, {name}`aliasReady`, one stored value per
column in each row, a column at every position that a {lit}`DO UPDATE` assigns, and
{name}`upsertBounded`. This check does not establish the constraints of the result,
which {name}`checkedRow` checks. -/
def upsertReady (keys : List (List Nat)) (table : Table) (clauses : List Resolved.ConflictClause)
    (rows : List (List Value)) : Bool :=
  tableReady keys table && aliasReady table.shape &&
  rows.all (fun values => values.length == table.shape.columns.length &&
    (table.shape.columns.zip values).all (fun (column, value) => storedForm column.affinity value)) &&
  clauses.all (fun clause => match clause.action with
    | .nothing => true
    | .update assignments _ => assignments.all fun (position, _) => (table.shape.columns[position]?).isSome) &&
  upsertBounded keys clauses table rows

end LiteralData
end Belay.Sqlite
