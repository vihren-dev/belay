import Belay.Sqlite.Model.Schema.Writes.ForeignKeyWrites

set_option doc.verso true

/-! The pieces of one statement's run that {lit}`StatementStep` combines: the unique keys of a
table, the checked write of INSERT and UPDATE, and what running a statement gives, with the run
of a write that checks foreign keys (ADR 0018, D4). -/

namespace Belay.Sqlite.Model

/-- Store a write's result when it satisfies the constraints of the given keys and its
rowids are distinct ({name}`LiteralData.rowidsDistinct`), or fail with
{lean}`ExecutionError.constraintViolation` and the input database. -/
def checkedWrite (database : Database) (target : Nat) (keys : List UniqueKey) (result : Table) : Effect :=
  if LiteralData.constraints keys result && LiteralData.rowidsDistinct result then
    .ok (database.setRows target result.rows)
  else .error (.constraintViolation, database)

/-- The outcome of INSERT: SQLite inserts the rows in order, and refuses a rowid alias
that is not an integer before the constraints of its row
({name}`LiteralData.aliasMismatch`), so the first such row is
{lean}`ExecutionError.datatypeMismatch` unless the rows before it already fail; with no
such row, {name}`checkedWrite` of the table with all rows inserted ({lit}`result`, which is
{name}`LiteralData.inserted`). A failure keeps the input database. -/
def insertOutcome (database : Database) (target : Nat) (keys : List UniqueKey) (table : Table)
    (rows : List (List Value)) (result : Table) : Effect :=
  match rows.findIdx? (LiteralData.aliasMismatch table.shape) with
  | some index =>
    let before := LiteralData.inserted table (rows.take index)
    if LiteralData.constraints keys before && LiteralData.rowidsDistinct before then
      .error (.datatypeMismatch, database)
    else .error (.constraintViolation, database)
  | none => checkedWrite database target keys result

end Belay.Sqlite.Model
