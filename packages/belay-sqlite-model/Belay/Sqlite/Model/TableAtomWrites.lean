import Belay.Sqlite.Model.TableAtomFrames
import Belay.Sqlite.Model.StatementStep

set_option doc.verso true

/-! Constraint-checked row writes preserve arbitrary table properties. -/

namespace Belay.Sqlite.Model

/-- For every table and rows, {name}`LiteralData.inserted` keeps the catalog entry of the table.
Proof sketch: induction on the rows; {name}`LiteralData.insertRow` changes only the rows. -/
theorem LiteralData.inserted_shape (table : Table) (rows : List (List Value)) :
    (LiteralData.inserted table rows).shape = table.shape := by
  unfold LiteralData.inserted
  induction rows generalizing table with
  | nil => rfl
  | cons values rest ih => exact (ih _).trans rfl

/-- For every atom, database, position, table, keys and result table: if every table of the database
has the atom, the database has the table at the position, the result has the entry of the table, and the
result has the atom when it passed {name}`LiteralData.constraints` and {name}`LiteralData.rowidsDistinct`,
then the effect of {name}`checkedWrite` satisfies "every table has the atom" ({name}`Effect.Satisfies`):
the database of a success and that of an error with {name}`ExecutionError.constraintFail` have it, and any
other error requires nothing. Proof sketch: a stored result passed the check, and
{name}`Database.EachTable.setRows` stores its rows; a failure keeps the database. -/
theorem checkedWrite_satisfies {atom : Table → Prop} {database : Database} (every : database.EachTable atom)
    {target : Nat} {table : Table} (found : database.table target = some table) (keys : List UniqueKey)
    (result : Table) (shape : result.shape = table.shape)
    (holds : (LiteralData.constraints keys result && LiteralData.rowidsDistinct result) = true → atom result) :
    (checkedWrite database target keys result).Satisfies fun after => after.EachTable atom := by
  unfold checkedWrite
  split
  · rename_i passed
    have whole : ({ table with rows := result.rows } : Table) = result := by cases result; simp_all
    exact Effect.satisfies_of_effectDatabase (every.setRows found (whole ▸ holds passed))
  · exact Effect.satisfies_of_database every rfl

/-- For every atom, database, position, table, keys, supplied rows and result table: if every table of
the database has the atom, the database has the table at the position, the result has the entry of the
table, and the result has the atom when it passed the check of {name}`checkedWrite`, then the effect of
{name}`insertOutcome` satisfies "every table has the atom" ({name}`Effect.Satisfies`). Proof sketch: a
refused rowid alias fails with the input database, and every other case is
{name}`checkedWrite_satisfies`. -/
theorem insertOutcome_satisfies {atom : Table → Prop} {database : Database} (every : database.EachTable atom)
    {target : Nat} {table : Table} (found : database.table target = some table) (keys : List UniqueKey)
    (rows : List (List Value)) (result : Table) (shape : result.shape = table.shape)
    (holds : (LiteralData.constraints keys result && LiteralData.rowidsDistinct result) = true → atom result) :
    (insertOutcome database target keys table rows result).Satisfies fun after => after.EachTable atom := by
  unfold insertOutcome
  split
  · dsimp only
    split <;> exact Effect.satisfies_of_database every rfl
  · exact checkedWrite_satisfies every found keys result shape holds

/-- For every atom, clock value, counters, parameter list, plain INSERT (no foreign key rules and no
trigger programs: {lean}`(none : Option Resolved.WriteRules)`) and database: if every table of the database
has the atom, and the table of the database at the target with the rows inserted has the atom when it
passed the check of {name}`checkedWrite` (the supplied cells are {name}`Resolved.rowsAt` the statement),
then the effect of {name}`runStatement` satisfies "every table has the atom" ({name}`Effect.Satisfies`).
Proof sketch: a missing table fails with the input database, and otherwise the effect is
{name}`insertOutcome_satisfies` with {name}`LiteralData.inserted_shape`. -/
theorem runStatement_insert_atom {atom : Table → Prop} (clock : Int) (counters : Counters)
    (parameters : List Value) (target : Nat) (rows : List (List Resolved.Cell))
    (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query) {database : Database}
    (every : database.EachTable atom)
    (holds : ∀ table, database.table target = some table →
      (LiteralData.constraints (database.keys target table) (LiteralData.inserted table
          (Resolved.rowsAt (Resolved.statementContext clock counters parameters database subqueries)
            table.shape.columns rows)) &&
        LiteralData.rowidsDistinct (LiteralData.inserted table
          (Resolved.rowsAt (Resolved.statementContext clock counters parameters database subqueries)
            table.shape.columns rows))) = true →
      atom (LiteralData.inserted table (Resolved.rowsAt
        (Resolved.statementContext clock counters parameters database subqueries) table.shape.columns rows))) :
    (runStatement clock counters parameters (.insert target rows returning subqueries none) database).effect.Satisfies
      fun after => after.EachTable atom := by
  simp only [runStatement, Option.map_none, StatementRun.withKeys]
  split
  · exact Effect.satisfies_of_database every rfl
  · rename_i table found
    exact insertOutcome_satisfies every found _ _ _ (LiteralData.inserted_shape _ _) (holds table found)

/-- For every atom, clock value, counters, parameter list, plain UPDATE and database: if every table of
the database has the atom, and, for the table at the target, the updated table has the atom when no
selected row has a refused rowid alias ({name}`LiteralData.updateMismatch`) and the table passed the check of
{name}`checkedWrite`, then the effect of {name}`runStatement` satisfies "every table has the atom"
({name}`Effect.Satisfies`). Proof sketch: a missing table and a refused rowid alias fail with the input
database, and otherwise the effect is {name}`checkedWrite_satisfies`; UPDATE keeps the entry. -/
theorem runStatement_update_atom {atom : Table → Prop} (clock : Int) (counters : Counters)
    (parameters : List Value) (target : Nat) (assignments : List (Nat × Resolved.Expr))
    (filter : Option Resolved.Expr) (returning : List (Resolved.Expr × String))
    (subqueries : List Resolved.Query) {database : Database} (every : database.EachTable atom)
    (holds : ∀ table, database.table target = some table →
      LiteralData.updateMismatch (Resolved.statementContext clock counters parameters database subqueries) table
        assignments filter = false →
      (LiteralData.constraints (database.keys target table) (LiteralData.updated
          (Resolved.statementContext clock counters parameters database subqueries) table assignments filter) &&
        LiteralData.rowidsDistinct (LiteralData.updated
          (Resolved.statementContext clock counters parameters database subqueries) table assignments filter)) = true →
      atom (LiteralData.updated (Resolved.statementContext clock counters parameters database subqueries) table
        assignments filter)) :
    (runStatement clock counters parameters (.update target assignments filter returning subqueries none) database).effect.Satisfies
      fun after => after.EachTable atom := by
  simp only [runStatement, Option.map_none, StatementRun.withKeys]
  split
  · exact Effect.satisfies_of_database every rfl
  · rename_i table found
    split
    · exact Effect.satisfies_of_database every rfl
    · rename_i accepted
      exact checkedWrite_satisfies every found _ _ rfl (holds table found (by simpa using accepted))

/-- For every atom that is a {name}`TableAtom`, clock value, counters, parameter list, plain DELETE and
database: if every table of the database has the atom, the effect of {name}`runStatement` satisfies
"every table has the atom" ({name}`Effect.Satisfies`). Proof sketch: DELETE stores a filter of the rows
({name}`LiteralData.deleted`), a sublist of the rows with the same entry. -/
theorem runStatement_delete_tableAtom {atom : Table → Prop} (tableAtom : TableAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (target : Nat) (filter : Option Resolved.Expr)
    (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query) {database : Database}
    (every : database.EachTable atom) :
    (runStatement clock counters parameters (.delete target filter returning subqueries none) database).effect.Satisfies
      fun after => after.EachTable atom := by
  simp only [runStatement, Option.map_none, StatementRun.withKeys]
  split
  · exact Effect.satisfies_of_database every rfl
  · rename_i table found
    refine Effect.satisfies_of_effectDatabase (every.setRows found ?_)
    exact tableAtom.sublist table _ (every _ table found) rfl (List.filter_sublist (l := table.rows))

end Belay.Sqlite.Model
