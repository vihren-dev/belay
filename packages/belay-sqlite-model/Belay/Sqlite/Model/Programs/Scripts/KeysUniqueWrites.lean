import Belay.Sqlite.Model.Programs.Scripts.StatementStep
import Belay.Sqlite.Model.Schema.Writes.KeysUniqueWrites

set_option doc.verso true

/-! The theorems of the atom "keys unique" (ADR 0022, D3, slice 2) for plain INSERT, UPDATE and
DELETE, the writes without the row engine (no foreign keys checked and no trigger programs), and
for the statements that write no row: a query, a setting, a prepare error, BEGIN, COMMIT and
ROLLBACK. -/

namespace Belay.Sqlite.Model

/-- For every clock value, counters, parameter list, plain INSERT (no foreign key rules and no trigger
programs: {lean}`(none : Option Resolved.WriteRules)`) and database: if the database satisfies
{name}`Database.KeysUnique`, the effect of {name}`runStatement` satisfies
{name}`Effect.Satisfies` for {name}`Database.KeysUnique`. It assumes nothing about the support check. Proof sketch: a missing
table fails with the input database, and otherwise the effect is
{name}`insertOutcome_keysUnique`. -/
theorem runStatement_insert_keysUnique (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat)
    (rows : List (List Resolved.Cell)) (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query)
    {database : Database} (unique : database.KeysUnique) :
    (runStatement clock counters parameters (.insert target rows returning subqueries none) database).effect.Satisfies Database.KeysUnique := by
  simp only [runStatement, Option.map_none, StatementRun.withKeys]
  split
  · exact Effect.satisfies_of_database unique rfl
  · rename_i table found
    exact insertOutcome_keysUnique unique found _ _

/-- For every clock value, counters, parameter list, plain UPDATE (no foreign key rules and no trigger
programs) and database: if the database satisfies {name}`Database.KeysUnique`, the effect of
{name}`runStatement` satisfies {name}`Effect.Satisfies` for {name}`Database.KeysUnique`. It assumes nothing about the support
check. Proof sketch: a missing table and a refused rowid alias fail with the input database,
and otherwise the effect is {name}`checkedWrite_keysUnique`. -/
theorem runStatement_update_keysUnique (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat)
    (assignments : List (Nat × Resolved.Expr)) (filter : Option Resolved.Expr) (returning : List (Resolved.Expr × String))
    (subqueries : List Resolved.Query) {database : Database} (unique : database.KeysUnique) :
    (runStatement clock counters parameters (.update target assignments filter returning subqueries none) database).effect.Satisfies Database.KeysUnique := by
  simp only [runStatement, Option.map_none, StatementRun.withKeys]
  split
  · exact Effect.satisfies_of_database unique rfl
  · rename_i table found
    split
    · exact Effect.satisfies_of_database unique rfl
    · exact checkedWrite_keysUnique unique found _

/-- For every clock value, counters, parameter list, plain DELETE (no foreign key rules and no trigger
programs) and database: if the database satisfies {name}`Database.KeysUnique`, the effect of
{name}`runStatement` satisfies {name}`Effect.Satisfies` for {name}`Database.KeysUnique`. It assumes nothing about the support
check. Proof sketch: DELETE stores a filter of the rows ({name}`LiteralData.deleted`), a
sublist ({name}`Table.KeysUnique.sublist`). -/
theorem runStatement_delete_keysUnique (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat)
    (filter : Option Resolved.Expr) (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query)
    {database : Database} (unique : database.KeysUnique) :
    (runStatement clock counters parameters (.delete target filter returning subqueries none) database).effect.Satisfies Database.KeysUnique := by
  simp only [runStatement, Option.map_none, StatementRun.withKeys]
  split
  · exact Effect.satisfies_of_database unique rfl
  · rename_i table found
    refine Effect.satisfies_of_effectDatabase (unique.setRows found ?_)
    exact (unique target table found).sublist (List.filter_sublist (l := table.rows))

/-- For every database and query run, the database of {name}`queryEffect` is the database: a
query writes no row. Proof sketch: each failure and the success of
{name}`queryEffect` carry the database. -/
theorem effectDatabase_queryEffect (database : Database) (run : Option (Resolved.SourceRows × Resolved.QueryRun)) :
    effectDatabase (queryEffect database run) = database := by
  unfold queryEffect
  split
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · rfl

/-- For every clock value, counters, parameter list, database and statement that writes no row (a query,
a setting, a prepare error, BEGIN, COMMIT or ROLLBACK): the database of the effect of
{name}`runStatement` is the database. BEGIN, COMMIT and ROLLBACK change the connection, not the
effect ({lit}`advanceWith`). Proof sketch: for each form, {name}`step` gives the database on
success and on its error ({name}`effectDatabase_queryEffect` for a query). -/
theorem runStatement_keeps_database (clock : Int) (counters : Counters) (parameters : List Value) (database : Database)
    (statement : Resolved.Statement)
    (writesNone : (∃ query subqueries, statement = .query query subqueries) ∨ (∃ setting on, statement = .setting setting on) ∨
      (∃ error, statement = .prepareError error) ∨ statement = .begin ∨ statement = .commit ∨ statement = .rollback) :
    effectDatabase (runStatement clock counters parameters statement database).effect = database := by
  rcases writesNone with ⟨query, subqueries, same⟩ | ⟨setting, on, same⟩ | ⟨error, same⟩ | same | same | same <;>
    subst same <;> simp only [runStatement, step] <;> first | exact effectDatabase_queryEffect _ _ | rfl

/-- For every clock value, counters, parameter list, database and statement that writes no row (a query,
a setting, a prepare error, BEGIN, COMMIT or ROLLBACK): if the database satisfies
{name}`Database.KeysUnique`, the effect of {name}`runStatement` satisfies
{name}`Effect.Satisfies` for {name}`Database.KeysUnique`. Proof sketch: {name}`runStatement_keeps_database`. -/
theorem runStatement_writesNone_keysUnique (clock : Int) (counters : Counters) (parameters : List Value) {database : Database}
    (unique : database.KeysUnique) (statement : Resolved.Statement)
    (writesNone : (∃ query subqueries, statement = .query query subqueries) ∨ (∃ setting on, statement = .setting setting on) ∨
      (∃ error, statement = .prepareError error) ∨ statement = .begin ∨ statement = .commit ∨ statement = .rollback) :
    (runStatement clock counters parameters statement database).effect.Satisfies Database.KeysUnique :=
  Effect.satisfies_of_database unique (runStatement_keeps_database clock counters parameters database statement writesNone)

end Belay.Sqlite.Model
