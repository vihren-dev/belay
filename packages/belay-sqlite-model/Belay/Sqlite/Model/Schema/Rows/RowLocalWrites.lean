import Belay.Sqlite.Model.Schema.Rows.TableAtomWrites
import Belay.Sqlite.Model.Schema.Rows.RowLocalAtoms
import Belay.Sqlite.Model.Schema.Writes.KeysUniqueWrites

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every atom, clock value, counters, parameter list, plain INSERT (no foreign key rules and no trigger
programs: {lean}`(none : Option Resolved.WriteRules)`) and database: if the atom is a
{name}`RowLocalAtom` and every table of the database has it, the effect of {name}`runStatement`
satisfies "every table has the atom" ({name}`Effect.Satisfies`): the database of a success and that
of an error with {name}`ExecutionError.constraintFail` have it, and any other error requires
nothing. It assumes nothing about the support check. Proof sketch: {name}`runStatement_insert_atom` with the constraint implication of
{name}`RowLocalAtom.constraints`. -/
theorem runStatement_insert_rowLocal {atom : Table → Prop} (rowLocal : RowLocalAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (target : Nat) (rows : List (List Resolved.Cell))
    (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query) {database : Database}
    (every : database.EachTable atom) :
    (runStatement clock counters parameters (.insert target rows returning subqueries none) database).effect.Satisfies
      fun after => after.EachTable atom :=
  runStatement_insert_atom clock counters parameters target rows returning subqueries every
    fun _ _ passed => rowLocal.constraints _ _ (Bool.and_eq_true_iff.mp passed).1

/-- For every atom, clock value, counters, parameter list, plain UPDATE (no foreign key rules and no trigger
programs) and database: if the atom is a {name}`RowLocalAtom` and every table of the database has
it, the effect of {name}`runStatement` satisfies "every table has the atom"
({name}`Effect.Satisfies`): the database of a success and that of an error with
{name}`ExecutionError.constraintFail` have it, and any other error requires nothing. It assumes
nothing
about the support check. Proof sketch: {name}`runStatement_update_atom` with the constraint implication of
{name}`RowLocalAtom.constraints`. -/
theorem runStatement_update_rowLocal {atom : Table → Prop} (rowLocal : RowLocalAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (target : Nat) (assignments : List (Nat × Resolved.Expr))
    (filter : Option Resolved.Expr) (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query)
    {database : Database} (every : database.EachTable atom) :
    (runStatement clock counters parameters (.update target assignments filter returning subqueries none) database).effect.Satisfies
      fun after => after.EachTable atom :=
  runStatement_update_atom clock counters parameters target assignments filter returning subqueries every
    fun _ _ _ passed => rowLocal.constraints _ _ (Bool.and_eq_true_iff.mp passed).1

/-- For every atom, clock value, counters, parameter list, plain DELETE (no foreign key rules and no trigger
programs) and database: if the atom is a {name}`RowLocalAtom` and every table of the database has
it, the effect of {name}`runStatement` satisfies "every table has the atom"
({name}`Effect.Satisfies`): the database of a success and that of an error with
{name}`ExecutionError.constraintFail` have it, and any other error requires nothing. It assumes
nothing
about the support check. Proof sketch: DELETE stores a filter of the rows
({name}`LiteralData.deleted`), a sublist of the rows with the same entry ({name}`TableAtom.sublist`). -/
theorem runStatement_delete_rowLocal {atom : Table → Prop} (rowLocal : RowLocalAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (target : Nat) (filter : Option Resolved.Expr)
    (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query) {database : Database}
    (every : database.EachTable atom) :
    (runStatement clock counters parameters (.delete target filter returning subqueries none) database).effect.Satisfies
      fun after => after.EachTable atom :=
  runStatement_delete_tableAtom rowLocal.toTableAtom clock counters parameters target filter returning subqueries every

end Belay.Sqlite.Model
