import Belay.Sqlite.Model.AdmittedTableAtomStatement
import Belay.Sqlite.Model.AdmittedEngineLaws
import Belay.Sqlite.Model.AdmittedInsertAtoms
import Belay.Sqlite.Model.AdmittedUpdateAtoms
import Belay.Sqlite.Model.AdmittedUpsertAtoms
import Belay.Sqlite.Model.AdmittedAddColumnLaws
import Belay.Sqlite.Model.RowLocalUpsert

set_option doc.verso true

/-! These experiments check that two existing statement guarantees follow from
{name}`Belay.Sqlite.Model.runStatement_tableAtom` with their original assumptions.
They reuse the facts for individual statement forms. They do not import either
of the existing whole-statement theorems that they replace. -/

namespace Belay.Sqlite.Model.ProofSimplification

/-- For every table property, its {name}`RowLocalAtom` evidence supplies the
empty-table and sublist facts of {name}`TableAtom`. The constraints fact is not
needed. For example, apply this to {name}`Table.notNullAtom`.
Proof sketch: select the two shared fields. -/
theorem rowLocalTableAtom {atom : Table → Prop} (rowLocal : RowLocalAtom atom) :
    TableAtom atom where
  empty := rowLocal.empty
  sublist := rowLocal.sublist

/-- For every table property, clock, counters, parameters, resolved statement
and database: assume the property has {name}`RowLocalAtom` evidence and holds
on every table. Assume also that, if the statement adds a column, appending
that column and every permitted {name}`AddedCell` to its target table keeps
the property. Then the statement effect satisfies the property on every
table. This covers success and the carried database of a constraint FAIL;
other errors require nothing. There is no readiness premise. For example,
the property can be {name}`Table.NotNull`.
Proof sketch: apply {name}`runStatement_tableAtom`; supply the append premise
and the three existing plain-write facts. The generic theorem owns the
statement cases and the writes that use the row engine. -/
theorem rowLocalStatement {atom : Table → Prop} (rowLocal : RowLocalAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (statement : Resolved.Statement) {database : Database}
    (every : database.EachTable atom)
    (appended : ∀ target column refuses, statement = .addColumn target column refuses → ∀ table value,
      database.table target = some table → AddedCell table column value →
        atom (table.appendColumns [(column, value)])) :
    (runStatement clock counters parameters statement database).effect.Satisfies fun after => after.EachTable atom := by
  apply runStatement_tableAtom (rowLocalTableAtom rowLocal) rowLocal.facts.laws
    clock counters parameters statement every
  · intro target column refuses table value same found added
    exact appended target column refuses same table value found added
  · intro writes
    rcases writes with ⟨target, rows, returning, subqueries, rfl⟩ |
      ⟨target, assignments, filter, returning, subqueries, rfl⟩ |
      ⟨target, rows, clauses, returning, algorithm, subqueries, rfl⟩
    · exact runStatement_insert_rowLocal rowLocal clock counters parameters
        target rows returning subqueries every
    · exact runStatement_update_rowLocal rowLocal clock counters parameters
        target assignments filter returning subqueries every
    · exact Effect.satisfies_of_effectDatabase
        (runStatement_upsert_rowLocal rowLocal clock counters parameters
          target rows clauses returning algorithm subqueries every)

/-- For every clock, counters, parameters, resolved statement and database:
if all tables have distinct rowids, the statement effect satisfies that same
property. This covers success and the carried database of a constraint FAIL;
other errors require nothing. It requires neither readiness nor any other
database atom. Use this certificate for the distinct-rowid guarantee alone.
Proof sketch: apply {name}`runStatement_tableAtom` to
{name}`Table.rowidsDistinctAtom`. Adding columns keeps rowids; the three
plain-write facts and {name}`rowidsDistinctFacts` supply the other premises. -/
theorem distinctStatement (clock : Int) (counters : Counters) (parameters : List Value)
    (statement : Resolved.Statement) {database : Database} (distinct : database.RowidsDistinct) :
    (runStatement clock counters parameters statement database).effect.Satisfies Database.RowidsDistinct := by
  apply runStatement_tableAtom Table.rowidsDistinctAtom rowidsDistinctFacts.laws
    clock counters parameters statement distinct
  · intro target column refuses table value _ found _
    exact Table.RowidsDistinct.appendColumns (distinct target table found) [(column, value)]
  · intro writes
    rcases writes with ⟨target, rows, returning, subqueries, rfl⟩ |
      ⟨target, assignments, filter, returning, subqueries, rfl⟩ |
      ⟨target, rows, clauses, returning, algorithm, subqueries, rfl⟩
    · exact runStatement_insert_rowidsDistinct clock counters parameters
        target rows returning subqueries distinct
    · exact runStatement_update_rowidsDistinct clock counters parameters
        target assignments filter returning subqueries distinct
    · exact runStatement_upsert_rowidsDistinct clock counters parameters
        target rows clauses returning algorithm subqueries distinct

#print axioms rowLocalTableAtom
#print axioms rowLocalStatement
#print axioms distinctStatement

end Belay.Sqlite.Model.ProofSimplification
