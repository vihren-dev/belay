import Belay.Sqlite.Model.ReadOnlyFrame

set_option doc.verso true

/-!
What plain writes of other tables and reads leave unchanged (ADR 0017, S6). A plain write changes the rows of
its target table and nothing else that a resolution reads. A read changes no row. So a statement that resolves
to a plain write of another table, or to a read, keeps the catalog, the table at a position, the snapshot of an
open transaction and the settings of the connection. The rule needs only the resolution of the statement, not
the engine. Statements with trigger and foreign-key rules, and statements that change the catalog, are outside
the rule: they can write a second table, and a claim about them needs a premise of its own.
-/

namespace Belay.Sqlite.Model

/-- What a plain write to another table, or a read, cannot change at a position: the catalog, the table
at the position with its rows, the snapshot of an open transaction, and the two connection settings. The
counters are not in it, because every write and some reads change them. -/
def Connection.shelter (position : Nat) (connection : Connection) :
    Catalog × Option Table × Option Model.Database × Bool × Bool :=
  (connection.state.database.catalog, connection.state.database.table position, connection.state.snapshot,
    connection.foreignKeys, connection.recursiveTriggers)

/-- For every position and two connections with the same shelter: both connections give the same state of
resolution. Proof sketch: the state of resolution is made of the catalog, the catalog of the snapshot and the
two settings, which the shelter holds. -/
theorem Connection.shelter_resolveState {position : Nat} {connection other : Connection}
    (same : connection.shelter position = other.shelter position) :
    connection.resolveState = other.resolveState := by
  simp only [Connection.shelter, Prod.mk.injEq] at same
  obtain ⟨catalog, -, snapshot, foreignKeys, recursiveTriggers⟩ := same
  simp [Connection.resolveState, catalog, snapshot, foreignKeys, recursiveTriggers]

/-- A resolved statement that leaves the shelter of a position unchanged: a plain write to a table other than
the table at the position, or a query, or a statement that SQLite refuses with a prepare error. For example,
an INSERT into another table is sheltered from position 0 when its table is not at position 0. -/
def Resolved.Statement.ShelteredFrom (position : Nat) (statement : Resolved.Statement) : Prop :=
  (∃ target, statement.plainWriteTarget = some target ∧ target ≠ position) ∨
    (∃ query subqueries, statement = .query query subqueries) ∨ ∃ error, statement = .prepareError error

/-- For every position, connection, statement and step that continues, if the statement resolves to a resolved
statement that is sheltered from the position, then the step has no other execution than the model's own and
its connection has the same shelter. In plain words, such a statement does not change the catalog, the table at
the position, the snapshot or the settings, also when it fails. Proof sketch:
{name}`runScriptStep_plainWrite_frame` gives the database as the database of the connection or with the rows of
another table replaced, which leaves the table at the position unchanged ({name}`Database.table_setRows_other`);
{name}`runScriptStep_readOnly_keeps` gives the connection itself for a read. -/
theorem Connection.shelter_step {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {output : Output} {others : List StatementExecution} {position : Nat}
    {resolved : Resolved.Statement} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (sheltered : resolved.ShelteredFrom position)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    others = [] ∧ next.shelter position = connection.shelter position := by
  rcases sheltered with ⟨target, plain, distinct⟩ | readOnly
  · obtain ⟨nothing, snapshot, foreignKeys, recursiveTriggers, database⟩ :=
      runScriptStep_plainWrite_frame found plain step
    refine ⟨nothing, ?_⟩
    simp only [Connection.shelter, snapshot, foreignKeys, recursiveTriggers]
    rcases database with same | ⟨rows, same⟩
    · rw [same]
    · rw [same, Database.table_setRows_other _ _ (Ne.symm distinct)]
      rfl
  · obtain ⟨nothing, same⟩ := runScriptStep_readOnly_keeps found (by
      rcases readOnly with ⟨query, subqueries, same⟩ | ⟨error, same⟩
      · exact Or.inl ⟨query, subqueries, same⟩
      · exact Or.inr ⟨error, same⟩) step
    rw [same]
    exact ⟨nothing, rfl⟩

end Belay.Sqlite.Model
