import Belay.Sqlite.Model.KeysUniqueStatement
import Belay.Sqlite.Model.StatementStep

set_option doc.verso true

/-! One step of a run keeps the atom "keys unique" (ADR 0022, D3, slice 2): the database of the
connection state, and its snapshot when a transaction is open, satisfy
{lit}`Database.KeysUnique` after the step, and so does each database of an outcome at which the
run halts. This module gives the invariant of a state and of an outcome, the condition of a
statement in a run, and the theorem of {lit}`advance`. -/

namespace Belay.Sqlite.Model

/-- For the given state of a run: the database of the state satisfies
{name}`Database.KeysUnique`, and the snapshot satisfies it when the state has one. A state
without a snapshot requires nothing of the snapshot. -/
def SqlState.KeysUnique (state : SqlState) : Prop :=
  state.database.KeysUnique ∧ ∀ snapshot, state.snapshot = some snapshot → snapshot.KeysUnique

/-- For the given outcome of a run, each database of it satisfies {name}`Database.KeysUnique`:

* the database of a success;
* the database of a failure;
* the persisted and the visible database of a pending outcome. -/
def Outcome.KeysUnique : Outcome → Prop
  | .success database | .failure _ _ database => database.KeysUnique
  | .pending persisted visible _ => persisted.KeysUnique ∧ visible.KeysUnique

/-- Decide {name}`Outcome.KeysUnique` by the decision of {name}`Database.KeysUnique` for each
database of the outcome, so that the kernel can check it for a concrete run. -/
instance Outcome.decidableKeysUnique : (outcome : Outcome) → Decidable outcome.KeysUnique
  | .success database | .failure _ _ database => inferInstanceAs (Decidable database.KeysUnique)
  | .pending persisted visible _ => inferInstanceAs (Decidable (persisted.KeysUnique ∧ visible.KeysUnique))

/-- For the given transition: a transition that continues has a state that satisfies
{name}`SqlState.KeysUnique`, and a halt has an outcome that satisfies
{name}`Outcome.KeysUnique`. -/
def SqlTransition.KeysUnique : SqlTransition → Prop
  | .next state => state.KeysUnique
  | .halt outcome => outcome.KeysUnique

/-- For the given database, the condition of a statement that a run reaches on the database
before it (owner decision of 2026-10-23 in the keys-unique status file):

* CREATE INDEX: the table of the index exists, and the index is supported for its width
  ({name}`CatalogIndex.supported`), as {name}`Catalog.supported` checks it;
* ADD COLUMN: {name}`Database.AddColumnCondition` of the target;
* DROP: {name}`Catalog.DropCondition` of the dropped positions;
* every other statement: nothing. -/
def Resolved.Statement.RunCondition (database : Database) : Resolved.Statement → Prop
  | .createIndex _ _ index =>
    ((database.catalog.tableAt index.table).any fun table => index.supported table.columns.length) = true
  | .addColumn target _ => database.AddColumnCondition target
  | .drop positions _ => database.catalog.DropCondition positions
  | .createTable .. | .createTrigger .. | .begin | .commit | .rollback | .insert .. | .update ..
  | .upsert .. | .delete .. | .prepareError _ | .query .. | .setting _ _ => True

/-- For every database and statement: if the statement meets its run condition
({name}`Resolved.Statement.RunCondition`), it meets the condition of the statement theorem
({name}`Resolved.Statement.KeysCondition`). The statement theorem does not use the condition of
CREATE INDEX. Proof sketch: ADD COLUMN and DROP have the same condition in both, and every other
statement has the condition {lean}`True` in the statement theorem. -/
theorem Resolved.Statement.keysCondition_of_runCondition {database : Database} :
    ∀ {statement : Resolved.Statement}, statement.RunCondition database → statement.KeysCondition database
  | .addColumn .., condition | .drop .., condition => condition
  | .createTable .., _ | .createIndex .., _ | .createTrigger .., _ | .begin, _ | .commit, _ | .rollback, _
  | .insert .., _ | .update .., _ | .upsert .., _ | .delete .., _ | .prepareError _, _ | .query .., _
  | .setting _ _, _ => trivial

/-- Whether a statement has no run condition: false for CREATE INDEX, ADD COLUMN and DROP, and
true for every other statement. For example, a script of CREATE TABLE and writes has no run
condition. -/
def Resolved.Statement.unconditioned : Resolved.Statement → Bool
  | .createIndex .. | .addColumn .. | .drop .. => false
  | .createTable .. | .createTrigger .. | .begin | .commit | .rollback | .insert .. | .update ..
  | .upsert .. | .delete .. | .prepareError _ | .query .. | .setting _ _ => true

/-- For every database and statement: if the statement has no run condition
({name}`Resolved.Statement.unconditioned`), it meets its run condition on the database. Proof
sketch: a case for each statement; CREATE INDEX, ADD COLUMN and DROP contradict the hypothesis,
and every other statement has the condition {lean}`True`. -/
theorem Resolved.Statement.runCondition_of_unconditioned {database : Database} :
    ∀ {statement : Resolved.Statement}, statement.unconditioned = true → statement.RunCondition database := by
  intro statement unconditioned
  cases statement <;> first | trivial | exact nomatch unconditioned

/-- For every state and outcome: if the state satisfies {name}`SqlState.KeysUnique` and the
outcome satisfies {name}`Outcome.KeysUnique`, the outcome of {name}`SqlState.finish` satisfies
{name}`Outcome.KeysUnique`. Proof sketch: a pending outcome gets the snapshot as its persisted
database. -/
theorem SqlState.finish_keysUnique {state : SqlState} (unique : state.KeysUnique) {outcome : Outcome}
    (kept : outcome.KeysUnique) : (state.finish outcome).KeysUnique := by
  unfold SqlState.finish
  split
  · exact kept
  · exact ⟨unique.2 _ ‹_›, kept⟩
  · exact ⟨unique.2 _ ‹_›, kept⟩
  · exact kept

/-- For every state, position, reason and database: if the state satisfies
{name}`SqlState.KeysUnique` and the database satisfies {name}`Database.KeysUnique`, the outcome
of {name}`SqlState.failed` satisfies {name}`Outcome.KeysUnique`. Proof sketch: a rollback gives
the snapshot; every other failure is {name}`SqlState.finish_keysUnique`. -/
theorem SqlState.failed_keysUnique {state : SqlState} (unique : state.KeysUnique) (position : Nat)
    (reason : ExecutionError) {database : Database} (kept : database.KeysUnique) :
    (state.failed position reason database).KeysUnique := by
  unfold SqlState.failed
  split
  · split
    · exact unique.2 _ ‹_›
    · exact SqlState.finish_keysUnique unique kept
  · exact SqlState.finish_keysUnique unique kept

/-- For every state, position and effect: if the state satisfies {name}`SqlState.KeysUnique`
and the effect satisfies {name}`Effect.KeysUnique`, the transition of
{name}`SqlState.publish` satisfies {name}`SqlTransition.KeysUnique`. Proof sketch: a success
continues with the database of the effect; an error halts with the reached database of a FAIL
failure or with the database of the state ({name}`SqlState.failed_keysUnique`). -/
theorem SqlState.publish_keysUnique {state : SqlState} (unique : state.KeysUnique) (position : Nat)
    {effect : Effect} (kept : effect.KeysUnique) : (state.publish position effect).KeysUnique := by
  cases effect with
  | ok database => exact ⟨kept database (.inl rfl), unique.2⟩
  | error failure =>
    obtain ⟨reason, reached⟩ := failure
    refine SqlState.failed_keysUnique unique position reason ?_
    split
    · subst reason
      exact kept reached (.inr rfl)
    · exact unique.1

/-- For every position, statement, state and effect: if the state satisfies
{name}`SqlState.KeysUnique` and the effect satisfies {name}`Effect.KeysUnique`, the transition
of {name}`advanceWith` satisfies {name}`SqlTransition.KeysUnique`. Proof sketch: BEGIN copies
the database into the snapshot, COMMIT drops the snapshot, ROLLBACK restores it, a failure of
them is {name}`SqlState.finish_keysUnique`, and every other statement is
{name}`SqlState.publish_keysUnique`. -/
theorem advanceWith_keysUnique (position : Nat) (statement : Resolved.Statement) {state : SqlState}
    (unique : state.KeysUnique) {effect : Effect} (kept : effect.KeysUnique) :
    (advanceWith position statement state effect).KeysUnique := by
  cases statement with
  | begin =>
    dsimp only [advanceWith]
    split
    · exact SqlState.finish_keysUnique unique unique.1
    · exact ⟨unique.1, fun _ same => Option.some.inj same ▸ unique.1⟩
  | commit =>
    dsimp only [advanceWith]
    split
    · exact unique.1
    · exact ⟨unique.1, fun _ same => nomatch same⟩
  | rollback =>
    dsimp only [advanceWith]
    split
    · exact unique.1
    · exact ⟨unique.2 _ ‹_›, fun _ same => nomatch same⟩
  | createTable | createIndex | createTrigger | addColumn | drop | insert | upsert | update | delete
  | prepareError | query | setting => exact SqlState.publish_keysUnique unique position kept

end Belay.Sqlite.Model
