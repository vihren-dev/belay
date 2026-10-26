import Belay.Sqlite.MigrationPatternFrames
import Belay.Sqlite.ExecutionIndexFree

set_option doc.verso true

/-! A sufficient rule for query calls (ADR 0017, S8). A weak translation of a query call
({name}`Belay.Sqlite.Migration.TranslatesOn`) compares only the value and the visible outputs. It does not
justify a full commutation with a migration, because an ordinary query moves the statement index and
can change the connection. This module gives the facts that turn a weak translation into a full
commutation for a query that keeps the connection, under a clock that gives one date at every index.
Each fact is a premise that the caller proves for the query family at hand. -/

namespace Belay.Sqlite.Migration

open Belay.Sqlite.Model

/-- The facts about one query call, its replacement and a migration that make the weak translation of the
call a full commutation. For every context where the predicate holds and the migration succeeds
({name}`Migration.Domain`), all of these hold.

* The query keeps the connection: every branch of the query returns a value and ends at the connection where
  it started.
* The replacement keeps the connection: after any branch of the migration, every branch of the replacement
  returns a value and ends at the connection where it started.
* The query and its replacement give equally many outputs on the branches that follow each other.
* The predicate holds again after the query. -/
structure QueryFrames {μ α : Type} (migration : Sql μ) (admitted : ExecutionContext → Prop)
    (query replacement : Sql α) : Prop where
  /-- Every branch of the query returns and keeps the connection. -/
  queryKeeps : ∀ state, Domain migration admitted state → ∀ first,
    query.Branch state.clock state.index state.connection first →
      first.connection = state.connection ∧ first.value.isSome = true
  /-- After every branch of the migration, every branch of the replacement returns and keeps the connection. -/
  replacementKeeps : ∀ state, Domain migration admitted state → ∀ ran,
    migration.Branch state.clock state.index state.connection ran →
    ∀ last, replacement.Branch state.clock (state.index + ran.outputs.length) ran.connection last →
      last.connection = ran.connection ∧ last.value.isSome = true
  /-- A branch of the query and a branch of the replacement after a branch of the migration have equally
  many outputs. -/
  sameCount : ∀ state, Domain migration admitted state → ∀ first ran last,
    query.Branch state.clock state.index state.connection first →
    migration.Branch state.clock state.index state.connection ran →
    replacement.Branch state.clock (state.index + ran.outputs.length) ran.connection last →
      first.outputs.length = last.outputs.length
  /-- The predicate holds at the context after every branch of the query. -/
  admittedKept : ∀ state, Domain migration admitted state → ∀ first,
    query.Branch state.clock state.index state.connection first → admitted (state.finish first)

/-- For every migration, predicate, query and replacement: if the query translates weakly
({name}`Migration.TranslatesOn`), and the facts hold that keep the connection and the count of outputs, and
the clock gives one date at every index at the contexts of the predicate, and the migration reaches one
connection with one count of outputs on all its branches, then the query commutes fully with the migration
({name}`Migration.CommutesAsOn`). Plain words: running the query and then the migration, and running the
migration and then the replacement, return the same value and visible outputs, reach the same complete
connection, and take the same number of statements, for every branch.
Proof sketch: {name}`Migration.TranslatesOn.commutes_of_frames` needs the later success of the migration, the
equal connections and the equal step counts. The query keeps the connection, so the migration runs from the
same connection at a later index, and a constant clock makes that run the same
({name}`Sql.branch_index_iff`, {name}`Sql.succeedsFrom_index`). Both orders end at the connection of the
migration, and their step counts are the counts of the migration and the query. -/
theorem TranslatesOn.commutes_of_query {μ α : Type} {migration : Sql μ} {query replacement : Sql α}
    {admitted : ExecutionContext → Prop}
    (translation : TranslatesOn migration admitted query replacement)
    (frames : QueryFrames migration admitted query replacement)
    (constant : ∀ state, admitted state → ∀ assignment ∈ state.clock, ∀ one other, assignment one = assignment other)
    (uniform : ∀ state, Domain migration admitted state → ∀ one other,
      migration.Branch state.clock state.index state.connection one →
      migration.Branch state.clock state.index state.connection other →
        one.connection = other.connection ∧ one.outputs.length = other.outputs.length) :
    CommutesAsOn migration admitted query replacement := by
  have indexFree : ∀ state, Domain migration admitted state → ∀ index,
      migration.SucceedsFrom state.clock index state.connection := fun state domain index =>
    (Sql.succeedsFrom_index migration state.clock (constant state domain.1) state.index index state.connection).1 domain.2
  have returnsAll : ∀ state, Domain migration admitted state → ∀ index (ran : SqlRun μ),
      migration.Branch state.clock index state.connection ran → ran.value.isSome = true :=
    fun state domain index ran branch =>
      ((Sql.succeedsFrom_iff_branches _ _ _ _).mp (indexFree state domain index) ran branch).1
  -- Every branch of the query-first order is a query branch followed by a migration branch.
  have beforeParts : ∀ state, Domain migration admitted state → ∀ one,
      (before query migration).Branch state.clock state.index state.connection one →
        ∃ first ran, query.Branch state.clock state.index state.connection first ∧
          migration.Branch state.clock (state.index + first.outputs.length) state.connection ran ∧
          one.connection = ran.connection ∧ one.outputs.length = first.outputs.length + ran.outputs.length := by
    intro state domain one branch
    obtain ⟨first, firstBranch, split⟩ := (Sql.branch_bind_iff query _ _ _ _ one).mp branch
    obtain ⟨keeps, returned⟩ := frames.queryKeeps state domain first firstBranch
    cases firstValue : first.value with
    | none => simp [firstValue] at returned
    | some value =>
      simp only [firstValue] at split
      obtain ⟨last, lastBranch, rfl⟩ := split
      obtain ⟨ran, ranBranch, split2⟩ := (Sql.branch_bind_iff migration _ _ _ _ last).mp lastBranch
      rw [keeps] at ranBranch
      cases ranValue : ran.value with
      | none => simp [ranValue] at split2; have := returnsAll state domain _ ran ranBranch; simp [ranValue] at this
      | some other =>
        simp only [ranValue] at split2
        obtain ⟨tail, tailBranch, rfl⟩ := split2
        obtain rfl := (Sql.branch_pure_iff value _ _ _ tail).mp tailBranch
        exact ⟨first, ran, firstBranch, ranBranch, by simp, by simp⟩
  have afterParts : ∀ state, Domain migration admitted state → ∀ two,
      (after migration replacement).Branch state.clock state.index state.connection two →
        ∃ ran last, migration.Branch state.clock state.index state.connection ran ∧
          replacement.Branch state.clock (state.index + ran.outputs.length) ran.connection last ∧
          two.connection = ran.connection ∧ two.outputs.length = ran.outputs.length + last.outputs.length := by
    intro state domain two branch
    obtain ⟨ran, ranBranch, split⟩ := (Sql.branch_bind_iff migration _ _ _ _ two).mp branch
    cases ranValue : ran.value with
    | none => have := returnsAll state domain _ ran ranBranch; simp [ranValue] at this
    | some other =>
      simp only [ranValue] at split
      obtain ⟨last, lastBranch, rfl⟩ := split
      obtain ⟨keeps, -⟩ := frames.replacementKeeps state domain ran ranBranch last lastBranch
      exact ⟨ran, last, ranBranch, lastBranch, keeps, by simp⟩
  refine TranslatesOn.commutes_of_frames translation ?_ ?_ ?_
  · intro state domain first branch value returned
    obtain ⟨keeps, -⟩ := frames.queryKeeps state domain first branch
    show migration.SucceedsFrom state.clock (state.index + first.outputs.length) first.connection
    rw [keeps]
    exact indexFree state domain _
  · intro state domain one two beforeBranch afterBranch _
    obtain ⟨first, ran, firstBranch, ranBranch, oneConnection, -⟩ := beforeParts state domain one beforeBranch
    obtain ⟨other, last, otherBranch, lastBranch, twoConnection, -⟩ := afterParts state domain two afterBranch
    have moved := (Sql.branch_index_iff migration state.clock (constant state domain.1) _ state.index state.connection ran).1 ranBranch
    obtain ⟨sameConnection, -⟩ := uniform state domain other ran otherBranch moved
    rw [oneConnection, twoConnection, sameConnection]
  · intro state domain one two beforeBranch afterBranch _
    obtain ⟨first, ran, firstBranch, ranBranch, -, oneLength⟩ := beforeParts state domain one beforeBranch
    obtain ⟨other, last, otherBranch, lastBranch, -, twoLength⟩ := afterParts state domain two afterBranch
    have ranBranch' : migration.Branch state.clock (state.index + first.outputs.length) state.connection ran := ranBranch
    have moved := (Sql.branch_index_iff migration state.clock (constant state domain.1) _ state.index state.connection ran).1 ranBranch'
    obtain ⟨-, sameLength⟩ := uniform state domain other ran otherBranch moved
    have count := frames.sameCount state domain first other last firstBranch otherBranch lastBranch
    omega

end Belay.Sqlite.Migration
