import Belay.Sqlite.Model.CompoundRun

set_option doc.verso true

/-! Compound rules of a SELECT (ADR 0027, D1, phase {lit}`compound`): how a compound ends when
each of its terms ends without a failure, and the rows of a chain of {lit}`UNION ALL`. A compound
whose terms all end without a failure and whose window binds ends without a failure in every
plan order that the model describes. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every context, outer row, window counters and term indexes whose runs for the outer row
all end with {lean}`RunEnd.done`, the terms that give their rows directly end with
{lean}`RunEnd.done` ({name}`directTerms`). Proof sketch: induction on the indexes; a term that
ends done passes the counters on. -/
theorem directTerms_done (context : EvalContext) (outer : List Value) :
    ∀ (indexes : List Nat) (count : WindowCount),
      (∀ index ∈ indexes, (context.subqueries index outer).ending = .done) →
        directTerms context outer count indexes = .done
  | [], _, _ => rfl
  | index :: later, count, done => by
    unfold directTerms
    split
    · rfl
    · simp only [done index List.mem_cons_self, RunEnd.direct]
      exact directTerms_done context outer later _ fun other member => done other (List.mem_cons_of_mem _ member)

/-- For every context, compound, outer row, left rows and steps whose terms all end with
{lean}`RunEnd.done` for the outer row, the left operand that starts done ({lit}`state`) stays done after the
steps ({name}`fillSteps`). Proof sketch: induction on the steps; each step runs its term or skips
it, and both end done. -/
theorem fillSteps_done (context : EvalContext) (compound : Compound) (outer : List Value) :
    ∀ (steps : List (CompoundOperator × Nat)) (state : List (List Value) × RunEnd), state.2 = .done →
      (∀ step ∈ steps, (context.subqueries step.2 outer).ending = .done) →
        (fillSteps context compound outer state steps).2 = .done
  | [], _, start, _ => start
  | (operator, index) :: later, (rows, ending), start, done => by
    simp only at start
    subst start
    refine fillSteps_done context compound outer later _ ?_ fun step member => done step (List.mem_cons_of_mem _ member)
    have right := done (operator, index) List.mem_cons_self
    simp only at right
    simp only
    split <;> (try split) <;> simp [right, RunEnd.intoTable]

/-- For every context, compound, outer row, window counters, operator, right term, earlier steps
and chain of term indexes, when the first term, the right term, the term of each earlier step and
each term of the chain end with {lean}`RunEnd.done` for the outer row, the step before the chain
ends with {lean}`RunEnd.done` ({name}`stepEnd`). Proof sketch: the left operand ends done
({name}`fillSteps_done`), the right term ends done or is skipped, and the chain ends done
({name}`directTerms_done`). -/
theorem stepEnd_done (context : EvalContext) (compound : Compound) (outer : List Value) (count : WindowCount)
    (operator : CompoundOperator) (index : Nat) (earlier : List (CompoundOperator × Nat)) (chain : List Nat)
    (first : (context.subqueries compound.first outer).ending = .done)
    (right : (context.subqueries index outer).ending = .done)
    (before : ∀ step ∈ earlier, (context.subqueries step.2 outer).ending = .done)
    (later : ∀ index ∈ chain, (context.subqueries index outer).ending = .done) :
    stepEnd context compound outer (some count) operator index earlier chain = .done := by
  have left := fillSteps_done context compound outer earlier.reverse
    ((context.subqueries compound.first outer).rows, (context.subqueries compound.first outer).ending.intoTable)
    (by simp [first, RunEnd.intoTable]) fun step member => before step (List.mem_reverse.mp member)
  unfold stepEnd
  dsimp only
  generalize fillSteps context compound outer
    ((context.subqueries compound.first outer).rows, (context.subqueries compound.first outer).ending.intoTable)
    earlier.reverse = state at left ⊢
  obtain ⟨leftRows, leftEnd⟩ := state
  simp only at left
  subst left
  cases operator <;> simp [right, RunEnd.intoTable, directTerms_done context outer chain _ later]

/-- For every context, compound, outer row, window counters, steps in reverse order and chain of
term indexes, when the first term, the term of each step and each term of the chain end with
{lean}`RunEnd.done` for the outer row, the compound without {lit}`ORDER BY` ends with
{lean}`RunEnd.done` ({name}`chainEnd`). Proof sketch: induction on the steps; a {lit}`UNION ALL`
step joins the chain, and any other step ends done by {name}`stepEnd_done`. -/
theorem chainEnd_done (context : EvalContext) (compound : Compound) (outer : List Value) (count : WindowCount)
    (first : (context.subqueries compound.first outer).ending = .done) :
    ∀ (steps : List (CompoundOperator × Nat)) (chain : List Nat),
      (∀ step ∈ steps, (context.subqueries step.2 outer).ending = .done) →
      (∀ index ∈ chain, (context.subqueries index outer).ending = .done) →
        chainEnd context compound outer (some count) steps chain = .done
  | [], chain, _, later => by
    unfold chainEnd
    exact directTerms_done context outer _ count fun index member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact first
      · exact later index member
  | (operator, index) :: earlier, chain, done, later => by
    have right := done (operator, index) List.mem_cons_self
    have before : ∀ step ∈ earlier, (context.subqueries step.2 outer).ending = .done :=
      fun step member => done step (List.mem_cons_of_mem _ member)
    cases operator with
    | unionAll =>
      exact chainEnd_done context compound outer count first earlier (index :: chain) before fun other member => by
        rcases List.mem_cons.mp member with rfl | member
        · exact right
        · exact later other member
    | union | except | intersect =>
      exact stepEnd_done context compound outer count _ index earlier chain first right before later

/-- Compound end rule: for every context, query whose window binds to some query {lit}`bound`,
compound and outer row, when the run of each term of the compound ({name}`Compound.terms`) for the
outer row ends with {lean}`RunEnd.done`, the compound ends with {lean}`RunEnd.done`
({name}`Compound.ending`), with or without {lit}`ORDER BY`. Proof sketch: with {lit}`ORDER BY`
every term ends done; without it, {name}`chainEnd_done` over the reversed steps. -/
theorem Compound.ending_done (context : EvalContext) {query bound : Query} (compound : Compound) (outer : List Value)
    (window : query.bindWindow context.parameters = some bound)
    (done : ∀ index ∈ compound.terms, (context.subqueries index outer).ending = .done) :
    compound.ending context query outer = .done := by
  unfold Compound.ending
  simp only [window, Option.map_some]
  split
  · exact chainEnd_done context compound outer _ (done _ List.mem_cons_self) _ [] (fun step member => done _ (by
      simp only [Compound.terms, List.mem_cons, List.mem_map]
      exact .inr ⟨step, List.mem_reverse.mp member, rfl⟩)) (by simp)
  · have all : (compound.terms.all fun index => (context.subqueries index outer).ending == RunEnd.done) = true := by
      simpa using done
    simp [all]

/-- {lit}`UNION ALL` rule: for every context, first term, collations, outer row and terms after it,
each joined by {lit}`UNION ALL`, the rows of the compound for the outer row
({name}`Compound.rows`) are the rows of each term for the outer row, in term order, with their
multiplicity. Proof sketch: {lit}`UNION ALL` appends the right rows; induction on the later terms. -/
theorem Compound.rows_unionAll (context : EvalContext) (first : Nat) (collations : List Collation)
    (outer : List Value) (later : List Nat) :
    Compound.rows context { first, rest := later.map (.unionAll, ·), collations } outer =
      (first :: later).flatMap fun index => (context.subqueries index outer).rows := by
  unfold Compound.rows Compound.combined
  suffices step : ∀ (start : List (List Value)) (certain : Bool),
      ((later.map (CompoundOperator.unionAll, ·)).foldl (fun (rows, certain) (operator, index) =>
        (operator.combine collations rows (context.subqueries index outer).rows,
          certain && operator.keepsCertain collations rows (context.subqueries index outer).rows))
        (start, certain)).1 = start ++ later.flatMap fun index => (context.subqueries index outer).rows by
    simpa using step _ true
  induction later with
  | nil => simp
  | cons index rest ih =>
    intro start certain
    rw [List.map_cons, List.foldl_cons]
    exact (ih _ _).trans (by simp [CompoundOperator.combine])

end Belay.Sqlite.Model.Resolved
