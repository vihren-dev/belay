import Belay.Sqlite.ExecutionViewLaws
import Belay.Sqlite.ExecutionBind

set_option doc.verso true

namespace Belay.Sqlite
open Model

/-- A chosen output of a continuing step also continues: a concrete alternative is rows.
Proof sketch: raw choices use the premise; concrete choices reduce to rows. -/
private theorem choice_continues {actual selected : Output} (choice : OutputChoice actual selected)
    (continued : actual.endsRun = false) : selected.endsRun = false := by
  rcases choice with rfl | concrete
  · exact continued
  · cases actual <;> simp only at concrete
    obtain ⟨rows, _, rfl⟩ := concrete
    rfl

/-- For every stopped prefix branch and continuation annotation, projecting the bound
program's prefix gives exactly the prefix's projection. The continuation contributes
nothing. Proof sketch: induction on the prefix branch stops at its unmodeled output. -/
theorem Sql.View.project_bind_stopped {α β : Type} {program : Sql α} {clock index connection first}
    (branch : program.Branch clock index connection first) (view : View program)
    (stopped : first.value = none) (next : α → Sql β) (later : ∀ value, View (next value)) :
    (view.bind next later).project first.outputs = view.project first.outputs := by
  induction branch with
  | pure => cases stopped
  | stopped => cases view; rfl
  | @continued statement values rest clock index connection actual state others found selected result step member choice _ hypothesis =>
    obtain rfl := Sql.Branch.found_eq step member
    cases view with
    | exec hidden views =>
      have continued := choice_continues choice (runScriptStep_continued step).2
      simp only [bind, project, continued, Bool.false_eq_true, ↓reduceIte]
      rw [hypothesis (views selected) stopped]

/-- For every returning prefix branch, continuation annotation and suffix trace, projecting
their concatenation equals the prefix projection followed by that returned value's
continuation projection. The suffix can be any trace; when it is a continuation branch,
{name}`Sql.Branch.bind_return` supplies the combined execution branch. Proof sketch:
induction on the prefix branch follows its selected outputs and then its returned value. -/
theorem Sql.View.project_bind_return {α β : Type} {program : Sql α} {clock index connection first}
    (branch : program.Branch clock index connection first) (view : View program)
    {value : α} (returned : first.value = some value) (next : α → Sql β)
    (later : ∀ value, View (next value)) (suffix : List Output) :
    (view.bind next later).project (first.outputs ++ suffix) =
      view.project first.outputs ++ (later value).project suffix := by
  induction branch with
  | pure => cases returned; cases view; rfl
  | stopped => cases returned
  | @continued statement values rest clock index connection actual state others found selected result step member choice _ hypothesis =>
    obtain rfl := Sql.Branch.found_eq step member
    cases view with
    | exec hidden views =>
      have continued := choice_continues choice (runScriptStep_continued step).2
      simp only [bind, List.cons_append, project, continued, Bool.false_eq_true, ↓reduceIte]
      rw [hypothesis (views selected) returned]
      split <;> rfl

/-- For a returning prefix branch, finishing the concatenated run through a bound view
equals finishing each segment through its own view. The continuation starts after every
raw prefix step, with the full prefix connection and projected prior observations. This
identity concerns observations; actual continuation execution uses the unchanged raw
context. Proof sketch: the trace concatenation law and associativity of raw step counts. -/
theorem Sql.View.finish_bind_return {α β : Type} {program : Sql α} (state : ExecutionContext)
    {first : SqlRun α} (branch : program.Branch state.clock state.index state.connection first)
    (view : View program) {value : α} (returned : first.value = some value)
    (next : α → Sql β) (later : ∀ value, View (next value)) (last : SqlRun β) :
    (view.bind next later).finish state { last with outputs := first.outputs ++ last.outputs } =
      (later value).finish (view.finish state first) last := by
  simp only [finish, ExecutionContext.finish, List.length_append]
  rw [project_bind_return branch view returned]
  simp [List.append_assoc, Nat.add_assoc]

end Belay.Sqlite
