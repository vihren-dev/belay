import Belay.Sqlite.ExecutionWPLaws

set_option doc.verso true

/-! The two facts that let {lit}`sql_run` start from a standard triple (ADR 0017, S6): a triple about a
program is a claim that the program checks its postcondition from every context that meets the
precondition, and a weakest precondition of a program is its check. Both hold by definition of the
predicate transformer {name}`Belay.Sqlite.Sql.transformer`; they are stated so that the tactic uses a theorem and not a
change of the goal. -/

namespace Belay.Sqlite
open Std.Do

/-- For every program, precondition on contexts and postcondition: the standard triple whose precondition
and postcondition are pure claims holds exactly when the program checks the postcondition ({name}`Sql.check`)
from every context that meets the precondition. In plain words, the triple notation adds nothing to the check
for a program of SQL. Proof sketch: both sides unfold to the same statement; the transformer of the program is
its check. -/
theorem Sql.triple_iff_check {α : Type} {program : Sql α} {pre : ExecutionContext → Prop}
    {post : α → ExecutionContext → Prop} :
    (⦃fun state => ⌜pre state⌝⦄ program ⦃⇓ value state => ⌜post value state⌝⦄) ↔
      ∀ state, pre state → program.check post state :=
  Iff.rfl

/-- For every program, postcondition and context: the weakest precondition of the program for the
postcondition holds at the context exactly when the program checks the postcondition there. In plain words,
the verification conditions that {lit}`mvcgen` leaves for a program of SQL are checks. Proof sketch: the
transformer of the program is its check. -/
theorem Sql.wp_down_iff_check {α : Type} (program : Sql α) (post : PostCond α (.arg ExecutionContext .pure))
    (state : ExecutionContext) :
    (wp⟦program⟧ post state).down ↔ program.check (fun value final => (post.1 value final).down) state :=
  Iff.rfl

end Belay.Sqlite
