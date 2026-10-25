import Belay.Sqlite.ProgramQueries
import Belay.Sqlite.ExecutionStep
import Belay.Sqlite.ExecutionWPLaws

set_option doc.verso true

namespace Belay.Sqlite
open Model Std.Do

/-- Mapping a program's returned value checks exactly the composed postcondition at the
same reached context. Unmodeled stops remain forbidden. Proof sketch: map is bind with pure. -/
theorem Sql.check_map {α β : Type} (program : Sql α) (function : α → β)
    (post : β → ExecutionContext → Prop) (state : ExecutionContext) :
    (program.map function).check post state ↔
      program.check (fun value final => post (function value) final) state := by
  rw [← Sql.bind_pure_map, Sql.check_bind]
  simp only [Sql.check_pure]

/-- Sending an empty script checks the empty returned output list at the unchanged context.
Proof sketch: the empty sender is pure. -/
theorem check_send_empty (post : List Output → ExecutionContext → Prop) (state : ExecutionContext) :
    (send (⟨[]⟩ : Script)).check post state ↔ post [] state := Sql.check_pure [] post state

/-- Sending appended scripts checks the first script, then the second from each exact
reached context. The returned output lists concatenate. Errors can continue and unmodeled
stops cannot. Proof sketch: send-append is bind followed by mapping concatenation. -/
theorem check_send_append (first second : Script) (post : List Output → ExecutionContext → Prop)
    (state : ExecutionContext) :
    (send (first ++ second)).check post state ↔
      (send first).check (fun before reached =>
        (send second).check (fun after final => post (before ++ after) final) reached) state := by
  rw [send_append]
  change ((send first).bind (fun before => (send second).bind
    (fun after => .pure (before ++ after)))).check post state ↔ _
  simp only [Sql.check_bind, Sql.check_pure]

/-- A one-statement query checks its converted result for every raw or concrete output of
the actual step, using the full next context. SQL errors become Except errors; an unmodeled
step fails. Proof sketch: unfold query and apply the execution-step and pure rules. -/
theorem check_query (script : Script) (one : script.statements.length = 1)
    (post : Except Nat (List (List Value)) → ExecutionContext → Prop) (state : ExecutionContext) :
    (query script one).check post state ↔
      let (statement, values) := script.statements[0]'(by rw [one]; exact Nat.one_pos)
      match runScriptStep runContext state.clock state.index state.connection statement values with
      | .ended _ => False
      | .continued actual connection =>
        ∀ selected, OutputChoice actual selected → post (queryResult selected) (state.next selected connection) := by
  unfold query
  generalize selected : script.statements[0] = entry
  rcases entry with ⟨statement, values⟩
  dsimp only
  split
  · rename_i reason step
    exact iff_false_intro (Sql.check_stopped step post)
  · rename_i actual connection step
    rw [Sql.check_continued step]
    simp only [Sql.check_pure]

/-- Single-value checking is query checking with its existing conversion: an error or a
result other than one row of one column becomes none. It preserves the query's full trace
and context. Proof sketch: single maps query using singleValue. -/
theorem check_single (script : Script) (one : script.statements.length = 1)
    (post : Option Value → ExecutionContext → Prop) (state : ExecutionContext) :
    (single script one).check post state ↔
      (query script one).check (fun rows final => post (singleValue rows) final) state :=
  Sql.check_map (query script one) singleValue post state

/-- The arbitrary checked postcondition for a sent script supplies a standard triple.
This rule works for BEGIN, COMMIT and ROLLBACK without resetting contexts or handling errors
implicitly. Proof sketch: the standard transformer is exactly the public branch check. -/
@[spec] theorem send_spec (script : Script) (post : List Output → ExecutionContext → Prop) :
    ⦃fun state => ⌜(send script).check post state⌝⦄ send script
      ⦃⇓ value state => ⌜post value state⌝⦄ := fun _ checked => checked

/-- A one-statement query's branch check supplies its standard triple for any postcondition.
Use {name}`check_query` to discharge the actual step and every selected output.
Proof sketch: the standard transformer unfolds to the given branch check. -/
@[spec] theorem query_spec (script : Script) (one : script.statements.length = 1)
    (post : Except Nat (List (List Value)) → ExecutionContext → Prop) :
    ⦃fun state => ⌜(query script one).check post state⌝⦄ query script one
      ⦃⇓ value state => ⌜post value state⌝⦄ := fun _ checked => checked

/-- A single-value query's branch check supplies its standard triple for any postcondition.
Use {name}`check_single` to retain the existing error conversion.
Proof sketch: the standard transformer unfolds to the given branch check. -/
@[spec] theorem single_spec (script : Script) (one : script.statements.length = 1)
    (post : Option Value → ExecutionContext → Prop) :
    ⦃fun state => ⌜(single script one).check post state⌝⦄ single script one
      ⦃⇓ value state => ⌜post value state⌝⦄ := fun _ checked => checked

end Belay.Sqlite
