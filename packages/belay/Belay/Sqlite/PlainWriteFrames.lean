import Belay.Sqlite.SqlFrames
import Belay.Sqlite.ExecutionStep

set_option doc.verso true

/-!
Frames of scripts of plain writes and reads (ADR 0017, S6). A script whose statements all resolve to plain
writes of other tables, or to reads, keeps the catalog, the table at a position, the snapshot of an open
transaction and the settings, on every branch of the program that sends it. The rule needs only the resolution
of each statement, not the engine; the step law is {name}`Belay.Sqlite.Model.Connection.shelter_step`.
Statements with trigger and foreign-key rules, and statements that change the catalog, are outside the rule.
-/

namespace Belay.Sqlite
open Model

/-- Whether a statement of a script is sheltered from a position when it resolves from the given state of
resolution: every successful resolution of it is a resolved statement that is sheltered
({name}`Resolved.Statement.ShelteredFrom`). A statement that resolution refuses is sheltered, because its
step stops the run without a change. -/
def Model.Syntax.Statement.ShelteredAt (position : Nat) (state : ResolveState) (statement : Syntax.Statement) : Prop :=
  ∀ resolved after, resolveStatement runContext state statement = .ok (resolved, after) →
    resolved.ShelteredFrom position

/-- For every position, list of statements with values and context: if every statement is sheltered from the
position at the state of resolution of the connection of the context, then the program that sends them keeps the
shelter of the position on every branch. In plain words, a script of plain writes of other tables and reads
cannot change the catalog, the table at the position, the snapshot or the settings, whatever the clock, the
counters and the outputs that its branches choose. Proof sketch: induction on the list. Each step keeps the
shelter ({name}`Connection.shelter_step`), so the state of resolution is the same for the rest
({name}`Connection.shelter_resolveState`), and {name}`Sql.Frame.exec` and {name}`Sql.Frame.map` join
the steps. -/
theorem Sql.Frame.sendStatements_sheltered (position : Nat) :
    ∀ (statements : List (Syntax.Statement × List Value)) (state : ExecutionContext),
      (∀ entry ∈ statements, entry.1.ShelteredAt position state.connection.resolveState) →
      (sendStatements statements).Frame (Connection.shelter position) state
  | [], state, _ => Sql.Frame.pure _ _ _
  | (statement, values) :: rest, state, sheltered => by
    refine Sql.Frame.exec fun actual next others step found member => ?_
    simp only [runScriptStep_executions step, List.mem_singleton] at member
    subst member
    have shape : ∀ resolved after,
        resolveStatement runContext state.connection.resolveState statement = .ok (resolved, after) →
        resolved.ShelteredFrom position := sheltered (statement, values) (by simp)
    have resolves : ∃ resolved after,
        resolveStatement runContext state.connection.resolveState statement = .ok (resolved, after) := by
      obtain ⟨resolved, after, value, same, -⟩ := runScriptStep_continued_spec step |>.2
      exact ⟨resolved, after, same⟩
    obtain ⟨resolved, after, ok⟩ := resolves
    obtain ⟨-, kept⟩ := Connection.shelter_step ok (shape _ _ ok) step
    refine ⟨kept, fun selected _ => ?_⟩
    refine Sql.Frame.map (Sql.Frame.sendStatements_sheltered position rest _ fun entry member => ?_)
    have same := Connection.shelter_resolveState kept
    simp only [ExecutionContext.next]
    rw [same]
    exact sheltered entry (List.mem_cons_of_mem _ member)

end Belay.Sqlite
