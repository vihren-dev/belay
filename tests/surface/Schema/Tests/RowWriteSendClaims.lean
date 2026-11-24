import Belay

set_option doc.verso true

/-! The output seen by a caller for each modeled row-by-row write and each admitted source order. -/

namespace RowWriteSendClaims
open Belay.Sqlite Model

/-- Writes without RETURNING report their change count or SQLite's primary error code. -/
private def countOrError : Output → Prop
  | .done _ | .error _ => True
  | .rows _ | .oneOf _ | .unmodeled _ => False

/-- Each permitted observation of a count or error is itself a count or error.
Proof sketch: neither output has an alternative set of rows. -/
private theorem choice_write {actual selected : Output} (write : countOrError actual)
    (choice : OutputChoice actual selected) : countOrError selected := by
  cases actual <;> simp_all [countOrError, OutputChoice]

/-- A production returning a count on success gives a count or error on any write effect.
Proof sketch: compute the successful and failed writes. -/
private theorem production_write (connection : Connection) (index : Nat) (counts : Counts) (effect : Effect) :
    countOrError (StatementExecution.ofWriteEffect connection index counts (.done (counts.changes.getD 0)) effect).output := by
  rcases effect with ⟨reason, reached⟩ | database <;> trivial

/-- For each valid connection and modeled UPSERT without RETURNING or write rules,
the caller sees exactly one count or error and that observation is appended to the trace.
Proof sketch: the conflict outcome selects success or failure in the UPSERT rule. -/
theorem upsert_output (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (rows : List (List Resolved.Cell)) (clauses : List Resolved.ConflictClause)
    (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt =
      .ok (.upsert target rows clauses [] algorithm subqueries none, after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      (∃ out, outputs = [out] ∧ countOrError out) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals exact ⟨⟨_, rfl, trivial⟩, rfl⟩

#print axioms upsert_output

/-- For each valid connection and modeled INSERT from a query without RETURNING or write rules,
the observation appended to the trace is a singleton count or error for the production actually
chosen. Proof sketch: an execution is either the main one or a member of the mapped further
productions. Each has a count or error, so its selected output has the same form. -/
theorem insertSelect_output (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (cells : List Resolved.SourceCell) (query : Resolved.Query) (clauses : List Resolved.ConflictClause)
    (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt =
      .ok (.insertSelect target cells query clauses [] algorithm subqueries none, after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      (∃ out, outputs = [out] ∧ countOrError out) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals
    rename_i selected choice
    refine ⟨⟨selected, rfl, choice_write ?_ choice⟩, rfl⟩
    rename_i execution member valid
    rcases List.mem_cons.mp member with own | other
    · subst execution
      trivial
    · obtain ⟨production, _, rfl⟩ := List.mem_map.mp other
      exact production_write _ _ _ _

#print axioms insertSelect_output

end RowWriteSendClaims
