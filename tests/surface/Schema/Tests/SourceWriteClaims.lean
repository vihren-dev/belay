import Belay

set_option doc.verso true

/-! Variable-database send contracts for source productions and DROP with write programs. -/

namespace SourceWriteClaims
open Belay.Sqlite Model

/-- An INSERT with RETURNING gives its caller rows or an SQLite error. -/
private def rowsOrError : Output → Prop
  | .rows _ | .error _ => True
  | .done _ | .oneOf _ | .unmodeled _ => False

/-- Each selection from rows or an error keeps that output form.
Proof sketch: neither constructor offers a choice of alternative row sets. -/
private theorem selected_rows {actual selected : Output} (shape : rowsOrError actual)
    (choice : OutputChoice actual selected) : rowsOrError selected := by
  cases actual <;> simp_all [rowsOrError, OutputChoice]

/-- A production returning projected rows has rows on success and its primary error on failure.
Proof sketch: distinguish the production's two effects. -/
private theorem production_rows (c : Connection) (i : Nat) (counts : Counts) (rows : List (List Value)) (effect : Effect) :
    rowsOrError (StatementExecution.ofWriteEffect c i counts (.rows rows) effect).output := by
  rcases effect with ⟨reason, reached⟩ | database <;> trivial

/-- On every valid connection where the resolved INSERT SELECT without write programs and RETURNING is modeled,
the program receives its returned rows or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem insertSelectReturning_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (cells : List Resolved.SourceCell) (query : Resolved.Query) (clauses : List Resolved.ConflictClause)
    (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query)
    (head : Resolved.Expr × String) (tail : List (Resolved.Expr × String)) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.insertSelect target cells query clauses (head :: tail) algorithm subqueries none, after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      (∃ observation, outputs = [observation] ∧ rowsOrError observation) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals
    rename_i selected choice
    refine ⟨⟨selected, rfl, selected_rows ?_ choice⟩, rfl⟩
    rename_i execution member valid
    rcases List.mem_cons.mp member with own | other
    · subst execution
      trivial
    · obtain ⟨production, _, rfl⟩ := List.mem_map.mp other
      exact production_rows _ _ _ _ _

#print axioms insertSelectReturning_trace

/-- On every valid connection where the resolved INSERT SELECT with write programs and no RETURNING is modeled,
the program receives its change count or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem insertSelectWithRules_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (cells : List Resolved.SourceCell) (query : Resolved.Query) (clauses : List Resolved.ConflictClause)
    (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query)
    (rules : Resolved.WriteRules) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.insertSelect target cells query clauses [] algorithm subqueries (some rules), after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ changes, outputs = [.done changes]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms insertSelectWithRules_trace

/-- On every valid connection where the resolved INSERT SELECT with write programs and RETURNING is modeled,
the program receives its returned rows or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem insertSelectReturningWithRules_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (cells : List Resolved.SourceCell) (query : Resolved.Query) (clauses : List Resolved.ConflictClause)
    (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query)
    (head : Resolved.Expr × String) (tail : List (Resolved.Expr × String))
    (rules : Resolved.WriteRules) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.insertSelect target cells query clauses (head :: tail) algorithm subqueries (some rules), after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ rows, outputs = [.rows rows]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms insertSelectReturningWithRules_trace

/-- On every valid connection where the resolved DROP with write programs and no RETURNING is modeled,
the program receives its change count or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem dropWithRules_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (positions : List Nat) (rules : Resolved.WriteRules) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.drop positions (some rules), after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ changes, outputs = [.done changes]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms dropWithRules_trace

end SourceWriteClaims
