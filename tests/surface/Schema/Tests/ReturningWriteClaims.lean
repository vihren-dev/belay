import Belay

set_option doc.verso true

/-! Variable-database send contracts for RETURNING without write programs. -/

namespace ReturningWriteClaims
open Belay.Sqlite Model

/-- On every valid connection where the resolved INSERT without write programs and RETURNING is modeled,
the program receives its returned rows or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem insertReturning_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (head : Resolved.Expr × String) (tail : List (Resolved.Expr × String))
    (target : Nat) (rows : List (List Resolved.Cell)) (subqueries : List Resolved.Query) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.insert target rows (head :: tail) subqueries none, after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ rows, outputs = [.rows rows]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms insertReturning_trace

/-- On every valid connection where the resolved UPSERT without write programs and RETURNING is modeled,
the program receives its returned rows or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem upsertReturning_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (head : Resolved.Expr × String) (tail : List (Resolved.Expr × String))
    (target : Nat) (rows : List (List Resolved.Cell)) (clauses : List Resolved.ConflictClause)
    (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.upsert target rows clauses (head :: tail) algorithm subqueries none, after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ rows, outputs = [.rows rows]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms upsertReturning_trace

/-- On every valid connection where the resolved UPDATE without write programs and RETURNING is modeled,
the program receives its returned rows or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem updateReturning_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (head : Resolved.Expr × String) (tail : List (Resolved.Expr × String))
    (target : Nat) (assignments : List (Nat × Resolved.Expr)) (filter : Option Resolved.Expr) (subqueries : List Resolved.Query) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.update target assignments filter (head :: tail) subqueries none, after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ rows, outputs = [.rows rows]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms updateReturning_trace

/-- On every valid connection where the resolved DELETE without write programs and RETURNING is modeled,
the program receives its returned rows or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem deleteReturning_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (head : Resolved.Expr × String) (tail : List (Resolved.Expr × String))
    (target : Nat) (filter : Option Resolved.Expr) (subqueries : List Resolved.Query) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.delete target filter (head :: tail) subqueries none, after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ rows, outputs = [.rows rows]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms deleteReturning_trace

end ReturningWriteClaims
