import Belay

set_option doc.verso true

/-! Variable-database send contracts for foreign-key or trigger writes. -/

namespace ProgramWriteClaims
open Belay.Sqlite Model

/-- On every valid connection where the resolved INSERT with write programs and RETURNING is modeled,
the program receives its returned rows or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem insertReturningWithRules_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (rows : List (List Resolved.Cell))
    (head : Resolved.Expr × String) (tail : List (Resolved.Expr × String))
    (subqueries : List Resolved.Query) (rules : Resolved.WriteRules) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.insert target rows (head :: tail) subqueries (some rules), after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ rows, outputs = [.rows rows]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms insertReturningWithRules_trace

/-- On every valid connection where the resolved UPSERT with write programs and no RETURNING is modeled,
the program receives its change count or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem upsertWithRules_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (rows : List (List Resolved.Cell))
    (clauses : List Resolved.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (subqueries : List Resolved.Query) (rules : Resolved.WriteRules) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.upsert target rows clauses [] algorithm subqueries (some rules), after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ changes, outputs = [.done changes]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms upsertWithRules_trace

/-- On every valid connection where the resolved UPSERT with write programs and RETURNING is modeled,
the program receives its returned rows or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem upsertReturningWithRules_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (rows : List (List Resolved.Cell))
    (clauses : List Resolved.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (head : Resolved.Expr × String) (tail : List (Resolved.Expr × String))
    (subqueries : List Resolved.Query) (rules : Resolved.WriteRules) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.upsert target rows clauses (head :: tail) algorithm subqueries (some rules), after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ rows, outputs = [.rows rows]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms upsertReturningWithRules_trace

/-- On every valid connection where the resolved UPDATE with write programs and no RETURNING is modeled,
the program receives its change count or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem updateWithRules_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (assignments : List (Nat × Resolved.Expr)) (filter : Option Resolved.Expr)
    (subqueries : List Resolved.Query) (rules : Resolved.WriteRules) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.update target assignments filter [] subqueries (some rules), after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ changes, outputs = [.done changes]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms updateWithRules_trace

/-- On every valid connection where the resolved UPDATE with write programs and RETURNING is modeled,
the program receives its returned rows or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem updateReturningWithRules_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (assignments : List (Nat × Resolved.Expr)) (filter : Option Resolved.Expr)
    (head : Resolved.Expr × String) (tail : List (Resolved.Expr × String))
    (subqueries : List Resolved.Query) (rules : Resolved.WriteRules) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.update target assignments filter (head :: tail) subqueries (some rules), after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ rows, outputs = [.rows rows]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms updateReturningWithRules_trace

/-- On every valid connection where the resolved DELETE with write programs and no RETURNING is modeled,
the program receives its change count or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem deleteWithRules_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (filter : Option Resolved.Expr)
    (subqueries : List Resolved.Query) (rules : Resolved.WriteRules) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.delete target filter [] subqueries (some rules), after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ changes, outputs = [.done changes]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms deleteWithRules_trace

/-- On every valid connection where the resolved DELETE with write programs and RETURNING is modeled,
the program receives its returned rows or a primary error, and the selected observation is appended
to the trace. Proof sketch: follow each continuing execution of the registered statement rule. -/
theorem deleteReturningWithRules_trace (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (filter : Option Resolved.Expr)
    (head : Resolved.Expr × String) (tail : List (Resolved.Expr × String))
    (subqueries : List Resolved.Query) (rules : Resolved.WriteRules) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.delete target filter (head :: tail) subqueries (some rules), after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ rows, outputs = [.rows rows]) ∨ (∃ code, outputs = [.error code])) ∧ final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms deleteReturningWithRules_trace

end ProgramWriteClaims
