import Belay.Sqlite.Program

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every program, mapping the identity function leaves the program unchanged.
Proof sketch: induction on the program, including each output continuation. -/
theorem Sql.map_id {α : Type} (program : Sql α) : program.map id = program := by
  induction program with
  | pure value => rfl
  | exec statement values rest later =>
    simp only [Sql.map]
    exact congrArg (Sql.exec statement values) (funext later)

/-- For every program and two continuations, binding twice equals binding once to their
composition. Proof sketch: induction on the program, with function extensionality at each
statement's output continuation. -/
theorem Sql.bind_assoc {α β γ : Type} (program : Sql α) (next : α → Sql β) (last : β → Sql γ) :
    (program.bind next).bind last = program.bind (fun value => (next value).bind last) := by
  induction program with
  | pure value => rfl
  | exec statement values rest later =>
    simp only [Sql.bind]
    exact congrArg (Sql.exec statement values) (funext later)

/-- For every program and function, binding to the pure result of that function equals
mapping the function. Proof sketch: induction on the program; both preserve each statement
and apply the function only to the final value. -/
theorem Sql.bind_pure_map {α β : Type} (program : Sql α) (function : α → β) :
    program.bind (fun value => .pure (function value)) = program.map function := by
  induction program with
  | pure value => rfl
  | exec statement values rest later =>
    simp only [Sql.bind, Sql.map]
    exact congrArg (Sql.exec statement values) (funext later)

/-- The program monad satisfies the identity, pure and composition laws for every program,
including continuations that inspect any output constructor. Proof sketch: the three
structural laws above supply the standard library's monad constructor. -/
instance : LawfulMonad Sql := LawfulMonad.mk' Sql
  Sql.map_id (fun _ _ => rfl) Sql.bind_assoc
  (bind_pure_comp := fun function program => Sql.bind_pure_map program function)

/-- For all lists of statements, sending their concatenation equals sending each list in
order and concatenating their returned outputs. Proof sketch: induction on the first list;
the monad laws move the map of its first output across the continuation. -/
theorem sendStatements_append (first second : List (Syntax.Statement × List Value)) :
    sendStatements (first ++ second) = (do
      let before ← sendStatements first
      let after ← sendStatements second
      pure (before ++ after)) := by
  induction first with
  | nil =>
    change sendStatements second = (sendStatements second).bind (fun value => .pure (id value))
    rw [Sql.bind_pure_map, Sql.map_id]
  | cons head tail later =>
    rcases head with ⟨statement, values⟩
    simp only [List.cons_append, sendStatements, later]
    change Sql.exec statement values _ = Sql.exec statement values _
    congr 1
    funext output
    change (Sql.map (fun x => output :: x)
      ((sendStatements tail).bind fun before => (sendStatements second).bind fun after => .pure (before ++ after))) =
      ((sendStatements tail).map (fun x => output :: x)).bind
        (fun before => (sendStatements second).bind fun after => .pure (before ++ after))
    simp only [← Sql.bind_pure_map, Sql.bind_assoc, Sql.bind]
    rfl

/-- For all scripts, sending their concatenation equals sending the first script and then
the second, with their output lists concatenated. Proof sketch: {name}`sendStatements_append`
applied to the statements of the two scripts. -/
theorem send_append (first second : Script) :
    send (first ++ second) = (do
      let before ← send first
      let after ← send second
      pure (before ++ after)) :=
  sendStatements_append first.statements second.statements

end Belay.Sqlite
