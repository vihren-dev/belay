import Belay.Sqlite.ApplicationCalls
import Belay.Sqlite.ProgramMonadLaws

set_option doc.verso true

/-! Applications (ADR 0017, S8). An application is a program that is built from calls of an
interface signature. It keeps the name and the argument of each call and the function that
chooses the rest from the result, so the same application runs against the old interface and
against the new one. {lit}`Application.interp` gives the ordinary {name}`Belay.Sqlite.Sql` program. -/

namespace Belay.Sqlite

open Belay.Sqlite.Calls

/-- An application over a signature that gives a value of type {lit}`α`: it either stops with a
value, or makes one call with an argument and continues with the application that the call's result
chooses. The continuation can branch on the result, so later calls and their arguments depend on
earlier results. -/
inductive Application {Name : Type} (signature : Signature Name) (α : Type) where
  /-- The application that makes no call and gives the value. -/
  | pure (value : α)
  /-- The application that makes the call with this name and argument, then continues with the
  application that {lit}`rest` gives for the call's result. -/
  | call (name : Name) (argument : signature.Argument name)
      (rest : signature.Result name → Application signature α)

namespace Application

variable {Name : Type} {signature : Signature Name}

/-- The application, then the application that the function gives for its value. Both keep their
calls, so the result is again an application. -/
def bind {α β : Type} : Application signature α → (α → Application signature β) → Application signature β
  | .pure value, next => next value
  | .call name argument rest, next => .call name argument fun result => (rest result).bind next

/-- The application with the function applied to its value. It makes the same calls. -/
def map {α β : Type} (function : α → β) : Application signature α → Application signature β
  | .pure value => .pure (function value)
  | .call name argument rest => .call name argument fun result => (rest result).map function

/-- The applications form a monad, so an application is written in {lit}`do` notation: a later call
can use the result of an earlier one. -/
instance : Monad (Application signature) where
  pure := Application.pure
  bind := Application.bind
  map := Application.map

/-- The application that makes one call and gives its result. -/
def invoke (name : Name) (argument : signature.Argument name) : Application signature (signature.Result name) :=
  .call name argument .pure

/-- The program of an application in an interface: each call sends the script of the interface
for its name and argument, and the rest of the application runs on its result. This is the ordinary
{name}`Sql` program, so every theorem about programs applies. -/
def interp {α : Type} (interface : Interface signature) : Application signature α → Sql α
  | .pure value => .pure value
  | .call name argument rest => (interface.run name argument).bind fun result => (rest result).interp interface

/-- For every interface and value, the program of the application that gives the value sends no
statement and gives the value. Proof sketch: the definition of {name}`Application.interp`. -/
@[simp] theorem interp_pure {α : Type} (interface : Interface signature) (value : α) :
    (Application.pure value : Application signature α).interp interface = Sql.pure value := rfl

/-- For every interface, call and continuation, the program of a call is the program of the call
followed by the program of the rest on the call's result. Proof sketch: the definition of
{name}`Application.interp`. -/
@[simp] theorem interp_call {α : Type} (interface : Interface signature) (name : Name)
    (argument : signature.Argument name) (rest : signature.Result name → Application signature α) :
    (Application.call name argument rest).interp interface =
      (interface.run name argument).bind fun result => (rest result).interp interface := rfl

/-- For every interface, application and continuation, the program of a bound application is the
bound program of the parts. The calls of the first part come first, and the second part runs on the
first part's value. Proof sketch: induction on the first application; a call moves the bind inside
its continuation, and the program bind is associative ({name}`Sql.bind_assoc`). -/
theorem interp_bind {α β : Type} (interface : Interface signature) (application : Application signature α)
    (next : α → Application signature β) :
    (application.bind next).interp interface =
      (application.interp interface).bind fun value => (next value).interp interface := by
  induction application with
  | pure value => rfl
  | call name argument rest hypothesis =>
    simp only [bind, interp_call, hypothesis]
    exact (Sql.bind_assoc _ _ _).symm

end Application
end Belay.Sqlite
