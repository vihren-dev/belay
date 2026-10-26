import Belay.Sqlite.Application

set_option doc.verso true

/-! Translation of applications (ADR 0017, S8). A translation replaces every call of an application
by its partner in the new interface. It keeps the control flow, because the application keeps the name
and the argument of each call and the function from a result to the rest. A program written with
{lit}`do` notation has no unique split into calls, so a program is translated through a witness: an
application together with the proof that the old interface runs it as that program. -/

namespace Belay.Sqlite

open Belay.Sqlite.Calls

namespace Calls.Pairing

variable {Name : Type} {signature : Signature Name}

/-- The translation of an application: the same application, run in the new interface. Each call
sends the script of its partner, with the same argument. -/
def translate (pairing : Pairing signature) {α : Type} (application : Application signature α) : Sql α :=
  application.interp pairing.new

/-- For every pairing and value, the translation of the application that gives the value is the
program that gives the value. Proof sketch: the definition of the translation. -/
theorem translate_pure (pairing : Pairing signature) {α : Type} (value : α) :
    pairing.translate (Application.pure value : Application signature α) = Sql.pure value := rfl

/-- For every pairing, call and continuation, the translation of a call sends the partner call, and
then the translation of the rest of the application on the result. Proof sketch: the definition of the
translation. -/
theorem translate_call (pairing : Pairing signature) {α : Type} (name : Name)
    (argument : signature.Argument name) (rest : signature.Result name → Application signature α) :
    pairing.translate (Application.call name argument rest) =
      (pairing.new.run name argument).bind fun result => pairing.translate (rest result) := rfl

/-- For every pairing, application and continuation, the translation of a bound application is the
bound translation of the parts. The continuation is translated for each value, so a continuation that
chooses a different call for a different value keeps its choice. Proof sketch:
{name}`Application.interp_bind`. -/
theorem translate_bind (pairing : Pairing signature) {α β : Type} (application : Application signature α)
    (next : α → Application signature β) :
    pairing.translate (application.bind next) =
      (pairing.translate application).bind fun value => pairing.translate (next value) :=
  Application.interp_bind pairing.new application next

end Calls.Pairing

/-- A witness that an interface runs a program: an application, and the proof that its program in the
interface is this program. The witness is data, so a translation can use its application. For example,
the application of a program that sends one call is the application that makes the call. -/
structure Application.Witness {Name : Type} {signature : Signature Name} (interface : Interface signature)
    {α : Type} (program : Sql α) where
  /-- The application that the program comes from. -/
  application : Application signature α
  /-- The program of the application in the interface is the given program. -/
  generates : application.interp interface = program

namespace Application.Witness

variable {Name : Type} {signature : Signature Name} {interface : Interface signature}

/-- The witness for the program that gives a value and sends nothing. -/
def pure {α : Type} (value : α) : Witness interface (Sql.pure value) := ⟨.pure value, rfl⟩

/-- The witness for the program that makes one call and continues with a program for each result, from a
witness for each continuation. -/
def call (name : Name) (argument : signature.Argument name) {α : Type}
    {next : signature.Result name → Sql α} (rest : ∀ result, Witness interface (next result)) :
    Witness interface ((interface.run name argument).bind next) :=
  ⟨.call name argument fun result => (rest result).application, by
    simp only [interp_call]
    exact congrArg _ (funext fun result => (rest result).generates)⟩

/-- The witness for a bind, from a witness for the first program and a witness for the continuation
at each value. -/
def bind {α β : Type} {program : Sql α} {next : α → Sql β} (first : Witness interface program)
    (rest : ∀ value, Witness interface (next value)) : Witness interface (program.bind next) :=
  ⟨first.application.bind fun value => (rest value).application, by
    rw [interp_bind, first.generates]
    exact congrArg _ (funext fun value => (rest value).generates)⟩

/-- The translation of a witnessed program: the program of its application in the new interface of
the pairing. Both interfaces use the application of the witness, so the control flow is the one of
the application and not a guess from the SQL text. -/
def translate {α : Type} {program : Sql α} (pairing : Pairing signature)
    (witness : Witness pairing.old program) : Sql α :=
  pairing.translate witness.application

/-- For every witness of a program in the old interface of a pairing, the original program is the
program of the witness's application in the old interface, and the translation is the program of the same
application in the new interface. Proof sketch: the proof field of the witness. -/
theorem original_eq {α : Type} {program : Sql α} (pairing : Pairing signature)
    (witness : Witness pairing.old program) : program = witness.application.interp pairing.old :=
  witness.generates.symm

end Application.Witness

/-- A convenient proposition: some application runs as the program in the interface. A proof of this
proposition cannot be turned into a witness, so a translation of the program needs a
{name}`Application.Witness`. -/
def Application.Generates {Name : Type} {signature : Signature Name} (interface : Interface signature)
    {α : Type} (program : Sql α) : Prop :=
  ∃ application : Application signature α, application.interp interface = program

/-- Every witness gives the proposition. Proof sketch: forget the data. -/
theorem Application.Witness.generates_prop {Name : Type} {signature : Signature Name}
    {interface : Interface signature} {α : Type} {program : Sql α} (witness : Witness interface program) :
    Application.Generates interface program :=
  ⟨witness.application, witness.generates⟩

end Belay.Sqlite
