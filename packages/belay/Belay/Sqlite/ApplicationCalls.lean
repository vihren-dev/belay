import Belay.Sqlite.Program

set_option doc.verso true

/-! Application interfaces (ADR 0017, S8). An interface is a family of calls. Each call has an
argument type, a family of scripts that the argument chooses, and a function that reads the
outputs of the script into a result. The calls are data, so a proof about an application never
guesses a call from the printed SQL. A pairing gives two interfaces over one signature, so a call
of the old interface and its partner in the new interface take the same argument and give the
same result type. Lean reports a missing partner or a different argument type where the pairing
is written. -/

namespace Belay.Sqlite.Calls

open Belay.Sqlite.Model

/-- The types of a family of calls: for each call name, the type of its argument and the type of its
result. Two interfaces that use one signature accept the same arguments for the same name. The name
type can be an enumeration, a number or any other type; two names can have the same scripts. -/
structure Signature (Name : Type) where
  /-- The type of the argument of the call with this name. -/
  Argument : Name → Type
  /-- The type of the result of the call with this name. -/
  Result : Name → Type

/-- One call of an interface: the scripts that an argument selects, and how the call reads its
result from the outputs of those scripts. A script can hold more than one statement, and the
argument can be any Lean type. For example, a call with the argument type {lean}`Nat` can send one
statement per number. A call that needs no result uses {lean}`PUnit` and ignores the outputs. -/
structure Entry (Argument Result : Type) where
  /-- The script that the call sends for an argument. -/
  script : Argument → Script
  /-- The result that the call gives for the outputs of its script, one output for each
  statement, in order ({name}`send`). -/
  result : List Output → Result

/-- The program of a call at an argument: it sends the script of the argument and gives the result
of the outputs. Its statements are the statements of the script, in order, and it adds no other
statement. -/
def Entry.program {Argument Result : Type} (entry : Entry Argument Result) (argument : Argument) :
    Sql Result :=
  (send (entry.script argument)).map entry.result

/-- An interface for a signature: one {name}`Entry` for each call name, with the argument and
result types that the signature gives. -/
abbrev Interface {Name : Type} (signature : Signature Name) : Type :=
  (name : Name) → Entry (signature.Argument name) (signature.Result name)

/-- An old and a new interface over one signature. The call of a name in the old interface has the
call of the same name in the new interface as its partner. Because both interfaces use the
signature, a partner always exists and has the same argument and result types. -/
structure Pairing {Name : Type} (signature : Signature Name) where
  /-- The interface of the application before the migration. -/
  old : Interface signature
  /-- The interface of the application after the migration. -/
  new : Interface signature

/-- The program of the call with a name and an argument, in an interface. -/
def Interface.run {Name : Type} {signature : Signature Name} (interface : Interface signature)
    (name : Name) (argument : signature.Argument name) : Sql (signature.Result name) :=
  (interface name).program argument

end Belay.Sqlite.Calls
