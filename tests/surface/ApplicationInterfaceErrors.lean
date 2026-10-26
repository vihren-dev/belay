import Belay

/-! A fixture of `tests/surface_application_test.py` that Lean must reject (ADR 0017, S8). Each
declaration is one mistake that an interface, pairing or application can contain: a call outside the
interface, an argument of the wrong type, an interface without a partner for one name, an interface
with a different argument type, and a pairing of interfaces over different signatures. The test
checks the messages. -/

set_option doc.verso true

namespace ApplicationInterfaceErrors
open Belay.Sqlite Belay.Sqlite.Calls

/-- The names of the calls. -/
inductive Call where
  | add | find

/-- The types of the two calls. -/
@[reducible] def signature : Signature Call where
  Argument
    | .add => Int64 × String
    | .find => Int64
  Result _ := Unit

/-- An interface that has a partner for each name. -/
def complete : Interface signature
  | .add => { script := fun (id, name) => sql r"INSERT INTO customers VALUES ($id, $name)", result := fun _ => () }
  | .find => { script := fun id => sql r"SELECT 1 FROM customers WHERE id = $id", result := fun _ => () }

/-- A call outside the interface. -/
def outsideTheInterface := Application.invoke (signature := signature) .remove (1 : Int64)

/-- An argument of the wrong type. -/
def wrongArgumentType := Application.invoke (signature := signature) .find "one"

/-- An interface without an entry for the name {lit}`find`. -/
def missingEntry : Interface signature
  | .add => { script := fun (id, name) => sql r"INSERT INTO customers VALUES ($id, $name)", result := fun _ => () }

/-- An entry whose argument type is not the one of the signature. -/
def differentArgumentType : Interface signature
  | .add => complete .add
  | .find => { script := fun (_ : String) => sql r"SELECT 1", result := fun _ => () }

/-- A signature with other names. -/
@[reducible] def otherSignature : Signature Nat where
  Argument _ := Int64
  Result _ := Unit

/-- An interface over the other signature. -/
def otherInterface : Interface otherSignature := fun _ =>
  { script := fun (id : Int64) => sql r"SELECT $id", result := fun _ => () }

/-- A pairing of interfaces over different signatures. -/
def mixedPairing : Pairing signature := ⟨complete, otherInterface⟩

end ApplicationInterfaceErrors
