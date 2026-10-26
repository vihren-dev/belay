import Belay

/-! A fixture module of `tests/surface_application_test.py`: interfaces, pairings and applications
(ADR 0017, S8). The shop interface has calls with different argument lists, a call of two statements,
and two calls with the same script that differ by name. The fixture checks that the program of an
application is the ordinary program, that translation keeps the control flow, and that two witnesses of
one program translate differently. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace ApplicationInterfaceFixture
open Belay.Sqlite Belay.Sqlite.Calls
open Belay.Sqlite.Model hiding Database

/-- The names of the calls of the shop. {lit}`count` and {lit}`recount` have the same script but are
two calls with two identities. -/
inductive ShopCall where
  | add | find | addTwo | count | recount
  deriving DecidableEq

/-- The argument and result types of the shop calls. The calls have an id and a name, an id, two
customers, and no argument. -/
@[reducible] def shopSignature : Signature ShopCall where
  Argument
    | .add => Int64 × String
    | .find => Int64
    | .addTwo => (Int64 × String) × (Int64 × String)
    | .count => Unit
    | .recount => Unit
  Result
    | .add => Unit
    | .find => Bool
    | .addTwo => Unit
    | .count => Nat
    | .recount => Nat

/-- Read the number from the first output of a count query, or zero. -/
def countOf : List Output → Nat
  | [.rows [[.integer n]]] => n.toNat
  | _ => 0

/-- Whether the last output of a lookup has a row. -/
def hasRow : List Output → Bool
  | [.rows (_ :: _)] => true
  | _ => false

/-- The shop interface before the migration. -/
def oldShop : Interface shopSignature
  | .add => { script := fun (id, name) => sql r"INSERT INTO customers VALUES ($id, $name)", result := fun _ => () }
  | .find => { script := fun id => sql r"SELECT 1 FROM customers WHERE id = $id", result := hasRow }
  | .addTwo => { script := fun ((a, x), (b, y)) => sql r"INSERT INTO customers VALUES ($a, $x); INSERT INTO customers VALUES ($b, $y)", result := fun _ => () }
  | .count => { script := fun _ => sql r"SELECT count(*) FROM customers", result := countOf }
  | .recount => { script := fun _ => sql r"SELECT count(*) FROM customers", result := countOf }

/-- The shop interface after the migration: the lookup reads another column. -/
def newShop : Interface shopSignature
  | .find => { script := fun id => sql r"SELECT 1 FROM customers WHERE rowid = $id", result := hasRow }
  | name => oldShop name

/-- The pairing of the two shop interfaces. -/
def shopPairing : Pairing shopSignature := ⟨oldShop, newShop⟩

/-- An application that adds a customer, looks it up, and then makes a different call and gives a
different number depending on the result of the lookup. -/
def welcome (id : Int64) (name : String) : Application shopSignature Nat := do
  let _ ← Application.invoke (signature := shopSignature) .add (id, name)
  let found ← Application.invoke (signature := shopSignature) .find id
  if found then Application.invoke (signature := shopSignature) .count ()
  else Application.invoke (signature := shopSignature) .recount ()

/-- The same program written by hand as a {lit}`Sql` program: each call is the map of its script. -/
def welcomeByHand (id : Int64) (name : String) : Sql Nat :=
  ((send (sql r"INSERT INTO customers VALUES ($id, $name)")).map fun _ => ()).bind fun _ =>
    ((send (sql r"SELECT 1 FROM customers WHERE id = $id")).map hasRow).bind fun found =>
      if found then (send (sql r"SELECT count(*) FROM customers")).map countOf
      else (send (sql r"SELECT count(*) FROM customers")).map countOf

/-- The program of the application in the old interface is the hand-written program. Proof sketch:
unfold the interpretation of each call; each call is the map of its script. -/
theorem welcome_is_the_program (id : Int64) (name : String) :
    (welcome id name).interp oldShop = welcomeByHand id name := by
  simp only [welcome, welcomeByHand, bind, Application.bind, Application.invoke, Application.interp, Interface.run, Entry.program, oldShop]
  congr 1
  funext _
  congr 1
  funext found
  cases found <;> rfl

/-- One customer. -/
def sample : Database := db! r"
  CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT);
  INSERT INTO customers VALUES(1, 'Ada');"

/-- The environment of the sample: all inputs are known after the setup INSERT. -/
def environment : Env :=
  { clock := some (fun _ => 0)
    counters := { changes := some 1, totalChanges := some 1, lastInsertRowid := some 1 } }

/-- The first context of the sample. -/
def initial : ExecutionContext := ExecutionContext.initial sample environment

/-- The program of the application in the new interface is the translated program, and the translation
replaces the call of {lit}`find` by its partner and nothing else. Proof sketch: unfold the translation of
each call. -/
theorem translation_replaces_each_call (id : Int64) (name : String) :
    shopPairing.translate (welcome id name) =
      ((send (sql r"INSERT INTO customers VALUES ($id, $name)")).map fun _ => ()).bind fun _ =>
        ((send (sql r"SELECT 1 FROM customers WHERE rowid = $id")).map hasRow).bind fun found =>
          if found then (send (sql r"SELECT count(*) FROM customers")).map countOf
          else (send (sql r"SELECT count(*) FROM customers")).map countOf := by
  simp only [welcome, Pairing.translate, bind, Application.bind, Application.invoke, Application.interp,
    Interface.run, Entry.program, shopPairing, newShop, oldShop]
  congr 1
  funext _
  congr 1
  funext found
  cases found <;> rfl

/-- The old interface runs the two count calls as the same program. This is why a program does not
tell which call it came from. -/
theorem count_calls_have_one_program :
    (Application.invoke (signature := shopSignature) .count ()).interp oldShop =
      (Application.invoke (signature := shopSignature) .recount ()).interp oldShop := rfl

/-- The two count calls are two different applications. -/
theorem count_calls_have_two_identities :
    Application.invoke (signature := shopSignature) .count () ≠
      Application.invoke (signature := shopSignature) .recount () := by
  intro same
  injection same with h
  cases h

/-- A pairing in which the partner of {lit}`recount` counts nothing. -/
def splitShop : Pairing shopSignature :=
  { old := oldShop
    new := fun
      | .recount => { script := fun _ => sql r"SELECT 0", result := countOf }
      | name => oldShop name }

/-- The program that both count calls give in the old interface has two witnesses. -/
def countByName : Application.Witness oldShop (oldShop.run .count ()) := ⟨.call .count () .pure, rfl⟩

/-- The same program, witnessed by the other call. -/
def countByRecount : Application.Witness oldShop (oldShop.run .count ()) := ⟨.call .recount () .pure, rfl⟩

/-- The two witnesses of one program have different translations: one counts the customers and the
other gives 0. The first context of the sample shows it. Proof sketch: kernel evaluation of the two
translated runs. -/
theorem witness_decides_the_translation :
    ((countByName.translate splitShop).runFrom initial.clock initial.index initial.connection).value = some 1 ∧
    ((countByRecount.translate splitShop).runFrom initial.clock initial.index initial.connection).value = some 0 := by
  constructor <;> decide +kernel

/-- Each call has the stated outputs on the first context. -/
theorem old_find_on_sample :
    ((oldShop.run .find (1 : Int64)).runFrom initial.clock initial.index initial.connection).value = some true := by
  decide +kernel

#print axioms welcome_is_the_program
#print axioms translation_replaces_each_call
#print axioms count_calls_have_one_program
#print axioms count_calls_have_two_identities
#print axioms witness_decides_the_translation

end ApplicationInterfaceFixture
