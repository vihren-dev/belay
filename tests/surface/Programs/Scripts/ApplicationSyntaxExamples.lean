import Belay

/-! A fixture module of `tests/surface_application_syntax_test.py`: the simulation syntax and the
{lit}`#explain` command (ADR 0017, S8). The four forms {lit}`M simulates P`, {lit}`M simulates P where G`,
{lit}`M simulates P scoped by R` and {lit}`M simulates P scoped by R where G` elaborate to the public
claims {name}`Belay.Sqlite.Simulation` and {name}`Belay.Sqlite.ScopedClaim`. The fixture checks that each
form is the primitive it names, and that the explanation of the two claims says what each one compares. -/

set_option doc.verso true
set_option sql.check false

namespace ApplicationSyntaxFixture
open Belay.Sqlite Belay.Sqlite.Calls

/-- A signature with one call that gives the outputs of its statement. -/
@[reducible] def readSignature : Signature Unit where
  Argument _ := Unit
  Result _ := List Output

/-- The interface that reads the table of customers. -/
def readCustomers : Interface readSignature
  | () => { script := fun _ => sql r"SELECT 1 FROM customers", result := id }

/-- The pairing of the interface with itself. -/
def samePairing : Pairing readSignature := ⟨readCustomers, readCustomers⟩

/-- The migration, as a program. -/
def migration : Sql (List Output) := send (sql r"CREATE TABLE audit(id INTEGER)")

/-- A query guard on the admitted contexts. -/
def sqlGuard : Script := sql r"SELECT 1 FROM customers"

/-- The relation that the scoped forms use: the contexts have equal clocks. -/
def sameClock (older newer : ExecutionContext) : Prop := older.clock = newer.clock

/-- The unguarded full form is the full-state simulation with the predicate that admits every
context. Plain words: the notation adds nothing to the primitive. -/
theorem full_form_is_the_primitive :
    (migration simulates samePairing) = Simulation (Runnable.toSql migration) (fun _ => True) samePairing := rfl

/-- The guarded full form reads the guard at the real context. -/
theorem guarded_full_form_is_the_primitive :
    (migration simulates samePairing where sqlGuard) =
      Simulation (Runnable.toSql migration) (fun context => Holds.inContext sqlGuard context (by check_query))
        samePairing := rfl

/-- The scoped form is the scoped claim of the relation, and the two claims are different
propositions. -/
theorem scoped_form_is_the_primitive :
    (migration simulates samePairing scoped by sameClock) =
      ScopedClaim (Runnable.toSql migration) (fun _ => True) sameClock samePairing := rfl

#print axioms full_form_is_the_primitive
#print axioms guarded_full_form_is_the_primitive
#print axioms scoped_form_is_the_primitive

#explain migration simulates samePairing
#explain migration simulates samePairing where sqlGuard
#explain migration simulates samePairing scoped by sameClock
#explain migration simulates samePairing scoped by sameClock where sqlGuard

end ApplicationSyntaxFixture
