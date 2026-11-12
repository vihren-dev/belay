import Belay.Sqlite.Frontend.Embedding.SqlTerm
import Belay.Sqlite.Schema.Dispatch.SqlEditorInfo

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term Meta

/-- The term of the database: {name}`Database.mk` of the literal of the model database and of
the proof {lit}`of_decide_eq_true (Eq.refl true)`, so the kernel decides {name}`Database.Valid`
for the literal when it checks the term. -/
def databaseExpr (raw : Database.Raw) : Expr :=
  let literal := toExpr raw
  let pinned := Lean.mkConst ``Profile.pinned
  let valid := mkApp2 (Lean.mkConst ``Belay.Sqlite.Model.Database.Valid) pinned literal
  let decision := mkApp2 (Lean.mkConst ``Belay.Sqlite.Model.Database.decidableValid) pinned literal
  let decided := mkApp2 (Lean.mkConst ``Eq.refl [Level.one]) (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true)
  mkApp2 (Lean.mkConst ``Database.mk) literal (mkApp3 (Lean.mkConst ``of_decide_eq_true) valid decision decided)

/-- The message of a database that the text builds and that is not valid, with the atom of
{name}`Database.Valid` that fails ({name}`Belay.Sqlite.Model.ValidityAtom.name`). -/
def invalidDatabaseMessage (atom : Belay.Sqlite.Model.ValidityAtom) : String :=
  s!"the database that db! builds is not valid: {atom.name} does not hold. The model's " ++
    "statements keep a database valid, so this is a defect of the model; report the SQL text " ++
    "to the maintainers of the model"

/-- The term of the database that a text builds with no error: {name}`databaseExpr` for a
valid database, or the error {name}`invalidDatabaseMessage` with the first atom that fails
({name}`Belay.Sqlite.Model.Database.failingAtom?`). The kernel decides
{name}`Belay.Sqlite.Model.Database.Valid` again when it checks the term. -/
def databaseTerm (raw : Database.Raw) : Except String Expr :=
  match raw.failingAtom? Profile.pinned with
  | some atom => .error (invalidDatabaseMessage atom)
  | none => .ok (databaseExpr raw)

end Belay.Sqlite
