import Belay.Sqlite.Frontend.Embedding.SqlTableOrigins
import Belay.Sqlite.Schema.Rows.Database

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term

/-- The model database literal in a database term: the first argument of {name}`Database.mk`,
which a {lit}`db!` term holds, without a wrapper of replay metadata. -/
def databaseLiteral? (database : Expr) : Option Expr :=
  match database.consumeMData.getAppFnArgs with
  | (``Database.mk, #[literal, _]) => some literal
  | _ => none

/-- The origins of the database that a term names: the term is a constant, or constants that
stand for each other ({lit}`def b := a`), whose value holds the literal that a {lit}`db!` recorded. A
term of any other form, and a declaration with a changed value, has none. The fuel bounds the
chain of constants; use {name}`aliasChainLimit`. -/
def originsOf (environment : Environment) : Nat → Expr → Option DatabaseOrigins
  | 0, _ => none
  | fuel + 1, database =>
    match database.consumeMData with
    | .const name _ =>
      let value? := (environment.find? name).bind (·.value?)
      match (tableOriginsExtension.getState environment).find? name with
      | some entry =>
        if (value?.bind databaseLiteral?).any (·.hash == entry.literalHash) then some entry else none
      | none => value?.bind (originsOf environment fuel)
    | _ => none

end Belay.Sqlite
