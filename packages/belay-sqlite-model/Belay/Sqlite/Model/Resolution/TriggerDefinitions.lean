import Belay.Sqlite.Model.Resolution.Context
import Belay.Sqlite.Model.Resolution.Drops
import Belay.Sqlite.Model.Resolution.SyntaxParameters

set_option doc.verso true

/-! Name resolution of CREATE TRIGGER and DROP TRIGGER (ADR 0018, D5), with the prepare errors
in the order of SQLite's {lit}`sqlite3BeginTrigger` and {lit}`sqlite3DropTrigger`. The catalog
keeps a trigger as written; the writes that may run it resolve its statements. -/

namespace Belay.Sqlite.Model

/-- Resolve CREATE TRIGGER of the name on the table: a table that does not exist is
{lit}`no such table: main.%s`; a name that begins with {lit}`sqlite_` is
{lit}`object name reserved for internal use`; the name of a trigger of the catalog is
{lit}`trigger %T already exists`, and with {lit}`IF NOT EXISTS` a statement that does nothing;
a table whose name begins with {lit}`sqlite_`, SQLite's schema tables too, is
{lit}`cannot create trigger on system table`; a parameter in the condition or the body is
{lit}`trigger cannot use variables` ({name}`ExprError.triggerVariables`). Otherwise the trigger
joins the end of the catalog. A trigger on a view, after the checks of its name, is
{name}`PrepareError.viewTrigger`: a view takes only INSTEAD OF triggers, which the model does not hold. -/
def resolveCreateTrigger (catalog : Catalog) (name : Identifier) (ifNotExists : Bool) (trigger : CatalogTrigger) :
    StatementResolution :=
  match catalog.findTable trigger.table, schemaTableName? trigger.table with
  | none, none =>
    if (catalog.findView trigger.table).isSome then
      if reservedName name then prepareError catalog (.expression (.reservedName name))
      else if (catalog.findTrigger name).isSome then
        if ifNotExists then .ok (.drop [], catalog.drop []) else prepareError catalog (.triggerExists name)
      else prepareError catalog (.viewTrigger (trigger.time == .before) trigger.table)
    else prepareError catalog (.noSuchReferencedTable trigger.table)
  | some _, _ | none, some _ =>
    if reservedName name then prepareError catalog (.expression (.reservedName name))
    else if (catalog.findTrigger name).isSome then
      if ifNotExists then .ok (.drop [], catalog.drop []) else prepareError catalog (.triggerExists name)
    else if reservedName trigger.table then prepareError catalog (.expression .triggerOnSystemTable)
    else if Syntax.Expr.optionParameter trigger.condition || trigger.body.any Syntax.BodyStatement.hasParameter then
      prepareError catalog (.expression .triggerVariables)
    else .ok (.createTrigger catalog.length name trigger, catalog.createTrigger name trigger)

/-- Resolve DROP TRIGGER: the trigger with the name leaves the catalog ({name}`Catalog.drop`); a
name that no trigger has is {lit}`no such trigger: %S`, and with {lit}`IF EXISTS` a DROP of
nothing. -/
def resolveDropTrigger (catalog : Catalog) (name : Identifier) (ifExists : Bool) : StatementResolution :=
  match catalog.findTrigger name with
  | some (position, _) => .ok (.drop [position], catalog.drop [position])
  | none => if ifExists then .ok (.drop [], catalog.drop []) else prepareError catalog (.noSuchTrigger name)

end Belay.Sqlite.Model
