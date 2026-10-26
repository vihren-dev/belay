import Belay.Sqlite.Model.ScriptRunApplied
import Belay.Sqlite.Model.ScriptRunDerived

set_option doc.verso true

/-! The run theorems of the atoms "catalog supported", "rows shaped", "rowids distinct" and "rowids in range"
for {lit}`runScriptAllFrom`, the complete executions of a script (ADR 0022, D3, slice 4). A statement that
{lit}`runScriptAllFrom` runs has passed the support check, and the resolver gives the condition of "catalog
supported" (the catalog after the statement is valid), so the theorems have no hypothesis on the statements
of the script. -/

namespace Belay.Sqlite.Model

/-- The run theorem of "catalog supported" for {name}`runScriptAllFrom`, the complete executions of a script. For every
limits, context, clock, index, connection and statements with their values: if the context is in execution
mode and has the given limits ({lit}`context.profile.limits = limits`), and the state of the connection
satisfies {name}`SqlState.Holds` for {name}`Database.CatalogSupported` (its database, and its snapshot when
a transaction is open), the state of the connection of every complete execution of the script ({lit}`run.connection.state`) satisfies it. It
has no hypothesis on the statements of the script: the resolver gives the condition of each statement
({name}`resolveStatement_appliedValid`). Proof sketch: {name}`runScriptAllFrom_holds_derived` for
{name}`catalogSupported_statementKeeps`. -/
theorem runScriptAllFrom_catalogSupported {limits : Limits} (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = limits)
    (holds : connection.state.Holds (Database.CatalogSupported limits)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds (Database.CatalogSupported limits) :=
  runScriptAllFrom_holds_derived (catalogSupported_statementKeeps limits) context clock
    (fun _ _ _ _ keep ok => resolveStatement_appliedValid context execution same keep ok) index script holds

/-- The run theorem of "rows shaped" for {name}`runScriptAllFrom`, the complete executions of a script. For every context,
clock, index, connection and statements with their values: if the state of the connection satisfies
{name}`SqlState.Holds` for {name}`Database.RowsShaped` (its database, and its snapshot when a transaction is
open), the state of the connection of every complete execution of the script ({lit}`run.connection.state`) satisfies it. It has no hypothesis
on the statements of the script, and the statement theorem needs no condition. Proof sketch:
{name}`runScriptAllFrom_holds_derived` for {name}`rowsShaped_statementKeeps`. -/
theorem runScriptAllFrom_rowsShaped (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds Database.RowsShaped) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds Database.RowsShaped :=
  runScriptAllFrom_holds_derived (rowsShaped_statementKeeps) context clock (fun _ _ _ _ _ _ => trivial) index script holds

/-- The run theorem of "rowids distinct" for {name}`runScriptAllFrom`, the complete executions of a script. For every
context, clock, index, connection and statements with their values: if the state of the connection satisfies
{name}`SqlState.Holds` for {name}`Database.RowidsDistinct` (its database, and its snapshot when a
transaction is open), the state of the connection of every complete execution of the script ({lit}`run.connection.state`) satisfies it. It has
no hypothesis on the statements of the script, and the statement theorem needs no condition. Proof sketch:
{name}`runScriptAllFrom_holds_derived` for {name}`rowidsDistinct_statementKeeps`. -/
theorem runScriptAllFrom_rowidsDistinct (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds Database.RowidsDistinct) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds Database.RowidsDistinct :=
  runScriptAllFrom_holds_derived (rowidsDistinct_statementKeeps) context clock (fun _ _ _ _ _ _ => trivial) index script holds

/-- The run theorem of "rowids in range" for {name}`runScriptAllFrom`, the complete executions of a script. For every
context, clock, index, connection and statements with their values: if the state of the connection satisfies
{name}`SqlState.Holds` for {name}`Database.RowidsInRange` (its database, and its snapshot when a transaction
is open), the state of the connection of every complete execution of the script ({lit}`run.connection.state`) satisfies it. It has no
hypothesis on the statements of the script, and the statement theorem needs no condition. Proof sketch:
{name}`runScriptAllFrom_holds_derived` for {name}`rowidsInRange_statementKeeps`. -/
theorem runScriptAllFrom_rowidsInRange (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds Database.RowidsInRange) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds Database.RowidsInRange :=
  runScriptAllFrom_holds_derived (rowidsInRange_statementKeeps) context clock (fun _ _ _ _ _ _ => trivial) index script holds

end Belay.Sqlite.Model
