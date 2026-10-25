import Belay.Sqlite.Model.NormalizedFieldExpandedTable
import Belay.Sqlite.Model.NormalizedFieldLookups
import Belay.Sqlite.Model.SimpleTableRowsOutput

set_option doc.verso true

/-! The outputs of the two lookups of a lowercase-field expansion in the actual run: the
original lookup on the original connection and the stored or original lookup on a connection
whose database is the expansion's. The outputs include every unmodeled stop of the step. -/

namespace Belay.Sqlite.Model.NormalizedField
open Resolved

/-- The query results do not depend on the output names. Proof sketch: the result function reads
no name. -/
theorem results_names (sources : List QuerySource) (filter : Option Expr) (columns : List Resolved.Output)
    (names other : List String) (context : EvalContext) (rows : List (List Value)) :
    (Query.simple sources filter columns names).results context rows =
      (Query.simple sources filter columns other).results context rows := rfl

/-- The output of the step of a statement that resolves to a calm simple table query is the rows
of the query's result over the table's scan, in normal form, for every clock and index. Proof
sketch: {name}`runScriptStep_output` and {name}`resolvedStepOutput_simpleTable_rows`. -/
theorem step_output_of_simple_query (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (statement : Syntax.Statement) (parameters : List Value) (position : Nat)
    (table : Table) (condition : Resolved.Expr) (column : Nat) (names : List String)
    (resolved : resolveStatement context connection.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first position] (some condition) [.scalar (.column column)] names) [],
        connection.resolveState))
    (present : connection.state.database.table position = some table) (calm : condition.Calm) :
    (runScriptStep context clock index connection statement parameters).output =
      .rows (normalForm ((Query.simple [QuerySource.first position] (some condition) [.scalar (.column column)] ["id"]).results
        (EvalContext.bound parameters) (sourceRows table))) := by
  rw [runScriptStep_output, resolved]
  exact resolvedStepOutput_simpleTable_rows clock index position connection parameters table _ _ names present
    (simpleColumn_calm position column condition names calm)

/-- For every parameter value, the original lookup on the original connection and the stored
lookup on a connection with the expanded database give the same step output, at any clocks and
indexes. The surrounding catalog, table shape, rows and stored values are arbitrary within the
premises: the table is physical with wide aliased rows, in-range primary-key, source and id
positions, plain original columns and an absent stored name. The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch: both statements resolve
to simple table queries ({name}`resolve_original_lookup`, {name}`resolve_stored_lookup`); their
outputs are the normal forms of query results, and {name}`results_translate` equates the results
over the two scans related by {name}`sourceRows_expandedTable`. -/
theorem translate_step_outputs (context : ResolveContext) (clock : Option Clock) (before after : Nat)
    (connection expanded : Connection) (reference : Syntax.TableReference)
    (idName sourceName storedName : Identifier) (text : String) (number : Nat) (value : Value)
    (table : Table) (position source id : Nat) (first second : Identifier × CatalogTrigger)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : connection.state.database.catalog.findTable reference.table = some (position, table.shape))
    (present : connection.state.database.table position = some table)
    (aligned : position < connection.state.database.rows.length)
    (fresh : columnPosition table.shape.columns storedName = none)
    (idFound : columnPosition table.shape.columns idName = some id)
    (sourceFound : columnPosition table.shape.columns sourceName = some source)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (keysInside : ∀ key ∈ table.shape.primaryKey, key < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none)
    (reached : expanded.state.database =
      expandedDatabase connection.state.database position source table storedName first second) :
    (runScriptStep context clock before connection
        (originalLookup reference idName sourceName text number) [value]).output =
      (runScriptStep context clock after expanded (storedLookup reference idName storedName text number) [value]).output := by
  have inside := columnPosition_lt sourceFound
  have idInside := columnPosition_lt idFound
  obtain ⟨names, original⟩ := resolve_original_lookup context connection.resolveState reference position table.shape
    idName sourceName text number namedSource current arguments found idFound sourceFound
  have extendedFound : expanded.state.database.catalog.findTable reference.table =
      some (position, (expandedTable table storedName source).shape) := by
    rw [reached]; exact expandedDatabase_findTable storedName first second found
  have storedFound := columnPosition_new fresh table.shape.strict
  obtain ⟨storedNames, stored⟩ := resolve_stored_lookup context expanded.resolveState reference position
    (expandedTable table storedName source).shape idName storedName text number namedSource current arguments extendedFound
    (columnPosition_append idFound _) storedFound
    (by simp [expandedTable, textColumn]; cases table.shape.strict <;> rfl) (by simp [expandedTable, textColumn])
  have presentAfter : expanded.state.database.table position = some (expandedTable table storedName source) := by
    rw [reached]; exact expandedDatabase_table storedName first second present aligned
  rw [step_output_of_simple_query context clock before connection _ [value] position table _ id names original present
      (originalFilter_calm source number),
    step_output_of_simple_query context clock after expanded _ [value] position _ _ id storedNames stored presentAfter
      (storedFilter_calm _ number),
    sourceRows_expandedTable table storedName source wide aliased inside keysInside plain]
  have same := results_translate (EvalContext.bound [value]) (sourceRows table) [QuerySource.first position]
    [QuerySource.first position] table.shape.columns.length source id number (sourceRows_width wide) idInside
  simpa [expandedTable] using congrArg (fun rows => Output.rows (normalForm rows)) same.symm

/-- For every parameter value, the original lookup gives the same step output on the original
connection and on a connection with the expanded database, at any clocks and indexes. The
premises are those of {name}`translate_step_outputs` except that the stored name need not be absent
from the columns: preservation never reads the new field. The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch: as there, with
{name}`results_preserve` in place of {name}`results_translate`. -/
theorem preserve_step_outputs (context : ResolveContext) (clock : Option Clock) (before after : Nat)
    (connection expanded : Connection) (reference : Syntax.TableReference)
    (idName sourceName storedName : Identifier) (text : String) (number : Nat) (value : Value)
    (table : Table) (position source id : Nat) (first second : Identifier × CatalogTrigger)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : connection.state.database.catalog.findTable reference.table = some (position, table.shape))
    (present : connection.state.database.table position = some table)
    (aligned : position < connection.state.database.rows.length)
    (idFound : columnPosition table.shape.columns idName = some id)
    (sourceFound : columnPosition table.shape.columns sourceName = some source)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (keysInside : ∀ key ∈ table.shape.primaryKey, key < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none)
    (reached : expanded.state.database =
      expandedDatabase connection.state.database position source table storedName first second) :
    (runScriptStep context clock before connection
        (originalLookup reference idName sourceName text number) [value]).output =
      (runScriptStep context clock after expanded (originalLookup reference idName sourceName text number) [value]).output := by
  have inside := columnPosition_lt sourceFound
  have idInside := columnPosition_lt idFound
  obtain ⟨names, original⟩ := resolve_original_lookup context connection.resolveState reference position table.shape
    idName sourceName text number namedSource current arguments found idFound sourceFound
  have extendedFound : expanded.state.database.catalog.findTable reference.table =
      some (position, (expandedTable table storedName source).shape) := by
    rw [reached]; exact expandedDatabase_findTable storedName first second found
  obtain ⟨extendedNames, extended⟩ := resolve_original_lookup context expanded.resolveState reference position
    (expandedTable table storedName source).shape idName sourceName text number namedSource current arguments extendedFound
    (columnPosition_append idFound _) (columnPosition_append sourceFound _)
  have presentAfter : expanded.state.database.table position = some (expandedTable table storedName source) := by
    rw [reached]; exact expandedDatabase_table storedName first second present aligned
  rw [step_output_of_simple_query context clock before connection _ [value] position table _ id names original present
      (originalFilter_calm source number),
    step_output_of_simple_query context clock after expanded _ [value] position _ _ id extendedNames extended presentAfter
      (originalFilter_calm source number),
    sourceRows_expandedTable table storedName source wide aliased inside keysInside plain]
  have same := results_preserve (EvalContext.bound [value]) (sourceRows table) [QuerySource.first position]
    [QuerySource.first position] table.shape.columns.length source id number (sourceRows_width wide) inside idInside
  simpa [expandedTable] using congrArg (fun rows => Output.rows (normalForm rows)) same.symm

end Belay.Sqlite.Model.NormalizedField
