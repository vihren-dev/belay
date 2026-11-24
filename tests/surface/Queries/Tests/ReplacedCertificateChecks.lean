import ReplacedCertificateObligations

set_option doc.verso true

/-! Original KeptRead.preserves and single-statement observation contracts. -/

namespace Belay.Sqlite
open Model

/-- The former schema check supplies both scans by kernel-certified resolution. -/
theorem KeptRead.original_preserves {schema : Database} {migration : Script} {statement : Syntax.Statement} (values : List Value)
    {name : Identifier} {position destination : Nat} {shape finalShape : CatalogTable}
    {path : List Resolved.Statement} {final readState afterState : ResolveState} {read : Resolved.Statement}
    {certificate : ReadCertificate} {names : List String}
    (readOnly : (⟨[(statement, values)]⟩ : Script).isQuery = true)
    (checked : resolveFrom runContext 0 schema.raw.connection.resolveState (migration.statements.map Prod.fst) =
      .ok (path, final))
    (lookup : schema.raw.catalog.findTable name = some (position, shape))
    (resolved : resolveStatement runContext schema.raw.connection.resolveState statement = .ok (read, readState))
    (certified : ReadAnalysis.analyze shape.columns.length read = .certified certificate)
    (place : certificate.position = position)
    (frame : schema.raw.connection.resolveState.tablePosition path migration.statements.length position =
      some destination)
    (lookupAfter : final.catalog.findTable name = some (destination, finalShape))
    (resolvedAfter : resolveStatement runContext final statement =
      .ok ((certificate.moved destination).statement names, afterState)) :
    Migration.QueryPreserves (send migration) ⟨[(statement, values)]⟩ (·.HasCatalog schema) readOnly := by
  obtain ⟨valid, width, firstNames, first⟩ := ReadAnalysis.analyze_sound certified
  apply KeptRead.preserves values readOnly checked lookup valid width ?_ place frame lookupAfter ?_
  · intro connection same
    apply ReadCertificate.original_scan valid (names := firstNames) (state := readState)
    rw [same, resolved, first]
  · intro connection same
    apply ReadCertificate.original_scan (valid.moved destination) (names := names) (state := afterState)
    rw [same, resolvedAfter]

/-- The original singleton premise rules out all further executions. -/
theorem original_sendStatements_single_branch (statement : Syntax.Statement) (values : List Value)
    (clock : Option Clock) (index : Nat) (connection : Connection) (observation : Option (List Output) × List Output)
    (single : ∀ resolved after, resolveStatement runContext connection.resolveState statement = .ok (resolved, after) →
      resolved.fromQuery = false) :
    (∃ result, (sendStatements [(statement, values)]).Branch clock index connection result ∧
        result.observation = observation) ↔
      ∃ selected, OutputChoice (runScriptStep runContext clock index connection statement values).output selected ∧
        observation = singleObservation (runScriptStep runContext clock index connection statement values).output
          selected :=
  sendStatements_single_branch statement values clock index connection observation
    (fun _ _ _ step => runScriptStep_others_of_single step single)

/-- The original singleton premise rules out all further executions. -/
theorem original_sendStatements_single_observations (first second : Syntax.Statement) (firstValues secondValues : List Value)
    (firstClock secondClock : Option Clock) (firstIndex secondIndex : Nat) (firstConnection secondConnection : Connection)
    (firstSingle : ∀ resolved after, resolveStatement runContext firstConnection.resolveState first =
      .ok (resolved, after) → resolved.fromQuery = false)
    (secondSingle : ∀ resolved after, resolveStatement runContext secondConnection.resolveState second =
      .ok (resolved, after) → resolved.fromQuery = false)
    (same : (runScriptStep runContext firstClock firstIndex firstConnection first firstValues).output =
      (runScriptStep runContext secondClock secondIndex secondConnection second secondValues).output) :
    ((sendStatements [(first, firstValues)]).runFrom firstClock firstIndex firstConnection).observation =
      ((sendStatements [(second, secondValues)]).runFrom secondClock secondIndex secondConnection).observation ∧
    ∀ observation,
      (∃ result, (sendStatements [(first, firstValues)]).Branch firstClock firstIndex firstConnection result ∧
        result.observation = observation) ↔
      ∃ result, (sendStatements [(second, secondValues)]).Branch secondClock secondIndex secondConnection result ∧
        result.observation = observation :=
  sendStatements_single_observations first second firstValues secondValues firstClock secondClock firstIndex secondIndex
    firstConnection secondConnection (fun _ _ _ step => runScriptStep_others_of_single step firstSingle)
    (fun _ _ _ step => runScriptStep_others_of_single step secondSingle) same

/-- The original checker contract uses the actual read as its own reference. -/
theorem KeptRead.original_preserves_of_check (name : Identifier) {schema : Database} {migration query : Script}
    (checked : KeptRead.preservesCheck name schema migration query = true) (readOnly : query.isQuery = true := by check_query) :
    Migration.QueryPreserves (send migration) query (·.HasCatalog schema) readOnly :=
  KeptRead.preserves_of_check name query checked readOnly

#print axioms KeptRead.original_preserves_of_check
#print axioms KeptRead.original_preserves
#print axioms original_sendStatements_single_branch
#print axioms original_sendStatements_single_observations

end Belay.Sqlite

namespace Belay.Sqlite.Model
open Resolved

/-- For every two connections, statement, parameters and table name that satisfy the premises below, the
steps of the statement on the two connections give the same output, at any clocks and statement indexes.
The premises are those of {name}`runScriptStep_simpleTable_output_agree` for one statement with one filter
on both connections, which reads only columns below the width:
* The name finds a table in each connection ({name}`Database.tableNamed`), at positions that can differ,
  for example after the drop of an earlier table.
* The statement resolves on each connection to a simple query of the table at the position that the name
  finds there, with the same filter and result columns and possibly different result names.
* Both queries are calm, the scan of the second table is the scan of the first with cells appended to each
  row, and every scanned row of the first table has at least the width.

In plain words, appended cells that the query does not read cannot change its output. For example, a query
that selects the column {lit}`id` of rows filtered by {lit}`name = ?1` gives the same output after any column
is appended to the table, provided that the query still resolves to the same columns. Proof sketch:
{name}`runScriptStep_simpleTable_output_agree`, whose agreement premise holds because the filter reads below
the width ({name}`Query.filterKeeps_append`); the tables come from the lookups by name
({name}`Database.tableNamed_some`). -/
theorem runScriptStep_simpleTable_output_append (context : ResolveContext) (clock : Option Clock)
    (before after : Nat) (connection expanded : Connection) (statement : Syntax.Statement)
    (parameters : List Value) (name : Identifier) (beforePosition afterPosition : Nat) (table extended : Table)
    (filter : Option Expr) (columns : List Resolved.Output) (names other : List String) (width : Nat)
    (extra : List Value → List Value) {beforeState afterState : ResolveState}
    (foundBefore : connection.state.database.tableNamed name = some (beforePosition, table))
    (foundAfter : expanded.state.database.tableNamed name = some (afterPosition, extended))
    (resolvedBefore : resolveStatement context connection.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first beforePosition] filter columns names) [], beforeState))
    (resolvedAfter : resolveStatement context expanded.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first afterPosition] filter columns other) [], afterState))
    (calmBefore : (Resolved.Statement.query
      (Query.simple [QuerySource.first beforePosition] filter columns names) []).Calm)
    (calmAfter : (Resolved.Statement.query
      (Query.simple [QuerySource.first afterPosition] filter columns other) []).Calm)
    (scans : sourceRows extended = (sourceRows table).map fun row => row ++ extra row)
    (wide : ∀ row ∈ sourceRows table, width ≤ row.length)
    (filterBelow : ∀ condition ∈ filter, condition.readsBelow width = true)
    (columnsBelow : ∀ column ∈ columns, column.readsBelow width = true) :
    (runScriptStep context clock before connection statement parameters).output =
      (runScriptStep context clock after expanded statement parameters).output :=
  runScriptStep_simpleTable_output_agree context clock before after connection expanded statement statement
    parameters beforePosition afterPosition table extended filter filter columns names other width extra
    resolvedBefore resolvedAfter (Database.tableNamed_some foundBefore).2 (Database.tableNamed_some foundAfter).2
    calmBefore calmAfter scans wide columnsBelow fun row member =>
      Query.filterKeeps_append (EvalContext.bound parameters) (EvalContext.plain_rowFree 0) row (extra row) width
        (wide row member) filter filterBelow


#print axioms runScriptStep_simpleTable_output_append

end Belay.Sqlite.Model
