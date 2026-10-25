import Belay.Sqlite.MigrationPatternFresh
import Belay.Sqlite.MigrationPatternAfter
import Belay.Sqlite.SendStatementsBranches
import Belay.Sqlite.SingleStatementObservations
import Belay.Sqlite.ScriptSuccess

set_option doc.verso true

/-! The lowercase-field expansion of a table as a migration pattern (ADR 0017, S6): add a plain TEXT
field, fill it with the lowercase of an existing column, and register two triggers that keep it
filled. A lookup of the original column through {lit}`lower` translates into a lookup of the new
field on every database that has the table, and a lookup that does not mention the field is
preserved. -/

namespace Belay.Sqlite.NormalizedFieldExpansion
open Belay.Sqlite.Model Belay.Sqlite.Model.NormalizedField

/-- The table named in {lit}`FROM` with an optional alias and no function arguments or derived source. -/
def tableReference (tableName : Identifier) (alias : Option Identifier := none) : Syntax.TableReference :=
  { table := tableName, alias }

/-- The four-statement expansion script for the table {lit}`tableName`: ADD the plain TEXT field
{lit}`name`, set it to the lowercase of the column {lit}`sourceName` for every row, then create the two
triggers. The trigger names and definitions, and the values bound to each statement, are arbitrary. -/
def expansion (tableName name sourceName : Identifier) (first second : Identifier × CatalogTrigger)
    (firstValues secondValues thirdValues fourthValues : List Value) : Script :=
  ⟨Model.NormalizedField.expansionScript tableName name sourceName first second firstValues secondValues
    thirdValues fourthValues⟩

/-- The lookup {lit}`SELECT id FROM t WHERE lower(source) = lower(?1)` as a query script with the value
bound to its parameter. -/
def originalLookupScript (tableName : Identifier) (alias : Option Identifier) (idName sourceName : Identifier)
    (text : String) (number : Nat) (value : Value) : Script :=
  ⟨[(originalLookup (tableReference tableName alias) idName sourceName text number, [value])]⟩

/-- The lookup {lit}`SELECT id FROM t WHERE stored = lower(?1)` over the new field as a query script
with the value bound to its parameter. -/
def storedLookupScript (tableName : Identifier) (alias : Option Identifier) (idName storedName : Identifier)
    (text : String) (number : Nat) (value : Value) : Script :=
  ⟨[(storedLookup (tableReference tableName alias) idName storedName text number, [value])]⟩

/-- A database has a table that the expansion can extend: the table is physical, found by name at a
catalog position, has an id column and a source column, and no column of the new name. Its
primary-key positions lie inside its columns, its columns are plain (not generated), and the catalog with
the new field added selects no trigger for an UPDATE of that field. Other tables, indexes, triggers
and rows are unrestricted. -/
structure Site (database : Database.Raw) (tableName idName sourceName storedName : Identifier) where
  /-- The catalog position of the table. -/
  position : Nat
  /-- The table with its rows. -/
  table : Table
  /-- The position of the id column. -/
  id : Nat
  /-- The position of the source column. -/
  source : Nat
  /-- The catalog finds the table by name at the position. -/
  found : database.catalog.findTable tableName = some (position, table.shape)
  /-- The database has this table at the position. -/
  present : database.table position = some table
  /-- No column has the new name. -/
  fresh : columnPosition table.shape.columns storedName = none
  /-- The id column is at its position. -/
  idFound : columnPosition table.shape.columns idName = some id
  /-- The source column is at its position. -/
  sourceFound : columnPosition table.shape.columns sourceName = some source
  /-- Every primary-key position is a column of the table. -/
  keysInside : ∀ key ∈ table.shape.primaryKey, key < table.shape.columns.length
  /-- No original column is generated. -/
  plain : ∀ old ∈ table.shape.columns, old.generated = none
  /-- With the new column added, the catalog selects no trigger for an UPDATE of that column. -/
  noneFiring : (database.catalog.addColumn position (textColumn storedName table.shape.strict)).triggersFiring
    { table := position, event := .update (some [table.shape.columns.length]) } = []

/-- For a database with a {name}`Site`, an expansion that succeeds, and two statements whose steps have
equal outputs on the original connection and on any connection with the expanded database, the first
statement translates into the second after the expansion. The equal-outputs premise must hold for every
clock index after the expansion and gets the table's row facts. The result covers the actual run and
every raw or concrete branch. Proof sketch: success of the sent script gives the model run;
{name}`expansion_state` gives its reached connection; every branch reaches the same connection
({name}`sendStatements_branch_shape`); and equal step outputs give equal observations
({name}`sendStatements_single_observations`, {name}`Migration.translatesAt_of_observations`). -/
theorem translatesAt_of_outputs (tableName idName sourceName storedName : Identifier)
    (first second : Identifier × CatalogTrigger) (firstValues secondValues thirdValues fourthValues : List Value)
    (db : Database) (env : Env) (site : Site db.raw tableName idName sourceName storedName)
    (original replacement : Syntax.Statement) (value : Value)
    (outputs : site.table.RowsWide → site.table.RowsAliased → site.position < db.raw.rows.length →
      ∀ (expanded : Connection) (after : Nat),
        expanded.state.database =
          expandedDatabase db.raw site.position site.source site.table storedName first second →
        (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) original [value]).output =
          (runScriptStep runContext env.clock after expanded replacement [value]).output) :
    Migration.TranslatesAt
      (send (expansion tableName storedName sourceName first second firstValues secondValues thirdValues
        fourthValues))
      (fun _ => True) (send ⟨[(original, [value])]⟩) (send ⟨[(replacement, [value])]⟩)
      (ExecutionContext.initial db env) := by
  rintro ⟨_, success⟩
  have wide : site.table.RowsWide := db.valid.admitted.rowsWide site.position site.table site.present
  have aliased : site.table.RowsAliased := db.valid.admitted.rowsAliased site.position site.table site.present
  have aligned : site.position < db.raw.rows.length := by
    rw [db.valid.admitted.rowsShaped.1]; exact Database.table_lt site.present
  have reachedSuccess : (sendStatements (expansion tableName storedName sourceName first second firstValues
      secondValues thirdValues fourthValues).statements).SucceedsFrom env.clock 0 (db.raw.connection env.counters) :=
    success
  have ok : List.allOk (runScriptFrom runContext env.clock 0 (db.raw.connection env.counters)
      (Model.NormalizedField.expansionScript tableName storedName sourceName first second firstValues
        secondValues thirdValues fourthValues)).outputs = true :=
    (Sql.succeedsFrom_sendStatements _ _ _ _).mp reachedSuccess
  obtain ⟨run, hrun⟩ : ∃ run, run = runScriptFrom runContext env.clock 0 (db.raw.connection env.counters)
      (Model.NormalizedField.expansionScript tableName storedName sourceName first second firstValues
        secondValues thirdValues fourthValues) := ⟨_, rfl⟩
  obtain ⟨counters, hconn, hlength⟩ := expansion_state (context := runContext) (clock := env.clock) (index := 0)
    (connection := db.raw.connection env.counters) (tableName := tableName) (name := storedName)
    (sourceName := sourceName) site.table first second firstValues secondValues thirdValues fourthValues
    site.found site.present site.fresh site.sourceFound wide aliased site.plain rfl rfl site.noneFiring ok
  rw [← hrun] at hconn
  have uniform : ∀ branch, (send (expansion tableName storedName sourceName first second firstValues secondValues
      thirdValues fourthValues)).Branch env.clock 0 (db.raw.connection env.counters) branch →
      branch.connection = run.connection ∧ branch.outputs.length = run.outputs.length := by
    intro branch reached
    rw [hrun]
    exact sendStatements_branch_shape _ _ _ _ branch reached
  have database : run.connection.state.database =
      expandedDatabase db.raw site.position site.source site.table storedName first second := by
    rw [hconn]
    rfl
  obtain ⟨actual, branches⟩ := sendStatements_single_observations original replacement [value] [value] env.clock
    env.clock 0 (0 + run.outputs.length) (db.raw.connection env.counters) run.connection
    (outputs wide aliased aligned run.connection (0 + run.outputs.length) database)
  exact Migration.translatesAt_of_observations _ _ _ (ExecutionContext.initial db env) run.outputs.length
    run.connection success uniform actual branches

/-- Original and stored lookups of a lowercase-field expansion: on every valid database that has a
{name}`Site`, for every complete environment and every value bound to the lookup parameter, if the
expansion succeeds on every raw and concrete branch from the initial context, then the original lookup
and the stored lookup have equal actual values and traces and the same set of branch observations. The
expansion's ADD, UPDATE and trigger-name failures are excluded by that success; no other table, index,
trigger or row is restricted. Plain words: for every such database, environment and value, if the
expansion succeeds, the lookup {lit}`WHERE lower(source) = lower(?1)` before it gives the same ids as
the lookup {lit}`WHERE stored = lower(?1)` after it. Proof sketch:
{name}`translatesAt_of_outputs` with {name}`translate_step_outputs`. -/
theorem queryTranslates (tableName : Identifier) (alias : Option Identifier)
    (idName sourceName storedName : Identifier) (text : String) (number : Nat) (value : Value)
    (first second : Identifier × CatalogTrigger) (firstValues secondValues thirdValues fourthValues : List Value) :
    Migration.QueryTranslates
      (send (expansion tableName storedName sourceName first second firstValues secondValues thirdValues
        fourthValues))
      (originalLookupScript tableName alias idName sourceName text number value)
      (storedLookupScript tableName alias idName storedName text number value)
      (fun db => Nonempty (Site db.raw tableName idName sourceName storedName)) := by
  intro db ⟨site⟩ env _
  exact translatesAt_of_outputs tableName idName sourceName storedName first second firstValues secondValues
    thirdValues fourthValues db env site _ _ value fun wide aliased aligned expanded after reached =>
    translate_step_outputs runContext env.clock 0 after (db.raw.connection env.counters) expanded
      (tableReference tableName alias) idName sourceName storedName text number value site.table site.position
      site.source site.id first second rfl rfl site.found site.present aligned site.fresh site.idFound
      site.sourceFound wide aliased site.keysInside site.plain reached

/-- Preserved original lookup of a lowercase-field expansion: on every valid database that has a
{name}`Site`, for every complete environment and every value, if the expansion succeeds, the lookup
{lit}`WHERE lower(source) = lower(?1)` gives the same actual value and trace and the same set of branch
observations after the expansion as before it. Proof sketch: {name}`translatesAt_of_outputs` with
{name}`preserve_step_outputs`. -/
theorem queryPreserves (tableName : Identifier) (alias : Option Identifier)
    (idName sourceName storedName : Identifier) (text : String) (number : Nat) (value : Value)
    (first second : Identifier × CatalogTrigger) (firstValues secondValues thirdValues fourthValues : List Value) :
    Migration.QueryPreserves
      (send (expansion tableName storedName sourceName first second firstValues secondValues thirdValues
        fourthValues))
      (originalLookupScript tableName alias idName sourceName text number value)
      (fun db => Nonempty (Site db.raw tableName idName sourceName storedName)) := by
  intro db ⟨site⟩ env _
  exact translatesAt_of_outputs tableName idName sourceName storedName first second firstValues secondValues
    thirdValues fourthValues db env site _ _ value fun wide aliased aligned expanded after reached =>
    preserve_step_outputs runContext env.clock 0 after (db.raw.connection env.counters) expanded
      (tableReference tableName alias) idName sourceName storedName text number value site.table site.position
      site.source site.id first second rfl rfl site.found site.present aligned site.idFound
      site.sourceFound wide aliased site.keysInside site.plain reached

end Belay.Sqlite.NormalizedFieldExpansion
