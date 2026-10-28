import Belay.Sqlite.Model

/-! Temporary migration witnesses for the 84 endpoint formulas at 3e2212ed6983.
Retain this single set through the execution-condition task's final Nix acceptance. -/

open Belay.Sqlite.Model

-- Former endpoint: runSqlFrom_notNull
example (position : Nat) (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds Database.NotNull) (conditions : PreservationMigration.RawConditions (fun statement database => statement.NotNullCondition database) position script state) :
    (runSqlFrom position script state).Holds Database.NotNull :=
  PreservationMigration.raw notNull_statementKeeps position script holds conditions

-- Former endpoint: runSql_notNull
example (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : Database.NotNull database) (conditions : PreservationMigration.RawConditions (fun statement database => statement.NotNullCondition database) 0 script { database }) :
    (runSql script database).Holds Database.NotNull :=
  PreservationMigration.raw_zero notNull_statementKeeps script holds conditions

-- Former endpoint: runSqlFrom_typesFit
example (position : Nat) (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds Database.TypesFit) (conditions : PreservationMigration.RawConditions (fun statement database => statement.TypesFitCondition database) position script state) :
    (runSqlFrom position script state).Holds Database.TypesFit :=
  PreservationMigration.raw typesFit_statementKeeps position script holds conditions

-- Former endpoint: runSql_typesFit
example (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : Database.TypesFit database) (conditions : PreservationMigration.RawConditions (fun statement database => statement.TypesFitCondition database) 0 script { database }) :
    (runSql script database).Holds Database.TypesFit :=
  PreservationMigration.raw_zero typesFit_statementKeeps script holds conditions

-- Former endpoint: runSqlFrom_checksHold
example (position : Nat) (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds Database.ChecksHold) (conditions : PreservationMigration.RawConditions (fun statement database => statement.ChecksHoldCondition database) position script state) :
    (runSqlFrom position script state).Holds Database.ChecksHold :=
  PreservationMigration.raw checksHold_statementKeeps position script holds conditions

-- Former endpoint: runSql_checksHold
example (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : Database.ChecksHold database) (conditions : PreservationMigration.RawConditions (fun statement database => statement.ChecksHoldCondition database) 0 script { database }) :
    (runSql script database).Holds Database.ChecksHold :=
  PreservationMigration.raw_zero checksHold_statementKeeps script holds conditions

-- Former endpoint: runSqlFrom_constraintAtoms
example (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds Database.ConstraintAtoms)
    (conditions : PreservationMigration.RawConditions (fun statement database => statement.AtomsCondition database) position script state) :
    (runSqlFrom position script state).Holds Database.ConstraintAtoms :=
  PreservationMigration.raw constraintAtoms_statementKeeps position script holds conditions

-- Former endpoint: runSql_constraintAtoms
example (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : database.ConstraintAtoms) (conditions : PreservationMigration.RawConditions (fun statement database => statement.AtomsCondition database) 0 script { database }) :
    (runSql script database).Holds Database.ConstraintAtoms :=
  PreservationMigration.raw_zero constraintAtoms_statementKeeps script holds conditions

-- Former endpoint: runSqlFrom_keysUnique
example (position : Nat) (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (unique : state.Holds Database.KeysUnique) (conditions : PreservationMigration.RawConditions (fun statement database => statement.RunCondition database) position script state) :
    (runSqlFrom position script state).Holds Database.KeysUnique :=
  PreservationMigration.raw keysUnique_statementKeeps position script unique conditions

-- Former endpoint: runSql_keysUnique
example (script : List (Resolved.Statement × List Value)) {database : Database}
    (unique : database.KeysUnique) (conditions : PreservationMigration.RawConditions (fun statement database => statement.RunCondition database) 0 script { database }) :
    (runSql script database).Holds Database.KeysUnique :=
  PreservationMigration.raw_zero keysUnique_statementKeeps script unique conditions

-- Former endpoint: runSqlFrom_catalogSupported
example (limits : Limits) (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds (Database.CatalogSupported limits))
    (supported : supportedSqlFrom position script state = true)
    (conditions : PreservationMigration.RawConditions (Resolved.Statement.AppliedValid limits) position script state) :
    (runSqlFrom position script state).Holds (Database.CatalogSupported limits) :=
  PreservationMigration.raw_ready (PreservationMigration.under_ready (catalogSupported_statementKeeps limits) (fun _ _ _ _ _ met _ => met)) position script holds supported conditions

-- Former endpoint: runSql_catalogSupported
example (limits : Limits) (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : Database.CatalogSupported limits database) (supported : supportedSqlFrom 0 script { database } = true)
    (conditions : PreservationMigration.RawConditions (Resolved.Statement.AppliedValid limits) 0 script { database }) :
    (runSql script database).Holds (Database.CatalogSupported limits) :=
  PreservationMigration.raw_ready_zero (PreservationMigration.under_ready (catalogSupported_statementKeeps limits) (fun _ _ _ _ _ met _ => met)) script holds supported conditions

-- Former endpoint: runSqlFrom_rowsShaped
example (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds (Database.RowsShaped))
    (supported : supportedSqlFrom position script state = true) :
    (runSqlFrom position script state).Holds (Database.RowsShaped) :=
  PreservationMigration.raw_ready (PreservationMigration.under_ready (rowsShaped_statementKeeps) (fun _ _ _ _ _ met _ => met)) position script holds supported (PreservationMigration.raw_always _ _ _)

-- Former endpoint: runSql_rowsShaped
example (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : Database.RowsShaped database) (supported : supportedSqlFrom 0 script { database } = true) :
    (runSql script database).Holds (Database.RowsShaped) :=
  PreservationMigration.raw_ready_zero (PreservationMigration.under_ready (rowsShaped_statementKeeps) (fun _ _ _ _ _ met _ => met)) script holds supported (PreservationMigration.raw_always _ _ _)

-- Former endpoint: runSqlFrom_rowidsDistinct
example (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds (Database.RowidsDistinct))
    (supported : supportedSqlFrom position script state = true) :
    (runSqlFrom position script state).Holds (Database.RowidsDistinct) :=
  PreservationMigration.raw_ready (PreservationMigration.under_ready (rowidsDistinct_statementKeeps) (fun _ _ _ _ _ met _ => met)) position script holds supported (PreservationMigration.raw_always _ _ _)

-- Former endpoint: runSql_rowidsDistinct
example (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : Database.RowidsDistinct database) (supported : supportedSqlFrom 0 script { database } = true) :
    (runSql script database).Holds (Database.RowidsDistinct) :=
  PreservationMigration.raw_ready_zero (PreservationMigration.under_ready (rowidsDistinct_statementKeeps) (fun _ _ _ _ _ met _ => met)) script holds supported (PreservationMigration.raw_always _ _ _)

-- Former endpoint: runSqlFrom_rowidsInRange
example (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds (Database.RowidsInRange))
    (supported : supportedSqlFrom position script state = true) :
    (runSqlFrom position script state).Holds (Database.RowidsInRange) :=
  PreservationMigration.raw_ready (PreservationMigration.under_ready (old := fun _ _ => True) (rowidsInRange_statementKeeps) (fun _ _ _ _ _ _ ready => ready)) position script holds supported (PreservationMigration.raw_always _ _ _)

-- Former endpoint: runSql_rowidsInRange
example (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : Database.RowidsInRange database) (supported : supportedSqlFrom 0 script { database } = true) :
    (runSql script database).Holds (Database.RowidsInRange) :=
  PreservationMigration.raw_ready_zero (PreservationMigration.under_ready (old := fun _ _ => True) (rowidsInRange_statementKeeps) (fun _ _ _ _ _ _ ready => ready)) script holds supported (PreservationMigration.raw_always _ _ _)

-- Former endpoint: runSqlFrom_rowsWide
example (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds (Database.RowsWide))
    (supported : supportedSqlFrom position script state = true) :
    (runSqlFrom position script state).Holds (Database.RowsWide) :=
  PreservationMigration.raw_ready (PreservationMigration.under_ready (old := fun _ _ => True) (rowsWide_statementKeeps) (fun _ _ _ _ _ _ ready => ready)) position script holds supported (PreservationMigration.raw_always _ _ _)

-- Former endpoint: runSql_rowsWide
example (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : Database.RowsWide database) (supported : supportedSqlFrom 0 script { database } = true) :
    (runSql script database).Holds (Database.RowsWide) :=
  PreservationMigration.raw_ready_zero (PreservationMigration.under_ready (old := fun _ _ => True) (rowsWide_statementKeeps) (fun _ _ _ _ _ _ ready => ready)) script holds supported (PreservationMigration.raw_always _ _ _)

-- Former endpoint: runSqlFrom_rowsStored
example (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds (Database.RowsStoredWide))
    (supported : supportedSqlFrom position script state = true) :
    (runSqlFrom position script state).Holds (Database.RowsStoredWide) :=
  PreservationMigration.raw_ready (PreservationMigration.under_ready (old := fun _ _ => True) (rowsStored_statementKeeps) (fun _ _ _ _ _ _ ready => ready)) position script holds supported (PreservationMigration.raw_always _ _ _)

-- Former endpoint: runSql_rowsStored
example (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : Database.RowsStoredWide database) (supported : supportedSqlFrom 0 script { database } = true) :
    (runSql script database).Holds (Database.RowsStoredWide) :=
  PreservationMigration.raw_ready_zero (PreservationMigration.under_ready (old := fun _ _ => True) (rowsStored_statementKeeps) (fun _ _ _ _ _ _ ready => ready)) script holds supported (PreservationMigration.raw_always _ _ _)

-- Former endpoint: runSqlFrom_rowsAliased
example (limits : Limits) (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds (Database.RowsAliasedSupported limits))
    (supported : supportedSqlFrom position script state = true)
    (conditions : PreservationMigration.RawConditions (Resolved.Statement.AppliedValid limits) position script state) :
    (runSqlFrom position script state).Holds (Database.RowsAliasedSupported limits) :=
  PreservationMigration.raw_ready (PreservationMigration.under_ready (rowsAliased_statementKeeps limits) (fun _ _ _ _ _ met ready => ⟨met, ready⟩)) position script holds supported conditions

-- Former endpoint: runSql_rowsAliased
example (limits : Limits) (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : Database.RowsAliasedSupported limits database) (supported : supportedSqlFrom 0 script { database } = true)
    (conditions : PreservationMigration.RawConditions (Resolved.Statement.AppliedValid limits) 0 script { database }) :
    (runSql script database).Holds (Database.RowsAliasedSupported limits) :=
  PreservationMigration.raw_ready_zero (PreservationMigration.under_ready (rowsAliased_statementKeeps limits) (fun _ _ _ _ _ met ready => ⟨met, ready⟩)) script holds supported conditions

-- Former endpoint: runSqlFrom_admitted
example {profile : Profile} (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds (Database.Admitted profile))
    (supported : supportedSqlFrom position script state = true)
    (conditions : PreservationMigration.RawConditions (Resolved.Statement.AppliedValid profile.limits) position script state) :
    (runSqlFrom position script state).Holds (Database.Admitted profile) :=
  PreservationMigration.raw_ready (PreservationMigration.under_ready (admitted_statementKeeps profile) (fun _ _ _ _ _ met ready => ⟨met, ready⟩)) position script holds supported conditions

-- Former endpoint: runSql_admitted
example {profile : Profile} (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : Database.Admitted profile database) (supported : supportedSqlFrom 0 script { database } = true)
    (conditions : PreservationMigration.RawConditions (Resolved.Statement.AppliedValid profile.limits) 0 script { database }) :
    (runSql script database).Holds (Database.Admitted profile) :=
  PreservationMigration.raw_ready_zero (PreservationMigration.under_ready (admitted_statementKeeps profile) (fun _ _ _ _ _ met ready => ⟨met, ready⟩)) script holds supported conditions

-- Former endpoint: runScriptAllFrom_catalogSupported
example {limits : Limits} (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = limits)
    (holds : connection.state.Holds (Database.CatalogSupported limits)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds (Database.CatalogSupported limits) :=
  PreservationMigration.surface_derived (PreservationMigration.under_ready (catalogSupported_statementKeeps limits) (fun _ _ _ _ _ met _ => met)) context clock
    (fun _ _ _ _ keep ok => resolveStatement_appliedValid context execution same keep ok) index script holds

-- Former endpoint: runScriptAllFrom_rowsShaped
example (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds Database.RowsShaped) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds Database.RowsShaped :=
  PreservationMigration.surface_derived (PreservationMigration.under_ready (rowsShaped_statementKeeps) (fun _ _ _ _ _ met _ => met)) context clock (fun _ _ _ _ _ _ => trivial) index script holds

