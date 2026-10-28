import Belay.Sqlite.Model

/-! Temporary migration witnesses for the 84 endpoint formulas at 3e2212ed6983.
Retain this single set through the execution-condition task's final Nix acceptance. -/

open Belay.Sqlite.Model

-- Former endpoint: runScriptAllFrom_rowidsDistinct
example (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds Database.RowidsDistinct) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds Database.RowidsDistinct :=
  runScriptAllFrom_holds_derived (rowidsDistinct_statementKeeps) context clock (fun _ _ _ _ _ _ => trivial) index script holds

-- Former endpoint: runScriptAllFrom_rowidsInRange
example (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds Database.RowidsInRange) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds Database.RowidsInRange :=
  runScriptAllFrom_holds_derived (rowidsInRange_statementKeeps) context clock (fun _ _ _ _ _ _ => trivial) index script holds

-- Former endpoint: runScriptAllFrom_rowsWide
example (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds Database.RowsWide) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds Database.RowsWide :=
  runScriptAllFrom_holds_derived (rowsWide_statementKeeps) context clock (fun _ _ _ _ _ _ => trivial) index script holds

-- Former endpoint: runScriptAllFrom_rowsStored
example (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds Database.RowsStoredWide) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds Database.RowsStoredWide :=
  runScriptAllFrom_holds_derived (rowsStored_statementKeeps) context clock (fun _ _ _ _ _ _ => trivial) index script holds

-- Former endpoint: runScriptAllFrom_rowsAliased
example {limits : Limits} (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = limits)
    (holds : connection.state.Holds (Database.RowsAliasedSupported limits)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds (Database.RowsAliasedSupported limits) :=
  runScriptAllFrom_holds_derived (rowsAliased_statementKeeps limits) context clock
    (fun _ _ _ _ keep ok => resolveStatement_appliedValid context execution same
      (keep.mono (fun _ holds => holds.2)) ok) index script holds

-- Former endpoint: runScriptAllFrom_admitted
example {profile : Profile} (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.Admitted profile)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds (Database.Admitted profile) :=
  runScriptAllFrom_holds_derived (admitted_statementKeeps profile) context clock
    (fun _ _ _ _ keep ok => resolveStatement_appliedValid context execution same
      (keep.mono (fun _ holds => holds.catalogSupported)) ok) index script holds

-- Former endpoint: runScriptAllFrom_keysUnique
example {profile : Profile} (context : ResolveContext) (clock : Option Clock)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.AdmittedWith profile Database.KeysUnique)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (Database.AdmittedWith profile Database.KeysUnique) :=
  runScriptAllFrom_admittedWith keysUnique_statementKeeps
    (fun _ statement admitted applied link => statement.runCondition_of_link admitted applied link)
    context clock index script execution same holds

-- Former endpoint: runScriptAllFrom_notNull
example {profile : Profile} (context : ResolveContext) (clock : Option Clock)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.AdmittedWith profile Database.NotNull)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (Database.AdmittedWith profile Database.NotNull) :=
  runScriptAllFrom_admittedWith notNull_statementKeeps
    (fun _ statement admitted _ _ => statement.notNullCondition_of_admitted admitted)
    context clock index script execution same holds

-- Former endpoint: runScriptAllFrom_typesFit
example {profile : Profile} (context : ResolveContext) (clock : Option Clock)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.AdmittedWith profile Database.TypesFit)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (Database.AdmittedWith profile Database.TypesFit) :=
  runScriptAllFrom_admittedWith typesFit_statementKeeps
    (fun _ statement admitted _ link => statement.typesFitCondition_of_link admitted link)
    context clock index script execution same holds

-- Former endpoint: runScriptAllFrom_checksHold
example {profile : Profile} (context : ResolveContext) (clock : Option Clock)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.AdmittedWith profile Database.ChecksHold)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (Database.AdmittedWith profile Database.ChecksHold) :=
  runScriptAllFrom_admittedWith checksHold_statementKeeps
    (fun _ statement admitted _ _ => statement.checksHoldCondition_of_admitted admitted)
    context clock index script execution same holds

-- Former endpoint: runScriptAllFrom_constraintAtoms
example {profile : Profile} (context : ResolveContext) (clock : Option Clock)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.AdmittedWith profile Database.ConstraintAtoms)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (Database.AdmittedWith profile Database.ConstraintAtoms) :=
  runScriptAllFrom_admittedWith constraintAtoms_statementKeeps
    (fun _ statement admitted applied link => statement.atomsCondition_of_link admitted applied link)
    context clock index script execution same holds

-- Former endpoint: runSqlFrom_rowReferences
example (profile : Profile) (position : Nat)
    (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping))
    (conditions : RunConditionsWith (fun statement database => statement.ForeignKeyRowsCondition profile database) position script state) :
    (runSqlFrom position script state).Holds (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  runSqlFrom_holds (rowReferences_statementKeeps profile) position script holds conditions

-- Former endpoint: runSql_rowReferences
example (profile : Profile) (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (conditions : RunConditionsWith (fun statement database => statement.ForeignKeyRowsCondition profile database) 0 script {database}) :
    (runSql script database).Holds (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  runSql_holds (rowReferences_statementKeeps profile) script holds conditions

-- Former endpoint: runScriptAllFrom_rowReferences
example (profile : Profile) (context : ResolveContext) (clock : Option Clock)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping))
    (conditions : ScriptConditionsWith (fun statement database => statement.ForeignKeyRowsCondition profile database)
      context clock index connection script) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  runScriptAllFrom_holds (rowReferences_statementKeeps profile) context clock index script holds conditions

-- Former endpoint: runSqlFrom_foreignKeyAtoms
example (profile : Profile) (mapping : ForeignKeyMapping) (position : Nat)
    (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds (fun database => database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping))
    (conditions : RunConditionsWith (fun statement database => statement.KeepsParentSchema ∧ statement.ForeignKeyRowsCondition profile database) position script state) :
    (runSqlFrom position script state).Holds
      (fun database => database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping) :=
  runSqlFrom_holds (foreignKeyAtoms_statementKeeps profile mapping) position script holds conditions

-- Former endpoint: runSql_foreignKeyAtoms
example (profile : Profile) (mapping : ForeignKeyMapping)
    (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping)
    (conditions : RunConditionsWith (fun statement database => statement.KeepsParentSchema ∧ statement.ForeignKeyRowsCondition profile database) 0 script {database}) :
    (runSql script database).Holds
      (fun database => database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping) :=
  runSql_holds (foreignKeyAtoms_statementKeeps profile mapping) script holds conditions

-- Former endpoint: runScriptAllFrom_foreignKeyAtoms
example (profile : Profile) (mapping : ForeignKeyMapping) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds (fun database => database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping))
    (conditions : ScriptConditionsWith (fun statement database => statement.KeepsParentSchema ∧ statement.ForeignKeyRowsCondition profile database)
      context clock index connection script) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (fun database => database.ParentSchemasCompatible mapping ∧ database.RowReferencesHold mapping) :=
  runScriptAllFrom_holds (foreignKeyAtoms_statementKeeps profile mapping) context clock index script holds conditions

-- Former endpoint: runSqlFrom_parentSchemasCompatible
example (mapping : ForeignKeyMapping) (position : Nat)
    (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds (Database.ParentSchemasCompatible mapping))
    (conditions : RunConditionsWith (fun statement _ => statement.KeepsParentSchema) position script state) :
    (runSqlFrom position script state).Holds (Database.ParentSchemasCompatible mapping) :=
  runSqlFrom_holds (parentSchemasCompatibleKeeps mapping) position script holds conditions

-- Former endpoint: runSql_parentSchemasCompatible
example (mapping : ForeignKeyMapping)
    (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : database.ParentSchemasCompatible mapping)
    (conditions : RunConditionsWith (fun statement _ => statement.KeepsParentSchema) 0 script { database }) :
    (runSql script database).Holds (Database.ParentSchemasCompatible mapping) :=
  runSql_holds (parentSchemasCompatibleKeeps mapping) script holds conditions

-- Former endpoint: runScriptAllFrom_parentSchemasCompatible
example (mapping : ForeignKeyMapping) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) {connection : Connection}
    (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds (Database.ParentSchemasCompatible mapping))
    (conditions : ScriptConditionsWith (fun statement _ => statement.KeepsParentSchema)
      context clock index connection script) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (Database.ParentSchemasCompatible mapping) :=
  runScriptAllFrom_holds (parentSchemasCompatibleKeeps mapping) context clock index script holds conditions

