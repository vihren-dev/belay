import Belay.Sqlite.Model

/-! Temporary migration witnesses for the 84 endpoint formulas at 3e2212ed6983.
Retain this single set through the execution-condition task's final Nix acceptance. -/

open Belay.Sqlite.Model

-- Former endpoint: runSqlFrom_parentSchemasCompatibleSelected
example (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState}
    (holds : state.Holds (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping))
    (conditions : PreservationMigration.RawConditions (fun statement database => statement.ForeignKeySchemaCondition database)
      position script state) :
    (runSqlFrom position script state).Holds
      (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping) :=
  PreservationMigration.raw parentSchemasCompatibleSelectedKeeps position script holds conditions

-- Former endpoint: runSql_parentSchemasCompatibleSelected
example (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping)
    (conditions : PreservationMigration.RawConditions (fun statement database => statement.ForeignKeySchemaCondition database)
      0 script {database}) :
    (runSql script database).Holds (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping) :=
  PreservationMigration.raw_zero parentSchemasCompatibleSelectedKeeps script holds conditions

-- Former endpoint: runScriptAllFrom_parentSchemasCompatibleSelected
example (context : ResolveContext) (clock : Option Clock)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds
      (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping))
    (conditions : PreservationMigration.SurfaceConditions (fun statement database => statement.ForeignKeySchemaCondition database)
      context clock index connection script) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping) :=
  PreservationMigration.surface parentSchemasCompatibleSelectedKeeps context clock index script holds conditions

-- Former endpoint: runSqlFrom_foreignKeyAtomsSelected
example (profile : Profile) (position : Nat)
    (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
      database.RowReferencesHold database.catalog.foreignKeyMapping))
    (conditions : PreservationMigration.RawConditions (fun statement database => statement.ForeignKeyAtomsCondition profile database)
      position script state) :
    (runSqlFrom position script state).Holds
      (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
        database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  PreservationMigration.raw (foreignKeyAtomsSelected_statementKeeps profile) position script holds conditions

-- Former endpoint: runSql_foreignKeyAtomsSelected
example (profile : Profile) (script : List (Resolved.Statement × List Value))
    {database : Database}
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
      database.RowReferencesHold database.catalog.foreignKeyMapping)
    (conditions : PreservationMigration.RawConditions (fun statement database => statement.ForeignKeyAtomsCondition profile database)
      0 script {database}) :
    (runSql script database).Holds
      (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
        database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  PreservationMigration.raw_zero (foreignKeyAtomsSelected_statementKeeps profile) script holds conditions

-- Former endpoint: runScriptAllFrom_foreignKeyAtomsSelected
example (profile : Profile) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds (fun database =>
      database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
        database.RowReferencesHold database.catalog.foreignKeyMapping))
    (conditions : PreservationMigration.SurfaceConditions (fun statement database => statement.ForeignKeyAtomsCondition profile database)
      context clock index connection script) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds
      (fun database => database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
        database.RowReferencesHold database.catalog.foreignKeyMapping) :=
  PreservationMigration.surface (foreignKeyAtomsSelected_statementKeeps profile) context clock index script holds conditions

-- Former endpoint: runStatement_insert_notNull
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (rows : List (List Resolved.Cell))
    (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query) {database : Database}
    (notNull : database.NotNull) :
    (runStatement clock counters parameters (.insert target rows returning subqueries none) database).effect.Satisfies Database.NotNull :=
  runStatement_insert_rowLocal Table.notNullAtom clock counters parameters target rows returning subqueries notNull

-- Former endpoint: runStatement_insert_typesFit
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (rows : List (List Resolved.Cell))
    (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query) {database : Database}
    (fits : database.TypesFit) :
    (runStatement clock counters parameters (.insert target rows returning subqueries none) database).effect.Satisfies Database.TypesFit :=
  runStatement_insert_rowLocal Table.typesFitAtom clock counters parameters target rows returning subqueries fits

-- Former endpoint: runStatement_insert_checksHold
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (rows : List (List Resolved.Cell))
    (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query) {database : Database}
    (holds : database.ChecksHold) :
    (runStatement clock counters parameters (.insert target rows returning subqueries none) database).effect.Satisfies Database.ChecksHold :=
  runStatement_insert_rowLocal Table.checksHoldAtom clock counters parameters target rows returning subqueries holds

-- Former endpoint: runStatement_update_notNull
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (assignments : List (Nat × Resolved.Expr))
    (filter : Option Resolved.Expr) (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query)
    {database : Database}
    (notNull : database.NotNull) :
    (runStatement clock counters parameters (.update target assignments filter returning subqueries none) database).effect.Satisfies Database.NotNull :=
  runStatement_update_rowLocal Table.notNullAtom clock counters parameters target assignments filter returning subqueries notNull

-- Former endpoint: runStatement_update_typesFit
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (assignments : List (Nat × Resolved.Expr))
    (filter : Option Resolved.Expr) (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query)
    {database : Database}
    (fits : database.TypesFit) :
    (runStatement clock counters parameters (.update target assignments filter returning subqueries none) database).effect.Satisfies Database.TypesFit :=
  runStatement_update_rowLocal Table.typesFitAtom clock counters parameters target assignments filter returning subqueries fits

-- Former endpoint: runStatement_update_checksHold
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (assignments : List (Nat × Resolved.Expr))
    (filter : Option Resolved.Expr) (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query)
    {database : Database}
    (holds : database.ChecksHold) :
    (runStatement clock counters parameters (.update target assignments filter returning subqueries none) database).effect.Satisfies Database.ChecksHold :=
  runStatement_update_rowLocal Table.checksHoldAtom clock counters parameters target assignments filter returning subqueries holds

-- Former endpoint: runStatement_delete_notNull
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (filter : Option Resolved.Expr)
    (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query) {database : Database}
    (notNull : database.NotNull) :
    (runStatement clock counters parameters (.delete target filter returning subqueries none) database).effect.Satisfies Database.NotNull :=
  runStatement_delete_rowLocal Table.notNullAtom clock counters parameters target filter returning subqueries notNull

-- Former endpoint: runStatement_delete_typesFit
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (filter : Option Resolved.Expr)
    (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query) {database : Database}
    (fits : database.TypesFit) :
    (runStatement clock counters parameters (.delete target filter returning subqueries none) database).effect.Satisfies Database.TypesFit :=
  runStatement_delete_rowLocal Table.typesFitAtom clock counters parameters target filter returning subqueries fits

-- Former endpoint: runStatement_delete_checksHold
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (filter : Option Resolved.Expr)
    (returning : List (Resolved.Expr × String)) (subqueries : List Resolved.Query) {database : Database}
    (holds : database.ChecksHold) :
    (runStatement clock counters parameters (.delete target filter returning subqueries none) database).effect.Satisfies Database.ChecksHold :=
  runStatement_delete_rowLocal Table.checksHoldAtom clock counters parameters target filter returning subqueries holds

-- Former endpoint: runStatement_writesNone_notNull
example (clock : Int) (counters : Counters) (parameters : List Value) {database : Database} (statement : Resolved.Statement)
    (writesNone : (∃ query subqueries, statement = .query query subqueries) ∨ (∃ setting on, statement = .setting setting on) ∨
      (∃ error, statement = .prepareError error) ∨ statement = .begin ∨ statement = .commit ∨ statement = .rollback)
    (notNull : database.NotNull) :
    (runStatement clock counters parameters statement database).effect.Satisfies Database.NotNull :=
  runStatement_writesNone_rowLocal (atom := Table.NotNull) clock counters parameters notNull statement writesNone

-- Former endpoint: runStatement_writesNone_typesFit
example (clock : Int) (counters : Counters) (parameters : List Value) {database : Database} (statement : Resolved.Statement)
    (writesNone : (∃ query subqueries, statement = .query query subqueries) ∨ (∃ setting on, statement = .setting setting on) ∨
      (∃ error, statement = .prepareError error) ∨ statement = .begin ∨ statement = .commit ∨ statement = .rollback)
    (fits : database.TypesFit) :
    (runStatement clock counters parameters statement database).effect.Satisfies Database.TypesFit :=
  runStatement_writesNone_rowLocal (atom := Table.TypesFit) clock counters parameters fits statement writesNone

-- Former endpoint: runStatement_writesNone_checksHold
example (clock : Int) (counters : Counters) (parameters : List Value) {database : Database} (statement : Resolved.Statement)
    (writesNone : (∃ query subqueries, statement = .query query subqueries) ∨ (∃ setting on, statement = .setting setting on) ∨
      (∃ error, statement = .prepareError error) ∨ statement = .begin ∨ statement = .commit ∨ statement = .rollback)
    (holds : database.ChecksHold) :
    (runStatement clock counters parameters statement database).effect.Satisfies Database.ChecksHold :=
  runStatement_writesNone_rowLocal (atom := Table.ChecksHold) clock counters parameters holds statement writesNone

-- Former endpoint: runStatement_upsert_notNull
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (rows : List (List Resolved.Cell))
    (clauses : List Resolved.ConflictClause) (returning : List (Resolved.Expr × String))
    (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query) {database : Database}
    (notNull : database.NotNull) :
    (effectDatabase (runStatement clock counters parameters (.upsert target rows clauses returning algorithm subqueries none) database).effect).NotNull :=
  runStatement_upsert_rowLocal Table.notNullAtom clock counters parameters target rows clauses returning algorithm subqueries notNull

-- Former endpoint: runStatement_upsert_typesFit
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (rows : List (List Resolved.Cell))
    (clauses : List Resolved.ConflictClause) (returning : List (Resolved.Expr × String))
    (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query) {database : Database}
    (fits : database.TypesFit) :
    (effectDatabase (runStatement clock counters parameters (.upsert target rows clauses returning algorithm subqueries none) database).effect).TypesFit :=
  runStatement_upsert_rowLocal Table.typesFitAtom clock counters parameters target rows clauses returning algorithm subqueries fits

-- Former endpoint: runStatement_upsert_checksHold
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (rows : List (List Resolved.Cell))
    (clauses : List Resolved.ConflictClause) (returning : List (Resolved.Expr × String))
    (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query) {database : Database}
    (holds : database.ChecksHold) :
    (effectDatabase (runStatement clock counters parameters (.upsert target rows clauses returning algorithm subqueries none) database).effect).ChecksHold :=
  runStatement_upsert_rowLocal Table.checksHoldAtom clock counters parameters target rows clauses returning algorithm subqueries holds

-- Former endpoint: runStatement_createTable_notNull
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (shape : CatalogTable)
    {database : Database}
    (notNull : database.NotNull) :
    (runStatement clock counters parameters (.createTable target name shape) database).effect.Satisfies Database.NotNull :=
  runStatement_createTable_rowLocal Table.notNullAtom clock counters parameters target name shape notNull

