import Belay.Sqlite.Model

/-! Temporary migration witnesses for the 84 endpoint formulas at 3e2212ed6983.
Retain this single set through the execution-condition task's final Nix acceptance. -/

open Belay.Sqlite.Model

-- Former endpoint: runStatement_createTable_typesFit
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (shape : CatalogTable)
    {database : Database}
    (fits : database.TypesFit) :
    (runStatement clock counters parameters (.createTable target name shape) database).effect.Satisfies Database.TypesFit :=
  runStatement_createTable_rowLocal Table.typesFitAtom clock counters parameters target name shape fits

-- Former endpoint: runStatement_createTable_checksHold
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (shape : CatalogTable)
    {database : Database}
    (holds : database.ChecksHold) :
    (runStatement clock counters parameters (.createTable target name shape) database).effect.Satisfies Database.ChecksHold :=
  runStatement_createTable_rowLocal Table.checksHoldAtom clock counters parameters target name shape holds

-- Former endpoint: runStatement_createIndex_notNull
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (index : CatalogIndex)
    {database : Database}
    (notNull : database.NotNull) :
    (runStatement clock counters parameters (.createIndex target name index) database).effect.Satisfies Database.NotNull :=
  runStatement_createIndex_rowLocal Table.notNullAtom clock counters parameters target name index notNull

-- Former endpoint: runStatement_createIndex_typesFit
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (index : CatalogIndex)
    {database : Database}
    (fits : database.TypesFit) :
    (runStatement clock counters parameters (.createIndex target name index) database).effect.Satisfies Database.TypesFit :=
  runStatement_createIndex_rowLocal Table.typesFitAtom clock counters parameters target name index fits

-- Former endpoint: runStatement_createIndex_checksHold
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (index : CatalogIndex)
    {database : Database}
    (holds : database.ChecksHold) :
    (runStatement clock counters parameters (.createIndex target name index) database).effect.Satisfies Database.ChecksHold :=
  runStatement_createIndex_rowLocal Table.checksHoldAtom clock counters parameters target name index holds

-- Former endpoint: runStatement_createTrigger_notNull
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (trigger : CatalogTrigger)
    {database : Database}
    (notNull : database.NotNull) :
    (runStatement clock counters parameters (.createTrigger target name trigger) database).effect.Satisfies Database.NotNull :=
  runStatement_createTrigger_rowLocal Table.notNullAtom clock counters parameters target name trigger notNull

-- Former endpoint: runStatement_createTrigger_typesFit
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (trigger : CatalogTrigger)
    {database : Database}
    (fits : database.TypesFit) :
    (runStatement clock counters parameters (.createTrigger target name trigger) database).effect.Satisfies Database.TypesFit :=
  runStatement_createTrigger_rowLocal Table.typesFitAtom clock counters parameters target name trigger fits

-- Former endpoint: runStatement_createTrigger_checksHold
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (trigger : CatalogTrigger)
    {database : Database}
    (holds : database.ChecksHold) :
    (runStatement clock counters parameters (.createTrigger target name trigger) database).effect.Satisfies Database.ChecksHold :=
  runStatement_createTrigger_rowLocal Table.checksHoldAtom clock counters parameters target name trigger holds

-- Former endpoint: runStatement_drop_notNull
example (clock : Int) (counters : Counters) (parameters : List Value) (positions : List Nat) {database : Database}
    (notNull : database.NotNull) :
    (runStatement clock counters parameters (.drop positions none) database).effect.Satisfies Database.NotNull :=
  runStatement_drop_rowLocal (atom := Table.NotNull) clock counters parameters positions notNull

-- Former endpoint: runStatement_drop_typesFit
example (clock : Int) (counters : Counters) (parameters : List Value) (positions : List Nat) {database : Database}
    (fits : database.TypesFit) :
    (runStatement clock counters parameters (.drop positions none) database).effect.Satisfies Database.TypesFit :=
  runStatement_drop_rowLocal (atom := Table.TypesFit) clock counters parameters positions fits

-- Former endpoint: runStatement_drop_checksHold
example (clock : Int) (counters : Counters) (parameters : List Value) (positions : List Nat) {database : Database}
    (holds : database.ChecksHold) :
    (runStatement clock counters parameters (.drop positions none) database).effect.Satisfies Database.ChecksHold :=
  runStatement_drop_rowLocal (atom := Table.ChecksHold) clock counters parameters positions holds

-- Former endpoint: runStatement_addColumn_notNull
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat)
    (column : CatalogColumn) (refuses : Bool) {database : Database} (notNull : database.NotNull)
    (wide : database.RowsWideAt target) :
    (runStatement clock counters parameters (.addColumn target column refuses) database).effect.Satisfies Database.NotNull :=
  runStatement_addColumn_rowLocal clock counters parameters target column refuses notNull fun table _ found added =>
    (notNull _ table found).appendColumn (wide table found) added

-- Former endpoint: runStatement_addColumn_typesFit
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat)
    (column : CatalogColumn) (refuses : Bool) {database : Database} (fits : database.TypesFit)
    (wide : database.RowsWideAt target) (strict : database.StrictDefaultFitsAt target column) :
    (runStatement clock counters parameters (.addColumn target column refuses) database).effect.Satisfies Database.TypesFit :=
  runStatement_addColumn_rowLocal clock counters parameters target column refuses fits fun table _ found added =>
    (fits _ table found).appendColumn (wide table found) (strict table found) added

-- Former endpoint: runStatement_addColumn_checksHold
example (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat)
    (column : CatalogColumn) (refuses : Bool) {database : Database} (holds : database.ChecksHold)
    (wide : database.RowsWideAt target) (reads : database.ChecksReadBelowAt target) :
    (runStatement clock counters parameters (.addColumn target column refuses) database).effect.Satisfies Database.ChecksHold :=
  runStatement_addColumn_rowLocal clock counters parameters target column refuses holds fun table _ found added =>
    (holds _ table found).appendColumn (wide table found) (reads table found) added

