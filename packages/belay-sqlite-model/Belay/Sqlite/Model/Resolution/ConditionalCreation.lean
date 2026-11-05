import Belay.Sqlite.Model.Resolution.Definitions

set_option doc.verso true

/-! {lit}`CREATE TABLE IF NOT EXISTS` and {lit}`CREATE INDEX IF NOT EXISTS` (ADR 0030, D3). SQLite
checks the name of the new object in the order of {lit}`resolveCreateTable` and
{lit}`resolveCreateIndex`; when the clause is present and the name check finds the object that
makes the statement a no-op, SQLite stops and reads nothing after the name. The no-op resolves to
{lit}`.drop []` with {lit}`catalog.drop []`, as a no-op of CREATE VIEW
does. Every other case resolves as without the clause. -/

namespace Belay.Sqlite.Model

/-- Whether {lit}`CREATE TABLE IF NOT EXISTS name` is a no-op on the catalog: the name is not
reserved (a reserved name is an error before the name check) and names a table or a view.
An index of the name stays an error, and a trigger has its own namespace. -/
def createTableKept (catalog : Catalog) (name : Identifier) : Bool :=
  !reservedName name && match catalog.find name with
    | some (_, { entry := .table _, .. }) | some (_, { entry := .view _, .. }) => true
    | some (_, { entry := .index _, .. }) | some (_, { entry := .trigger _, .. }) | none => false

/-- Whether {lit}`CREATE INDEX IF NOT EXISTS name ON tableName` is a no-op on the catalog: the
checks before the name pass (the table exists, and neither the table name nor the index name
is reserved), and the name is an index, whatever its table, terms, filter or uniqueness.
A table or a view of the name stays an error. -/
def createIndexKept (catalog : Catalog) (name tableName : Identifier) : Bool :=
  (catalog.findTable tableName).isSome && !reservedName tableName && !reservedName name &&
    match catalog.find name with
    | some (_, { entry := .index _, .. }) => true
    | some (_, { entry := .table _, .. }) | some (_, { entry := .view _, .. })
    | some (_, { entry := .trigger _, .. }) | none => false

/-- Resolve {lit}`CREATE TABLE`, with the clause {lit}`IF NOT EXISTS` when {lit}`ifNotExists`:
the no-op of {name}`createTableKept`, else {name}`resolveCreateTable`. -/
def resolveCreateTableIf (context : ResolveContext) (catalog : Catalog) (name : Identifier)
    (columns : List Syntax.ColumnDefinition) (constraints : List Syntax.TableConstraint)
    (options : Syntax.TableOptions) (ifNotExists : Bool) : StatementResolution :=
  if ifNotExists && createTableKept catalog name then .ok (.drop [], catalog.drop [])
  else resolveCreateTable context catalog name columns constraints options

/-- Resolve {lit}`CREATE INDEX`, with the clause {lit}`IF NOT EXISTS` when {lit}`ifNotExists`:
the no-op of {name}`createIndexKept`, else {name}`resolveCreateIndex`. -/
def resolveCreateIndexIf (context : ResolveContext) (catalog : Catalog) (name : Identifier) (unique : Bool)
    (tableName : Identifier) (terms : List Syntax.OrderTerm) (filter : Option Syntax.Expr)
    (ifNotExists : Bool) : StatementResolution :=
  if ifNotExists && createIndexKept catalog name tableName then .ok (.drop [], catalog.drop [])
  else resolveCreateIndex context catalog name unique tableName terms filter

/-- For every condition, catalog, resolution, statement and catalog after it: if the resolution
that is the no-op on the catalog when the condition holds, and the given resolution otherwise,
succeeds with the statement and the catalog after it, then

* the statement is {lit}`.drop []` and the catalog after it is {lit}`catalog.drop []`, or
* the given resolution succeeds with the same statement and catalog.

Proof sketch: split the condition. -/
theorem noOpOr_ok {kept : Bool} {catalog after : Catalog} {resolution : StatementResolution}
    {statement : Resolved.Statement}
    (ok : (if kept then .ok (.drop [], catalog.drop []) else resolution) = .ok (statement, after)) :
    (statement = .drop [] ∧ after = catalog.drop []) ∨ resolution = .ok (statement, after) := by
  split at ok
  · cases ok; exact .inl ⟨rfl, rfl⟩
  · exact .inr ok

/-- For every context, catalog, CREATE TABLE and flag: if {name}`resolveCreateTableIf` succeeds with
a statement and a catalog after it, then the statement is {lit}`.drop []` with
{lit}`catalog.drop []` after it, or {name}`resolveCreateTable` succeeds with the same statement and
catalog. Proof sketch: {name}`noOpOr_ok`. -/
theorem resolveCreateTableIf_cases {context : ResolveContext} {catalog after : Catalog} {name : Identifier}
    {columns : List Syntax.ColumnDefinition} {constraints : List Syntax.TableConstraint}
    {options : Syntax.TableOptions} {ifNotExists : Bool} {statement : Resolved.Statement}
    (ok : resolveCreateTableIf context catalog name columns constraints options ifNotExists = .ok (statement, after)) :
    (statement = .drop [] ∧ after = catalog.drop []) ∨
      resolveCreateTable context catalog name columns constraints options = .ok (statement, after) :=
  noOpOr_ok ok

/-- For every context, catalog, CREATE INDEX and flag: if {name}`resolveCreateIndexIf` succeeds with
a statement and a catalog after it, then the statement is {lit}`.drop []` with
{lit}`catalog.drop []` after it, or {name}`resolveCreateIndex` succeeds with the same statement and
catalog. Proof sketch: {name}`noOpOr_ok`. -/
theorem resolveCreateIndexIf_cases {context : ResolveContext} {catalog after : Catalog} {name : Identifier}
    {unique : Bool} {tableName : Identifier} {terms : List Syntax.OrderTerm} {filter : Option Syntax.Expr}
    {ifNotExists : Bool} {statement : Resolved.Statement}
    (ok : resolveCreateIndexIf context catalog name unique tableName terms filter ifNotExists = .ok (statement, after)) :
    (statement = .drop [] ∧ after = catalog.drop []) ∨
      resolveCreateIndex context catalog name unique tableName terms filter = .ok (statement, after) :=
  noOpOr_ok ok

/-- Without the clause, CREATE TABLE resolves with {name}`resolveCreateTable`. Proof sketch: the
condition is false by definition. -/
@[simp] theorem resolveCreateTableIf_false (context : ResolveContext) (catalog : Catalog) (name : Identifier)
    (columns : List Syntax.ColumnDefinition) (constraints : List Syntax.TableConstraint)
    (options : Syntax.TableOptions) :
    resolveCreateTableIf context catalog name columns constraints options false =
      resolveCreateTable context catalog name columns constraints options := rfl

/-- Without the clause, CREATE INDEX resolves with {name}`resolveCreateIndex`. Proof sketch: the
condition is false by definition. -/
@[simp] theorem resolveCreateIndexIf_false (context : ResolveContext) (catalog : Catalog) (name : Identifier)
    (unique : Bool) (tableName : Identifier) (terms : List Syntax.OrderTerm) (filter : Option Syntax.Expr) :
    resolveCreateIndexIf context catalog name unique tableName terms filter false =
      resolveCreateIndex context catalog name unique tableName terms filter := rfl

end Belay.Sqlite.Model
