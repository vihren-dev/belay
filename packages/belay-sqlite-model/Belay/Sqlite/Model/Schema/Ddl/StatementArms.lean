import Belay.Sqlite.Model.Schema.Dispatch.ResolveStatement
import Belay.Sqlite.Model.Frontend.Codecs.StatementAttr
import Belay.Sqlite.Model.Queries.Preparation.WriteTracedLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- CREATE TABLE resolves against the catalog of the state, with {name}`resolveCreateTableIf` for the
clause {lit}`IF NOT EXISTS`. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_createTable (context : ResolveContext) (state : ResolveState)
    (name : Identifier) (columns : List Syntax.ColumnDefinition) (constraints : List Syntax.TableConstraint)
    (options : Syntax.TableOptions) (ifNotExists : Bool) :
    resolveStatement context state (.createTable name columns constraints options ifNotExists) =
      state.withCatalog (resolveCreateTableIf context state.catalog name columns constraints options ifNotExists) := rfl

/-- CREATE INDEX resolves against the catalog of the state, with {name}`resolveCreateIndexIf` for the
clause {lit}`IF NOT EXISTS`. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_createIndex (context : ResolveContext) (state : ResolveState)
    (name : Identifier) (unique : Bool) (table : Identifier) (terms : List Syntax.OrderTerm)
    (filter : Option Syntax.Expr) (ifNotExists : Bool) :
    resolveStatement context state (.createIndex name unique table terms filter ifNotExists) =
      state.withCatalog (resolveCreateIndexIf context state.catalog name unique table terms filter ifNotExists) := rfl

/-- ALTER TABLE RENAME TO resolves against the catalog of the state. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_renameTable (context : ResolveContext) (state : ResolveState)
    (table newName : Identifier) :
    resolveStatement context state (.renameTable table newName) =
      state.withCatalog (resolveRenameTable context state.catalog table newName) := rfl

/-- ALTER TABLE RENAME COLUMN resolves against the catalog of the state. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_renameColumn (context : ResolveContext) (state : ResolveState)
    (table column newName : Identifier) (columnToken : String) (quoted : Bool) :
    resolveStatement context state (.renameColumn table column newName columnToken quoted) =
      state.withCatalog (resolveRenameColumn context state.catalog table column newName columnToken quoted) := rfl

/-- ALTER TABLE DROP COLUMN resolves against the catalog of the state. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_dropColumn (context : ResolveContext) (state : ResolveState)
    (table column : Identifier) (columnToken : String) :
    resolveStatement context state (.dropColumn table column columnToken) =
      state.withCatalog (resolveDropColumn context state.catalog table column columnToken) := rfl

/-- DROP TABLE is a write: it checks the foreign keys of the state. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_dropTable (context : ResolveContext) (state : ResolveState)
    (name : Identifier) (ifExists : Bool) :
    resolveStatement context state (.dropTable name ifExists) =
      state.withWrite context (resolveDropTable state.catalog name ifExists) := rfl

/-- DROP VIEW resolves against the catalog of the state. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_dropView (context : ResolveContext) (state : ResolveState)
    (name : Identifier) (ifExists : Bool) :
    resolveStatement context state (.dropView name ifExists) =
      state.withCatalog (resolveDropView state.catalog name ifExists) := rfl

/-- DROP INDEX resolves against the catalog of the state. Proof sketch: both sides are equal by definition. -/
@[statement_arms] theorem resolveStatement_dropIndex (context : ResolveContext) (state : ResolveState)
    (name : Identifier) (ifExists : Bool) :
    resolveStatement context state (.dropIndex name ifExists) =
      state.withCatalog (resolveDropIndex state.catalog name ifExists) := rfl

end Belay.Sqlite.Model
