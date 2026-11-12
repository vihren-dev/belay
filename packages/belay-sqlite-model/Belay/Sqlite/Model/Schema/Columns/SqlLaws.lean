import Belay.Sqlite.Model.Shared.Execution.SqlExecution
import Belay.Sqlite.Model.Queries.Evaluation.QueryPlainLaws
import Belay.Sqlite.Model.Shared.Resolved.StatementCatalog
import Belay.Sqlite.Model.Schema.Columns.ReadDefaults
import Belay.Sqlite.Model.Schema.Dispatch.StatementCounterReads

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Every statement in the script is CREATE TABLE or ADD COLUMN. This is a syntax
guard, not a validity or success claim. The empty script satisfies it; CREATE
INDEX, transaction control, literal writes and prepare errors do not. Use it for
schema preservation laws. -/
def SchemaOnly (script : List Resolved.Statement) : Prop :=
  ∀ statement ∈ script, statement.kind = .definition

/-- No statement in the script is INSERT (with or without {lit}`ON CONFLICT`, or with
cells that read the clock), UPDATE or DELETE, no DROP TABLE deletes rows for foreign keys, and
no query has a fallible call (a JSON call or
a function that can fail) in its expressions ({name}`Resolved.Query.expressions`,
{name}`Resolved.Expr.isFallibleCall` at any depth) or a {lit}`json_each`
source. This is a syntax guard, not a success claim; the empty script satisfies it. Each
statement:
* is not a write ({name}`Resolved.Statement.Kind.write`),
* if it is a DROP, checks no foreign keys, and
* if it is a query, has no subqueries, no {lit}`DISTINCT`, no fallible call, no
  {lit}`json_each` source, no compound terms ({name}`Resolved.Query.compound`) and no call of a
  counter function ({name}`Resolved.Statement.counterReads` is empty). -/
def NoWrites (script : List Resolved.Statement) : Prop :=
  ∀ statement ∈ script, statement.kind ≠ .write ∧
    (∀ positions keys, statement = .drop positions keys → keys = none) ∧
    ∀ query subqueries, statement = .query query subqueries →
    subqueries = [] ∧ query.distinct = none ∧ query.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true ∧
      query.sources.all (!·.source.isEach) = true ∧ query.compound = none ∧
      (Resolved.Statement.query query subqueries).counterReads = []

/-- Each definition in the script is one that the model describes: each ADD COLUMN has a time
default ({name}`CatalogColumn.clockDefault`) or a successful {name}`readDefaultValue` result,
and no statement is CREATE INDEX. Every CREATE TABLE and every other statement is
unrestricted; the empty script satisfies it. -/
def ModeledDefinitions (script : List Resolved.Statement) : Prop :=
  ∀ statement ∈ script, match statement with
    | .createTable .. => True
    | .addColumn _ column _ => (column.clockDefault || (readDefaultValue column).toOption.isSome) = true
    | .createIndex .. => False
    | .createView .. | .createTrigger .. | .rewrite _ | .dropColumn .. | .drop .. => True
    | .insert .. | .upsert .. | .insertSelect .. | .update .. | .delete .. | .begin | .commit | .rollback | .prepareError _
    | .query .. | .setting .. => True

end Belay.Sqlite.Model
