import Belay.Sqlite.Model.Resolution.FunctionSources
import Belay.Sqlite.Model.Resolution.TableReference

set_option doc.verso true

/-! The reference to a source in {lit}`FROM`, resolved with the name trace (ADR 0013, D5): a table, a
{lit}`json_each` source, a table-valued pragma, or an indexed query. The paths follow
{lit}`Syntax.Statement.select`: child 1 is the first source and child 2 the joins; in a join,
child 1 is its source. -/

namespace Belay.Sqlite.Model

/-- A source of {lit}`FROM` whose reference is resolved: a table at its catalog position, or at its position
in the catalog of the initial database, {lit}`json_each` with the path of its reference and its arguments as written, which
resolve after the scope is complete ({name}`resolveEachArguments`), or the rows of a
table-valued pragma ({name}`pragmaReference`), or an indexed SELECT with its output width. -/
inductive SourceItem where
  /-- A table at its position in the catalog. -/
  | table (position : Nat)
  /-- A table at its position in the catalog of the initial database ({lit}`before.t`). -/
  | initialTable (position : Nat)
  /-- A {lit}`json_each` source: the path of its reference and its arguments. -/
  | each (path : List Nat) (arguments : List Syntax.Expr)
  /-- A table-valued pragma with its rows. -/
  | pragma (rows : Resolved.PragmaRows)
  /-- An indexed query with the width of its output rows. -/
  | subquery (index width : Nat)

/-- A source of {lit}`FROM` before its expressions resolve: the source, the kind of its
join with the sources before it, and its condition. -/
structure PendingSource where
  /-- The table, function, pragma or indexed SELECT source. -/
  item : SourceItem
  /-- The kind of the join; an inner join for the first source. -/
  kind : Resolved.JoinKind
  /-- The condition of the join; none for the first source. -/
  condition : JoinCondition

/-- The item and the source in scope of the reference at {lit}`path`: a table
({name}`resolveTableReference`), a table-valued pragma, whose name starts with
{lit}`pragma_` ({name}`pragmaReference`), {lit}`json_each` ({name}`eachReference`), or an indexed
query from {lit}`queries`. Use the default callback when no indexed queries are available.
The {lit}`prefix_` locates local restrictions; query callback failures already have their paths.
A view used with function arguments reports SQLite's not-a-function error
before its body is expanded.

A reference with the schema name {lit}`before` ({name}`Syntax.TableReference.readsInitial`) resolves
in the optional catalog {lit}`initial` of the initial database, as an {name}`SourceItem.initialTable` whose
source is marked {name}`ScopeSource.initial`, and a missing table is SQLite's {lit}`no such table: before.t`.
Without that catalog, with a function call, or with another schema name, it is
{name}`RestrictionKind.initialDatabase`; it never reads the current catalog. An indexed query expanded from a
view of the initial database keeps the mark.
The table, alias and schema of the reference are recorded at their parts of {lit}`path`: schema
first, then the table, then the alias. A source that a view, a {lit}`WITH` definition or a derived table
expanded to has the table as written (none for a derived table) and its alias; {lit}`index` is the
position of the source in its {lit}`FROM`. -/
def resolveReferenceTraced (catalog : Catalog) (path : List Nat) (reference : Syntax.TableReference)
    (queries : Nat → Except SourceIssue ScopeSource := fun _ => .error (.value (.restriction [] .subqueryHere)))
    (prefix_ : List Nat := []) (initial : Option Catalog := none) (index : Nat := 0) :
    Traced SourceIssue (SourceItem × ScopeSource) :=
  match reference.query with
  | some queryIndex => do
    if reference.arguments.isSome then throw (.value (.restriction (prefix_ ++ path) .subqueryHere))
    Traced.recordAll (reference.schemaOccurrences (prefix_ ++ path))
    let source ← Traced.lift (queries queryIndex)
    let expanded : ScopeSource :=
      { source with
        name := reference.alias.getD (name! "")
        qualified := reference.alias.isSome
        queryIndex := some queryIndex
        initial := reference.readsInitial
        hasRowid := false }
    Traced.recordAll (reference.expandedOccurrences (prefix_ ++ path) (expanded.reference index))
    pure (.subquery queryIndex source.columns.length, expanded)
  | none => Traced.under prefix_ (do
    Traced.recordAll (reference.schemaOccurrences path)
    let resolved ← (match reference.schema, reference.arguments with
      | some _, some _ => throw (.value (.restriction path .initialDatabase))
      | some _, none => match initial with
        | some initialCatalog =>
          if reference.readsInitial then
            Traced.map (fun ((position, source) : Nat × ScopeSource) =>
              (SourceItem.initialTable position, { source with initial := true }))
              ((resolveTableReferenceTraced initialCatalog path reference index .initialTable).mapError
                (initialIssue reference))
          else throw (.value (.restriction path .initialDatabase))
        | none => throw (.value (.restriction path .initialDatabase))
      | none, none => do
        let (position, source) ← resolveTableReferenceTraced catalog path reference index
        pure (SourceItem.table position, source)
      | none, some arguments =>
        if (catalog.findView reference.table).isSome then throw (.value (.prepare (.view (.functionCall reference.table))))
        else if (bytes! "pragma_").isPrefixOf reference.table.folded then do
          let (rows, source) ← Traced.lift ((pragmaReference catalog path reference arguments).mapError .value)
          pure (SourceItem.pragma rows, source)
        else do
          let source ← Traced.lift ((eachReference path reference arguments).mapError .value)
          pure (SourceItem.each path arguments, source) : Traced SourceIssue (SourceItem × ScopeSource))
    Traced.recordAll (reference.alias.toList.map (aliasOccurrence path))
    pure resolved)

/-- The item and the source in scope of the reference at {lit}`path`: {name}`resolveReferenceTraced`
without its trace. -/
def resolveReference (catalog : Catalog) (path : List Nat) (reference : Syntax.TableReference)
    (queries : Nat → Except SourceIssue ScopeSource := fun _ => .error (.value (.restriction [] .subqueryHere)))
    (prefix_ : List Nat := []) (initial : Option Catalog := none) : Except SourceIssue (SourceItem × ScopeSource) :=
  (resolveReferenceTraced catalog path reference queries prefix_ initial).drop

/-- For every position of the source in its {lit}`FROM`: the position changes only the trace of a table
reference, not its result. Proof sketch: the position appears only in the records of the table. -/
@[traced_drop] theorem drop_resolveReferenceTraced (catalog : Catalog) (path : List Nat)
    (reference : Syntax.TableReference)
    (queries : Nat → Except SourceIssue ScopeSource) (prefix_ : List Nat) (initial : Option Catalog) (index : Nat) :
    (resolveReferenceTraced catalog path reference queries prefix_ initial index).drop =
      resolveReference catalog path reference queries prefix_ initial := by
  unfold resolveReference resolveReferenceTraced
  repeat' split
  all_goals simp [traced_drop, drop_resolveTableReferenceTraced_index]

end Belay.Sqlite.Model
