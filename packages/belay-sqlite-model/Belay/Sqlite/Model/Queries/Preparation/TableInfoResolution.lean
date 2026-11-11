import Belay.Sqlite.Model.Queries.Select.SimpleStatementResolution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every name that is the keyword {lit}`pragma_table_info` without ASCII case, the lowercase name starts with
{lit}`pragma_`, which is the test of {name}`resolveReference` for a table-valued pragma. Proof sketch: the lowercase
name is the keyword ({name}`equalsKeyword`), which starts with {lit}`pragma_` by computation. -/
theorem Identifier.pragma_prefix_of_isKeyword (name : Identifier)
    (isFunction : name.isKeyword (bytes! "pragma_table_info") = true) :
    (bytes! "pragma_").isPrefixOf name.folded = true := by
  have folded : name.folded = bytes! "pragma_table_info" := by
    simpa [Identifier.isKeyword, equalsKeyword, Identifier.folded] using isFunction
  rw [folded]
  decide

/-- The scope of the source {lit}`pragma_table_info('t')` with the rows of the table: the eight cells of
{name}`pragmaSource`, the six columns of the pragma and the two hidden cells, under the alias of the reference or
else the name of the function. -/
def tableInfoScope (reference : Syntax.TableReference) (argument : List UInt8) (rows : List (List Value)) : Scope :=
  Scope.place [(pragmaSource reference argument tableInfoNames rows).2] 0

/-- For every catalog, reference to the function {lit}`pragma_table_info` with one text argument, when the catalog has no
table or view with the name of the function and has rows for the table of the argument, a {lit}`FROM` clause of that reference alone
resolves to the one inner pragma source with those rows, and the scope of {name}`tableInfoScope`. The source reference has no indexed query.
The result holds for every derived-source callback and diagnostic prefix; neither is read on this
successful pragma path. Leave both at their defaults for a query without derived sources.
The table reference names no schema: it is not a {lit}`before.t` source. Proof sketch: unfold
{name}`resolveSources` and {name}`pragmaReference`; the reference has arguments and the prefix {lit}`pragma_`, so
{name}`resolveReference` takes the pragma branch, and the scope of one source is placed at offset 0. -/
theorem resolveSources_tableInfo (catalog : Catalog) (reference : Syntax.TableReference) (argument : List UInt8)
    (rows : List (List Value)) (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = some [.string argument])
    (isFunction : reference.table.isKeyword (bytes! "pragma_table_info") = true)
    (notTable : catalog.findTable reference.table = none)
    (notView : catalog.findView reference.table = none)
    (info : catalog.tableInfoRows ⟨argument⟩ = some rows)
    (queries : Nat → Except SourceIssue ScopeSource := fun _ => .error (.value (.restriction [] .subqueryHere)))
    (prefix_ : List Nat := []) :
    resolveSources catalog (some reference) [] 0 queries prefix_ = .ok ([{
        item := .pragma (pragmaSource reference argument tableInfoNames rows).1, kind := .inner, condition := .none }],
      tableInfoScope reference argument rows) := by
  have prefixed := Identifier.pragma_prefix_of_isKeyword _ isFunction
  simp [resolveSources_some, resolveReference, resolveReferenceTraced, namedSource, current, arguments, prefixed, pragmaReference, notTable, notView, isFunction, info,
    maximumJoinTables, mergeJoinsTraced, mergeJoins, resolveAll, resolveAllFrom, Bind.bind, Except.bind, Except.mapError,
    joinOperator, tableInfoScope, Scope.place, traced_drop]

/-- The first source of a query that is a pragma with the rows of the pragma, as an inner join without a condition. -/
def Resolved.QuerySource.pragma (rows : Resolved.PragmaRows) : Resolved.QuerySource :=
  { kind := .inner, source := .pragma rows, condition := none }

/-- The one inner pragma source without a condition, which {name}`resolveSources_tableInfo` gives, resolves to the
source {name}`Resolved.QuerySource.pragma`, for any scope and quote setting. Proof sketch: unfold the resolver and the
join condition check; there is no condition to resolve. -/
theorem resolvePendingSources_pragma (dqs : Bool) (scope : Scope) (rows : Resolved.PragmaRows) :
    resolvePendingSources dqs scope [{ item := .pragma rows, kind := .inner, condition := .none }] =
      .ok [Resolved.QuerySource.pragma rows] := by
  simp [resolvePendingSources_arm, resolveJoinCondition_none, resolveAll, resolveAllFrom, Bind.bind, Except.bind, Pure.pure,
    Except.pure, Resolved.QuerySource.pragma]

end Belay.Sqlite.Model
