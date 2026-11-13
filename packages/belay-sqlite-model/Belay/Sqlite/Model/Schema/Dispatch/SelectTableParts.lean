import Belay.Sqlite.Model.Schema.Dispatch.SelectColumnResolution
import Belay.Sqlite.Model.Queries.Select.SimpleSelectResolution
import Belay.Sqlite.Model.Queries.Select.ExprResolutionLaws

set_option doc.verso true

/-! The query of a {lit}`SELECT` of one table, as a computation on a catalog. Its resolution depends on the
catalog only, so a check can compute it once on the catalog of a schema, and {lit}`readParts_resolves`
gives the resolution of the statement on every resolution state with that catalog. -/

namespace Belay.Sqlite.Model

/-- The resolved condition of an optional {lit}`WHERE` term in a scope, as {name}`FilterResolves` takes
it: {lit}`some none` without a term, {lit}`some (some condition)` for a term that names no alias and
resolves, and none otherwise. -/
def filterCondition (context : ResolveContext) (scope : Scope) (aliases : List Identifier) :
    Option Syntax.Expr → Option (Option Resolved.Expr)
  | none => some none
  | some term =>
    if namesAlias scope aliases term then none else
      match resolveOperand context.profile.dqsDml scope { later := [] } true term with
      | .ok (condition, _) => some (some condition)
      | .error _ => none

/-- For every scope, alias list, optional term and condition that {name}`filterCondition` gives, the term
resolves to the condition as {name}`FilterResolves` says. Proof sketch: the two cases of the term. -/
theorem filterCondition_resolves {context : ResolveContext} {scope : Scope} {aliases : List Identifier}
    {filter : Option Syntax.Expr}
    {condition : Option Resolved.Expr} (found : filterCondition context scope aliases filter = some condition) :
    FilterResolves context.profile.dqsDml scope aliases filter condition := by
  cases filter with
  | none =>
    cases found
    exact FilterResolves.of_none _ _ _ _
  | some term =>
    simp only [filterCondition] at found
    split at found
    · cases found
    · rename_i noAlias
      split at found
      · rename_i resolvedCondition affinity resolved
        cases found
        exact FilterResolves.of_term (result := (resolvedCondition, affinity)) (Bool.eq_false_iff.mpr noAlias) resolved
      · cases found

/-- Whether no fallible call of the resolved result columns reads an aggregate value, as
{name}`resolveStatement_select_table` requires. -/
def noFeed (resolved : List (List (Resolved.Output × String × Option Affinity))) : Bool :=
  !(resolved.flatten.filterMap fun (output, _) => match output with
    | .scalar expression => some expression
    | .aggregate _ => none).any (fun expression =>
      expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _))

/-- The query of a {lit}`SELECT` of one table on a catalog, from its result columns, its table and its
filter: the catalog position of the table, the resolved filter and the resolved result columns. None when
the table has a schema name, a subquery or table arguments, when a result column calls an aggregate, or
when the table, the columns or the filter do not resolve. -/
def tableReadParts (context : ResolveContext) (catalog : Catalog) (columns : List Syntax.ResultColumn)
    (reference : Syntax.TableReference)
    (filter : Option Syntax.Expr) : Option (Nat × Option Resolved.Expr × List Resolved.Output) :=
    if reference.query.isNone && reference.schema.isNone && reference.arguments.isNone &&
        columns.all (fun
          | .expression value _ _ => value.aggregateCalls.isEmpty
          | .star | .sourceStar _ => true) then
      match catalog.findTable reference.table with
      | none => none
      | some (position, table) =>
        let scope := tableScope catalog reference position table
        if (starIssue scope columns).isNone then
          match resolveAll (resolveResultColumn context.profile.dqsDml scope { later := [] }) columns with
          | .ok resolved =>
            if noFeed resolved then
              (filterCondition context scope ((resultAliases scope columns).filterMap id) filter).map
                fun condition => (position, condition, resolved.flatten.map (·.1))
            else none
          | .error _ => none
        else none
    else none

/-- The query of a one-table read on a catalog ({name}`tableReadParts`), for a {lit}`SELECT` of one table
without a join, grouping, ordering, a limit, a subquery, {lit}`HAVING`, {lit}`DISTINCT` or a compound. None
for every other statement. -/
def readParts (context : ResolveContext) (catalog : Catalog) :
    Syntax.Statement → Option (Nat × Option Resolved.Expr × List Resolved.Output)
  | .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound =>
    match source, joins, groupBy, orderBy, limit, offset, subqueries, having, distinct, compound with
    | some reference, [], [], [], none, none, [], none, false, none =>
      tableReadParts context catalog columns reference filter
    | _, _, _, _, _, _, _, _, _, _ => none
  | .createView .. | .createTable .. | .createIndex .. | .addColumn .. | .renameTable .. | .renameColumn ..
  | .dropColumn .. | .dropTable .. | .dropView .. | .dropIndex .. | .begin | .commit | .rollback | .insert ..
  | .insertSelect .. | .update .. | .delete .. | .pragma .. | .createTrigger .. | .dropTrigger .. => none

/-- For every resolution state and statement for which {name}`readParts` gives a query on the catalog of
the state, the statement resolves to the simple query of the table at that position with that filter and
those result columns, with some result names, no subquery and the state unchanged. Proof sketch: the
premises of {name}`resolveStatement_select_table` are the conditions that {name}`readParts` checks. -/
theorem readParts_resolves {context : ResolveContext} {state : ResolveState} {statement : Syntax.Statement}
    {position : Nat}
    {filter : Option Resolved.Expr} {columns : List Resolved.Output}
    (parts : readParts context state.catalog statement = some (position, filter, columns)) :
    ∃ names, resolveStatement context state statement = .ok (.query
      (Resolved.Query.simple [Resolved.QuerySource.first position] filter columns names) [], state) := by
  cases statement with
  | select resultColumns source joins written groupBy orderBy limit offset subqueries having distinct compound =>
  simp only [readParts] at parts
  split at parts
  · rename_i reference
    unfold tableReadParts at parts
    split at parts
    · rename_i shapeChecks
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at shapeChecks
      obtain ⟨⟨⟨noQuery, noSchema⟩, noArguments⟩, noAggregate⟩ := shapeChecks
      split at parts
      · cases parts
      · rename_i found_position table found
        dsimp only at parts
        split at parts
        · rename_i noStar
          split at parts
          · rename_i resolved columnsOk
            split at parts
            · rename_i fed
              cases condition : filterCondition context (tableScope state.catalog reference found_position table)
                  ((resultAliases (tableScope state.catalog reference found_position table) resultColumns).filterMap id)
                  written with
              | none => simp [condition] at parts
              | some resolvedFilter =>
                simp only [condition, Option.map_some, Option.some.injEq, Prod.mk.injEq] at parts
                obtain ⟨rfl, rfl, rfl⟩ := parts
                refine ⟨_, resolveStatement_select_table context state reference written found_position table
                  resolvedFilter resultColumns resolved noQuery noSchema noArguments found noAggregate
                  (Option.isNone_iff_eq_none.mp noStar) columnsOk (filterCondition_resolves condition) ?_⟩
                revert fed; unfold noFeed; cases (List.filterMap _ resolved.flatten).any _ <;> simp
            · cases parts
          · cases parts
        · cases parts
    · cases parts
  · cases parts
  | _ => simp [readParts] at parts

end Belay.Sqlite.Model
