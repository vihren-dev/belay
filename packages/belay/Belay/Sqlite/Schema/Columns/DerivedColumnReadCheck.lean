import Belay.Sqlite.Schema.Columns.DerivedColumnSiteCheck
import Belay.Sqlite.Schema.Columns.DerivedColumnReads

set_option doc.verso true

/-! A computed check of a read that the derived-column migration keeps ({lit}`Site.ReadPreserved`). The
read is a one-table {lit}`SELECT` without a join, a subquery, grouping, ordering or a limit. Its
resolution depends on the catalog only, so the check resolves it once on the catalog before the
migration and once on the catalog after it, and requires the same query. -/

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- Whether a resolved expression is calm by its form: it has no fallible call, no read of the clock and
no call of a counter function ({name}`Resolved.Expr.Calm` as a computation). -/
def calmCheck (expression : Resolved.Expr) : Bool :=
  !expression.any Resolved.Expr.isFallibleCall && !expression.any Resolved.Expr.readsClockHere &&
    !expression.any Resolved.Expr.isCounter

/-- For every expression that passes {name}`calmCheck`, the expression is calm. Proof sketch: a node that
calls a counter function of some kind is a counter node ({name}`Resolved.Expr.any_mono`). -/
theorem calm_of_calmCheck {expression : Resolved.Expr} (checked : calmCheck expression = true) :
    expression.Calm := by
  simp only [calmCheck, Bool.and_eq_true, Bool.not_eq_true'] at checked
  refine ⟨checked.1.1, checked.1.2, fun kind => ?_⟩
  cases found : expression.any (Resolved.Expr.readsCounterHere kind)
  · rfl
  · have counter := Resolved.Expr.any_mono _ Resolved.Expr.isCounter (fun node hit => by
      cases node <;> simp_all [Resolved.Expr.readsCounterHere, Resolved.Expr.isCounter]) expression found
    rw [checked.2] at counter
    cases counter

/-- The resolved condition of an optional {lit}`WHERE` term in a scope, as {name}`FilterResolves` takes
it: {lit}`some none` without a term, {lit}`some (some condition)` for a term that names no alias and
resolves, and none otherwise. -/
def filterCondition (scope : Scope) (aliases : List Identifier) : Option Syntax.Expr → Option (Option Resolved.Expr)
  | none => some none
  | some term =>
    if namesAlias scope aliases term then none else
      match resolveOperand runContext.profile.dqsDml scope { later := [] } true term with
      | .ok (condition, _) => some (some condition)
      | .error _ => none

/-- For every scope, alias list, optional term and condition that {name}`filterCondition` gives, the term
resolves to the condition as {name}`FilterResolves` says. Proof sketch: the two cases of the term. -/
theorem filterCondition_resolves {scope : Scope} {aliases : List Identifier} {filter : Option Syntax.Expr}
    {condition : Option Resolved.Expr} (found : filterCondition scope aliases filter = some condition) :
    FilterResolves runContext.profile.dqsDml scope aliases filter condition := by
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

/-- The query of a one-table read on a catalog: the catalog position of the table, the resolved filter
and the resolved result columns. None when the statement is not a {lit}`SELECT` of one named table without
a join, a schema name, table arguments, grouping, ordering, a limit, a window or {lit}`DISTINCT`, when a
result column calls an aggregate, or when the columns or the filter do not resolve. -/
def readParts (catalog : Catalog) : Syntax.Statement → Option (Nat × Option Resolved.Expr × List Resolved.Output)
  | .select columns (some reference) [] filter [] [] none none [] none false none =>
    if reference.query.isNone && reference.schema.isNone && reference.arguments.isNone &&
        columns.all (fun
          | .expression value _ _ => value.aggregateCalls.isEmpty
          | .star | .sourceStar _ => true) then
      match catalog.findTable reference.table with
      | none => none
      | some (position, table) =>
        let scope := tableScope catalog reference position table
        if (starIssue scope columns).isNone then
          match resolveAll (resolveResultColumn runContext.profile.dqsDml scope { later := [] }) columns with
          | .ok resolved =>
            if noFeed resolved then
              (filterCondition scope ((resultAliases scope columns).filterMap id) filter).map
                fun condition => (position, condition, resolved.flatten.map (·.1))
            else none
          | .error _ => none
        else none
    else none
  | _ => none

/-- For every resolution state and statement for which {name}`readParts` gives a query on the catalog of
the state, the statement resolves to the simple query of the table at that position with that filter and
those result columns, with some result names, no subquery and the state unchanged. Proof sketch: the
premises of {name}`resolveStatement_select_table` are the conditions that {name}`readParts` checks. -/
theorem readParts_resolves {state : ResolveState} {statement : Syntax.Statement} {position : Nat}
    {filter : Option Resolved.Expr} {columns : List Resolved.Output}
    (parts : readParts state.catalog statement = some (position, filter, columns)) :
    ∃ names, resolveStatement runContext state statement = .ok (.query
      (Resolved.Query.simple [Resolved.QuerySource.first position] filter columns names) [], state) := by
  unfold readParts at parts
  split at parts
  · rename_i resultColumns reference written
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
              cases condition : filterCondition (tableScope state.catalog reference found_position table)
                  ((resultAliases (tableScope state.catalog reference found_position table) resultColumns).filterMap id)
                  written with
              | none => simp [condition] at parts
              | some resolvedFilter =>
                simp only [condition, Option.map_some, Option.some.injEq, Prod.mk.injEq] at parts
                obtain ⟨rfl, rfl, rfl⟩ := parts
                refine ⟨_, resolveStatement_select_table runContext state reference written found_position table
                  resolvedFilter resultColumns resolved noQuery noSchema noArguments found noAggregate
                  (Option.isNone_iff_eq_none.mp noStar) columnsOk (filterCondition_resolves condition) ?_⟩
                revert fed; unfold noFeed; cases (List.filterMap _ resolved.flatten).any _ <;> simp
            · cases parts
          · cases parts
        · cases parts
    · cases parts
  · cases parts

/-- Whether the read is a query of the table at the position that the migration keeps: {name}`readParts`
gives the same query, at the position, on the catalog before the migration and on the catalog with the
column added; the filter and the result columns read only the old columns; and every expression of them
passes {name}`calmCheck`. For example, {lit}`SELECT id FROM customers WHERE email = ?1` passes, and
{lit}`SELECT * FROM customers` fails, because after the migration its result columns include the new
column. -/
def readCheck (catalog : Catalog) (position width : Nat) (column : CatalogColumn) (statement : Syntax.Statement) :
    Bool :=
  match readParts catalog statement, readParts (catalog.addColumn position column) statement with
  | some (before, filter, columns), some (after, filterAfter, columnsAfter) =>
    before == position && after == position && filter == filterAfter && columns == columnsAfter &&
      filter.all (·.readsBelow width) && columns.all (·.readsBelow width) &&
      filter.all calmCheck && (columns.flatMap Resolved.Output.scalars).all calmCheck
  | _, _ => false

/-- For every site of the migration without triggers, the catalog of the database that it reaches is the
catalog of the database with the column of the site added. Proof sketch: the definitions. -/
theorem Site.reached_nil_catalog {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} (site : Site database tableName definition value) :
    (site.reached []).catalog = database.catalog.addColumn site.position site.column :=
  rfl

/-- The {name}`Site.ReadPreserved` of a read at a site of the migration without triggers, when the read
passes {name}`readCheck` on the catalog of the database. -/
def Site.ReadPreserved.ofCheck {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} (site : Site database tableName definition value)
    {statement : Syntax.Statement}
    (checked : readCheck database.catalog site.position site.table.shape.columns.length site.column statement = true) :
    site.ReadPreserved [] statement :=
  match before : readParts database.catalog statement,
      after : readParts (database.catalog.addColumn site.position site.column) statement, checked with
  | some (beforePosition, filter, columns), some (afterPosition, filterAfter, columnsAfter), checked => by
    simp only [readCheck, before, after, Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨⟨⟨⟨⟨⟨⟨atBefore, atAfter⟩, sameFilter⟩, sameColumns⟩, filterBelow⟩, columnsBelow⟩, filterCalm⟩,
      columnsCalm⟩ := checked
    subst atBefore atAfter sameFilter sameColumns
    refine ⟨filter, columns, ?_, List.all_eq_true.mp columnsBelow, ?_, ?_, ?_⟩
    · intro condition member
      simp only [Option.mem_def] at member
      subst member
      simpa using filterBelow
    · intro state same
      obtain ⟨names, resolves⟩ := readParts_resolves (state := state) (same ▸ before)
      exact ⟨names, state, resolves⟩
    · intro state same
      rw [Site.reached_nil_catalog] at same
      obtain ⟨names, resolves⟩ := readParts_resolves (state := state) (same ▸ after)
      exact ⟨names, state, resolves⟩
    · exact fun names => Resolved.Statement.simpleTable_calm _ filter columns names
        (by
          intro expression member
          simp only [List.mem_append] at member
          rcases member with member | member
          · cases filter with
            | none => cases member
            | some condition =>
              simp only [Option.toList_some, List.mem_singleton] at member
              subst member
              exact calm_of_calmCheck (by simpa using filterCalm)
          · exact calm_of_calmCheck (List.all_eq_true.mp columnsCalm expression member))
        (fun output member => Resolved.Output.operands_of_readsBelow (List.all_eq_true.mp columnsBelow output member))
  | none, _, checked => absurd checked (by simp [readCheck, before])
  | some _, none, checked => absurd checked (by simp [readCheck, before, after])

end Belay.Sqlite.DerivedColumnMigration
