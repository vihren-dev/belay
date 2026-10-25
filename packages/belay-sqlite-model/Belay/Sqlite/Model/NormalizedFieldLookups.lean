import Belay.Sqlite.Model.NormalizedFieldSelectResolution
import Belay.Sqlite.Model.SelectOneResolution
import Belay.Sqlite.Model.ExprCalmLaws

set_option doc.verso true

/-! The two lookup statements of a lowercase-field expansion as written syntax, their
resolution to simple table queries, and their calm statements. -/

namespace Belay.Sqlite.Model.NormalizedField
open Resolved

/-- The lookup {lit}`SELECT id FROM t WHERE lower(source) = lower(?n)` as syntax: the table
reference, the written name of the returned column, its result text, the compared column and the
one-based parameter number. -/
def originalLookup (reference : Syntax.TableReference) (idName sourceName : Identifier) (text : String)
    (number : Nat) : Syntax.Statement :=
  .select [.expression (.identifier idName .none) none text] (some reference) []
    (some (.compare .eq (.call "lower" [.identifier sourceName .none]) (.call "lower" [.parameter number])))
    [] [] none none [] none false none

/-- The lookup {lit}`SELECT id FROM t WHERE stored = lower(?n)` as syntax, over the stored
lowercase column. -/
def storedLookup (reference : Syntax.TableReference) (idName storedName : Identifier) (text : String)
    (number : Nat) : Syntax.Statement :=
  .select [.expression (.identifier idName .none) none text] (some reference) []
    (some (.compare .eq (.identifier storedName .none) (.call "lower" [.parameter number])))
    [] [] none none [] none false none

/-- A found column as the only result of a one-table {lit}`SELECT` with a resolving filter
resolves to the simple query of the table at its catalog position, returning that column, with
no subquery and an unchanged state. The output name is whatever the resolver names it. Proof
sketch: {name}`resolveStatement_select_simple` with the table source, the one resolved column of
{name}`resolveColumns_identifier` and the filter. -/
theorem resolveStatement_select_column (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (filter : Option Syntax.Expr) (position : Nat) (table : CatalogTable)
    (condition : Option Resolved.Expr) (idName : Identifier) (text : String) {idPosition : Nat}
    (namedSource : reference.query = none) (arguments : reference.arguments = none)
    (found : state.catalog.findTable reference.table = some (position, table))
    (idFound : columnPosition table.columns idName = some idPosition)
    (resolves : FilterResolves context.profile.dqsDml (tableScope state.catalog reference position table) []
      filter condition) :
    ∃ names, resolveStatement context state (.select [.expression (.identifier idName .none) none text]
        (some reference) [] filter [] [] none none [] none false none) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.first position] condition
        [.scalar (.column idPosition)] names) [], state) := by
  obtain ⟨name, affinity, columns⟩ := resolveColumns_identifier context.profile.dqsDml { later := [] }
    (reference.alias.getD ((state.catalog[position]?.map (·.name)).getD reference.table)) table.columns
    (!table.withoutRowid) .none idFound none text
  have simple : (Syntax.Subquery.mk [.expression (.identifier idName .none) none text] (some reference) [] filter [] []
      none none none none false none none).Simple := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨[name], ?_⟩
  have result := resolveStatement_select_simple context state
    (Syntax.Subquery.mk [.expression (.identifier idName .none) none text] (some reference) [] filter [] [] none none
      none none false none none)
    simple rfl _ _ _ condition _ (resolveSources_table state.catalog reference position table namedSource arguments found)
    (by simp [starIssue]) columns (by simpa [resultAliases] using resolves)
    (resolvePendingSources_table context.profile.dqsDml _ position)
    (by simp [Resolved.Expr.any, Resolved.Expr.isFallibleCall])
  simpa using result

/-- For a table with the stored lowercase source column's name and an id column, the original
lookup resolves to the simple query of the table with {name}`originalFilter` and the id column.
Proof sketch: {name}`resolveStatement_select_column` with {name}`resolve_original_filter`; no
result alias exists to be named by the filter. -/
theorem resolve_original_lookup (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (position : Nat) (table : CatalogTable)
    (idName sourceName : Identifier) (text : String) (number : Nat) {idPosition sourcePosition : Nat}
    (namedSource : reference.query = none) (arguments : reference.arguments = none)
    (found : state.catalog.findTable reference.table = some (position, table))
    (idFound : columnPosition table.columns idName = some idPosition)
    (sourceFound : columnPosition table.columns sourceName = some sourcePosition) :
    ∃ names, resolveStatement context state (originalLookup reference idName sourceName text number) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.first position]
        (some (originalFilter sourcePosition number)) [.scalar (.column idPosition)] names) [], state) :=
  resolveStatement_select_column context state reference _ position table _ idName text namedSource arguments found
    idFound (FilterResolves.of_term (result := (originalFilter sourcePosition number, none))
      (by simp [namesAlias, namesAliasIn]) (resolve_original_filter sourceFound number))

/-- For a table whose stored column has TEXT affinity and BINARY collation, the stored lookup
resolves to the simple query of the table with {name}`storedFilter` and the id column. Proof
sketch: as {name}`resolve_original_lookup`, with {name}`resolve_stored_filter`. -/
theorem resolve_stored_lookup (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (position : Nat) (table : CatalogTable)
    (idName storedName : Identifier) (text : String) (number : Nat) {idPosition storedPosition : Nat}
    (namedSource : reference.query = none) (arguments : reference.arguments = none)
    (found : state.catalog.findTable reference.table = some (position, table))
    (idFound : columnPosition table.columns idName = some idPosition)
    (storedFound : columnPosition table.columns storedName = some storedPosition)
    (stored : table.columns[storedPosition]?.map CatalogColumn.affinity = some .text)
    (binary : table.columns[storedPosition]?.map (·.collation) = some .binary) :
    ∃ names, resolveStatement context state (storedLookup reference idName storedName text number) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.first position]
        (some (storedFilter storedPosition number)) [.scalar (.column idPosition)] names) [], state) :=
  resolveStatement_select_column context state reference _ position table _ idName text namedSource arguments found
    idFound (FilterResolves.of_term (result := (storedFilter storedPosition number, none))
      (by simp [namesAlias, namesAliasIn]) (resolve_stored_filter storedFound stored binary number))

/-- The original lowercase predicate is calm: it has no fallible call, clock read or counter
call. Proof sketch: unfold the comparison and the two lowercase calls; lowercase cannot fail. -/
theorem originalFilter_calm (source number : Nat) : (originalFilter source number).Calm := by
  simp [originalFilter, Expr.Calm, Expr.any, Arguments.any, Expr.isFallibleCall, Expr.readsClockHere,
    Expr.readsCounterHere, ScalarFunction.canFail]

/-- The stored lowercase predicate is calm. Proof sketch: as {name}`originalFilter_calm`. -/
theorem storedFilter_calm (stored number : Nat) : (storedFilter stored number).Calm := by
  simp [storedFilter, Expr.Calm, Expr.any, Arguments.any, Expr.isFallibleCall, Expr.readsClockHere,
    Expr.readsCounterHere, ScalarFunction.canFail]

/-- For every calm condition, the statement of the simple query of one table position returning
one column is calm. Proof sketch: the expressions of the statement are the condition and the
column, and the first source of a table has none. -/
theorem simpleColumn_calm (position idPosition : Nat) (condition : Resolved.Expr)
    (names : List String) (calm : condition.Calm) :
    (Resolved.Statement.query (Resolved.Query.simple [Resolved.QuerySource.first position] (some condition)
      [.scalar (.column idPosition)] names) []).Calm := by
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.expressions, Resolved.Query.keptExpressions,
    Resolved.Query.simple, Resolved.QuerySource.first, Resolved.QuerySource.expressions, List.mem_append,
    List.mem_flatMap, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at member
  simp only [Resolved.Output.scalars, Resolved.Output.operands, List.mem_singleton, List.not_mem_nil,
    exists_eq_left, List.map_nil, or_false, Option.toList_some] at member
  rcases member with member | member
  · rcases member with rfl | absent
    · exact calm
    · simp at absent
  · rcases member with rfl | absent
    · exact Expr.calm_column idPosition
    · simp at absent

end Belay.Sqlite.Model.NormalizedField
