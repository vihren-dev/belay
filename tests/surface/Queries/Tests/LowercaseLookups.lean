import LowercaseFilters

set_option doc.verso true

/-! The guide's two lookup statements as written syntax, and their resolution (ADR 0017, S6). The
lookup {lit}`SELECT id FROM t WHERE lower(source) = lower(?n)` and the lookup {lit}`SELECT id FROM t WHERE
stored = lower(?n)` resolve to simple queries of the table with the filters of {lit}`LowercaseFilters`. The
general resolution law {name}`Belay.Sqlite.Model.resolveStatement_select_column` does the work for the
statement. This module proves only what is particular to {lit}`lower`: the resolution of its filters. -/

namespace LowercaseFixture
open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- In the scope of one table read from the catalog, lowercase of a found column resolves to that column's
lowercase expression with no comparison affinity. The result is the same whether the table has an alias
({lit}`aliased`), because the flag only tells a name trace whether the table was written with an alias.
Proof sketch: resolve the one argument with the column lookup law, then reduce the known call. -/
theorem resolve_lower_column_at {dqs : Bool} {position : Option Nat} {tableName name : Identifier}
    {columns : List CatalogColumn} {rowid aliased : Bool} {source : Nat}
    (found : columnPosition columns name = some source) :
    resolveOperand dqs (Scope.singleAt position tableName columns rowid aliased) {} true
      (.call "lower" [.identifier name .none]) =
      .ok (.scalar .lower (.cons (.column source) .nil), none) := by
  rw [resolveOperand_arm_call, resolveArguments_arm_cons, resolveArguments_arm_nil,
    resolveOperand_identifier_singleAt found]
  rfl

/-- Lowercase of a parameter resolves to the lowercase expression of that parameter, without comparison
affinity. Proof sketch: resolve the one argument, then reduce the known call. -/
theorem resolve_lower_parameter {dqs : Bool} (scope : Scope) (number : Nat) :
    resolveOperand dqs scope {} true (.call "lower" [.parameter number]) =
      .ok (.scalar .lower (.cons (.parameter number) .nil), none) := by
  rw [resolveOperand_arm_call, resolveArguments_arm_cons, resolveArguments_arm_nil, resolveOperand_parameter]
  rfl

/-- In the scope of one table read from the catalog, the written filter {lit}`lower(source) = lower(?n)`
resolves to {name}`originalFilter` of the source column position and the parameter number, for a source
name that the table has. Proof sketch: the comparison law resolves both operands; function results carry
neither affinity nor collation, so the default BINARY collation applies. -/
theorem resolve_original_filter_at {dqs : Bool} {position : Option Nat} {tableName source : Identifier}
    {columns : List CatalogColumn} {rowid aliased : Bool} {sourcePosition : Nat}
    (found : columnPosition columns source = some sourcePosition) (number : Nat) :
    resolveOperand dqs (Scope.singleAt position tableName columns rowid aliased) {} true
      (.compare .eq (.call "lower" [.identifier source .none]) (.call "lower" [.parameter number])) =
      .ok (originalFilter sourcePosition number, none) := by
  rw [resolveOperand_compare _ _ (by decide) (by decide)]
  simp only [resolve_lower_column_at found, resolve_lower_parameter, Except.mapError, bind, Except.bind]
  simp [comparisonAffinity, comparisonCollation, Syntax.Expr.explicitCollation, Syntax.Expr.firstExplicitCollation,
    Syntax.Expr.columnCollation, originalFilter]

/-- In the scope of one table read from the catalog, the written filter {lit}`stored = lower(?n)` resolves
to {name}`storedFilter` of the stored column position and the parameter number, when that column has TEXT
affinity and BINARY collation. Proof sketch: the comparison law resolves the column with its TEXT affinity
and the call without one, and TEXT affinity is the comparison affinity. -/
theorem resolve_stored_filter_at {dqs : Bool} {position : Option Nat} {tableName stored : Identifier}
    {columns : List CatalogColumn} {rowid aliased : Bool} {storedPosition : Nat}
    (found : columnPosition columns stored = some storedPosition)
    (text : columns[storedPosition]?.map CatalogColumn.affinity = some .text)
    (binary : columns[storedPosition]?.map (·.collation) = some .binary) (number : Nat) :
    resolveOperand dqs (Scope.singleAt position tableName columns rowid aliased) {} true
      (.compare .eq (.identifier stored .none) (.call "lower" [.parameter number])) =
      .ok (storedFilter storedPosition number, none) := by
  have resolved : (Scope.singleAt position tableName columns rowid aliased).resolveName stored =
      .found storedPosition [storedPosition] := resolveName_one_source_at found
  rw [resolveOperand_compare _ _ (by decide) (by decide)]
  simp only [resolveOperand_identifier_singleAt found, resolve_lower_parameter, text, Except.mapError, bind,
    Except.bind]
  simp [comparisonAffinity, comparisonCollation, Syntax.Expr.explicitCollation, Syntax.Expr.firstExplicitCollation,
    Syntax.Expr.columnCollation, resolved, Scope.columns_singleAt, binary, storedFilter]

/-- The lookup {lit}`SELECT id FROM t WHERE lower(source) = lower(?n)` as syntax: the table reference, the
written name of the returned column, its result text, the compared column and the one-based parameter
number. -/
def originalLookup (reference : Syntax.TableReference) (idName sourceName : Identifier) (text : String)
    (number : Nat) : Syntax.Statement :=
  .select [.expression (.identifier idName .none) none text] (some reference) []
    (some (.compare .eq (.call "lower" [.identifier sourceName .none]) (.call "lower" [.parameter number])))
    [] [] none none [] none false none

/-- The lookup {lit}`SELECT id FROM t WHERE stored = lower(?n)` as syntax, over the stored lowercase column. -/
def storedLookup (reference : Syntax.TableReference) (idName storedName : Identifier) (text : String)
    (number : Nat) : Syntax.Statement :=
  .select [.expression (.identifier idName .none) none text] (some reference) []
    (some (.compare .eq (.identifier storedName .none) (.call "lower" [.parameter number])))
    [] [] none none [] none false none

/-- For a table that has the id column and the source column, the original lookup resolves to the simple
query of the table with {name}`originalFilter` and the id column. The table reference names no schema,
query or arguments. Proof sketch: {name}`Belay.Sqlite.Model.resolveStatement_select_column` with
{name}`resolve_original_filter_at`; no result alias exists to be named by the filter. -/
theorem resolve_original_lookup (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (position : Nat) (table : CatalogTable)
    (idName sourceName : Identifier) (text : String) (number : Nat) {idPosition sourcePosition : Nat}
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : state.catalog.findTable reference.table = some (position, table))
    (idFound : columnPosition table.columns idName = some idPosition)
    (sourceFound : columnPosition table.columns sourceName = some sourcePosition) :
    ∃ names, resolveStatement context state (originalLookup reference idName sourceName text number) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.first position]
        (some (originalFilter sourcePosition number)) [.scalar (.column idPosition)] names) [], state) :=
  resolveStatement_select_column context state reference _ position table _ idName text namedSource current arguments
    found idFound (FilterResolves.of_term (result := (originalFilter sourcePosition number, none))
      (by simp [namesAlias, namesAliasIn]) (resolve_original_filter_at sourceFound number))

/-- For a table whose stored column has TEXT affinity and BINARY collation, the stored lookup resolves to
the simple query of the table with {name}`storedFilter` and the id column. Proof sketch: as
{name}`resolve_original_lookup`, with {name}`resolve_stored_filter_at`. -/
theorem resolve_stored_lookup (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (position : Nat) (table : CatalogTable)
    (idName storedName : Identifier) (text : String) (number : Nat) {idPosition storedPosition : Nat}
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : state.catalog.findTable reference.table = some (position, table))
    (idFound : columnPosition table.columns idName = some idPosition)
    (storedFound : columnPosition table.columns storedName = some storedPosition)
    (stored : table.columns[storedPosition]?.map CatalogColumn.affinity = some .text)
    (binary : table.columns[storedPosition]?.map (·.collation) = some .binary) :
    ∃ names, resolveStatement context state (storedLookup reference idName storedName text number) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.first position]
        (some (storedFilter storedPosition number)) [.scalar (.column idPosition)] names) [], state) :=
  resolveStatement_select_column context state reference _ position table _ idName text namedSource current arguments
    found idFound (FilterResolves.of_term (result := (storedFilter storedPosition number, none))
      (by simp [namesAlias, namesAliasIn]) (resolve_stored_filter_at storedFound stored binary number))

/-- The original lowercase predicate is calm: it has no fallible call, clock read or counter call. Proof
sketch: unfold the comparison and the two lowercase calls; lowercase cannot fail. -/
theorem originalFilter_calm (source number : Nat) : (originalFilter source number).Calm := by
  simp [originalFilter, Expr.Calm, Expr.any, Arguments.any, Expr.isFallibleCall, Expr.readsClockHere,
    Expr.readsCounterHere, ScalarFunction.canFail]

/-- The stored lowercase predicate is calm. Proof sketch: as {name}`originalFilter_calm`. -/
theorem storedFilter_calm (stored number : Nat) : (storedFilter stored number).Calm := by
  simp [storedFilter, Expr.Calm, Expr.any, Arguments.any, Expr.isFallibleCall, Expr.readsClockHere,
    Expr.readsCounterHere, ScalarFunction.canFail]

/-- For every calm condition, the statement of the simple query of one table position returning one column
is calm. Proof sketch: {name}`Belay.Sqlite.Model.Resolved.Statement.simpleTable_calm` with the one scalar
result column, which is calm. -/
theorem simpleColumn_calm (position idPosition : Nat) (condition : Resolved.Expr) (names : List String)
    (calm : condition.Calm) :
    (Resolved.Statement.query (Resolved.Query.simple [Resolved.QuerySource.first position] (some condition)
      [.scalar (.column idPosition)] names) []).Calm := by
  apply Resolved.Statement.simpleTable_calm
  · intro expression member
    simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
      List.mem_singleton, Resolved.Output.scalars] at member
    rcases member with rfl | rfl
    · exact calm
    · exact Expr.calm_column idPosition
  · intro column member
    cases List.mem_singleton.mp member
    rfl

end LowercaseFixture
