import Belay.Sqlite.Model.NormalizedFieldQueries
import Belay.Sqlite.Model.NormalizedFieldResolution
import Belay.Sqlite.Model.SimpleStatementResolution
import Belay.Sqlite.Model.Resolution.ResultColumnArms

set_option doc.verso true

/-! Resolution of the two lookups that a lowercase-field expansion relates, in the scope of
one physical table: {lit}`SELECT id FROM t WHERE lower(source) = lower(?n)` and
{lit}`SELECT id FROM t WHERE stored = lower(?n)`. Each resolves to the simple query of the table
at its catalog position with the filters of {lit}`originalFilter` and {lit}`storedFilter`. -/

namespace Belay.Sqlite.Model.NormalizedField
open Resolved

/-- Appending an item that the test rejects to a list without a match leaves it without a match.
Proof sketch: induction on the list; the head is rejected, as is the appended item. -/
theorem findPosition_append_rejected {α : Type} {test : α → Bool} {items : List α} {item : α}
    (absent : findPosition test items = none) (rejected : test item = false) :
    findPosition test (items ++ [item]) = none := by
  induction items with
  | nil => simp [findPosition, rejected]
  | cons head rest ih =>
    by_cases hit : test head = true
    · simp [findPosition, hit] at absent
    · have restAbsent : findPosition test rest = none := by simpa [findPosition, hit] using absent
      simpa [findPosition, hit] using ih restAbsent

/-- Creating a trigger leaves the table lookup of every name as it was: triggers are not in the
namespace of tables and indexes, and the new trigger is appended after every other object.
Proof sketch: the search finds the same first match in the old prefix, or none in it and none
at the appended trigger. -/
theorem findTable_createTrigger (catalog : Catalog) (name triggerName : Identifier) (trigger : CatalogTrigger) :
    (catalog.createTrigger triggerName trigger).findTable name = catalog.findTable name := by
  unfold Catalog.findTable Catalog.find Catalog.createTrigger
  cases located : findPosition (fun object => object.name.sameName name && !object.isTrigger) catalog with
  | some pair => rw [findPosition_append _ located]
  | none =>
    rw [findPosition_append_rejected located (by simp [CatalogObject.isTrigger, CatalogEntry.isTrigger])]

/-- A found identifier as the only result column of a table read from the catalog resolves to its
column position. Its output name and affinity are whatever the resolver gives. Proof sketch: unfold
the result-column resolver for an expression that is a name, then apply the single-source name law. -/
theorem resolveColumns_identifier_at (dqs : Bool) (shapes : SubqueryShapes) (position : Option Nat)
    (tableName : Identifier) (columns : List CatalogColumn) (rowid aliased : Bool) {id : Identifier}
    (quote : Syntax.QuoteKind) {idPosition : Nat} (found : columnPosition columns id = some idPosition)
    (alias : Option Identifier) (text : String) :
    ∃ (name : String) (affinity : Option Affinity),
      resolveAll (resolveResultColumn dqs (Scope.singleAt position tableName columns rowid aliased) shapes)
        [.expression (.identifier id quote) alias text] = .ok [[(.scalar (.column idPosition), name, affinity)]] := by
  simp [resolveAll, resolveAllFrom, resolveResultColumn_expression, resolveOperand_identifier_singleAt found, Bind.bind,
    Except.bind, Pure.pure, Except.pure, Except.mapError]

/-- A found identifier as the only result column resolves to its column position. Its output
name and affinity are whatever the resolver gives. Proof sketch: this is
{name}`resolveColumns_identifier_at` for a table that has no catalog position. -/
theorem resolveColumns_identifier (dqs : Bool) (shapes : SubqueryShapes) (tableName : Identifier)
    (columns : List CatalogColumn) (rowid : Bool) {id : Identifier} (quote : Syntax.QuoteKind) {idPosition : Nat}
    (found : columnPosition columns id = some idPosition) (alias : Option Identifier) (text : String) :
    ∃ (name : String) (affinity : Option Affinity),
      resolveAll (resolveResultColumn dqs (Scope.single tableName columns rowid) shapes)
        [.expression (.identifier id quote) alias text] = .ok [[(.scalar (.column idPosition), name, affinity)]] :=
  resolveColumns_identifier_at dqs shapes none tableName columns rowid false quote found alias text

/-- Lowercase of a parameter resolves to the lowercase expression of that parameter, without
comparison affinity. Proof sketch: resolve the one argument, then reduce the known call. -/
theorem resolve_lower_parameter {dqs : Bool} (scope : Scope) (number : Nat) :
    resolveOperand dqs scope {} true (.call "lower" [.parameter number]) =
      .ok (.scalar .lower (.cons (.parameter number) .nil), none) := by
  rw [resolveOperand_arm_call, resolveArguments_arm_cons, resolveArguments_arm_nil, resolveOperand_parameter]
  rfl

/-- In the scope of one table read from the catalog, the written filter {lit}`lower(source) = lower(?n)` resolves to
{name}`originalFilter` of the source column position and the parameter number, for a source
name that the table has. Proof sketch: the comparison law resolves both operands; function
results carry neither affinity nor collation, so the default BINARY collation applies. -/
theorem resolve_original_filter_at {dqs : Bool} {position : Option Nat} {tableName source : Identifier} {columns : List CatalogColumn}
    {rowid aliased : Bool} {sourcePosition : Nat}
    (found : columnPosition columns source = some sourcePosition) (number : Nat) :
    resolveOperand dqs (Scope.singleAt position tableName columns rowid aliased) {} true
      (.compare .eq (.call "lower" [.identifier source .none]) (.call "lower" [.parameter number])) =
      .ok (originalFilter sourcePosition number, none) := by
  rw [resolveOperand_compare _ _ (by decide) (by decide)]
  simp only [resolve_lower_column_at found, resolve_lower_parameter, Except.mapError, bind, Except.bind]
  simp [comparisonAffinity, comparisonCollation, Syntax.Expr.explicitCollation, Syntax.Expr.firstExplicitCollation,
    Syntax.Expr.columnCollation, originalFilter]

/-- In the scope of one table, the written filter {lit}`lower(source) = lower(?n)` resolves to
{name}`originalFilter` of the source column position and the parameter number, for a source
name that the table has. Proof sketch: this is {name}`resolve_original_filter_at` for a table that
has no catalog position. -/
theorem resolve_original_filter {dqs : Bool} {tableName source : Identifier} {columns : List CatalogColumn}
    {rowid : Bool} {sourcePosition : Nat}
    (found : columnPosition columns source = some sourcePosition) (number : Nat) :
    resolveOperand dqs (Scope.single tableName columns rowid) {} true
      (.compare .eq (.call "lower" [.identifier source .none]) (.call "lower" [.parameter number])) =
      .ok (originalFilter sourcePosition number, none) :=
  resolve_original_filter_at (position := none) found number

/-- In the scope of one table read from the catalog, the written filter {lit}`stored = lower(?n)` resolves to
{name}`storedFilter` of the stored column position and the parameter number, when that column
has TEXT affinity and BINARY collation. Proof sketch: the comparison law resolves the column
with its TEXT affinity and the call without one, and TEXT affinity is the comparison affinity. -/
theorem resolve_stored_filter_at {dqs : Bool} {position : Option Nat} {tableName stored : Identifier} {columns : List CatalogColumn}
    {rowid aliased : Bool} {storedPosition : Nat}
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

/-- In the scope of one table, the written filter {lit}`stored = lower(?n)` resolves to
{name}`storedFilter` of the stored column position and the parameter number, when that column
has TEXT affinity and BINARY collation. Proof sketch: this is {name}`resolve_stored_filter_at` for
a table that has no catalog position. -/
theorem resolve_stored_filter {dqs : Bool} {tableName stored : Identifier} {columns : List CatalogColumn}
    {rowid : Bool} {storedPosition : Nat}
    (found : columnPosition columns stored = some storedPosition)
    (text : columns[storedPosition]?.map CatalogColumn.affinity = some .text)
    (binary : columns[storedPosition]?.map (·.collation) = some .binary) (number : Nat) :
    resolveOperand dqs (Scope.single tableName columns rowid) {} true
      (.compare .eq (.identifier stored .none) (.call "lower" [.parameter number])) =
      .ok (storedFilter storedPosition number, none) :=
  resolve_stored_filter_at (position := none) found text binary number

end Belay.Sqlite.Model.NormalizedField
