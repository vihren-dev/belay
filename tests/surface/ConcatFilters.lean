import LowercaseExpansion

set_option doc.verso true

/-! A derived expression of two columns instead of the lowercase of one (ADR 0017, S6). The migration stores
{lit}`a || b` in a TEXT column, and the lookup {lit}`WHERE a || b = lower(?n)` moves to
{lit}`WHERE stored = lower(?n)`. This module states the two resolved filters, proves that the move keeps
every comparison, and proves how the lookup resolves. The general laws of the model do the rest; only the
facts that are particular to concatenation are proved here: the result is NULL or TEXT, so TEXT affinity
leaves it and the lowercase probe unchanged. -/

namespace ConcatFixture
open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved LowercaseFixture

/-- The value of the concatenation operator {lit}`||` on two values: NULL when either is NULL, and the text
that joins their text forms otherwise. -/
def pipesValue (left right : Value) : Value :=
  if left.isNull || right.isNull then .null else .text (left.textBytes ++ right.textBytes)

/-- The resolved concatenation of the columns at two positions. -/
def pipesCall (first second : Nat) : Expr := .scalar .pipes (.cons (.column first) (.cons (.column second) .nil))

/-- For every context, row and two expressions, the concatenation call returns the value of the operator on the
values of the two expressions. Proof sketch: the call reduces to the definition of the operator. -/
theorem eval_pipes (context : EvalContext) (row : List Value) (left right : Expr) :
    (Expr.scalar .pipes (.cons left (.cons right .nil))).eval context row =
      pipesValue (left.eval context row) (right.eval context row) := rfl

/-- For every two values, TEXT affinity leaves their concatenation unchanged: it is NULL or TEXT. Proof sketch:
case analysis on whether an operand is NULL. -/
theorem store_pipes (left right : Value) : Value.store .text (pipesValue left right) = pipesValue left right := by
  unfold pipesValue
  split <;> rfl

/-- The original predicate {lit}`a || b = lower(?n)` with resolved column positions and parameter number.
The concatenation has no affinity and the lowercase has none, so the comparison has none and BINARY
collation. -/
def pipesFilter (first second parameter : Nat) : Expr :=
  .compare .eq none (pipesCall first second) (.scalar .lower (.cons (.parameter parameter) .nil))

/-- For every context whose subqueries ignore the outer row, row with exactly {lit}`width` cells, two columns
inside the row and parameter position, reading the appended stored cell at position {lit}`width` gives the
value of the predicate that concatenates the two cells. In plain words, the move from
{lit}`a || b = lower(?n)` to {lit}`stored = lower(?n)` changes no comparison, for any parameter value. Proof
sketch: {name}`Expr.eval_compare_stored_left`; its agreement premise holds because TEXT affinity keeps both
operands ({name}`comparisonOperands_text_of_stored`, {name}`store_pipes`, {name}`store_lower`). -/
theorem storedFilter_append_pipes (context : EvalContext) (rowFree : context.RowFree) (row : List Value)
    (width first second parameter : Nat) (wide : row.length = width) :
    (storedFilter width parameter).eval context
        (row ++ [pipesValue (row.getD first .null) (row.getD second .null)]) =
      (pipesFilter first second parameter).eval context row := by
  subst wide
  have general := Expr.eval_compare_stored_left context rowFree row .eq (some .text) none .binary .binary
    (pipesCall first second) (.scalar .lower (.cons (.parameter parameter) .nil))
    (pipesValue (row.getD first .null) (row.getD second .null)) .text rfl
    (by simp [Expr.readsBelow, Expr.any, Expr.isColumnFrom, Arguments.any])
    (by
      simp only [compareValue, store_pipes]
      rw [comparisonOperands_text_of_stored _ _ (store_pipes _ _) (by rw [eval_lower]; exact store_lower _)])
  rw [store_pipes] at general
  exact general

/-- For every column positions of any row, the concatenation predicate keeps its value when cells are appended
to the row, if both columns lie inside the row. Proof sketch: both columns read the same cells
({name}`Expr.eval_append`). -/
theorem pipesFilter_append (context : EvalContext) (rowFree : context.RowFree) (row extra : List Value)
    (first second parameter : Nat) (firstInside : first < row.length) (secondInside : second < row.length) :
    (pipesFilter first second parameter).eval context (row ++ extra) =
      (pipesFilter first second parameter).eval context row :=
  Expr.eval_append context rowFree row extra (Nat.le_refl _)
    (by simp [pipesFilter, pipesCall, Expr.readsBelow, Expr.any, Arguments.any, Expr.isColumnFrom, firstInside,
      secondInside])

/-- In the scope of one table read from the catalog, the written value {lit}`a || b` resolves to the
concatenation of the two columns, without affinity, for names that the table has. Proof sketch: resolve both
operands with the column lookup law, then reduce the operator. -/
theorem resolve_pipes_at {dqs : Bool} {position : Option Nat} {tableName first second : Identifier}
    {columns : List CatalogColumn} {rowid aliased : Bool} {firstPosition secondPosition : Nat}
    (firstFound : columnPosition columns first = some firstPosition)
    (secondFound : columnPosition columns second = some secondPosition) :
    resolveOperand dqs (Scope.singleAt position tableName columns rowid aliased) {} true
      (.concatenate (.identifier first .none) (.identifier second .none)) =
      .ok (pipesCall firstPosition secondPosition, none) := by
  rw [resolveOperand_arm_concatenate, resolveOperand_identifier_singleAt firstFound,
    resolveOperand_identifier_singleAt secondFound]
  rfl

/-- In the scope of one table read from the catalog, the written filter {lit}`a || b = lower(?n)` resolves to
{name}`pipesFilter`. Proof sketch: the comparison law resolves both operands; neither has affinity or
collation, so the default BINARY collation applies. -/
theorem resolve_pipes_filter_at {dqs : Bool} {position : Option Nat} {tableName first second : Identifier}
    {columns : List CatalogColumn} {rowid aliased : Bool} {firstPosition secondPosition : Nat}
    (firstFound : columnPosition columns first = some firstPosition)
    (secondFound : columnPosition columns second = some secondPosition) (number : Nat) :
    resolveOperand dqs (Scope.singleAt position tableName columns rowid aliased) {} true
      (.compare .eq (.concatenate (.identifier first .none) (.identifier second .none))
        (.call "lower" [.parameter number])) = .ok (pipesFilter firstPosition secondPosition number, none) := by
  rw [resolveOperand_compare _ _ (by decide) (by decide)]
  simp only [resolve_pipes_at firstFound secondFound, resolve_lower_parameter, Except.mapError, bind, Except.bind]
  simp [comparisonAffinity, comparisonCollation, Syntax.Expr.explicitCollation, Syntax.Expr.firstExplicitCollation,
    Syntax.Expr.columnCollation, pipesFilter]

/-- The concatenation predicate is calm: it has no fallible call, clock read or counter call. Proof sketch:
unfold the comparison and the calls; neither concatenation nor lowercase can fail. -/
theorem pipesFilter_calm (first second number : Nat) : (pipesFilter first second number).Calm := by
  simp [pipesFilter, pipesCall, Expr.Calm, Expr.any, Arguments.any, Expr.isFallibleCall, Expr.readsClockHere,
    Expr.readsCounterHere, ScalarFunction.canFail]

/-- The lookup {lit}`SELECT id FROM t WHERE a || b = lower(?n)` as syntax. -/
def pipesLookup (reference : Syntax.TableReference) (idName firstName secondName : Identifier) (text : String)
    (number : Nat) : Syntax.Statement :=
  .select [.expression (.identifier idName .none) none text] (some reference) []
    (some (.compare .eq (.concatenate (.identifier firstName .none) (.identifier secondName .none))
      (.call "lower" [.parameter number])))
    [] [] none none [] none false none

/-- For a table that has the id column and the two columns, the lookup resolves to the simple query of the table
with {name}`pipesFilter` and the id column. The table reference names no schema, query or arguments. Proof
sketch: {name}`resolveStatement_select_column` with {name}`resolve_pipes_filter_at`. -/
theorem resolve_pipes_lookup (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (position : Nat) (table : CatalogTable)
    (idName firstName secondName : Identifier) (text : String) (number : Nat)
    {idPosition firstPosition secondPosition : Nat}
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : state.catalog.findTable reference.table = some (position, table))
    (idFound : columnPosition table.columns idName = some idPosition)
    (firstFound : columnPosition table.columns firstName = some firstPosition)
    (secondFound : columnPosition table.columns secondName = some secondPosition) :
    ∃ names, resolveStatement context state (pipesLookup reference idName firstName secondName text number) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.first position]
        (some (pipesFilter firstPosition secondPosition number)) [.scalar (.column idPosition)] names) [], state) :=
  resolveStatement_select_column context state reference _ position table _ idName text namedSource current arguments
    found idFound (FilterResolves.of_term (result := (pipesFilter firstPosition secondPosition number, none))
      (by simp [namesAlias, namesAliasIn]) (resolve_pipes_filter_at firstFound secondFound number))

end ConcatFixture
