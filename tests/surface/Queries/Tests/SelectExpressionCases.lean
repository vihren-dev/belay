import SelectProjectionCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A11 of the expression rules of ADR 0027: a projection that copies a column, reads
a parameter and computes an arithmetic and a {lit}`CASE` expression, over every database with generic
table and column premises, with a witness and the contrast that the value of an expression does not
discharge its failure obligation. -/

namespace SelectExpressionCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectProjectionCases

/-- The query of A11: the customer, a tag, twice the amount and whether the invoice is due. -/
def billing (tag : Value) : Script :=
  sql r"SELECT customer, :tag, amount * 2, CASE WHEN amount > 0 THEN 'due' ELSE 'none' END FROM invoices" tag

/-- The result columns of {name}`billing` as the parser gives them. -/
def billingColumns : List Syntax.ResultColumn :=
  [.expression (.identifier (name! "customer") .none) none "customer",
   .expression (.parameter 1) none ":tag",
   .expression (.arithmetic .multiply (.identifier (name! "amount") .none) (.numeric "2")) none "amount * 2",
   .expression (.caseOf [.compare .gt (.identifier (name! "amount") .none) (.numeric "0"), .string [100, 117, 101],
      .string [110, 111, 110, 101]] false) none "CASE WHEN amount > 0 THEN 'due' ELSE 'none' END"]

/-- The text {lit}`'due'`. -/
def due : Value := .text [100, 117, 101]

/-- The text {lit}`'none'`. -/
def noneDue : Value := .text [110, 111, 110, 101]

/-- The resolved outputs of {name}`billingColumns` over a table whose columns {lit}`customer` and
{lit}`amount` are at the given positions, with the affinity and collation of the amount column. -/
def billingOutputs (customerIndex amountIndex : Nat) (amount : CatalogColumn) : List Resolved.Output :=
  [.scalar (.column customerIndex), .scalar (.parameter 1),
   .scalar (.arithmetic .multiply (.column amountIndex) (.literal (.integer 2))),
   .scalar (.scalar .iif (.cons (.compare .gt (some amount.affinity) (.column amountIndex) (.literal (.integer 0))
     amount.collation) (.cons (.literal due) (.cons (.literal noneDue) .nil))))]

/-- For every catalog, table position and table with the columns {lit}`customer` and {lit}`amount`
at the given positions, where the amount column is {lit}`amount`: the result columns of
{name}`billing` resolve in the scope of the table, and their outputs are {name}`billingOutputs`.
Proof sketch: the resolution laws of a column, a parameter, a numeric and a string literal and a
comparison; the comparison has the collation of the amount column. -/
theorem billingColumns_resolve (catalog : Catalog) {position customerIndex amountIndex : Nat} {table : CatalogTable}
    {amount : CatalogColumn}
    (customerFound : columnPosition table.columns (name! "customer") = some customerIndex)
    (amountFound : columnPosition table.columns (name! "amount") = some amountIndex)
    (amountAt : table.columns[amountIndex]? = some amount) :
    ∃ resolved, resolveAll (resolveResultColumn runContext.profile.dqsDml
      (tableScope catalog { table := name! "invoices", alias := none } position table) { later := [] })
      billingColumns = .ok resolved ∧ resolved.flatten.map (·.1) = billingOutputs customerIndex amountIndex amount := by
  have collation : comparisonCollation (tableScope catalog { table := name! "invoices", alias := none } position
      table) (.identifier (name! "amount") .none) (.numeric "0") = amount.collation := by
    simp only [comparisonCollation, Syntax.Expr.explicitCollation, Syntax.Expr.columnCollation, tableScope,
      resolveName_one_source_at amountFound]
    simp [Scope.columns, Scope.singleAt, amountAt]
  have two : queryNumeric "2" false = .ok (.integer 2) := by decide
  have zero : queryNumeric "0" false = .ok (.integer 0) := by decide
  simp [billingColumns, resolveAll, resolveAllFrom, resolveResultColumn_expression,
    resolveOperand_identifier_table customerFound, resolveOperand_identifier_table amountFound,
    resolveOperand_parameter, resolveOperand_numeric, resolveOperand_string,
    resolveOperand_compare_of_notBoolean _ (Syntax.Expr.numeric "0") rfl, traced_arms, Except.mapError, Except.map,
    Bind.bind, Except.bind, Pure.pure, Except.pure, two, zero, collation, amountAt, comparisonAffinity,
    billingOutputs, due, noneDue]

/-- The query of A11 has one statement. -/
theorem billing_one (tag : Value) : (billing tag).statements.length = 1 := rfl

/-- A row of A11 comes from a stored row: it is the customer cell, the bound tag, the amount cell times 2, and
{name}`due` when the amount is greater than 0 under the affinity and collation of the column, else
{name}`noneDue`. -/
def billedFrom (stored : List Row) (customerIndex amountIndex : Nat) (amount : CatalogColumn) (tag : Value)
    (row : List Value) : Prop :=
  ∃ source ∈ stored, row = [source.values.getD customerIndex .null, boundValue tag,
    ArithmeticOperator.multiply.apply (source.values.getD amountIndex .null) (.integer 2),
    if Resolved.truthy (Comparison.gt.apply
        (Resolved.comparisonOperands (some amount.affinity) (source.values.getD amountIndex .null) (.integer 0)).1
        (Resolved.comparisonOperands (some amount.affinity) (source.values.getD amountIndex .null) (.integer 0)).2
        amount.collation) then due else noneDue]

/-- A11 with generic premises: for every database, environment and tag, when the catalog has a table
{lit}`invoices` at a position with the columns {lit}`customer` and {lit}`amount`, the query
{name}`billing` returns a result, and each of its rows comes from a stored row of the table as
{name}`billedFrom` says: the customer cell, the bound tag, the amount cell times 2 by the arithmetic of
the model, and the {lit}`CASE` value of the amount. The table can have any rows, also none. Proof
sketch: {name}`resolveStatement_select_table` with {name}`billingColumns_resolve` gives the simple query
of the table; {name}`Run.query_returnsResult_calmTable` reduces the claim to the possible results over
the scan, because no output can fail; {name}`Resolved.Query.mem_possibleResults_plain` gives the
source row of each result row, and the value rules compute its cells. -/
theorem billing_rows (db : Database) (env : Env) (tag : Value) {position customerIndex amountIndex : Nat}
    {table : CatalogTable} {amount : CatalogColumn}
    (found : db.raw.catalog.findTable (name! "invoices") = some (position, table))
    (customerFound : columnPosition table.columns (name! "customer") = some customerIndex)
    (amountFound : columnPosition table.columns (name! "amount") = some amountIndex)
    (amountAt : table.columns[amountIndex]? = some amount) :
    (db.run (query (billing tag) (billing_one tag)) env).returnsRows
      (billedFrom (db.raw.rows.getD position []) customerIndex amountIndex amount tag) := by
  obtain ⟨resolved, columnsOk, outputs⟩ := billingColumns_resolve db.raw.catalog customerFound amountFound amountAt
  have noFeed : (resolved.flatten.filterMap fun (output, _) => match output with
      | .scalar expression => some expression
      | .aggregate _ => none).any (fun expression =>
        expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false := by
    have mapped : (resolved.flatten.filterMap fun (output, _) => match output with
        | .scalar expression => some expression
        | .aggregate _ => none) = (resolved.flatten.map (·.1)).filterMap fun output => match output with
        | .scalar expression => some expression
        | .aggregate _ => none := by
      rw [List.filterMap_map]
      rfl
    rw [mapped, outputs]
    simp [billingOutputs, Resolved.Expr.any, Resolved.Arguments.any, Resolved.Expr.isFallibleCall]
  have resolvedStatement := resolveStatement_select_table runContext (db.raw.connection env.counters).resolveState
    { table := name! "invoices", alias := none } none position table none billingColumns resolved rfl rfl rfl found rfl
    (by simp [starIssue, billingColumns]) columnsOk (FilterResolves.of_none _ _ _ _) noFeed
  rw [outputs] at resolvedStatement
  rw [Run.returnsRows, Run.query_returnsResult_calmTable (script := billing tag) rfl (billing_one tag) db env
    resolvedStatement rfl (Database.table_of_findTable _ _ _ _ found) ?calm rfl rfl rfl ?noOverflow rfl]
  · intro result member row inResult
    obtain ⟨source, inSource, -, rfl⟩ := Resolved.Query.mem_possibleResults_plain rfl rfl rfl member inResult
    obtain ⟨stored, storedIn, rfl⟩ := (mem_sourceRows_iff _ source).mp inSource
    refine ⟨stored, storedIn, ?_⟩
    simp [Resolved.Query.rowOutput, Resolved.Query.simple, billingOutputs, Resolved.Expr.eval_column,
      Resolved.Expr.eval_parameter, Resolved.Expr.eval_arithmetic, Resolved.Expr.eval_iif, Resolved.Expr.eval_compare,
      Resolved.Expr.eval_literal, Resolved.Arguments.eval_cons, Resolved.Arguments.eval_nil, Resolved.iifValue,
      parameterValue]
  · apply Resolved.Statement.simpleTable_calm
    · simp [billingOutputs, Resolved.Output.scalars, Resolved.Expr.Calm, Resolved.Expr.any, Resolved.Arguments.any,
        Resolved.Expr.isFallibleCall, Resolved.Expr.readsClockHere, Resolved.Expr.readsCounterHere,
        Resolved.ScalarFunction.canFail]
    · simp [billingOutputs, Resolved.Output.operands]
  · simp [Resolved.Query.fails, Resolved.Query.simple]

/-- The text {lit}`'q1'`. -/
def quarter : Value := .text [113, 49]

/-- A11 witness: on {name}`shop`, with the tag {lit}`'q1'`, the query returns the two invoices with their
customer, the tag, twice the amount, and {lit}`'due'` for the positive amount and {lit}`'none'` for 0. -/
theorem billing_witness :
    (shop.run (query (billing quarter) (billing_one _))).returnsResult (· =
      [[.text [97, 99, 109, 101], quarter, .integer 20, due], [.text [122, 101, 116, 97], quarter, .integer 0, noneDue]]) := by
  decide +kernel

/-- The query of the A11 contrast: the absolute value of each amount. -/
def absolute : Script := sql r"SELECT abs(amount) FROM invoices"

/-- The contrast query has one statement. -/
theorem absolute_one : absolute.statements.length = 1 := rfl

/-- An invoice whose amount is the least 64-bit integer, whose absolute value has no 64-bit integer. -/
def extreme : Database := db! r"
  CREATE TABLE invoices (id INTEGER PRIMARY KEY, amount INTEGER);
  INSERT INTO invoices VALUES (1, -9223372036854775808);"

/-- A11 contrast: the value of an expression does not discharge its failure obligation. A call of
{lit}`abs` is not calm, because the function can fail; its value rule gives NULL for the row of
{name}`extreme`, and its fault rule a fault other than none there; the run of the query there returns neither a result nor an error: the model does
not describe the step, so no claim about its result holds. -/
theorem fault_contrast :
    ¬ (Resolved.Expr.scalar .abs (.cons (.column 1) .nil)).Calm ∧
      (Resolved.Expr.scalar .abs (.cons (.column 1) .nil)).eval (Resolved.EvalContext.bound [])
        [.integer 1, .integer (-9223372036854775808)] = .null ∧
      ((Resolved.Expr.scalar .abs (.cons (.column 1) .nil)).evaluate (Resolved.EvalContext.bound [])
        [.integer 1, .integer (-9223372036854775808)]).2 ≠ .none ∧
      ¬ (extreme.run (query absolute absolute_one)).returnsResult (fun _ => True) ∧
      ¬ (extreme.run (query absolute absolute_one)).returnsError (fun _ => True) :=
  ⟨by simp [Resolved.Expr.calm_scalar, Resolved.ScalarFunction.canFail], by decide +kernel,
    by rw [Resolved.Expr.fault_scalar _ _ (by decide)]; decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms billingColumns_resolve
#print axioms billing_rows
#print axioms billing_witness
#print axioms fault_contrast

end SelectExpressionCases
