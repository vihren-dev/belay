import Belay.Sqlite.Resolution.QueryExprs

set_option doc.verso true

/-! Resolution of a single-table {lit}`SELECT` (ADR 0012, slice 1). The steps follow
SQLite's resolver: the table, the result columns, {lit}`WHERE`, {lit}`GROUP BY`,
{lit}`ORDER BY`, then {lit}`LIMIT` and {lit}`OFFSET`. The paths of a restriction use the
child positions of {lit}`Syntax.Statement.select`: 0 the columns, 2 the filter, 3 the
grouping terms, 4 the ordering terms, 5 the limit and 6 the offset. -/

namespace Belay.Sqlite

/-- The value of an integer literal, possibly negated; {lean}`(none : Option Int)`
for any other expression. -/
def integerLiteral : Syntax.Expr → Option Int
  | .numeric text => match numericValue text false with | .integer value => some value | _ => none
  | .negate (.numeric text) => match numericValue text true with | .integer value => some value | _ => none
  | _ => none

/-- One resolved result column with its name: {lit}`*` gives every column of the
table under its defined name; an aggregate is a whole result column; any other
expression is a scalar. A name is the {lit}`AS` alias, else the defined name of a
referenced column, else the source text as written. -/
def resolveResultColumn (dqs : Bool) (columns : List CatalogColumn) (column : Nat) :
    Syntax.ResultColumn → Except ValueIssue (List (Resolved.Output × String))
  | .star => .ok (columns.mapIdx fun position defined => (.scalar (.column position), defined.name))
  | .expression value alias text => do
    let named := fun (output : Resolved.Output) (defined : Option String) => [(output, alias.getD (defined.getD text))]
    match value with
    | .countRows => .ok (named (.aggregate .countRows) none)
    | .aggregate function operand =>
      let (resolved, _) ← (resolveOperand dqs columns true operand).mapError (·.under [0, column, 0, 1])
      .ok (named (.aggregate (match function with
        | .count => .count resolved | .min => .min resolved | .max => .max resolved)) none)
    | _ =>
      let (resolved, _) ← (resolveOperand dqs columns false value).mapError (·.under [0, column, 0])
      let defined := match resolved, value with
        | .column position, .identifier .. => columns[position]?.map CatalogColumn.name
        | _, _ => none
      .ok (named (.scalar resolved) defined)

/-- The result column that an {lit}`ORDER BY` or {lit}`GROUP BY` term names: an integer
{lit}`k` from 1 to the number of columns names column {lit}`k - 1`; an identifier
names the first column with that alias. {lit}`some (.error ())` is an integer out of
range; {lean}`(none : Option (Except Unit Nat))` is any other term. -/
def namedResult (names : List (Option String)) : Syntax.Expr → Option (Except Unit Nat)
  | .identifier name _ =>
    (names.findIdx? fun alias => alias.any (normalizeIdentifier · == normalizeIdentifier name)).map .ok
  | term => (integerLiteral term).map fun (number : Int) =>
      if 1 ≤ number ∧ number ≤ (names.length : Int) then .ok (number.toNat - 1) else .error ()

/-- Resolve a {lit}`LIMIT` or {lit}`OFFSET` expression: an integer literal, or none. -/
def windowValue (path : List Nat) : Option Syntax.Expr → Except ValueIssue (Option Int)
  | none => .ok none
  | some term => match integerLiteral term with
    | some value => .ok (some value)
    | none => .error (.restriction path "only an integer literal is modeled as LIMIT or OFFSET; write an integer")

/-- Resolve a {lit}`SELECT` from one table; see the module documentation for the steps. -/
def resolveSelect (context : ResolveContext) (catalog : Catalog) (index : Nat)
    (results : List Syntax.ResultColumn) (tableName : String) (filter : Option Syntax.Expr)
    (groupBy : List Syntax.Expr) (orderBy : List Syntax.OrderTerm) (limit offset : Option Syntax.Expr) :
    StatementResolution :=
  let dqs := context.profile.dqsDml
  match catalog.findTable tableName with
  | none => prepareError catalog (.noSuchTable tableName)
  | some (position, table) =>
  let resolved : Except ValueIssue Resolved.Query := do
    let outputs := (← resolveAll (resolveResultColumn dqs table.columns) results).flatten
    let aliases := results.flatMap fun
      | .star => table.columns.map fun _ => none
      | .expression _ alias _ => [alias]
    let condition ← match filter with
      | none => pure none
      | some term => some <$> condition [2] (resolveOperand dqs table.columns true term)
    let aggregate := !groupBy.isEmpty || outputs.any fun (output, _) => match output with
      | .aggregate _ => true | .scalar _ => false
    let terms ← resolveAll (fun item term => match namedResult aliases term with
      | some (.ok column) => match outputs[column]? with
        | some (.scalar expression, _) => .ok expression
        | _ => .error (.prepare .aggregateInGroupBy)
      | some (.error ()) => .error (.prepare (.groupByOutOfRange (item + 1) outputs.length))
      | none => match term with
        | .countRows | .aggregate .. => .error (.prepare .aggregateInGroupBy)
        | .identifier .. => (resolveOperand dqs table.columns true term).map (·.1) |>.mapError (·.under [3, item])
        | _ => .error (.restriction [3, item] "only a column name or a result column number is modeled in GROUP BY")) groupBy
    if aggregate && outputs.any (fun (output, _) => match output with
        | .scalar expression => !terms.contains expression | .aggregate _ => false) then
      throw (.restriction [0] "a result column outside GROUP BY in an aggregate query is not modeled; group by it or aggregate it")
    let order ← resolveAll (fun item (term : Syntax.OrderTerm) => match namedResult aliases term.expression with
      | some (.ok column) => .ok (Resolved.SortKey.output column, term.descending)
      | some (.error ()) => .error (.prepare (.orderByOutOfRange (item + 1) outputs.length))
      | none =>
        if aggregate then .error (.restriction [4, item] "an aggregate query is modeled with ORDER BY result column numbers or aliases only")
        else (resolveOperand dqs table.columns false term.expression).map (fun (e, _) => (.expression e, term.descending))
          |>.mapError (·.under [4, item, 0])) orderBy
    let limitValue ← windowValue [5] limit
    let offsetValue ← windowValue [6] offset
    if offsetValue.any (· < 0) then throw (.restriction [6] "a negative OFFSET is not modeled; write OFFSET 0 or more")
    return { table := position, filter := condition, aggregate, groupBy := terms, columns := outputs.map (·.1),
             names := outputs.map (·.2), orderBy := order, offset := (offsetValue.getD 0).toNat,
             limit := limitValue.bind fun value => if value < 0 then none else some value.toNat }
  match resolved with
  | .ok query => .ok (.query query, catalog)
  | .error issue => issueResolution catalog index [] issue

/-- For every successful resolution of a {lit}`SELECT`, the catalog is unchanged.
Proof sketch: every branch of the resolver returns the input catalog. -/
theorem resolveSelect_same (context : ResolveContext) (catalog after : Catalog) (index : Nat)
    (results : List Syntax.ResultColumn) (tableName : String) (filter : Option Syntax.Expr)
    (groupBy : List Syntax.Expr) (orderBy : List Syntax.OrderTerm) (limit offset : Option Syntax.Expr)
    (statement : Resolved.Statement)
    (ok : resolveSelect context catalog index results tableName filter groupBy orderBy limit offset =
      .ok (statement, after)) :
    after = catalog := by
  unfold resolveSelect at ok
  simp only [prepareError, issueResolution] at ok
  repeat' split at ok
  all_goals first | (cases ok; rfl) | (cases ok)

end Belay.Sqlite
