import Belay.Sqlite.Resolution.QueryExprs

set_option doc.verso true

/-! Resolution of a single-table {lit}`SELECT` (ADR 0012, slice 1). The steps follow
SQLite's resolver: the table, the result columns, {lit}`WHERE`, {lit}`GROUP BY`,
{lit}`ORDER BY`, then {lit}`LIMIT` and {lit}`OFFSET`. The paths of a restriction use the
child positions of {lit}`Syntax.Statement.select`: 0 the columns, 2 the filter, 3 the
grouping terms, 4 the ordering terms, 5 the limit and 6 the offset. -/

namespace Belay.Sqlite

/-- The integer of a numeric value, if it is one. -/
def NumericValue.integer? : NumericValue → Option Int
  | .integer value => some value
  | .real | .hexTooBig => none

/-- The value of an integer literal, possibly negated; {lean}`(none : Option Int)`
for any other expression. -/
def integerLiteral : Syntax.Expr → Option Int
  | .numeric text => (numericValue text false).integer?
  | .negate operand => match operand with
    | .numeric text => (numericValue text true).integer?
    | .null | .string _ | .blob _ | .currentTime _ | .identifier .. | .negate _ | .positive _ | .equals ..
    | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. => none
  | .null | .string _ | .blob _ | .currentTime _ | .identifier .. | .positive _ | .equals .. | .compare ..
  | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. => none

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
    | .callStar name =>
      if normalizeIdentifier name == "count" then .ok (named (.aggregate .countRows) none)
      else throw (unmodeledFunction.under [0, column, 0])
    | .call name operand => match aggregateNamed name with
      | some aggregate =>
        let (resolved, _) ← (resolveOperand dqs columns true operand).mapError (·.under [0, column, 0, 1])
        .ok (named (.aggregate (aggregate resolved)) none)
      | none => throw (unmodeledFunction.under [0, column, 0])
    | .identifier name _ =>
      let (resolved, _) ← (resolveOperand dqs columns false value).mapError (·.under [0, column, 0])
      .ok (named (.scalar resolved) ((columnPosition columns name).bind (columns[·]?.map CatalogColumn.name)))
    | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .negate _ | .positive _ | .equals ..
    | .compare .. | .and .. | .or .. | .not _ | .isNull .. =>
      let (resolved, _) ← (resolveOperand dqs columns false value).mapError (·.under [0, column, 0])
      .ok (named (.scalar resolved) none)

/-- The index of the first result column whose alias has the folded name. -/
def aliasIndex (names : List (Option String)) (name : String) : Option Nat :=
  names.findIdx? fun alias => alias.any (normalizeIdentifier · == normalizeIdentifier name)

/-- Whether a result column of an aggregate query is admitted by the model: an
aggregate, or a scalar that is one of the grouping terms. SQLite also admits other
scalars ("bare columns", whose row it chooses); that is a model restriction. -/
def groupedOutput (terms : List Resolved.Expr) : Resolved.Output → Bool
  | .aggregate _ => true
  | .scalar expression => terms.contains expression

/-- The result column that an {lit}`ORDER BY` or {lit}`GROUP BY` term names: an integer
{lit}`k` from 1 to the number of columns names column {lit}`k - 1`; an identifier
names the first column with that alias. {lit}`some (.error ())` is an integer out of
range; {lean}`(none : Option (Except Unit Nat))` is any other term. -/
def namedResult (names : List (Option String)) : Syntax.Expr → Option (Except Unit Nat)
  | .identifier name _ => (aliasIndex names name).map .ok
  | term@.null | term@(.numeric _) | term@(.string _) | term@(.blob _) | term@(.currentTime _)
  | term@(.negate _) | term@(.positive _) | term@(.equals ..) | term@(.compare ..) | term@(.and ..)
  | term@(.or ..) | term@(.not _) | term@(.isNull ..) | term@(.callStar _) | term@(.call ..) =>
    (integerLiteral term).map fun (number : Int) =>
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
  | none =>
    if reservedName tableName then
      restrict index [1] "queries of SQLite's own tables, such as sqlite_schema, are not modeled; query an application table"
    else prepareError catalog (.noSuchTable tableName)
  | some (position, table) =>
  let resolved : Except ValueIssue Resolved.Query := do
    let outputs := (← resolveAll (resolveResultColumn dqs table.columns) results).flatten
    let aliases := results.flatMap fun
      | .star => table.columns.map fun _ => none
      | .expression _ alias _ => [alias]
    let condition ← match filter with
      | none => pure none
      | some term =>
        if namesAlias table.columns (aliases.filterMap id) term then throw (aliasInExpression.under [2])
        else some <$> condition [2] (resolveOperand dqs table.columns true term)
    let aggregate := !groupBy.isEmpty || outputs.any fun (output, _) => match output with
      | .aggregate _ => true
      | .scalar _ => false
    let grouped := fun (column : Nat) => match outputs[column]? with
      | some (.scalar expression, _) => .ok expression
      | some (.aggregate _, _) | none => .error (.prepare .aggregateInGroupBy)
    let terms ← resolveAll (fun item term => match term with
      | .identifier name _ => match columnPosition table.columns name, aliasIndex aliases name with
        | some position, _ => .ok (.column position)
        | none, some column => grouped column
        | none, none => (resolveOperand dqs table.columns true term).map (·.1) |>.mapError (·.under [3, item])
      | .callStar _ | .call .. =>
        .error (if aggregateCall term then .prepare .aggregateInGroupBy else unmodeledFunction.under [3, item])
      | .numeric _ | .negate _ => match namedResult aliases term with
        | some (.ok column) => grouped column
        | some (.error ()) => .error (.prepare (.groupByOutOfRange (item + 1) outputs.length))
        | none => .error (.restriction [3, item] "only a column name or a result column number is modeled in GROUP BY")
      | .null | .string _ | .blob _ | .currentTime _ | .positive _ | .equals .. | .compare .. | .and .. | .or ..
      | .not _ | .isNull .. =>
        .error (.restriction [3, item] "only a column name or a result column number is modeled in GROUP BY")) groupBy
    if aggregate && !outputs.all (groupedOutput terms ·.1) then
      throw (.restriction [0] "a result column outside GROUP BY in an aggregate query is not modeled; group by it or aggregate it")
    let order ← resolveAll (fun item (term : Syntax.OrderTerm) => match namedResult aliases term.expression with
      | some (.ok column) => .ok (Resolved.SortKey.output column, term.descending)
      | some (.error ()) => .error (.prepare (.orderByOutOfRange (item + 1) outputs.length))
      | none =>
        if aggregate then .error (.restriction [4, item] "an aggregate query is modeled with ORDER BY result column numbers or aliases only")
        else if namesAlias table.columns (aliases.filterMap id) term.expression then
          .error (aliasInExpression.under [4, item, 0])
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
