import Belay.Sqlite.Model.Resolution.QueryExprs
import Belay.Sqlite.Model.Resolution.ResolveAll

set_option doc.verso true

/-! Resolution of the {lit}`RETURNING` columns of an INSERT or UPDATE (ADR 0012,
slice 3a). SQLite resolves them as the result columns of a {lit}`SELECT` over the
written table, after the values and the filter: {lit}`*` is every column under its
defined name, an expression is evaluated over the written row and named by its
alias, the defined name of a bare column, or its source text. An aggregate is
SQLite's {lit}`misuse of aggregate function`. -/

namespace Belay.Sqlite.Model

/-- The field of {lit}`Syntax.Statement.insert` that holds its {lit}`RETURNING` columns, the
first step of the issue path of a {lit}`RETURNING` column. -/
def insertReturningField : Nat := 5

/-- The field of {lit}`Syntax.Statement.update` that holds its {lit}`RETURNING` columns. -/
def updateReturningField : Nat := 3

/-- The field of {lit}`Syntax.Statement.delete` that holds its {lit}`RETURNING` columns. -/
def deleteReturningField : Nat := 2

/-- The defined name of the column that a bare result expression names, as SQLite names
a result column without an alias: the column's name as declared, for an unqualified name
that reads one column ({name}`Scope.resolveName`) or a qualified name; none for any other
expression, such as a merged name of a full join, which SQLite names as written. -/
def definedName (scope : Scope) : Syntax.Expr → Option String
  | .identifier name _ => match scope.resolveName name with
    | .found _ [position] => scope.columns[position]?.map (·.name.text)
    | .found .. | .missing | .ambiguous => none
  | .qualified source column schema => match scope.resolveSchemaQualified source column schema with
    | .found _ [position] => scope.columns[position]?.map (·.name.text)
    | .found .. | .missing | .ambiguous => none
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic ..
  | .cast .. | .collate .. | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf .. | .concatenate .. | .raise .. => none

/-- The occurrence of the alias of the {lit}`RETURNING` column at {lit}`item`, at {lit}`[item, 1]`. -/
def returningAliasOccurrence (item : Nat) (alias : Identifier) : NameOccurrence :=
  { resultAliasOccurrence 0 alias with path := [item, 1] }

/-- One {lit}`RETURNING` column at position {lit}`item`: the expressions and names it
gives. The paths of its issues and occurrences start at the column's position: part 0 is the
expression and part 1 the alias, which is recorded after the expression resolved. {lit}`*` is every
visible column of the one table of the write; a {lit}`source.*` column is SQLite's
{name}`ExprError.returningSourceStar`. -/
def returningColumnTraced (dqs : Bool) (scope : Scope) (item : Nat) :
    Syntax.ResultColumn → Traced ValueIssue (List (Resolved.Expr × String))
  | .star => pure (scope.visible.map fun (position, column) => (.column position, column.name.text))
  | .sourceStar _ => throw (.prepare .returningSourceStar)
  | .expression value alias text => do
      let (resolved, _) ← (resolveOperandTraced dqs scope {} true value).under [item, 0]
      Traced.recordAll (alias.toList.map (returningAliasOccurrence item))
      pure [(resolved, (alias.map (·.text)).getD ((definedName scope value).getD text.text))]

/-- Whether a result column is {lit}`source.*`. -/
def Syntax.ResultColumn.isSourceStar : Syntax.ResultColumn → Bool
  | .sourceStar _ => true
  | .star | .expression .. => false

/-- The {lit}`RETURNING` columns of a write over the table's scope, in order, or the
first issue. No {lit}`RETURNING` is the empty list. SQLite expands the wildcards before
it resolves names, so a {lit}`source.*` column anywhere is
{name}`ExprError.returningSourceStar` before the issue of any other column. The trace holds the
names of the columns up to the failing one. -/
def resolveReturningTraced (dqs : Bool) (scope : Scope) (items : List Syntax.ResultColumn) :
    Traced ValueIssue (List (Resolved.Expr × String)) :=
  if items.any Syntax.ResultColumn.isSourceStar then throw (.prepare .returningSourceStar) else
  (resolveAllTraced (returningColumnTraced dqs scope) items).map List.flatten

/-- The {lit}`RETURNING` columns of a write: {name}`resolveReturningTraced` without its trace. -/
def resolveReturning (dqs : Bool) (scope : Scope) (items : List Syntax.ResultColumn) :
    Except ValueIssue (List (Resolved.Expr × String)) :=
  (resolveReturningTraced dqs scope items).drop

end Belay.Sqlite.Model
