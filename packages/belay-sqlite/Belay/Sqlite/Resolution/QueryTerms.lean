import Belay.Sqlite.Resolution.Values
import Belay.Sqlite.Resolution.QueryForm

set_option doc.verso true

/-! The terms of a {lit}`SELECT` that name a result column or a number (ADR 0012, slice 1):
integer literals, the result column that an {lit}`ORDER BY` or {lit}`GROUP BY` term names,
the {lit}`LIMIT` and {lit}`OFFSET` values, and the checks of grouped result columns that
{lit}`Queries.lean` makes. -/

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
    | .null | .string _ | .blob _ | .currentTime _ | .identifier .. | .negate _ | .positive _
    | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast ..
    | .qualified .. | .collate .. | .exists _ | .inQuery .. | .subquery _ => none
  | .null | .string _ | .blob _ | .currentTime _ | .identifier .. | .positive _ | .compare ..
  | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast ..
  | .qualified .. | .collate .. | .exists _ | .inQuery .. | .subquery _ => none

/-- The index of the first result column whose alias has the folded name. -/
def aliasIndex (names : List (Option Identifier)) (name : Identifier) : Option Nat :=
  names.findIdx? fun alias => alias.any (·.sameName name)

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
def namedResult (names : List (Option Identifier)) : Syntax.Expr → Option (Except Unit Nat)
  | .identifier name _ => (aliasIndex names name).map .ok
  | term@.null | term@(.numeric _) | term@(.string _) | term@(.blob _) | term@(.currentTime _)
  | term@(.negate _) | term@(.positive _) | term@(.compare ..) | term@(.and ..)
  | term@(.or ..) | term@(.not _) | term@(.isNull ..) | term@(.callStar _) | term@(.call ..)
  | term@(.arithmetic ..) | term@(.cast ..) | term@(.qualified ..) | term@(.collate ..) | term@(.exists _)
  | term@(.inQuery ..) | term@(.subquery _) =>
    (integerLiteral term).map fun (number : Int) =>
      if 1 ≤ number ∧ number ≤ (names.length : Int) then .ok (number.toNat - 1) else .error ()

/-- Resolve a {lit}`LIMIT` or {lit}`OFFSET` expression: an integer literal, or none. -/
def windowValue (path : List Nat) : Option Syntax.Expr → Except ValueIssue (Option Int)
  | none => .ok none
  | some term => match integerLiteral term with
    | some value => .ok (some value)
    | none => .error (.restriction path .windowValue)

/-- Whether a query is a model restriction because SQLite may skip a failing group: it
has {lit}`GROUP BY`, a {lit}`LIMIT` or {lit}`OFFSET`, and a result column that can fail
({name}`Resolved.Output.canFail`). SQLite finalizes the groups in an order that the
model does not describe and stops at the window, so it may never compute a group
whose {lit}`SUM` overflows. -/
def windowSkipsFailure (groupBy : List Syntax.Expr) (limit offset : Option Syntax.Expr)
    (outputs : List Resolved.Output) : Bool :=
  !groupBy.isEmpty && (limit.isSome || offset.isSome) && outputs.any Resolved.Output.canFail

end Belay.Sqlite
