import Belay.Sqlite.Model.Resolution.CompoundTerms

set_option doc.verso true

/-! The names of the result columns of a compound {lit}`SELECT` that SQLite sorts as
{lit}`SELECT * FROM (compound)` (ADR 0019, D3; {lit}`convertCompoundSelectToSubquery`). The
columns then have the names of the derived table's columns ({lit}`sqlite3ColumnsFromExprList`),
not the names of the left-most term. For example, the column of
{lit}`SELECT a COLLATE NOCASE FROM t EXCEPT SELECT a FROM u ORDER BY 1 COLLATE BINARY` is named
{lit}`a`, and that of the same compound without {lit}`COLLATE BINARY` is named
{lit}`a COLLATE NOCASE`. -/

namespace Belay.Sqlite.Model

/-- The expression without the {lit}`COLLATE` operators and the calls of {lit}`likely`,
{lit}`unlikely` and {lit}`likelihood` around it ({lit}`sqlite3ExprSkipCollateAndLikely`). For
example, {assert}`(Syntax.Expr.call "likely" [.collate .null (name! "nocase")]).withoutCollateAndLikely = .null`. -/
def Syntax.Expr.withoutCollateAndLikely : Syntax.Expr → Syntax.Expr
  | .collate operand _ => operand.withoutCollateAndLikely
  | expression@(.call name arguments) => match normalizeIdentifier name, arguments with
    | "likely", [operand] | "unlikely", [operand] | "likelihood", [operand, _] => operand.withoutCollateAndLikely
    | _, _ => expression
  | expression@.null | expression@(.numeric _) | expression@(.string _) | expression@(.blob _)
  | expression@(.parameter _) | expression@(.currentTime _) | expression@(.identifier ..) | expression@(.negate _)
  | expression@(.positive _) | expression@(.compare ..) | expression@(.and ..) | expression@(.or ..)
  | expression@(.not _) | expression@(.isNull ..) | expression@(.callStar _) | expression@(.arithmetic ..)
  | expression@(.cast ..) | expression@(.qualified ..) | expression@(.exists _) | expression@(.inQuery ..)
  | expression@(.subquery _) | expression@(.inList ..) | expression@(.between ..) | expression@(.caseOf ..)
  | expression@(.concatenate ..) | expression@(.raise ..) => expression

/-- The name without a suffix of {lit}`:` and digits, which SQLite removes before it adds a new
suffix: from the end, SQLite skips the digits, but not the first character, and removes the
rest when it stops at {lit}`:`. For example, {assert}`nameStem "a:12" = "a"`,
{assert}`nameStem "a:" = "a"` and {assert}`nameStem "a1" = "a1"`. -/
def nameStem (name : String) : String :=
  let characters := name.toList
  let digits := min (characters.reverse.takeWhile Char.isDigit).length (characters.length - 1)
  let stop := characters.length - 1 - digits
  if characters[stop]? == some ':' then String.ofList (characters.take stop) else name

/-- The name of a column that is unique among the names {lit}`taken`, which SQLite compares
without ASCII letter case: the name itself, else its stem ({name}`nameStem`) with {lit}`:1`,
then with {lit}`:2`, {lit}`:3` and {lit}`:4`; none when these names are taken too, as SQLite
then adds a random number. -/
def uniqueColumnName (taken : List String) (name : String) : Option String :=
  let free := fun (candidate : String) => !taken.any (normalizeIdentifier · == normalizeIdentifier candidate)
  let rec attempt : Nat → String → Option String
    | 0, _ => none
    | fuel + 1, candidate =>
      if free candidate then some candidate
      else attempt fuel s!"{nameStem candidate}:{5 - fuel}"
  attempt 5 name

/-- The names of the derived table's columns from the outputs of the left-most term of a
compound: {lit}`names` are the names of the term, the {lit}`AS` alias or the column name of
{lit}`*` and {lit}`x.*`, which stay; an expression without alias that reads one column after
{name}`Syntax.Expr.withoutCollateAndLikely` has the column's name ({name}`definedName`); the
names {lit}`true` and {lit}`false` in any letter case become {lit}`column` with the column
number; and each name is made unique ({name}`uniqueColumnName`). None when SQLite would add a
random number. -/
def derivedNames (scope : Scope) (results : List Syntax.ResultColumn) (names : List String) : Option (List String) :=
  let outputs := (resultAliases scope results).zip ((resultExpressions scope results).zip names)
  let plain := outputs.zipIdx.map fun ((alias, written, name), index) =>
    let named := match alias, written with
      | none, some value => (definedName scope value.withoutCollateAndLikely).getD name
      | some _, _ | none, none => name
    if normalizeIdentifier named == "true" || normalizeIdentifier named == "false" then s!"column{index + 1}" else named
  plain.foldl (fun taken name => taken.bind fun earlier => (uniqueColumnName earlier name).map (earlier ++ [·])) (some [])

end Belay.Sqlite.Model
