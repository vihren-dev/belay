import Belay.Sqlite.Model.Resolution.SyntaxEquality
import Belay.Sqlite.Model.Resolution.Collations
import Belay.Sqlite.Model.Resolution.ResultColumnTraced
import Belay.Sqlite.Model.Resolution.QueryTerms

set_option doc.verso true

/-! The association of grouping terms with result columns (ADR 0030, D5), as SQLite's
{lit}`resolve.c` records it: a number names its result column, and every other term (also an
alias, as its aliased expression) is associated with the last result column that is the same
written expression. An associated result column that is not a column under at most
{lit}`COLLATE` gives the term's value on the first row of the group; the other result columns
read the row of the group ({lit}`Resolved.Query.groupRow`). The comparison reads the written
expressions, because the resolved form keeps no {lit}`COLLATE` node. -/

namespace Belay.Sqlite.Model

/-- The positions of the source columns that a written column reference reads in the scope
({name}`NameResolution.found`); {lean}`(none : Option (List Nat))` for any other expression and
for a name that reads no column. With {lit}`t(a)`, {lit}`a` and {lit}`t.a` read the same
positions. -/
def Syntax.Expr.columnReadsIn (scope : Scope) : Syntax.Expr → Option (List Nat)
  | .identifier name _ => match scope.resolveName name with
    | .found _ reads => some reads
    | .missing | .ambiguous => none
  | .qualified source column schema => match scope.resolveSchemaQualified source column schema with
    | .found _ reads => some reads
    | .missing | .ambiguous => none
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast ..
  | .collate .. | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf .. | .concatenate ..
  | .raise .. => none

/-- The value of a numeric literal that SQLite's parser stores as a number
({lit}`EP_IntValue`): an integer literal, decimal or hexadecimal, from {lean}`0` to
{lean}`2147483647`. For example {lit}`01` and {lit}`0x1` give {lean}`1`; {lit}`1.0` and
{lit}`3000000000` give {lean}`(none : Option Int)`, so SQLite compares them as written. -/
def smallIntegerLiteral (text : String) : Option Int :=
  (integerLiteral (.numeric text)).filter (· ≤ 2147483647)

mutual
/-- Whether two written expressions are the same for the association of a grouping term
(SQLite's {lit}`sqlite3ExprCompare`): the same tree, where two column references are the same
when they read the same source columns ({lit}`reads`), two small integer literals are the same
when their values are ({name}`smallIntegerLiteral`), function names and collation names
compare without ASCII case, and {lit}`CAST` type names, unary plus and every other part
compare as written ({name}`Syntax.Expr.same`). For example {lit}`A + 0` is the same as
{lit}`a+0`, and {lit}`0 + a` is not. -/
def Syntax.Expr.sameIn (reads : Syntax.Expr → Option (List Nat)) : Syntax.Expr → Syntax.Expr → Bool
  | a@(.identifier ..), b@(.identifier ..) | a@(.identifier ..), b@(.qualified ..)
  | a@(.qualified ..), b@(.identifier ..) | a@(.qualified ..), b@(.qualified ..) =>
    match reads a, reads b with
    | some x, some y => x == y
    | some _, none | none, some _ | none, none => a.same b
  | .null, .null => true
  | .numeric a, .numeric b => match smallIntegerLiteral a, smallIntegerLiteral b with
    | some x, some y => x == y
    | some _, none | none, some _ | none, none => a == b
  | .currentTime a, .currentTime b => a == b
  | .callStar a, .callStar b => normalizeIdentifier a == normalizeIdentifier b
  | .string a, .string b | .blob a, .blob b => a == b
  | .negate a, .negate b | .positive a, .positive b | .not a, .not b => a.sameIn reads b
  | .compare o a b, .compare p c d => o == p && a.sameIn reads c && b.sameIn reads d
  | .arithmetic o a b, .arithmetic p c d => o == p && a.sameIn reads c && b.sameIn reads d
  | .and a b, .and c d | .or a b, .or c d | .concatenate a b, .concatenate c d =>
    a.sameIn reads c && b.sameIn reads d
  | .isNull a n, .isNull b m => n == m && a.sameIn reads b
  | .call n xs, .call m ys => normalizeIdentifier n == normalizeIdentifier m && Syntax.Expr.sameListIn reads xs ys
  | .cast a t, .cast b u => t == u && a.sameIn reads b
  | .collate a n, .collate b m => n.sameName m && a.sameIn reads b
  | .exists i, .exists j | .subquery i, .subquery j | .parameter i, .parameter j => i == j
  | .inQuery a i n, .inQuery b j m => i == j && n == m && a.sameIn reads b
  | .inList a xs n, .inList b ys m => n == m && a.sameIn reads b && Syntax.Expr.sameListIn reads xs ys
  | .between a l h n, .between b k g m => n == m && a.sameIn reads b && l.sameIn reads k && h.sameIn reads g
  | .caseOf xs n, .caseOf ys m => n == m && Syntax.Expr.sameListIn reads xs ys
  | .raise k none, .raise l none => k == l
  | .raise k (some a), .raise l (some b) => k == l && a.sameIn reads b
  | .raise _ none, .raise _ (some _) | .raise _ (some _), .raise _ none => false
  | .identifier .., _ | .qualified .., _
  | .null, _ | .numeric _, _ | .string _, _ | .blob _, _ | .parameter _, _ | .currentTime _, _
  | .negate _, _ | .positive _, _ | .compare .., _ | .and .., _ | .or .., _ | .not _, _ | .isNull .., _
  | .callStar _, _ | .call .., _ | .arithmetic .., _ | .cast .., _ | .collate .., _ | .exists _, _
  | .inQuery .., _ | .subquery _, _ | .inList .., _ | .between .., _ | .caseOf .., _ | .concatenate .., _
  | .raise .., _ => false

/-- Whether two lists of written expressions are the same, item by item
({name}`Syntax.Expr.sameIn`). -/
def Syntax.Expr.sameListIn (reads : Syntax.Expr → Option (List Nat)) : List Syntax.Expr → List Syntax.Expr → Bool
  | [], [] => true
  | a :: xs, b :: ys => a.sameIn reads b && Syntax.Expr.sameListIn reads xs ys
  | [], _ :: _ | _ :: _, [] => false
end

/-- Whether a written expression is a column reference under zero or more {lit}`COLLATE`
clauses: a qualified name, or a name that reads a column of the scope. Such a result column
reads the row of the group also when a grouping term is associated with it. -/
def Syntax.Expr.columnUnderCollate (scope : Scope) : Syntax.Expr → Bool
  | .identifier name _ => (scope.resolveName name matches .found ..)
  | .qualified .. => true
  | .collate operand _ => operand.columnUnderCollate scope
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast ..
  | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf .. | .concatenate ..
  | .raise .. => false

/-- The written expression of each result column, in the order of the outputs: an expression
column gives itself, and each column that {lit}`*` or {lit}`x.*` expands to gives
{lean}`(none : Option Syntax.Expr)`, as {lit}`resultAliases` lists them. -/
def writtenResults (scope : Scope) (results : List Syntax.ResultColumn) : List (Option Syntax.Expr) :=
  results.flatMap fun
    | .star => scope.visible.map fun _ => none
    | .sourceStar name => ((scope.starColumns? name).map (·.map fun _ => none)).getD []
    | .expression value _ _ => [some value]

/-- The result column associated with a grouping term, as SQLite's {lit}`resolve.c` records
it: a number names its result column ({name}`namedResult`); an alias that no source column has
stands for its aliased expression; that expression, or any other term, is associated with the
last result column whose written form is the same ({name}`Syntax.Expr.sameIn`). For example
with {lit}`SELECT a+0 AS k, a+0`, {lit}`GROUP BY k` is associated with the second column.
{lean}`(none : Option Nat)` when no result column is the same. -/
def associatedResult (scope : Scope) (written : List (Option Syntax.Expr)) (aliases : List (Option Identifier))
    (term : Syntax.Expr) : Option Nat :=
  let lastSame := fun (expression : Syntax.Expr) =>
    ((written.zipIdx.filter fun (column, _) =>
      column.any (·.sameIn (·.columnReadsIn scope) expression)).getLast?).map (·.2)
  match term with
  | .identifier name _ => match scope.resolveName name, aliasIndex aliases name with
    | .missing, some column => (written[column]?).join.bind lastSame
    | .missing, none | .ambiguous, _ | .found .., _ => lastSame term
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast ..
  | .qualified .. | .collate .. | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf ..
  | .concatenate .. | .raise .. => match namedResult aliases term with
    | some (.ok column) => some column
    | some (.error ()) | none => lastSame term

/-- The result columns that give the value of their grouping term on the first row of the
group ({lit}`Resolved.Query.firstRowColumns`): each column associated with a grouping term
({name}`associatedResult`) whose written form is not a column under at most {lit}`COLLATE`
({name}`Syntax.Expr.columnUnderCollate`). -/
def firstRowResults (scope : Scope) (results : List Syntax.ResultColumn) (terms : List Syntax.Expr) : List Nat :=
  let written := writtenResults scope results
  terms.filterMap fun term => (associatedResult scope written (resultAliases scope results) term).filter
    fun column => (written[column]?).join.any (!·.columnUnderCollate scope)

end Belay.Sqlite.Model
