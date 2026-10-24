import Belay.Sqlite.Model.Resolution.CompoundNames

set_option doc.verso true

/-! Declared-type origins of query results. SQLite's {lit}`columnType` follows a
column or scalar subquery to its original result expression. For a compound,
this origin follows the right-most term. It differs from the normalized type
of the compound's own source column, which starts from its left-most term. -/

namespace Belay.Sqlite.Model

/-- The declared type of the column that a name reads. A merged full-join name
reads a coalesce and has no origin type. Unresolved names and trigger cells also
have none, as SQLite's column-type lookup does not follow trigger expressions. -/
def Scope.nameOriginType (scope : Scope) : NameResolution → Option String
  | .found _ [position] =>
    if scope.triggerCell position then none else scope.columns[position]?.bind (·.declaredType)
  | .found _ _ | .missing | .ambiguous => none

/-- The declared-type origin of an expression, as SQLite's {lit}`columnType`
finds it. A column retains its declaration and a scalar subquery retains its
first result's origin. Other expressions, including CAST, COLLATE and unary
plus, have no declaration to retain. -/
def Syntax.Expr.originType (scope : Scope) (shapes : SubqueryShapes) : Syntax.Expr → Option String
  | .identifier name _ => scope.nameOriginType (scope.resolveName name)
  | .qualified source column => scope.nameOriginType (scope.resolveQualified source column)
  | .subquery index => (shapes.find index).bind (·.originType)
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .negate _ | .positive _
  | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic ..
  | .cast .. | .collate .. | .exists _ | .inQuery .. | .inList .. | .between .. | .caseOf ..
  | .concatenate .. | .raise .. => none

/-- The origin of a star-expanded result. RIGHT JOIN can select the later
column, while FULL JOIN can replace both origins with a coalesce. -/
def Scope.starOriginType (scope : Scope) (position : Nat) (column : CatalogColumn) : Option String :=
  match scope.starOperand position column with
  | .ok (.column index, _) => scope.columns[index]?.bind (·.declaredType)
  | .ok _ | .error _ => none

/-- The origin type of each result column, including the columns expanded by
stars. Use this list's first element for a scalar subquery's origin. -/
def resultOriginTypes (scope : Scope) (shapes : SubqueryShapes)
    (results : List Syntax.ResultColumn) : List (Option String) :=
  results.flatMap fun
    | .star => scope.visible.map fun (position, column) => scope.starOriginType position column
    | .sourceStar name => ((scope.starColumns? name).getD []).map fun (position, column) =>
      scope.starOriginType position column
    | .expression value _ _ => [value.originType scope shapes]

end Belay.Sqlite.Model
