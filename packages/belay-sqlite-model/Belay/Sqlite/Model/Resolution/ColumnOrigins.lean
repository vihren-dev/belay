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
    if scope.triggerCell position then none else scope.originTypeAt position
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

/-- The cell selected by a star-expanded result. RIGHT JOIN can select the later
column; FULL JOIN can produce a coalesce, which has no single source cell. -/
def Scope.starColumnIndex (scope : Scope) (position : Nat) (column : CatalogColumn) : Option Nat :=
  match scope.starOperand position column with
  | .ok (.column index, _) => some index
  | .ok (.literal _, _) | .ok (.compare .., _) | .ok (.and .., _) | .ok (.or .., _)
  | .ok (.not _, _) | .ok (.isNull .., _) | .ok (.arithmetic .., _) | .ok (.cast .., _)
  | .ok (.coalesce .., _) | .ok (.json .., _) | .ok (.now _, _) | .ok (.parameter _, _)
  | .ok (.counter _, _) | .ok (.date .., _) | .ok (.scalar .., _) | .ok (.exists _, _)
  | .ok (.inQuery .., _) | .ok (.subquery _, _) | .ok (.inList .., _)
  | .ok (.aggregateValue _, _) | .error _ => none

/-- The origin of a star-expanded result. A merged FULL JOIN result has no
origin; a selected column follows its query source's original declaration. -/
def Scope.starOriginType (scope : Scope) (position : Nat) (column : CatalogColumn) : Option String :=
  (scope.starColumnIndex position column).bind scope.originTypeAt

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
