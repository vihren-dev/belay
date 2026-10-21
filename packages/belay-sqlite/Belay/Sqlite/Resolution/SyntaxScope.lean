import Belay.Sqlite.Resolution.Scope

set_option doc.verso true

/-! Questions about an expression as written over the sources in scope, which resolution
asks before it resolves the expression: whether it names a result column alias, and
whether it reads a column. -/

namespace Belay.Sqlite

mutual
/-- Whether an expression names a result column alias: an identifier that names no
column of the query's own sources ({name}`Scope.inner`) but, after ASCII folding, is one of
{lit}`aliases`, which in a subquery also holds the aliases of the queries around it. SQLite
resolves such a name in {lit}`WHERE` and inside {lit}`ORDER BY` expressions to the
aliased result expression, before the double-quoted string fallback. -/
def namesAlias (scope : Scope) (aliases : List Identifier) : Syntax.Expr → Bool
  | .identifier name _ => (scope.inner.matches name).isEmpty &&
      aliases.any (·.sameName name)
  | .compare _ left right | .and left right | .or left right | .arithmetic _ left right =>
    namesAlias scope aliases left || namesAlias scope aliases right
  | .not operand | .isNull operand _ | .negate operand | .positive operand | .cast operand _
  | .collate operand _ | .inQuery operand .. =>
    namesAlias scope aliases operand
  | .call _ arguments => namesAliasIn scope aliases arguments
  | .inList operand values _ => namesAlias scope aliases operand || namesAliasIn scope aliases values
  | .between operand low high _ =>
    namesAlias scope aliases operand || namesAlias scope aliases low || namesAlias scope aliases high
  | .caseOf operands _ => namesAliasIn scope aliases operands
  | .concatenate left right => namesAlias scope aliases left || namesAlias scope aliases right
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .callStar _ | .qualified .. | .exists _
  | .subquery _ => false

/-- Whether some argument names a result column alias ({name}`namesAlias`). -/
def namesAliasIn (scope : Scope) (aliases : List Identifier) : List Syntax.Expr → Bool
  | [] => false
  | argument :: rest => namesAlias scope aliases argument || namesAliasIn scope aliases rest
end

mutual
/-- Whether an expression names a column in scope: an identifier with the folded name of
a column, or a qualified name of one, anywhere in the expression, or a subquery, which can read
the row. A write value that names a column depends on the row. -/
def mentionsColumn (scope : Scope) : Syntax.Expr → Bool
  | .identifier name _ => !(scope.matches name).isEmpty
  | .qualified source column => scope.resolveQualified source column != .missing
  | .compare _ left right | .and left right | .or left right | .arithmetic _ left right =>
    mentionsColumn scope left || mentionsColumn scope right
  | .not operand | .isNull operand _ | .negate operand | .positive operand | .cast operand _
  | .collate operand _ =>
    mentionsColumn scope operand
  | .exists _ | .inQuery .. | .subquery _ => true
  | .call _ arguments => mentionsColumnIn scope arguments
  | .inList operand values _ => mentionsColumn scope operand || mentionsColumnIn scope values
  | .between operand low high _ => mentionsColumn scope operand || mentionsColumn scope low || mentionsColumn scope high
  | .caseOf operands _ => mentionsColumnIn scope operands
  | .concatenate left right => mentionsColumn scope left || mentionsColumn scope right
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .callStar _ => false

/-- Whether some argument names a column in scope ({name}`mentionsColumn`). -/
def mentionsColumnIn (scope : Scope) : List Syntax.Expr → Bool
  | [] => false
  | argument :: rest => mentionsColumn scope argument || mentionsColumnIn scope rest
end

mutual
/-- Whether an expression has a qualified name {lit}`source.column` anywhere, which SQLite
refuses in a key term of CREATE INDEX. -/
def Syntax.Expr.hasQualifiedName : Syntax.Expr → Bool
  | .qualified .. => true
  | .compare _ left right | .and left right | .or left right | .arithmetic _ left right =>
    left.hasQualifiedName || right.hasQualifiedName
  | .not operand | .isNull operand _ | .negate operand | .positive operand | .cast operand _
  | .collate operand _ | .inQuery operand .. =>
    operand.hasQualifiedName
  | .call _ arguments => Syntax.Expr.anyQualifiedName arguments
  | .inList operand values _ => operand.hasQualifiedName || Syntax.Expr.anyQualifiedName values
  | .between operand low high _ => operand.hasQualifiedName || low.hasQualifiedName || high.hasQualifiedName
  | .caseOf operands _ => Syntax.Expr.anyQualifiedName operands
  | .concatenate left right => left.hasQualifiedName || right.hasQualifiedName
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .callStar _ | .identifier .. | .exists _
  | .subquery _ => false

/-- Whether some argument has a qualified name ({name}`Syntax.Expr.hasQualifiedName`). -/
def Syntax.Expr.anyQualifiedName : List Syntax.Expr → Bool
  | [] => false
  | argument :: rest => argument.hasQualifiedName || Syntax.Expr.anyQualifiedName rest
end

end Belay.Sqlite
