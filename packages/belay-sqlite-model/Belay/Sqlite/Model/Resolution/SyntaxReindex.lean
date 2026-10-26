import Belay.Sqlite.Model.Resolution.Syntax

set_option doc.verso true

/-! Copy indexed query syntax into a different statement list. Common table expressions
need a copy for each use because each use can have different enclosing column bindings. -/

namespace Belay.Sqlite.Model.Syntax

mutual
/-- Change every query index in an expression with {lit}`index`, keeping all other syntax.
The callback can fail when an index does not belong to the copied query. Use
{lean}`(fun i => some i)` to validate without changing indexes. -/
def Expr.reindexM [Monad m] (index : Nat → m Nat) : Expr → m Expr
  | .negate operand => do return .negate (← operand.reindexM index)
  | .positive operand => do return .positive (← operand.reindexM index)
  | .compare operator left right => do return .compare operator (← left.reindexM index) (← right.reindexM index)
  | .and left right => do return .and (← left.reindexM index) (← right.reindexM index)
  | .or left right => do return .or (← left.reindexM index) (← right.reindexM index)
  | .not operand => do return .not (← operand.reindexM index)
  | .isNull operand negated => do return .isNull (← operand.reindexM index) negated
  | .call name arguments => do return .call name (← Expr.reindexListM index arguments)
  | .arithmetic operator left right => do return .arithmetic operator (← left.reindexM index) (← right.reindexM index)
  | .cast operand typeName => do return .cast (← operand.reindexM index) typeName
  | .collate operand name => do return .collate (← operand.reindexM index) name
  | .exists child => do return .exists (← index child)
  | .inQuery operand child negated => do return .inQuery (← operand.reindexM index) (← index child) negated
  | .subquery child => do return .subquery (← index child)
  | .inList operand values negated => do return .inList (← operand.reindexM index) (← Expr.reindexListM index values) negated
  | .between operand low high negated => do return .between (← operand.reindexM index) (← low.reindexM index) (← high.reindexM index) negated
  | .caseOf operands hasBase => do return .caseOf (← Expr.reindexListM index operands) hasBase
  | .concatenate left right => do return .concatenate (← left.reindexM index) (← right.reindexM index)
  | .raise kind (some message) => do return .raise kind (some (← message.reindexM index))
  | .null => pure .null
  | .numeric text => pure (.numeric text)
  | .string bytes => pure (.string bytes)
  | .blob bytes => pure (.blob bytes)
  | .parameter number => pure (.parameter number)
  | .currentTime keyword => pure (.currentTime keyword)
  | .identifier name quote => pure (.identifier name quote)
  | .qualified source column schema => pure (.qualified source column schema)
  | .callStar name => pure (.callStar name)
  | .raise kind none => pure (.raise kind none)

/-- Change query indexes in a list of expressions with {name}`Expr.reindexM`.
An empty list stays empty. -/
def Expr.reindexListM [Monad m] (index : Nat → m Nat) : List Expr → m (List Expr)
  | [] => do return []
  | first :: rest => do return (← first.reindexM index) :: (← Expr.reindexListM index rest)
end

/-- Change all query indexes in an expression with a total function. This is the pure
form of {name}`Expr.reindexM`; use {lean}`id` to keep the indexes. -/
def Expr.reindex (index : Nat → Nat) (expression : Expr) : Expr :=
  Id.run (expression.reindexM (pure ∘ index))


/-- Change the query indexes of a result expression. Stars retain their written names, and an
expression keeps its text without the name tokens, which name the subqueries of the original list. -/
def ResultColumn.reindexM [Monad m] (index : Nat → m Nat) : ResultColumn → m ResultColumn
  | .expression value alias text => do
    -- The name tokens of the text name the subqueries of the original list, so a copy for another
    -- list keeps only the text; the copy serves resolution and is never rewritten.
    return .expression (← value.reindexM index) alias text.text
  | .star => pure .star
  | .sourceStar source => pure (.sourceStar source)

/-- Change the query indexes of a FROM source and of its function arguments.
Names and aliases retain their written spelling. -/
def TableReference.reindexM [Monad m] (index : Nat → m Nat) (reference : TableReference) : m TableReference := do
  return { reference with
    query := ← reference.query.mapM index
    arguments := ← reference.arguments.mapM (Expr.reindexListM index) }

/-- Change query indexes in all clauses and in the parent link of a query.
The callback can reject references that do not belong to the copied query. -/
def Subquery.reindexM [Monad m] (index : Nat → m Nat) (query : Subquery) : m Subquery := do
  let joins ← query.joins.mapM fun join => do
    return { join with
      source := ← join.source.reindexM index
      condition := ← join.condition.mapM (Expr.reindexM index) }
  let orderBy ← query.orderBy.mapM fun term => do
    return { term with expression := ← term.expression.reindexM index }
  let compound ← query.compound.mapM fun terms => do
    let rest ← terms.rest.mapM fun (operator, child) => do return (operator, ← index child)
    return { first := ← index terms.first, rest : Compound }
  return { query with
    columns := ← query.columns.mapM (ResultColumn.reindexM index)
    source := ← query.source.mapM (TableReference.reindexM index)
    joins
    filter := ← query.filter.mapM (Expr.reindexM index)
    groupBy := ← Expr.reindexListM index query.groupBy
    orderBy
    limit := ← query.limit.mapM (Expr.reindexM index)
    offset := ← query.offset.mapM (Expr.reindexM index)
    parent := ← query.parent.mapM index
    having := ← query.having.mapM (Expr.reindexM index)
    compound }

end Belay.Sqlite.Model.Syntax
