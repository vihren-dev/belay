import Belay.Sqlite.Model.Shared.Resolved.ResolvedExprForm

set_option doc.verso true

namespace Belay.Sqlite.CompiledScript
open Model Resolved

-- These implementation-local instances order syntax. SQLite value comparisons use their own affinity and collation.
deriving instance Ord for Comparison, Affinity, Collation, ArithmeticOperator, JsonFunction, TimeKeyword,
  CounterKind, DateFunction, TrimSide, ScalarFunction, Value
mutual
/-- Compare resolved syntax structurally. Recursion on the first expression makes this
order computable by Lean's kernel as well as by the evaluator. -/
def exprOrder (first second : Resolved.Expr) : Ordering :=
  let different := compare first.ctorIdx second.ctorIdx
  match first with
  | .column a => match second with
    | .column b => compare a b
    | _ => different
  | .parameter a => match second with
    | .parameter b => compare a b
    | _ => different
  | .exists a => match second with
    | .exists b => compare a b
    | _ => different
  | .subquery a => match second with
    | .subquery b => compare a b
    | _ => different
  | .aggregateValue a => match second with
    | .aggregateValue b => compare a b
    | _ => different
  | .literal a => match second with
    | .literal b => compare a b
    | _ => different
  | .compare op aff l r col => match second with
    | .compare op' aff' l' r' col' => (compare op op').then ((compare aff aff').then ((exprOrder l l').then ((exprOrder r r').then (compare col col'))))
    | _ => different
  | .and l r => match second with
    | .and l' r' => (exprOrder l l').then (exprOrder r r')
    | _ => different
  | .or l r => match second with
    | .or l' r' => (exprOrder l l').then (exprOrder r r')
    | _ => different
  | .coalesce l r => match second with
    | .coalesce l' r' => (exprOrder l l').then (exprOrder r r')
    | _ => different
  | .not a => match second with
    | .not b => exprOrder a b
    | _ => different
  | .isNull a neg => match second with
    | .isNull b neg' => (exprOrder a b).then (compare neg neg')
    | _ => different
  | .arithmetic op l r => match second with
    | .arithmetic op' l' r' => (compare op op').then ((exprOrder l l').then (exprOrder r r'))
    | _ => different
  | .cast aff e => match second with
    | .cast aff' e' => (compare aff aff').then (exprOrder e e')
    | _ => different
  | .json f args => match second with
    | .json f' args' => (compare f f').then (argsOrder args args')
    | _ => different
  | .date f args => match second with
    | .date f' args' => (compare f f').then (argsOrder args args')
    | _ => different
  | .scalar f args => match second with
    | .scalar f' args' => (compare f f').then (argsOrder args args')
    | _ => different
  | .now a => match second with
    | .now b => compare a b
    | _ => different
  | .counter a => match second with
    | .counter b => compare a b
    | _ => different
  | .inQuery a i aff col neg => match second with
    | .inQuery b j aff' col' neg' => (exprOrder a b).then ((compare i j).then ((compare aff aff').then ((compare col col').then (compare neg neg'))))
    | _ => different
  | .inList a vals aff col neg => match second with
    | .inList b vals' aff' col' neg' => (exprOrder a b).then ((argsOrder vals vals').then ((compare aff aff').then ((compare col col').then (compare neg neg'))))
    | _ => different

/-- Lexicographic order of the arguments of a function or IN expression. -/
private def argsOrder : Resolved.Arguments → Resolved.Arguments → Ordering
  | .nil, .nil => .eq
  | .nil, .cons .. => .lt
  | .cons .., .nil => .gt
  | .cons a as, .cons b bs => (exprOrder a b).then (argsOrder as bs)
end

attribute [-instance] instOrdComparison instOrdAffinity instOrdCollation instOrdArithmeticOperator
  instOrdJsonFunction instOrdTimeKeyword instOrdCounterKind instOrdDateFunction instOrdTrimSide
  instOrdScalarFunction instOrdValue
end Belay.Sqlite.CompiledScript
