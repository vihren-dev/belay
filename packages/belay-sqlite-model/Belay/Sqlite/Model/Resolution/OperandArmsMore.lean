import Belay.Sqlite.Model.Resolution.OperandArms

set_option doc.verso true

/-! The remaining equations of {lit}`resolveOperand`, and those of {lit}`resolveArguments` and
{lit}`resolveCase`: calls, constants, subqueries and the forms built from several operands. They
have the shape that the functions had before the name trace was threaded through them. -/

namespace Belay.Sqlite.Model

variable (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (misuse : Bool)

/-- For every call: the arguments resolve first, an aggregate that reads an outer query is a model
restriction, and then, when {lit}`misuse` is false, a listed aggregate is its value by index; with
{lit}`misuse` true, or for a call that is not listed, the call is {name}`callOperand`. Proof sketch: unfold the definitions, push the projection through the monad with {lit}`traced_drop`, and split on the cases of the arm. -/
@[traced_arms] theorem resolveOperand_arm_call (name : String) (arguments : List Syntax.Expr) :
    resolveOperand dqs scope shapes misuse (.call name arguments) = (do
    let resolved ← resolveArguments dqs scope shapes misuse 0 arguments
    if aggregateCall (.call name arguments) && resolved.readsUnder shapes shapes.outer then
      throw (.restriction [] .outerAggregate)
    match misuse, (Syntax.Expr.call name arguments).indexIn shapes.aggregates with
    | false, some index => .ok (.aggregateValue index, none)
    | _, _ => callOperand scope misuse name arguments resolved) := by
  simp only [resolveOperand, resolveOperandTraced, resolveArguments, traced_drop]
  cases (resolveArgumentsTraced dqs scope shapes misuse 0 arguments).drop <;> simp [traced_drop]
  all_goals repeat' split
  all_goals simp_all [traced_drop]


/-- For every call of a function on {lit}`*`: when {lit}`misuse` is false, a listed aggregate is its
value by index; with {lit}`misuse` true, or for a call that is not listed, it is an aggregate misuse or
the issue of a star call. Proof sketch: unfold the definitions, push the projection through the monad with {lit}`traced_drop`, and split on the cases of the arm. -/
@[traced_arms] theorem resolveOperand_arm_callStar (name : String) :
    resolveOperand dqs scope shapes misuse (.callStar name) = (
    match misuse, (Syntax.Expr.callStar name).indexIn shapes.aggregates with
    | false, some index => .ok (.aggregateValue index, none)
    | _, _ => .error (if aggregateCall (.callStar name) then aggregateIssue misuse name else starCallIssue name)) := by
  simp only [resolveOperand, resolveOperandTraced]
  repeat' split
  all_goals simp_all [traced_drop]

/-- For every constant: the null literal has the value null and no affinity. Proof sketch: both sides are equal by definition. -/
@[traced_arms] theorem resolveOperand_arm_null :
    resolveOperand dqs scope shapes misuse .null = .ok (.literal .null, none) := rfl

/-- For every text literal: its bytes as a text value. Proof sketch: both sides are equal by definition. -/
@[traced_arms] theorem resolveOperand_arm_string (bytes : List UInt8) :
    resolveOperand dqs scope shapes misuse (.string bytes) = .ok (.literal (.text bytes), none) := rfl

/-- For every blob literal: its bytes as a blob value. Proof sketch: both sides are equal by definition. -/
@[traced_arms] theorem resolveOperand_arm_blob (bytes : List UInt8) :
    resolveOperand dqs scope shapes misuse (.blob bytes) = .ok (.literal (.blob bytes), none) := rfl

/-- For every time keyword: the clock value of the statement. Proof sketch: both sides are equal by definition. -/
@[traced_arms] theorem resolveOperand_arm_currentTime (keyword : String) :
    resolveOperand dqs scope shapes misuse (.currentTime keyword) = .ok (.now (timeKeywordNamed keyword), none) := rfl

/-- For every parameter: the parameter of its number. Proof sketch: both sides are equal by definition. -/
@[traced_arms] theorem resolveOperand_arm_parameter (number : Nat) :
    resolveOperand dqs scope shapes misuse (.parameter number) = .ok (.parameter number, none) := rfl

/-- For every {lit}`EXISTS`: it names a subquery that resolution resolved before, else it is a model
restriction. Proof sketch: unfold the definitions, push the projection through the monad with {lit}`traced_drop`, and split on the cases of the arm. -/
@[traced_arms] theorem resolveOperand_arm_exists (index : Nat) :
    resolveOperand dqs scope shapes misuse (.exists index) = (match shapes.find index with
    | some _ => .ok (.exists index, none)
    | none => .error (.restriction [] .subqueryHere)) := by
  simp only [resolveOperand, resolveOperandTraced]
  cases shapes.find index <;> simp [traced_drop]

/-- For every scalar subquery: it has the affinity of its result column. Proof sketch: both sides are equal by definition. -/
@[traced_arms] theorem resolveOperand_arm_subquery (index : Nat) :
    resolveOperand dqs scope shapes misuse (.subquery index) =
    (shapes.column index).map fun shape => (.subquery index, shape.affinity) := rfl

/-- For every {lit}`IN` over a list: the operand and the list resolve, and the comparison uses the
affinity and the collation of the operand, except that a list of one constant value with an explicit
collation is {lit}`x = +c`. Proof sketch: unfold the definitions, push the projection through the monad with {lit}`traced_drop`, and split on the cases of the arm. -/
@[traced_arms] theorem resolveOperand_arm_inList (operand : Syntax.Expr) (values : List Syntax.Expr) (negated : Bool) :
    resolveOperand dqs scope shapes misuse (.inList operand values negated) = (do
    let a ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    let resolved ← resolveArguments dqs scope shapes misuse 0 values
    match values, resolved with
    | [value], .cons element .nil =>
      if value.explicitCollation.isSome && (element.lowestRead shapes).isNone &&
          !element.any Resolved.Expr.namesSubquery && !element.readsClock then
        -- SQLite's parser reads `x IN (c)` for one constant `c` as `x = +c`.
        let compared := .compare .eq a.2 a.1 element (comparisonCollation scope operand value)
        .ok (if negated then .not compared else compared, none)
      else .ok (.inList a.1 resolved a.2 (operand.collationIn scope) negated, none)
    | _, _ => .ok (.inList a.1 resolved a.2 (operand.collationIn scope) negated, none)) := by
  simp only [resolveOperand, resolveOperandTraced, resolveArguments, inListTraced, traced_drop]
  cases (resolveOperandTraced dqs scope shapes misuse operand).drop <;> simp [traced_drop]
  cases (resolveArgumentsTraced dqs scope shapes misuse 0 values).drop <;> simp [traced_drop]
  all_goals repeat' split
  all_goals simp_all [traced_drop]

/-- For every {lit}`BETWEEN`: it is {lit}`x >= a AND x <= b`, negated when written with {lit}`NOT`. Proof sketch: unfold the definitions and push the projection through the monad with {lit}`traced_drop`. -/
@[traced_arms] theorem resolveOperand_arm_between (operand low high : Syntax.Expr) (negated : Bool) :
    resolveOperand dqs scope shapes misuse (.between operand low high negated) = (do
    let a ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    let l ← (resolveOperand dqs scope shapes misuse low).mapError (·.under [1])
    let h ← (resolveOperand dqs scope shapes misuse high).mapError (·.under [2])
    let both := Resolved.Expr.and (.compare .ge (comparisonAffinity a.2 l.2) a.1 l.1 (comparisonCollation scope operand low))
      (.compare .le (comparisonAffinity a.2 h.2) a.1 h.1 (comparisonCollation scope operand high))
    .ok (if negated then .not both else both, none)) := by
  simp only [resolveOperand, resolveOperandTraced, betweenTraced, traced_drop]

/-- For every {lit}`CASE`: its operands are the arguments of {lit}`iif`. Proof sketch: unfold the definitions and push the projection through the monad with {lit}`traced_drop`. -/
@[traced_arms] theorem resolveOperand_arm_caseOf (operands : List Syntax.Expr) (hasBase : Bool) :
    resolveOperand dqs scope shapes misuse (.caseOf operands hasBase) = (do
    let arguments ← resolveCase dqs scope shapes misuse hasBase none 0 operands
    .ok (.scalar .iif arguments, none)) := by
  simp only [resolveOperand, resolveOperandTraced, resolveCase, traced_drop]

/-- For every {lit}`||`: the scalar function of the operator over both operands. Proof sketch: unfold the definitions and push the projection through the monad with {lit}`traced_drop`. -/
@[traced_arms] theorem resolveOperand_arm_concatenate (left right : Syntax.Expr) :
    resolveOperand dqs scope shapes misuse (.concatenate left right) = (do
    let a ← (resolveOperand dqs scope shapes misuse left).mapError (·.under [0])
    let b ← (resolveOperand dqs scope shapes misuse right).mapError (·.under [1])
    .ok (.scalar .pipes (.cons a.1 (.cons b.1 .nil)), none)) := by
  simp only [resolveOperand, resolveOperandTraced, traced_drop]

/-- For every {lit}`RAISE`: it is an error outside a trigger's statements. Proof sketch: both sides are equal by definition. -/
@[traced_arms] theorem resolveOperand_arm_raise (kind : Syntax.RaiseKind) (message : Option Syntax.Expr) :
    resolveOperand dqs scope shapes misuse (.raise kind message) = .error (.prepare .raiseOutsideTrigger) := rfl

/-- For every {lit}`IN` over a query: the operand resolves, and the comparison uses the affinity of
{name}`comparisonAffinity` and the collation of {name}`inCollation`. Proof sketch: unfold the definitions and push the projection through the monad with {lit}`traced_drop`. -/
@[traced_arms] theorem resolveOperand_arm_inQuery (operand : Syntax.Expr) (index : Nat) (negated : Bool) :
    resolveOperand dqs scope shapes misuse (.inQuery operand index negated) = (do
    let a ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    let shape ← shapes.column index
    .ok (.inQuery a.1 index (comparisonAffinity a.2 shape.affinity) (inCollation scope operand shape) negated, none)) := by
  simp only [resolveOperand, resolveOperandTraced, inQueryTraced, traced_drop]

/-- For no arguments: nothing resolves. Proof sketch: both sides are equal by definition. -/
@[traced_arms] theorem resolveArguments_arm_nil (index : Nat) :
    resolveArguments dqs scope shapes misuse index [] = .ok .nil := rfl

/-- For an argument and the rest: each resolves in written order, the issue of argument {lit}`k` at
{lit}`[1, k]`. Proof sketch: unfold the definitions and push the projection through the monad with {lit}`traced_drop`. -/
@[traced_arms] theorem resolveArguments_arm_cons (index : Nat) (argument : Syntax.Expr) (rest : List Syntax.Expr) :
    resolveArguments dqs scope shapes misuse index (argument :: rest) = (do
    let a ← (resolveOperand dqs scope shapes misuse argument).mapError (·.under [1, index])
    let tail ← resolveArguments dqs scope shapes misuse (index + 1) rest
    .ok (.cons a.1 tail)) := by
  simp only [resolveArguments, resolveArgumentsTraced, resolveOperand, traced_drop]

/-- For no operands: nothing resolves. Proof sketch: both sides are equal by definition. -/
@[traced_arms] theorem resolveCase_arm_nil (needsBase : Bool) (base : Option (Syntax.Expr × Operand)) (index : Nat) :
    resolveCase dqs scope shapes misuse needsBase base index [] = .ok .nil := rfl

/-- For an operand and the rest of a {lit}`CASE`: the base comes first when it is needed, a
{lit}`WHEN` value is compared with the base as {lit}`=` compares them, and every other operand is
kept as it is. Proof sketch: unfold the definitions, push the projection through the monad with {lit}`traced_drop`, and split on the cases of the arm. -/
@[traced_arms] theorem resolveCase_arm_cons (needsBase : Bool) (base : Option (Syntax.Expr × Operand)) (index : Nat)
    (operand : Syntax.Expr) (rest : List Syntax.Expr) :
    resolveCase dqs scope shapes misuse needsBase base index (operand :: rest) = (do
    let resolved ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0, index])
    if needsBase then resolveCase dqs scope shapes misuse false (some (operand, resolved)) (index + 1) rest
    else
      let isWhen := (index - (if base.isSome then 1 else 0)) % 2 == 0 && !rest.isEmpty
      let item := match base, isWhen with
        | some (written, value), true =>
          .compare .eq (comparisonAffinity value.2 resolved.2) value.1 resolved.1 (comparisonCollation scope written operand)
        | _, _ => resolved.1
      let tail ← resolveCase dqs scope shapes misuse false base (index + 1) rest
      .ok (.cons item tail)) := by
  simp only [resolveCase, resolveCaseTraced, resolveOperand, traced_drop]
  cases (resolveOperandTraced dqs scope shapes misuse operand).drop <;> simp [traced_drop]
  all_goals repeat' split
  all_goals simp_all [traced_drop, caseWhenTraced]

end Belay.Sqlite.Model
