import Belay.Sqlite.Model.Resolution.OperandProjection

set_option doc.verso true

/-! The equations of {lit}`resolveOperand`, {lit}`resolveArguments` and {lit}`resolveCase`, one for each
form of expression, in the shape that the functions had before the name trace was threaded through
them. Each is the projection of the traced arm, so a proof that unfolds the resolver with
{lit}`simp only [traced_arms]` meets the same bodies as before. -/

namespace Belay.Sqlite.Model

variable (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (misuse : Bool)

/-- For every unqualified name: it is the operand of its name when the scope has one column of it,
and otherwise a model restriction for a rowid name, a text literal for a double-quoted name when
{lit}`dqs` is on, the integer of an unquoted {lit}`TRUE` or {lit}`FALSE`, or SQLite's error. -/
@[traced_arms] theorem resolveOperand_arm_identifier (name : Identifier) (quote : Syntax.QuoteKind) :
    resolveOperand dqs scope shapes misuse (.identifier name quote) = (match scope.resolveName name with
    | .found _ reads => scope.nameRead reads
    | .missing =>
      if rowidName name && scope.any (fun source => source.namesVisible && source.hasRowid) then
        .error (.restriction [] .rowidName)
      else if quote == .double && dqs then .ok (.literal (.text name.bytes), none)
      else if quote == .none && booleanKeywordName name then
        .ok (.literal (.integer (if name.isKeyword (bytes! "true") then 1 else 0)), none)
      else .error (.prepare (.noSuchColumn name))
    | .ambiguous => .error (.prepare (.ambiguousColumn name))) := by
  simp only [resolveOperand, resolveOperandTraced, identifierTraced]
  cases scope.resolveName name <;> simp only [traced_drop, missingUse]
  all_goals repeat' split
  all_goals simp_all [traced_drop]


/-- For every qualified name {lit}`schema.source.column`: it is the operand of its column when the
sources of the qualifier have one, and otherwise a model restriction for a rowid name, or SQLite's
{lit}`ambiguous column name` or {lit}`no such column`, written with the qualifier. -/
@[traced_arms] theorem resolveOperand_arm_qualified (source column : Identifier) (schema : Option Identifier) :
    resolveOperand dqs scope shapes misuse (.qualified source column schema) =
    (match scope.resolveSchemaQualified source column schema with
    | .found _ reads => scope.nameRead reads
    | .missing =>
      if rowidName column && scope.rowidSource source then .error (.restriction [] .rowidName)
      else .error (.prepare (.noSuchColumn (qualifiedName schema source column)))
    | .ambiguous => .error (.prepare (.ambiguousColumn (qualifiedName schema source column)))) := by
  simp only [resolveOperand, resolveOperandTraced, qualifiedTraced]
  cases scope.resolveSchemaQualified source column schema <;> simp only [traced_drop]
  all_goals repeat' split
  all_goals simp_all [traced_drop]

/-- For every comparison: both operands resolve, each with its issues under its own child; a truth
test such as {lit}`x IS TRUE` is the test of the left operand, and any other comparison keeps the
affinity of {name}`comparisonAffinity` and the collation of {name}`comparisonCollation`. -/
@[traced_arms] theorem resolveOperand_arm_compare (operator : Comparison) (left right : Syntax.Expr) :
    resolveOperand dqs scope shapes misuse (.compare operator left right) = (do
    let a ← (resolveOperand dqs scope shapes misuse left).mapError (·.under [1])
    let b ← (resolveOperand dqs scope shapes misuse right).mapError (·.under [2])
    if truthTest operator right b.1 then
      -- x IS [NOT] TRUE is (NOT NOT x) IS [NOT] 1, and x IS [NOT] FALSE is (NOT x) IS [NOT] 1.
      let tested := if b.1.literal? == some (.integer 1) then .not (.not a.1) else .not a.1
      .ok (.compare operator none tested (.literal (.integer 1)), none)
    else .ok (.compare operator (comparisonAffinity a.2 b.2) a.1 b.1 (comparisonCollation scope left right), none)) := by
  simp only [resolveOperand, resolveOperandTraced, compareTraced, traced_drop]

/-- For every {lit}`COLLATE`: the operand resolves, and a collation name that is none of the three
collations of SQLite is a model restriction. -/
@[traced_arms] theorem resolveOperand_arm_collate (operand : Syntax.Expr) (name : Identifier) :
    resolveOperand dqs scope shapes misuse (.collate operand name) = (do
    let resolved ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    if (Collation.named? name).isNone then .error (.restriction [] .unknownCollation) else .ok resolved) := by
  simp only [resolveOperand, resolveOperandTraced, traced_drop]

/-- For every {lit}`AND`: both operands resolve as conditions. -/
@[traced_arms] theorem resolveOperand_arm_and (left right : Syntax.Expr) :
    resolveOperand dqs scope shapes misuse (.and left right) = (do
    let a ← condition [0] (resolveOperand dqs scope shapes misuse left)
    let b ← condition [1] (resolveOperand dqs scope shapes misuse right)
    .ok (.and a b, none)) := by
  simp only [resolveOperand, resolveOperandTraced, traced_drop]

/-- For every {lit}`OR`: both operands resolve as conditions. -/
@[traced_arms] theorem resolveOperand_arm_or (left right : Syntax.Expr) :
    resolveOperand dqs scope shapes misuse (.or left right) = (do
    let a ← condition [0] (resolveOperand dqs scope shapes misuse left)
    let b ← condition [1] (resolveOperand dqs scope shapes misuse right)
    .ok (.or a b, none)) := by
  simp only [resolveOperand, resolveOperandTraced, traced_drop]

/-- For every {lit}`NOT`: the operand resolves as a condition. -/
@[traced_arms] theorem resolveOperand_arm_not (operand : Syntax.Expr) :
    resolveOperand dqs scope shapes misuse (.not operand) = (do
    let a ← condition [0] (resolveOperand dqs scope shapes misuse operand)
    .ok (.not a, none)) := by
  simp only [resolveOperand, resolveOperandTraced, traced_drop]

/-- For every {lit}`IS NULL`: the operand resolves, and the test has no affinity. -/
@[traced_arms] theorem resolveOperand_arm_isNull (operand : Syntax.Expr) (negated : Bool) :
    resolveOperand dqs scope shapes misuse (.isNull operand negated) = (do
    let a ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    .ok (.isNull a.1 negated, none)) := by
  simp only [resolveOperand, resolveOperandTraced, traced_drop]

/-- For every arithmetic operator: both operands resolve, and the result has no affinity. -/
@[traced_arms] theorem resolveOperand_arm_arithmetic (operator : ArithmeticOperator) (left right : Syntax.Expr) :
    resolveOperand dqs scope shapes misuse (.arithmetic operator left right) = (do
    let a ← (resolveOperand dqs scope shapes misuse left).mapError (·.under [1])
    let b ← (resolveOperand dqs scope shapes misuse right).mapError (·.under [2])
    .ok (.arithmetic operator a.1 b.1, none)) := by
  simp only [resolveOperand, resolveOperandTraced, traced_drop]

/-- For every {lit}`CAST`: the operand resolves, and the result has the affinity of the type name. -/
@[traced_arms] theorem resolveOperand_arm_cast (operand : Syntax.Expr) (typeName : String) :
    resolveOperand dqs scope shapes misuse (.cast operand typeName) = (do
    let a ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    let affinity := affinityOf (some typeName)
    .ok (.cast affinity a.1, some affinity)) := by
  simp only [resolveOperand, resolveOperandTraced, traced_drop]

/-- For every numeric literal: the value of {name}`queryNumeric` without a sign. -/
@[traced_arms] theorem resolveOperand_arm_numeric_literal (text : String) :
    resolveOperand dqs scope shapes misuse (.numeric text) =
    (queryNumeric text false).map fun value => (.literal value, none) := by
  simp only [resolveOperand, resolveOperandTraced, traced_drop]

/-- For every negated numeric literal: the value of {name}`queryNumeric` with a sign. -/
@[traced_arms] theorem resolveOperand_arm_negate_literal (text : String) :
    resolveOperand dqs scope shapes misuse (.negate (.numeric text)) =
    (queryNumeric text true).map fun value => (.literal value, none) := by
  simp only [resolveOperand, resolveOperandTraced, traced_drop]

/-- For every other unary minus: {lit}`0 - operand`, as SQLite generates it. -/
@[traced_arms] theorem resolveOperand_arm_negate (operand : Syntax.Expr) (notNumeric : ∀ text, operand ≠ .numeric text) :
    resolveOperand dqs scope shapes misuse (.negate operand) = (do
    let a ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    .ok (.arithmetic .subtract (.literal (.integer 0)) a.1, none)) := by
  cases operand <;> first | exact absurd rfl (notNumeric _) | simp only [resolveOperand, resolveOperandTraced, traced_drop]

/-- For every unary plus: the operand's value without its affinity. -/
@[traced_arms] theorem resolveOperand_arm_positive (operand : Syntax.Expr) :
    resolveOperand dqs scope shapes misuse (.positive operand) = (do
    let a ← (resolveOperand dqs scope shapes misuse operand).mapError (·.under [0])
    .ok (a.1, none)) := by
  simp only [resolveOperand, resolveOperandTraced, traced_drop]

end Belay.Sqlite.Model
