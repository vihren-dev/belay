set_option doc.verso true

/-! The comparison and arithmetic operators of SQL, without their rules. The syntax and
the resolved forms name operators; the rules are in {lit}`Comparison` and
{lit}`Arithmetic`. Keeping the operators apart means a change of a rule does not
rebuild the syntax and the catalog. -/

namespace Belay.Sqlite.Model

/-- A comparison operator of SQL: the six that give NULL for a NULL operand, and
{lit}`IS` and {lit}`IS NOT`, which treat two NULLs as equal (R-24731-45773). -/
inductive Comparison where
  /-- {lit}`=` or {lit}`==`. -/
  | eq
  /-- {lit}`<>` or {lit}`!=`. -/
  | ne
  /-- {lit}`<`. -/
  | lt
  /-- {lit}`<=`. -/
  | le
  /-- {lit}`>`. -/
  | gt
  /-- {lit}`>=`. -/
  | ge
  /-- {lit}`IS`. -/
  | is
  /-- {lit}`IS NOT`. -/
  | isNot
  deriving Repr, DecidableEq

/-- An arithmetic operator of SQL. -/
inductive ArithmeticOperator where
  /-- {lit}`+`. -/
  | add
  /-- {lit}`-`. -/
  | subtract
  /-- {lit}`*`. -/
  | multiply
  /-- {lit}`/`. -/
  | divide
  /-- {lit}`%`. -/
  | remainder
  deriving Repr, DecidableEq

end Belay.Sqlite.Model
