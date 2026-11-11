import Lean.ScopedEnvExtension
import Lean.Attributes
import Lean.Meta.Tactic.Simp.RegisterCommand

set_option doc.verso true

/-! The registry of SELECT phase rules: the attribute {lit}`sql_select_rule PHASE` tags a proved
theorem with one of the thirteen phases of a SELECT, and the procedure of {lit}`sql_select` reads the
tagged theorems of a phase in qualified declaration-name order. A registration is global, so it persists
through imports and a library can supply rules, or local ({lit}`attribute [local sql_select_rule filter]`),
so it ends with its section. The phase is a routing tag only: the procedure applies a rule by ordinary
theorem application, which keeps every premise of the rule. -/

namespace Belay.Sqlite

open Lean

/-- The evaluation laws that {lit}`sql_select` gives to the simplifier when it closes a premise or the
last goal: definitions of the results of a query that unfold to their parts, and the values of
expressions. The set is separate from the global simplifier set. -/
register_simp_attr sql_select_simp

/-- A phase of the evaluation of a SELECT, as the rules of the procedure route them. The phase
{lit}`window` is the cut of {lit}`LIMIT` and {lit}`OFFSET` and the choice among tied rows; SQL window
functions are not modeled. -/
inductive SelectPhase where
  /-- Table scans, joins, derived tables and other sources of rows. -/
  | source
  /-- The value and the fault of an expression. -/
  | expression
  /-- {lit}`WHERE`. -/
  | filter
  /-- {lit}`GROUP BY`: the groups and the row of a group. -/
  | group
  /-- Aggregate functions over a group. -/
  | aggregate
  /-- {lit}`HAVING`. -/
  | having
  /-- The result columns of a row or a group. -/
  | project
  /-- {lit}`DISTINCT`. -/
  | distinct
  /-- {lit}`ORDER BY`. -/
  | order
  /-- {lit}`LIMIT`, {lit}`OFFSET` and the choice among tied rows. -/
  | window
  /-- {lit}`UNION`, {lit}`INTERSECT` and {lit}`EXCEPT`. -/
  | compound
  /-- Scalar, {lit}`IN` and {lit}`EXISTS` subqueries. -/
  | subquery
  /-- The run of the statement: resolution, readiness and the output of the step. -/
  | execution
  deriving Inhabited, BEq, Repr

/-- The name of each phase, as the attribute and the explanations write it. -/
def SelectPhase.all : List (SelectPhase × String) :=
  [(.source, "source"), (.expression, "expression"), (.filter, "filter"), (.group, "group"),
    (.aggregate, "aggregate"), (.having, "having"), (.project, "project"), (.distinct, "distinct"),
    (.order, "order"), (.window, "window"), (.compound, "compound"), (.subquery, "subquery"),
    (.execution, "execution")]

/-- The name of a phase, for example {lit}`"filter"`. -/
def SelectPhase.label (phase : SelectPhase) : String :=
  ((SelectPhase.all.find? (·.1 == phase)).map (·.2)).getD "unknown"

/-- One registration: a theorem and its phase. -/
structure SelectRuleEntry where
  /-- The phase that routes the rule. -/
  phase : SelectPhase
  /-- The theorem. -/
  rule : Name
  deriving Inhabited

/-- The registered rules. Global entries come from the imports and the current file; local entries end
with their section. -/
initialize selectRuleExtension : SimpleScopedEnvExtension SelectRuleEntry (Array SelectRuleEntry) ←
  registerSimpleScopedEnvExtension { initial := #[], addEntry := fun entries entry => entries.push entry }

/-- The syntax of the attribute: {lit}`sql_select_rule` and the name of one phase. -/
syntax (name := sqlSelectRule) "sql_select_rule " ident : attr

/-- Register the attribute. It accepts one phase and only a theorem; {lit}`scoped` registration is
refused, because a namespace alone must not activate a rule. -/
initialize registerBuiltinAttribute {
  name := `sqlSelectRule
  descr := "a proved rule of a SELECT phase for sql_select"
  applicationTime := .afterTypeChecking
  add := fun declaration written kind => do
    let `(attr| sql_select_rule $phase:ident) := written
      | throwError "sql_select_rule needs one phase name, for example `sql_select_rule filter`."
    let some (found, _) := SelectPhase.all.find? (·.2 == phase.getId.toString)
      | throwError "sql_select_rule: unknown phase `{phase.getId}`. Use one of: \
          {", ".intercalate (SelectPhase.all.map (·.2))}."
    unless (← getConstInfo declaration) matches .thmInfo _ do
      throwError "sql_select_rule: `{declaration}` is not a theorem. Register a proved theorem."
    if kind == .scoped then
      throwError "sql_select_rule: scoped registration is not supported. Use a global or a local registration."
    selectRuleExtension.add { phase := found, rule := declaration } kind }

/-- The registered rules of the phases, each phase in qualified declaration-name order, the phases in
the given order. A rule registered twice is listed once. -/
def registeredSelectRules (phases : List SelectPhase) : CoreM (Array (SelectPhase × Name)) := do
  let entries := selectRuleExtension.getState (← getEnv)
  let mut found : Array (SelectPhase × Name) := #[]
  for phase in phases do
    let names := (entries.filter (·.phase == phase)).map (·.rule)
    let sorted := names.qsort (fun a b => a.toString < b.toString)
    for name in sorted do
      unless found.any (·.2 == name) do
        found := found.push (phase, name)
  return found

end Belay.Sqlite
