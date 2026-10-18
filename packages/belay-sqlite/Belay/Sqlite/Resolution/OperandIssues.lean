import Belay.Sqlite.Resolution.IssueLemmas

set_option doc.verso true

/-! The issues of query expression resolution name no catalog object (ADR 0012,
slice 3a). Constant values in writes are resolved as query expressions, and the
rules for prepare errors of INSERT and UPDATE need this fact. -/

namespace Belay.Sqlite

/-- For every literal text and sign, the issues of {name}`queryNumeric` name no
catalog object: the only prepare error is {lit}`hex literal too big`. Proof sketch:
split the match of {name}`queryNumeric`; the failing branches give that error. -/
theorem queryNumeric_issues (text : String) (negated : Bool) : IssuesNameNoObject (queryNumeric text negated) := by
  intro issue failed
  unfold queryNumeric at failed
  dsimp only at failed
  split at failed <;> cases failed <;> simp [ValueIssue.namesNoObject, PrepareError.namesObject]

/-- For every flag and name, the issues of a function call name no catalog object:
{name}`aggregateIssue`, {name}`callIssue` and {name}`pairIssue` give only
{lit}`misuse of aggregate function`, {lit}`wrong number of arguments`, or a restriction.
Proof sketch: unfold the three functions and split their conditions. -/
theorem callIssues (misuse : Bool) (name : String) :
    (aggregateIssue misuse name).namesNoObject ∧ (callIssue name).namesNoObject ∧ (pairIssue name).namesNoObject := by
  unfold aggregateIssue callIssue pairIssue unmodeledFunction
  refine ⟨?_, ?_, ?_⟩ <;> split <;> simp [ValueIssue.namesNoObject, PrepareError.namesObject]

/-- For every name, JSON function and argument list, the issues of {name}`jsonCall` name
no catalog object: its only error is {name}`PrepareError.wrongArgumentCount`. -/
theorem jsonCall_issues (name : String) (function : Resolved.JsonFunction) (arguments : Resolved.Arguments) :
    IssuesNameNoObject (jsonCall name function arguments) := by
  intro issue failed
  unfold jsonCall at failed
  split at failed <;> cases failed
  simp [ValueIssue.namesNoObject, PrepareError.namesObject]

/-- For every date and time function and argument list, the issues of {name}`dateCall`
name no catalog object: it has none. Proof sketch: {name}`dateCall` always succeeds. -/
theorem dateCall_issues (function : Resolved.DateFunction) (arguments : Resolved.Arguments) :
    IssuesNameNoObject (dateCall function arguments) := by
  intro issue failed
  cases failed

/-- For every name, resolved argument list and issue that names no catalog object, the issues
of {name}`functionCall` name no catalog object. Proof sketch: its errors are the given
issue and those of {name}`jsonCall_issues`; {name}`dateCall` cannot fail. -/
theorem functionCall_issues (name : String) (arguments : Resolved.Arguments) (issue : ValueIssue)
    (named : issue.namesNoObject) : IssuesNameNoObject (functionCall name arguments issue) := by
  intro failure failed
  unfold functionCall at failed
  split at failed
  · cases failed
  · split at failed
    · exact jsonCall_issues name _ _ failure failed
    · exact dateCall_issues _ _ failure failed
    · cases failed; exact named

mutual
/-- For every setting, column list, flag and expression, the issues of
{name}`resolveOperand` name no catalog object. Proof sketch: structural recursion on the
expression, with {lit}`resolveArguments_issue` for the arguments of a call. A compound
expression sequences its operands with {name}`bind_issues`, {name}`under_issues` and
{name}`condition_issues`, and fails itself only with a restriction; a leaf gives
{lit}`no such column`, {lit}`ambiguous column name`, a restriction,
{name}`queryNumeric_issues`, {name}`callIssues` or {name}`functionCall_issues`. -/
theorem resolveOperand_issue (dqs : Bool) (scope : Scope) (misuse : Bool) :
    (expression : Syntax.Expr) → IssuesNameNoObject (resolveOperand dqs scope misuse expression)
  | .null | .string _ | .blob _ | .currentTime _ => by
    intro issue failed; simp only [resolveOperand] at failed; cases failed <;> trivial
  | .numeric text => map_issues _ (queryNumeric_issues _ _)
  | .identifier name doubleQuoted => by
    intro issue failed
    simp only [resolveOperand] at failed
    repeat' split at failed
    all_goals (cases failed <;> simp [ValueIssue.namesNoObject, PrepareError.namesObject])
  | .qualified source column => by
    intro issue failed
    simp only [resolveOperand] at failed
    repeat' split at failed
    all_goals (cases failed <;> simp [ValueIssue.namesNoObject, PrepareError.namesObject])
  | .callStar name => by
    intro issue failed
    simp only [resolveOperand] at failed
    cases failed
    split
    · exact (callIssues misuse name).1
    · exact (callIssues misuse name).2.1
  | .call name arguments => by
    have resolved := resolveArguments_issue dqs scope misuse 0 arguments
    intro issue failed
    simp only [resolveOperand] at failed
    split at failed
    · split at failed
      · exact dateCall_issues _ _ issue failed
      · cases failed; exact (callIssues misuse name).2.1
    · split at failed
      · exact bind_issues resolved (fun _ => functionCall_issues _ _ _ (callIssues misuse name).2.1) issue failed
      · cases failed
        split
        · exact (callIssues misuse name).1
        · exact (callIssues misuse name).2.1
    · split at failed
      · exact bind_issues resolved (fun _ => functionCall_issues _ _ _ (callIssues misuse name).2.2) issue failed
      · cases failed; exact (callIssues misuse name).2.2
  | .compare operator left right =>
    bind_issues (under_issues _ (resolveOperand_issue dqs scope misuse left)) fun a =>
      bind_issues (under_issues _ (resolveOperand_issue dqs scope misuse right)) fun b => by
        intro issue failed
        split at failed <;> cases failed
  | .and left right =>
    bind_issues (condition_issues _ (resolveOperand_issue dqs scope misuse left)) fun _ =>
      bind_issues (condition_issues _ (resolveOperand_issue dqs scope misuse right)) fun _ =>
        fun _ failed => by cases failed
  | .or left right =>
    bind_issues (condition_issues _ (resolveOperand_issue dqs scope misuse left)) fun _ =>
      bind_issues (condition_issues _ (resolveOperand_issue dqs scope misuse right)) fun _ =>
        fun _ failed => by cases failed
  | .not operand =>
    bind_issues (condition_issues _ (resolveOperand_issue dqs scope misuse operand)) fun _ _ failed => by
      cases failed
  | .isNull operand negated =>
    bind_issues (under_issues _ (resolveOperand_issue dqs scope misuse operand)) fun _ _ failed => by
      cases failed
  | .arithmetic operator left right =>
    bind_issues (under_issues _ (resolveOperand_issue dqs scope misuse left)) fun _ =>
      bind_issues (under_issues _ (resolveOperand_issue dqs scope misuse right)) fun _ _ failed => by
        cases failed
  | .cast operand typeName =>
    bind_issues (under_issues _ (resolveOperand_issue dqs scope misuse operand)) fun _ _ failed => by
      cases failed
  | .positive operand =>
    bind_issues (under_issues _ (resolveOperand_issue dqs scope misuse operand)) fun _ _ failed => by
      cases failed
  | .negate operand => by
    have ih := resolveOperand_issue dqs scope misuse operand
    cases operand with
    | numeric text => exact map_issues _ (queryNumeric_issues _ _)
    | _ => exact bind_issues (under_issues _ ih) fun _ _ failed => by cases failed

/-- For every setting, column list, flag, start index and argument list, the issues of
{name}`resolveArguments` name no catalog object. Proof sketch: structural recursion on the
list, with {name}`resolveOperand_issue` for each argument. -/
theorem resolveArguments_issue (dqs : Bool) (scope : Scope) (misuse : Bool) :
    (index : Nat) → (arguments : List Syntax.Expr) →
      IssuesNameNoObject (resolveArguments dqs scope misuse index arguments)
  | _, [] => fun _ failed => by cases failed
  | index, argument :: rest =>
    bind_issues (under_issues _ (resolveOperand_issue dqs scope misuse argument)) fun _ =>
      bind_issues (resolveArguments_issue dqs scope misuse (index + 1) rest) fun _ _ failed => by
        cases failed
end

end Belay.Sqlite
