import Belay.Sqlite.Resolution.ErrorKinds

set_option doc.verso true

/-! The issues of query expression resolution name no catalog object (ADR 0012,
slice 3a). Constant values in writes are resolved as query expressions, and the
rules for prepare errors of INSERT and UPDATE need this fact. -/

namespace Belay.Sqlite

/-- Every issue of a computation names no catalog object. -/
abbrev IssuesNameNoObject (result : Except ValueIssue α) : Prop :=
  ∀ issue, result = .error issue → issue.namesNoObject

/-- For all computations: if the issues of the first and of every continuation name no
catalog object, so do the issues of their sequence. -/
theorem bind_issues {first : Except ValueIssue α} {next : α → Except ValueIssue β}
    (left : IssuesNameNoObject first) (right : ∀ value, IssuesNameNoObject (next value)) :
    IssuesNameNoObject (first >>= next) := by
  intro issue failed
  cases first with
  | error inner => cases failed; exact left _ rfl
  | ok value => exact right value issue failed

/-- For every computation and path: if its issues name no catalog object, so do its
issues under the path. -/
theorem under_issues {result : Except ValueIssue α} (path : List Nat) (issues : IssuesNameNoObject result) :
    IssuesNameNoObject (result.mapError (·.under path)) := by
  intro issue failed
  cases result with
  | error inner => cases failed; exact ValueIssue.under_namesNoObject _ _ (issues _ rfl)
  | ok _ => cases failed

/-- For every path and operand computation: if its issues name no catalog object, so
do the issues of {name}`condition`. -/
theorem condition_issues (path : List Nat) {result : Except ValueIssue Operand}
    (issues : IssuesNameNoObject result) : IssuesNameNoObject (condition path result) := by
  intro issue failed
  cases result with
  | error inner => cases failed; exact ValueIssue.under_namesNoObject _ _ (issues _ rfl)
  | ok operand => simp only [condition] at failed; split at failed <;> cases failed; trivial

/-- For every value computation and function: mapping the value keeps the issues. -/
theorem map_issues {result : Except ValueIssue α} (function : α → β) (issues : IssuesNameNoObject result) :
    IssuesNameNoObject (result.map function) := by
  intro issue failed
  cases result with
  | error inner => cases failed; exact issues _ rfl
  | ok _ => cases failed

/-- For every literal text and sign, the issues of {name}`queryNumeric` name no
catalog object: the only prepare error is {lit}`hex literal too big`. -/
theorem queryNumeric_issues (text : String) (negated : Bool) : IssuesNameNoObject (queryNumeric text negated) := by
  intro issue failed
  unfold queryNumeric at failed
  dsimp only at failed
  split at failed <;> cases failed <;> simp [ValueIssue.namesNoObject, PrepareError.namesObject]

/-- For every flag and name, the issues of a function call name no catalog object:
{name}`aggregateIssue`, {name}`callIssue` and {name}`pairIssue` give only
{lit}`misuse of aggregate function`, {lit}`wrong number of arguments`, or a restriction. -/
theorem callIssues (misuse : Bool) (name : String) :
    (aggregateIssue misuse name).namesNoObject ∧ (callIssue name).namesNoObject ∧ (pairIssue name).namesNoObject := by
  unfold aggregateIssue callIssue pairIssue unmodeledFunction
  refine ⟨?_, ?_, ?_⟩ <;> split <;> simp [ValueIssue.namesNoObject, PrepareError.namesObject]

/-- For every setting, column list, flag and expression, the issues of
{name}`resolveOperand` name no catalog object. Proof sketch: induction on the
expression. A compound expression sequences its operands with {name}`bind_issues`,
{name}`under_issues` and {name}`condition_issues`, and fails itself only with a
restriction; a leaf gives {lit}`no such column`, a literal issue
({name}`literalValue_issue`), {name}`queryNumeric_issues` or {name}`callIssues`. -/
theorem resolveOperand_issue (dqs : Bool) (columns : List CatalogColumn) (misuse : Bool)
    (expression : Syntax.Expr) : IssuesNameNoObject (resolveOperand dqs columns misuse expression) := by
  have pair_match : ∀ (a b : Operand) (build : Resolved.Expr → Resolved.Expr → Resolved.Expr)
      (shift : List Nat → List Nat), IssuesNameNoObject (match affinityIssue a b with
        | some (path, reason) => (Except.error (.restriction (shift path) reason) : Except ValueIssue Operand)
        | none => .ok (build a.1 b.1, none)) := by
    intro a b build shift issue failed
    split at failed <;> cases failed; trivial
  induction expression with
  | null | string _ | blob _ | currentTime _ =>
    exact map_issues _ (fun issue failed => literalValue_issue _ _ _ failed)
  | numeric text => exact map_issues _ (queryNumeric_issues _ _)
  | identifier name doubleQuoted =>
    intro issue failed
    simp only [resolveOperand] at failed
    repeat' split at failed
    all_goals (cases failed <;> simp [ValueIssue.namesNoObject, PrepareError.namesObject])
  | callStar name =>
    intro issue failed
    simp only [resolveOperand] at failed
    cases failed
    split
    · exact (callIssues misuse name).1
    · exact (callIssues misuse name).2.1
  | call name operand _ =>
    intro issue failed
    simp only [resolveOperand] at failed
    cases failed
    split
    · exact (callIssues misuse name).1
    · exact (callIssues misuse name).2.1
  | equals left right ihl ihr =>
    exact bind_issues (under_issues _ ihl) fun a => bind_issues (under_issues _ ihr) fun b =>
      pair_match a b (Resolved.Expr.compare .eq) id
  | compare operator left right ihl ihr =>
    exact bind_issues (under_issues _ ihl) fun a => bind_issues (under_issues _ ihr) fun b =>
      pair_match a b (Resolved.Expr.compare operator) (List.map (· + 1))
  | and left right ihl ihr =>
    exact bind_issues (condition_issues _ ihl) fun _ => bind_issues (condition_issues _ ihr) fun _ =>
      fun _ failed => by cases failed
  | or left right ihl ihr =>
    exact bind_issues (condition_issues _ ihl) fun _ => bind_issues (condition_issues _ ihr) fun _ =>
      fun _ failed => by cases failed
  | not operand ih => exact bind_issues (condition_issues _ ih) fun _ _ failed => by cases failed
  | isNull operand negated ih => exact bind_issues (under_issues _ ih) fun _ _ failed => by cases failed
  | arithmetic operator left right ihl ihr =>
    exact bind_issues (under_issues _ ihl) fun _ => bind_issues (under_issues _ ihr) fun _ _ failed => by cases failed
  | cast operand typeName ih => exact bind_issues (under_issues _ ih) fun _ _ failed => by cases failed
  | positive operand ih => exact bind_issues (under_issues _ ih) fun _ _ failed => by cases failed
  | callPair name first rest ihf ihr =>
    intro issue failed
    simp only [resolveOperand] at failed
    split at failed
    · exact bind_issues (under_issues _ ihf) (fun _ => bind_issues (under_issues _ ihr) fun _ _ failed => by
        cases failed) issue failed
    · cases failed; exact (callIssues misuse name).2.2
  | negate operand ih =>
    cases operand with
    | numeric text => exact map_issues _ (queryNumeric_issues _ _)
    | _ => exact bind_issues (under_issues _ ih) fun _ _ failed => by cases failed

/-- For every setting and expression, an issue of {name}`constantValue` names no
catalog object. Proof sketch: the issue is one of {name}`resolveOperand`. -/
theorem constantValue_issue (dqs : Bool) (expression : Syntax.Expr) (issue : ValueIssue)
    (failed : constantValue dqs expression = .error issue) : issue.namesNoObject := by
  unfold constantValue at failed
  simp only [Except.map] at failed
  split at failed
  · cases failed; exact resolveOperand_issue _ _ _ _ _ (by assumption)
  · cases failed

/-- For every column list, an issue of {name}`assignedValue` names no catalog object.
Proof sketch: an expression that names a column is a restriction, and every other
expression is a constant, which {name}`constantValue_issue` covers. -/
theorem assignedValue_issue (columns : List CatalogColumn) (dqs : Bool) (expression : Syntax.Expr)
    (issue : ValueIssue) (failed : assignedValue columns dqs expression = .error issue) :
    issue.namesNoObject := by
  unfold assignedValue at failed
  split at failed
  · cases failed; trivial
  · exact constantValue_issue _ _ _ failed

end Belay.Sqlite
