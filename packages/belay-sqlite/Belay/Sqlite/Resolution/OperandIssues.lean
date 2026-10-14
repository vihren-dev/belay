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
catalog object, so do the issues of their sequence. Proof sketch: a failed sequence
failed in the first computation, or in the continuation of its value. -/
theorem bind_issues {first : Except ValueIssue α} {next : α → Except ValueIssue β}
    (left : IssuesNameNoObject first) (right : ∀ value, IssuesNameNoObject (next value)) :
    IssuesNameNoObject (first >>= next) := by
  intro issue failed
  cases first with
  | error inner => cases failed; exact left _ rfl
  | ok value => exact right value issue failed

/-- For every computation and path: if its issues name no catalog object, so do its
issues under the path. Proof sketch: a path changes only the location of a
restriction ({name}`ValueIssue.under_namesNoObject`). -/
theorem under_issues {result : Except ValueIssue α} (path : List Nat) (issues : IssuesNameNoObject result) :
    IssuesNameNoObject (result.mapError (·.under path)) := by
  intro issue failed
  cases result with
  | error inner => cases failed; exact ValueIssue.under_namesNoObject _ _ (issues _ rfl)
  | ok _ => cases failed

/-- For every path and operand computation: if its issues name no catalog object, so
do the issues of {name}`condition`. Proof sketch: {name}`condition` passes an issue on
under the path, and adds only a restriction. -/
theorem condition_issues (path : List Nat) {result : Except ValueIssue Operand}
    (issues : IssuesNameNoObject result) : IssuesNameNoObject (condition path result) := by
  intro issue failed
  cases result with
  | error inner => cases failed; exact ValueIssue.under_namesNoObject _ _ (issues _ rfl)
  | ok operand => simp only [condition] at failed; split at failed <;> cases failed; trivial

/-- For every value computation and function: mapping the value keeps the issues.
Proof sketch: a failed map is the failed computation. -/
theorem map_issues {result : Except ValueIssue α} (function : α → β) (issues : IssuesNameNoObject result) :
    IssuesNameNoObject (result.map function) := by
  intro issue failed
  cases result with
  | error inner => cases failed; exact issues _ rfl
  | ok _ => cases failed

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

/-- For every setting, column list, flag and expression, the issues of
{name}`resolveOperand` name no catalog object. Proof sketch: induction on the
expression. A compound expression sequences its operands with {name}`bind_issues`,
{name}`under_issues` and {name}`condition_issues`, and fails itself only with a
restriction; a leaf gives {lit}`no such column`, {lit}`ambiguous column name`, a restriction,
{name}`queryNumeric_issues` or {name}`callIssues`. -/
theorem resolveOperand_issue (dqs : Bool) (scope : Scope) (misuse : Bool)
    (expression : Syntax.Expr) : IssuesNameNoObject (resolveOperand dqs scope misuse expression) := by
  have pair_match : ∀ (a b : Operand) (build : Resolved.Expr → Resolved.Expr → Resolved.Expr)
      (shift : List Nat → List Nat), IssuesNameNoObject (match affinityIssue a b with
        | some (path, reason) => (Except.error (.restriction (shift path) reason) : Except ValueIssue Operand)
        | none => .ok (build a.1 b.1, none)) := by
    intro a b build shift issue failed
    split at failed <;> cases failed; trivial
  induction expression with
  | null | string _ | blob _ | currentTime _ =>
    intro issue failed; simp only [resolveOperand] at failed; cases failed <;> trivial
  | numeric text => exact map_issues _ (queryNumeric_issues _ _)
  | identifier name doubleQuoted =>
    intro issue failed
    simp only [resolveOperand] at failed
    repeat' split at failed
    all_goals (cases failed <;> simp [ValueIssue.namesNoObject, PrepareError.namesObject])
  | qualified source column =>
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
  cases h : resolveOperand dqs [] true expression with
  | error cause => rw [h] at failed; cases failed; exact resolveOperand_issue dqs [] true expression _ h
  | ok _ => rw [h] at failed; cases failed

/-- For every list of computations whose issues name no catalog object, the issues of
their concatenation in order name none. Proof sketch: induction on the list, with
{name}`bind_issues` at each element. -/
theorem concat_issues (results : List (Except ValueIssue (List β)))
    (each : ∀ result ∈ results, IssuesNameNoObject result) :
    IssuesNameNoObject (results.foldr (fun next rest => do let first ← next; let others ← rest; .ok (first ++ others))
      (.ok [])) := by
  induction results with
  | nil => intro issue failed; cases failed
  | cons head tail ih =>
    exact bind_issues (each head (by simp)) fun _ =>
      bind_issues (ih fun result member => each result (by simp [member])) fun _ _ failed => by cases failed

/-- For every scope, the issues of {name}`sourceStarColumns` name no catalog object: the
only one is {name}`PrepareError.noSuchSource`. -/
theorem sourceStarColumns_issues (scope : Scope) (source : String) :
    IssuesNameNoObject (sourceStarColumns scope source) := by
  intro issue failed
  unfold sourceStarColumns at failed
  split at failed <;> cases failed
  simp [ValueIssue.namesNoObject, PrepareError.namesObject]

/-- For every scope, the issues of one {lit}`RETURNING` column name no catalog
object. Proof sketch: {lit}`source.*` has the issues of {name}`sourceStarColumns_issues`,
and an expression has the issues of {name}`resolveOperand` under a path. -/
theorem returningColumn_issues (dqs : Bool) (scope : Scope) (item : Nat)
    (column : Syntax.ResultColumn) : IssuesNameNoObject (returningColumn dqs scope item column) := by
  cases column with
  | star => intro issue failed; cases failed
  | sourceStar source => exact sourceStarColumns_issues scope source
  | expression value alias text =>
    simp only [returningColumn]
    exact bind_issues (under_issues _ (resolveOperand_issue _ _ _ _)) fun operand _ failed => by
      obtain ⟨_, _⟩ := operand; cases failed

/-- For every list of {lit}`RETURNING` columns, the issues of
{name}`resolveReturning` name no catalog object. Proof sketch:
{name}`concat_issues` with {name}`returningColumn_issues` for each column. -/
theorem resolveReturning_issue (dqs : Bool) (scope : Scope) (items : List Syntax.ResultColumn) :
    IssuesNameNoObject (resolveReturning dqs scope items) := by
  apply concat_issues
  intro result member
  obtain ⟨index, bound, equal⟩ := List.mem_mapIdx.1 member
  exact equal ▸ returningColumn_issues _ _ _ _

end Belay.Sqlite
