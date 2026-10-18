import Belay.Sqlite.Resolution.OperandIssues

set_option doc.verso true

/-! The issues of {lit}`RETURNING` resolution name no catalog object (ADR 0012, slice
3a): each column is a query expression ({lit}`resolveOperand_issue`). -/

namespace Belay.Sqlite

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

/-- For every scope, the issues of one {lit}`RETURNING` column name no catalog
object. Proof sketch: {lit}`source.*` is {name}`PrepareError.returningSourceStar`, which
names none, and an expression has the issues of {name}`resolveOperand` under a path. -/
theorem returningColumn_issues (dqs : Bool) (scope : Scope) (item : Nat)
    (column : Syntax.ResultColumn) : IssuesNameNoObject (returningColumn dqs scope item column) := by
  cases column with
  | star => intro issue failed; cases failed
  | sourceStar source =>
    intro issue failed; cases failed; simp [ValueIssue.namesNoObject, PrepareError.namesObject]
  | expression value alias text =>
    simp only [returningColumn]
    exact bind_issues (under_issues _ (resolveOperand_issue _ _ _ _)) fun operand _ failed => by
      obtain ⟨_, _⟩ := operand; cases failed

/-- For every list of {lit}`RETURNING` columns, the issues of
{name}`resolveReturning` name no catalog object. Proof sketch: a {lit}`source.*` column
gives {name}`PrepareError.returningSourceStar`, which names none; otherwise
{name}`concat_issues` with {name}`returningColumn_issues` for each column. -/
theorem resolveReturning_issue (dqs : Bool) (scope : Scope) (items : List Syntax.ResultColumn) :
    IssuesNameNoObject (resolveReturning dqs scope items) := by
  unfold resolveReturning
  split
  · intro issue failed; cases failed; simp [ValueIssue.namesNoObject, PrepareError.namesObject]
  apply concat_issues
  intro result member
  obtain ⟨index, bound, equal⟩ := List.mem_mapIdx.1 member
  exact equal ▸ returningColumn_issues _ _ _ _

end Belay.Sqlite
