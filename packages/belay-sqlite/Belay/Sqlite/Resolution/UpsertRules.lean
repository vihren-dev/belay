import Belay.Sqlite.Resolution.UpdateRules

set_option doc.verso true

/-! The prepare-error rule for the {lit}`ON CONFLICT` clauses of INSERT: their issues
name no catalog object. See {lit}`Belay.Sqlite.Resolution.PrepareSpec` for the rule and
its references. -/

namespace Belay.Sqlite

/-- For every column list, key list and target names, the issues of {name}`targetKey`
name no catalog object. Proof sketch: a name fails only with
{name}`PrepareError.noSuchColumn`, and the key search only with
{name}`PrepareError.conflictTargetMismatch`. -/
theorem targetKey_issues (columns : List CatalogColumn) (keys : List (List Nat)) (names : List String) :
    IssuesNameNoObject (targetKey columns keys names) := by
  unfold targetKey
  apply bind_issues
  · intro issue failed
    refine resolveAll_issue _ _ _ (fun _ name issue failed => ?_) failed
    split at failed <;> cases failed
    simp [ValueIssue.namesNoObject, PrepareError.namesObject]
  · intro positions issue failed
    split at failed <;> cases failed
    simp [ValueIssue.namesNoObject, PrepareError.namesObject]

/-- For every setting, scope, key list, clause position, target flag and action, the
issues of {name}`resolveConflictAction` name no catalog object. Proof sketch: the
assignments by {name}`resolveAssignment_issues`, the filter by {name}`condition_issues`,
and the remaining checks give only restrictions. -/
theorem resolveConflictAction_issues (dqs : Bool) (scope : Scope) (keys : List (List Nat)) (clause : Nat)
    (targeted : Bool) (action : Syntax.ConflictAction) :
    IssuesNameNoObject (resolveConflictAction dqs scope keys clause targeted action) := by
  cases action with
  | nothing => intro issue failed; cases failed
  | update assignments filter =>
    apply bind_issues
    · exact under_issues _ fun issue failed =>
        resolveAll_issue _ _ _ (fun _ _ _ h => resolveAssignment_issues _ _ _ _ _ _ h) failed
    · intro resolved
      apply bind_issues
      · cases filter with
        | none => intro issue failed; cases failed
        | some term => exact map_issues _ (condition_issues _ (resolveOperand_issue _ _ _ _))
      · intro resolvedFilter issue failed
        split at failed
        · cases failed; trivial
        · split at failed <;> cases failed; trivial

/-- For every setting, table name, table, key list, clause position and clause, the
issues of {name}`resolveConflict` name no catalog object. Proof sketch: the target by
{name}`targetKey_issues` and the action by {name}`resolveConflictAction_issues`. -/
theorem resolveConflict_issues (dqs : Bool) (tableName : String) (table : CatalogTable)
    (keys : List (List Nat)) (clause : Nat) (written : Syntax.ConflictClause) :
    IssuesNameNoObject (resolveConflict dqs tableName table keys clause written) := by
  apply bind_issues
  · cases written.target with
    | none => intro issue failed; cases failed
    | some names => exact under_issues _ (map_issues _ (targetKey_issues _ _ _))
  · intro target
    apply bind_issues (resolveConflictAction_issues _ _ _ _ _ _)
    intro action issue failed
    cases failed

end Belay.Sqlite
