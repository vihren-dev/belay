import SqliteVerifier.Library

/-! Human-reviewable engineering requirements, independent of candidate inputs. -/
namespace Requirements

/-- Every invoice rowid and selected amount is an approved logical observation. -/
abbrev LogicalState := SqliteVerifier.LogicalRows

/-- Permit precisely the expected third-statement error and preserve invoice observations. -/
def contract : SqliteVerifier.LogicalContract LogicalState where
  valid := fun _ => True
  change := Eq
  catalogRequirement catalog := catalog.columnsOf (name! "invoices") =
    some [{ name := name! "amount", declaredType := some "INTEGER" }, { name := name! "note", declaredType := some "TEXT" }]
  failure := fun before _ _ after => before = after
  applicability := fun _ outcome =>
    match outcome with
    | .failure 2 (.prepare (.tableExists (name! "audit"))) _ => True
    | _ => False

end Requirements
