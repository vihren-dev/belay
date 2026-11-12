import Belay.Sqlite.Model.Programs.Claims.QueryOutputs
import Belay.Sqlite.Model.Queries.Preparation.QueryOutputs
import Belay.Sqlite.Model.Queries.Evaluation.QueryLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every list of results, the results of {name}`Output.ofResults` are the same results as
the list, once each and sorted: some list {lit}`listed` has exactly the members of {lit}`rs`, and
the output is {name}`Output.rows` for one result, {name}`Output.oneOf` for more, and
{name}`Output.unmodeled` for none. Proof sketch: sorting and removing repeats keep the members
({name}`Resolved.stableSort_perm`, {name}`List.mem_eraseDups`). -/
theorem Output.ofResults_listed (rs : List (List (List Value))) :
    ∃ listed : List (List (List Value)), (∀ x, x ∈ listed ↔ x ∈ rs) ∧
      Output.ofResults rs = match listed with
        | [result] => .rows result
        | [] => .unmodeled "the model gives no result for this query"
        | first :: second :: rest => .oneOf (first :: second :: rest) := by
  refine ⟨Resolved.stableSort (fun a b => (compareResults a b).isLE) rs.eraseDups, fun x => ?_, rfl⟩
  rw [(Resolved.stableSort_perm _ _).mem_iff, List.mem_eraseDups]

/-- For every list of results, {name}`Output.ofResults` of it is no error ({name}`Output.isError`
is false). Proof sketch: it is rows, a choice of results, or unmodeled. -/
theorem Output.isError_ofResults (rs : List (List (List Value))) : (Output.ofResults rs).isError = false := by
  obtain ⟨listed, mem, eq⟩ := Output.ofResults_listed rs
  rw [eq]
  match listed with
  | [] => simp [Output.isError]
  | [result] => simp [Output.isError]
  | first :: second :: rest => simp [Output.isError]

end Belay.Sqlite.Model
