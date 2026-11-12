import Belay.Sqlite.Model.Queries.Evaluation.QueryRun

set_option doc.verso true

namespace Belay.Sqlite.Model

namespace Resolved

/-- Run rule: for every context, query that is no compound, rows and query {lit}`bound` that the
window binds to with the values of the context ({name}`Query.bindWindow`), the run of the query
({name}`Query.run`) is: the result rows of {lit}`bound`; the fault {lean}`Fault.must` when
{lit}`bound` certainly fails ({name}`Query.mustFail`), else {lean}`Fault.may` when it possibly
fails ({name}`Query.mayFail`) or its {lit}`DISTINCT` is uncertain ({name}`Query.distinctCertain`),
else {lean}`Fault.none`; the overflow of {name}`Query.fails`; and no mismatch. Proof sketch: the
definition of {name}`Query.run`. -/
theorem Query.run_single (context : EvalContext) (query : Query) (rows : List (List Value)) {bound : Query}
    (single : query.compound = none) (window : query.bindWindow context.parameters = some bound) :
    query.run context rows =
      { rows := bound.results context rows,
        fault := if bound.mustFail context rows then .must
          else if bound.mayFail context rows || !bound.distinctCertain context rows then .may else .none,
        overflow := bound.fails context rows, mismatch := false } := by
  simp [Query.run, single, window]

/-- For every context, query that is no compound, rows and query {lit}`bound` that the window
binds to: the run has no mismatch, no overflow and no fault exactly when {lit}`bound` has no
failing aggregate ({name}`Query.fails`), does not certainly fail ({name}`Query.mustFail`), does
not possibly fail ({name}`Query.mayFail`), and keeps the same rows for {lit}`DISTINCT` in every
order ({name}`Query.distinctCertain`). Proof sketch: {name}`Query.run_single` and a case split
on the three Booleans of the fault. -/
theorem Query.run_clean_iff (context : EvalContext) (query : Query) (rows : List (List Value)) {bound : Query}
    (single : query.compound = none) (window : query.bindWindow context.parameters = some bound) :
    ((query.run context rows).mismatch = false ∧ (query.run context rows).overflow = false ∧
        (query.run context rows).fault = .none) ↔
      bound.fails context rows = false ∧ bound.mustFail context rows = false ∧
        bound.mayFail context rows = false ∧ bound.distinctCertain context rows = true := by
  rw [Query.run_single context query rows single window]
  cases bound.mustFail context rows <;> cases bound.mayFail context rows <;>
    cases bound.distinctCertain context rows <;> simp

end Resolved

end Belay.Sqlite.Model
