import Belay.Sqlite.Queries

set_option doc.verso true

/-! The laws of {lit}`Holds`, {lit}`Empty` and {lit}`Fails` (ADR 0017, S2): at most one of them holds
for a query and a database, so {lit}`¬ Holds q db` follows from {lit}`Empty q db` and from
{lit}`Fails q db`. None of them holds when the output is {lit}`Output.unmodeled`, so the three do
not cover every case. -/

namespace Belay.Sqlite

/-- For each output, {name}`Output.hasRows` and {name}`Output.hasNoRows` are not both true. Proof
sketch: by cases on the output; for {name}`Output.oneOf`, the first result is empty and not
empty. -/
theorem Model.Output.hasRows_not_hasNoRows (output : Output) (rows : output.hasRows = true) :
    output.hasNoRows = false := by
  cases output with
  | rows found => simp_all [Model.Output.hasRows, Model.Output.hasNoRows]
  | oneOf results =>
    cases results with
    | nil => simp [Model.Output.hasRows] at rows
    | cons first rest => simp_all [Model.Output.hasRows, Model.Output.hasNoRows]
  | done _ | error _ | unmodeled _ => simp [Model.Output.hasRows] at rows

/-- For every query {lit}`q` and database {lit}`db`: if {name}`Holds` of {lit}`q` on {lit}`db`
holds, then {name}`Empty` of {lit}`q` on {lit}`db` does not. Proof sketch: both read the same output,
and {name}`Model.Output.hasRows_not_hasNoRows`. -/
theorem Holds.not_empty {q : Script} {db : Database} {query : q.isQuery = true}
    (holds : Holds q db query) : ¬ Empty q db query := by
  unfold Holds Empty at *
  cases output : q.outputOn db with
  | none => simp [output] at holds
  | some value =>
    simp only [output, Option.any_some] at holds ⊢
    simp [Model.Output.hasRows_not_hasNoRows value holds]

/-- For every query {lit}`q` and database {lit}`db`: if {name}`Holds` of {lit}`q` on {lit}`db`
holds, then {name}`Fails` of {lit}`q` on {lit}`db` does not. Proof sketch: an output with rows is not
an error. -/
theorem Holds.not_fails {q : Script} {db : Database} {query : q.isQuery = true}
    (holds : Holds q db query) : ¬ Fails q db query := by
  unfold Holds Fails at *
  cases output : q.outputOn db with
  | none => simp [output] at holds
  | some value => cases value <;> simp_all [Model.Output.hasRows, Output.isError]

/-- For every query {lit}`q` and database {lit}`db`: if {name}`Empty` of {lit}`q` on {lit}`db`
holds, then {name}`Fails` of {lit}`q` on {lit}`db` does not. Proof sketch: an output without rows is
not an error. -/
theorem Empty.not_fails {q : Script} {db : Database} {query : q.isQuery = true}
    (empty : Empty q db query) : ¬ Fails q db query := by
  unfold Empty Fails at *
  cases output : q.outputOn db with
  | none => simp [output] at empty
  | some value => cases value <;> simp_all [Model.Output.hasNoRows, Output.isError]

end Belay.Sqlite
