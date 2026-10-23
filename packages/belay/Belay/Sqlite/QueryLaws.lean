import Belay.Sqlite.Queries

set_option doc.verso true

/-! The laws of {lit}`Holds`, {lit}`Empty` and {lit}`Fails` (ADR 0017, S2): at most one of them holds
for a query and a database, so {lit}`¬ Holds q db` follows from {lit}`Empty q db` and from
{lit}`Fails q db`. None of them holds when the output is {lit}`Output.unmodeled`, so the three do
not cover every case. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every query {lit}`q` and database {lit}`db`: if {name}`Holds` of {lit}`q` on {lit}`db`
holds, then {name}`Empty` of {lit}`q` on {lit}`db` does not. Proof sketch: both read the same output,
and {name}`Output.hasRows_not_hasNoRows`. -/
theorem Holds.not_empty {q : Script} {db : Database} {query : q.isQuery = true}
    (holds : Holds q db query) : ¬ Empty q db query := by
  unfold Holds Empty at *
  cases output : q.outputOn db with
  | none => simp [output] at holds
  | some value =>
    simp only [output, Option.any_some] at holds ⊢
    simp [Output.hasRows_not_hasNoRows value holds]

/-- For every query {lit}`q` and database {lit}`db`: if {name}`Holds` of {lit}`q` on {lit}`db`
holds, then {name}`Fails` of {lit}`q` on {lit}`db` does not. Proof sketch: both read the same output,
and {name}`Output.hasRows_not_isError`. -/
theorem Holds.not_fails {q : Script} {db : Database} {query : q.isQuery = true}
    (holds : Holds q db query) : ¬ Fails q db query := by
  unfold Holds Fails at *
  cases output : q.outputOn db with
  | none => simp [output] at holds
  | some value =>
    simp only [output, Option.any_some] at holds ⊢
    simp [Output.hasRows_not_isError value holds]

/-- For every query {lit}`q` and database {lit}`db`: if {name}`Empty` of {lit}`q` on {lit}`db`
holds, then {name}`Fails` of {lit}`q` on {lit}`db` does not. Proof sketch: both read the same output,
and {name}`Output.hasNoRows_not_isError`. -/
theorem Empty.not_fails {q : Script} {db : Database} {query : q.isQuery = true}
    (empty : Empty q db query) : ¬ Fails q db query := by
  unfold Empty Fails at *
  cases output : q.outputOn db with
  | none => simp [output] at empty
  | some value =>
    simp only [output, Option.any_some] at empty ⊢
    simp [Output.hasNoRows_not_isError value empty]

end Belay.Sqlite
