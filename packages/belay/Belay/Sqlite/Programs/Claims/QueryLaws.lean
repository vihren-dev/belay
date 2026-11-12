import Belay.Sqlite.Programs.Scripts.QueryObservations

set_option doc.verso true

/-! The laws of {lit}`Holds`, {lit}`Empty` and {lit}`Fails` (ADR 0017, S2): at most one of them holds
for a query and a database, so {lit}`¬ Holds q db` follows from {lit}`Empty q db` and from
{lit}`Fails q db`. None of them holds when the output is {lit}`Output.unmodeled`, so the three do
not cover every case. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every query {lit}`q` and database {lit}`db`: if {name}`Holds` of {lit}`q` on {lit}`db`
holds, then {name}`Empty` of {lit}`q` on {lit}`db` does not. Proof sketch: both read the same output
({name}`Script.returnsResult_iff_outputOn`), and the cases of the output. -/
theorem Holds.not_empty {q : Script} {db : Database} {query : q.isQuery = true}
    (holds : Holds q db query) : ¬ Empty q db query := by
  obtain ⟨output, found, holds⟩ :=
    (Script.returnsResult_iff_outputOn query db _).mp holds
  rw [Empty, Script.returnsResult_of_outputOn query found]
  cases output <;> simp_all [Output.returnsResult]
  exact List.exists_mem_of_ne_nil _ holds.1

/-- For every query {lit}`q` and database {lit}`db`: if {name}`Holds` of {lit}`q` on {lit}`db`
holds, then {name}`Fails` of {lit}`q` on {lit}`db` does not. Proof sketch: both read the same output
({name}`Script.returnsResult_iff_outputOn`), and the cases of the output. -/
theorem Holds.not_fails {q : Script} {db : Database} {query : q.isQuery = true}
    (holds : Holds q db query) : ¬ Fails q db query := by
  obtain ⟨output, found, holds⟩ :=
    (Script.returnsResult_iff_outputOn query db _).mp holds
  rw [Fails, Script.returnsError_of_outputOn query found]
  cases output <;> simp_all [Output.returnsResult, Output.returnsError]

/-- For every query {lit}`q` and database {lit}`db`: if {name}`Empty` of {lit}`q` on {lit}`db`
holds, then {name}`Fails` of {lit}`q` on {lit}`db` does not. Proof sketch: both read the same output
({name}`Script.returnsResult_iff_outputOn`), and the cases of the output. -/
theorem Empty.not_fails {q : Script} {db : Database} {query : q.isQuery = true}
    (empty : Empty q db query) : ¬ Fails q db query := by
  obtain ⟨output, found, empty⟩ :=
    (Script.returnsResult_iff_outputOn query db _).mp empty
  rw [Fails, Script.returnsError_of_outputOn query found]
  cases output <;> simp_all [Output.returnsResult, Output.returnsError]

end Belay.Sqlite
