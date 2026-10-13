import VerifierConformance.Outputs
import Belay.Sqlite.QueryExamples

set_option doc.verso true

/-! Checked examples of a query statement in a script (ADR 0012): it changes nothing,
the script continues, and its output is the result column names and rows. -/

namespace Belay.Sqlite.Conformance.QueryOutputs

open Resolved.QueryExamples in
/-- A database with the example table of {lit}`Belay.Sqlite.Resolved.QueryExamples`
at catalog position 0. -/
def database : Database := fun position => if position = 0 then some table else none

#guard match advance 0 (.query Resolved.QueryExamples.grouped) { database } with
  | .next next => next.database 0 == database 0 && next.snapshot.isNone
  | .halt _ => false
#guard outputTraceFrom 0 [.query Resolved.QueryExamples.plain] { database } ==
  [some ⟨["v"], [[.text [97]], [.text [98]], [.text [99]], [.text [100]]], none⟩]
-- A query whose table is missing has no output.
#guard outputTraceFrom 0 [.query { Resolved.QueryExamples.plain with table := 5 }] { database } == [none]

end Belay.Sqlite.Conformance.QueryOutputs
