import Belay.Sqlite.ProofCostTrace

/-! Checks of the trace reader of the proof-cost collector: exact counts, the Float limit, and the
status of a body node. -/

open Lean Belay.Sqlite Belay.Sqlite.ProofCost

/-- A body trace with the given counters and result. -/
def node (start stop : Float) (result : Option TraceResult := some .success) : MessageData :=
  .trace { cls := `Elab.definition.value, startTime := start, stopTime := stop, result? := result }
    m!"name" #[]

#guard exactCount { cls := `t, startTime := 10, stopTime := 1011 } == some 1001
#guard exactCount { cls := `t, startTime := 0.5, stopTime := 1 } == none
#guard exactCount { cls := `t, startTime := 0, stopTime := 9007199254740992 } == none
#guard exactCount { cls := `t, startTime := 5, stopTime := 4 } == none
#guard (bodyNodes (node 0 0)).map (fun found => (found.label, found.heartbeats.isSome)) == #[("name", true)]
#guard (bodyNodes (node 0 0)).all (·.status == .completed)
#guard (bodyNodes (node 0 0.5)).all (·.status == .precisionUnavailable)
#guard (bodyNodes (node 0 4 (some .error))).all (·.status == .failed)
#guard (bodyNodes (.trace { cls := `other } m!"name" #[])).isEmpty
#eval IO.println "EDGES \"passed\""
