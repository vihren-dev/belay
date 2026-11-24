import Belay.Sqlite.Model.Programs.Scripts.QueryOutputFacts
import Belay.Sqlite.Model.Programs.Scripts.ReadOnlyFrame
import Belay.Sqlite.Model.Programs.Scripts.StepRuleAttr

set_option doc.verso true

/-! The exact step of a resolved query and the modeled choices in its output. -/

namespace Belay.Sqlite.Model

/-- For each resolved query, a missing clock or unknown counter ends its step with the
corresponding reason. A query outside the described fragment ends as unmodeled. A missing
source or result also ends the run. A window type mismatch, integer overflow and definite
function fault give their SQLite error codes, in that order. Among the distinct, sorted row
results, no result ends the run, one gives rows, and two or more give a choice. A continuing
query keeps the connection and has no further execution. Proof sketch: the general output
equation and the read-only frame determine the whole step. Expand the output on query data. -/
@[step_rule] theorem runScriptStep_query_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {query : Resolved.Query} {subqueries : List Resolved.Query}
    (found : resolveStatement context connection.resolveState statement = .ok (.query query subqueries, after)) :
    runScriptStep context clock index connection statement parameters =
      let resolved := Resolved.Statement.query query subqueries
      let db := connection.state.database
      match statementClock clock index resolved with
      | none => .ended clockUnmodeled
      | some value => match connection.state.counters.firstUnknown resolved.counterReads with
        | some kind => .ended (counterUnknownReason kind)
        | none =>
          let counters := connection.state.counters.view resolved.counterReads
          if query.described value counters parameters db subqueries then
            match query.runOn value counters parameters db subqueries with
            | none => .ended "the model gives no result for this query"
            | some (_, run) =>
              if run.mismatch then .continued (.error ExecutionError.datatypeMismatch.primaryCode) connection []
              else if run.overflow then .continued (.error ExecutionError.integerOverflow.primaryCode) connection []
              else if run.fault == .must then .continued (.error ExecutionError.functionError.primaryCode) connection []
              else match query.possibleOn value counters parameters db subqueries with
                | none => .ended "the model gives no result for this query"
                | some candidates =>
                  match Resolved.stableSort (fun a b => (compareResults a b).isLE) candidates.eraseDups with
                  | [] => .ended "the model gives no result for this query"
                  | [rows] => .continued (.rows rows) connection []
                  | first :: second :: rest => .continued (.oneOf (first :: second :: rest)) connection []
          else .ended unmodeledHere := by
  let fromOutput : Output → RunStep
    | .unmodeled reason => .ended reason
    | out@(.rows _) | out@(.oneOf _) | out@(.done _) | out@(.error _) => .continued out connection []
  have read : runScriptStep context clock index connection statement parameters =
      fromOutput (resolvedStepOutput clock index connection parameters (.query query subqueries)) := by
    have output := runScriptStep_output context clock index connection statement parameters
    simp only [found] at output
    cases step : runScriptStep context clock index connection statement parameters with
    | ended reason => rw [← output, step]; rfl
    | continued out next others =>
      obtain ⟨rfl, rfl⟩ := runScriptStep_readOnly_keeps found (.inl ⟨_, _, rfl⟩) step
      have ongoing := (runScriptStep_continued step).2
      rw [← output, step]
      cases out <;> first | rfl | cases ongoing
  rw [read]
  dsimp only
  cases clocked : statementClock clock index (.query query subqueries) with
  | none => simp [resolvedStepOutput, clocked, fromOutput]
  | some value =>
    cases known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads with
    | some kind => simp [resolvedStepOutput, clocked, known, fromOutput]
    | none =>
      rw [resolvedStepOutput_query_at clock index connection parameters query subqueries clocked known]
      dsimp only
      generalize connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads = observed
      cases described : query.described value observed parameters connection.state.database subqueries
      · rfl
      · simp only [ite_true, Resolved.Query.outputOn]
        cases ran : query.runOn value observed parameters connection.state.database subqueries with
        | none => rfl
        | some pair =>
          obtain ⟨source, run⟩ := pair
          dsimp only
          cases mismatch : run.mismatch <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> try rfl
          cases overflow : run.overflow <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> try rfl
          cases fault : run.fault == .must <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> try rfl
          cases possible : query.possibleOn value observed parameters connection.state.database subqueries with
          | none => rfl
          | some candidates =>
            simp only [Output.ofResults]
            cases sorted : Resolved.stableSort (fun a b => (compareResults a b).isLE) candidates.eraseDups with
            | nil => rfl
            | cons first rest => cases rest <;> rfl

end Belay.Sqlite.Model
