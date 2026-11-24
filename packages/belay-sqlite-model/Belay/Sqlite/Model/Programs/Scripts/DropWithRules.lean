import Belay.Sqlite.Model.Programs.Scripts.WriteRuleProofs

set_option doc.verso true

/-! The exact DROP step with the resolved write programs of its implicit deletion. -/

namespace Belay.Sqlite.Model

/-- For any context, clock, index, connection and bound values, suppose resolution gives a DROP
with write rules. A missing required clock or unknown counter ends the run. Unsupported key
or trigger work ends it as unmodeled. A successful drop reports zero changes, installs the
database produced by the programs and applies their counts. An unmodeled effect ends the
step. Each modeled refusal reports its primary code and applies its counts and conflict
algorithm. Each continuing step has one execution. Proof sketch: the support, effect and counts
come from {name}`dropKeys`; a successful DDL output reports zero. -/
@[step_rule] theorem runScriptStep_dropWithRules_eq {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {positions : List Nat} {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions (some rules), after)) :
    runScriptStep context clock index connection statement parameters =
      let stmt := Resolved.Statement.drop positions (some rules)
      match statementClock clock index stmt with
      | none => .ended clockUnmodeled
      | some value => match connection.state.counters.firstUnknown stmt.counterReads with
        | some kind => .ended (counterUnknownReason kind)
        | none =>
          let result := dropKeys rules value positions connection.state.database
          if result.ready then
            match result.effect with
            | .ok database => .continued (.done 0) (connection.afterWrite database result.counts) []
            | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere
              else .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached result.counts) []
          else .ended unmodeledHere := by
  let stmt := Resolved.Statement.drop positions (some rules)
  have ordinary : stmt.isControl = false := rfl
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  apply runScriptStep_of_clock_counter found
  intro value known
  let run := connection.state.statementRun value parameters stmt
  have observed (db : Database) (effect : run.effect = .ok db) :
      Output.ofStep value parameters stmt connection.state run (advanceRun index stmt connection.state run) = .done 0 := by
    rw [advanceRun_ordinary _ _ _ _ ordinary, effect]
    rfl
  dsimp only
  rw [ranScriptStep_write (output := .done 0) ordinary same (connection.state.statementRun_alternatives value parameters stmt none rfl)
    (by intro reason bad; cases bad) observed]
  simp only [stmt, SqlState.statementRun, runStatement, known, Option.isNone_none, Bool.and_true, Option.map_some,
    StatementRun.withKeys, Bool.true_and]
  rfl

end Belay.Sqlite.Model
