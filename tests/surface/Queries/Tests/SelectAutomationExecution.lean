import Belay

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! ADR 0027 checks of the existing execution contract: all selected outputs must
satisfy success, while modeled errors and unsupported stops remain distinct. -/

namespace SelectAutomationExecution
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- Two non-NULL values, for a query whose one-row window has two permitted results. -/
def sample : Database := db! r"
  CREATE TABLE items(value INTEGER NOT NULL);
  INSERT INTO items VALUES (1), (2);"

/-- The actual SQL program used for alternative-result checks. -/
def readOne : Sql (Except Nat (List (List Value))) := query (sql r"SELECT value FROM items LIMIT 1")

/-- A successful result has one row and only non-NULL cells; errors do not satisfy it. -/
def successfulOne (result : Except Nat (List (List Value))) : Prop :=
  match result with
  | .ok rows => rows.length = 1 ∧ ∀ row ∈ rows, ∀ cell ∈ row, cell ≠ .null
  | .error _ => False

/-- The finite success predicate is decidable for the concrete execution probes. -/
instance (result : Except Nat (List (List Value))) : Decidable (successfulOne result) := by
  cases result <;> simp only [successfulOne] <;> infer_instance

/-- Every branch of the actual SELECT succeeds with one non-NULL row. This includes
the raw alternatives wrapper and every listed concrete output, by {name}`Sql.check`. -/
theorem all_choices_succeed :
    readOne.check (fun result _ => successfulOne result) (ExecutionContext.initial sample {}) := by
  decide +kernel

/-- The pure representative is not enough: some permitted branch returns the second
value, so the universal execution claim that every result is the first value is false. -/
theorem representative_is_insufficient :
    ¬ readOne.check (fun result _ => result = .ok [[.integer 1]])
      (ExecutionContext.initial sample {}) := by
  decide +kernel

/-- A malformed JSON expression gives a modeled SQL error. -/
def failingRead : Sql (Except Nat (List (List Value))) := query (sql r"SELECT json_extract('invalid', '$')")

/-- The error cannot satisfy a success postcondition. A conditional claim that requires
False only on success does hold, showing why such a claim alone does not prove success. -/
theorem error_is_not_success :
    ¬ failingRead.check (fun result _ => successfulOne result) (ExecutionContext.initial sample {}) ∧
    failingRead.check (fun result _ => result.toOption = none)
      (ExecutionContext.initial sample {}) := by
  decide +kernel

/-- Every program satisfies a triple with false precondition, including this failing
query. Such a triple is not evidence that any database meets a usable schema premise.
Proof sketch: the precondition supplies False before any execution obligation. -/
theorem false_precondition :
    ⦃fun _ => ⌜False⌝⦄ failingRead ⦃⇓ result _ => ⌜successfulOne result⌝⦄ := by
  exact fun _ impossible => impossible.elim

/-- An unsupported step cannot check even the true postcondition at any context where
the step stops. Proof sketch: the existing stopped-branch law rejects its actual branch. -/
theorem unsupported_is_not_vacuous {statement : Syntax.Statement} {values : List Value}
    {state : ExecutionContext} {reason : String}
    (stopped : runScriptStep runContext state.clock state.index state.connection statement values =
      .ended reason) :
    ¬ (Sql.exec statement values (fun output => .pure (queryResult output))).check
      (fun _ _ => True) state :=
  Sql.check_stopped stopped _

/-- A SELECT preparation error is a modeled error, not an unsupported stop or successful
empty result. Its error observation can satisfy an error-aware postcondition. -/
theorem preparation_error :
    (query (sql r"SELECT absent FROM missing")).check (fun result _ => result = .error 1)
      (ExecutionContext.initial sample {}) := by
  decide +kernel

/-- A continuing context has a prefix, nonzero index, clock, counters and transaction. -/
def prior : ExecutionContext :=
  { clock := some (fun index => 212602449600000 + 86400000 * index)
    index := 7
    connection := {
      foreignKeys := true
      recursiveTriggers := true
      state := { database := sample.raw, snapshot := some sample.raw, counters := { changes := some 7 } } }
    outputs := [.done 3] }

/-- Every selected result reads the existing counter and statement clock. The next
context retains the prefix, settings and open transaction, advances the index once,
and retains the same clock at the next index. This is not a fresh-run claim. -/
theorem continuing_context :
    (query (sql r"SELECT changes(), CURRENT_TIMESTAMP FROM items LIMIT 1")).check
      (fun result final => result = .ok [[.integer 7, ("2025-01-08 00:00:00" : String)]] ∧
        final.index = 8 ∧ final.outputs.head? = some (.done 3) ∧
        final.connection.foreignKeys = true ∧ final.connection.recursiveTriggers = true ∧
        final.connection.state.snapshot.isSome = true ∧
        final.connection.state.counters.changes = some 7 ∧
        final.clock.map (fun clock => clock 8) = some (212602449600000 + 86400000 * 8)) prior := by
  decide +kernel

/-- The raw alternatives wrapper is a required observation. A postcondition that
accepts both concrete rows but refuses the wrapper still fails the SELECT check. -/
theorem raw_wrapper_required :
    ¬ (send (sql r"SELECT value FROM items LIMIT 1")).check
      (fun outputs _ => outputs = [.rows [[.integer 1]]] ∨ outputs = [.rows [[.integer 2]]]) prior := by
  decide +kernel

#print axioms all_choices_succeed
#print axioms representative_is_insufficient
#print axioms error_is_not_success
#print axioms false_precondition
#print axioms unsupported_is_not_vacuous
#print axioms preparation_error
#print axioms continuing_context
#print axioms raw_wrapper_required

end SelectAutomationExecution
