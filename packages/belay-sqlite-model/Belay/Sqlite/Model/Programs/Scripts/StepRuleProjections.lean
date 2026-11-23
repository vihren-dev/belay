import Belay.Sqlite.Model.Programs.Scripts.ScriptRun

set_option doc.verso true

/-! The projections of a kind rule (statement rule pilot). A kind rule gives the step of every statement that
resolves to its kind as an equation {lit}`runScriptStep … = result`, where {lit}`result` is a term that reads the
connection, the database and the counters. The theorems of this module read a fact about the step from such an
equation and a fact about {lit}`result`. They do not depend on the kind, so one theorem serves the rules of all
kinds. A fact about {lit}`result` usually follows by {lit}`split` on its cases. -/

namespace Belay.Sqlite.Model

/-- Whether a step of a statement continues the run. The Boolean form lets a closed check compute it
for every clock and every counter, which an existence statement does not. -/
def RunStep.continues : RunStep → Bool
  | .continued .. => true
  | .ended _ => false

/-- For every step, it continues exactly when some output, next connection and list of further
executions give it. Proof sketch: case split on the step. -/
theorem RunStep.continues_iff {step : RunStep} :
    step.continues = true ↔ ∃ output next others, step = .continued output next others := by
  cases step <;> simp [RunStep.continues]

/-- The property holds for the output, the next connection and the further executions of a step that
continues. A step that ends requires nothing. For example, {lean}`RunStep.Continuing (fun _ _ others => others = []) (.ended "x")`
holds. Use it to state what every continuing case of the result of a kind rule gives. -/
def RunStep.Continuing (property : Output → Connection → List StatementExecution → Prop) : RunStep → Prop
  | .continued output next others => property output next others
  | .ended _ => True

/-- For every property of continuing cases, decidable condition and two steps {lit}`yes` and {lit}`no`: if the
continuing case of {lit}`yes` meets the property whenever the condition holds, and the continuing case of {lit}`no`
meets it whenever the condition fails, then the continuing case of {lit}`if condition then yes else no` meets it
({name}`RunStep.Continuing`). A selected step that ends the run requires nothing. {lit}`sql_run` uses it to split a
kind rule on its conditions. Proof sketch: case split on the condition. -/
theorem RunStep.continuing_ite {property : Output → Connection → List StatementExecution → Prop} {condition : Prop}
    [Decidable condition] {yes no : RunStep} (whenYes : condition → yes.Continuing property)
    (whenNo : ¬condition → no.Continuing property) : (if condition then yes else no).Continuing property := by
  by_cases holds : condition
  · simpa [holds] using whenYes holds
  · simpa [holds] using whenNo holds

/-- The partial form of a rule. For every two steps {lit}`step` and {lit}`result`, property, output, next
connection and further executions: if {lit}`step = result` (a kind rule), the property holds for each continuing
case of {lit}`result` ({name}`RunStep.Continuing`), and {lit}`step` continues with the output, the connection and
the executions, then the property holds for them. The theorem requires nothing of a step that ends. Proof
sketch: substitute the two equations. -/
theorem RunStep.of_rule {step result : RunStep} (rule : step = result)
    {property : Output → Connection → List StatementExecution → Prop} (holds : result.Continuing property)
    {output : Output} {next : Connection} {others : List StatementExecution}
    (continued : step = .continued output next others) : property output next others := by
  subst rule
  subst continued
  exact holds

/-- For every two steps {lit}`step` and {lit}`result`: if {lit}`step = result` (a kind rule) and {lit}`result`
continues ({name}`RunStep.continues`), then {lit}`step` continues with some output, next connection and further
executions. Proof sketch: rewrite with the rule and use {name}`RunStep.continues_iff`. -/
theorem RunStep.continued_of_rule {step result : RunStep} (rule : step = result)
    (continues : result.continues = true) : ∃ output next others, step = .continued output next others :=
  RunStep.continues_iff.1 (rule ▸ continues)

/-- For every two steps {lit}`step` and {lit}`result`: if {lit}`step = result` (a kind rule) and {lit}`step`
continues ({name}`RunStep.continues`), then {lit}`result` continues. It carries a fact about the step, such as one
that a closed check computes, to the form that the kind rule gives. Proof sketch: rewrite with the rule. -/
theorem RunStep.continues_of_rule {step result : RunStep} (rule : step = result) (continues : step.continues = true) :
    result.continues = true :=
  rule ▸ continues

/-- For every two steps {lit}`step` and {lit}`result`, output, next connection and further executions: if
{lit}`step = result` (a kind rule), every continuing case of {lit}`result` has no further execution, and
{lit}`step` continues with the output, the connection and the executions, then there is no further execution.
Proof sketch: {name}`RunStep.of_rule`. -/
theorem RunStep.others_of_rule {step result : RunStep} (rule : step = result)
    (single : result.Continuing fun _ _ others => others = []) {output : Output} {next : Connection}
    {others : List StatementExecution} (continued : step = .continued output next others) : others = [] :=
  RunStep.of_rule rule single continued

/-- For every two steps {lit}`step` and {lit}`result`, output, next connection, further executions and list of
results: if {lit}`step = result` (a kind rule), the output of no continuing case of {lit}`result` is a choice
between results, and {lit}`step` continues with the output, the connection and the executions, then the output
is not {lit}`.oneOf` of the list. Proof sketch: {name}`RunStep.of_rule`. -/
theorem RunStep.ne_oneOf_of_rule {step result : RunStep} (rule : step = result)
    (plain : result.Continuing fun output _ _ => ∀ results, output ≠ .oneOf results) {output : Output}
    {next : Connection} {others : List StatementExecution} (continued : step = .continued output next others)
    (results : List (List (List Value))) : output ≠ .oneOf results :=
  RunStep.of_rule rule plain continued results

/-- For every two steps {lit}`step` and {lit}`result`, output, next connection and further executions: if
{lit}`step = result` (a kind rule), the output of no continuing case of {lit}`result` is an error
({name}`Output.isError`), and {lit}`step` continues with the output, the connection and the executions, then
the output is not an error. Use it for a kind, or a case of a kind, that cannot fail. Proof sketch:
{name}`RunStep.of_rule`. -/
theorem RunStep.isError_of_rule {step result : RunStep} (rule : step = result)
    (quiet : result.Continuing fun output _ _ => output.isError = false) {output : Output} {next : Connection}
    {others : List StatementExecution} (continued : step = .continued output next others) :
    output.isError = false :=
  RunStep.of_rule rule quiet continued

end Belay.Sqlite.Model
