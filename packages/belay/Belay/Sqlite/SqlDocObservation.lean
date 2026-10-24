import Belay.Sqlite.Run

set_option doc.verso true

/-! Observations for checked SQL documentation. Text compares the headerless cell display;
typed expectations retain storage classes, statement boundaries and change counts. -/

namespace Belay.Sqlite.SqlDoc

/-- The observation a checked example promises. Choose the complete output list when result
types, empty result sets, statement boundaries or write counts matter. -/
inductive Expectation where
  /-- Rows in statement order, cells separated by {lit}` | ` and rows by newlines.
  This display preserves cell contents but can identify different typed outputs. -/
  | text (expected : String)
  /-- The complete output list, including every alternative of {name}`Output.oneOf`. -/
  | outputs (expected : List Output)

/-- Why an ordinary checked observation fails. Statement positions are zero-based.
SQL failures and restrictions stay distinct so a caller can handle expected SQL failures. -/
inductive Failure where
  /-- An executed statement returned an SQL error, which normal expectations reject. -/
  | sqlError (index code : Nat)
  /-- A statement is outside the model's described behavior. -/
  | unmodeled (index : Nat) (reason : String)
  /-- A caller supplied an empty alternatives list, which an actual modeled run never gives. -/
  | noAlternatives (index : Nat)
  /-- One permitted rendered result differs from the expected text. -/
  | textMismatch (expected actual : String)
  /-- The complete actual outputs differ from the typed expectation. -/
  | outputsMismatch (expected actual : List Output)
  deriving Repr

/-- A diagnostic that retains the mismatching text or full typed output. Text is quoted to
make leading/trailing spaces, blank lines and embedded newlines visible. -/
def Failure.message : Failure → String
  | .sqlError index code => s!"SQL statement {index + 1} failed with result code {code}"
  | .unmodeled index reason => s!"SQL statement {index + 1} is unmodeled: {reason}"
  | .noAlternatives index => s!"SQL statement {index + 1} has no permitted result"
  | .textMismatch expected actual =>
    s!"SQL result mismatch\nexpected text: {repr expected}\nactual text: {repr actual}"
  | .outputsMismatch expected actual =>
    s!"SQL output mismatch\nexpected outputs: {repr expected}\nactual outputs: {repr actual}"

/-- Check that every output is a successful modeled observation. Errors, restrictions and
empty alternative lists fail at their first statement. An empty output list succeeds. -/
def validateOutputs (outputs : List Output) : Except Failure Unit := do
  for (output, index) in outputs.zipIdx do
    match output with
    | .error code => throw (.sqlError index code)
    | .unmodeled reason => throw (.unmodeled index reason)
    | .oneOf [] => throw (.noAlternatives index)
    | .rows _ | .done _ | .oneOf (_ :: _) => pure ()

/-- Render each row without headers, padding or trimming. Keep an empty row as an empty
line, which differs from no rows when another statement contributes text. -/
def rowLines (rows : List (List Value)) : List String :=
  rows.map fun row => " | ".intercalate (row.map Belay.Sqlite.Model.Value.cellText)

/-- Every permitted text observation of the complete output list. This takes every choice
of rows at each {name}`Output.oneOf`, preserves statement order, and omits successful write
counts. It rejects the same failures as {name}`validateOutputs`. For no outputs it gives
one empty observation. Only the final join removes result-set boundaries; cell text is intact. -/
def renderedAlternatives (outputs : List Output) : Except Failure (List String) := do
  validateOutputs outputs
  let mut alternatives : List (List String) := [[]]
  for output in outputs do
    let rows := match output with
      | .rows rows => [rowLines rows]
      | .oneOf results => results.map rowLines
      | .done _ | .error _ | .unmodeled _ => [[]]
    alternatives := alternatives.flatMap fun earlier => rows.map (earlier ++ ·)
  return alternatives.map ("\n".intercalate ·)

/-- Check explicit observations against an expectation. Text succeeds exactly when every
permitted rendered result equals the expected text; typed checking compares the complete
list. Both modes reject SQL errors, restrictions and empty alternative lists, even when the
typed expectation contains the same failing constructor. -/
def checkOutputs (expectation : Expectation) (outputs : List Output) : Except Failure Unit := do
  match expectation with
  | .text expected =>
    for actual in ← renderedAlternatives outputs do
      if actual != expected then throw (.textMismatch expected actual)
  | .outputs expected =>
    validateOutputs outputs
    if outputs != expected then throw (.outputsMismatch expected outputs)

end Belay.Sqlite.SqlDoc
