import Belay.Sqlite.Model.Programs.Scripts.Output

set_option doc.verso true

/-! What the output of a query says about its rows, for every result that SQLite may give: which
statements only read, and whether an output has rows or has none. The surface states queries as
propositions with them ({lit}`Holds`, {lit}`Empty` and {lit}`Fails`). -/

namespace Belay.Sqlite.Model

/-- Whether the output says that each result that SQLite may give has a row: rows that are not
empty, or at least one result, of which none is empty. -/
def Output.hasRows : Output → Bool
  | .rows found => !found.isEmpty
  | .oneOf results => !results.isEmpty && results.all (!·.isEmpty)
  | .done _ | .error _ | .unmodeled _ => false

/-- Whether the output says that each result that SQLite may give has no row: rows that are
empty, or at least one result, of which each is empty. -/
def Output.hasNoRows : Output → Bool
  | .rows found => found.isEmpty
  | .oneOf results => !results.isEmpty && results.all (·.isEmpty)
  | .done _ | .error _ | .unmodeled _ => false

/-- For each output, {name}`Output.hasRows` and {name}`Output.hasNoRows` are not both true. Proof
sketch: by cases on the output; for {name}`Output.oneOf`, the first result is empty and not
empty. -/
theorem Output.hasRows_not_hasNoRows (output : Output) (rows : output.hasRows = true) :
    output.hasNoRows = false := by
  cases output with
  | rows found => simp_all [Output.hasRows, Output.hasNoRows]
  | oneOf results =>
    cases results with
    | nil => simp [Output.hasRows] at rows
    | cons first rest => simp_all [Output.hasRows, Output.hasNoRows]
  | done _ | error _ | unmodeled _ => simp [Output.hasRows] at rows

/-- For each output: if {name}`Output.hasRows` is true, then {name}`Output.isError` is false.
Proof sketch: by cases on the output. -/
theorem Output.hasRows_not_isError (output : Output) (rows : output.hasRows = true) : output.isError = false := by
  cases output <;> simp_all [Output.hasRows, Output.isError]

/-- For each output: if {name}`Output.hasNoRows` is true, then {name}`Output.isError` is false.
Proof sketch: by cases on the output. -/
theorem Output.hasNoRows_not_isError (output : Output) (empty : output.hasNoRows = true) : output.isError = false := by
  cases output <;> simp_all [Output.hasNoRows, Output.isError]

/-- {lit}`output.returnsResult Q`: the output is one successful result that has the property
{lit}`Q`, or a nonempty choice of results that all have it. In terms of the formula:

* {name}`Output.rows` with the rows {lit}`rows`: {lit}`Q rows`;
* {name}`Output.oneOf` with the results {lit}`results`: the list is not empty and each result
  in it satisfies {lit}`Q`;
* {name}`Output.done`, {name}`Output.error` and {name}`Output.unmodeled`: false, for every
  {lit}`Q`, also for {lit}`fun _ => True`.

An empty choice is false, not true without a check. For example, {lit}`.rows [[.integer 1]]`
returns a result with one row, and {lit}`.error 1` returns no result. Use
{lit}`fun _ => True` when only success matters. -/
def Output.returnsResult (property : List (List Value) → Prop) : Output → Prop
  | .rows found => property found
  | .oneOf results => results ≠ [] ∧ ∀ result ∈ results, property result
  | .done _ | .error _ | .unmodeled _ => False

/-- {name}`Output.returnsResult` is decidable for each output when its property is decidable: the
check decides the property of the rows, or of each result of a choice. So {lit}`decide` proves a
claim about a computed output. -/
instance (property : List (List Value) → Prop) [DecidablePred property] (output : Output) :
    Decidable (output.returnsResult property) :=
  match output with
  | .rows found => inferInstanceAs (Decidable (property found))
  | .oneOf results => inferInstanceAs (Decidable (results ≠ [] ∧ ∀ result ∈ results, property result))
  | .done _ | .error _ | .unmodeled _ => isFalse id

/-- {lit}`output.returnsError E`: the output is an error ({name}`Output.error`) whose result code
satisfies {lit}`E`. Every other output is false. Use {lit}`fun _ => True` for any error. -/
def Output.returnsError (property : Nat → Prop) : Output → Prop
  | .error code => property code
  | .rows _ | .oneOf _ | .done _ | .unmodeled _ => False

/-- {name}`Output.returnsError` is decidable for each output when its property is decidable: the
check decides the property of the result code of an error. -/
instance (property : Nat → Prop) [DecidablePred property] (output : Output) :
    Decidable (output.returnsError property) :=
  match output with
  | .error code => inferInstanceAs (Decidable (property code))
  | .rows _ | .oneOf _ | .done _ | .unmodeled _ => isFalse id

/-- For each output: {name}`Output.hasRows` is true exactly when the output returns a result that
is not empty ({name}`Output.returnsResult`). Proof sketch: by cases on the output. -/
theorem Output.hasRows_iff_returnsResult (output : Output) :
    output.hasRows = true ↔ output.returnsResult (· ≠ []) := by
  cases output <;> simp [Output.hasRows, Output.returnsResult]

/-- For each output: {name}`Output.hasNoRows` is true exactly when the output returns a result
that is empty ({name}`Output.returnsResult`). Proof sketch: by cases on the output. -/
theorem Output.hasNoRows_iff_returnsResult (output : Output) :
    output.hasNoRows = true ↔ output.returnsResult (· = []) := by
  cases output <;> simp [Output.hasNoRows, Output.returnsResult]

/-- For each output: {name}`Output.isError` is true exactly when the output returns an error with
any code ({name}`Output.returnsError`). Proof sketch: by cases on the output. -/
theorem Output.isError_iff_returnsError (output : Output) :
    output.isError = true ↔ output.returnsError fun _ => True := by
  cases output <;> simp [Output.isError, Output.returnsError]

end Belay.Sqlite.Model
