import Belay.Sqlite.Model.StoreValue
import Belay.Sqlite.Model.Resolution.QueryForm

set_option doc.verso true

/-! The window of a query whose {lit}`LIMIT` or {lit}`OFFSET` is a parameter (ADR 0019, slice 1):
when the query starts, SQLite reads the bound values with {lit}`OP_MustBeInt`, which fails the
statement with {lit}`datatype mismatch` for a value that is not an integer. -/

namespace Belay.Sqlite.Model

/-- The integer that SQLite's {lit}`OP_MustBeInt` reads from a {lit}`LIMIT` or {lit}`OFFSET`
value: the integer of the NUMERIC store of the value ({name}`numericStore`) when it is a 64-bit
integer; {lean}`(none : Option Int)`, a {lit}`datatype mismatch`, for every other value.
{assert}`windowInteger (.text [50]) = some 2`, and
{assert}`windowInteger .null = none`. -/
def windowInteger (value : Value) : Option Int :=
  match numericStore value with
  | .integer whole => if fitsInt64Range whole then some whole else none
  | .null | .real _ | .text _ | .blob _ => none

end Belay.Sqlite.Model

namespace Belay.Sqlite.Model.Resolved

/-- The {lit}`LIMIT` of a query with the statement's values: the literal {name}`Query.limit`
without a parameter; for {lit}`LIMIT ?`, the integer of its parameter ({name}`parameterValue`,
{name}`windowInteger`), where a negative integer is no limit. The outer
{lean}`(none : Option (Option Nat))` is a value without an integer. -/
def Query.boundLimit (parameters : List Value) (query : Query) : Option (Option Nat) :=
  match query.limitParameter with
  | none => some query.limit
  | some number => (windowInteger (parameterValue parameters number)).map fun value =>
    if value < 0 then none else some value.toNat

/-- The {lit}`OFFSET` of a query with the statement's values and its bound {lit}`limit`: the literal
{name}`Query.offset` without a parameter; for {lit}`OFFSET ?`, 0 when the {lit}`limit` is 0, because
SQLite then does not read the {lit}`OFFSET`, else the integer of its parameter, where a negative
integer skips no rows. {lean}`(none : Option Nat)` is a value without an integer. -/
def Query.boundOffset (parameters : List Value) (query : Query) (limit : Option Nat) : Option Nat :=
  match query.offsetParameter with
  | none => some query.offset
  | some number =>
    if limit == some 0 then some 0 else (windowInteger (parameterValue parameters number)).map Int.toNat

/-- The query with its window bound to the statement's values, in SQLite's order: SQLite reads the
{lit}`LIMIT` first ({name}`Query.boundLimit`), and the {lit}`OFFSET` only when the {lit}`LIMIT` is
not 0 ({name}`Query.boundOffset`). {lean}`(none : Option Query)` is a {lit}`datatype mismatch`:
a value that SQLite reads is not an integer. The result has no window parameters
({name}`Query.limitParameter` and {name}`Query.offsetParameter` are none), so the readers of
{name}`Query.limit` and {name}`Query.offset` use the bound window. A query without window
parameters is the same query. -/
def Query.bindWindow (parameters : List Value) (query : Query) : Option Query :=
  (query.boundLimit parameters).bind fun limit => (query.boundOffset parameters limit).map fun offset =>
    { query with limit, offset, limitParameter := none, offsetParameter := none }

/-- For every list of values and every query whose {name}`Query.limitParameter` and
{name}`Query.offsetParameter` are none, {name}`Query.bindWindow` gives the same query. -/
theorem Query.bindWindow_literal (parameters : List Value) (query : Query) (limit : query.limitParameter = none)
    (offset : query.offsetParameter = none) : query.bindWindow parameters = some query := by
  cases query
  simp_all [Query.bindWindow, Query.boundLimit, Query.boundOffset]

/-- For every list of values and all queries {lit}`query` and {lit}`bound`, when
{name}`Query.bindWindow` gives {lit}`bound` for {lit}`query`, then {lit}`bound` is {lit}`query` with
some {lit}`limit` and {lit}`offset` and without window parameters: every other field is the same.
Proof sketch: a successful {name}`Query.bindWindow` is a bind of the bound LIMIT and the bound
OFFSET, so the two values that it found are the witnesses, and the record update that it
builds is the stated query. -/
theorem Query.bindWindow_some (parameters : List Value) (query bound : Query)
    (found : query.bindWindow parameters = some bound) :
    ∃ (limit : Option Nat) (offset : Nat),
      bound = { query with limit, offset, limitParameter := none, offsetParameter := none } := by
  simp only [Query.bindWindow, Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
  obtain ⟨limit, -, offset, -, rfl⟩ := found
  exact ⟨limit, offset, rfl⟩

end Belay.Sqlite.Model.Resolved
