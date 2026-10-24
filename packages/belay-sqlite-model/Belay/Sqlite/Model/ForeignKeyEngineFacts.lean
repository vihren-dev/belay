import Belay.Sqlite.Model.AdmittedWriteLaws
import Belay.Sqlite.Model.RowEngineResultLaws
import Belay.Sqlite.Model.KeysUniqueRowEngine
import Belay.Sqlite.Model.ForeignKeyCounterRun
import Belay.Sqlite.Model.ForeignKeySelfLookup

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- A database is admitted by the profile and has unique declared and indexed keys.
Both facts are needed at intermediate row writes. This permits outstanding foreign-key
violations; their bound belongs to {name}`KeyState.CounterBound`. -/
abbrev Database.ForeignKeyReady (profile : Profile) (database : Database) : Prop := database.Admitted profile ∧ database.KeysUnique
/-- For a fixed profile and catalog, a key state is admitted, has unique keys, and its
foreign-key violation count is at most its immediate counter. Intermediate actions can have
a positive counter; only the publication boundary requires row-reference truth. -/
abbrev KeyState.ForeignKeyInvariant (profile : Profile) (catalog : Catalog) (state : KeyState) : Prop :=
  state.Holds (Database.ForeignKeyReady profile) catalog ∧ state.CounterBound catalog
/-- For a fixed profile and catalog, FAIL states satisfy admission, unique keys and
the counter bound; rollback carriers satisfy admission and unique keys only. Raw errors and
undescribed stops impose nothing, because SQL restores an input or snapshot separately. -/
abbrev KeyStop.ForeignKeyInvariant (profile : Profile) (catalog : Catalog) (stop : KeyStop) : Prop :=
  stop.Holds (Database.ForeignKeyReady profile) catalog ∧ stop.CounterBound catalog

/-- For any two key states with identical rows and immediate counters, the foreign-key
invariant transfers from the second to the first. Bookkeeping fields can differ.
Proof sketch: transfer the database facts by rows and the bound by rows and counter. -/
theorem KeyState.foreignKeyInvariant_of_rows_counter {profile : Profile} {catalog : Catalog} {state other : KeyState}
    (rows : state.rows = other.rows) (counter : state.counter = other.counter) (good : KeyState.ForeignKeyInvariant profile catalog other) :
    KeyState.ForeignKeyInvariant profile catalog state := ⟨KeyState.holds_of_rows rows good.1, good.2.of_rows_counter rows counter⟩

/-- Schema-level conditions for composing foreign-key checks over future row writes:
child scans agree with parent lookups on stored values, selected column keys are checked for
uniqueness, and any accepted self-parent shortcut implies an ordinary singleton lookup. These quantify all applicable links
and future stored values, so value-changing actions need no initial-row-only assumption.
A catalog with no foreign-key links satisfies every field vacuously. -/
structure Catalog.ForeignKeyComparisons (catalog : Catalog) : Prop where
  /-- Every located catalog link compares all stored child/parent rows consistently in scans and lookups. -/
  scans : ∀ link ∈ catalog.foreignKeyLinks, ∀ position key child parent,
    link.parent = .located position key → catalog.tableAt link.child = some child →
    catalog.tableAt position = some parent → link.LookupScanConsistent child parent key
  /-- Every selected column comparison names a key checked by the actual parent uniqueness checks. -/
  unique : ∀ link ∈ catalog.foreignKeyLinks, ∀ position pairs parent,
    link.parent = .located position (.columns pairs) → catalog.tableAt position = some parent →
    UniqueKey.ofColumns parent.columns (pairs.map Prod.snd) ∈ catalog.uniqueKeys position parent
  /-- Every stored row accepted by a self link's shortcut is found by its ordinary singleton lookup. -/
  self : ∀ link ∈ catalog.foreignKeyLinks, ∀ key shape,
    link.parent = .located link.child key → catalog.tableAt link.child = some shape → link.SelfLookupSound shape key

/-- For any frame with no fired programs at the given table, time and event, running
programs returns the input state and does not end the row. Proof sketch: the fold is empty. -/
theorem runPrograms_empty {catalog : Catalog} {nested : NestedRun} {frame : RowFrame}
    {table : Nat} {time : Syntax.TriggerTime} {event : Resolved.TriggerEvent} {cells : List Value}
    (empty : frame.fired table time event = []) (state : KeyState) :
    runPrograms catalog nested frame table time event cells state = .ok (state,false) := by
  simp only [runPrograms, empty, List.foldlM_nil]
  rfl

end Belay.Sqlite.Model
