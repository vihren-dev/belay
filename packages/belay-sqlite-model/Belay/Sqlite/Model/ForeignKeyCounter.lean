import Belay.Sqlite.Model.ForeignKeyMappingLaws
import Belay.Sqlite.Model.RowEngineKeyState

set_option doc.verso true

/-! The global immediate-constraint invariant for foreign keys. The counter bounds the
number of unsatisfied row/declaration pairs across the whole database. The count reuses
the engine's selected links and row comparisons, regardless of pragma output order. -/

namespace Belay.Sqlite.Model

/-- Count every unsatisfied child row and foreign-key declaration using the catalog-selected
mapping. This includes violations from several tables, even when the pragma's unspecified
cross-table order prevents an exact output. A database with valid references has count zero. -/
def Database.foreignKeyViolations (database : Database) : Nat :=
  (database.catalog.foreignKeyLinks.map fun link =>
    (database.rowsAt link.child).countP fun row => !link.satisfied database row).sum

/-- For every database, the total violation count is zero exactly when every declared foreign
key of every stored child row is satisfied under the catalog-selected mapping. Parent-schema
compatibility is independent. Proof sketch: a sum of nonnegative counts is zero exactly when
every selected link is satisfied by all of its child rows; the catalog-link correspondence
gives the table and database row-reference facts. -/
theorem Database.foreignKeyViolations_zero (database : Database) :
    database.foreignKeyViolations = 0 ↔ database.RowReferencesHold database.catalog.foreignKeyMapping := by
  simp only [Database.foreignKeyViolations, List.sum_eq_zero_iff_forall_eq_nat, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, List.countP_eq_zero,
    Bool.not_eq_true]
  constructor
  · intro all position table present
    apply (Table.rowReferencesHold_selected_iff database position table present).mpr
    intro link member row found
    have inLinks := (List.mem_filter.mp (List.mem_reverse.mp member)).1
    have child := (List.mem_filter.mp (List.mem_reverse.mp member)).2
    have same : link.child = position := by simpa only [beq_iff_eq] using child
    have inRows : row ∈ database.rowsAt link.child := by
      simpa only [same, Database.rowsAt, present, Option.map_some, Option.getD_some] using found
    simpa using all link inLinks row inRows
  · intro holds link member row found
    have childMember : link ∈ childLinks database.catalog.foreignKeyLinks link.child := by
      simp only [childLinks, List.mem_reverse, List.mem_filter, beq_self_eq_true, and_true]
      exact member
    obtain ⟨_, _, shape, atShape, _⟩ := (database.catalog.mem_childLinks_iff _ _).mp childMember
    have present : database.table link.child = some { shape, rows := database.rows.getD link.child [] } := by
      simp only [Database.table, atShape, Option.map_some]
    have selected := (Table.rowReferencesHold_selected_iff database link.child _ present).mp
      (holds link.child _ present)
    have inRows : row ∈ ({ shape, rows := database.rows.getD link.child [] } : Table).rows := by
      simpa only [Database.rowsAt, present, Option.map_some, Option.getD_some] using found
    simpa using selected link childMember row inRows

/-- For the fixed catalog and row-engine state, the number of unsatisfied row/declaration
pairs is at most the immediate FK counter. This constrains all tables together and permits
outstanding violations while actions or triggers run. A negative counter cannot satisfy it. -/
def KeyState.CounterBound (catalog : Catalog) (state : KeyState) : Prop :=
  ((state.database catalog).foreignKeyViolations : Int) ≤ state.counter

/-- For every catalog and state with the counter bound, a zero counter implies that all row
references hold under the catalog-selected mapping. Proof sketch: a nonnegative count below
zero is zero, and {name}`Database.foreignKeyViolations_zero` gives the row fact. -/
theorem KeyState.CounterBound.zero {catalog : Catalog} {state : KeyState}
    (bound : state.CounterBound catalog) (zero : state.counter = 0) :
    (state.database catalog).RowReferencesHold catalog.foreignKeyMapping := by
  apply (Database.foreignKeyViolations_zero _).mp
  unfold KeyState.CounterBound at bound
  omega

/-- For every database with valid selected row references, its initial row-engine state has
the counter bound. Proof sketch: its violation count and initial counter are both zero. -/
theorem KeyState.CounterBound.start {database : Database}
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping) :
    ({ rows := database.rows } : KeyState).CounterBound database.catalog := by
  change (database.foreignKeyViolations : Int) ≤ 0
  rw [(database.foreignKeyViolations_zero).mpr holds]
  decide

/-- For every catalog and two states with equal rows and FK counters, the first has the
counter bound when the second does. Other metadata, including statement change counts, is
unrestricted. Proof sketch: the bound reads only these two fields. -/
theorem KeyState.CounterBound.of_rows_counter {catalog : Catalog} {state other : KeyState}
    (rows : state.rows = other.rows) (counter : state.counter = other.counter)
    (bound : other.CounterBound catalog) : state.CounterBound catalog := by
  simpa only [KeyState.CounterBound, KeyState.database, rows, counter] using bound

/-- For a row-engine stop, a FAIL state has the counter bound. Other errors require nothing:
the SQL run discards their state and keeps its input or saved transaction snapshot. The
snapshot's row fact is a separate entry requirement of the run-preservation theorem. -/
def KeyStop.CounterBound (catalog : Catalog) : KeyStop → Prop
  | .stopped .fail state => state.CounterBound catalog
  | .stopped .rollback _ | .error _ _ | .undescribed => True

end Belay.Sqlite.Model
