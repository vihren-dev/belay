import Belay
import Belay.Sqlite.Model.ForeignKeyCountDelete

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! The generic deletion phase accounts for a self-reference without adding a phantom
violation. A second fixture shows why deleting a parent must add its orphan count. -/

open Belay.Sqlite
open Belay.Sqlite.Model

/-- A row references its own BLOB-affinity primary key. -/
def selfReference : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY REFERENCES p(k)); INSERT INTO p VALUES(1);"

/-- The concrete table extracted from the checked input schema. -/
def target : Table :=
  { shape := (selfReference.raw.catalog.tableAt 0).getD { columns := [] }
    rows := selfReference.raw.rows.getD 0 [] }

/-- The schema's single foreign key, with its selected column comparison. -/
def selfLink : ForeignKeyLink :=
  { child := 0, key := target.shape.allForeignKeys.headD
      { table := .ofString "p", columns := [0], referenced := [.ofString "k"], onDelete := .noAction, onUpdate := .noAction }
    parent := .located 0 (.columns [(0, 0)]) }

/-- The only stored row of the self-reference fixture. -/
def old : Row := { rowid := 1, values := [.integer 1] }

/-- The actual old-row steps followed by the engine's physical row removal. -/
def removed : Except KeyStop KeyState :=
  (fun reached => reached.changeRows 0 (fun rows => rows.filter (·.rowid != old.rowid))) <$>
    oldSteps selfReference.raw.catalog { rows := selfReference.raw.rows } 0 old
      (childLinks selfReference.raw.catalog.foreignKeyLinks 0)
      (parentLinks selfReference.raw.catalog.foreignKeyLinks 0) false

/-- The structural BLOB comparison theorem discharges the universal row-pair premise for
this schema; no finite enumeration of parent or child values is used. -/
theorem selfComparison : ∀ link ∈ selfReference.raw.catalog.foreignKeyLinks, ∀ key child,
    link.parent = .located 0 key → selfReference.raw.table link.child = some child →
    link.LookupScanConsistent child.shape target.shape key := by
  intro link member key child selected childAt
  change link ∈ [selfLink] at member
  simp only [List.mem_singleton] at member
  subst link
  change ParentLink.located 0 (.columns [(0, 0)]) = .located 0 key at selected
  cases selected
  have childSame : child = target := Option.some.inj (childAt.symm.trans (by rfl))
  subst child
  exact ForeignKeyLink.lookupScanConsistent_blob selfLink target.shape target.shape 0 0
    (target.shape.columns.headD { name := .ofString "k", declaredType := none })
    (target.shape.columns.headD { name := .ofString "k", declaredType := none }) rfl rfl rfl rfl

/-- The generic physical-deletion theorem preserves the global counter bound on this actual
self-reference execution. Its comparison premise comes from the structural theorem above. -/
theorem selfDeletionBound : ResultHolds (KeyState.CounterBound selfReference.raw.catalog)
    (KeyStop.CounterBound selfReference.raw.catalog) removed := by
  exact oldSteps_remove_parent_counterBound
    (catalog := selfReference.raw.catalog) (state := { rows := selfReference.raw.rows })
    (position := 0) (table := target)
    (KeyState.CounterBound.start (database := selfReference.raw) (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
    (selfReference.rowid_unique 0 target (by decide +kernel))
    selfReference.valid.admitted.rowsStored old (by decide +kernel) selfComparison false

/-- The self-row is excluded from its own parent scan, so deletion leaves counter and
violation count at zero. This is checked against the existing execution functions. -/
theorem selfDeletionZero : (match removed with
    | .ok state => state.counter = 0 ∧ (state.database selfReference.raw.catalog).foreignKeyViolations = 0
    | .error _ => False) := by
  change (0 : Int) = 0 ∧ (0 : Nat) = 0
  exact ⟨rfl, rfl⟩

/-- An ordinary child must remain counted after its parent is removed before actions run. -/
def referencing : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- The actual old-row phase adds one pending violation for the retained child. This is the
intermediate state that later actions or a statement-level FK error must handle. -/
theorem parentDeletionCountsOrphan : (match
    (fun reached => reached.changeRows 0 (fun rows => rows.filter (·.rowid != old.rowid))) <$>
      oldSteps referencing.raw.catalog { rows := referencing.raw.rows } 0 old
        (childLinks referencing.raw.catalog.foreignKeyLinks 0)
        (parentLinks referencing.raw.catalog.foreignKeyLinks 0) false with
    | .ok state => state.counter = 1 ∧ (state.database referencing.raw.catalog).foreignKeyViolations = 1
    | .error _ => False) := by
  change (1 : Int) = 1 ∧ (1 : Nat) = 1
  exact ⟨rfl, rfl⟩

#print axioms parentDeletionCountsOrphan
#print axioms selfComparison
#print axioms selfDeletionBound
#print axioms selfDeletionZero
#print axioms parentFound_any
#print axioms parentFound_remove_split
#print axioms Table.RowidsDistinct.row_eq
#print axioms ForeignKeyLink.unsatisfied_remove_parent
#print axioms ForeignKeyLink.satisfied_setRows_other
#print axioms countP_remove_rowid
#print axioms childRows_countP
#print axioms ForeignKeyLink.violationCount_remove_parent
#print axioms ForeignKeyLink.violationCount_remove_other
#print axioms oldSteps_parents_append
#print axioms oldSteps_parent_single
#print axioms oldSteps_parent_exact
#print axioms oldSteps_counter_delta
#print axioms Database.foreignKeyViolations_remove_parent
#print axioms parentRemovalMatches_sum
#print axioms oldSteps_remove_parent_counterBound
