import Belay
import Belay.Sqlite.Model.ForeignKeyInsertBound

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! The insertion bound accounts for self-parent lookup and repairs of pending violations.
A raw duplicate parent shows why the enlarged-table uniqueness premise is necessary. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyInsertFixture

/-- An empty table whose BLOB-affinity primary key references itself. -/
def selfReference : Belay.Sqlite.Database := db! "CREATE TABLE p(k PRIMARY KEY REFERENCES p(k));"

/-- The target table of the checked self-reference schema. -/
def target : Table :=
  { shape := (selfReference.raw.catalog.tableAt 0).getD { columns := [] }
    rows := [] }

/-- The schema's selected self-reference comparison. -/
def selfLink : ForeignKeyLink :=
  { child := 0, key := target.shape.allForeignKeys.headD
      { table := .ofString "p", columns := [0], referenced := [.ofString "k"], onDelete := .noAction, onUpdate := .noAction }
    parent := .located 0 (.columns [(0, 0)]) }

/-- The new row is its own parent. -/
def new : Row := { rowid := 1, values := [.integer 1] }

/-- The real new-row checks followed by the physical append, with parent scans enabled. -/
def appended (database : Belay.Sqlite.Model.Database) (counter : Int) (row : Row := new) : Except KeyStop KeyState :=
  (fun reached => reached.changeRows 0 (· ++ [row])) <$>
    newSteps database.catalog { rows := database.rows, counter } 0 row
      (childLinks database.catalog.foreignKeyLinks 0)
      (parentLinks database.catalog.foreignKeyLinks 0) true none []

/-- For every stored row pair of this schema, the BLOB structural theorem equates lookup
and scan. It is not a finite enumeration of the fixture's current rows. -/
theorem selfComparison : ∀ link ∈ selfReference.raw.catalog.foreignKeyLinks, ∀ key child,
    link.parent = .located 0 key → selfReference.raw.table link.child = some child →
    link.LookupScanConsistent child.shape target.shape key := by
  intro link member key child selected childAt
  change link ∈ [selfLink] at member
  simp only [List.mem_singleton] at member
  subst link
  change ParentLink.located 0 (.columns [(0, 0)]) = .located 0 key at selected
  cases selected
  have same : child = target := Option.some.inj (childAt.symm.trans (by rfl))
  subst child
  exact ForeignKeyLink.lookupScanConsistent_blob selfLink target.shape target.shape 0 0
    (target.shape.columns.headD { name := .ofString "k", declaredType := none })
    (target.shape.columns.headD { name := .ofString "k", declaredType := none }) rfl rfl rfl rfl

/-- The shortcut implication holds for every stored row in this schema by BLOB affinity. -/
theorem selfShortcut : ∀ link ∈ childLinks selfReference.raw.catalog.foreignKeyLinks 0, ∀ key,
    link.parent = .located 0 key → link.SelfLookupSound target.shape key := by
  intro link member key selected
  change link ∈ [selfLink] at member
  simp only [List.mem_singleton] at member
  subst link
  change ParentLink.located 0 (.columns [(0, 0)]) = .located 0 key at selected
  cases selected
  apply ForeignKeyLink.selfLookupSound_blob
  intro pair member
  simp only [List.mem_singleton] at member
  subst pair
  exact ⟨target.shape.columns.headD { name := .ofString "k", declaredType := none }, rfl, rfl⟩

/-- The generic phase law proves the bound for an actual self-referencing insertion.
Its universal comparison premises come from structural laws, not final row validity. -/
theorem selfInsertionBound : ResultHolds (KeyState.CounterBound selfReference.raw.catalog)
    (KeyStop.CounterBound selfReference.raw.catalog) (appended selfReference.raw 0) := by
  exact newSteps_append_parent_counterBound
    (catalog := selfReference.raw.catalog) (state := { rows := selfReference.raw.rows })
    (position := 0) (table := target)
    (KeyState.CounterBound.start (database := selfReference.raw) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) selfReference.valid.admitted.rowsStored new
    (by decide +kernel) (by simp [Table.KeysUnique, target]) (by simp [Table.RowidsDistinct, target]) selfComparison
    (by
      intro link member pairs selected
      change link ∈ [selfLink] at member
      simp only [List.mem_singleton] at member
      subst link
      change ParentLink.located 0 (.columns [(0, 0)]) = .located 0 (.columns pairs) at selected
      cases selected
      decide +kernel) selfShortcut true

/-- The self insert is accepted with no outstanding violation. -/
theorem selfInsertionZero : (match appended selfReference.raw 0 with
    | .ok state => state.counter = 0 ∧ (state.database selfReference.raw.catalog).foreignKeyViolations = 0
    | .error _ => False) := by
  change (0 : Int) = 0 ∧ (0 : Nat) = 0
  exact ⟨rfl, rfl⟩

/-- An orphan stored while enforcement is off supplies a pending violation to repair. -/
def orphan : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p); INSERT INTO c VALUES(1);"

/-- Inserting its parent removes the pending violation from both rows and counter. -/
theorem insertionRepairsOrphan : (match appended orphan.raw 1 with
    | .ok state => state.counter = 0 ∧ (state.database orphan.raw.catalog).foreignKeyViolations = 0
    | .error _ => False) := by
  change (0 : Int) = 0 ∧ (0 : Nat) = 0
  exact ⟨rfl, rfl⟩

/-- An existing parent has one matching child and an unrelated orphan. -/
def duplicate : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1),(9);"

/-- If raw work bypasses uniqueness, another identical parent scan can erase a counter
unit belonging to a different orphan. The resolved INSERT checks uniqueness before publishing. -/
theorem duplicateNeedsUniqueness : (match appended duplicate.raw 1 { new with rowid := 2 } with
    | .ok state => state.counter = 0 ∧ (state.database duplicate.raw.catalog).foreignKeyViolations = 1
    | .error _ => False) := by
  change (0 : Int) = 0 ∧ (1 : Nat) = 1
  exact ⟨rfl, rfl⟩

end ForeignKeyInsertFixture

#print axioms ForeignKeyInsertFixture.selfComparison
#print axioms ForeignKeyInsertFixture.selfShortcut
#print axioms ForeignKeyInsertFixture.selfInsertionBound
#print axioms ForeignKeyInsertFixture.selfInsertionZero
#print axioms ForeignKeyInsertFixture.insertionRepairsOrphan
#print axioms ForeignKeyInsertFixture.duplicateNeedsUniqueness
#print axioms indexHolds_childValues
#print axioms indexHolds_shared_keyEqual
#print axioms parentFound_fresh_no_old
#print axioms Collation.compare_eq_of_binary
#print axioms LiteralData.keyCellsEqual_of_binary
#print axioms ForeignKeyLink.selfLookupSound_rowid
#print axioms ForeignKeyLink.selfLookupSound_columns
#print axioms ForeignKeyLink.selfLookupSound_blob
#print axioms ForeignKeyLink.selfLookupSound_stored
#print axioms parentFound_split_self
#print axioms newSteps_children_append
#print axioms newSteps_child_single
#print axioms newSteps_children_exact
#print axioms newSteps_parents_append
#print axioms newSteps_parent_single
#print axioms newSteps_parents_lower
#print axioms newSteps_counter_delta
#print axioms parentFound_append
#print axioms childMatches_not_null
#print axioms ForeignKeyLink.satisfied_append_parent
#print axioms ForeignKeyLink.unsatisfied_append_parent
#print axioms ForeignKeyLink.matching_new_parent_unsatisfied
#print axioms ForeignKeyLink.violationCount_append_parent
#print axioms ForeignKeyLink.violationCount_append_other
#print axioms Database.foreignKeyViolations_append_parent
#print axioms ForeignKeyLink.newRowSatisfied_append
#print axioms parentInsertionMatches_sum
#print axioms newSteps_append_parent_counterBound
