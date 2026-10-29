import Belay.Sqlite.Model.SourceAgreement

/-! Focused checks of the source agreement contract: absence, shape and pragma observations. -/

namespace Belay.Sqlite.Model
open Resolved

/-- An absent initial database cannot agree with a present table, even with empty rows. -/
example (first second database : Database) (position : Nat) (table : Table)
    (found : database.table position = some table) :
    ¬Source.Agrees first second none (some database) (.initialTable position) := by
  simp [Source.Agrees, found]

/-- A missing table agrees with an absent initial database; database presence is not required. -/
example (first second database : Database) (position : Nat)
    (missing : database.table position = none) :
    Source.Agrees first second none (some database) (.initialTable position) := by
  simp [Source.Agrees, missing]

/-- Empty rows shared by two differently shaped tables do not suffice for agreement. -/
example :
    let first : Table := { shape := { columns := [] }, rows := [] }
    let second : Table := { shape := { columns := [{ name := name! "a", declaredType := none }] }, rows := [] }
    first.rows = second.rows ∧
      ¬Source.Agrees (Database.ofTables [(name! "t", first)])
        (Database.ofTables [(name! "t", second)]) none none (.table 0) := by
  simp only [Source.Agrees]
  decide +kernel

/-- Fixed pragma sources satisfy the agreement although the current-read flag excludes them. -/
example (first second : Database) (before after : Option Database) (width : Nat) (rows : List (List Value)) :
    Source.Agrees first second before after (.pragma (.fixed width rows)) ∧
      (Source.pragma (.fixed width rows)).readsCurrent = true := ⟨rfl, rfl⟩

/-- With a fixed pragma source and no nested queries, both databases can change simultaneously. -/
example (query : Query) (width : Nat) (rows : List (List Value))
    (sources : query.sources = [{ kind := .inner, source := .pragma (.fixed width rows), condition := none }])
    (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (before after : Option Database) :
    query.possibleOn clock counters parameters first [] before =
      query.possibleOn clock counters parameters second [] after := by
  apply Query.possibleOn_agrees query clock counters parameters first second [] before after
  · intro join member
    rw [sources] at member
    simp only [List.mem_singleton] at member
    subst join
    rfl
  · simp

/-- A malformed stored row lets a check pragma observe a difference between the databases. -/
private def failingTable : Table :=
  { shape := { columns := [{ name := name! "a", declaredType := none, notNull := true }] }
    rows := [{ rowid := 1, values := [.null] }] }

/-- Database-dependent pragma rows must agree; replacing every pragma by True would lose this check. -/
example : ¬Source.Agrees (Database.ofTables []) (Database.ofTables [(name! "t", failingTable)])
    none none (.pragma (.check true 0 none)) := by
  simp only [Source.Agrees]
  decide +kernel

/-- The optional pragma result preserves the unsupported case caused by two failing tables. -/
example :
    let database := Database.ofTables [(name! "t", failingTable), (name! "u", failingTable)]
    PragmaRows.rowsOn database (.check true 0 none) = none ∧
      ¬Source.Agrees (Database.ofTables []) database none none (.pragma (.check true 0 none)) := by
  simp only [Source.Agrees]
  decide +kernel

/-- Agreement gives equal complete contexts at every depth, including all correlated outer rows.
The depth is independent of the number of nested queries. -/
example (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (queries : List Query) (before after : Option Database)
    (agree : ∀ query ∈ queries, Query.Agrees first second before after query) (depth : Nat) :
    subqueryContext clock counters parameters first queries before depth =
      subqueryContext clock counters parameters second queries after depth :=
  subqueryContext_agrees clock counters parameters first second queries before after agree depth

end Belay.Sqlite.Model
