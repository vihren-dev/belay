import SourceAgreement
import Belay.Sqlite.Model.TwoStateReads

set_option doc.verso true

/-! Experiment: recover existing two-state endpoint formulas from one source contract. -/

namespace ProofBoundaries

open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- Unread initial sources give agreement for any two initial databases. Proof sketch:
every source has a false initial-origin test, so only the unchanged current lookups remain. -/
theorem queryAgrees_initial (database : Database) (before after : Option Database) (query : Query)
    (plain : query.readsInitial = false) : QueryAgrees database database before after query := by
  intro join member
  simp only [Query.readsInitial, List.any_eq_false] at plain
  have unread := plain join member
  obtain ⟨kind, source, condition⟩ := join
  cases source <;> simp_all [Source.isInitial, SourceAgrees]

/-- Unread current sources give agreement for any two current databases. Proof sketch:
the false test excludes both current tables and pragmas; other lookups are unchanged. -/
theorem queryAgrees_current (first second : Database) (initial : Option Database) (query : Query)
    (plain : query.readsCurrent = false) : QueryAgrees first second initial initial query := by
  intro join member
  simp only [Query.readsCurrent, List.any_eq_false] at plain
  have unread := plain join member
  obtain ⟨kind, source, condition⟩ := join
  cases source <;> simp_all [Source.readsCurrent, SourceAgrees]

/-- This is the existing initial-origin statement-context formula, with arbitrary nested
queries. The proof uses the shared depth induction and the initial-origin adapter. -/
theorem statementContext_initial (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Database) (queries : List Query) (before after : Option Database)
    (plain : ∀ query ∈ queries, query.readsInitial = false) :
    statementContext clock counters parameters database queries before =
      statementContext clock counters parameters database queries after :=
  statementContext_agrees clock counters parameters database database queries before after
    (fun query member => queryAgrees_initial database before after query (plain query member))

/-- This is the existing current-origin statement-context formula, using the same depth
induction; its predicate still excludes database-dependent pragma sources. -/
theorem statementContext_current (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (queries : List Query) (initial : Option Database)
    (plain : ∀ query ∈ queries, query.readsCurrent = false) :
    statementContext clock counters parameters first queries initial =
      statementContext clock counters parameters second queries initial :=
  statementContext_agrees clock counters parameters first second queries initial initial
    (fun query member => queryAgrees_current first second initial query (plain query member))

/-- This is the existing initial-origin full-run endpoint, including absent source tables.
Its proof is one application of the new run theorem, with no specialized traversal. -/
theorem runOn_initial (query : Query) (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Database) (queries : List Query) (before after : Option Database)
    (own : query.readsInitial = false) (nested : ∀ other ∈ queries, other.readsInitial = false) :
    query.runOn clock counters parameters database queries before =
      query.runOn clock counters parameters database queries after :=
  runOn_agrees query clock counters parameters database database queries before after
    (queryAgrees_initial database before after query own)
    (fun other member => queryAgrees_initial database before after other (nested other member))

/-- This is the existing initial-origin permitted-results endpoint, including source absence.
It follows from the shared source contract and initial-origin adapter. -/
theorem possibleOn_initial (query : Query) (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Database) (queries : List Query) (before after : Option Database)
    (own : query.readsInitial = false) (nested : ∀ other ∈ queries, other.readsInitial = false) :
    query.possibleOn clock counters parameters database queries before =
      query.possibleOn clock counters parameters database queries after :=
  possibleOn_agrees query clock counters parameters database database queries before after
    (queryAgrees_initial database before after query own)
    (fun other member => queryAgrees_initial database before after other (nested other member))

/-- This is the existing current-origin permitted-results endpoint. Pragmas remain excluded
by the original premise; the general theorem instead accepts explicitly equal pragma rows. -/
theorem possibleOn_current (query : Query) (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (queries : List Query) (initial : Option Database)
    (own : query.readsCurrent = false) (nested : ∀ other ∈ queries, other.readsCurrent = false) :
    query.possibleOn clock counters parameters first queries initial =
      query.possibleOn clock counters parameters second queries initial :=
  possibleOn_agrees query clock counters parameters first second queries initial initial
    (queryAgrees_current first second initial query own)
    (fun other member => queryAgrees_current first second initial other (nested other member))

/-- A missing optional database can agree with a present database when the selected table
is absent there too. This checks absence equality rather than demanding database equality. -/
theorem missing_initial_agrees (first second database : Database) (position : Nat)
    (missing : database.table position = none) :
    SourceAgrees first second none (some database) (.initialTable position) := by
  simp [SourceAgrees, missing]

/-- Pragma agreement is exactly equality of its optional rows, with no false assumption
that every pragma ignores the current database. -/
theorem pragma_agrees_iff (first second : Database) (before after : Option Database) (pragma : PragmaRows) :
    SourceAgrees first second before after (.pragma pragma) ↔ pragma.rowsOn first = pragma.rowsOn second :=
  Iff.rfl

#print axioms statementContext_initial
#print axioms statementContext_current
#print axioms runOn_initial
#print axioms possibleOn_initial
#print axioms possibleOn_current

end ProofBoundaries
