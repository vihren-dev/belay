import Belay.Sqlite.Model.ForeignKeyCounterRows

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For any nested runner and program list with no fired BEFORE UPDATE programs at any
target/assigned list, the BEFORE target frame holds. Proof sketch: the actual empty program
fold returns the original state. This is a sufficient helper; the general frame permits
BEFORE programs that affect other tables or otherwise retain the target rows. -/
theorem NestedRun.beforeUpdateFrame_of_empty {profile : Profile} {catalog : Catalog}
    (programs : List Resolved.Program) (nested : NestedRun)
    (empty : ∀ position assigned, ({clock := 0, programs} : RowFrame).fired position .before (.update (some assigned)) = []) :
    nested.BeforeUpdateFrame profile catalog programs := by
  intro frame position assigned cells state reached ended same _ ran _
  have noBefore : frame.fired position .before (.update (some assigned)) = [] := by
    simpa only [RowFrame.fired, same] using empty position assigned
  rw [runPrograms_empty noBefore, Except.ok.injEq, Prod.mk.injEq] at ran
  exact congrArg (fun value : KeyState => (value.database catalog).rowsAt position) ran.1.symm

/-- For an admitted input with unique keys and valid selected row references, enforced
row execution preserves row references in each success or partial FAIL database retained
by the effect. It requires schema comparisons, safe generated programs/actions, a BEFORE
target frame at every fuel and safe raw work. Other error carriers impose nothing here;
SQL restoration of input or snapshot databases is a separate run obligation.
Proof sketch: initialize the counter bound at zero, apply the actual fuel induction, and
use the publication rule that success and FAIL states have counter zero. -/
theorem rowsKeys_rowReferences {profile : Profile} (rules : Resolved.WriteRules) (clock : Int) (target : Nat)
    (work : RowWork) {database : Database} (ready : Database.ForeignKeyReady profile database)
    (references : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (enforced : rules.keys = true)
    (facts : database.catalog.ForeignKeyComparisons)
    (programSafe : ProgramsForeignKeySafe database.catalog rules.programs)
    (actionSafe : ActionsForeignKeySafe database.catalog)
    (before : ∀ fuel, (NestedRun.credited (runRows database.catalog database.catalog.foreignKeyLinks fuel)).BeforeUpdateFrame profile database.catalog rules.programs)
    (safe : work.ForeignKeySafe database.catalog) (plain : Bool) (algorithm : Option ConflictAlgorithm) :
    (rowsKeys rules clock target work database plain algorithm).effect.Satisfies
      (fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  unfold rowsKeys
  apply keyRun_rowReferences references target plain
  have result := runRows_foreignKeyKeeps profile database.catalog rules.programs facts programSafe actionSafe before
    (rules.depth + 1) (rules.frame clock algorithm) work {rows := database.rows} rfl safe
    ⟨ready, KeyState.CounterBound.start references⟩
  simpa only [Resolved.WriteRules.links, enforced, ite_true] using
    result.imp (fun _ good => good.2) (fun _ good => good.2)

end Belay.Sqlite.Model
