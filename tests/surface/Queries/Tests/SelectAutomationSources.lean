import SelectAutomationCore

set_option doc.verso true
set_option sql.check false

/-! ADR 0027 experiments on the existing indexed source and join evaluator. The
uncertainty example follows the complete-row boundary of DerivedSourceExamples. -/

namespace SelectAutomation
open Belay.Sqlite
open Belay.Sqlite.Model.Resolved

/-- A two-column source whose first values coincide and second values differ. -/
def pairSource : Query :=
  { (projection none) with
    sources := [{
      kind := .inner
      source := .pragma (.fixed 2 [[.integer 1, .integer 2], [.integer 1, .integer 3]])
      condition := none }]
    columns := [.scalar (.column 0), .scalar (.column 1)], names := ["first", "second"] }

/-- An outer query that projects the second column of indexed subquery zero. -/
def nested : Query :=
  { (projection none) with
    sources := [{ kind := .inner, source := .subquery 0 2, condition := none }]
    columns := [.scalar (.column 1)] }

/-- A complete derived source gives the second column to the containing SELECT. -/
theorem nested_projection :
    (nested.runOn 0 {} [] {} [pairSource]).map (·.2.rows) =
      some [[.integer 2], [.integer 3]] := by decide +kernel

/-- Equal first-column multisets do not make complete derived rows certain. A window
can choose different second columns, so the outer evaluator refuses this source. -/
theorem nested_uncertainty :
    let inner := { pairSource with limit := some 1 }
    (inner.subqueryRun (.plain 0) {} []).rowsCertain = true ∧
    (inner.subqueryRun (.plain 0) {} []).sourceCertain = false ∧
    nested.runOn 0 {} [] {} [inner] = none := by decide +kernel

/-- Ordering by the distinct second column makes the one-row nested source usable. -/
theorem nested_ordered :
    (nested.runOn 0 {} [] {}
      [{ pairSource with limit := some 1, orderBy := [{ key := .output 1 }] }]).map (·.2.rows) =
      some [[.integer 2]] := by decide +kernel

/-- A right operand with a configurable join kind and ON condition. -/
def joinOperand (kind : JoinKind) (condition : Bool) : QuerySource :=
  { kind, source := .pragma (.fixed 1 [[.integer 4]]),
    condition := some (.literal (.integer (if condition then 1 else 0))) }

/-- Matching inner rows concatenate their cells. An unmatched left join supplies NULL
on the right even though the right source has only a non-NULL value. -/
theorem join_null_extension :
    joinRows (.bound []) 1 [[.integer 9]] (joinOperand .inner true) 1 [[.integer 4]] =
      [[.integer 9, .integer 4]] ∧
    joinRows (.bound []) 1 [[.integer 9]] (joinOperand .left false) 1 [[.integer 4]] =
      [[.integer 9, .null]] := by decide +kernel

/-- A derived source with a fault is refused, even when its rows are empty. It must
not become a successful empty relation for the containing query. -/
theorem nested_fault :
    let context : EvalContext := { clock := 0, subqueries := fun _ _ => { rows := [], fault := .may } }
    nested.source context {} = none := by decide +kernel

#print axioms nested_projection
#print axioms nested_uncertainty
#print axioms nested_ordered
#print axioms join_null_extension
#print axioms nested_fault

end SelectAutomation
