import S6RulesQueryPattern

/-! A fixture module of `tests/surface_s6_automation_test.py`: the tactic {lit}`sql_commute` on the migration query
pattern of {lit}`S6RulesQueryPattern` (ADR 0017, S6). With the analysis result and the obligations as hints, the
tactic proves the weak claim (preservation) with the rule {name}`ReadCertificate.preservesAt_send` and the strong
claim (commutation) with {name}`ReadCertificate.commutesOn_send`. The hints of the weak claim do not close the strong
claim, and without hints no claim closes: the tactic leaves the premises that it cannot close. -/

set_option doc.verso true

namespace S6RulesQueryPattern
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open Lean Elab Tactic

/-- Fails unless the open goals of the proof have exactly the given tags, in order. The fixtures use it to check
which premises {lit}`sql_commute` leaves. -/
elab "assert_open_goals " "[" tags:ident,* "]" : tactic => do
  let expected := tags.getElems.map (·.getId) |>.toList
  let actual ← (← getGoals).mapM fun goal => return (← goal.getTag).eraseMacroScopes
  unless actual == expected do
    throwError "expected the open goals {expected}, but they are {actual}"

/-- For every bound value, the lookup is preserved by the migration at the original context. Proof sketch:
{lit}`sql_commute` applies {name}`ReadCertificate.preservesAt_send`; the analysis result gives the certificate and
its validity, and the obligations give the rest. -/
theorem lookup_preserved_by_sql_commute (name : Value) :
    Migration.PreservesAt (send expansion) (fun _ => True) (send (lookup name)) initial := by
  sql_commute [analysis, obligations]

/-- For every bound value, the lookup commutes fully with the migration at every admitted context. Proof sketch:
{lit}`sql_commute` applies {name}`ReadCertificate.commutesOn_send`; the hints give the certificate, the constant
clock, the obligations at the reached connection, and the fact that the admitted contexts stay admitted. -/
theorem lookup_commutes_by_sql_commute (name : Value) :
    Migration.CommutesOn (send expansion) admitted (send (lookup name)) := by
  sql_commute [analysis,
    (fun state same assignment member one other => by
      rw [same.2] at member
      cases member
      rfl),
    (fun state domain => by
      obtain ⟨⟨connection, clock⟩, -⟩ := domain
      rw [connection, clock]
      exact obligations),
    (fun state domain selected => domain.1)]

/-- warning: sql_commute left the premise constant open: the clock must give one date at every statement index. A clock that changes is a conflict that this rule does not cover.
---
warning: sql_commute left the premise obligations open: no hint gives the obligations of the certificate: the resolution of the read before and after the migration, and the cells that the migration appends to each scan.
---
warning: sql_commute left the premise admittedKept open: the predicate of the claim must hold again after the read has run.
---
warning: declaration uses `sorry` -/
#guard_msgs in
/-- The hints of the weak claim do not close the strong claim: the tactic chooses the rule by the claim, the
certificate is found, and the three premises of commutation stay open. -/
theorem weak_hints_leave_commutation_open (name : Value) :
    Migration.CommutesOn (send expansion) admitted (send (lookup name)) := by
  sql_commute [analysis, obligations]
  assert_open_goals [constant, obligations, admittedKept]
  all_goals sorry

#print axioms lookup_preserved_by_sql_commute
#print axioms lookup_commutes_by_sql_commute

end S6RulesQueryPattern
