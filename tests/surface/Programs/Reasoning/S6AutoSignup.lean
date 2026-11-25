import GlobalSignupInvariant

/-! A fixture module of `tests/surface_s6_automation_test.py`: the partial-index invariant of the guide, proved
with the tactic {lit}`sql_run` (ADR 0017, S6). The claims are those of {lit}`SignupInvariantClaims` and
{lit}`GlobalSignupInvariant`, which have explicit proofs with {name}`Sql.check_send_of_rule`. Here the tactic
reduces the program to the kind rule of plain INSERT. The statement is a field of the site, so the tactic takes
the kind rule whose resolution premise the first hint closes. The goal that remains is the final property of the
reached database, which is valid; the unique index of the database gives it by the laws of valid databases. -/

set_option doc.verso true
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The claim of {name}`signup_keeps`, proved with {lit}`sql_run`. The hints close the resolution of the insert
and the model's coverage, and the tactic takes the kind rule of the statement from the first hint. The
goal that remains is the final property for the reached database, which {name}`AccountSignupSite.keeps_of_valid`
proves. -/
theorem signup_keeps_by_sql_run (e : String) (f : Value) :
    FreshEnsures (send (signupAccount e))
      (fun db => Holds (atMostOneLiveAccountWithEmail f) db ∧ Nonempty (AccountSignupSite db e))
      (ifOk (holds (atMostOneLiveAccountWithEmail f))) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db ⟨_, ⟨site⟩⟩ env _complete
  rw [site.script]
  sql_run [site.resolves, site.modeled env]
  case success =>
    intro _allOk
    exact (Holds.reached_iff_holds_of_valid _ _ _ valid.1).2 (site.keeps_of_valid f valid.1 rfl)

/-- The claim of {name}`signup_keeps_global`, proved with {lit}`sql_run` and
{name}`GlobalSignupSite.keeps_of_valid`. -/
theorem signup_keeps_global_by_sql_run (e : String) :
    FreshEnsures (send (signupAccount e))
      (fun db => Holds oneLive db ∧ Nonempty (GlobalSignupSite db e))
      (ifOk (holds oneLive)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db ⟨_, ⟨site⟩⟩ env _complete
  rw [site.script]
  sql_run [site.resolves, site.modeled env]
  case success =>
    intro _allOk
    exact (Holds.reached_iff_holds_of_valid _ _ _ valid.1).2 (site.keeps_of_valid valid.1 rfl)

#print axioms signup_keeps_by_sql_run
#print axioms signup_keeps_global_by_sql_run

end AssertionExamples
