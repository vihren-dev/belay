import S6AutoCommute
import S6RulesNegativeReads
import S6RulesNegativeClock

/-! A fixture module of `tests/surface_s6_automation_test.py`: claims that {lit}`sql_commute` cannot prove (ADR 0017,
S6). A read of the total change count has no certificate, and a migration that stores the clock does not commute
with a read under a clock that changes. In both, the tactic leaves the premise that is false as a goal and says so;
{lit}`S6RulesNegativeReads` and {lit}`S6RulesNegativeClock` show that the premise fails and that the claim is false. The
fixture ends each example with {lit}`sorry` only to look at the open goals; it declares no theorem. -/

set_option doc.verso true

namespace S6RulesNegativeReads
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The read of {name}`counterRead` as a script. -/
def counterScript : Script := sql r"SELECT id FROM items WHERE total_changes() = 1"

/--
warning: sql_commute left the premise valid open: no hint gives a valid certificate. Pass a hint of the form ReadAnalysis.analyze width resolved = .certified certificate. The analysis answers unknown for reads of counters, the clock, table metadata and SELECT star, and then no rule applies.
---
warning: sql_commute left the premise obligations open: no hint gives the obligations of the certificate: the resolution of the read before and after the migration, and the cells that the migration appends to each scan.
---
warning: declaration uses `sorry`
-/
#guard_msgs in
-- With no certificate for the counter read, sql_commute leaves the validity and the obligations open.
example :
    Migration.PreservesAt (send expansion) (fun _ => True) (send counterScript) initial := by
  sql_commute
  assert_open_goals [valid, obligations, certificate]
  all_goals sorry

end S6RulesNegativeReads

namespace S6RulesNegativeClock
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/--
warning: sql_commute left the premise valid open: no hint gives a valid certificate. Pass a hint of the form ReadAnalysis.analyze width resolved = .certified certificate. The analysis answers unknown for reads of counters, the clock, table metadata and SELECT star, and then no rule applies.
---
warning: sql_commute left the premise constant open: the clock must give one date at every statement index. A clock that changes is a conflict that this rule does not cover.
---
warning: sql_commute left the premise obligations open: no hint gives the obligations of the certificate: the resolution of the read before and after the migration, and the cells that the migration appends to each scan.
---
warning: sql_commute left the premise admittedKept open: the predicate of the claim must hold again after the read has run.
---
warning: declaration uses `sorry`
-/
#guard_msgs in
-- Under a clock that changes, sql_commute leaves the constant clock open, which is false by
-- moving_clock_not_constant.
example :
    Migration.CommutesOn (send stampMigration) (fun _ => True) (send lookupAda) := by
  sql_commute
  assert_open_goals [valid, constant, obligations, admittedKept, certificate]
  all_goals sorry

end S6RulesNegativeClock
