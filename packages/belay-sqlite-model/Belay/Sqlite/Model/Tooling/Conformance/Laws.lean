import Belay.Sqlite.Model.Programs.Scripts.Laws

set_option doc.verso true

/-! SQLite model laws describe transaction rollback, statement failure and
row preservation when a column is added. -/
set_option maxHeartbeats 2000000
namespace Belay.Sqlite.Model.Conformance

#print axioms rollback
#print axioms statement_atomicity
#print axioms constraint_rollback

end Belay.Sqlite.Model.Conformance
