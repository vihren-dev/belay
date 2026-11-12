import Belay.Sqlite.Model.Programs.Claims.InitialSourceExamples
import Belay.Sqlite.Model.Queries.Preparation.InitialSourceGuardExamples

set_option doc.verso true

/-! Regression examples for the guards of the initial-database source (ADR 0017, S6): a function call in
the body of an initial view looks up its name in the initial catalog (a pragma function is refused), a three-part column name picks the
source of its schema, and a stored view body never names the initial database. -/

namespace Belay.Sqlite.Model.TwoStateFixtures

example : (stepOutputOf threePartQuery [] initialT).bind rows? = some (ints [[1, 3], [2, 3]]) := by decide +kernel
example : (stepOutputOf sameNameQuery [] initialT).bind rows? = some (ints [[1], [2]]) := by decide +kernel

end Belay.Sqlite.Model.TwoStateFixtures
