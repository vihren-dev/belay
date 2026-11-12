import Belay.Sqlite.Model.Queries.Fixtures.InitialSourceFixtureExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.TwoStateFixtures

-- A left join of a current table to an initial table extends the unmatched row with NULL.
/-- The current table {lit}`t(a INTEGER)` with the rows 2 and 3, which a join with the initial rows 1 and 2 matches. -/
def joinCurrent : Database := databaseOf [tableOf "t" [col "a"] (ints [[2], [3]])]

end Belay.Sqlite.Model.TwoStateFixtures
