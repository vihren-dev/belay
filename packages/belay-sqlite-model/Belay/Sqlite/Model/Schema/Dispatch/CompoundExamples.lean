import Belay.Sqlite.Model.Schema.Dispatch.Execution
import Belay.Sqlite.Model.Queries.Evaluation.CompoundExamples

set_option doc.verso true

/-! Checked examples of compound {lit}`SELECT` over resolved queries (ADR 0019, D3): each
operator, the duplicate rule, the kept row, the window, and the points where SQLite runs a
term, reads the window and fails. Native SQLite is the authority for these values; the authored
compound corpus compares them with it. The terms are queries without {lit}`FROM`, at the indexes
that the compound names in the statement's list of subqueries. -/

namespace Belay.Sqlite.Model.Resolved.CompoundExamples

/-- The rows, the fault, the overflow and the mismatch of a compound statement with its terms,
with the values of its parameters, over an empty database at clock 0. -/
def runOf (query : Query) (terms : List Query) (parameters : List Value := []) :
    Option (List (List Value) × Fault × Bool × Bool) :=
  (query.runOn 0 {} parameters (.ofTables []) terms).map fun (_, run) => (run.rows, run.fault, run.overflow, run.mismatch)

-- SELECT 1 UNION SELECT 2 INTERSECT SELECT 2: the operators apply from left to right.
example : runOf (compound [.union, .intersect] [.binary]) [literals [int 1], literals [int 2], literals [int 2]] =
    some ([[.integer 2]], .none, false, false) := by decide +kernel
-- UNION ALL keeps both rows; UNION keeps one.
example : runOf (compound [.unionAll] [.binary]) [literals [int 1], literals [int 1]] =
    some ([[.integer 1], [.integer 1]], .none, false, false) := by decide +kernel
example : runOf (compound [.union] [.binary]) [literals [int 1], literals [int 1]] =
    some ([[.integer 1]], .none, false, false) := by decide +kernel
-- SELECT NULL EXCEPT SELECT NULL gives no row: NULL equals NULL.
example : runOf (compound [.except] [.binary]) [literals [.literal .null], literals [.literal .null]] =
    some ([], .none, false, false) := by decide +kernel
-- SELECT 1, NULL INTERSECT SELECT 1, NULL gives one row.
example : runOf (compound [.intersect] [.binary, .binary]) [literals [int 1, .literal .null], literals [int 1, .literal .null]] =
    some ([[.integer 1, .null]], .none, false, false) := by decide +kernel
-- SELECT 1 INTERSECT SELECT '1' gives no row: the rule has no affinity.
example : runOf (compound [.intersect] [.binary]) [literals [int 1], literals [.literal (.text [49])]] =
    some ([], .none, false, false) := by decide +kernel
-- SELECT 1 UNION SELECT 1.0: the rows are equal and differ, so SQLite's plan chooses the row.
example : (runOf (compound [.union] [.binary]) [literals [int 1], literals [.literal (.real 0x3FF0000000000000)]]).map (·.2.1) =
    some .may := by decide +kernel
-- Under NOCASE, 'A' UNION 'a' is one row that the plan chooses; 'a' UNION 'a' is certain.
example : (runOf (compound [.union] [.nocase]) [literals [.literal (.text [65])], literals [.literal (.text [97])]]).map
    (fun (rows, fault, _) => (rows.length, fault)) = some (1, .may) := by decide +kernel
example : runOf (compound [.union] [.nocase]) [literals [.literal (.text [97])], literals [.literal (.text [97])]] =
    some ([[.text [97]]], .none, false, false) := by decide +kernel
-- EXCEPT under NOCASE: SELECT 'A' EXCEPT SELECT 'a' gives no row.
example : runOf (compound [.except] [.nocase]) [literals [.literal (.text [65])], literals [.literal (.text [97])]] =
    some ([], .none, false, false) := by decide +kernel
-- SELECT 1 UNION ALL SELECT 2 UNION ALL SELECT 3 LIMIT 1 OFFSET 1 gives 2.
example : runOf { compound [.unionAll, .unionAll] [.binary] with limit := some 1, offset := 1 }
    [literals [int 1], literals [int 2], literals [int 3]] = some ([[.integer 2]], .none, false, false) := by decide +kernel
-- SELECT 2 UNION SELECT 1 UNION SELECT 3 ORDER BY 1 DESC gives 3, 2, 1.
example : runOf { compound [.union, .union] [.binary] with orderBy := [{ key := .output 0, descending := true }] }
    [literals [int 2], literals [int 1], literals [int 3]] =
    some ([[.integer 3], [.integer 2], [.integer 1]], .none, false, false) := by decide +kernel

end Belay.Sqlite.Model.Resolved.CompoundExamples
