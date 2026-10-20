import Belay.Sqlite.Resolution.Examples

set_option doc.verso true

/-! Examples of store-time affinity in resolution (ADR 0012, amendment 1): INSERT and
UPDATE store each value as SQLite stores it in a column of the affinity. -/

namespace Belay.Sqlite.Resolution.StoreExamples
open Belay.Sqlite.Resolution.Examples

-- INSERT: the text '1' is stored as the integer 1 in the INTEGER column b.
#guard statements (migration tableT [.insert (name! "t") (some [(name! "b")]) [[.string [49]]] []]) == [.insert 0 [[.value .null, .value (.integer 1)]] []]
-- INSERT: an integer is stored as its text in the TEXT column a.
#guard statements (migration tableT [.insert (name! "t") (some [(name! "a")]) [[.numeric "7"]] []]) == [.insert 0 [[.value (.text [55]), .value .null]] []]
-- UPDATE: SET stores the text '1' as the integer 1 in the INTEGER column b.
#guard statements (migration tableT [.update (name! "t") [((name! "b"), .string [49])] none]) == [.update 0 [(1, .literal (.integer 1))] none []]

end Belay.Sqlite.Resolution.StoreExamples
