import Belay.Sqlite.Model.Queries.Select.JoinExamples
import Belay.Sqlite.Model.Shared.Execution.SqlExecution

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.CollationExamples

open Belay.Sqlite.Model

-- NOCASE folds ASCII capitals only: 'A' = 'a', and 'Ä' (C3 84) differs from 'ä' (C3 A4).
#guard Collation.nocase.compare (.text [65]) (.text [97]) == .eq
#guard Collation.nocase.compare (.text [195, 132]) (.text [195, 164]) != .eq
-- RTRIM ignores trailing spaces only: 'a ' = 'a', and 'a ' < 'a\t' since it compares 'a' with 'a\t'.
#guard Collation.rtrim.compare (.text [97, 32]) (.text [97]) == .eq
#guard Collation.rtrim.compare (.text [97, 32]) (.text [97, 9]) == .lt
#guard Collation.binary.compare (.text [97, 32]) (.text [97, 9]) == .gt
-- A collation changes only TEXT: the integer 1 is the integer 1 under NOCASE.
#guard Collation.nocase.key (.integer 1) == .integer 1

end Belay.Sqlite.Model.Resolution.CollationExamples
