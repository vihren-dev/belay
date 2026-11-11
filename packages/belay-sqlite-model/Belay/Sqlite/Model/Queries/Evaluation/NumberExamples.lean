import Belay.Sqlite.Model.Queries.Evaluation.Summation
import Belay.Sqlite.Model.Queries.Evaluation.Comparison

set_option doc.verso true

/-! Checked examples of SQLite's conversions between text and numbers (ADR 0012, slice 2).
Each expected value is the result of a {lit}`CAST` or an arithmetic operator in the
pinned native SQLite 3.51.0. The examples fix the intended reading of each
rule; the conformance cases compare the conversions with native SQLite. -/

namespace Belay.Sqlite.Model.NumberExamples

open Belay.Sqlite.Model

-- SUM is exact over integers; an overflow fails unless a later REAL input follows;
-- TEXT gets numeric affinity, and text that is not a number adds 0.0.
#guard (sumOf [.integer int64Maximum, .integer 1]).sumValue == none
#guard (sumOf [.integer int64Maximum, .integer 1, .real 0x3FE0000000000000]).sumValue == some (.real 4890909195324358656)
#guard [(sumOf []).sumValue, (sumOf [.null]).sumValue, (sumOf [.text "7".toUTF8.toList, .integer 1]).sumValue,
  (sumOf [.text "abc".toUTF8.toList]).sumValue] == [some .null, some .null, some (.integer 8), some (.real 0)]
-- AVG never fails: the overflowing sum continues in doubles.
#guard [(sumOf []).averageValue, (sumOf [.integer int64Maximum, .integer 1]).averageValue] ==
  [.null, .real 4886405595696988160]

#guard !(Value.real 0x7FF8000000000000).isNull && (Value.null).isNull
#guard Comparison.apply .is (.real 0x7FF8000000000000) .null == .integer 0

end Belay.Sqlite.Model.NumberExamples
