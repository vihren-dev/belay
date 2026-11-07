import Belay.Sqlite.Model.PossibleResults

set_option doc.verso true

/-! Examples of the normal form of the results that SQLite may give (ADR 0018, D6), each checked by
the kernel: the order of output normalization for values that {lit}`Value.compare` alone does not
order. The acceptance cases of ADR 0027 (A12, A14) cover the results of windows, ties and
{lit}`DISTINCT`. -/

namespace Belay.Sqlite.Model.PossibleResultsExamples

-- The normal form is one list for any input order: NULL comes before a NaN REAL, which
-- Value.compare alone would call equal, and the integer 1 before the real 1.0.
example : Resolved.normalForm [[.real 0x7FF8000000000000], [.null]] = Resolved.normalForm [[.null], [.real 0x7FF8000000000000]] := by
  decide +kernel
example : Resolved.normalForm [[.real 0x3FF0000000000000], [.integer 1]] = [[.integer 1], [.real 0x3FF0000000000000]] := by
  decide +kernel

end Belay.Sqlite.Model.PossibleResultsExamples
