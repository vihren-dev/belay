import Belay.Sqlite.Model.Resolution.OperandArmsMore

set_option doc.verso true

/-! Resolution of the expressions of a query (ADR 0012, slice 1): names become column positions, and
each comparison keeps the affinity and collation that evaluation applies. {lit}`OperandTraced.lean`
resolves with the name trace, {lit}`OperandProjection.lean` gives the functions without it, and
{lit}`OperandArms.lean` and {lit}`OperandArmsMore.lean` give their equations by form. -/
