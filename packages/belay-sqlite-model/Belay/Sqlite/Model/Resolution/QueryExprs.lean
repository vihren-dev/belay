import Belay.Sqlite.Model.Resolution.OperandProjection

set_option doc.verso true

/-! Resolution of the expressions of a query (ADR 0012, slice 1): names become column positions, and
each comparison keeps the affinity and collation that evaluation applies. {lit}`OperandTraced.lean`
resolves with the name trace, {lit}`OperandProjection.lean` gives the functions without it, and
{lit}`OperandArms.lean` and {lit}`OperandArmsMore.lean` give their equations by form.
Proof consumers import those equations separately, so executable resolution can be mutated
without compiling proofs of the unchanged behavior. -/
