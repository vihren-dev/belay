import Lean.Meta.Tactic.Simp.RegisterCommand

/-- The equations of {lit}`resolveStatement`, one for each statement form, in the shape that the
function had before the name trace. A proof that unfolds a statement with `simp only [statement_arms]`
finds the same bodies as before. -/
register_simp_attr statement_arms
