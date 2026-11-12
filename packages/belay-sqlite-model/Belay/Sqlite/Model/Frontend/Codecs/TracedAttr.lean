import Lean.Meta.Tactic.Simp.RegisterCommand

/-- The lemmas that push the projection of a traced computation through its monad. A proof
about a resolver function that is the projection of its traced form restates the old
{lit}`Except` body with `simp only [traced_drop]`. -/
register_simp_attr traced_drop

/-- The equations of a resolver function that is the projection of its traced form, in the shape of
the function before it was traced: one equation for each constructor of its argument. A proof that
unfolds the function with `simp only [traced_arms]` finds the same bodies as before. -/
register_simp_attr traced_arms
