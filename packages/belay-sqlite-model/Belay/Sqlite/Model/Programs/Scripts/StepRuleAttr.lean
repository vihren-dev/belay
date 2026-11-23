import Lean.Meta.Tactic.Simp.RegisterCommand

/-- The kind rules of the script step: for each kind of resolved statement, one theorem that gives
{lit}`runScriptStep` exactly, with the resolution of the statement as its only premise about the syntax.
Tools that reason about programs, such as the surface tactic {lit}`sql_run`, read the rules of this set
and try each one, so a new kind rule needs only this attribute. A proof can also rewrite with the set:
{lit}`simp only [step_rule, found]` replaces the step by the result that the rule gives. -/
register_simp_attr step_rule
