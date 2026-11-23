import Lean.Meta.Tactic.Simp.RegisterCommand

set_option doc.verso true

/-! The simp set of the kind rules of the script step. The set is registered in a module of its own because a
simp set must be registered in a module that comes before the modules that use it, and each kind rule is in the
module of its kind. -/

/-- The kind rules of the script step: for each kind of resolved statement, one theorem that gives
{lit}`runScriptStep` exactly, with the resolution of the statement as its only premise about the syntax. A tool
that reasons about programs can read the rules of this set and try each one, so a new kind rule needs only this
attribute. A proof can rewrite with the set when the resolution is a hypothesis:
{lit}`simp (disch := assumption) only [step_rule] at step` replaces the step by the result that the rule gives. -/
register_simp_attr step_rule
