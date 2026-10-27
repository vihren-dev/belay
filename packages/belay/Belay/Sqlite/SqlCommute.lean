import Belay.Sqlite.SqlRunShape
import Belay.Sqlite.ReadAnalysis
import Belay.Sqlite.ReadCertificatePreservation
import Belay.Sqlite.CertifiedQueryCommutation

set_option doc.verso true

/-! The tactic {lit}`sql_commute` (ADR 0017, S6). It proves the claim that a read keeps its results across a
migration, or commutes with it, only from the proved dependency rules: {name}`Belay.Sqlite.ReadCertificate.preservesAt_send`
for weak preservation and {name}`Belay.Sqlite.ReadCertificate.commutesOn_send` for full commutation. The tactic does not
search for a dependency fact. It reads the migration and the one statement of the read from the goal, applies the
rule that belongs to the claim, closes the premises of the rule from the hints, and leaves every other premise as
a goal with a warning that says what is missing. The rule for preservation never closes a goal of commutation,
because the tactic chooses the rule by the claim and not by the hints. -/

namespace Belay.Sqlite.Run
open Lean Meta Elab Tactic Term

/-- The two claims that {lit}`sql_commute` proves: results kept across the migration (weak), and a full swap of
the read and the migration (strong). -/
inductive CommuteClaim where
  /-- Preservation: the read gives the same values and outputs before and after the migration. -/
  | preservation
  /-- Commutation: the read and the migration also reach the same connection, counters and index. -/
  | commutation

/-- The claim that a goal states, and the rule that proves it. Only two claims have a rule: {name}`Migration.PreservesAt` and {name}`Migration.CommutesOn`. -/
def claimOf? (goalType : Expr) : Option (CommuteClaim × Name) :=
  match goalType.getAppFn.constName? with
  | some name =>
    if name == ``Migration.PreservesAt then
      some (.preservation, ``ReadCertificate.preservesAt_send)
    else if name == ``Migration.CommutesOn then some (.commutation, ``ReadCertificate.commutesOn_send)
    else none
  | none => none

/-- What a premise of the rules means and why a hint is missing, by the name of the premise in the rule. The text
is part of the warning that {lit}`sql_commute` gives for a premise that it leaves open. -/
def premiseAdvice (premise : Name) : String :=
  if premise == `valid then
    "no hint gives a valid certificate. Pass a hint of the form ReadAnalysis.analyze width resolved = .certified certificate. The analysis answers unknown for reads of counters, the clock, table metadata and SELECT star, and then no rule applies."
  else if premise == `obligations then
    "no hint gives the obligations of the certificate: the resolution of the read before and after the migration, and the cells that the migration appends to each scan."
  else if premise == `constant then
    "the clock must give one date at every statement index. A clock that changes is a conflict that this rule does not cover."
  else if premise == `single then
    "the migration must be a script of statements that are none INSERT from a query. Pass a hint that proves it for each statement. A migration with an INSERT from a query reaches different connections in different branches, so the rule does not cover it. State the claim with ReadCertificate.preservesAt, and prove the obligations of the certificate at the end of every branch with sendStatements_branch_invariant."
  else if premise == `admittedKept then
    "the predicate of the claim must hold again after the read has run."
  else s!"the premise {premise} is not closed by a hint."

/-- Try to close one premise of a rule: by evaluation for the premise {lit}`single` (the migration has no INSERT
from a query), then each hint for the premise: the hint itself, the soundness of an analysis result, and these
two under the variables and hypotheses that the premise introduces. -/
def closePremise (tag : Name) (hints : Array (TSyntax `term)) (goal : MVarId) : TacticM Bool := goal.withContext do
  let mut attempts : Array (TSyntax `tactic) := #[]
  if tag == `single then attempts := attempts.push (← `(tactic| decide))
  for hint in hints do
    attempts := attempts ++ #[← `(tactic| exact $hint), ← `(tactic| exact (ReadAnalysis.analyze_sound $hint).1),
      ← `(tactic| (intros; exact $hint))]
  for attempt in attempts do
    try
      setGoals [goal]
      withoutRecover (Term.withoutErrToSorry (evalTactic attempt))
      if (← getGoals).isEmpty then return true
    catch _ => pure ()
  return false

/-- Apply the rule of the claim to the goal. Return the premises that no hint closes, each with its name, and the variables of the rule that stay undetermined. -/
def applyCommuteRule (hints : Array (TSyntax `term)) (goal : MVarId) :
    TacticM (List (Name × MVarId) × List MVarId) :=
  goal.withContext do
  let goalType ← instantiateMVars (← goal.getType)
  let some (_, rule) := claimOf? goalType
    | throwError "sql_commute proves only a claim of Migration.PreservesAt or Migration.CommutesOn. Use another tactic for this goal."
  let args := goalType.getAppArgs
  let application := if goalType.isAppOf ``Migration.PreservesAt then args[args.size - 2]! else args.back!
  unless application.getAppFn.isConstOf ``send do
    throwError "sql_commute reads a read that is a sent script, but the read in this goal is not. Write the read as send followed by a script."
  let some (statement, values, rest) ← firstStatement? (application.getArg! 0)
    | throwError "sql_commute cannot read the statement of the read: the script does not reduce to a list of statements. Write the read as a script of one literal statement, or apply ReadCertificate.preservesAt_send or ReadCertificate.commutesOn_send directly."
  unless ← isLast rest do
    throwError "sql_commute handles a read of one statement, and the script of the read has more statements. Apply ReadCertificate.preservesAt_send or ReadCertificate.commutesOn_send directly to each statement."
  let ruleInfo ← getConstInfo rule
  let (mvars, _, conclusion) ← forallMetaTelescope ruleInfo.type
  let mut tagged : Array (Name × MVarId) := #[]
  for index in [0:mvars.size] do
    let name := (← mvars[index]!.mvarId!.getDecl).userName
    tagged := tagged.push (name, mvars[index]!.mvarId!)
  for (name, mvar) in tagged do
    if name == `statement then unless ← isDefEq (.mvar mvar) statement do throwError "sql_commute: the statement does not fit the rule."
    if name == `values then unless ← isDefEq (.mvar mvar) values do throwError "sql_commute: the values do not fit the rule."
  unless ← isDefEq conclusion goalType do
    throwError "sql_commute: the goal does not have the shape of the rule {rule}. Check that the migration is a sent script and that the read is a sent script of one statement."
  let mut open_ : Array (Name × MVarId) := #[]
  let mut variables : Array (Name × MVarId) := #[]
  for (name, mvar) in tagged do
    if ← mvar.isAssigned then continue
    let type ← instantiateMVars (← mvar.getType)
    if ← isProp type then
      if ← closePremise name hints mvar then continue
      open_ := open_.push (name, mvar)
    else if name == `certificate then variables := variables.push (name, mvar)
    else throwError "sql_commute: the variable {name} of the rule is not determined by the goal."
  goal.assign (mkAppN (.const rule (← mkFreshLevelMVarsFor ruleInfo)) mvars)
  let unassigned ← variables.filterM fun (_, mvar) => return !(← mvar.isAssigned)
  return (open_.toList, unassigned.toList.map (·.2))

/-- Run {lit}`sql_commute`: apply the rule of the claim, and leave the premises that no hint closes. -/
syntax (name := sqlCommute) "sql_commute" (" [" term,* "]")? : tactic

/-- Run {lit}`sql_commute`: apply the rule of the claim to the main goal, close the premises of the rule from the
hints, and put the premises that stay open, with a warning for each, and the undetermined certificate in place of
the main goal. -/
@[tactic sqlCommute] def evalSqlCommute : Tactic := fun stx => do
  let hints : Array (TSyntax `term) := match stx with
    | `(tactic| sql_commute [$hints,*]) => hints.getElems
    | _ => #[]
  let goal ← getMainGoal
  let siblings := (← getGoals).drop 1
  let (open_, variables) ← applyCommuteRule hints goal
  for (name, _) in open_ do
    logWarning m!"sql_commute left the premise {name} open: {premiseAdvice name}"
  setGoals ((open_.map (·.2)) ++ variables ++ siblings)

end Belay.Sqlite.Run
