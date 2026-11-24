import Belay.Sqlite.Programs.Scripts.SendStepRules
import Belay.Sqlite.Programs.Claims.ReadStepRule
import Belay.Sqlite.Programs.Automation.SqlRunShape

set_option doc.verso true

/-! The rules that {lit}`sql_run` applies (ADR 0017, S6): for each kind of program step the public rule
and how the tactic treats each premise of the rule. The rules are theorems with their own proofs; this
module only chooses among them, so a wrong choice makes the tactic fail and cannot make it accept a false
goal. -/

namespace Belay.Sqlite.Run
open Lean Elab Tactic

/-- The most rules that one run of {lit}`sql_run` applies along one path of the program. The limit stops a
program that unfolds without end; a real program is far below it. -/
def traversalFuel : Nat := 400

/-- A syntax premise left open prevents entry into the outcome of the read or send rule. -/
def blockingPremises : List Name := [`isStatement, `isSelect]

/-- What the tactic does with one premise of a rule. -/
inductive Role where
  /-- A premise about the context, the statement or the model. The tactic tries the hints and the
  hypotheses, and leaves the goal open when none fits. -/
  | side
  /-- The continuation runs under these binders of the reached postcondition. -/
  | outcome (names : List Name)

/-- The names of the premises of the rules. A goal with another name is a variable of the rule, such as the
position of a table. A premise that is closed sets it. -/
def premiseNames : List Name :=
  [`valid, `modeled, `notChoice, `reached, `isStatement, `isSelect,
    `notInsertSelect]

/-- The reached post is an outcome. Each other named premise is a side goal. -/
def roleOf (kind : Name) (premise : Name) : Role :=
  if premise == `reached then
    if kind == ``Model.Syntax.Statement.select then .outcome [`selected, `choice]
    else .outcome [`output, `next, `step, `valid]
  else .side

/-- The tactic that applies the rule for a sent statement of the given kind. A statement of a kind without a
rule of its own is sent with the general rule {name}`Sql.check_send_of_step_notInsertSelect`, whose premises stay open. -/
def sendRule (kind : Name) : TacticM (TSyntax `tactic) :=
  if kind == ``Model.Syntax.Statement.select then
    `(tactic| refine' Sql.check_send_select ?isSelect ?modeled ?reached)
  else
    `(tactic| refine' Sql.check_send_of_step_notInsertSelect ?notInsertSelect ?modeled ?notChoice ?reached ?valid)

end Belay.Sqlite.Run
