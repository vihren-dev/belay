import Lean.Elab.Tactic.Basic
import Belay.Sqlite.PlainInsertStepRule
import Belay.Sqlite.PlainUpdateStepRule
import Belay.Sqlite.PlainDeleteStepRule
import Belay.Sqlite.AddColumnStepRule
import Belay.Sqlite.ReadStepRule
import Belay.Sqlite.SqlRunShape

set_option doc.verso true

/-! The rules that {lit}`sql_run` applies (ADR 0017, S6): for each kind of program step the public rule
and how the tactic treats each premise of the rule. The rules are theorems with their own proofs; this
module only chooses among them, so a wrong choice makes the tactic fail and cannot make it accept a false
goal. -/

namespace Belay.Sqlite.Run
open Lean Elab Tactic

/-- What the tactic does with one premise of a rule. -/
inductive Role where
  /-- A premise about the context, the statement or the model. The tactic tries the hints and the
  hypotheses, and leaves the goal open when none fits. -/
  | side
  /-- A premise that holds for every outcome of the step: the tactic introduces variables and hypotheses
  with the given names, and replaces the variable named {lit}`next` by the connection that an equation among
  the hypotheses gives. The goal that remains is a check of the rest of the program. -/
  | outcome (names : List Name) (replacesNext : Bool)

/-- The names of the premises of the rules. A goal with another name is a variable of the rule, such as the
position of a table. A premise that is closed sets it. -/
def premiseNames : List Name :=
  [`valid, `found, `present, `modeled, `notChoice, `success, `failure, `reached, `isStatement, `isSelect]

/-- The role of a premise, by the name that the rule application gives it. The premises of a failed step
and of a successful step are outcomes. All other premises are side goals. -/
def roleOf (kind : Name) (premise : Name) : Role :=
  if premise == `success then
    if kind == ``Model.Syntax.Statement.addColumn then
      .outcome [`output, `value, `default, `next, `noError, `ongoing, `timed, `clockNull, `clockRead, `nextIs, `valid] true
    else .outcome [`output, `value, `next, `noError, `ongoing, `timed, `nextIs, `valid] true
  else if premise == `failure then .outcome [`output, `value, `next, `failed, `ongoing, `nextIs, `valid] true
  else if premise == `reached then
    if kind == ``Model.Syntax.Statement.select then .outcome [`selected, `choice] false
    else .outcome [`output, `next, `step, `valid] false
  else .side

/-- The tactic that applies the rule for a sent statement of the given kind. A statement of a kind without a
rule of its own is sent with the general rule {name}`Sql.check_send_of_step`, whose premises stay open. -/
def sendRule (kind : Name) : TacticM (TSyntax `tactic) :=
  if kind == ``Model.Syntax.Statement.insert then
    `(tactic| refine' Sql.check_send_plainInsert ?valid ?found ?present ?modeled ?success ?failure)
  else if kind == ``Model.Syntax.Statement.update then
    `(tactic| refine' Sql.check_send_plainUpdate ?valid ?found ?present ?modeled ?success ?failure)
  else if kind == ``Model.Syntax.Statement.delete then
    `(tactic| refine' Sql.check_send_plainDelete ?valid ?found ?present ?modeled ?success ?failure)
  else if kind == ``Model.Syntax.Statement.addColumn then
    `(tactic| refine' Sql.check_send_addColumn ?valid ?found ?present ?modeled ?success ?failure)
  else if kind == ``Model.Syntax.Statement.select then
    `(tactic| refine' Sql.check_send_select ?isSelect ?modeled ?reached)
  else
    `(tactic| refine' Sql.check_send_of_step ?modeled ?notChoice ?reached ?valid)

end Belay.Sqlite.Run
