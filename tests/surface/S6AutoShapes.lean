import Belay

/-! A fixture module of `tests/surface_s6_automation_test.py`: the shapes that {lit}`sql_run` refuses or stops
at. A program that starts with a raw execution step, or is a variable, gives an error before the tactic changes
the goal. A program that has such a part after a rule leaves that part as a goal and warns. -/

set_option doc.verso true

namespace S6AutoShapes
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- error: sql_run cannot start: the program is a raw execution step. Prove this goal with the public rules, for example Sql.check_bind and Sql.check_send_of_step. -/
#guard_msgs in
example (statement : Syntax.Statement) (values : List Value) (post : Unit → ExecutionContext → Prop)
    (context : ExecutionContext) :
    (Sql.exec statement values (fun _ => Sql.pure ())).check post context := by
  sql_run

/-- error: sql_run cannot start: the program is a variable or an unknown term. Prove this goal with the public rules, for example Sql.check_bind and Sql.check_send_of_step. -/
#guard_msgs in
example (program : Sql Nat) (post : Nat → ExecutionContext → Prop) (context : ExecutionContext) :
    program.check post context := by
  sql_run

/-- error: sql_run proves a check of a SQL program, a triple, or the goal that mvcgen leaves for one. This goal is none of these. Use another tactic, or state the claim with Sql.check. -/
#guard_msgs in
example : (2 : Nat) + 2 = 4 := by
  sql_run

/-- warning: sql_run stopped: the program is a variable or an unknown term. The goal stays open. -/
#guard_msgs in
/-- A part after a rule that the tactic cannot read stays as a goal, with a warning, and an explicit hypothesis
closes it. -/
theorem unreadable_continuation_stays_open (rest : Nat → Sql Nat) (post : Nat → ExecutionContext → Prop)
    (context : ExecutionContext) (given : (rest 1).check post context) :
    ((Sql.pure 1).bind rest).check post context := by
  sql_run
  exact given

/-- error: sql_run cannot start: the statement is not a constructor that Lean can read, and no hint closes the resolution of an insert, update, delete or ADD COLUMN. Prove this goal with the public rules, for example Sql.check_bind and Sql.check_send_of_step. -/
#guard_msgs in
example (statement : Syntax.Statement) (values : List Value) (post : List Output → ExecutionContext → Prop)
    (context : ExecutionContext) :
    (send ⟨[(statement, values)]⟩).check post context := by
  sql_run

/-- A statement that Lean cannot read, for example a field of a structure, takes the rule from the hypotheses:
here the resolution is a plain DELETE, so the tactic applies {name}`Sql.check_send_plainDelete` and leaves its
two outcome goals, which the trivial post closes. -/
theorem unreadable_statement_takes_the_rule_of_its_resolution (statement : Syntax.Statement)
    (values : List Value) (context : ExecutionContext) (target : Nat) (filter : Option Resolved.Expr)
    (after : ResolveState) (table : Table) (valid : context.connection.state.Holds (Database.Valid Profile.pinned))
    (found : resolveStatement runContext context.connection.resolveState statement =
      .ok (.delete target filter [] [] none, after))
    (present : context.connection.state.database.table target = some table)
    (modeled : ∃ output next others, runScriptStep runContext context.clock context.index context.connection
      statement values = .continued output next others) :
    (send ⟨[(statement, values)]⟩).check (fun _ _ => True) context := by
  sql_run
  all_goals (intros; trivial)

end S6AutoShapes
