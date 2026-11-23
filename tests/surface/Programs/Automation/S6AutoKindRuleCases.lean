import Belay

/-! A fixture module of {lit}`tests/surface_s6_automation_test.py`: the cases of a kind rule that {lit}`sql_run`
must not take (statement rule pilot). A hint with a premise that it cannot close does not select the case of a
match: the tactic splits the match instead, and the proof stays complete. A continuing case with a choice between
results is not a single output, so {lit}`Belay.Sqlite.Run.ruleCases` keeps it unchanged, without an error. The
tactic finds the resolution premise of a kind rule by its type, whatever its name, and keeps each other premise of
the rule as a goal, also one with the name of a premise of the bridge. -/

set_option doc.verso true

namespace S6AutoKindRuleCases
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

set_option linter.unusedVariables false in
/-- For every context, statement, target, rows, resolution state and table: if the statement resolves to a plain
INSERT of the rows into the target and its step continues, the program that sends it checks a post that is always
true. The hint {lit}`present` gives the table only under a premise, so the tactic splits the match on the table
instead of a rewrite that would leave the premise open. The proof term does not use {lit}`present`, so the
linter of unused variables is off for it. -/
theorem conditional_hint_keeps_the_split (ctx : ExecutionContext) (stmt : Syntax.Statement) (target : Nat)
    (rows : List (List Resolved.Cell)) (after : ResolveState) (table : Table)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.insert target rows [] [] none, after))
    (present : True → ctx.connection.state.database.table target = some table)
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt []).continues = true) :
    (send ⟨[(stmt, [])]⟩).check (fun _ _ => True) ctx := by
  sql_run [found, present, modeled]
  all_goals trivial

/-- For every post that is always true, context, results and connection: a continuing case with the output
{lit}`.oneOf` stays as it is after {lit}`Belay.Sqlite.Run.ruleCases`, and it holds by the definition of
{name}`Sql.SendReached`. -/
theorem choice_case_stays (ctx : ExecutionContext) (results : List (List (List Value))) (next : Connection) :
    RunStep.Continuing (Sql.SendReached (fun _ _ => True) ctx) (.continued (.oneOf results) next []) := by
  run_tac do
    let goals ← Belay.Sqlite.Run.ruleCases #[] (← Lean.Elab.Tactic.getMainGoal)
    Lean.Elab.Tactic.setGoals goals
  guard_target =ₛ RunStep.Continuing (Sql.SendReached (fun _ _ => True) ctx) (.continued (.oneOf results) next [])
  intro found member _
  simp only [RunStep.executions, List.mem_singleton] at member
  subst member
  exact ⟨trivial, fun _ _ => trivial⟩

/-- For every resolution context, connection, statement, target, name, table and resolution state: the statement
resolves from the connection to a CREATE TABLE of the table with the name at the target. A reducible name for the
resolution equation, which a kind rule may use for its premise. -/
abbrev ResolvesToCreate (context : ResolveContext) (connection : Connection) (statement : Syntax.Statement)
    (target : Nat) (name : Identifier) (table : CatalogTable) (after : ResolveState) : Prop :=
  resolveStatement context connection.resolveState statement = .ok (.createTable target name table, after)

set_option linter.unusedVariables false in
/-- The kind rule of CREATE TABLE ({name}`runScriptStep_createTable_eq`) with other premises: for every resolution
context, clock, index, connection, statement, parameter values, resolution state, target, name and table, if the
database of the connection has as many row lists as catalog entries (the premise {lit}`valid`, which has the name
of a premise of the bridge) and the statement resolves to a CREATE TABLE (the premise {lit}`resolved`, stated with
{name}`ResolvesToCreate`), the step is the step that the rule gives. The rule does not need the first premise; it is there for the test. -/
theorem createTable_rule_renamed {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {name : Identifier} {table : CatalogTable}
    (valid : connection.state.database.rows.length = connection.state.database.catalog.length)
    (resolved : ResolvesToCreate context connection statement target name table after) :
    runScriptStep context clock index connection statement parameters =
      if target = connection.state.database.catalog.length ∧
          connection.state.database.rows.length = connection.state.database.catalog.length then
        .continued (.done 0) (connection.withDatabase (connection.state.database.createTable name table)) []
      else .ended unmodeledHere :=
  runScriptStep_createTable_eq resolved

section RenamedRule
attribute [-step_rule] runScriptStep_createTable_eq
attribute [step_rule] createTable_rule_renamed

/-- For every context, statement, target, name, table and resolution state: if the connection is valid and the
statement resolves to a CREATE TABLE, the program that sends it ends with no error. The renamed rule
{name}`createTable_rule_renamed` is the only kind rule of CREATE TABLE in the set here: the tactic closes its
resolution premise from the hint and keeps its premise {lit}`valid` as a goal. -/
theorem renamed_rule_keeps_its_premise (ctx : ExecutionContext) (stmt : Syntax.Statement) (target : Nat)
    (name : Identifier) (shape : CatalogTable) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.createTable target name shape, after)) :
    (send ⟨[(stmt, [])]⟩).check (fun outputs _ => outputs.all (fun o => !o.isError) = true) ctx := by
  sql_run [found]
  case valid => exact valid.1.admitted.rowsShaped.1
  case success => rfl

end RenamedRule

#print axioms conditional_hint_keeps_the_split
#print axioms choice_case_stays
#print axioms renamed_rule_keeps_its_premise

end S6AutoKindRuleCases
