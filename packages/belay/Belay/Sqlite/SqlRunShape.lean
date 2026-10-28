import Lean.Meta.Basic
import Belay.Sqlite.ExecutionSuccess
import Belay.Sqlite.ProgramQueries

set_option doc.verso true

/-! What {lit}`sql_run` reads from a goal (ADR 0017, S6): the program of a check goal, the head of the
program, and the first statement of a sent script. These functions only inspect terms. They prove nothing,
so a wrong answer can make the tactic fail but cannot make it accept a false goal: every proof step
that uses the answer is a checked rule. -/

namespace Belay.Sqlite.Run
open Lean Meta

/-- The program, as {name}`Sql.check` takes it, when the goal is a check after reducible unfolding.
The unfolding turns {name}`Sql.ifOk` and {name}`Sql.andOk` into checks. -/
def checkProgram? (goal : Expr) : MetaM (Option Expr) := do
  let goal ← whnfR goal
  return if goal.isAppOfArity ``Sql.check 4 then some (goal.getArg! 1) else none

/-- The kinds of program that {lit}`sql_run` treats in its own way. -/
inductive Head where
  /-- {name}`Sql.bind`, the {lit}`>>=` of a {lit}`do` block. -/
  | bind
  /-- {name}`Sql.pure`. -/
  | pure
  /-- {name}`Sql.map`. -/
  | map
  /-- {name}`send`, with its script. -/
  | send (script : Expr)
  /-- {name}`single`, with its script. -/
  | single (script : Expr)
  /-- {name}`query`, with its script. -/
  | query (script : Expr)
  /-- A branch of Lean: {lit}`if`, {lit}`match`; {lit}`split` opens its cases. -/
  | branch
  /-- A raw {name}`Sql.exec`; the tactic has no rule for a program that is not built by the public
  constructors. -/
  | raw
  /-- A defined program, to unfold. -/
  | definition (name : Name)
  /-- Another term, for example a variable. -/
  | opaque

/-- The head of a program, after the reducible unfolding of the monad instance. -/
def classifyProgram (program : Expr) : MetaM Head := do
  let program ← withTransparency .instances (whnf program)
  let head := program.getAppFn
  match head.constName? with
  | some name =>
    if name == ``Sql.bind then return .bind
    else if name == ``Sql.pure then return .pure
    else if name == ``Sql.map then return .map
    else if name == ``Sql.exec then return .raw
    else if name == ``send then return .send (program.getArg! 0)
    else if name == ``single then return .single (program.getArg! 0)
    else if name == ``query then return .query (program.getArg! 0)
    else if name == ``ite || name == ``dite then return .branch
    else if (← isMatcherApp program) then return .branch
    else return .definition name
  | none => return .opaque

/-- The first statement of a script, its values and the rest of the statements, when the script
reduces to a list of statements. A script that depends on a variable list is not reduced. -/
def firstStatement? (script : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let statements ← whnfD (← mkAppM ``Script.statements #[script])
  match_expr statements with
  | List.cons _ pair rest =>
    match_expr (← whnfD pair) with
    | Prod.mk _ _ statement values => return some (statement, values, rest)
    | _ => return none
  | _ => return none

/-- Whether the rest of a statement list is empty. -/
def isLast (rest : Expr) : MetaM Bool := do
  return (← whnfD rest).isAppOf ``List.nil

/-- The name of the constructor of {name}`Model.Syntax.Statement` that builds a statement, when it reduces to
one. A statement that is a variable or a field of a structure has no kind. A pragma has the name of the
constructor of {name}`Model.Syntax.Pragma` that builds it, because the pragmas that set a value and those that
read a table have different rules. -/
def statementKind? (statement : Expr) : MetaM (Option Name) := do
  let statement ← whnfD statement
  let constructor? (term : Expr) : MetaM (Option Name) :=
    return term.getAppFn.constName?.filter (← getEnv).isConstructor
  let head ← constructor? statement
  if head == some ``Model.Syntax.Statement.pragma then
    return ← constructor? (← whnfD statement.appArg!)
  return head

end Belay.Sqlite.Run
