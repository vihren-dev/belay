import Belay.Sqlite.SqlRunShape

set_option doc.verso true

/-! The part of a program that a replay of its first scripts can follow. A replay starts at the initial
database, so it can run only the scripts that the program sends before any Lean code runs. The functions
only inspect terms. They prove nothing: the checker certifies the claim itself. -/

namespace Belay.Sqlite.Check
open Lean Meta

/-- The scripts of a program that a replay at the initial database can run, and whether more of the program
is out of reach. -/
structure ProgramScripts where
  /-- The scripts that the program sends first, before any Lean code runs, in order. -/
  scripts : Array Expr := #[]
  /-- Whether the program has a part that the replay cannot run: a continuation that is Lean code, a branch
  of Lean, or a term that is no program built from {name}`send`, {name}`query` and {name}`single`. -/
  leanCode : Bool := false

/-- The default number of unfoldings and binds that {lit}`programScripts` follows. -/
def defaultProgramFuel : Nat := 64

/-- Read the program: a sent script, a query or a single value gives its script; a pure program has none; a
bind keeps the scripts of its first part and marks the rest as Lean code; a map keeps the scripts of its
program; a defined program is unfolded. Any other program is Lean code. The first argument is the fuel that
bounds the unfolding; use {lean}`defaultProgramFuel` when the caller has no other limit. -/
def programScripts : Nat → Expr → MetaM ProgramScripts
  | 0, _ => pure { leanCode := true }
  | fuel + 1, program => do
    checkSystem "SQL program inspection"
    let reduced ← withTransparency .instances (whnf program)
    match ← Run.classifyProgram reduced with
    | .send script | .single script | .query script => return { scripts := #[script] }
    | .pure => return {}
    | .map => programScripts fuel (reduced.getArg! 3)
    | .bind => return { (← programScripts fuel (reduced.getArg! 2)) with leanCode := true }
    | .definition _ =>
      match ← unfoldDefinition? reduced with
      | some unfolded => programScripts fuel unfolded
      | none => return { leanCode := true }
    | .branch | .raw | .opaque => return { leanCode := true }

end Belay.Sqlite.Check
