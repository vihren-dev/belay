import Lean.Elab.DocString

set_option doc.verso true

/-! The header of a checked SQL documentation block, such as
{lit}`sql (db := start) (id := 7) +error`. Native Verso reads the header before it calls the
handler, so a value is a number, a string or the name of a definition. This module sorts the
arguments into the options of the block and the bindings of parameters, and reports the
arguments that it cannot use. -/

namespace Belay.Sqlite.SqlDoc

open Lean Elab Term
open scoped Lean.Doc.Syntax

/-- A named argument of the header: its name, the whole argument for errors, and its value. -/
structure Argument where
  /-- The name before {lit}`:=`. -/
  name : String
  /-- The syntax of the whole argument, where an error about it is shown. -/
  reference : Syntax
  /-- The number, string or name after {lit}`:=`. -/
  value : Doc.DocArg

/-- The header sorted by meaning. -/
structure Header where
  /-- {lit}`(db := name)`: the closed database the SQL starts from. -/
  database : Option Argument := none
  /-- {lit}`(env := name)`: the closed environment with the clock and counters. -/
  environment : Option Argument := none
  /-- {lit}`(values := name)`: the explicit values of the parameters of each statement. -/
  explicitValues : Option Argument := none
  /-- {lit}`(expected := name)`: the complete typed list of outputs. -/
  typedOutputs : Option Argument := none
  /-- {lit}`+error`: the block expects an SQL failure. -/
  expectsError : Bool := false
  /-- Every other named argument, each binding the parameter of its name. -/
  bindings : List Argument := []
  /-- What is wrong with the header, each at the argument that causes it. -/
  problems : List (Syntax × String) := []

/-- A named argument of a header, or none for another kind. -/
def namedArgument? (argument : TSyntax `doc_arg) : Option (Ident × TSyntax `arg_val) :=
  match argument with
  | `(doc_arg| $name:ident := $value:arg_val) => some (name, value)
  | `(doc_arg| ($name:ident := $value:arg_val)) => some (name, value)
  | _ => none

/-- A flag of a header: its name, and whether it is on. -/
def flagArgument? (argument : TSyntax `doc_arg) : Option (Ident × Bool) :=
  match argument with
  | `(doc_arg| +$name:ident) => some (name, true)
  | `(doc_arg| -$name:ident) => some (name, false)
  | _ => none

/-- Add one argument to the header: an option, a binding, the {lit}`error` flag, or a problem. A
name that appears twice, a flag other than {lit}`error`, and a positional argument are problems. -/
def Header.add (header : Header) (argument : TSyntax `doc_arg) : TermElabM Header := do
  let problem (message : String) : Header := { header with problems := header.problems ++ [(argument.raw, message)] }
  if let some (flag, enabled) := flagArgument? argument then
    if flag.getId.eraseMacroScopes == `error then return { header with expectsError := enabled }
    return problem s!"a SQL block has only the flag +error; remove {flag.getId.eraseMacroScopes}"
  let some (nameSyntax, valueSyntax) := namedArgument? argument
    | return problem "a SQL block takes named arguments; bind a parameter with (name := value)"
  let name := nameSyntax.getId.eraseMacroScopes.toString
  let value ← Doc.DocArg.ofSyntax valueSyntax
  let entry : Argument := { name, reference := argument.raw, value }
  let options := [header.database, header.environment, header.explicitValues, header.typedOutputs]
  if (options.filterMap id ++ header.bindings).any (·.name == name) then
    return problem s!"the header argument {name} appears twice; keep one"
  match name with
  | "db" => return { header with database := some entry }
  | "env" => return { header with environment := some entry }
  | "values" => return { header with explicitValues := some entry }
  | "expected" => return { header with typedOutputs := some entry }
  | "error" => return problem "error is a flag; write +error"
  | _ => return { header with bindings := header.bindings ++ [entry] }

/-- Sort the arguments of the header. -/
def parseHeader (arguments : Array (TSyntax `doc_arg)) : TermElabM Header :=
  arguments.foldlM Header.add {}

end Belay.Sqlite.SqlDoc
