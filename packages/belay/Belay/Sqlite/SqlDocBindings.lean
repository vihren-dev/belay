import Belay.Sqlite.SqlParameters
import Belay.Sqlite.Values

set_option doc.verso true

/-! The values of the parameters of a checked SQL documentation block. A block binds its
parameters in one of two ways. With named bindings, each parameter name is a header argument,
and the shared parameter plan in file mode decides the numbers. A {lit}`$name` is an argument like
the others and never a Lean variable, and {lit}`:a` and {lit}`?1` bind as in a {lit}`sql` term. With the explicit list, the header gives one list of values for each
statement and no name is needed. This module decides what is wrong with the inputs, as problems at the
SQL token or the header argument that the user can change. It does not elaborate Lean terms. -/

namespace Belay.Sqlite.SqlDoc

open Translation Belay.Sqlite

/-- The header options of a block. A parameter with one of these names cannot be bound by name,
because the header argument of that name has another meaning. -/
def reservedNames : List String := ["db", "env", "values", "expected", "error"]

/-- Where a problem is shown. -/
inductive Place where
  /-- A byte range of the SQL text of the block. -/
  | sql (start stop : Nat)
  /-- The header argument with the name. -/
  | header (name : String)
  deriving Repr, BEq

/-- Something the user must change: where it is, and what to do. -/
structure Problem where
  /-- Where the problem is shown. -/
  place : Place
  /-- What is wrong and what the user can do. -/
  message : String
  deriving Repr, BEq

/-- The header argument that binds a parameter, or the problem at the parameter when its name
cannot be a header argument. {lit}`?` and {lit}`?NNN` give {lit}`p` and the number, as in a
{lit}`sql` term. -/
def bindingName (parameter : Parameter) : Except Problem String :=
  let place := Place.sql parameter.start parameter.stop
  match parameter.text.toList with
  | '?' :: _ => .ok s!"p{parameter.number}"
  | _ :: name =>
    if isLeanIdentifier (String.ofList name) then .ok (String.ofList name)
    else .error { place, message := s!"the parameter {parameter.text} has a name that a header argument cannot have; bind the parameters of this block with the explicit list (values := ...)" }
  | [] => .ok s!"p{parameter.number}"

/-- The problem of a parameter whose name is a header option. -/
def reservedProblem (parameter : Parameter) (name : String) : Problem :=
  { place := .sql parameter.start parameter.stop,
    message := s!"the parameter {parameter.text} has the name {name} of a header option, so a header argument cannot bind it; bind the parameters of this block with the explicit list (values := ...)" }

/-- The names that the parameters need, each with the first parameter in text order that gives it,
or the problems of parameters whose names cannot be bound by name. -/
def requiredNames (parameters : List Parameter) : Except (List Problem) (List (String × Parameter)) :=
  let named := parameters.map fun parameter => (parameter, bindingName parameter)
  let problems := named.filterMap fun (parameter, name) => match name with
    | .error problem => some problem
    | .ok name => if reservedNames.contains name then some (reservedProblem parameter name) else none
  if problems.isEmpty then
    .ok (named.foldl (fun found (parameter, name) => match name with
      | .ok name => if found.any (·.1 == name) then found else found ++ [(name, parameter)]
      | .error _ => found) [])
  else .error problems

/-- The plan of a block that binds its parameters by name, or the problems with its parameters
and the header arguments. {lit}`supplied` is the names of the header arguments that are not
options. A parameter without a header argument is a problem at the parameter, and a header
argument that no parameter needs is a problem at the argument. -/
def namedPlan (statements : List (List Parameter)) (supplied : List String) :
    Except (List Problem) ParameterPlan := do
  let required ← requiredNames statements.flatten
  let plan ← match planParameters statements .file with
    | .ok plan => pure plan
    | .error diagnostic =>
      let hint := "; or bind the parameters of this block with the explicit list (values := ...)"
      throw [{ place := .sql diagnostic.start diagnostic.stop, message := diagnostic.message ++ hint }]
  let missing := required.filterMap fun (name, parameter) =>
    if supplied.contains name then none
    else some ({ place := Place.sql parameter.start parameter.stop,
                 message := s!"the parameter {parameter.text} has no value; add the header argument ({name} := value) to the block" } : Problem)
  let unused := (supplied.eraseDups.filter fun name => !required.any (·.1 == name)).map fun name =>
    ({ place := Place.header name,
       message := s!"the header argument {name} binds no parameter of the SQL; remove it, or write a parameter with that name" } : Problem)
  if missing.isEmpty && unused.isEmpty then pure plan else throw (missing ++ unused)

/-- The values of the statements for a plan: the value that {lit}`lookup` gives for the name of
each slot, or NULL for a slot that no parameter uses. -/
def planValues (plan : ParameterPlan) (lookup : String → Option Value) : List (List Value) :=
  plan.slots.map fun slots => slots.map fun
    | .null => Value.null
    | .source source => (lookup source.name).getD Value.null

/-- The largest parameter number of a statement, or 0 for a statement without parameters. -/
def largestNumber (parameters : List Parameter) : Nat :=
  parameters.foldl (fun largest parameter => max largest parameter.number) 0

/-- The problems of an explicit list of values: one list for each statement, and in each list one
value for each number from 1 to the largest number of the statement. A shorter list would bind
NULL by accident, and a longer one binds a number that the statement does not have, which
SQLite refuses. A number that no parameter uses takes any value, and NULL is the usual one. -/
def explicitProblems (statements : List (List Parameter)) (values : List (List Value)) : List Problem :=
  let header := Place.header "values"
  if statements.length != values.length then
    [{ place := header,
       message := s!"the list (values := ...) has {values.length} lists and the SQL has {statements.length} statements; give one list for each statement, and the empty list for a statement without parameters" }]
  else
    (statements.zip values).zipIdx.filterMap fun ((parameters, list), index) =>
      let largest := largestNumber parameters
      if list.length == largest then none
      else some { place := header,
                  message := s!"statement {index + 1} uses parameter numbers up to {largest}, and its list has {list.length} values; give one value for each number from 1 to {largest}, with NULL for a number that no parameter uses" }

end Belay.Sqlite.SqlDoc
