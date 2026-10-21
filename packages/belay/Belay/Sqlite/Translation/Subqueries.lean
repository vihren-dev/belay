import Belay.Sqlite.Translation.Shapes

set_option doc.verso true

/-! Lift the subqueries of a statement into its list. The port of
{lit}`belay/sqlite/syntax_subqueries.py`: an expression names a subquery by its index in the
list, and each subquery names the query around it, none for the statement's query or write, else
the index of an earlier subquery. Outside a list, a subquery is refused with its range. -/

namespace Belay.Sqlite.Translation

open Lean (Json)

/-- The mappers that the parts of a query call for their operands and nested queries; the
translation's root ties them to its own functions, as they call each other. -/
structure Mappers where
  /-- Map an {lit}`expr` production of a query. -/
  expression : SqlTree → ParseNode → TranslateM Located
  /-- Map a {lit}`select` production to the clauses of {lit}`Syntax.Subquery` without its parent. -/
  clauses : SqlTree → ParseNode → TranslateM (Array (String × Located))

/-- Run the action with a new subquery list for one statement open, and give its subqueries;
the scope around it is kept. -/
def statementSubqueries (action : TranslateM α) : TranslateM (α × Array Located) := do
  let around ← get
  set { around with active := some {} }
  let result ← action
  let items := match (← get).active with
    | some listed => listed.items.filterMap id
    | none => #[]
  set around
  return (result, items)

/-- Run the action with every subquery refused with the refusal, for a clause whose subqueries
the model does not place, such as RETURNING. -/
def noSubqueries (refusal : String) (action : TranslateM α) : TranslateM α := do
  let around ← get
  set ({ active := none, refusal } : Scope)
  let result ← action
  set around
  return result

/-- Add the subquery of a {lit}`select` production to the statement's list and give its index;
its own subqueries come after it. Refuse it where no list is open. -/
def lift (mappers : Mappers) (tree : SqlTree) (select : ParseNode) : TranslateM Nat := do
  let scope ← get
  let some listed := scope.active | unsupported select scope.refusal
  let index := listed.items.size
  let around := listed.current
  set { scope with active := some { items := listed.items.push none, current := some index } }
  let clauses ← mappers.clauses tree select
  let scope ← get
  let items := (scope.active.map (·.items)).getD #[]
  let parent := leaf (match around with | some position => (position : Json) | none => .null) select.start select.stop
  let item := structure' (clauses.extract 0 8 ++ #[("parent", parent)] ++ clauses.extract 8 clauses.size)
    select.start select.stop
  set { scope with active := some { items := items.set! index (some item), current := around } }
  return index

/-- The fields that a statement's JSON omits when they have these values, so that statements
without them keep the form that frozen records hold. -/
def defaultFields : List (String × Json) := [("subqueries", .arr #[]), ("having", .null), ("distinct", false)]

/-- The statement constructor with its fields, the {lit}`subqueries` field and the fields
{lit}`after` it, in the order of the Lean constructor; its JSON omits each field of
{name}`defaultFields` that has its default value. -/
def withSubqueries (name : String) (fields : Array (String × Located)) (items : Array Located) (start stop : Nat)
    (after : Array (String × Located) := #[]) : Located :=
  let parts := fields ++ #[("subqueries", sequence items start stop)] ++ after
  let kept := parts.filter fun (field, part) => defaultFields.lookup field != some part.value
  { value := Json.mkObj [(name, fieldObject kept)], start, stop, children := parts.map (·.2) }

end Belay.Sqlite.Translation
