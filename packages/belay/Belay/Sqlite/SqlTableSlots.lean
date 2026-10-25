import Belay.Sqlite.SqlDiagnostics

set_option doc.verso true

/-! The places of a statement where the syntax names a table: the target of a write, the
table of an index or trigger, and the named tables of {lit}`FROM` in the statement's query and in
its indexed subqueries. The syntax fixes each place as a path of {lit}`Span.select`, so the
search reads no text for a name. Each place also checks that the bytes it selects write the name
that the syntax holds, so a path that selects another node gives no place. A name that a
{lit}`WITH` definition of the statement also names is not a place, because the definition may
shadow the table. A column or an alias is no place; the editor does not describe them without
the name trace of the resolver (the editor task, part 2b). -/

namespace Belay.Sqlite

open Belay.Sqlite.Model Translation

/-- A place of a statement that names a table: the table name as the syntax holds it and the
half-open byte range of its text in the SQL text. -/
structure TableSlot where
  /-- The table name as the syntax holds it. -/
  name : Identifier
  /-- The first byte of the written name, which may be quoted. -/
  start : Nat
  /-- The byte after the written name. -/
  stop : Nat
  deriving Repr, BEq

/-- The place at the path of the span when the selected bytes write the name, with ASCII case
ignored and quotes removed ({name}`leafName?`). A path that selects another node, or an empty
range, gives {lean}`(none : Option TableSlot)`. For example, the path of the table of
{lit}`INSERT INTO t VALUES (1)` selects the bytes 12 to 13. -/
def slotAt? (bytes : ByteArray) (span : Span) (path : List Nat) (name : Identifier) : Option TableSlot :=
  let (start, stop) := span.select path
  if start < stop && leafName? bytes (start, stop) == some name.folded then some { name, start, stop }
  else none

/-- The place of a named table of {lit}`FROM` at the path of its reference. A table-valued function
and a derived table name no table. The name is child 0 of the reference
({name}`Syntax.TableReference`). -/
def referenceSlot? (bytes : ByteArray) (span : Span) (path : List Nat)
    (reference : Syntax.TableReference) : Option TableSlot :=
  if reference.query.isNone && reference.arguments.isNone then slotAt? bytes span (path ++ [0]) reference.table
  else none

/-- The places of the first source and the joins of a query whose clauses start at the path
{lit}`prefix_`: the source is child 1 and the joins are child 2, and child 1 of a join is its
source ({name}`Syntax.Subquery`, {lit}`Syntax.Statement.select`). -/
def querySlots (bytes : ByteArray) (span : Span) (prefix_ : List Nat) (source : Option Syntax.TableReference)
    (joins : List Syntax.Join) : List TableSlot :=
  (source.bind (referenceSlot? bytes span (prefix_ ++ [1]))).toList ++
    (joins.zipIdx.filterMap fun (join, index) => referenceSlot? bytes span (prefix_ ++ [2, index, 1]) join.source)

/-- The places of the indexed subqueries, which the statement holds as child {lit}`field`. -/
def subquerySlots (bytes : ByteArray) (span : Span) (field : Nat) (subqueries : List Syntax.Subquery) : List TableSlot :=
  subqueries.zipIdx.flatMap fun (subquery, index) => querySlots bytes span [field, index] subquery.source subquery.joins

/-- The names of the {lit}`WITH` definitions of the subqueries. -/
def definitionNames (subqueries : List Syntax.Subquery) : List (List UInt8) :=
  subqueries.filterMap fun subquery => subquery.commonTable.map (·.name.folded)

/-- The table that the statement creates or drops, so that a name of an earlier statement of a
script no longer names the table that the database had at the start. -/
def replacedTable? : Syntax.Statement → Option Identifier
  | .createTable name .. | .dropTable name _ => some name
  | .createView .. | .createIndex .. | .addColumn .. | .dropView .. | .dropIndex .. | .begin | .commit
  | .rollback | .insert .. | .update .. | .delete .. | .select .. | .pragma _ | .createTrigger ..
  | .dropTrigger .. => none

/-- The places of a statement, from its syntax and its ranges, without the places whose name a
{lit}`WITH` definition of the statement names. A statement of another form, and the body of a
trigger, have none. -/
def tableSlotsOf (bytes : ByteArray) (item : Located Syntax.Statement) : List TableSlot :=
  let span := item.span
  let target (path : List Nat) (name : Identifier) := (slotAt? bytes span path name).toList
  let (found, subqueries) : List TableSlot × List Syntax.Subquery := match item.value with
    | .select (source := source) (joins := joins) (subqueries := subqueries) .. =>
      (querySlots bytes span [] source joins ++ subquerySlots bytes span 8 subqueries, subqueries)
    | .insert (table := table) (subqueries := subqueries) .. =>
      (target [0] table ++ subquerySlots bytes span 6 subqueries, subqueries)
    | .update (table := table) (subqueries := subqueries) .. =>
      (target [0] table ++ subquerySlots bytes span 4 subqueries, subqueries)
    | .delete (table := table) (subqueries := subqueries) .. =>
      (target [0] table ++ subquerySlots bytes span 3 subqueries, subqueries)
    | .createIndex (table := table) .. => (target [2] table, [])
    | .addColumn table _ => (target [0] table, [])
    | .dropTable name _ => (target [0] name, [])
    | .createTrigger (table := table) .. => (target [4] table, [])
    | .createView (query := query) (subqueries := subqueries) .. =>
      (querySlots bytes span [3] query.source query.joins ++ subquerySlots bytes span 4 subqueries, subqueries)
    | .createTable .. | .dropView .. | .dropIndex .. | .begin | .commit | .rollback | .pragma _
    | .dropTrigger .. => ([], [])
  found.filter fun slot => !(definitionNames subqueries).contains slot.name.folded

end Belay.Sqlite
