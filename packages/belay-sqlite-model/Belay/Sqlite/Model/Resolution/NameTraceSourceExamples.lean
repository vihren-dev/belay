import Belay.Sqlite.Model.Resolution.MergedNameExamples
import Belay.Sqlite.Model.Resolution.SourceListFromArms

set_option doc.verso true

/-! Examples of the name trace of the sources of {lit}`FROM`: a table and its alias, a missing table
with the tables and views of the catalog as candidates, the names of {lit}`USING`, a table of the initial
database, and a derived table. The catalog is {lit}`MergedNameExamples.merging`: the tables
{lit}`t`, {lit}`r`, {lit}`u`, {lit}`w` and {lit}`v` at positions 0 to 4. -/

namespace Belay.Sqlite.Model.NameTraceSourceExamples
open Resolution.MergedNameExamples Resolution.JoinExamples Resolution.UsingExamples

/-- The traced resolution of a {lit}`FROM` list over the catalog {name}`merging`. -/
private def traced (source : Syntax.TableReference) (joins : List Syntax.Join := [])
    (initial : Option Catalog := none) :=
  resolveSourcesTraced merging (some source) joins 0 (initial := initial)

/-- Whether a result is a source of the given kind and index. -/
private def isSource (kind : SourceKind) (index : Nat) : NameResult → Bool
  | .source reference => reference.kind == kind && reference.index == index
  | .found _ | .ambiguous _ | .missing .. | .schema _ | .resultColumn _ | .declares | .compared ..
  | .unreached _ => false

/-- Whether a result is a name that is bound to exactly the given number of columns. -/
private def foundCount (count : Nat) : NameResult → Bool
  | .found bindings => bindings.length == count
  | .ambiguous _ | .missing .. | .source _ | .schema _ | .resultColumn _ | .declares | .compared ..
  | .unreached _ => false

/-- Whether a result is a missing name whose candidates are the given number of catalog objects. -/
private def missingObjects (count : Nat) : NameResult → Bool
  | .missing .error candidates => candidates.length == count && candidates.all fun
    | .catalogObject .. => true
    | .column _ | .resultAlias .. | .source _ => false
  | .missing .textLiteral _ | .missing .booleanKeyword _ | .missing .rowidName _ | .found _ | .ambiguous _
  | .source _ | .schema _ | .resultColumn _ | .declares | .compared .. | .unreached _ => false

/-- A table with an alias records the table as a source at child 0 of the first source and the alias at
child 1. -/
private def aliasedTable : Bool :=
  (match (traced { table := name! "t", alias := some (name! "x") }).trace with
    | [table, alias] =>
      table.path == [1, 0] && table.role == .tableReference && isSource .baseTable 0 table.result &&
      alias.path == [1, 1] && alias.role == .aliasDeclaration && alias.result == .declares
    | _ => false)

#guard aliasedTable

/-- A table that the catalog lacks fails with SQLite's {lit}`no such table`, and its occurrence lists the
five tables of the catalog as candidates. -/
private def missingTable : Bool :=
  (match traced (table (name! "z")) with
    | ⟨.error (.noSuchTable missing), [occurrence]⟩ =>
      missing == name! "z" && occurrence.path == [1, 0] && missingObjects 5 occurrence.result
    | _ => false)

#guard missingTable

/-- The name of {lit}`USING` is recorded at its position in the {lit}`USING` list of the join, bound to
the column of each side. -/
private def usingName : Bool :=
  (match (traced (table (name! "t")) [usingJoin [] (name! "r") [name! "a"]]).trace with
    | [left, right, using_] =>
      left.path == [1, 0] && right.path == [2, 0, 1, 0] &&
      using_.path == [2, 0, 3, 0] && using_.role == .columnReference && foundCount 2 using_.result
    | _ => false)

#guard usingName

/-- A name of {lit}`USING` that a side lacks fails, and the occurrence lists the common columns. -/
private def usingMissing : Bool :=
  (match traced (table (name! "t")) [usingJoin [] (name! "r") [name! "zz"]] with
    | ⟨.error _, trace⟩ =>
      (match trace.getLast? with
        | some last => last.path == [2, 0, 3, 0] && (match last.result with
            | .missing .error _ => true
            | .missing .textLiteral _ | .missing .booleanKeyword _ | .missing .rowidName _ | .found _
            | .ambiguous _ | .source _ | .schema _ | .resultColumn _ | .declares | .compared ..
            | .unreached _ => false)
        | none => false)
    | ⟨.ok _, _⟩ => false)

#guard usingMissing

/-- A table with the schema {lit}`before` records the schema at child 4 and then the table of the initial
database, whose source has the kind {lit}`initialTable`. -/
private def initialTable : Bool :=
  (match (traced { table := name! "t", alias := none, schema := some Syntax.initialSchemaName }
      (initial := some merging)).trace with
    | [schema, table] =>
      schema.path == [1, 4] && schema.role == .qualifier && schema.result == .schema true &&
      table.path == [1, 0] && isSource .initialTable 0 table.result
    | _ => false)

#guard initialTable

/-- A derived table has no table name, so the trace holds only its alias, at child 1 of the source. -/
private def derivedTable : Bool :=
  let derived : ScopeSource := { name := name! "d", columns := [{ name := name! "a", declaredType := none }], role := .derivedTable }
  (match (resolveSourcesTraced merging (some { table := name! "", alias := some (name! "d"), query := some 0 }) []
      0 (fun _ => .ok derived)).trace with
    | [alias] => alias.path == [1, 1] && alias.role == .aliasDeclaration
    | _ => false)

#guard derivedTable

end Belay.Sqlite.Model.NameTraceSourceExamples
