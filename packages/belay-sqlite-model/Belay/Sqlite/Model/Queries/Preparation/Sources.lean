import Belay.Sqlite.Model.Queries.Preparation.Writes
import Belay.Sqlite.Model.Queries.Select.JoinMerge

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Why the sources of {lit}`FROM` do not resolve: an issue of an expression or of a join
form ({name}`ValueIssue`), or SQLite's {lit}`no such table: %s` for a table that the
catalog does not have, which names a catalog object and so is no value issue. -/
inductive SourceIssue where
  /-- An issue of an expression or of a join form. -/
  | value (issue : ValueIssue)
  /-- {lit}`no such table: %s`, with the table name as written. -/
  | noSuchTable (name : Identifier)
  deriving Repr, DecidableEq

/-- Prefix a model restriction's path; a missing table and a prepare error keep their names. -/
def SourceIssue.under (path : List Nat) : SourceIssue → SourceIssue
  | .value issue => .value (issue.under path)
  | .noSuchTable name => .noSuchTable name

/-- The issue of a table of the initial database: SQLite names a missing one with its schema, as in
{lit}`no such table: before.t`; every other issue is unchanged. -/
def initialIssue (reference : Syntax.TableReference) : SourceIssue → SourceIssue
  | .noSuchTable name => .noSuchTable ⟨(reference.schema.map (·.bytes ++ bytes! ".")).getD [] ++ name.bytes⟩
  | .value issue => .value issue

/-- The paths of a source issue move below a node as those of its value issue do. -/
instance : Traced.Underable SourceIssue := ⟨SourceIssue.under⟩

/-- For every path and issue: moving a source issue below a node is {name}`SourceIssue.under`. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem Traced.underable_sourceIssue (path : List Nat) (issue : SourceIssue) :
    Traced.Underable.under path issue = issue.under path := rfl

/-- For every path: moving a source issue below a node is {name}`SourceIssue.under`, as a function. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem Traced.underable_sourceIssue_function (path : List Nat) :
    (Traced.Underable.under path : SourceIssue → SourceIssue) = SourceIssue.under path := rfl

/-- A value issue is a source issue ({name}`SourceIssue.value`), so the resolution of the
sources can use the functions that give value issues. -/
instance : MonadLift (Except ValueIssue) (Except SourceIssue) := ⟨Except.mapError .value⟩

/-- A traced computation with value issues is one with source issues; the trace stays. -/
instance : MonadLift (Traced ValueIssue) (Traced SourceIssue) := ⟨Traced.mapError .value⟩

/-- The rule by which a join of the kind changes an unqualified name of a column that it
merges: an inner or left join keeps the left result, a right join takes its own column,
and a full join coalesces them. -/
def Resolved.JoinKind.mergeRule : Resolved.JoinKind → MergeRule
  | .right => .takeRight
  | .full => .coalesce
  | .inner | .left => .keepLeft

end Belay.Sqlite.Model
