import Belay.Sqlite.SqlDiagnostics

set_option doc.verso true

/-! The places in the SQL text where the name trace of a statement gives the editor a decision
(the editor task, part 2b). The trace comes from the resolver run that decides the statement
({name}`Belay.Sqlite.Model.resolveStatementTraced`), so the editor never rebuilds a scope and never
searches for the text of a name. This module only turns the occurrences of a trace into byte ranges
of the SQL text:

- an occurrence in the body of a stored view is not at a path of the text, so it gives no place;
- two records that describe one decision (a {lit}`WITH` definition that the resolver copies for each
  use) give one place, and records that disagree about one decision give none, because the editor
  never guesses between them;
- the bytes at the path of a named occurrence must write that name, so a path that selects another
  node gives no place. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model Translation

/-- A place of the SQL text and the decisions of the resolver about it. A place of a name has one
decision. The place of a comparison has one decision for each operand pair that the expression
compares, for example two for {lit}`x BETWEEN low AND high`. -/
structure NameSite where
  /-- The first byte of the range in the SQL text. -/
  start : Nat
  /-- The byte after the range. -/
  stop : Nat
  /-- The decisions at the path, in the order of the trace. -/
  occurrences : List NameOccurrence

/-- What identifies one decision of the resolver: where it was made, what the occurrence is, and for
a comparison which operand pair. Two records with one key describe the same decision. -/
def decisionOf (occurrence : NameOccurrence) : List Nat × NameRole × Option ComparisonForm :=
  (occurrence.path, occurrence.role, match occurrence.result with
    | .compared form _ _ => some form
    | .found _ | .ambiguous _ | .missing .. | .source _ | .schema _ | .resultColumn _ | .declares
    | .unreached _ => none)

/-- The records of exact paths that agree about their decision: a record that appears more than once
counts once, and the records of a decision that has two different results are left out. -/
def agreedOccurrences (trace : NameTrace) : List NameOccurrence :=
  let distinct := (trace.filter (·.exact)).eraseDups
  distinct.filter fun occurrence => (distinct.filter (decisionOf · == decisionOf occurrence)).length == 1

/-- Whether the bytes of the range write the name of the occurrence. An occurrence without a name,
such as a comparison, accepts any range. -/
def writesName (bytes : ByteArray) (range : Nat × Nat) (occurrence : NameOccurrence) : Bool :=
  match occurrence.name with
  | some name => leafName? bytes range == some name.folded
  | none => true

/-- The places of a statement from the trace of its resolution ({name}`agreedOccurrences`). The path
of each place selects its range in the statement's span ({name}`Span.select`). A range that is empty,
that ends after the text, or that does not write the name of a decision gives no place. For example,
the trace of {lit}`SELECT nmae FROM t` against {lit}`t(name)` has the place of bytes 7 to 11, with
one decision, a missing column. -/
def nameSites (bytes : ByteArray) (item : Located Syntax.Statement) (trace : NameTrace) : List NameSite :=
  let agreed := agreedOccurrences trace
  (agreed.map (·.path)).eraseDups.filterMap fun path =>
    let here := agreed.filter (·.path == path)
    let (start, stop) := item.span.select path
    if start < stop && stop ≤ bytes.size && here.all (writesName bytes (start, stop)) then
      some { start, stop, occurrences := here }
    else none

end Belay.Sqlite
