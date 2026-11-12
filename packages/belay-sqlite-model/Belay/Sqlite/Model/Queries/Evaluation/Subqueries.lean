import Belay.Sqlite.Model.Queries.Evaluation.QueryRun
import Belay.Sqlite.Model.Queries.Evaluation.QueryFunctions

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- Whether SQLite gives the same first values on both sides of a cut before {lit}`position` of
the sorted records, in every order that the {lit}`ORDER BY` terms allow: the cut is at the start
or after the end, or the records around it are not tied, or every record tied with the one
after the cut has the same first value. With {lit}`wholeRows`, compare all result cells instead;
use it for a derived source, whose consumer can read any column. -/
def certainCut (directions : List (Bool × Collation)) (sorted : List Record) (position : Nat)
    (wholeRows : Bool := false) : Bool :=
  match position, sorted[position]? with
  | 0, _ | _, none => true
  | before + 1, some after =>
    match sorted[before]? with
    | none => true
    | some previous =>
      compareSort directions previous.2 after.2 != .eq ||
        (sorted.filter (compareSort directions ·.2 after.2 == .eq)).all
          (fun record => if wholeRows then record.1 == after.1 else record.1.head? == after.1.head?)

/-- Whether the first values of a subquery's window are the same in every order that its
{lit}`ORDER BY` terms allow, for a window of at most {lit}`limit` rows after its
{lit}`OFFSET`: no rows, or both cuts of the window are certain ({name}`certainCut`). Without
{lit}`ORDER BY` every record is tied, as SQLite may read the rows in any order. With
{lit}`wholeRows`, each cut compares complete result rows instead of their first values. -/
def Query.windowCertain (context : EvalContext) (query : Query) (rows : List (List Value)) (limit : Option Nat)
    (wholeRows : Bool := false) :
    Bool :=
  limit == some 0 ||
    let directions := query.orderBy.map fun term => (term.descending, term.collation)
    let sorted := stableSort (fun a b => (compareSort directions a.2 b.2).isLE)
      (query.uniqueRecords context rows)
    certainCut directions sorted query.offset wholeRows &&
      limit.all (fun count => certainCut directions sorted (query.offset + count) wholeRows)

end Belay.Sqlite.Model.Resolved
