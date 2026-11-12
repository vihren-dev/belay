import Belay.Sqlite.Model.Queries.Evaluation.Subqueries

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- Unwindowed certainty rule: for every context, query without {lit}`OFFSET`, rows and choice of
complete rows, the window without {lit}`LIMIT` is certain ({name}`Query.windowCertain`): a window
that keeps every record has no cut. So a derived query without {lit}`LIMIT` and {lit}`OFFSET`
has certain complete rows in every order. -/
theorem Query.windowCertain_unwindowed (context : EvalContext) {query : Query} (noOffset : query.offset = 0)
    (rows : List (List Value)) (wholeRows : Bool) : query.windowCertain context rows none wholeRows = true := by
  simp [Query.windowCertain, noOffset, certainCut]

end Belay.Sqlite.Model.Resolved
