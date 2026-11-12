import Belay.Sqlite.Model.Schema.Dispatch.CompoundExamples
import Belay.Sqlite.Model.Programs.Scripts.StatementStep
import Belay.Sqlite.Model.Queries.Evaluation.CompoundFailureExamples

set_option doc.verso true

/-! Checked examples of the failures of a compound {lit}`SELECT` (ADR 0019, D3): where SQLite
runs a term, where it reads {lit}`LIMIT` and {lit}`OFFSET`, and when a failure is certain. The
probes are those of outcome 10 of the task file of slice 3, checked natively. The failing term is
{lit}`SELECT abs(-9223372036854775808)`; a fault {lit}`Fault.must` is the statement's
{lit}`integer overflow` error. -/

namespace Belay.Sqlite.Model.Resolved.CompoundExamples

-- The model describes a compound statement whose term certainly fails
-- ({name}`statementReady`): the compound describes the failures of its terms.
example : statementReady 0 {} [] (.query (compound [.union] [.binary]) [literals [int 1], failingTerm]) (.ofTables []) =
    true := by decide +kernel
-- It does not describe a compound whose term names a subquery with a call that can fail.
example : statementReady 0 {} [] (.query (compound [.union] [.binary])
    [literals [.subquery 2], literals [int 1], literals [failing]]) (.ofTables []) =
    false := by decide +kernel

end Belay.Sqlite.Model.Resolved.CompoundExamples
