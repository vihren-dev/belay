import Belay.Sqlite.Model.Programs.Scripts.StatementStep
import Belay.Sqlite.Model.Values.Json.JsonFaultExamples

set_option doc.verso true

/-! Checked examples of where a JSON failure is part of the outcome (ADR 0012, amendment
5, slice 6b). Each fact was checked on native SQLite 3.51.0, one statement per line; the
conformance cases compare them with it. -/

namespace Belay.Sqlite.Model.Resolved.JsonFaultExamples

-- SQLite certainly reports the failure of a result column without FROM, and the step
-- fails with it.
#guard fromless.mustFail (.plain 0) [[]] && statementReady 0 {} [] (.query fromless []) empty

-- Under LIMIT 0 SQLite evaluates nothing; OFFSET 1 skips the result column; WHERE 0
-- leaves no row. The model does not describe the first two, and the third succeeds.
#guard !{ fromless with limit := some 0 }.mustFail (.plain 0) [[]] && !statementReady 0 {} [] (.query { fromless with limit := some 0 } []) empty
#guard !{ fromless with offset := 1 }.mustFail (.plain 0) [[]] && !statementReady 0 {} [] (.query { fromless with offset := 1 } []) empty

-- SQLite may skip an operand of AND, so a failure under AND is not certain.
#guard !statementReady 0 {} [] (.query { fromless with columns := [.scalar (.and (.literal (.integer 0)) malformed)] } []) empty
-- A constant WHERE term is evaluated once before the rows, also over an empty table;
-- a result column is not.
#guard !statementReady 0 {} [] (.query { fromless with sources := [.first 0], filter := some malformed, columns := [] } []) empty
#guard statementReady 0 {} [] (.query { fromless with sources := [.first 0] } []) empty
-- An aggregate query evaluates its result row over NULL cells when no row passes WHERE.
#guard
  let columns : List Output := [.scalar malformed, .aggregate .countRows]
  !statementReady 0 {} [] (.query { fromless with sources := [.first 0], aggregate := true, columns := columns } []) empty

end Belay.Sqlite.Model.Resolved.JsonFaultExamples
