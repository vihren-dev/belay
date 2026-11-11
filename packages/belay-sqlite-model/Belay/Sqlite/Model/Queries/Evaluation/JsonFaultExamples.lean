import Belay.Sqlite.Model.Queries.Evaluation.JsonReady
import Belay.Sqlite.Model.Values.Json.JsonFaultExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved.JsonFaultExamples

#guard selected.eval (.plain 0) [] == .integer 1 && malformed.eval (.plain 0) [] == .null

#guard !{ fromless with filter := some (.literal (.integer 0)) }.mayFail (.plain 0) [[]]
-- An aggregate operand fails also under OFFSET.
#guard { fromless with aggregate := true, columns := [.aggregate (.count malformed)], offset := 1 }.mustFail (.plain 0) [[]]

-- A JSON aggregate writes its operand as json_array does: JSONB that the model does not
-- describe (a header longer than needed) is a possible failure, and a failing operand stays
-- certain.
#guard
  let blob : Query := { fromless with aggregate := true, columns := [.aggregate (.jsonGroupArray (.literal (.blob [0xc7, 1, 0x61])))] }
  blob.mayFail (.plain 0) [[]] && !blob.mustFail (.plain 0) [[]] && (blob.run (.plain 0) [[]]).fault == .may
#guard
  let column : Output := .aggregate (.jsonGroupObject (text "a") (.literal (.blob [0xc7, 1, 0x61])))
  let blob : Query := { fromless with aggregate := true, columns := [column] }
  blob.mayFail (.plain 0) [[]] && !blob.mustFail (.plain 0) [[]]
#guard { fromless with aggregate := true, columns := [.aggregate (.jsonGroupArray malformed)] }.mustFail (.plain 0) [[]]
#guard { fromless with aggregate := true, columns := [.aggregate (.jsonGroupObject malformed (text "x"))] }.mustFail (.plain 0) [[]]
#guard !{ fromless with aggregate := true, columns := [.aggregate (.jsonGroupArray selected)] }.mayFail (.plain 0) [[]]

end Belay.Sqlite.Model.Resolved.JsonFaultExamples
