import Belay.Sqlite.ByteText

set_option doc.verso true

/-! Checked examples of the byte helpers ({lit}`ByteText.lean`). -/

namespace Belay.Sqlite.ByteTextExamples
open Belay.Sqlite

-- The literal is the UTF-8 bytes of its text, also outside ASCII.
#guard bytes! "auto" == [97, 117, 116, 111]
#guard bytes! "" == [] && bytes! "é" == [0xc3, 0xa9]
-- Folding changes only ASCII capitals; a keyword matches without case.
#guard [65, 90, 91, 97, 0xc3].map lowerAscii == [97, 122, 91, 97, 0xc3]
#guard equalsKeyword (bytes! "NoW") (bytes! "now") && !equalsKeyword (bytes! "nowx") (bytes! "now")
-- A C string ends at the first NUL.
#guard bytesBeforeNul [110, 111, 119, 0, 120] == bytes! "now" && bytesBeforeNul (bytes! "now") == bytes! "now"

end Belay.Sqlite.ByteTextExamples
