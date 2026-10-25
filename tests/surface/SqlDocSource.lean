import Lean.Elab.Command
import Belay.Sqlite.SqlDocSource

set_option doc.verso true

namespace SqlDocSource
open Belay.Sqlite.SqlDoc

/-- The file range of a text range, for a block that starts at the given file offset. -/
def locate (blockStart : Nat) (original text : String) (start stop : Nat) : Option (Nat × Nat) :=
  (SourceMap.ofSource? blockStart original text).map (·.fileRange start stop)

-- A block without indentation maps by offset.
#guard locate 100 "SELECT 1;\nSELECT 2;\n" "SELECT 1;\nSELECT 2;\n" 7 9 == some (107, 109)
#guard locate 100 "SELECT 1;\nSELECT 2;\n" "SELECT 1;\nSELECT 2;\n" 17 19 == some (117, 119)

-- A fence indented by four spaces: each line adds four bytes.
#guard locate 100 "    SELECT 1;\n    SELECT 2;\n" "SELECT 1;\nSELECT 2;\n" 7 9 == some (111, 113)
#guard locate 100 "    SELECT 1;\n    SELECT 2;\n" "SELECT 1;\nSELECT 2;\n" 17 19 == some (125, 127)

-- A range that ends at the start of a line stays on the previous line.
#guard locate 100 "  a;\n  b;\n" "a;\nb;\n" 0 3 == some (102, 105)
#guard locate 100 "  a;\n  b;\n" "a;\nb;\n" 3 5 == some (107, 109)

-- Blank lines may have fewer spaces than the fence; extra spaces stay in the text.
#guard locate 100 "    a;\n  \n      b;\n" "a;\n\n  b;\n" 4 5 == some (114, 115)
#guard locate 100 "    a;\n  \n      b;\n" "a;\n\n  b;\n" 7 8 == some (117, 118)

-- Bytes, not characters, count: an accent and an emoji take two and four bytes.
#guard locate 100 "  SELECT 'é😀', x;\n" "SELECT 'é😀', x;\n" 17 18 == some (119, 120)
#guard locate 100 "  SELECT 'é😀', x;\n" "SELECT 'é😀', x;\n" 7 8 == some (109, 110)

-- An empty range covers one byte.
#guard locate 100 "  a;\n" "a;\n" 1 1 == some (103, 104)

-- Text that is not the original with indentation removed gives no map.
#guard locate 100 "  a;\n" "b;\n" 0 1 == none
#guard locate 100 "  a;\n  b;\n" "a;\n" 0 1 == none
#guard locate 100 "x a;\n" "a;\n" 0 1 == none

end SqlDocSource

open Lean Elab Command in
run_cmd logInfo "SQL doc source checks passed"
