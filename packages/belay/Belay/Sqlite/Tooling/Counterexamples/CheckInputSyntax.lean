import Lean.Elab.Term

set_option doc.verso true

/-! Shared input spelling keeps explicit witness selection independent of searched checking.
The two-word form distinguishes a quantified input named env from the execution environment. -/

namespace Belay.Sqlite.Check
open Lean

/-- One explicit search input. A schema guides generation; repeated databases give an ordered
candidate sequence. Named inputs match quantified binders, including binders named env or schema. -/
declare_syntax_cat sqlCheckInput
syntax "(" ident ":=" term ")" : sqlCheckInput
syntax "(" ident ident ":=" term ")" : sqlCheckInput

end Belay.Sqlite.Check
