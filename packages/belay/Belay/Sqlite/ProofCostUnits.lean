import Belay.Sqlite.ProofCostRecord

set_option doc.verso true

/-! Units of the proof-cost report (ADR 0017, S7). A stored count is an exact number of internal
heartbeats. The user reads and sets bounds in Lean budget units, as with {lit}`maxHeartbeats`:
one unit is {lean}`Belay.Sqlite.heartbeatsPerBudgetUnit` internal heartbeats, so a decimal with
three places is exact and no step needs rounding. -/

namespace Belay.Sqlite

/-- A count of internal heartbeats as budget units with three decimal places. -/
def showUnits (heartbeats : Nat) : String :=
  let fraction := toString (heartbeats % heartbeatsPerBudgetUnit)
  s!"{heartbeats / heartbeatsPerBudgetUnit}.{"".pushn '0' (3 - fraction.length)}{fraction}"

/-- The value of a decimal in budget units as internal heartbeats, or a message that says what to
change. The text must be digits with at most three decimal places, so that the result is exact:
{lit}`0`, {lit}`2.5` and {lit}`0.001` are valid; {lit}`0.0001` and {lit}`-1` are not. -/
def parseUnits (text : String) : Except String Nat :=
  let invalid := Except.error s!"the allowance {repr text} is not valid; write budget units as a decimal \
    number with at most three decimal places, for example 0, 2.5 or 0.001"
  match text.splitOn "." with
  | [whole] => if allDigits whole then .ok (whole.toNat! * heartbeatsPerBudgetUnit) else invalid
  | [whole, fraction] =>
    if allDigits whole && allDigits fraction && fraction.length ≤ 3 then
      .ok (whole.toNat! * heartbeatsPerBudgetUnit + (fraction ++ "".pushn '0' (3 - fraction.length)).toNat!)
    else invalid
  | _ => invalid
where
  allDigits (digits : String) : Bool := !digits.isEmpty && digits.all Char.isDigit

end Belay.Sqlite

/-! Examples, checked when this module compiles:

```lean
open Belay.Sqlite
#guard showUnits 31765 == "31.765"
#guard showUnits 2500 == "2.500"
#guard showUnits 7 == "0.007"
#guard (parseUnits "2.5").toOption == some 2500
#guard (parseUnits "0").toOption == some 0
#guard (parseUnits "0.001").toOption == some 1
#guard (parseUnits "0.0001").toOption == none
#guard (parseUnits "-1").toOption == none
#guard (parseUnits "").toOption == none
#guard (parseUnits "1.").toOption == none
```
-/
