import Belay.Sqlite.Model.Arithmetic

set_option doc.verso true

/-! SQLite's {lit}`SUM` and {lit}`AVG` (ADR 0012, slice 2), ported from {lit}`sumStep`,
{lit}`sumFinalize` and {lit}`avgFinalize` of the pinned 3.51.0 source. The sum stays an
exact integer while every input is an integer and the sum fits in 64 bits. After a
REAL input or an integer overflow, it continues as a Kahan-Babuska-Neumaier sum of
doubles. An integer overflow that no later REAL input follows makes {lit}`SUM` fail with
{lit}`integer overflow`; {lit}`AVG` never fails. -/

namespace Belay.Sqlite.Model

/-- An input of {lit}`SUM` after {lit}`sqlite3_value_numeric_type`: an integer, or a
double that the approximate sum adds. -/
inductive SumInput where
  /-- An INTEGER, or TEXT that reads as one. -/
  | integer (value : Int)
  /-- A REAL, TEXT that reads as a REAL or not as a number, or a BLOB, with its double. -/
  | double (value : Float)

/-- The input that a non-NULL value gives to {lit}`SUM`. TEXT gets numeric affinity
({lit}`applyNumericAffinity`): text whose {name}`atof` code is 1 and that equals an
integer, or that {name}`atoi64` reads whole, is that integer; other numeric text is its
double; text that is not a number keeps its {name}`atof` double. A BLOB adds its
{name}`atof` double. -/
def Value.sumInput? : Value → Option SumInput
  | .null => none
  | .integer value => some (.integer value)
  | .real bits => some (.double (Float.ofBits bits))
  | .blob bytes => some (.double (atof bytes).1)
  | .text bytes =>
    let (double, code) := atof bytes
    let whole := realToI64 double
    if code == 1 && realSameAsInt double whole then some (.integer whole)
    else if code == 1 && (atoi64 bytes).2 == 0 then some (.integer (atoi64 bytes).1)
    else some (.double double)

/-- The state of {lit}`SUM` and {lit}`AVG`: the number of inputs, the exact integer sum,
whether the sum is approximate, whether an integer overflow is pending, and the
approximate sum with its error term. -/
structure SumState where
  /-- The number of non-NULL inputs. -/
  count : Nat := 0
  /-- The exact sum of the integer inputs while the sum is exact. -/
  integerSum : Int := 0
  /-- Whether the sum continues in doubles. -/
  approximate : Bool := false
  /-- Whether an integer overflow happened and no REAL input followed it. -/
  overflow : Bool := false
  /-- The approximate sum. -/
  sum : Float := 0
  /-- The error term of the approximate sum. -/
  error : Float := 0

/-- The magnitude from which an integer enters the approximate sum in two parts:
{lit}`2^52`. -/
def kbnSplitBound : Int := 2 ^ 52

/-- The part of an integer below {lit}`16384` in magnitude, with the sign of the integer,
that {lit}`SUM` adds separately from the rest. -/
def kbnSmallPart (value : Int) : Int := value.tmod 16384

/-- One Kahan-Babuska-Neumaier step ({lit}`kahanBabuskaNeumaierStep`). -/
def SumState.addDouble (state : SumState) (value : Float) : SumState :=
  let total := state.sum + value
  let error := if state.sum.abs > value.abs then state.error + ((state.sum - total) + value)
    else state.error + ((value - total) + state.sum)
  { state with sum := total, error }

/-- Add an integer to the approximate sum ({lit}`kahanBabuskaNeumaierStepInt64`): an
integer at least {name}`kbnSplitBound` in magnitude enters in two parts. -/
def SumState.addInteger (state : SumState) (value : Int) : SumState :=
  if value ≤ -kbnSplitBound || value ≥ kbnSplitBound then
    let small := kbnSmallPart value
    (state.addDouble (Float.ofInt (value - small))).addDouble (Float.ofInt small)
  else state.addDouble (Float.ofInt value)

/-- Start the approximate sum from the exact integer sum
({lit}`kahanBabuskaNeumaierInit`). -/
def SumState.startApproximate (state : SumState) : SumState :=
  let value := state.integerSum
  if value ≤ -kbnSplitBound || value ≥ kbnSplitBound then
    let small := kbnSmallPart value
    { state with approximate := true, sum := Float.ofInt (value - small), error := Float.ofInt small }
  else { state with approximate := true, sum := Float.ofInt value, error := 0 }

/-- One input of {lit}`SUM` or {lit}`AVG` ({lit}`sumStep`). -/
def SumState.add (state : SumState) (value : Value) : SumState :=
  match value.sumInput? with
  | none => state
  | some input =>
    let state := { state with count := state.count + 1 }
    match input, state.approximate with
    | .integer value, false =>
      if fitsInt64Range (state.integerSum + value) then { state with integerSum := state.integerSum + value }
      else ({ state.startApproximate with overflow := true }).addInteger value
    | .integer value, true => state.addInteger value
    | .double value, false => state.startApproximate.addDouble value
    | .double value, true => { state with overflow := false }.addDouble value

/-- Whether a double is an infinity or a NaN ({lit}`sqlite3IsOverflow`). -/
def doubleOverflows (value : Float) : Bool := value.isInf || value.isNaN

/-- The approximate total with its error term, unless the error term overflows. -/
def SumState.approximateTotal (state : SumState) : Float :=
  if doubleOverflows state.error then state.sum else state.sum + state.error

/-- The value of {lit}`SUM` ({lit}`sumFinalize`): NULL without inputs, the exact integer
sum, or the approximate total. {lean}`(none : Option Value)` stands for the
{lit}`integer overflow` error. -/
def SumState.sumValue (state : SumState) : Option Value :=
  if state.count == 0 then some .null
  else if !state.approximate then some (.integer state.integerSum)
  else if state.overflow then none
  else some (realValue state.approximateTotal)

/-- The value of {lit}`AVG` ({lit}`avgFinalize`): NULL without inputs, else the total as a
double divided by the number of inputs. -/
def SumState.averageValue (state : SumState) : Value :=
  if state.count == 0 then .null
  else
    let total := if state.approximate then state.approximateTotal else Float.ofInt state.integerSum
    realValue (total / Float.ofNat state.count)

/-- The value of {lit}`TOTAL` ({lit}`totalFinalize`): the total as a REAL, {lit}`0.0` without
inputs; it never fails, because an integer overflow only makes the sum approximate. -/
def SumState.totalValue (state : SumState) : Value :=
  realValue (if state.approximate then state.approximateTotal else Float.ofInt state.integerSum)

/-- The state of {lit}`SUM` or {lit}`AVG` after a list of values. -/
def sumOf (values : List Value) : SumState := values.foldl SumState.add {}

end Belay.Sqlite.Model
