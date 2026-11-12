import VerifierConformance.Programs.Scripts.RunPass

set_option doc.verso true

namespace Belay.Sqlite.Model.Conformance

/-- The clock of a run that continues, from the clock value of each statement: the values, and 0
beyond them, or {lean}`(none : Option Clock)` without values, so that a statement that reads the
clock ends the run. -/
def runClock (clocks : List Int) : Option Clock :=
  if clocks.isEmpty then none else some fun position => clocks.getD position 0

end Belay.Sqlite.Model.Conformance
