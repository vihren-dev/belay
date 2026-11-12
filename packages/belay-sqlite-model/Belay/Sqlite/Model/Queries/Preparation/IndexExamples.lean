import Belay.Sqlite.Model.Queries.Fixtures.Examples
import Belay.Sqlite.Model.Shared.Execution.SqlExecution

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.IndexExamples

open Belay.Sqlite.Model Syntax

/-- A CREATE INDEX of {lit}`d` with the key terms and the filter. -/
def indexD (terms : List OrderTerm) (filter : Option Expr := none) (unique : Bool := false) : Syntax.Statement :=
  .createIndex (name! "i") unique (name! "d") terms filter

/-- A key term of an expression, ascending. -/
def term (expression : Expr) : OrderTerm := { expression, descending := false }

#guard (PrepareError.expression .qualifiedIndexTerm).message == "the \".\" operator prohibited in index expressions"
#guard (PrepareError.expression (.nondeterministicIndex true)).message ==
  "non-deterministic functions prohibited in partial index WHERE clauses"

/-- INSERT of one row into {lit}`d`. -/
def insertD (a : String) (b : Expr) : Syntax.Statement := .insert (name! "d") none [[.numeric a, b]] [] none []

/-- {lit}`b IS NOT NULL`. -/
def bPresent : Expr := .isNull (.identifier (name! "b") .none) true

end Belay.Sqlite.Model.Resolution.IndexExamples
