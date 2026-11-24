import Belay

set_option doc.verso true

/-! Temporary retention evidence for ADR 0033 in {lit}`tests/surface_schema_script_test.py`.
The pragma contract follows from {name}`Belay.Sqlite.Model.resolveStatementPragma_readOnly` and {name}`Belay.Sqlite.Model.runScriptStep_readOnly_keeps`. -/

namespace Belay.Sqlite.ReplacedFrames
open Belay.Sqlite.Model

/-- For every connection and statement of a pragma that only reads, such as {lit}`PRAGMA foreign_key_check`,
and every step that continues: the step has no further execution and the next connection is the
connection. In plain words, a pragma without a value changes nothing, not even the counters, also
when it fails as a prepare error. Proof sketch: {name}`resolveStatementPragma_readOnly` shows that the
resolved statement is a query or a prepare error, and {name}`runScriptStep_readOnly_keeps` applies. -/
theorem runScriptStep_pragma_keeps {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {pragma : Syntax.Pragma} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {resolved : Resolved.Statement} {after : ResolveState} (reads : pragma.readsOnly = true)
    (found : resolveStatement context connection.resolveState (.pragma pragma) = .ok (resolved, after))
    (step : runScriptStep context clock index connection (.pragma pragma) parameters = .continued output next others) :
    others = [] ∧ next = connection :=
  runScriptStep_readOnly_keeps found
    (resolveStatementPragma_readOnly reads (by simpa only [statement_arms] using found)) step

#print axioms runScriptStep_pragma_keeps

end Belay.Sqlite.ReplacedFrames
