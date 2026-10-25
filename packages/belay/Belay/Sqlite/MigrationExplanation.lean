import Belay.Sqlite.MigrationPatternSyntax

set_option doc.verso true

namespace Belay.Sqlite

open Lean

/-- Explain the four fresh migration-pattern primitives after elaboration. The
message states their segments, quantifiers, original-context success domain,
vacuity and observation scope. Other propositions return none; callers must report
that unsupported claim instead of guessing its meaning. -/
def migrationExplanation (claim : Expr) : Option MessageData := do
  let weak ← match claim.getAppFn.constName?, claim.getAppArgs.toList with
    | some ``Migration.QueryPreserves, [_, _, _, _, _]
    | some ``Migration.QueryTranslates, [_, _, _, _, _, _, _] => some true
    | some ``Migration.Commutes, [_, _, _, _, _]
    | some ``Migration.CommutesAs, [_, _, _, _, _, _] => some false
    | _, _ => none
  let domain := m!"For every valid bundled database admitted by the claim's predicate, and every complete fresh environment, compare only when the migration succeeds at that original context on its actual run and every permitted raw or concrete branch. Earlier trace success is not an added premise. If the migration fails there, that instance is vacuous; prove migration success separately. A where SQL guard uses Holds: every permitted query result must contain a row without error. It uses the database's default Script.outputOn observation, not the comparison environment."
  let segments := if weak then
    m!"Compare the original read-only query with the replacement read-only query after the migration."
    else m!"Compare application followed by the migration with the migration followed by replacement. Both orders return the application's value. A migration failure after the moved application remains observable and cannot remove the original context from the domain."
  let observations := if weak then
    m!"Compare returned values and projected output traces, including actual-run agreement and all permitted branch observations. Final connection state, clock and next index are omitted. This weak comparison does not justify an arbitrary later continuation."
    else m!"Compare returned values and projected output traces, including actual-run agreement and all permitted branch observations. Compare the complete final connection, clock and raw next-statement index exactly, including counters and transaction snapshots."
  return m!"{domain}\n{segments}\nHide only successful outputs from the identified migration segment. Retain errors, unmodeled stops and partial traces; projection never changes execution or the returned value.\n{observations}"

end Belay.Sqlite
