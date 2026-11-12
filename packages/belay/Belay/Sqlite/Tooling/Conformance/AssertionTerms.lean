import Belay.Sqlite.Programs.Reasoning.FreshRules

set_option doc.verso true

/-!
Assertions on execution contexts for Std.Do triples about {lit}`Sql` programs. {lit}`holds` is the
default query assertion and {lit}`holdsInContext` the real-context one. {lit}`ifOk` and
{lit}`andOk` are the conditional and the total error policies as postconditions, and
{lit}`FreshEnsures` is the fresh-run claim of such a postcondition. Each equals the corresponding
{lit}`Sql.ifOk`, {lit}`Sql.andOk` or {lit}`FreshTriple` statement, so the notation adds no new
semantics.
-/

namespace Belay.Sqlite
open Std.Do

/-- A plain assertion {lit}`⌜claim⌝` is decidable when its proposition is: the assertion holds exactly when
the proposition holds. -/
instance assertionPureDecidable (claim : Prop) [Decidable claim] :
    Decidable (ULift.down (SPred.pure claim : SPred PostShape.pure.args)) :=
  inferInstanceAs (Decidable claim)

end Belay.Sqlite
