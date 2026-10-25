import Belay.Sqlite.MigrationExplanation
import Belay.Sqlite.FreshNotation

set_option doc.verso true

/-!
Plain-word explanations of fresh-run claims, ordinary Std.Do triples and success claims for the
{lit}`#explain` command. An explanation reads the head of the elaborated claim and the constants
of its postcondition, so it states the entry, the captured start, the error policy and the query
observation without a new semantics.
-/

namespace Belay.Sqlite

open Lean

/-- The error policy that a postcondition states, found from the constants it mentions:
{name}`ifOk` and {name}`andOk` (also their value-aware forms and the {name}`Sql` forms). For an
ordinary triple the trace can hold outputs from before the program, which the text states. A
postcondition without these constants has no error policy of its own. -/
def policyExplanation (claim : Expr) (ordinary : Bool) : MessageData :=
  let names := claim.getUsedConstants
  let uses := fun (candidates : List Name) => candidates.any names.contains
  let prefixText := fun (effect : String) => if ordinary then
    m!" An output that is not OK before the program, in the trace of the starting context, {effect}." else m!""
  if uses [``andOk, ``andOkWith, ``Sql.andOk] then
    m!"Error policy andOk: the whole trace must have no modeled SQL error, and the final property must hold.{prefixText "makes the claim false"}"
  else if uses [``ifOk, ``ifOkWith, ``Sql.ifOk] then
    m!"Error policy ifOk: the final property is required only when the whole trace has no modeled SQL error. A modeled error removes the obligation. An unmodeled stop in the run of the program is never excused.{prefixText "removes the obligation"}"
  else
    m!"Error policy: neither ifOk nor andOk. A modeled SQL error does not fail the claim unless the postcondition inspects the trace. Every branch must still stay modeled."

/-- The query observations that a claim mentions, found from the constants it uses. The default
assertions read the database of a context as {name}`Holds` reads a database. The in-context
assertion reads the real context. A claim with neither mentions no query. -/
def observationExplanation (claim : Expr) : MessageData :=
  let names := claim.getUsedConstants
  let uses := fun (candidates : List Name) => candidates.any names.contains
  let defaultText : List MessageData := if uses [``Holds, ``holds, ``Holds.reached] then
    [m!"Default query assertions (Holds, holds) read the database with the default observation: no clock, unknown counters, foreign keys off and no open transaction. Every permitted result must have a row. An empty, failed or unmodeled query does not hold. They assert nothing about the actual clock, counters or settings."] else []
  let contextText : List MessageData := if uses [``holdsInContext, ``Holds.inContext] then
    [m!"holdsInContext reads the actual clock at the next statement index and the actual counters, settings and open transaction of the context where it is evaluated. It runs no program step."] else []
  match defaultText ++ contextText with
  | [] => m!"The claim states no query assertion."
  | texts => MessageData.joinSep texts "\n"

/-- Explain a fresh-run claim, an ordinary Std.Do triple or a success claim after elaboration.
The message states the entry assumptions, the scope of the captured start, the error policy and
the observation context. It returns none for any other proposition, so the caller reports it as
unsupported instead of inventing a meaning. -/
def freshExplanation (claim : Expr) : Option MessageData :=
  let branches := m!"Every permitted branch must return a value and stay modeled: the actual output and, for a oneOf output, each concrete choice of its rows."
  match claim.getAppFn.constName? with
  | some ``FreshTriple | some ``FreshEnsures => some
    m!"Fresh-run claim. It covers every valid bundled database that satisfies the precondition and every complete environment (a clock and all three counters known). Each run starts at statement index 0 with an empty trace, on the idle connection that is built from that database and the environment's counters, with foreign keys off. The initial database is captured once and stays fixed for the whole claim, also after a bind. A database that fails the precondition adds no obligation.\n{branches} The postcondition holds at the final context of each branch.\n{policyExplanation claim false}\n{observationExplanation claim}"
  | some ``Std.Do.Triple => some
    m!"Ordinary triple. It covers every execution context that satisfies the precondition, whatever its clock, next statement index, counters, settings, open transaction and earlier trace. It is not a fresh-run claim: a precondition such as holds does not fix the starting context.\n{branches} The postcondition holds at the final context of each branch.\n{policyExplanation claim true}\n{observationExplanation claim}"
  | some ``Succeeds => some
    m!"Success claim. It covers every valid bundled database that satisfies the predicate and every complete environment. At index 0 with an empty trace, the program must run without a modeled SQL error and without an unmodeled stop on the actual output and, for a oneOf output, on each concrete choice of its rows. It equals the fresh-run claim with andOk ⌜True⌝. A database that fails the predicate adds no obligation.\n{observationExplanation claim}"
  | _ => none

/-- Explain a migration pattern or a fresh-run, ordinary-triple or success claim. -/
def claimExplanation (claim : Expr) : Option MessageData :=
  migrationExplanation claim <|> freshExplanation claim

end Belay.Sqlite
