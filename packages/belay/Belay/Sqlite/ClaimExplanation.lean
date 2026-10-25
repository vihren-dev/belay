import Belay.Sqlite.MigrationExplanation
import Belay.Sqlite.FreshNotation

set_option doc.verso true

/-!
Plain-word explanations of fresh-run claims, ordinary Std.Do triples and success claims for the
{lit}`#explain` command. An explanation reads the head of the elaborated claim and the constants
of its postcondition, so it states the entry, the captured start, the error policy and the query
observation without a new semantics. It explains an ordinary triple only for the {lit}`Sql`
monad, because only there the contexts and branches are those of the SQL execution model.
-/

namespace Belay.Sqlite

open Lean

/-- The postcondition constructors that state the total error policy. The explanation names a
policy only when the postcondition itself is an application of one of them. -/
def totalPolicyNames : List Name := [``andOk, ``andOkWith]

/-- The postcondition constructors that state the conditional error policy. The explanation names
a policy only when the postcondition itself is an application of one of them. -/
def conditionalPolicyNames : List Name := [``ifOk, ``ifOkWith]

/-- The constants of the default query assertions, which observe a database as {lit}`Holds`
does. The explanation lists the assertion when any of them occurs in the claim, in any position,
also under a negation: the observation context does not depend on the position. -/
def defaultObservationNames : List Name := [``Holds, ``holds, ``Holds.reached]

/-- The constants of the real-context query assertions. The explanation lists the assertion
when any of them occurs in the claim, in any position. -/
def contextObservationNames : List Name := [``holdsInContext, ``Holds.inContext]

/-- The error policy that a postcondition states. A postcondition that is an application of
{name}`andOk`, {name}`andOkWith`, {name}`ifOk` or {name}`ifOkWith` has that policy. Any other
postcondition, including a missing one, has no policy of its own: the text says so, and does not
guess from the constants inside it. For an ordinary triple the trace can hold outputs from
before the program, which the text states. -/
def policyExplanation (post : Option Expr) (ordinary : Bool) : MessageData :=
  let head := post.bind fun expression => expression.consumeMData.getAppFn.constName?
  let prefixText := fun (effect : String) => if ordinary then
    m!" An output that is not OK before the program, in the trace of the starting context, {effect}." else m!""
  match head with
  | some name =>
    if totalPolicyNames.contains name then
      m!"Error policy andOk: the whole trace must have no modeled SQL error, and the final property must hold.{prefixText "makes the claim false"}"
    else if conditionalPolicyNames.contains name then
      m!"Error policy ifOk: the final property is required only when the whole trace has no modeled SQL error. A modeled error removes the obligation. An unmodeled stop in the run of the program is never excused.{prefixText "removes the obligation"}"
    else
      m!"Error policy: not stated by ifOk or andOk. The postcondition determines how a modeled SQL error affects the claim. Every branch must still stay modeled."
  | none =>
    m!"Error policy: not stated by ifOk or andOk. The postcondition determines how a modeled SQL error affects the claim. Every branch must still stay modeled."

/-- The query observations that a claim mentions, found from the constants it uses
({name}`defaultObservationNames`, {name}`contextObservationNames`). The default assertions read
the database of a context as {name}`Holds` reads a database. The in-context assertion reads the
real context. A claim with neither mentions no query assertion. -/
def observationExplanation (claim : Expr) : MessageData :=
  let names := claim.getUsedConstants
  let uses := fun (candidates : List Name) => candidates.any names.contains
  let defaultText : List MessageData := if uses defaultObservationNames then
    [m!"Default query assertions (Holds, holds) read the database with the default observation: no clock, unknown counters, foreign keys off and no open transaction. Every permitted result must have a row. An empty, failed or unmodeled query does not hold. They assert nothing about the actual clock, counters or settings."] else []
  let contextText : List MessageData := if uses contextObservationNames then
    [m!"holdsInContext reads the actual clock at the next statement index and the actual counters, settings and open transaction of the context where it is evaluated. It runs no program step."] else []
  match defaultText ++ contextText with
  | [] => m!"The claim states no query assertion."
  | texts => MessageData.joinSep texts "\n"

/-- Whether the arguments of a Std.Do triple are those of a {name}`Sql` program with the
standard execution transformer {name}`sqlWPMonad`. Only then the contexts and branches of the
explanation are those of the SQL execution model; a triple over another monad or with another
instance is not explained. -/
def standardTransformer (arguments : Array Expr) : Bool :=
  arguments[0]?.bind (·.constName?) == some ``Sql &&
    (arguments[2]?.map (·.getUsedConstants.contains ``sqlWPMonad)).getD false

/-- Explain a fresh-run claim, an ordinary Std.Do triple about a {name}`Sql` program or a success
claim after elaboration. The message states the entry assumptions, the scope of the captured
start, the error policy and the observation context. It returns none for any other proposition,
including a triple about another monad or with another transformer, so the caller reports it as unsupported instead of
inventing a meaning. -/
def freshExplanation (claim : Expr) : Option MessageData :=
  let branches := m!"Every permitted branch must return a value and stay modeled: the actual output and, for a oneOf output, each concrete choice of its rows."
  let arguments := claim.getAppArgs
  match claim.getAppFn.constName? with
  | some ``FreshTriple => some
    m!"Fresh-run claim. It covers every valid bundled database that satisfies the precondition and every complete environment (a clock and all three counters known). Each run starts at statement index 0 with an empty trace, on the idle connection that is built from that database and the environment's counters, with foreign keys off. The initial database is captured once and stays fixed for the whole claim, also after a bind. A database that fails the precondition adds no obligation.\n{branches} The postcondition holds at the final context of each branch.\n{policyExplanation none false}\n{observationExplanation claim}"
  | some ``FreshEnsures => some
    m!"Fresh-run claim. It covers every valid bundled database that satisfies the precondition and every complete environment (a clock and all three counters known). Each run starts at statement index 0 with an empty trace, on the idle connection that is built from that database and the environment's counters, with foreign keys off. The initial database is captured once and stays fixed for the whole claim, also after a bind. A database that fails the precondition adds no obligation.\n{branches} The postcondition holds at the final context of each branch.\n{policyExplanation arguments.back? false}\n{observationExplanation claim}"
  | some ``Std.Do.Triple =>
    if standardTransformer arguments then some
      m!"Ordinary triple. It covers every execution context that satisfies the precondition, whatever its clock, next statement index, counters, settings, open transaction and earlier trace. It is not a fresh-run claim: a precondition such as holds does not fix the starting context.\n{branches} The postcondition holds at the final context of each branch.\n{policyExplanation arguments.back? true}\n{observationExplanation claim}"
    else none
  | some ``Succeeds => some
    m!"Success claim. It covers every valid bundled database that satisfies the predicate and every complete environment. At index 0 with an empty trace, the program must run without a modeled SQL error and without an unmodeled stop on the actual output and, for a oneOf output, on each concrete choice of its rows. It equals the fresh-run claim with andOk ⌜True⌝. A database that fails the predicate adds no obligation.\n{observationExplanation claim}"
  | _ => none

/-- Explain a migration pattern or a fresh-run, ordinary-triple or success claim. -/
def claimExplanation (claim : Expr) : Option MessageData :=
  migrationExplanation claim <|> freshExplanation claim

end Belay.Sqlite
