import Belay
import Belay.Sqlite.CheckOperation

open Belay.Sqlite Lean Elab Meta

/-! The complete operation shares inferred samples, kernel certificates and original SQL
replays. Intended data premises prevent a missing table from replacing a boundary example. -/

namespace SearchFixture

/-- A false universal query claim admits the empty database as its intended witness. -/
def missing : Prop := ∀ db : Database, Holds (sql "SELECT 1 FROM absent") db
/-- Every database has a row for SELECT 1, so universal emptiness is false. -/
def nonempty : Prop := ∀ db : Database, Empty (sql "SELECT 1") db
/-- SELECT 1 does not fail, contradicting the universal failure claim. -/
def failure : Prop := ∀ db : Database, Fails (sql "SELECT 1") db
/-- A complete environment cannot repair the missing INSERT target. -/
def success : Prop := Succeeds (sql "INSERT INTO absent VALUES (1)") (fun _ => True)
/-- Any supplied parameter still leaves one SELECT row, contradicting emptiness. -/
def parameter : Prop := ∀ amount : Value, ∀ db : Database, Empty ((sql "SELECT :amount") amount) db
/-- The inferred default table refutes this ordinary Lean claim about every database. -/
def plain : Prop := ∀ db : Database, db.rows "t" = none

/-- An explicit NOCASE group exposes duplicate ASCII keys. -/
def nocaseQuery : Script := sql "SELECT 1 FROM people GROUP BY address COLLATE NOCASE HAVING COUNT(*) > 1"
/-- The exact inferred schema fixes the intended table and column. -/
def nocaseSchema : Database := (Sampling.scriptHints nocaseQuery).schema.getD Database.empty
/-- Under this exact schema and a/A rows, the query is not empty. -/
def nocase : Prop := ∀ db : Database,
  db.raw.catalog = nocaseSchema.raw.catalog →
  db.rows "people" = some [[Value.text [97]], [Value.text [65]]] → Empty nocaseQuery db

/-- The same NOCASE grouping must distinguish non-ASCII case variants. -/
def caseQuery : Script := sql "SELECT 1 FROM people GROUP BY address COLLATE NOCASE HAVING COUNT(*) > 1"
/-- Under this schema and æ/Æ rows, no duplicate group exists. -/
def nonascii : Prop := ∀ db : Database,
  db.raw.catalog = nocaseSchema.raw.catalog →
  db.rows "people" = some [[Value.text "æ".toUTF8.toList], [Value.text "Æ".toUTF8.toList]] →
  Holds caseQuery db

/-- The ordinary SUM query must report its modeled overflow. -/
def sumQuery : Script := sql "SELECT SUM(amount) FROM ledger"
/-- The exact inferred ledger schema fixes the intended aggregate input. -/
def sumSchema : Database := (Sampling.scriptHints sumQuery).schema.getD Database.empty
/-- Under this schema and two 2^62 integers, SUM fails rather than returning a row. -/
def overflow : Prop := ∀ db : Database,
  db.raw.catalog = sumSchema.raw.catalog →
  db.rows "ledger" = some [[Value.integer 4611686018427387904], [Value.integer 4611686018427387904]] →
  Holds sumQuery db

/-- A model restriction must refuse replay instead of alleging a native SQL failure. -/
def unavailable : Prop := ∀ db : Database, Holds (sql "SELECT random()") db

/-- A raw run expression outside recognized query sites is still SQL, not a plain predicate. -/
def hiddenExecution : Prop := ∀ db : Database, (db.run (sql "SELECT 1")).outputs = []

/-- Removing construction metadata leaves this index outside the simple replay formatter. -/
def indexed : Database := db! "CREATE TABLE t(a); CREATE INDEX i ON t(a);"

/-- An unreplayable refutation must not hide a later replayable refutation. -/
def skipsUnreplayable : Term.TermElabM Unit := do
  let first : Check.Witness := { database := databaseExpr (← Replay.databaseValue (mkConst ``indexed)).raw }
  let second : Check.Witness := { database := mkConst ``Database.empty }
  discard <| Check.refuteWitness (mkConst ``nonempty) first
  unless (← Check.attempt (Check.replayClaim (mkConst ``nonempty) first)).isNone do
    throwError "the first candidate unexpectedly has a replay"
  let outcome ← Check.check (mkConst ``nonempty) 2000000
    { witnesses := #[first, second], candidates := 2 } (shrinkAttempts := 0)
    (prove := fun _ => pure none)
  let .refuted witness _ := outcome.result
    | throwError "the checker stopped before the later replayable candidate"
  unless witness.database == second.database && !outcome.replays.isEmpty do
    throwError "the report did not retain the later replayable candidate"

/-- Export only ordinary row/error observations used by these fixtures, together with the
exact shared replay text. The Python test runs that text under pinned native SQLite. -/
def emitReplay (name : Name) (report : Replay.Report) : Term.TermElabM Unit := do
  let outputs ← report.outputs.mapM fun output => match output with
    | .rows rows => pure (Json.mkObj [("rows", toJson rows)])
    | .error code => pure (Json.mkObj [("error", toJson code)])
    | .done _ | .oneOf _ | .unmodeled _ =>
      throwError "unexpected observation shape in the search replay fixture"
  logInfo m!"SEARCH-REPLAY:{(Json.mkObj [("name", toJson name.toString),
    ("sql", toJson report.sqlite), ("outputs", toJson outputs)]).compress}"

/-- Disable proof automation to measure the candidate and replay path independently. -/
def noProof (_ : Expr) : Term.TermElabM (Option Check.Proven) := pure none

/-- Recheck the original negation; SQL reports must retain a replay of original source. -/
def refutes (name : Name) (hasSql : Bool := true) : Term.TermElabM Unit := do
  let before ← IO.getNumHeartbeats
  let started ← IO.monoMsNow
  let outcome ← Check.check (mkConst name) 2000000 (shrinkAttempts := 2) (prove := noProof)
  let .refuted _ proof := outcome.result | throwError "no checked counterexample for {name}"
  discard <| Check.certify (mkNot (mkConst name)) proof
  unless !outcome.replays.isEmpty && outcome.replays.all (fun report => report.original.isSome == hasSql) do
    throwError "the original query/plain-predicate replay boundary was lost for {name}"
  outcome.replays.forM (emitReplay name)
  logInfo m!"SEARCH {name}: certified; heartbeats={(← IO.getNumHeartbeats) - before}; elapsedMs={(← IO.monoMsNow) - started}"

elab "check_search" : command => Command.liftTermElabM do
  skipsUnreplayable
  let .proved _ := (← Check.check (mkConst ``True) 200000).result
    | throwError "a checked true claim was not proved"
  for name in [``missing, ``nonempty, ``failure, ``success, ``parameter, ``nocase, ``nonascii, ``overflow] do
    refutes name
  refutes ``plain false
  let unavailableWitness : Check.Witness := { database := mkConst ``Database.empty }
  let .unknown := (← Check.check (mkConst ``unavailable) 2000000
    { witnesses := #[unavailableWitness], candidates := 1 } (prove := noProof)).result
    | throwError "an unmodeled observation became a native SQL counterexample"
  let hidden : Check.Witness := { database := mkConst ``Database.empty }
  discard <| Check.refuteWitness (mkConst ``hiddenExecution) hidden
  let .unknown := (← Check.check (mkConst ``hiddenExecution) 2000000
    { witnesses := #[hidden], candidates := 1 } (prove := noProof)).result
    | throwError "unsupported SQL execution was mislabeled as a plain Lean predicate"
  let .unknown := (← Check.check (mkConst ``missing) 0).result
    | throwError "a disabled check produced a result"
  logInfo "shared SQL search and replay passed"

set_option maxHeartbeats 10000000 in
check_search

end SearchFixture
