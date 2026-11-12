import Belay

open Belay.Sqlite Lean Meta

/-! SQL inference must use actual table/column names and bound values. Its finite guesses
still pass the ordinary validity and exact-proposition certificate boundary. -/

/-- An explicit collation makes the intended data failure independent of hidden schema. -/
def query : Script := sql "SELECT address FROM people WHERE address COLLATE NOCASE = 'A'"

/-- The schema inferred from the query's physical source and column read. -/
def inferred : Database := (Sampling.scriptHints query).schema.getD Database.empty

#guard inferred.raw.catalog.findTable (Belay.Sqlite.Model.Identifier.ofString "people") |>.isSome
#guard inferred.rows "people" == some []
#guard (inferred.raw.catalog.columnsOf (Belay.Sqlite.Model.Identifier.ofString "people")).map
  (·.map (·.name.text)) == some ["address"]

/-- False claim about the exact intended rows; missing schema cannot supply a substitute. -/
def claim : Prop := ∀ database : Database,
  database.raw.catalog = inferred.raw.catalog →
  database.rows "people" = some [[Value.text [97]], [Value.text [65]]] → Empty query database

set_option maxHeartbeats 1000000 in
run_meta do
  let some witness := (Sampling.scriptCandidates query).find? fun database =>
      database.rows "people" == some [[Value.text [97]], [Value.text [65]]]
    | throwError "SQL inference did not supply the intended case-pair rows"
  discard <| Check.refuteWitness (mkConst ``claim) { database := databaseExpr witness.raw }
  logInfo "inferred SQL counterexample certified"

/-- Qualified and quoted names must survive inference; constants include actual bindings. -/
def bound : Script := (sql r#"SELECT p."odd name" FROM "Line Items" AS p WHERE p."odd name" = :amount"#)
  (Value.integer 27)

#guard (Sampling.scriptHints bound).expressions.values.contains (.integer 27)
#guard (Sampling.scriptHints bound).schema.any fun database =>
  (database.raw.catalog.columnsOf (Belay.Sqlite.Model.Identifier.ofString "Line Items")).map
    (·.map (·.name.text)) == some ["odd name"]
#guard (Sampling.scriptCandidates bound).any fun database =>
  database.rows "Line Items" == some [[Value.integer 27], [Value.integer 27]]
#guard (Sampling.scriptCandidates (sql "SELECT 1")).all (fun database => database.raw.catalog.isEmpty)
#guard (Sampling.scriptHints (sql "UPDATE ledger SET total = 19 WHERE key = X'00FF'")).expressions.values.contains
  (.blob [0, 255])
