import ConcatExpansion

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

/-! A fixture module of {lit}`tests/surface_derived_column_test.py`: two derived expressions other than the lowercase of
one column (ADR 0017, S6). In the first example the migration stores {lit}`a || b` in a TEXT column and the lookup
{lit}`WHERE a || b = lower(?1)` moves to {lit}`WHERE c = lower(?1)`. The general laws apply, and the fixture shows
that their site and their success are satisfiable on a database. In the second example the migration stores the
integer {lit}`a + b` in a TEXT column and the lookup {lit}`WHERE a + b = 5.0` moves to {lit}`WHERE c = 5.0`. TEXT
affinity turns the stored 5 into the text '5' and the probe 5.0 into the text '5.0', so the premise that the
affinity of the column changes neither operand of the comparison fails, and the lookups differ. The fixture emits
the SQL of each lookup for the native check. -/

namespace DerivedColumnExamples
open Belay.Sqlite ConcatFixture LowercaseFixture
open Belay.Sqlite.Model hiding Database

/-- A complete environment with a constant clock and the counters after the setup INSERT. -/
def environment : Env :=
  { clock := some (fun _ => 0)
    counters := { changes := some 1, totalChanges := some 1, lastInsertRowid := some 1 } }

/-- One row with two text parts, before the TEXT column exists. -/
def joined : Belay.Sqlite.Database := db! r"
  CREATE TABLE t(id INTEGER PRIMARY KEY, a TEXT, b TEXT);
  INSERT INTO t VALUES(1, 'al', 'pha');"

/-- The first context of {name}`joined`. -/
def joinedInitial : ExecutionContext := ExecutionContext.initial joined environment

/-- The migration: add the TEXT column and fill it with the concatenation of the two columns. -/
def joinMigration : Script := sql r"
  ALTER TABLE t ADD COLUMN c TEXT;
  UPDATE t SET c = a || b;"

/-- The guide's script is the general derived-column migration of {name}`pipesWritten`, without triggers and
bound values. Proof sketch: the parsed statements and the general script's statements are the same terms. -/
theorem joinMigration_is_general :
    joinMigration = DerivedColumnMigration.migration (name! "t") (textDefinition (name! "c"))
      (pipesWritten (name! "a") (name! "b")) [] [] [] := rfl

/-- The table of {name}`joined` at catalog position 0. -/
def joinedTable : Table := (joined.raw.table 0).get (by decide +kernel)

/-- The one-row database has the site of the concatenation migration: the table is found by name at position
0, the id is column 0, the parts are columns 1 and 2, no column is named {lit}`c`, and no trigger exists. Proof
sketch: each field is a closed fact about the parsed database, checked by kernel evaluation. -/
theorem joined_has_site : Nonempty (ConcatSite joined.raw (name! "t") (name! "id") (name! "a") (name! "b") (name! "c")) :=
  ⟨{ position := 0, table := joinedTable, id := 0, first := 1, second := 2
     found := by decide +kernel
     present := (Option.some_get _).symm
     fresh := by decide +kernel
     idFound := by decide +kernel
     firstFound := by decide +kernel
     secondFound := by decide +kernel
     keysInside := by decide +kernel
     plain := by decide +kernel
     noneFiring := by decide +kernel }⟩

/-- The migration succeeds at the first context on every branch, so the context is in the domain of the
translation law. Proof sketch: kernel evaluation of the public success predicate. -/
theorem joined_domain : Migration.Domain (send joinMigration) (fun _ => True) joinedInitial :=
  ⟨True.intro, by decide +kernel⟩

/-- For every bound value, the lookup {lit}`WHERE a || b = lower(?1)` before the migration and the lookup
{lit}`WHERE c = lower(?1)` after it have equal actual values, traces and branch observations at the first
context. Plain words: in the one-row database, looking up the id by the concatenation before the migration
gives what looking it up by the stored column gives after it, for every probe value. Proof sketch: the general
{name}`concat_queryTranslates` with the site {name}`joined_has_site`. -/
theorem joined_lookup_translates (value : Value) :
    Migration.TranslatesAt (send joinMigration) (fun _ => True)
      (send ⟨[(pipesLookup (tableReference (name! "t") none) (name! "id") (name! "a") (name! "b") "id" 1,
        [value])]⟩)
      (send ⟨[(storedLookup (tableReference (name! "t") none) (name! "id") (name! "c") "id" 1, [value])]⟩)
      joinedInitial := by
  rw [joinMigration_is_general]
  exact concat_queryTranslates (name! "t") none (name! "id") (name! "a") (name! "b") (name! "c") "id" 1 value
    [] [] [] joined joined_has_site environment ⟨rfl, rfl, rfl, rfl⟩

/-- The lookup before the migration, with the probe as a literal. -/
def joinedBefore : Script := sql r"SELECT id FROM t WHERE a || b = lower('ALPHA')"

/-- The lookup after the migration, with the same probe. -/
def joinedAfter : Script := sql r"SELECT id FROM t WHERE c = lower('ALPHA')"

/-- The migration and the lookup after it as one script. -/
def joinedWitness : Script := sql r"
  ALTER TABLE t ADD COLUMN c TEXT;
  UPDATE t SET c = a || b;
  SELECT id FROM t WHERE c = lower('ALPHA');"

/-- Both lookups find the row. Proof sketch: kernel evaluation of the two runs. -/
theorem joined_outputs :
    ((send joinedBefore).runFrom joinedInitial.clock joinedInitial.index joinedInitial.connection).value =
      some [.rows [[.integer 1]]] ∧
    ((Migration.after (send joinMigration) (send joinedAfter)).runFrom joinedInitial.clock joinedInitial.index
      joinedInitial.connection).value = some [.rows [[.integer 1]]] := by
  decide +kernel

/-- One row of integers, before the TEXT column exists. -/
def summed : Belay.Sqlite.Database := db! r"
  CREATE TABLE u(id INTEGER PRIMARY KEY, a INTEGER, b INTEGER);
  INSERT INTO u VALUES(1, 2, 3);"

/-- The first context of {name}`summed`. -/
def summedInitial : ExecutionContext := ExecutionContext.initial summed environment

/-- The migration: add a TEXT column and fill it with the integer sum of the two columns. -/
def sumMigration : Script := sql r"
  ALTER TABLE u ADD COLUMN c TEXT;
  UPDATE u SET c = a + b;"

/-- The lookup before the migration, with the REAL probe 5.0. -/
def sumBefore : Script := sql r"SELECT id FROM u WHERE a + b = 5.0"

/-- The lookup after the migration, with the same probe. -/
def sumAfter : Script := sql r"SELECT id FROM u WHERE c = 5.0"

/-- The migration and the lookup after it as one script. -/
def sumWitness : Script := sql r"
  ALTER TABLE u ADD COLUMN c TEXT;
  UPDATE u SET c = a + b;
  SELECT id FROM u WHERE c = 5.0;"

/-- The migration succeeds at the first context. Proof sketch: kernel evaluation. -/
theorem summed_domain : Migration.Domain (send sumMigration) (fun _ => True) summedInitial :=
  ⟨True.intro, by decide +kernel⟩

/-- The lookup before the migration finds the row, and the lookup after it finds nothing. Proof sketch: kernel
evaluation of the two runs. -/
theorem summed_outputs :
    ((send sumBefore).runFrom summedInitial.clock summedInitial.index summedInitial.connection).value =
      some [.rows [[.integer 1]]] ∧
    ((Migration.after (send sumMigration) (send sumAfter)).runFrom summedInitial.clock summedInitial.index
      summedInitial.connection).value = some [.rows []] := by
  decide +kernel

/-- The moved lookup does not translate the original one, although the migration succeeds. Plain words: at the
first context the two lookups have different values. Proof sketch: the weak translation compares the values,
which {name}`summed_outputs` separates. -/
theorem summed_lookup_not_translated :
    ¬ Migration.TranslatesAt (send sumMigration) (fun _ => True) (send sumBefore) (send sumAfter) summedInitial := by
  intro claim
  have same := congrArg Prod.fst (claim summed_domain).actual
  change ((send sumBefore).runFrom summedInitial.clock summedInitial.index summedInitial.connection).value =
    ((Migration.after (send sumMigration) (send sumAfter)).runFrom summedInitial.clock summedInitial.index
      summedInitial.connection).value at same
  rw [summed_outputs.1, summed_outputs.2] at same
  cases same

/-- The premise of the general move law fails for this example: the comparison of the stored cell with the
probe differs from the comparison of the computed value with the probe. The stored cell is the integer 5 after
TEXT affinity, and the probe is the REAL value 5.0, whose bits are {lit}`0x4014000000000000`. Proof sketch:
kernel evaluation of the two comparisons. -/
theorem affinity_premise_fails :
    Resolved.compareValue .eq (some .text) .binary (Value.store .text (.integer 5)) (.real 0x4014000000000000) ≠
      Resolved.compareValue .eq none .binary (.integer 5) (.real 0x4014000000000000) := by
  decide +kernel

#print axioms joinMigration_is_general
#print axioms joined_has_site
#print axioms joined_domain
#print axioms joined_lookup_translates
#print axioms joined_outputs
#print axioms summed_domain
#print axioms summed_outputs
#print axioms summed_lookup_not_translated
#print axioms affinity_premise_fails

open Lean Elab Meta in
/-- Keep exact model value tags so the test can compare native observations. -/
def outputJson : Output → Json
  | .rows rows => Json.mkObj [("rows", toJson rows)]
  | .done changes => Json.mkObj [("done", toJson changes)]
  | .error code => Json.mkObj [("error", toJson code)]
  | .oneOf results => Json.mkObj [("oneOf", toJson results)]
  | .unmodeled reason => Json.mkObj [("unmodeled", toJson reason)]

open Lean Elab Meta in
/-- Emit one replay of the S5 path: the SQL text, and the outputs that the model gives. -/
def emitReplay (name : String) (report : Replay.Report) : Term.TermElabM Unit := do
  logInfo m!"REPLAY:{(Json.mkObj [("name", toJson name), ("sql", toJson report.sqlite),
    ("outputs", toJson (report.outputs.map outputJson))]).compress}"

open Lean Elab Meta in
/-- Replay each lookup on the database it reads: the original lookups before the migration, and the moved
lookups after the migration script. -/
elab "report_derived_column_replays" : command => Command.liftTermElabM do
  emitReplay "joined-before" (← Replay.scriptReport (mkConst ``joined) (mkConst ``joinedBefore))
  emitReplay "joined-after" (← Replay.scriptReport (mkConst ``joined) (mkConst ``joinedWitness))
  emitReplay "summed-before" (← Replay.scriptReport (mkConst ``summed) (mkConst ``sumBefore))
  emitReplay "summed-after" (← Replay.scriptReport (mkConst ``summed) (mkConst ``sumWitness))

report_derived_column_replays

end DerivedColumnExamples
