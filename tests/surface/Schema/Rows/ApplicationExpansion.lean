import LowercaseSimulation

/-! A fixture module of `tests/surface_application_test.py`: lookups across the lowercase-field expansion
(ADR 0017, S8). The expansion adds a stored lowercase copy of the email, fills it, and creates two
triggers that keep it filled. The scoped theorem for lookups is universal over databases with a site;
this fixture instantiates it on the customers database. The fixtures {lit}`ApplicationCounterCalls` and
{lit}`ApplicationMissingTrigger` build on it. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace ApplicationExpansionFixture
open Belay.Sqlite Belay.Sqlite.Calls LowercaseFixture
open Belay.Sqlite.Model hiding Database

/-- One customer before the stored column exists. -/
def sample : Belay.Sqlite.Database := db! r"
  CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  INSERT INTO customers VALUES(1, 'Ada', 'Alpha@X');"

/-- A complete environment that matches the counters after the setup INSERT. -/
def environment : Env :=
  { clock := some (fun _ => 0)
    counters := { changes := some 1, totalChanges := some 1, lastInsertRowid := some 1 } }

/-- The first context of the sample. -/
def initial : ExecutionContext := ExecutionContext.initial sample environment

/-- The expansion: add the field, fill it, and create the two maintenance triggers. -/
def expansion : Script := sql r"
  ALTER TABLE customers ADD COLUMN email_lower TEXT;
  UPDATE customers SET email_lower = lower(email);
  CREATE TRIGGER customers_email_ins AFTER INSERT ON customers BEGIN
    UPDATE customers SET email_lower=lower(NEW.email) WHERE id=NEW.id; END;
  CREATE TRIGGER customers_email_upd AFTER UPDATE OF email ON customers BEGIN
    UPDATE customers SET email_lower=lower(NEW.email) WHERE id=NEW.id; END;"

/-- The body of both triggers. -/
def maintenanceBody : List Syntax.BodyStatement :=
  [.update (name! "customers")
    [(name! "email_lower", .call "lower" [.qualified (name! "NEW") (name! "email")])]
    (some (.compare .eq (.identifier (name! "id") .none) (.qualified (name! "NEW") (name! "id"))))]

/-- The trigger after every INSERT. -/
def insertTrigger : Identifier × CatalogTrigger :=
  (name! "customers_email_ins",
    { table := name! "customers", time := .after, event := .insert, body := maintenanceBody })

/-- The trigger after an UPDATE of the email. -/
def updateTrigger : Identifier × CatalogTrigger :=
  (name! "customers_email_upd",
    { table := name! "customers", time := .after, event := .update [name! "email"],
      body := maintenanceBody })

/-- The plan of the expansion above. -/
def plan : Plan :=
  { tableName := name! "customers", alias := none, idName := name! "id", sourceName := name! "email"
    storedName := name! "email_lower", text := "id", number := 1, first := insertTrigger,
    second := updateTrigger, firstValues := [], secondValues := [], thirdValues := [], fourthValues := [] }

/-- The migration of the plan is the script above. Proof sketch: the two terms are the same. -/
theorem plan_migration_is_the_script : plan.migration = send expansion := rfl

/-- The table of the sample at catalog position 0. -/
def sampleTable : Table := (sample.raw.table 0).get (by decide +kernel)

/-- The sample has a site for the plan. Proof sketch: each field is a closed fact about the parsed
database, checked by kernel evaluation. -/
theorem sample_has_site :
    Nonempty (LowercaseSite sample.raw plan.tableName plan.idName plan.sourceName plan.storedName) :=
  ⟨{ position := 0, table := sampleTable, id := 0, source := 2
     found := by decide +kernel
     present := (Option.some_get _).symm
     fresh := by decide +kernel
     idFound := by decide +kernel
     sourceFound := by decide +kernel
     keysInside := by decide +kernel
     plain := by decide +kernel
     noneFiring := by decide +kernel }⟩

/-- The first context of the sample is admitted. Proof sketch: the facts of a valid database with a site
({name}`Plan.Source.ofDatabase`). -/
theorem initial_is_admitted : plan.Admitted initial := by
  obtain ⟨site⟩ := sample_has_site
  exact ⟨Plan.Source.ofDatabase plan sample environment.counters site⟩

/-- The expansion succeeds at the first context, so the context is in the migration domain. Proof
sketch: kernel evaluation of the success predicate. -/
theorem original_domain : Migration.Domain plan.migration plan.Admitted initial :=
  ⟨initial_is_admitted, by decide +kernel⟩

/-- An application over lookups that chooses its second lookup from the result of the first: when the
first lookup finds a row it gives true, otherwise it looks up the second value. -/
def lookupTwice (first second : Value) : Application lookupSignature Bool :=
  .call () first fun found =>
    match found with
    | [.rows (_ :: _)] => .pure true
    | [] | [.rows []] | [.done _] | [.error _] | [.oneOf _] | [.unmodeled _] | _ :: _ :: _ =>
      .call () second fun other => .pure (other == [.rows []])

/-- On the sample, every branch of the expansion gives an agreement of the application with original
lookups and the application with stored lookups, for every pair of values. It is an instance of the
universal theorem {name}`Plan.lookups_agree_after_expansion`. -/
theorem lookups_agree_at_sample (first second : Value) (run : SqlRun (List Output))
    (branch : plan.migration.Branch initial.clock initial.index initial.connection run)
    (value : List Output) (returned : run.value = some value) :
    Sql.ScopedAt plan.Related ((lookupTwice first second).interp plan.pairing.old)
      ((lookupTwice first second).interp plan.pairing.new) initial
      ((Sql.View.quiet plan.migration).finish initial run) :=
  plan.lookups_agree_after_expansion _ initial original_domain run branch value returned

/-- The context that the quiet view gives after the actual run of the expansion from a context. -/
def migratedFrom (state : ExecutionContext) : ExecutionContext :=
  (Sql.View.quiet plan.migration).finish state (plan.migration.runFrom state.clock state.index state.connection)

#print axioms sample_has_site
#print axioms original_domain
#print axioms lookups_agree_at_sample

end ApplicationExpansionFixture
