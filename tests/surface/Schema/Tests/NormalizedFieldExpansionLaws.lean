import LowercaseQueries

/-! Installed consumers of the general derived-column migration laws, with the lowercase of one column as
the derived expression. The concrete customers expansion of the counter example is an instance of the general
four-statement script, its database has a site, and the public query laws give an observation equality at its
initial context. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace NormalizedFieldExpansionFixture
open Belay.Sqlite LowercaseFixture
open Belay.Sqlite.Model hiding Database

/-- One customer; the same database as in the counter example. -/
def sample : Database := db! r"
  CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  INSERT INTO customers VALUES(1, 'Ada', 'Alpha@X');"

/-- The environment of the counter example: all inputs known after the setup INSERT. -/
def environment : Env :=
  { clock := some (fun _ => 0)
    counters := { changes := some 1, totalChanges := some 1, lastInsertRowid := some 1 } }

/-- The initial execution context of the sample. -/
def initial : ExecutionContext := ExecutionContext.initial sample environment

/-- The four-statement expansion of the counter example. -/
def expansion : Script := sql r"
  ALTER TABLE customers ADD COLUMN email_lower TEXT;
  UPDATE customers SET email_lower = lower(email);
  CREATE TRIGGER customers_email_ins AFTER INSERT ON customers BEGIN
    UPDATE customers SET email_lower=lower(NEW.email) WHERE id=NEW.id; END;
  CREATE TRIGGER customers_email_upd AFTER UPDATE OF email ON customers BEGIN
    UPDATE customers SET email_lower=lower(NEW.email) WHERE id=NEW.id; END;"

/-- The environment is complete. Proof sketch: every field holds a value. -/
theorem complete_environment : environment.Complete := ⟨rfl, rfl, rfl, rfl⟩

/-- The expansion succeeds at the initial context on every branch, so it is inside the domain of
the translation laws. Proof sketch: kernel evaluation of the public success predicate. -/
theorem original_domain : Migration.Domain (send expansion) (fun _ => True) initial := by
  exact ⟨True.intro, by decide +kernel⟩

/-- The body of both triggers: copy the lowercase of the new email into the stored field of the
changed row. -/
def maintenanceBody : List Syntax.BodyStatement :=
  [.update (name! "customers")
    [(name! "email_lower", .call "lower" [.qualified (name! "NEW") (name! "email")])]
    (some (.compare .eq (.identifier (name! "id") .none) (.qualified (name! "NEW") (name! "id"))))]

/-- The trigger that runs after every INSERT into {lit}`customers`. -/
def insertTrigger : Identifier × CatalogTrigger :=
  (name! "customers_email_ins",
    { table := name! "customers", time := .after, event := .insert, body := maintenanceBody })

/-- The trigger that runs after an UPDATE of {lit}`email` in {lit}`customers`. -/
def updateTrigger : Identifier × CatalogTrigger :=
  (name! "customers_email_upd",
    { table := name! "customers", time := .after, event := .update [name! "email"],
      body := maintenanceBody })

/-- The counter example's expansion is the general four-statement expansion of the table
{lit}`customers` with the field {lit}`email_lower` over {lit}`lower(email)`, with the two
CREATE TRIGGER statements of {name}`insertTrigger` and {name}`updateTrigger` and no bound values.
Proof sketch: the parsed statements and the general script's statements are the same terms, so
the equality holds by reflexivity. -/
theorem counter_expansion_is_general :
    expansion =
      LowercaseFixture.expansion (name! "customers") (name! "email_lower") (name! "email")
        insertTrigger updateTrigger [] [] [] [] := by
  rfl

/-- The table of the one-customer database at catalog position 0. -/
def sampleTable : Table :=
  (sample.raw.table 0).get (by decide +kernel)

/-- The one-customer database has a site for the expansion: its table is found by name at
position 0, the id is column 0, the email is column 2, no column is named {lit}`email_lower`, and
no trigger exists. Proof sketch: each field is a closed fact about the parsed database, checked
by kernel evaluation. -/
theorem sample_has_site : Nonempty (LowercaseSite sample.raw
    (name! "customers") (name! "id") (name! "email") (name! "email_lower")) :=
  ⟨{ position := 0, table := sampleTable, id := 0, source := 2
     found := by decide +kernel
     present := (Option.some_get _).symm
     fresh := by decide +kernel
     idFound := by decide +kernel
     sourceFound := by decide +kernel
     keysInside := by decide +kernel
     plain := by decide +kernel
     noneFiring := by decide +kernel }⟩

/-- At the counter example's initial context, the original lookup on the email before the expansion
and the stored lookup after it have equal actual values, traces and branch observations, for every
bound value. Plain words: in the one-customer database, looking up an id by the lowercase of the
email before the expansion gives what looking it up by the new lowercase field gives after it.
Proof sketch: the public translation law applies to the general form of the concrete expansion,
with the site of the sample and its success at the initial context
({name}`original_domain`). -/
theorem sample_lookup_translates (value : Value) :
    Migration.TranslatesAt (send expansion) (fun _ => True)
      (send (originalLookupScript (name! "customers") none (name! "id")
        (name! "email") "id" 1 value))
      (send (storedLookupScript (name! "customers") none (name! "id")
        (name! "email_lower") "id" 1 value))
      initial := by
  obtain ⟨site⟩ := sample_has_site
  rw [counter_expansion_is_general]
  exact LowercaseFixture.queryTranslates (name! "customers") none (name! "id") (name! "email")
    (name! "email_lower") "id" 1 value insertTrigger updateTrigger [] [] [] []
    sample ⟨site⟩ environment
    complete_environment

/-- The same instance for the preserved original lookup. Plain words: looking up an id by the
lowercase of the email gives the same result before and after the expansion. Proof sketch: as
{name}`sample_lookup_translates`, with the public preservation law. -/
theorem sample_lookup_preserved (value : Value) :
    Migration.TranslatesAt (send expansion) (fun _ => True)
      (send (originalLookupScript (name! "customers") none (name! "id")
        (name! "email") "id" 1 value))
      (send (originalLookupScript (name! "customers") none (name! "id")
        (name! "email") "id" 1 value))
      initial := by
  obtain ⟨site⟩ := sample_has_site
  rw [counter_expansion_is_general]
  exact LowercaseFixture.queryPreserves (name! "customers") none (name! "id") (name! "email")
    (name! "email_lower") "id" 1 value insertTrigger updateTrigger [] [] [] []
    sample ⟨site⟩ environment
    complete_environment

#print axioms counter_expansion_is_general
#print axioms sample_has_site
#print axioms sample_lookup_translates
#print axioms sample_lookup_preserved
#print axioms DerivedColumnMigration.translatesAt_of_outputs
#print axioms LowercaseFixture.queryTranslates
#print axioms LowercaseFixture.queryPreserves
#print axioms Model.derivedColumn_state

end NormalizedFieldExpansionFixture
