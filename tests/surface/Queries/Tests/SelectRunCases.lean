import SelectProcedureCases

set_option doc.verso true

/-! The check of a query ({lit}`Sql.check`) at the initial context of a database, proved by
{lit}`sql_select` and by {lit}`sql_run`, which gives the check of one query to {lit}`sql_select`. The
claims are those of the core set, stated as a check or as a Hoare triple instead of as a run. The
schemas and the scripts are those of the case modules. -/

namespace SelectRunCases
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database
open SelectProjectionCases SelectGroupCases

/-- A04 as a check: for every database with the catalog of {name}`invoices` and every environment, the
query of every customer, run at the initial context, ends with each result that is a list of rows being
a permutation of the customer cells of the scanned rows ({name}`Database.scanAt`). A result that is an
error is not constrained. -/
theorem customers_check (db : Database) (env : Env) (schema : db.HasCatalog invoices) :
    (query SelectCardinalityCases.customers SelectCardinalityCases.customers_one).check
      (fun result _ => ∀ rows, result = .ok rows → rows.Perm ((db.scanAt 0).map fun row => [row.getD 1 .null]))
      (ExecutionContext.initial db env) := by
  sql_select [schema]

/-- The claim of {name}`customers_check`, proved by {lit}`sql_run`, which gives the check of the query to
{lit}`sql_select`. -/
theorem customers_run (db : Database) (env : Env) (schema : db.HasCatalog invoices) :
    (query SelectCardinalityCases.customers SelectCardinalityCases.customers_one).check
      (fun result _ => ∀ rows, result = .ok rows → rows.Perm ((db.scanAt 0).map fun row => [row.getD 1 .null]))
      (ExecutionContext.initial db env) := by
  sql_run [schema]

/-- A08 as a check: for every database with the catalog of {name}`orders` and every environment,
{lit}`count(*)`, run at the initial context, ends with the result of one row with the number of scanned
rows, also 0 for no row. -/
theorem count_check (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (query SelectCountCases.countAll SelectCountCases.countAll_one).check
      (fun result _ => result = .ok [[.integer (db.scanAt 0).length]]) (ExecutionContext.initial db env) := by
  sql_run [schema]

/-- A08 as a Hoare triple: for every database with the catalog of {name}`orders` and every environment,
from the initial context, {lit}`count(*)` ends with the result of one row with the number of scanned
rows. -/
theorem count_triple (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    ⦃fun context : ExecutionContext => ⌜context = ExecutionContext.initial db env⌝⦄
      query SelectCountCases.countAll SelectCountCases.countAll_one
    ⦃⇓ result _ => ⌜result = .ok [[.integer (db.scanAt 0).length]]⌝⦄ := by
  sql_run [schema]

end SelectRunCases

#print axioms SelectRunCases.customers_check
#print axioms SelectRunCases.customers_run
#print axioms SelectRunCases.count_check
#print axioms SelectRunCases.count_triple
