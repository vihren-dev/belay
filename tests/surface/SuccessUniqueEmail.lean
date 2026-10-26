import Belay

set_option doc.verso true

/-! The corrected Level 2 email example requires a physical customers table, the SQL
uniqueness guard and a free index name. The guard supplies email-column existence. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The guide precondition: each NOCASE email group has at most one row. -/
def noDuplicateEmails : Script := sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM customers GROUP BY email COLLATE NOCASE HAVING count(*) > 1)"

/-- For every existing email column, the explicit NOCASE grouping term resolves to
that column under NOCASE. Proof sketch: resolve the column, then its explicit collation. -/
theorem group_nocase {table : CatalogTable} {index : Nat}
    (found : columnPosition table.columns (name! "email") = some index) (db : Database) (position : Nat) :
    GroupTermResolves true (tableScope db.raw.catalog { table := name! "customers", alias := none } position table)
      { current := some 0, aggregates := [.callStar "count"] }
      (.collate (.identifier (name! "email") .none) (name! "NOCASE")) (.column index) .nocase := by
  have resolved : (tableScope db.raw.catalog { table := name! "customers", alias := none } position table).resolveName (name! "email") =
      .found index [index] := resolveName_one_source_at found
  have operand := resolveOperand_identifier_table (catalog := db.raw.catalog) (reference := {table := name! "customers", alias := none})
    (position := position) (dqs := true) (shapes := {current := some 0, aggregates := [.callStar "count"]})
    (misuse := true) (quote := Syntax.QuoteKind.none) found
  simp only [GroupTermResolves, resolveGroupTerm_collate, Syntax.Expr.collatedColumn, resolved]
  rw [resolveOperand_collate _ (by rfl)]
  rw [operand]
  have coll : Collation.named? (name! "NOCASE") = some .nocase := rfl
  simp [Syntax.Expr.collationIn, Syntax.Expr.explicitCollation, coll,
    Except.mapError, Except.map]

/-- For every customers table without an email column, the grouping claim is false.
Proof sketch: its COLLATE term is not a column, so subquery resolution gives a model
restriction and the resulting output has no rows. -/
theorem missing_email (db : Database) (position : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "customers") = some (position, table))
    (missing : columnPosition table.columns (name! "email") = none) :
    ¬ Holds noDuplicateEmails db := by
  have absent : (tableScope db.raw.catalog { table := name! "customers", alias := none } position table).resolveName
      (name! "email") = .missing := by
    simp [tableScope, Scope.resolveName, Scope.depths, Scope.singleAt, Scope.resolveAt, Scope.resolveStep, missing]
  have one : queryNumeric "1" false = .ok (.integer 1) := rfl
  have countName : normalizeIdentifier "count" = "count" := rfl
  have sources := resolveSources_table db.raw.catalog { table := name! "customers", alias := none } position table rfl rfl rfl found
  have application : reservedName (name! "customers") = false := by decide
  have unique : ([0] : List Nat).eraseDups = [0] := rfl
  have noMain : ∀ queries prefix_, resolveSources db.raw.catalog none [] 0 queries prefix_ = .ok ([], []) := by
    intros
    rfl
  have notView := Catalog.findView_none_of_table found
  have resolved : ∃ restriction, resolveStatement runContext db.raw.connection.resolveState
      noDuplicateEmails.statements[0].1 = .error restriction := by
    simp [noDuplicateEmails, resolveStatement_select, resolveSelect, resolveSelectTraced, resolveSelectDetailsTraced, prepareQuerySourcesTraced, resolveSourcesTraced_drop, resolveQueryBodyTraced_drop, traced_drop, traced_arms, aliasJoinItem?, querySourceCopiesNeeded, Syntax.TableReference.namesStoredView, notView,
      CommonTableCopies.recursionIssue, CommonTableCopies.originalIssue, CommonTableCopies.originalPath, Connection.resolveState, Database.Raw.connection,
      subqueryScopes, subqueryScopesTraced, scopeOrder, compoundOf, subqueryScope, subqueryScopeTraced, Scope.columns,
      noMain, sources, Scope.enclose, resolveSubqueryBodies, resolveSubqueryBodiesTraced, subqueryBodyOrder, unique, QueryScope.sourceIndexes, QueryScope.refresh, QueryScope.refreshTraced, Scope.refreshSources, compoundColumnsIssue,
      prepareError, ResolveState.withCatalog, Bind.bind, Except.bind, Except.mapError,
      Except.map, Functor.map, Pure.pure, Except.pure, starIssue, SourceIssue.under,
      resolveAll, resolveAllFrom, countName, Syntax.Expr.aggregateCalls, aggregateCall, Syntax.Expr.distinctList, resolvePendingSources_table, resultAliases, resultCollations, resolveGroupTerm_collate, Syntax.Expr.collatedColumn, absent, Syntax.Expr.collationIn, issueResolution, restrict, one, definedName, ValueIssue.under]
  obtain ⟨restriction, failed⟩ := resolved
  intro holds
  have output := Script.outputOn_eq_step noDuplicateEmails db _ [] [] rfl
  change noDuplicateEmails.outputOn db = some (match resolveStatement runContext db.raw.connection.resolveState noDuplicateEmails.statements[0].1 with | .error restriction => .unmodeled restriction.reason | .ok (resolved, _) => resolvedStepOutput none 0 db.raw.connection [] resolved) at output
  rw [failed] at output
  simp [Holds, output, Output.hasRows] at holds

/-- The unique email index of the guide. -/
def uniqueEmail : Script := sql r"CREATE UNIQUE INDEX customers_email ON customers (email COLLATE NOCASE)"

/-- For every database with a physical customers table, where the guide grouping query
holds and the index name is free, the email index succeeds in every complete environment.
Proof sketch: the table premise supplies the source, the grouping claim excludes a missing
email column, and the grouping law excludes key conflicts. These facts supply the exact
CREATE INDEX success conditions. -/
theorem uniqueEmail_ok : Succeeds uniqueEmail (fun db =>
    (db.catalog.findTable (name! "customers")).isSome = true ∧ Holds noDuplicateEmails db ∧
    db.catalog.find (name! "customers_email") = none) := by
  apply (Succeeds.iff_createIndex (script := uniqueEmail) (head := rfl) _).mpr
  rintro db ⟨tablePresent, holds, freeName⟩
  cases found : db.raw.catalog.findTable (name! "customers") with
  | none => simp [Belay.Sqlite.Database.catalog, found] at tablePresent
  | some pair =>
    rcases pair with ⟨position, table⟩
    cases column : columnPosition table.columns (name! "email") with
    | none => exact False.elim (missing_email db position table found column holds)
    | some index =>
      have groups := (Holds.iff_selectOne_noDuplicateKeys (head := rfl) (count := rfl)
        (namedSource := rfl) (current := rfl) (arguments := rfl) (found := found) (groupResolves := group_nocase column db position)
        (keyCalm := Resolved.Expr.calm_column index)).mp holds
      refine ⟨position, table, [{ term := .column index, collation := .nocase }], none,
        found, by decide, by decide, freeName, ?_, rfl, ?_⟩
      · have coll : Collation.named? (name! "NOCASE") = some .nocase := rfl
        simp [indexKeys, indexTerm, column, coll, Syntax.Expr.collationIn, Syntax.Expr.explicitCollation,
          Functor.map, Except.map, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · intro _
        exact LiteralData.uniqueRows_of_column_groups
          {shape := table, rows := db.raw.rows.getD position []} (Resolved.EvalContext.bound []) (by simp [CatalogIndex.uniqueKey]) groups


/-- The corrected condition holds on a table whose two emails differ under NOCASE. -/
def distinctEmails : Database := db! r"CREATE TABLE customers (email TEXT); INSERT INTO customers VALUES ('a@x'), ('b@x')"
example : (distinctEmails.catalog.findTable (name! "customers")).isSome = true ∧
    Holds noDuplicateEmails distinctEmails ∧ distinctEmails.catalog.find (name! "customers_email") = none := by
  decide +kernel
example : (distinctEmails.run uniqueEmail).outputs.allOk = true := by decide +kernel

-- The original guide claim omits the name check: this database satisfies its SQL query
-- but an existing table uses the requested index name.
example : let db := db! r"CREATE TABLE customers (email TEXT); CREATE TABLE customers_email (x)";
    Holds noDuplicateEmails db ∧ (db.run uniqueEmail).outputs.allOk = false := by decide +kernel

-- NOCASE folds ASCII only; both addresses can remain distinct under the index.
example : let db := db! r"CREATE TABLE customers (email TEXT); INSERT INTO customers VALUES ('é@x'), ('É@x')";
    Holds noDuplicateEmails db ∧ (db.run uniqueEmail).outputs.allOk = true := by decide +kernel

#print axioms uniqueEmail_ok
