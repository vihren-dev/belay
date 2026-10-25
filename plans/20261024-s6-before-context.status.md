# Status: S6 initial/current query context

Created 2026-10-24. Status: IN PROGRESS.
Task: [task file](20261024-s6-before-context.task.md).
Specs: ADR17 S6 and the checked foundations prototype.

## Evidence and prerequisites

The prototype confirms that before-qualified queries are rejected and that the
current evaluator has one database origin. The guide explicitly requires fixed
initial-database observations. A bounded read-only context supplies that behavior
through the existing model; a general connection attachment feature is unnecessary.

The query-source/CTE/view representation is complete (PR #255), so this task now
owns the resolver, evaluator and text-translator files for qualified sources. The
accepted S6 equivalence and universal guide-effect decisions do not change this
primitive's meaning.

## Native SQLite 3.51.0 findings that bound the first version

- `before.t.a` names a column of `FROM before.t`; `before.t.*` is a syntax error
  in SQLite, so the model gives no three-part star.
- A table alias hides the table name: `FROM before.t AS x` allows `before.x.a`
  and refuses `before.t.a`.
- `FROM t, before.t` makes an unqualified column of both tables ambiguous.
- `before.nosuch` is "no such table" at prepare time (an error, never an empty
  observation).
- Schema arguments of table-valued functions (`before.f(args)`) and references
  to `before` inside view and trigger bodies are refused, as are schemas other
  than `before`. A view of the initial database expands in the initial context.

## Progress

- 2026-10-24: specified exact origins, metadata/context propagation, conservative
  extension laws and native two-database observation tests. Await task review.
  No production change or task acceptance result is claimed.
- 2026-10-25: native findings recorded above and task text corrected (no three-part
  star; `before` in view and trigger bodies and in function sources stays refused).
  Design fixed: the initial database and catalog are optional trailing arguments of
  resolution and evaluation; `Resolved.Source.initialTable` reads the initial database;
  one dispatch (`usesSchema`) makes ordinary queries use the unchanged path.
- 2026-10-25, commit "model: read the fixed initial database through a before-qualified
  source": `Syntax.TableReference.schema`, `Expr.qualified ... (schema)`, `ScopeSource.initial`,
  `Resolved.Source.initialTable`, optional `initial` arguments of `resolveSelect` and of
  the evaluator chain (`QuerySource.join` to `resolvedStepOutput`); restriction
  `initial-database`; translator accepts `before` only. Checks: `just dev-build`,
  Nix predictions equal to the baseline (one reason text restored), `tests/syntax_*`,
  restriction tests. Local results are not evidence.
- 2026-10-25, commit "model: observe a query over the initial and the current database":
  `observeTwoState`, `resolveTwoState`, `usesSchema`, `Syntax.Statement.asQuery?`; laws
  `*_initial_irrelevant` and `*_current_irrelevant` from `QuerySource.join` to
  `resolvedStepOutput`; conservative extension `observeTwoState_ordinary`; kernel
  fixtures `TwoStateExamples` and `TwoStateViewExamples`; surface entry
  `Script.observeTwoState`; `tests/surface_two_state_test.py` (native differential
  oracle with the pinned sqlite3 and an attached read-only copy, mutation check, refusal
  checks, modeled write between observations, axiom audit). Names and rowid: the model
  refuses `rowid`, `_rowid_` and `oid`, so the rowid fixture reads the alias name.
  The native oracle finds unqualified names in an attached database when the main
  database lacks the table, which the model (correctly) does not; the cases keep a
  current table whenever they query an unqualified name.
- 2026-10-25, review of the first commit: four rounds, each with new "must" findings, all
  fixed except one "should" finding that is rejected with a reason. The fixes: `CREATE VIEW`
  with a `before` source is refused (`initial-database`) because SQLite refuses it; error
  text of a three-part column keeps the schema name; the expansion of an initial view does
  not tag a function call as `before`; examples for initial views, subqueries and
  `Scope.resolveSchemaQualified_below`. The review rule for four rounds applies: the
  owner decides how to continue before the second commit is reviewed.
