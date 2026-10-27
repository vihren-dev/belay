# Status: query inserts and ALTER table rebuild

Created 2026-10-24. Status: OPEN. The task was checked against the code on
2026-10-26; stage (a) of part 1 is implemented (see Progress).
Task: [task file](20261024-table-rebuild.task.md).
Specs: ADR19 D4/slice 5, ADR17 S6 and ADR22 preservation contracts.

## Accepted decision and prerequisites

On 2026-10-25 the owner accepted possible write executions for plan-dependent
INSERT SELECT behavior. The task and ADR19 now require explicit production
traces and their correlated write states, outputs, errors and counters; public
proofs and conformance must share those alternatives. The pinned optimizer is
not being implemented, and a plan-independent subset is not a substitute.
The existing native rowid/FAIL/ORDER BY probes supply witnesses, not a proof of
complete branch coverage. Review `20261025T015823Z-0088b6d3` of the amendment
had no findings.

The owner accepted exact INSERT SELECT streaming/materialization, including
error precedence and partial writes, on 2026-10-24. ADR19 D4 records the native
overflow-versus-unique-conflict example; the previous always-materialize rule
is superseded. This is a planning/native-source observation, not task acceptance.

The prerequisites have landed: the [query-source task](20261024-query-sources.task.md)
is DONE (2026-10-25), parts 1 and 2 of the
[FK atom task](20261024-foreign-key-atoms.task.md) are accepted, and the
[model name trace](20261025-model-name-trace.task.md) is DONE (2026-10-26). This
task extends those representations and preservation laws. S6's universal
rebuild proof is separate.

## Progress

- 2026-10-24: specified complete D4 scope, three acceptance parts, native
  differential cases and modular contracts. Review `20261024T141909Z-c30f4ce2`
  had no musts and two shoulds. Added the owner cadence override and linked the
  prerequisite tasks. Follow-up review remains.
  No new corpus claim, production source change or acceptance result is claimed.

- 2026-10-26: the workspace `table-rebuild` starts at `4fc773a5` (merged name
  trace), merged with the amendment commit `0088b6d3`, which the base lacked.
  Check of the task against the code and native SQLite 3.51.0, before any
  implementation:
  - Confirmed: the precedence example (rows 2 and 1 stay in `dest` without the
    trigger; integer overflow and no `2` with it); the paired index probes and
    the dead-branch, unused-CTE, UPDATE-only trigger, RETURNING and transfer cases
    of the readiness note (its probe script reproduces them); the file and
    function names of the task; the pinned `parser/upstream/sqlite3.c` (SHA256
    `dc58f0b5`); `Translation/Writes.valueRows` refuses a SELECT source; the
    cadence text agrees with `AGENTS.md`; Valid does not include the FK atoms.
  - Corrected without a change of requirement: the stale prerequisite text, the
    prediction count (55 files, not 53), the superseded owner-choice section of
    the readiness note, and the missing "Starting point" facts (what a catalog
    stores, native rewrite of stored source text, name trace gaps).
  - Open questions, reported to the coordinator and not decided here. (1) Part 1
    holds three changes that each could be a task: the language front end and
    resolution, the exact source production with the insertion fold, and the
    alternatives of a run in the shared statement run, script run, `Sql.Branch`
    and `Output` with the laws of every client. (2) The model syntax does not keep
    the place of the name tokens in stored source text, which the column and
    table renames must rewrite; adding them touches the translator, the syntax
    and its derived instances.
  - Native facts for part 2, verified: `RENAME TO`, `RENAME COLUMN` and
    `DROP COLUMN` leave `changes()`, `total_changes()` and `last_insert_rowid()`
    unchanged; the foreign keys of other tables are rewritten with enforcement
    off; the view output name and the CHECK label are rewritten token by token
    (examples in the task).
  - Name trace gaps for the column rename (planned, to confirm in part 2): a
    view body can be traced as a SELECT statement of its own, which gives exact
    paths. The trigger programs (WHEN condition and body statements with the
    trigger-row scope) need a traced form of `resolveBodyStatement`, so the
    rename closes that gap. CREATE TABLE bodies need no trace, because the
    catalog holds them resolved by position.
  - Plan. Part 1: syntax, text translation, codecs and resolved form of query
    inserts; source production and the insertion fold; the alternatives of a run
    (statement run, script run, `Sql.Branch`, `Output`); preservation laws and
    the narrow query-to-insert contract; conformance membership of complete
    executions; surface forms. Part 2: RENAME TO and RENAME COLUMN with the
    catalog rewrite, the eager validation of views and triggers, rollback, laws
    and conformance. Part 3: DROP COLUMN with the position remap, dependency
    errors, laws, the concrete unsafe and corrected rebuild, documentation.
  - Judge PRs: each part adds authored corpus cases and so needs its own judge
    branch and an owner-approved judge PR (new corpus, claims and lock). The
    conformance classifier is subject code and needs no judge change.
  - Predictions baseline: `build/predictions-baseline` (55 files) is the output of
    the model name trace task, built on its pre-trace base; that task's status
    records that its final tree predicts exactly the same, so it is the baseline
    of `4fc773a5`. It was not rebuilt at `4fc773a5` itself.
  - Review `20261026T091236Z-2957bba7` of the check commit had no findings.

- 2026-10-26: owner decisions (through the coordinator). (1) The alternatives
  interface of write executions is a separate task, `20261026-possible-write-executions`,
  in another workspace; this task consumes it, does stage (a) of part 1 now and stage (b)
  (exact source production and the insertion fold) after the coordinator says to merge
  it. (2) The translator records the place and quoting of name tokens in stored source
  text (view result-column text, CHECK raw text) and the quoting of an ALTER's new name;
  this is the start of part 2. The task file records both.
- 2026-10-26: stage (a), the language front end and the preparation of INSERT SELECT.
  - Syntax: `Syntax.Statement.insertSelect` with `Syntax.SelectBody` as the query (the
    fields of a SELECT statement, so that a path below child 2 is the path in a SELECT).
    Path steps: table 0, column list 1, query 2 (subqueries at 2/8), conflicts 3,
    algorithm 4, RETURNING 5. JSON and `ToExpr` codecs derive.
  - Text: `Translation/Writes.insertQuery` maps `INSERT/REPLACE ... SELECT`, with an ordinary WITH
    prefix, compound queries, conflict clauses and RETURNING. A VALUES source keeps the
    `insert` form. A trigger body still refuses a query source (unchanged, a documented
    limit of triggers). `INSERT ... SELECT ... FROM s ON CONFLICT` is the pinned
    parser's syntax error and stays one; `... WHERE true ON CONFLICT ...` parses.
  - Resolution: `Resolution/InsertQueries.resolveInsertQueryTraced` follows the native
    order checked by probes on 3.51.0: table (a view is "cannot modify"), column list
    (unknown, then generated column), query names, column counts (`N values for M
    columns`, `table t has K columns but N values were supplied`), then conflict
    targets and RETURNING. The destination columns are not visible to the query. The
    name trace has the table, the list, the query, the clauses and RETURNING.
  - Decision: no `Resolved.Statement` constructor yet. A query that SQLite prepares ends
    in the temporary restriction `query-source-insert` (docs/semantic-subset.md,
    conformance/restriction_examples.py); stage (b) replaces it by a resolved form with
    the semantics, so about 40 exhaustive matches are not changed twice. Prepare errors
    are real, resolved outputs. Laws: `resolveInsertQuery_prepareError` and `_same`
    extend the catalog-unchanged, valid and schema-link laws of the resolver.
  - Native finding: SQLite accepts a column named twice in the INSERT column list; the
    model keeps its restriction `insert-column-twice` for it.
  - Deviation to flag: adding the syntax constructor forces exhaustive-match arms in
    four modules that the editor part 2b agent owns (`SqlTableSlots`,
    `SqlStatementContexts`, `SqlOrderWarnings`, `SqlTableOrigins` in
    `packages/belay/Belay/Sqlite/`). The arms are the minimum (the slots of the table
    and of the source tables; the query's nested-subquery slots under child 2/8 are
    not covered and belong to that agent). `SampleScriptHints` (not an editor module)
    gets a real arm. The commit builds only with these arms.
  - Tests: kernel `#guard` examples (`InsertQueryExamples`, 15 cases), `tests/syntax_insert_query_test.py`
    (9 cases), the translation range checks of `tests/surface/TranslationChecks.lean`
    (not run locally: its runner needs the Nix runtime; `just test-full` runs it).
  - Predictions after stage (a): 55 files compared with the baseline. 64 predictions
    changed. 63 are unsupported before and after (the old reason "Only VALUES rows are
    modeled as an INSERT source" or an unsupported `selectnowith`; now
    `query-source-insert` (48), a recursive-common-table restriction (13), or another
    later restriction (2)). One is newly predicted (`select1:select1-4.5:66` in
    corpus-v5): a prepare error of an INSERT SELECT; the Nix verdict
    of the part checks it against the native record.
- 2026-10-26: review `20261026T100318Z-7d3e84be` of stage (a): 3 musts and 2 shoulds, all fixed.
  Finding: a rowid name in an INSERT column list (`INSERT INTO t(rowid) ...`) was resolved as
  "table has no column named rowid", while SQLite stores the rowid. This was already so for
  VALUES inserts. Both forms now give the existing `rowid-name` restriction
  (`insertRowidTarget`; an earlier unknown or generated name stays an error). The file-size
  musts were fixed by shortening `Restrictions.lean` and moving `resolve_namesUnique` to
  `NamesSpecScript.lean`.
- 2026-10-26: predictions recompared after the review fixes (55 files): the same 64 changes
  as before, and 86 `rowid-name` predictions whose message text now names the INSERT column
  list; no status changed. Reviews `20261026T102355Z-3a5d704e` (1 must, fixed) and
  `20261026T102455Z-2c17775a` (no findings). Stage (a) is at a reviewed stopping point; the
  part's `just test-full` and `just verdict` run at the end of part 1.
- 2026-10-26: token positions of stored source text (part 2, first syntax change; owner answer A).
  - Done: the text of a result column is a `Syntax.SourceText` (the text and its
    `Syntax.NameToken`s, in `Resolution/SyntaxTokens.lean`), built by the translator
    (`Translation/NameTokens.lean`). Each token has its byte offsets in the text, its quote
    kind, the node paths of the range tree that have its range, and, for a name inside an
    indexed subquery of the text, the index of that subquery. Result columns of WITH
    definitions, derived tables and subqueries record their own tokens. A plain string
    coerces to a text without tokens, so no construction of a result column changed; the JSON
    of a text without tokens is the plain string.
  - Decision: the translator marks the range-tree nodes that are one name token (`Span.isName`,
    set by `plainName`, the expression identifier and bare aliases), not by reading the text.
    A token carries the paths of every marked node with its range (an identifier and its two
    parts). The name trace's path is one of them, and the fixture
    `tests/surface/NameTokenPaths.lean` checks that every exact trace occurrence inside a result
    column has a token with its path. Names that are no column or table (`max`, aliases) are
    tokens too; a client takes the token by the path of an occurrence. A string where the
    grammar expects a name (`t.'a'`) is a token of the new quote kind `single`; a string
    literal is no token. Review finding R19 (a text heuristic missed `t.'a'`) led to this.
  - Decision: `ResultColumn.reindexM` (the copy for another subquery list) keeps only the
    text. Mapping the tokens' subquery indexes through the reindex function made 6 predictions
    unsupported (`subquery-here`), because the CTE copy's mapping has no entry for an unused
    index.
  - Not done here, by design: the CHECK raw text and the new-name quoting of an ALTER. The CHECK
    label is a resolved string of the catalog, and SQLite derives it from the stored raw text
    (dequoting a text that starts with a quote), so its tokens are only useful together with
    the catalog storing the raw text; the new-name quoting belongs to the RENAME forms, which do
    not exist yet. Both come with the rename statements. The editor's need (replace only the
    identifier) is met by the existing leaf spans of names and the first byte of the token.
  - Tests: `tests/syntax_name_tokens_test.py` (5 cases), `tests/surface_name_tokens_test.py` with
    `NameTokenPaths.lean` (run with the full runtime; locally through a scratch runtime root
    that links the dev-build packages), the syntax tests (the fixture `parse_sql` strips tokens
    unless `name_tokens=True`). Found and fixed a stage (a) range check that had never run
    locally (`TranslationChecks.lean`: the range of an INSERT query keeps the space before
    RETURNING).
  - Decision: tokens are recorded only for result columns in the body of CREATE VIEW (the
    only place where the text names a stored column; `Scope.nameTokens`, set by
    `recordingNameTokens` in `Translation/Views.lean`). The claims fixtures compare `sql!` syntax
    with hand-written syntax by `rfl`, and tokens elsewhere would break that without any use.
    The Python fixture `parse_sql` and `NameTokenPaths.lean` follow (a view for the tokens, a
    SELECT for the trace).
  - Fixes the first `just test-full` exposed (stage (a) leftovers that had never run locally):
    the `rowid-name` message fixtures (`DbBangErrors`, `SqlBangErrors`, `SqlDiagnosticsChecks`),
    and the missing `insertSelect` arms in `ViewsSupport` and `ClaimsViewTriggers`.
  - Predictions: the 55 files are byte-identical to the stage (a) ones (`diff -r` clean).
  - Reviews: `20261026T113647Z-9b5f7fa8` (1 must: single-quoted names; 1 should: the fixture's
    catch-all; both fixed) and `20261026T115129Z-0d0f790e` (1 should, rejected with a reason:
    the fixture marks its statements and fails when a marked one is no SELECT).
  - Gates of the token change (Nix results): `just verdict` passes; the 55 predictions are
    byte-identical to stage (a). `just test-full` on this base (4fc773a5) cannot pass for reasons
    of the base that the possible-executions branch (95b61eb4) repairs: the documentation
    inventory runs out of its 60 s compiler limit (the run takes 70 to 85 s of CPU; the
    inventory itself reports 5320 of 5320 declarations documented), the surface suite ends with
    exit 124, the frozen suite's `test_review_corpus_extends_and_replays` runs out of the 30 s
    classifier limit, and `test_signup_invariant_with_partial_unique_index` needs the
    `resolveOperand_arm_compare` rewrite (commit 9193ed53 of that branch). No other test fails
    (the other suites and the host source tests pass). The gates are to be rerun on the merge
    with 95b61eb4.
- 2026-10-26: merged f5e85829 (editor part 2b on the possible-executions interface) into the
  workspace (`jj new 24abec47 f5e85829`, no conflicts: the editor's modules already carry the
  `insertSelect` arms). The dev-build passes, as do the syntax tests and the surface name-token,
  name-trace, translation, views and editor tests (local scratch runtime). The review of the
  merge (`20261026T135851Z-cbcd2647`) found two musts in the editor agent's plan files, which the
  merge does not change; both rejected with that reason. Gates on the merge: see the entry below.
- Gates on the merge (Nix results): `just test-full` passes (no exception; the base now has the
  surface split and the raised limits), `just verdict` passes, and the 55 predictions are
  byte-identical to the stage (a) ones. Stage (b) waits for the coordinator.

- Merge gates before stage (b) (Nix results, from the coordinator): test-reports
  `/nix/store/yc98h3yg6vgh1iv732dcgz53sjqfx9bl-sqlite-verifier-test-reports`, verdict
  `/nix/store/2ws8nqmj8qllb2psmlxy0wg2953l788z-sqlite-verifier-verdict`, predictions
  `/nix/store/a08msf5g6062f0hwwdhnkmahmizqgkdb-sqlite-verifier-predictions` (identical to
  `build/predictions-a2`, the 55-file baseline).
- 2026-10-26, part 1, stage (b): INSERT from a query gets its possible executions through the
  `StatementExecution` interface.
  - Model: `Resolved.Query.productions` gives one production for each order in which SQLite may
    read the source (`Table.accessOrders`: the scan, then each index), or one for a total ORDER BY;
    `insertSelectRun` runs the first as the statement's own run and the others as
    `StatementRun.alternatives`. A statement with rules (a trigger or an enforced foreign key) is
    described for one production only. A source error after rows that all succeed ends the statement
    and keeps no row (also with OR FAIL); streaming against collecting only changes
    `last_insert_rowid()`. The transfer optimization is a candidate only for a query whose result
    columns are the columns of the source in order (a new conjunct; `abs(x)` is no candidate).
    `statementOutput` gives a failed INSERT from a query with a source failure its RETURNING names,
    no rows and the changes of its run. The laws moved: `InsertSelectLaws` (141 lines) and
    `InsertSelectOutcomeLaws` (183 lines); the examples are `InsertSelectExamples` and
    `InsertSelectTransferExamples`.
  - Native facts (SQLite 3.51.0): the recorder's `check_write_window` reads the whole source before
    a limited write, so a LIMIT write whose uncut source fails cannot be recorded; the Lean examples
    keep that case (`limitedCopy`).
  - Conformance: `conformance/authored_insert_queries.py` (62 cases, version 7 records, which run on
    after an error and hold the counters; a version 5 record uses the halting classifier, which
    knows one execution only). 55 agree. 7 stay unmodeled, with kernel proofs of the boundary:
    GROUP BY, compounds, ORDER BY over a source that may fail (2), the transfer optimization (2)
    and a trigger with a source that has two orders. `tests/conformance_insert_queries_test.py`
    checks the verdicts natively and in the kernel. No case disagrees.
  - Mutants: `conformance/insert_query_mutants.py` (9 mutants: scan order only, alternatives dropped,
    always streams, always collects, RETURNING does not collect, transfer rowids ignored, transfer
    takes any projection, rules with two orders, source failure has no output), all killed by
    `tests/conformance_insert_query_mutants_test.py` (run by name); guards checked by
    `tests/mutant_guards_test.py`. One planned mutant (`any trigger collects`) is equivalent:
    ON CONFLICT DO UPDATE on a table with a trigger is refused, so no update program reaches the
    source analysis. The modules are in `build-support/tests.nix` and the tests in
    `tests/nix_suites.json` (entries only).
  - Surface: `tests/surface/InsertSelectExecutions.lean` (5 checks over `decide +kernel`), in
    `tests/surface_execution_test.py`.
  - Predictions (Nix, `build/predictions-b2`, same as b1): the 55 files compared with the baseline: 42
    cases go from unsupported (`query-source-insert`) to predicted; 6 are unsupported with another
    reason (3 `row-dependent-key`, 2 `trigger-form`, 1 `alias-in-expression`); no predicted case
    changed.
  - Proof repairs by hand in this stage: about 75 in total so far.
  - Scope notes for the report: the stage touches run-law and belay surface law files of the
    possible-executions task (single premises on `Succeeds.script_iff`, `branch_shape` and others);
    the authored corpus freeze (corpus numbers, the Nix corpus list, evidence writers, the lock) is
    for the judge PR and is not done here.
  - Review of stage (b), round 1 (`20261026T195228Z-408913ec`: 8 musts, 1 should; the test commit
    `20261026T194601Z-f9c925f6`: 1 should), all fixed in the `refactor:` commit that follows:
    a source fault is no described production (`productionOver` returns none for it), a window
    parameter is bound before `scansRows` is asked, `last_insert_rowid()` in an INSERT from a query
    is the restriction `connectionCounterRead` (the counter changes with each streamed row), the
    catch-all cases of `fromQuery`, `isInsertSelect`, `scansRows` and `cellsOf` list their
    constructors, the docs of the three run-law restatements and the proof sketch of
    `runScriptStepFailure_continued` say what they cover, the `Scope.ownSources` rule has checked
    examples (`SubqueryResolutionExamples`), and the new or grown files are split under 200 lines
    (`ResolveStatementSingle*`, `ScriptRunContinued`, `ScriptRunPositions`, `StepCatalogLiteral`,
    `ScriptRunResolved`, `ScopeOwn`, and `insert_query_setups.py`). New checked examples:
    `InsertSelectSourceFaultExamples`.
  - `Sql.branch_continued_iff` takes the proof that the step has no further execution as a last
    argument with the default `by rfl`, so the surface fixtures that name a step with `[]` stay as
    they were; its four package call sites and one fixture (`ExecutionEquivalence`) follow the
    argument order. The surface fixtures of the execution and the migration patterns suites compile
    (no `sorryAx`). Proof repairs by hand: about 80 in total.
  - `just test-full` (test-source) found that `InsertSelectRun` imported the resolver
    (`SubqueryResolution`) for `Query.readsTable`, which put `Lean.Meta` into the import closure of
    the model laws (`tests/test_model_ownership.py`). `Query.readsTable` moved to `QueryForm`.
  - `just test-full` (restriction examples) found that the restriction `query-source-insert` was
    reached by no text any more: the frontend refuses INSERT from a query in a trigger body before
    the model sees it, and a statement INSERT from a query is described. The registry must not keep
    a restriction that no SQL reaches (`tests/conformance_restriction_examples_test.py`), so the
    restriction is retired (constructor, text, registry map, documentation row, example); the form
    of a trigger body that a body statement cannot have stays `trigger-form`. The refusal that
    users see is the frontend's: "Only VALUES rows are modeled as an INSERT source".
  - `just test-full` (test-model, mutants) found that the production mutants did not carry
    `InsertSelectRun` although `StatementStep` calls it; `conformance/mutation_check.py` now copies it.
  - `just test-full` (surface) found fixtures that name every resolved statement or use the laws whose
    premises changed: `ClaimsViewCatalog`, `ViewsSupport` and `ClaimsCommonTables` list the arm
    `insertSelect`; `SuccessUniqueEmail` needs the absent name for the own sources of the scope;
    `S6WpSoundness` takes the first execution of a step that may have further ones; `AddCustomerClaims`
    uses the new law `runScriptStep_select_others` (a SELECT has one next state) and the premise of
    `check_send_single_of_step`; `ExpansionCountClaims` gives the condition of
    `Sql.succeedsFrom_sendStatements` from `expansion_noInsertSelect`. Proof repairs by hand: about 87
    in total, above the line of 80 that asks for a stop; the report flags this.
  - Reviews: `20261026T213513Z-7de3cfdd` (mutant file list) and `20261026T213607Z-769be6ba` (surface
    fixtures and `runScriptStep_select_others`): no findings.
  - `just test-full` (test-model, mutants, run 4) found that the Nix inputs of the model suites did not
    carry `InsertSelectRun.lean`, which the production mutants read; `build-support/tests.nix` lists it
    with the other run files. The local run reads the whole tree, so only the Nix run shows this.
  - Review `20261026T215351Z-9b4e3a73` (Nix inputs of the model suites): no findings.
  - `just test-full` (surface, run 5) found that `tests/success_theorems_test.py` restates
    `Succeeds.script_iff` without its premise (no statement is an INSERT from a query); the restated
    law takes the premise. Everything else of the run passed (375 surface tests, all other suites).
  - Review `20261026T221012Z-ecb46ac9` (success theorem test): no findings. `just test-full` (run 6) passes
    in Nix: all test suites, surface suite 376 passed. Next: `just verdict`.
  - Stage (b) gates in Nix: `just test-full` passes (run 6) and `just verdict` passes (no DISAGREE;
    the 55-file predictions baseline holds). The manual proof repair count is about 87, over the line of
    80, so work stops here for a report to the coordinator before part 2 (renames).

### Merge of S6 automation part 1 (PR #277)

- Merged `tasks/s6-automation-part1@origin` (96dc386f) into the head of stage (b) with a merge commit.
  Conflicts: `packages/belay-sqlite-model/lakefile.toml` (modules of both sides kept) and
  `DuplicateKeyResolution.lean` (the generalized `Query.duplicateKeys` of #275 kept; the theorem
  `resolveQueryBody_duplicateKeys` takes the premise `scope.ownSources = scope`, given by `ownTable` for
  the table scope).
- The new S6 files used laws whose premises stage (b) changed. Repairs, with general statements:
  - Model: `Resolved.Statement.plainWriteTarget` has no target for `insertSelect`;
    `runScriptStep_plainWrite_frame` and `runScriptStep_readOnly_keeps` read the new shape of
    `runScriptStep_continued_spec` and give `runScriptStep_others` the premise `fromQuery = false`.
  - Belay: `Sql.Frame.sendStatements_sheltered` takes the shelter step's `others = []`;
    `ReadAnalysis.analyze` answers `notQuery` for `insertSelect`; `Sql.ifOk_send_plainUpdate` and
    `Sql.ifOk_send_addColumn` give the single-execution premise as `Sql.ifOk_send_plainInsert` does;
    new `ReadCertificate.Obligations.single_original` and `single_other` (a certified statement
    resolves to a query); `ReadCertificate.preservesAt_send` and `commutesOn_send` take
    `∀ entry ∈ script.statements, entry.1.isInsertSelect = false`.
  - Fixtures: `S6RulesEffects` gives the premise of `check_send_single_of_step`; `S6RulesQueryPattern`
    proves `expansion_single` by kernel evaluation and passes it.
- Proof repairs by hand in this merge: about 16 (about 103 in total).
- Checks on the merged tree: model, belay, translator and conformance-runner builds pass, `just dev-build`
  passes, `tests/surface_s6_rules_test.py` and the surface tests of the files above pass.
- Reviews: `20261026T225245Z-1e62c949` (2 musts about docstrings in `ReadCertificate.lean` and
  `CertifiedQueryCommutation.lean`, both fixed in `refactor: answer the review of the merge ...`) and
  `20261026T225449Z-307b2940` (no findings).
- Gates on the merged tree in Nix: `just test-full` passes (surface suite 383 passed, all other suites
  pass), output `/nix/store/wg3i1d06xiy3lmkkldsi47cx254ny809-sqlite-verifier-test-reports`;
  `just verdict` passes with no DISAGREE, output
  `/nix/store/3lqr3pxr2xk5gbfdmbzwfr8rg1al1dpm-sqlite-verifier-verdict`, predictions
  `/nix/store/07yg9qqpjvv7z1kznsqsbw5hzqfv6ysh-sqlite-verifier-predictions` (identical to `build/predictions-b3`).

### Part 2, unit 2.1: rename syntax, SQLite-ordered prepare errors, temporary restriction

- New syntax `Statement.renameTable table newName` and `Statement.renameColumn table column newName
  columnToken quoted` (`columnToken` is the old column name as written, `quoted` tells whether the new name
  was written with a quote). The translator `Translation/Renames.lean` maps the two productions (an
  unqualified table name only); `ALTER TABLE ... DROP COLUMN` stays unsupported until part 3.
- `Resolution/Renames.lean`: `resolveRenameTable` and `resolveRenameColumn` give the prepare errors in the order
  that native SQLite 3.51.0 gives them (probes in the task file): no such table; new name taken
  (`renameTargetTaken`); system table; reserved new name; view (`viewNotAltered` for RENAME TO,
  `viewColumnsNotRenamed` for RENAME COLUMN); no such column (`renameNoSuchColumn` prints the token as written).
  A rename that passes all checks is the new restriction `alter-rename` until unit 2.5 models the rewrite.
- Laws in `Resolution/RenameSpec.lean` (catalog unchanged, a step of `CatalogStep.same`); the new arms of the
  spec files (`NamesSpec`, `ResolveStateSpec`, `ResolveStatementValid`, `ResolveStatementFacts`,
  `ResolveStatementSingle`, `TransactionSpec`) use them. Exhaustive-match arms in the editor modules of
  `packages/belay` (`SqlTableSlots`, `SqlStatementContexts`, `SqlOrderWarnings`, `SqlTableOrigins`) and
  `SampleScriptHints` are the minimal ones; `SqlTableSlots` gives the two statements the slot of their table.
- Tests: `RenameExamples.lean` (`#guard` checks of the error order and the restriction),
  `tests/syntax_mapping_test.py`, `conformance/restriction_examples.py` (example of `alter-rename`),
  `tests/surface/DbBangErrors.lean` (the message that lists the modeled statements).
- Checks: Nix results are recorded at the end of part 2. Manual proof repairs in this unit: 0 (new cases only).

### Part 2, unit 2.2: the text of a CHECK constraint keeps its name tokens

- `Syntax.ColumnConstraint.check` and `TableConstraint.check` take the trimmed source text of the condition with
  the places of its name tokens (`text : SourceText`, empty for a constraint with a `CONSTRAINT name`). The
  translator records them for every unnamed CHECK (`Translation/Constraints.lean`, `NameTokens.lean`).
- `CheckConstraint.source : Option CheckText` keeps that text and the tokens that the resolver bound to the
  table (`LabelTarget.table`, a qualifier) or to a column position (`LabelTarget.column`). The binding is read
  from the occurrences of `resolveOperandTraced` by the node paths of the tokens (`checkText` in
  `Resolution/TableChecks.lean`); there is no second lookup of a spelling. The label that execution reports is
  unchanged, so the rename of unit 2.5 rewrites `source` and the dequoted label together.
- Tests: `Resolution/CheckTextExamples.lean` (`#guard` checks), `tests/syntax_constraints_test.py`.

### Part 2, unit 2.3: the names of a trigger program are traced

- The trigger gap of the name trace is closed. `resolveProgramTraced` (`Resolution/TriggerPrograms.lean`)
  records the names of the WHEN condition below the path `[5]` and those of the body statement `k` below
  `[6, k]`: the fields of a trigger statement are name, IF NOT EXISTS, time, event, table, condition, body.
  A body statement uses the field numbers of the statement of the same name (`Statement.insert` and
  `Statement.update` have a RETURNING field that a body lacks; a body SELECT has no compound). The
  resolvers `resolveBodyStatement`, `resolveRaiseSelect`, `resolveBodySelect` and `resolveProgram` are the
  `.drop` of their traced forms (`TriggerBodies.lean`, `TriggerStatements.lean`, `TriggerPrograms.lean`), so the
  trace and the resolved program cannot disagree. `triggerEvent` moved to `TriggerPrograms.lean`.
- A write to a view in a body decides no name (it is a prepare error); the rename of unit 2.5 handles it.
  A raising SELECT keeps the operands of its CASE in place; the message of a RAISE is resolved as an extra result column, and
  its names move back to the message in the written column (`raiseMessagePaths`, `moveToMessage`); the message is the child 1 of a RAISE.
- Tests: `Resolution/TriggerTraceExamples.lean` (`#guard` checks of the paths of a program and of a raising
  SELECT); the existing `TriggerProgramExamples.lean` still passes, and so do `tests/syntax_triggers_test.py`
  and the trigger tests of the conformance suites.
- Review of unit 2.2: `20261027T004253Z-27fd1515` (2 musts and 1 should, all fixed in the refactor commit). Review of unit 2.3:
  `20261027T010453Z-47a210a9` (1 must: the names of the message of a RAISE had the path of the extra column; fixed in unit 2.4's
  refactor commit).
- Manual proof repairs in this unit: 0.

### Part 2, unit 2.4: replace a name of an object by its trace path

- `Resolution/RewriteEdit.lean` (`NameEdit`: path, old name, new name, `RenameStyle`; the quote rule of SQLite for
  `RENAME TO` and `RENAME COLUMN`), `RewriteExpr.lean` (`Expr.renameAt`), `RewriteQuery.lean` (`TableReference`,
  `ResultColumn`, `Join`, `Subquery`), `RewriteText.lean` (`SourceText.replaceTokens`, `SourceText.renameAt`: the
  bytes of the name tokens that have the path of the edit, with the tokens behind them moved), `RewriteSelect.lean`
  (`renameSelectAt`: query and subqueries of a statement, with the texts of the result columns) and
  `RewriteBody.lean` (`BodyStatement.renameAt`, `CatalogTrigger.renameAt`). Every function takes the path of a
  name occurrence of the name trace and gives none when the path does not lead to the old name, so a layout
  that the engine does not know is a failure of the rewrite, never a silent change of another name.
- Tests: `Resolution/RewriteExamples.lean` checks, for samples that cover every expression form, the clauses of a
  query, subqueries, the program of a trigger and a raising SELECT, that the rewrite works at the path of every
  occurrence that a rename rewrites and that the trace of the rewritten object has the new name at that path;
  and the rewrite of the text of a result column (quote rule; the start and stop of every token after an edit, and a
  second edit that reads the tokens of the first).
- Not covered yet (restricted by the guard of the path, decided in unit 2.5): names in the arguments of a
  table-valued function, ON CONFLICT targets, and USING names (to be probed against native SQLite).
- Manual proof repairs in this unit: 0.

### Unit 2.5a: the trace tells an aliased source

- `SourceRef.aliased` and `ScopeSource.aliased` (default false) tell whether the `FROM` item has an alias. A rename of
  a table renames a qualifier that names the table and keeps a qualifier that names an alias (native SQLite 3.51.0:
  `select t.a from t as t` stays `t.a`, with `FROM "u" as t`). `tableScope` and the table reference set the flag;
  `Scope.singleAt` takes it as a last argument with the default false.
- Tests: `NameTraceSourceExamples.lean` checks the flag for a table with and without an alias.
- Manual proof repairs in this unit: 7 (the single-source laws and the normalized-field lookup laws gained an
  `aliased` argument; one call site passes `aliased := false`). Total for the task so far: about 110.

### Unit 2.5b: the catalog after a rename

- `Resolution/RenameEdits.lean`: `RenameRequest.decide` reads the trace of a view or trigger and gives, for each
  occurrence, keep, an edit, or a restriction. A table rename edits a table reference or a qualifier that names the
  base table itself, never a qualifier that names an alias. A column rename edits a name whose one binding is the
  column; a name that a join merged is the restriction `alter-rename`. Names inside another stored view are not exact
  and keep their spelling. The rows `NEW` and `OLD` of a trigger have `role := .triggerRow`, so a trigger on the
  renamed table is told from a trigger on another table.
- `Resolution/RenameChecks.lean`: `CheckText.rename`, `CheckConstraint.rename` and `dequoteLabel` (SQLite's
  `sqlite3Dequote`): the text of an unnamed CHECK constraint is rewritten token by token and its label is the
  dequoted new text. `Resolution/RenameTables.lean`: the changes in a table (name of the column, foreign key parent
  and referenced names, CHECK texts). `Resolution/RenameDependents.lean`: `renameView`, `renameTrigger`
  (header: trigger table, `UPDATE OF` names), `checkView`, `checkTrigger`, `RenameFailure`.
  `Resolution/RenameCatalog.lean`: `renameCatalog` in the two passes of SQLite 3.51.0: pass 1 rewrites every
  object and fails with `error in view v: ...` (native: a runtime error of the statement, a prepare error of the
  model with no effect); pass 2 resolves every object of the new catalog (`error in view v after rename: ...`,
  `error in table t after rename: duplicate column name: b`); last the catalog must be supported under the limits.
- `PrepareError.dependentObject kind name afterRename error` with `DependentKind` (messages, JSON, names).
- Native facts (SQLite 3.51.0): a rename fails when any view or trigger of the catalog does not resolve, also one that
  does not read the renamed table; a rename of a column to the name of another gives
  `error in table t after rename: duplicate column name: b` (the name of the later column); a column may be renamed
  to `rowid`.
- Tests: `RenameEditExamples.lean` (view and trigger edits), `RenameChecksExamples.lean` (labels, tokens, dequote).
  The catalog functions are tested through the statement in unit 2.5c.
- Manual proof repairs in this unit: 0.

### Unit 2.5c: the rewrite statement and its preservation proofs

- `Resolved.Statement.rewrite (catalog : Catalog)` is the resolved form of a rename: the resolver computes the whole
  new catalog (`renameCatalog`), the statement replaces the catalog and leaves the rows as they are. `applyCatalog
  (.rewrite renamed) _ = renamed`; the new statement kind is `Statement.Kind.rewrite` (not a control statement).
- Execution: `step` stores the new catalog only when `Catalog.keepsOutline` holds for the old and the new catalog, else
  it fails with `.unmodeled` and the input database. The test is a runtime guard on purpose: every preservation proof
  follows from the guard, so no proof depends on the resolver. That the resolver passes the guard is a test, not a
  theorem (examples in unit 2.5d and the differential matrix).
- `Resolution/CatalogOutline.lean`: `Catalog.outline` (each object with `blankNames`: no column names, no CHECK
  labels or sources, no foreign key parent names), `Catalog.selectedParents` (parent link of every foreign key of
  every table), `Catalog.keepsOutline`. Laws for tables: `OutlineTableLaws.lean` (NOT NULL, types, CHECKs),
  `OutlineDatabaseLaws.lean` (each row-local and table atom), `OutlineKeyLaws.lean` (unique keys),
  `OutlineForeignKeyLaws.lean` and `OutlineSelectedParentLaws.lean` (foreign key facts for the selected mapping:
  `Database.RowReferencesHold.of_outline`, `Database.ParentSchemasCompatible.of_outline`).
- `StatementRewrite.lean`: `runStatement_rewrite_satisfies` and the row-local and table-atom instances. The atom
  classes `RowLocalAtom` and `TableAtom` gained a field `renamed` (same rows and shape after `blankNames` keep the
  atom). Every statement theorem of the matrix (Admitted/Valid atoms, unique keys, FK rows and selected mapping) has
  an arm for `.rewrite`: Valid-catalog takes the `next` hypothesis as for CREATE; the fixed-mapping FK law
  (`KeepsParentSchema`) is False for a rewrite, the selected-mapping laws hold with no condition.
- `step_extends` (PreservationLaws) excludes the rewrite (a rename changes names, so the new catalog does not extend
  the old one); its caller derives that from the statement kind.
- The belay package needed two `.rewrite _` arms (`ReadAnalysis`, `DbDiagnostics`); no editor module changed.
- Review of 2.5b (`20261027T015742Z-0a7f0813`): three musts, to fix in the next units: R7 (trigger execution checks
  must not be rename errors: use the rename-specific name validation in `renameTrigger` and `checkTrigger`), R19
  (SQLite's `renameFixQuotes` literal normalization is not implemented: a double-quoted string that becomes a column
  name after a rename; documented here as incomplete until implemented), R11 (direct catalog tests).
- Manual proof repairs in this unit: about 12 (case arms with a real proof, in `step_extends`, the `StepCatalog`
  laws, the FK matrix and the key laws). New proofs: about 30 small laws in the Outline modules. Total for the task
  so far: about 122.

### Unit 2.5d: the rename resolver produces the rewrite

- `resolveRenameTable` and `resolveRenameColumn` keep their check order and then call `finishRename`: `renameCatalog`
  gives the new catalog, and the statement is `.rewrite renamed`. A failure of `renameCatalog` is a prepare error
  with the catalog unchanged, or a restriction (`alter-rename`). `RenameSpec.lean` proves the outcome: either a
  prepare error with the catalog unchanged, or a rewrite whose catalog is `supported` (so it is a valid catalog).
- Review musts of 2.5b: R7 is fixed by `RenameVerdict.lean`: only the name-resolution class of errors that native
  SQLite raises during a rename (no such column or table, ambiguous names, JOIN USING and NATURAL checks, HAVING and
  GROUP BY aggregate checks, compound shape) is a rename error; every other check of a trigger or view body that
  fails is a restriction, because native SQLite accepts the rename. This is a deviation from the first plan, where
  every prepare error was a rename error. A recursive term with an aggregate is no rename error (SQLite accepts the
  rename; `CommonTableError.raisedByRename`). R19 is fixed: a double-quoted string that is not a name becomes the
  literal `'z'` in the views and triggers of a column rename (`NameEdit.fixQuote`, same as native `renameQuotefix`),
  also in the text that names an unaliased view column (`SourceText.renameAt`); a table rename leaves it as
  written (checked natively); a column rename of a table with such a text in a CHECK is a restriction. R11 is fixed
  by `RenameCatalogExamples.lean` and `RenameFailureExamples.lean` (compiled-evaluator `#guard` checks of the new
  catalog, errors of pass 1 and pass 2).
- Phase of dependent-object errors: SQLite reports `error in view v ...` and `error in table t after rename ...`
  while the statement runs (`sqlite3_step`), checked natively; `PrepareError.reportedWhileRunning` is true for
  `dependentObject` only and `VerifierConformance.errorPhase` gives `step` for it. The other rename errors (no such
  table or column, target taken) are prepare errors.
- Conformance: `conformance/authored_renames.py` (51 cases, version 7 records; setups in `rename_setups.py`) and
  `tests/conformance_renames_test.py`: the judge's verdict of every case through the predict command (views and
  triggers included) is AGREE except 4 cases that stay unmodeled (a recursive aggregate in a view, a CHECK with a loose quote
  in a column rename, a self-join with USING in a view, and a schema-qualified table name that the translation refuses), and the kernel proves the cases without views. The
  cases include the dependent-object failures and their `step` phase. No case disagrees. The corpus freeze (corpus
  number, evidence writer, lock) is for the judge PR.
- Review musts of 2.5c: R2 and R13 are docstring changes (errors other than success and `constraintFail` put no
  obligation on the database; `Statement.applyCatalog` returns the supplied catalog for a rewrite). R11 is fixed by
  `rewritesAndRuns` (a rename resolves to a rewrite and the run succeeds with the same rows) and
  `rejectedRewriteKeepsDatabase` (an outline mismatch fails as `.unmodeled` with the input database).
- The restriction `alter-rename` is narrower: its text, `docs/semantic-subset.md` and the conformance example
  (a view with a USING-merged column) changed. Nix results for this unit come with the part 2 `just test-full`.
- Manual proof repairs in this unit: 0 new (the outcome lemmas are short). Total for the task so far: about 122.

### Unit 2.6: contracts, mutants and surface checks of the renames

- Narrow contracts for S6 (`StatementRewrite.lean`): `step_rewrite_of_keeps` (the run succeeds and stores the catalog with the
  rows of the database), `step_rewrite_of_not_keeps` (it fails as `.unmodeled` with the input database) and
  `step_rewrite_ok` (what a successful run says: the catalog of the rewrite, the rows of the database, the guard).
  A client unfolds nothing of `step`.
- Mutants: `conformance/rename_mutants.py` (8 mutants: parent column and parent table not followed, duplicate column
  unchecked, dependent error in the prepare phase, taken name ignored, table keeps its old name, rewrite always
  rejected, rewrite loses rows), all killed by `tests/conformance_rename_mutants_test.py` (run by name, 8 passed);
  guards checked by `tests/mutant_guards_test.py`. The modules are in `build-support/tests.nix` and the tests in
  `tests/nix_suites.json` (entries only).
- Surface: `tests/surface/RenameExecutions.lean` (5 checks over `decide +kernel`: the new names succeed, the rows
  and rowids are kept, the old names and a taken name fail), in `tests/surface_execution_test.py`.
- `docs/semantic-subset.md` lists the two ALTER forms and the narrowed restriction `alter-rename`.
- Reviews: `20261027T025920Z-40b1a98e` (2 musts, both fixed in the commit that follows it and a `refactor:` commit:
  the recursive aggregate, the quotefix of the text of a view column, and exhaustive matches); the refactor commit
  `20261027T033625Z-bd168538` has no findings.
- Manual proof repairs in this unit: 0. Total for the task so far: about 122.

### Unit 2.7: renames stay out of scope for records without a profile

- The first part-2 `just verdict` found four DISAGREE cases in the corpora v1 to v3: `alterlegacy-1.2:2`, `1.3:5`,
  `4.1b:22` and `9.3:43`. Their setup turns `PRAGMA legacy_alter_table` on, which the subject cannot see in a record of
  version 1 (no profile), and the model implements only the default (off). The same situation exists for foreign
  keys (ADR 0014, slice 4), so the fix follows that rule: `conformance/profile_scope.legacy_alter_scope` makes a
  rename in a record without a profile UNSUPPORTED; `conformance/predict.py` and `conformance/native_replay.py` call it
  next to `foreign_key_scope`. Profiled records (version 4 and later) cannot change the setting (the recorder refuses
  the pragma), so the authored rename cases are unaffected.
- Tests: `tests/profile_scope_test.py` (rename forms found; unprofiled records with a rename are out of scope;
  profiled records and records without a rename stay in scope).
- Manual proof repairs in this unit: 0. Total for the task so far: about 122.
- Reviews: `20261027T040327Z-cf19e736` and `20261027T041119Z-f7b3be39` have no findings; `20261027T040944Z-5b83c434`
  (2 shoulds: the message names the next action; the test docstrings name the code under test) both fixed in
  `f7b3be39`.
- Nix verdict after the fix: `just verdict` passes with no DISAGREE. Of the 55 prediction files, those of corpora v1 to
  v5 differ from the baseline only in newly supported cases (149 cases go from unsupported to predicted, none
  changes otherwise).

### Unit 2.8: surface fixtures know the rewrite statement

- The second `just test-full` (pre-fix tree) failed in `surfaceChecks` and `surface` (the first one stopped earlier at the
  documentation inventory, so these were not visible): the fixtures `ViewsSupport`, `ClaimsViewCatalog`,
  `ClaimsCommonTables` and `ClaimsViewTriggers` match all statement forms and lacked arms for `Resolved.Statement.rewrite`
  and `Syntax.Statement.renameTable` / `renameColumn`. The arms were added (these are exhaustive-match arms, not new
  tests); `tests/surface_claims_test.py` and `tests/surface_views_test.py` pass.
- `surface_sampling_test` and `surface_search_test` timed out in that run only because three Nix test runs shared the
  machine (alone they take 55 s and 86 s; their own command limits are 180 s for the sampling test and 90 s and 240 s
  for the search test); they pass alone.
- The third `just test-full` found one more fixture break: `tests/surface/GlobalSignupInvariant.lean` called
  `NormalizedField.resolveColumns_identifier_at`, which got the argument `aliased` in the rename work; the call passes
  `_` for it.
- Manual proof repairs in this unit: 0. Total for the task so far: about 122.

### Part 2 gates (Nix)

- `just test-full` passes on the final part-2 tree (after the fixes of units 2.7 and 2.8):
  `/nix/store/wxpcysk9684lwnsz5ynmwcx9wj6vns5x-sqlite-verifier-test-reports`.
- `just verdict` passes with no DISAGREE: `/nix/store/8n6csifr50qkrah6l7l13xvxnq2hcv17-sqlite-verifier-verdict`
  (AGREE 5318, MODEL_UNSUPPORTED 2282).
- Change of the verdict from part 1 (#278, `/nix/store/3lqr3pxr2xk5gbfdmbzwfr8rg1al1dpm-sqlite-verifier-verdict`) to
  part 2: 106 cases go from MODEL_UNSUPPORTED to AGREE, and nothing else changes (the coordinator's comparison of the two
  verdicts). The 149 cases that I counted earlier were the prediction files compared with the baseline taken before
  the task started, so they include the gains of part 1 and were counted before the `legacy_alter_table` scope fix of
  unit 2.7; the 106 is the figure for part 2.
- Reviews of the last commits: `20261027T041119Z-f7b3be39` and `20261027T050120Z-e548dbb3` have no findings.
- Part 2 is complete (PR #279, bookmark `tasks/table-rebuild-part2` at fa4ec661). Part 3 (DROP COLUMN and the
  integrated rebuild coverage) starts next.

## Part 3: DROP COLUMN and the integrated rebuild coverage

### Unit 3.1: the DROP COLUMN statement form, still a restriction

- `Syntax.Statement.dropColumn table column columnToken` (path 0 table, path 1 column); the translator maps
  `ALTER TABLE fullname DROP kwcolumn_opt nm` (`Translation/Renames.lean`, `Statements.lean`); a schema name before the
  table is still refused. The "not modeled" message now lists ALTER TABLE DROP COLUMN (the golden text in
  `tests/surface/DbBangErrors.lean` follows; this is a change of an existing expected text, flagged to `main`).
- The new restriction `alter-drop` (`RestrictionKind.alterDrop`, text, registry, `docs/semantic-subset.md`, conformance
  example) is what `resolveDropColumn` returns for every input in this unit; `resolveDropColumn_no_success` lets the
  catalog-level laws (`NamesSpec`, `ResolveStateSpec`, `ResolveStatementValid/Facts/Single`) cover the form. Later units
  replace the placeholder and these arms.
- Exhaustive matches over `Syntax.Statement` got a `.dropColumn ..` arm, among them the editor modules of
  `packages/belay` (`SqlTableSlots` treats the table as path 0 like ADD COLUMN; the others list it with the other ALTER
  forms). This is the same minimal-arm deviation as in part 2.
- Tests: `tests/syntax_mapping_test.py` (DROP COLUMN mapping with and without COLUMN, quoted names and tokens; the
  schema-qualified form is refused); the refusal case that used DROP COLUMN as an unmodeled form is gone.
- Manual proof repairs in this unit: 0. Total for the task so far: about 122.

### Unit 3.2: facts about the text of a definition

- SQLite keeps the text of a table and of an index, and prints a name of that text as written when the text no longer
  resolves after DROP COLUMN. The model keeps no text for generated columns, table-level keys, foreign keys and
  indexes, so the catalog now records the facts that the error spelling needs: `CatalogTable.inlineUnique` (columns
  with a UNIQUE column constraint, because SQLite refuses to drop only those), `CatalogTable.exactNames` and
  `CatalogIndex.exactNames` (the text spells every column as declared, with no double quote), and
  `CatalogTable.quotedRename` (a quoted column rename wrote a quoted name into the text). `Resolution/SpelledNames.lean`
  computes them at CREATE TABLE (`CatalogTable.withSpelling`) and CREATE INDEX; `blankNames` resets `quotedRename`, so
  the outline of a table does not change.
- `statisticsTable` moved to `Resolution/StatisticsTables.lean` to keep `Definitions.lean` under 200 lines.
- Proof repairs (3 manual): `CatalogTable.supported_withSpelling` (new, by `rfl`) and the three `createTable` validity
  theorems now speak of the table with its spelling; `Catalog.Valid.createIndex` takes the `exactNames` flag;
  `CreateIndexSuccessLaws` states the index with its flag. One `#guard` of `Examples.lean` got `inlineUnique := [0]`.
- Tests: `Resolution/SpelledNamesExamples.lean` (compiled-evaluator `#guard` checks of the facts at CREATE TABLE,
  CREATE INDEX and the quoted column rename).
- Manual proof repairs in this unit: 3. Total for the task so far: about 125.

### Units 3.3 to 3.6: the DROP COLUMN model, its laws and the contracts (one commit)

- Statement form `Resolved.Statement.dropColumn table index stored` (kind `.rewrite`; `stored` is the catalog that
  the resolver computed). `Database.runsDropColumn` holds when `Catalog.droppable` accepts the drop and the stored
  catalog has the outline of the catalog after the drop (`Catalog.dropColumn`); the step then stores the catalog and
  removes the cell of every row (`Database.dropColumn`, `Row.dropValue`), keeps the rowids and the table order, and
  otherwise fails with `ExecutionError.unmodeled` and the input database (the same shape as the rename step).
- `Catalog.droppable` (Resolution/ColumnDropCatalog, ColumnDropSpec): the column is no PRIMARY KEY, no UNIQUE, no key
  column, no column of an index definition, no alias of the rowid, not read by a generated column or by a CHECK of
  another column, not named by a foreign key of the table, and no table has a foreign key to the table (the model
  restricts this case; see the open items). `CatalogTable.DropsCleanly` is the structure of the table-side facts, and
  `Catalog.droppable_spec` gives it back. The columns whose constraints the dropped column owns alone (a CHECK that
  reads only that column, a column-level constraint) are not dependencies: `CatalogTable.checksAfterDrop` removes
  them, and `CatalogTable.allChecks_dropColumnAt` shows what remains.
- Laws in new files (all under 200 lines): expression and key rewrite (`ColumnDropExpr*`, `ColumnDropKeys`,
  `ColumnDropKeyLaws`, `ColumnDropTable`), cells (`DropColumnCellLaws`), per-fact table laws (`DropColumnFactLaws`,
  `DropColumnKeyLaws`), the transport through the database (`DropColumnDatabaseLaws`: `Database.table_dropColumn`,
  `runsDropColumn_spec`, `Database.EveryTable.dropColumn`), Admitted and Valid facts for the run
  (`DropColumnAdmittedLaws`, `DropColumnValidLaws`), and the foreign key part: parent invariance and child positions
  (`ColumnDropParent*Laws`, `ColumnDropParentChildren`), mapped keys (`ColumnDropParentMapLaws`), link transport
  (`DropColumnLinkLaws`, `DropColumnReferenceLaws`), and `RowReferencesHold` / `ParentSchemasCompatible` for the run
  (`DropColumnForeignFacts`). The statement contracts are in `StatementDropColumn`.
- Contracts: `runStatement_dropColumn_satisfies` (any property that the run keeps; the failing run keeps the
  database) and `runStatement_dropColumn_eachTable`. The clients (`runStatement_rowidsDistinct` and its siblings,
  `runStatement_keysUnique`, `runStatement_catalogSupported`, `runStatement_rowReferences`,
  `runStatement_parentSchemasCompatibleSelected`, `runStatement_foreignKeyAtomsSelected`, the Admitted/ValidAtoms
  theorems) add one arm each and do not unfold the run. The exception is `literalStep_success_catalog`: its new arm
  unfolds `literalStep`, `runStatement` and `step`, because that theorem reads the stored catalog of the run itself. `ForeignKeyRowsCondition`,
  `ForeignKeySchemaCondition` and `ForeignKeyAtomsCondition` are `True` for the new form, with a bullet that says why:
  the run stores a catalog only when it keeps the outline and the selected parents of the catalog after the drop, and
  `Catalog.droppable` refuses the columns that a foreign key names.
- Shared structures changed: `RowLocalAtom` and `TableAtom` gained the field `dropped` (a table that has the atom and
  loses a column cleanly still has it). Every instance discharges it from the new per-fact laws. This affects the S6
  automation agent only where it builds a new instance of these structures; told to `main` in the report.
- The review of unit 3.2 (`20261027T061435Z-1d272086`): one must (the docstring of `Catalog.Valid.createTable` now
  names the spelling metadata) and one should (the two `#guard` matches list every `CatalogEntry` constructor); both
  fixed.
- Placement of the arms in the packages `belay` (`ReadAnalysis`, `DbDiagnostics`): minimal exhaustive-match arms only.
- Manual proof repairs in this unit: about 30 (new arms in the existing statement theorems and their helpers, and the
  seven new `dropped` fields). Total for the task so far: about 155.

#### Generalization analysis (owner rule of 2026-10-27)

For each new public statement: the general form chosen, and what stays specific.

- `Catalog.find_mapIdx`: general (any change of the objects that keeps names and kinds); `Catalog.find_dropColumn` is
  an instance. Other lemmas of `ColumnDropParentLaws` (`parentIndexes_dropColumn_other`, `parentLink_dropColumn`) stay
  specific to `CatalogObject.dropColumn`: their proofs read the fact that tables and indexes at other positions are
  unchanged, which a general rewrite statement would need as one more premise per use; no second client exists.
- `ParentKey.mapChildren`, `ParentLink.mapChildren`, `ForeignKey.mapColumns`, `matchIndex_mapColumns`,
  `primaryKey_zip_mapColumns`, `Catalog.parentKey_mapColumns`, `Catalog.parentLink_mapColumns`,
  `ForeignKeyLink.satisfied_mapChildren`, `indexHolds_mapChildren`, `childValues_mapChildren`,
  `parentFound_mapChildren`: general in the column move (any function on positions; the only premises are the ones
  the proof reads: the moved cells equal the old cells, and the located parents have the same table and rows in both
  databases). Only the final instance
  (`Catalog.parentLink_dropColumn_mapColumns`, `Database.foreignKey_of_drop`) names the dropped column.
- `Database.EveryTable.dropColumn`: general in the fact (any fact of a position and table, with a premise for the
  unchanged tables and one for the changed table). `runStatement_dropColumn_satisfies`: general in the property.
  `runStatement_dropColumn_eachTable`: general in the atom, with the minimal two premises.
- `Table.*.dropColumn` (one per atom): each states the atom for the table without the column with only the premise the
  proof uses (for example `RowsStored` and `NotNull` need no clean-drop premise); a joint statement over all atoms
  would only restate the field `dropped` of `RowLocalAtom` and `TableAtom`, which is the general form for atoms.
- `Expr.evaluate_dropColumn` and `Expr.eval_dropColumn` (ColumnDropExprLaws): general in the expression and the
  row, with the premise that the expression does not read the dropped column. `LiteralData.*_dropValue`: general in
  the key and the row.
- Stays specific, no general form attempted: `Catalog.droppable_spec` and `CatalogTable.droppable_spec` (they are the
  definition unfolded), `Catalog.uniqueKeys_free` (two uses only, both on the dropped table).

#### Shared-law changes of part 3 (for the S6 part 3 work and the NOT IN task at merge)

1. `RowLocalAtom` and `TableAtom` gained the field `dropped` (a table that has the atom and loses a column cleanly
   still has it). A new instance of either structure must discharge it.
2. `Syntax.Statement.dropColumn` is a new constructor: every exhaustive match over `Syntax.Statement` needs an arm
   (the editor modules got the minimal arm).
3. `Resolved.Statement.dropColumn table index stored` is a new constructor: every exhaustive match over
   `Resolved.Statement` needs an arm (about 25 theorems; see the open point below).
4. The golden text in `tests/surface/DbBangErrors.lean` changed: the "not modeled" message lists ALTER TABLE DROP
   COLUMN.
5. (Unit 3.8) The run of a rename (`Resolved.Statement.rewrite`) stores the new catalog when it has the same
   outline (`Catalog.sameOutline`), no longer when the foreign keys also select the same parents (`Catalog.keepsOutline`
   stays for DROP COLUMN). `runStatement_rewrite_satisfies` takes one premise less (`fun same => ...`). The conditions
   `ForeignKeyRowsCondition` and `ForeignKeySchemaCondition` (and so `ForeignKeyAtomsCondition`) of a rewrite are now
   `renamed.selectedParents = database.catalog.selectedParents` instead of `True`. S6 part 3 and the NOT IN task must
   use the new shape at merge; a proof that calls `runStatement_rewrite_satisfies` with two lambda arguments needs one.

#### Open point for a later cleanup task: the cost of a new `Resolved.Statement` constructor

- Theorems that needed a new arm (unit 3.3): `runStatement_rowidsDistinct`, `runStatement_keysUnique`
  (`KeysCondition`), `runStatement_catalogSupported`, the shaped, distinct and table-atom statement theorems
  (`AdmittedShapedStatement`, `AdmittedDistinctStatement`, `AdmittedTableAtomStatement`, `RowLocalStatement`),
  `runStatement_rowReferences` and `ForeignKeyRowsCondition`, `runStatement_parentSchemasCompatibleSelected`,
  `runStatement_foreignKeyAtomsSelected` and their two conditions (`ForeignKeySelectedStatement`),
  `literalStep_success_catalog`, `step_extends` (`PreservationLaws`), `ValidAtomsStatement`, `KeysUniqueRunStep`,
  `AtomsConditionsOfLink`, `FailingConstraintLaws`, `StepCatalogLaws`, `RunHoldsStep`, `SqlLaws`, `SqlAdvance`,
  `StatementClock`, `StatementOutput`, `StatementSingleton`, `ForeignKeySchemaWrites`, `ForeignKeyCreate`,
  `ResolveStateSpec`, `ResolveStatementForms`, and the output and message definitions.
- Sketch of a combinator: every table-local invariant theorem has the same shape for a schema statement: the
  failing run keeps the database; the succeeding run gives a database that is a function of the input
  (`step` equations) and must be shown to have the invariant. A per-constructor record
  `Resolved.Statement.Frames` with the fields (a) `keeps_on_failure` (`step_..._of_not_runs`), (b) `eachTable`
  (a `RowLocalAtom`/`TableAtom`-parametric law, as `runStatement_dropColumn_eachTable`), (c) `catalog` (the catalog
  of the success: `applyCatalog`), (d) `rows`-shaped and key facts as properties of the stored database, would let one
  generic theorem `runStatement_of_frames` derive all `Satisfies` statements for the atoms; a new constructor then
  supplies one `Frames` value and the 25 theorems stay untouched. The rename and DROP COLUMN steps already have this
  form (`runStatement_rewrite_satisfies` and `runStatement_dropColumn_satisfies` are the generic part).
- Estimate: about 250 to 350 lines for the record and the generic theorem, and about 25 one-line arms removed per later
  constructor; the migration of the existing 25 theorems is a mechanical rewrite of about 1 to 3 lines each.

### Unit 3.7: the DROP COLUMN resolver, native conformance evidence and mutants

- Resolver (`Resolution/DropColumnResolve.lean`, `DropColumnDependents.lean`, `DropColumnOutcome.lean`): the checks
  follow `sqlite3AlterDropColumn` of SQLite 3.51.0 (table, system table, view, column as the statement writes it, PRIMARY
  KEY before UNIQUE, last column), then the two schema tests. Pass 1 runs over the catalog as it is and finds a view
  or trigger that does not resolve; pass 2 runs over the objects of the catalog in schema order, with the positions
  of the columns before the drop, and finds in order: a table that still names the column (table-level UNIQUE key,
  CHECK, generated expression, foreign key), an index that reads it, and a view or trigger that no longer resolves in
  the catalog after the drop. The success is `Resolved.Statement.dropColumn` with `Catalog.dropColumn`; late-resolved
  views and triggers are resolved again in that catalog, so they keep no stale position and are still validated.
  `PrepareError` gained `dropColumn` (view, primary key, UNIQUE, last column) and `DependentPhase` (`current`,
  `afterRename`, `afterDropColumn`) replaced the flag `afterRename`; the JSON key is `phase`.
- Restrictions that remain (`alter-drop`, narrower; text and conformance example changed): the table is the parent of a
  foreign key (the model does not move the parent columns of other tables; the docstring of `CatalogObject.allowsDrop`
  says that this is a model restriction and SQLite allows the drop), a trigger with `UPDATE OF` the column, several
  kinds of definition that name the column, a definition whose spelling the model does not know (quoted, qualified,
  other letter case), and a catalog after the drop outside the limits. The restriction text and
  `docs/semantic-subset.md` name them.
- Outcome laws: `DropOutcome`, `finishDropColumn_outcome`, `resolveDropColumn_outcome`, `DropOutcome.step`,
  `.applyCatalog`, `.valid` replace the old `resolveDropColumn_no_success`. The call sites in
  `ResolveStatementFacts`, `ResolveStatementValid`, `ResolveStatementSingle`, `NamesSpec` and `ResolveStateSpec` use them.
- Bug found by the native cases and fixed: pass 2 first ran over the catalog after the drop, so an index on a column
  after the dropped one looked as if it read the dropped column (its positions had moved). Pass 2 now reads the objects
  of the catalog before the drop; `DropColumnExamples` guards it (`shifted`).
- Compiled-evaluator `#guard` checks (`Resolution/DropColumnExamples.lean`): error order, spellings, index and table
  failures, restrictions, successful drops with a populated database (cells, order, rowids, other tables kept), the
  rejection of a catalog that is not the catalog after the drop (the run fails with the database unchanged).
- Conformance: `conformance/authored_column_drops.py` (38 cases, version 7 records; setups in
  `column_drop_setups.py`; the existing `authored_drops.py` is the DROP TABLE module) and
  `tests/conformance_column_drops_test.py`: the judge's verdict is AGREE for every case except
  `column-drop-parent-unrelated`, which stays a restriction (a parent column that no key names). The kernel proves the
  table-only cases. `column-drop-index-reads-column` and its siblings check the `step` phase of the dependent-object
  errors. The prepare errors (primary key, UNIQUE, last column, view, missing table or column) have phase `prepare`.
  No case disagrees. Savepoints are not modeled, so no savepoint case is included. The Nix verdict of the part
  gates (below, when written) covers the corpora with `ALTER TABLE ... DROP COLUMN`.
- Mutants: `conformance/column_drop_mutants.py` (9 mutants: primary key, UNIQUE and last column checks removed, index
  that reads the column allowed, CHECK and generated dependencies ignored, rows lost, cell kept, run always
  rejected), run by name with `tests/conformance_column_drop_mutants_test.py`; all 9 killed. A mutant that needs a view
  cannot be measured, because the mutant runner replays tables only; views are judged through the predictions.
- Review of the unit 3.3 to 3.6 commit (`20261027T074345Z-1230d27d`): 10 musts and 1 should, all fixed in the
  `refactor:` commit (R11: executable tests for the accepted drop with rows and the rejected run; R7: the foreign-key
  parent rule is named a model restriction; R2: premises added to six docstrings and `{name}` references; R3: proof
  sketches; R19: this file names `literalStep_success_catalog` as the one client that unfolds the run).
- Generalization analysis of the new statements: `DropOutcome` is general in the limits, the catalogs and the statement
  (it is the outcome of any drop resolution; `resolveDropColumn_outcome` is the instance for the resolver).
  `DropOutcome.step`, `.applyCatalog` and `.valid` take only the premises their proofs use (the outcome, the limits).
  `finishDropColumn_outcome` stays specific to the drop: it reads the definition of `finishDropColumn`.
- Manual proof repairs in this unit: 0 beyond mechanical arms (about 10 one-line replacements of the old stub lemma
  and updated message constructors). Total for the task so far: about 165, none of them a non-mechanical arm.

### Unit 3.8: the rebuild runs, and a rename may make a dangling foreign key find a parent

- Finding: the guide's rebuild (create the new table, copy, drop the old table, rename the new one to the old name)
  was out of scope. After the DROP TABLE, the foreign keys of the children name a table that does not exist; the rename of
  the new table to that name makes them find a parent. The run of a rewrite stored the catalog only when every foreign
  key selected the same parent, so this rename failed as `.unmodeled`, and the predictions of the corrected rebuild were
  `MODEL_UNSUPPORTED`. The step does not need that test: it replaces the catalog and keeps the rows. Only the proofs of the
  foreign-key atoms need the same selected parents, as they need `Catalog.CreateKeepsSelection` for a CREATE TABLE.
- Change: the guard of the rewrite is `Catalog.sameOutline` (new); the foreign-key conditions of a rewrite are the
  equality of the selected parents (shared-law change 5 above). The row-local, table, key and Valid statement theorems
  lose an unused argument. The rename resolver is unchanged.
- Consequence for S6: the rebuild's rename satisfies the weaker guard but not the new condition, so the foreign-key atoms
  after the rebuild come from the database (what `PRAGMA foreign_key_check` reports), not from a frame law. This is the
  same situation as for a CREATE TABLE that locates a dangling key; the universal claim is for S6.
- Cases (`conformance/authored_rebuilds.py`, 11 cases; `tests/conformance_rebuilds_test.py`): the unsafe rebuild with
  enforcement on (cascade through the implicit DELETE of DROP TABLE), the corrected rebuild with enforcement off and
  `foreign_key_check` (clean, and with a violation after a parent row is left out), the default connection with
  enforcement off, `PRAGMA foreign_keys` inside a transaction (no effect, both directions), a rename of the old table first
  (the foreign keys of the children follow it), a view that blocks the rename, a rollback of the whole rebuild and the
  rebuild of the child. The recorder fixes the enforcement state at the start of a case through the measured profile
  (a pragma outside a transaction would change the profile), so the cases say it with the feature `fk-on`. Every case agrees
  with native SQLite except `rebuild-drop-column-instead`, which stays a restriction (a drop of a column of a parent
  table). The kernel proves the table-only cases.
- Mutant: `conformance/rebuild_mutants.py` (`rename_keeps_selected_parents`: the old guard), killed by
  `tests/conformance_rebuild_mutants_test.py`. The rename mutants of part 2 changed their text to `sameOutline`.
- Generalization analysis: `Catalog.sameOutline` and `Catalog.sameOutline_eq` are general in the catalogs.
  `runStatement_rewrite_satisfies` is more general than before (it needs only the outline). The condition for the rewrite
  states the equality for any renamed catalog; the dangling-to-located case is the instance that it excludes.
- Manual proof repairs in this unit: 6, all one-line changes of a lambda or a condition. Total for the task so far: about 171.

### Merge of the NOT IN laws task (PR #281, with S6 automation part 2, PR #280)

- Merge commit of `tasks/not-in-subquery-laws` (d92513aa) into the part 3 chain. The only conflict was the module glob
  list of `packages/belay-sqlite-model/lakefile.toml`; I took the union of both sides (`union_globs.py`, 11 modules
  added from part 3, none removed).
- Adaptation to the five shared-law changes (the `dropped` field, `Syntax.Statement.dropColumn`,
  `Resolved.Statement.dropColumn`, `Catalog.sameOutline` with its changed arities, and the golden text): none was
  needed. The NOT IN modules build no `RowLocalAtom` or `TableAtom` instance and match no statement type
  exhaustively, and the S6 tactics and the S5 checker use the shared theorems only through their general statements.
  The model package and the whole `dev-build` (2545 jobs) build on the merged tree. The surface fixtures of S6 compile in
  `just test-full`, whose result is below.
