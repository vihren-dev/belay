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
