# Status: S6 effect rules and automation

Created 2026-10-24. Status: OPEN. Part 1 done (2026-10-26); part 2 in progress; part 3 has not started.
Task: [task file](20261024-s6-automation.task.md).
Specs: ADR17 S6; production execution/assertion/pattern tasks; S5 checker.

## Scope and inputs

This task completes the required proof tactics and their checked effect/frame
rules. It preserves the flexible semantic primitives. Dependency analysis is
conservative and supplies certificates to proved rules; disjoint table names
alone do not establish full commutation. The S6 prototype's counter, clock,
trigger and all-continuation examples remain acceptance cases.

The production execution, assertion and migration tasks plus S5 are
prerequisites. Final FK and table-rebuild work supplies the example semantics.
No production automation, general footprint engine or completion is claimed.

## Progress

- 2026-10-24: specified checked certificates, explicit proof routes, tactics,
  stable proof suggestions, S5 integration and private guide acceptance.
  Review 20261024T152950Z-8b118fbc found no musts or shoulds. Implementation
  remains unassigned pending its listed prerequisites.
- 2026-10-26: inputs refreshed against main after #270 and the possible write
  executions (#271): the prerequisites are implemented, the task names the current
  modules, the query-equivalence example, three acceptance parts (the rebuild example
  waits for the table-rebuild task) and the guide changes recorded here for the guide
  acceptance task. Assigned for part 1.
- 2026-10-26: part 1 commit 1: statement effect rules (UPDATE, ADD COLUMN), frames and shelter rule, read
  certificates with the untrusted analyzer, weak preservation and full commutation rules, positive and negative
  fixtures and `tests/surface_s6_rules_test.py`. Local fixture runs pass.
- 2026-10-26: review 20261026T191757Z-6bec4bb9 (4 musts: R5 constructor enumeration in `plainWriteTarget` and
  `ReadAnalysis.analyze`, R6 shelter laws moved to model `ShelterFrame`, R19 commutation premises) fixed in the
  `refactor:` commit; re-review 20261026T192140Z-92a4ce94 has no findings.
- 2026-10-26: end of part 1 gates at the refactor commit. `just test-full`:
  `/nix/store/nh9g4vv5gpqxxjnxwcc1ri21rz801lb3-sqlite-verifier-test-reports` (the first run ended at the 1500 s
  limit with no failed test, the rerun passed). `just verdict`:
  `/nix/store/cjzhc4ilbgbgbirqmhrv4hlxq1zv0s52-sqlite-verifier-verdict`. Predictions
  `/nix/store/1pngxqkmdkg1k09aq739y7nqxmrsnv32-sqlite-verifier-predictions` are byte-identical to the base
  `/nix/store/vghpgg7nyb4nifg434ddx5dcrmzmh216-sqlite-verifier-predictions` (55 entries, `diff -r`). Part 1 is
  done; parts 2 and 3 have not started.

## Part 1 plan, 2026-10-26

Scope rule from the owner (2026-10-26, applies to all parts): the specific examples of the user guide
(customers, accounts, signup, purge, notBlocked, the email_lower expansion and so on) are not part of the
core (model package) or the surface (belay package). Everything under `packages/` is general: laws about
statement families, frames, certificates and their soundness, stated over arbitrary tables, columns and
schemas with explicit premises, with no module, declaration or premise shaped around one guide example.
Guide examples appear only as test fixtures under `tests/surface` and their pytest drivers. Part 1 adds no
`NormalizedField*`-style module and does not extend the existing `NormalizedField*` modules. A guide
example that general rules cannot prove is recorded below as an open point, not as an example-specific
lemma in a package.

Scope: acceptance part 1 only (effect and frame specifications, conservative dependency
certificates, all-continuation program rules). No tactics, S5 integration or code actions (part 2)
and no INSERT SELECT, RENAME or DROP COLUMN (part 3). The table-rebuild agent owns the model run,
statement and INSERT SELECT files and the surface execution proofs for several executions; part 1
adds new modules only and adds lines to the shared registries.

Modules added (each below 200 lines, checked Verso docstrings; all general):

- Model (registered in the model `lakefile.toml` globs and in `Belay/Sqlite/Model.lean`):
  `PlainUpdateEffect` (stored rows of an error-free plain UPDATE, no choice output), `AddColumnEffect`
  (database after ADD COLUMN), `NonQueryOutput` (a step of a statement that is not a query gives no choice
  output), `PlainWriteFrame` (a plain INSERT, UPDATE or DELETE changes only the rows of its target and keeps
  snapshot and settings), `ReadOnlyFrame` (a query or prepare error step keeps the connection), `ShelterFrame` (`Connection.shelter`,
  `Statement.ShelteredFrom`, `Connection.shelter_step`: a plain write of another table or a read keeps the
  catalog, the table at a position, the snapshot and the settings),
  `SimpleQueryAppend` (a simple query that reads only columns below a width gives the same results when cells
  are appended to its rows) and `CertifiedQueryOutputs` (step outputs of such a query on two connections whose
  table scans differ by appended cells, for any table and any added cells).
- Surface (registered in the `belay` `lakefile.lean` globs and in `Belay/Sqlite.lean`):
  `PlainUpdateEffect` and `AddColumnEffect` (fresh-run `ifOk` rules for UPDATE and ADD COLUMN, like
  `Sql.ifOk_send_plainInsert`), `SqlFrames` (`Sql.Frame` as a claim about every branch, with pure, one-step,
  bind, map and composition rules), `PlainWriteFrames` (`Statement.ShelteredAt` and
  `Sql.Frame.sendStatements_sheltered`: scripts of plain writes of other tables and reads keep the catalog, the
  table at a position, the snapshot and the settings), `ReadCertificate` (certificate, validity, obligations,
  `output_eq`), `ReadAnalysis` (the untrusted analyzer that may return unknown, `analyze_sound`),
  `ReadCertificatePreservation` (weak preservation of a certified read across any migration whose
  obligations hold) and `CertifiedQueryCommutation` (full commutation of a certified read with a migration under
  a constant clock).
- Tests: `tests/surface_s6_rules_test.py` (six tests, listed in `tests/nix_suites.json`) with fixtures
  `tests/surface/S6RulesEffects.lean` (UPDATE and ADD COLUMN effects, conditional and total fresh triples),
  `S6RulesFrames.lean` (frames of a program with an output-dependent continuation, a read with two permitted
  results, the snapshot of an open transaction), `S6RulesQueryPattern.lean` (the migration query pattern of the
  guide proved by the general certificate rules for every bound value), and the negative fixtures
  `S6RulesNegativeReads.lean` (SELECT star, metadata, counter read), `S6RulesNegativeCertificates.lean` (different
  change counts, unmodeled syntax, a certificate whose soundness obligation fails), `S6RulesNegativeFrames.lean`
  (trigger, foreign-key action, generated column, rollback) and `S6RulesNegativeClock.lean` (moving clock).
- Shared files touched, added lines only: the two lakefiles, the two barrels, `tests/nix_suites.json`.

Dropped from the first plan: `PlainWriteErrors` (the failure cases are inside `PlainWriteFrame`) and
`ReadCertificateExpansion` (replaced by the general `ReadCertificatePreservation`, which has no expansion in it).

Rules that the tests exercise by name: `Sql.ifOk_send_plainUpdate`, `Sql.ifOk_send_addColumn`,
`plainUpdate_database`, `Sql.Frame.bind`, `Sql.Frame.sendStatements_sheltered`, `ReadAnalysis.analyze_sound`,
`ReadCertificate.output_eq`, `ReadCertificate.preservesAt_send`, `ReadCertificate.commutesOn_send`.

Guide changes to record for the guide acceptance task: none so far. The guide's lookup-after-expansion
claim is now also provable by the general certificate rules; the guide text needs no change.

Open points:

- The guide's migration query pattern is proved for one concrete database and every bound value
  (`S6RulesQueryPattern.lean`), not for every admitted database with a site. The existing
  `NormalizedField*` lemmas already prove the universal output equality for the guide table, and the general
  rules would need an `appended` obligation for every database of the site. Options: (a) leave it, (b) state
  the obligations for a site structure in a fixture. Recommendation: (a) for part 1; revisit in part 2 when the
  tactics need a source of obligations.
- The rule `ReadCertificate.commutesOn_send` takes a constant clock, the obligations at the connection of
  the run, and the premise `admittedKept` as premises; it accepts any `admitted` predicate that meets them. The
  fixture `S6RulesQueryPattern.lean` chooses the `admitted` predicate that holds only at the original connection
  and clock,; a wider predicate must also satisfy `admittedKept`. A moving clock is a negative fixture
  (`S6RulesNegativeClock.lean`): the premise of a constant clock fails and the commutation claim is false.

## Part 1 accepted; integration on the open PR stack (2026-10-26)

- Decision on the first open point: (a). Part 1 keeps the claim for one concrete database. Part 2 states
  the universal claim over a site, as a fixture in `tests/surface` that uses the general certificate rules,
  not the example-specific parts of the `NormalizedField*` modules (they are due for the cleanup task).
- The task file now says that outcomes are general laws and guide examples are test fixtures only
  (commit `spec: S6 automation outcomes are general laws; ...`, review `20261026T201455Z-11ea972d`: no
  findings).
- The branch has the merge of the open stack top (#275, the global signup invariant) and sits on top of
  stack 273. The two barrel conflicts (`Model.lean`, `lakefile.toml`) keep the modules of both sides.
  Checks on the merged tree:
  - `just test-full`: exit 0, `/nix/store/ba3574xwy2b7rx4a3yzc5kbv1xwvil6j-sqlite-verifier-test-reports`
    (the first run ended with exit 124 at the 1500 s limit with no failed test, beside another test-full;
    the rerun passed).
  - `just verdict`: exit 0, `/nix/store/qqlwfhcc7d9xdjwg58447dri5d52wy6g-sqlite-verifier-verdict`
    (55 corpora, AGREE 5170, MODEL_UNSUPPORTED 2430).
- Next: part 2 (tactics, checker and code-action integration, the guide examples except the rebuild).

## Part 2: tactics, checker integration, code actions (started 2026-10-26)

Scope: acceptance part 2 of the task file. All package code is general; the guide examples are fixtures in
`tests/surface`. The table-rebuild agent owns the model run and statement files; part 2 adds new modules and added
lines in the shared registries (barrels, lakefiles, `tests/nix_suites.json`).

Commit 1 (step rules and `sql_run`):

- Model: `FailedStepFrame` (a failed plain write, a failed ADD COLUMN and a failed step keep the connection that
  the step reports), `SelectStepFrame` (a SELECT step keeps the connection).
- Surface rules: `SendStepRules` (`Sql.check_send_of_step`, the generic rule for one statement), one rule per
  statement family (`PlainInsertStepRule`, `PlainUpdateStepRule`, `PlainDeleteStepRule`, `AddColumnStepRule`:
  premises for the resolution, the table, the model coverage, then a success goal and a failure goal), and
  `ReadStepRule` (`Sql.check_single_select`, `Sql.check_query_select`, `Sql.check_send_select`). The success and
  failure goals of the write rules carry the fact that the step does not end the run, which a program that
  continues after the statement needs.
- Tactic: `SqlRunShape` (reads the program), `SqlRunRules` (which rule, which names for the goals),
  `SqlRunGoals` (closing premises with hints, entering outcomes, entering triples), `SqlRun` (`sql_run [hints]`),
  `SqlRunTriples` (a triple and its verification condition are the check of the program, by `Iff.rfl`).
  `sql_run` uses the checked lemmas of `SqlRunTriples` to enter a triple, and it also accepts the goal that
  `mvcgen [definition]` leaves (a check at a state with an equation to the initial context). It does not call
  `mvcgen` by itself. Obligations that the rules do not close stay as goals with the tag of the rule premise; a
  program that cannot be read fails before any change with a message that names the part.
- Fixtures (`tests/surface`): `S6AutoAddCustomer` (the guide's insertion claim: fresh-run claim by `sql_run`,
  the standard triple by `mvcgen` then `sql_run`, and the same claim by the public rules alone), `S6AutoEffects`
  (UPDATE claim by `sql_run` and by the rules), `S6AutoShapes` (exact error and warning messages for a raw step, a
  variable program and an unreadable part after a rule). Driver `tests/surface_s6_automation_test.py` in the
  `surface` suite.
- Not done yet in part 2: `sql_commute`, `sql_auto`, the "Try this" script and code action, checker integration,
  the remaining guide fixtures and the negative fixtures.
- Decision for the failure goal of a total (`andOk`) claim: `sql_run` leaves it as an obligation, since the
  model coverage hint cannot show that the statement does not fail. The claim for the conditional form (`ifOk`)
  closes it without a hint.
- 2026-10-26: review 20261026T221752Z-30d94d7d of commit 1 (3 musts, 3 shoulds), all fixed in the `refactor:` commit:
  `sql_run` kept no sibling goals after the main goal (fixed, fixture `second_goal_stays`); the docstrings of the
  four write rules restate the quantifiers of their success and failure premises; fixture `S6AutoPaths` covers the
  DELETE, ADD COLUMN, query, single and sent SELECT paths; named policy definitions (`traversalFuel`,
  `blockingPremises`); docstrings for the helpers and the rule modules.
- 2026-10-26: review 20261026T222942Z-da9e0c53 (1 must): the fixture `second_goal_stays` hid the sibling goal in a
  bullet; it now runs `sql_run` while both goals are visible.
- Coordinator note (2026-10-26): the table-rebuild work changes `runScriptStep_others`, `Succeeds.script_iff`,
  `Succeeds.of_default`, `Sql.branch_continued_iff` and the `found_eq` and `branch_shape` signatures. Part 2 code
  reaches them through few places: `runScriptStep_others` in `SendStepRules` (one use), `Sql.Branch.found_eq` in
  `ReadStepRule` (three uses), `sendStatements_branch_shape` in the part 1 certificate rules and the new
  `sql_commute` (through the rules). No new code uses `Succeeds.*` or `Sql.branch_continued_iff`.

Commit 3 (`sql_commute`):

- Surface: `SqlCommute` (`sql_commute [hints]`). The tactic reads the claim from the goal (`Migration.PreservesAt` or
  `Migration.CommutesOn`; `Migration.PreservesOn` is not supported yet), reads the one statement of the read, applies
  `ReadCertificate.preservesAt_send` or `ReadCertificate.commutesOn_send` by the claim, closes the premises of the rule
  from the hints (the hint itself, the soundness of an analysis result `ReadAnalysis.analyze_sound`, and these under
  introduced variables), and leaves each other premise as a goal with a warning that says what is missing. The tactic
  does not search for dependency facts: it uses the proved rules and the hints. The rule follows the claim and not the
  hints, so the hints of a weak claim never close a strong one.
- Fixtures: `S6AutoCommute` (preservation and commutation of the lookup of `S6RulesQueryPattern`, and the weak hints
  that leave `constant`, `obligations` and `admittedKept` open), `S6AutoCommuteNegative` (a counter read and a
  migration under a moving clock leave the false premise open; the rules fixtures show that it is false).
  The driver test is in `tests/surface_s6_automation_test.py`.
- Review 20261026T223322Z-e1e78b5e (1 must, 2 shoulds) was for the earlier state of `SqlCommute` that the previous
  commit contained by mistake (the preservation goal failed because the rule type was unfolded into more binders,
  and no fixture used the tactic). Fixed in this commit: the rule type is not unfolded, the fixtures above use the
  tactic, the handler has a docstring and the two read errors say what to do.
- 2026-10-26: review 20261026T223834Z-2826a0a8 of the `sql_commute` commit (2 musts: sibling goals dropped by
  `sql_commute`; `Migration.PreservesOn` claimed but unsupported). This is the fourth review round in a row with
  new musts, so work stopped; the owner approved a fifth round on 2026-10-27, and the count starts again. The fixes are committed (2026-10-27)
  (siblings kept, `PreservesOn` removed from the supported claims, fixture `second_goal_stays` in `S6AutoCommute`;
  the negative fixtures are `example`s, not named theorems);
  the findings are resolved.

Merge with the table rebuild part 1 stack top (2026-10-27):

- Merge commit of the branch and `tasks/table-rebuild-part1` (change qzqstszv, PR #278), no rebase. Registries are the
  union of both sides (`lakefile.toml` of the model gets `FailedStepFrame` and `SelectStepFrame` on the new list).
- Repairs for the changed laws: `FailedStepFrame` reads the new shape of `runScriptStep_continued_spec`.
  `Sql.check_send_of_step` takes a premise `single` (the statement resolves to no INSERT from a query without rules)
  and uses `runScriptStep_others_of_single` and the new `check_send_single_of_step`; the four write rules close it
  from their `found` premise. New `Sql.check_send_of_step_notInsertSelect` has the syntactic premise
  `statement.isInsertSelect = false` (by `resolveStatement_single`); `sql_run` uses it for a statement without a rule
  of its own and closes the premise `notInsertSelect` by `rfl`, so a sent INSERT from a query leaves that premise open.
  `sql_commute` closes the new premise `single` of the certificate rules by `decide` and explains it when it stays open.
  `ReadStepRule` needed no change.
- New fixtures in `S6AutoPaths`: a sent INSERT from a query leaves the premise `notInsertSelect` open (it is false),
  and a sent CREATE INDEX (a statement without a rule of its own) closes it by evaluation. Nix check results for
  the merged state follow at the end of part 2.

Commit (`sql_auto`, 2026-10-27):

- Surface: `AutoSearch` (the search: the routes `sql_commute`, `sql_run` with a finishing step per remaining goal, and
  `grind` with the hint names that are no local hypotheses; each route runs in a copy of the tactic state without error
  recovery, so a failed route leaves the original goal as it was and a route that only reports an error cannot admit a
  goal; the routes share the remaining heartbeats, and a route that uses its share fails with a reason) and `SqlAuto`
  (`sql_auto [hints]`: keeps the sibling goals, fails with one line per route when no route closes the goal, and offers
  the explicit steps of the winning route as the "Try this" replacement of the call, one step per line at the column
  of the call). The explicit tactics stay usable alone. Only kernel-checked proofs close a goal.
- `sql_run` now fails on a first goal that is no check, triple or `mvcgen` goal. Before, it returned the goal
  without a message (fixture `S6AutoShapes`).
- Fix in the S5 budget helper `speculative` (`CheckBudget`): the state was restored also after success, because
  a `let mut` flag set inside `try ... finally` is not visible in `finally`. It now keeps the changes after success.
  S5 behavior can change; the S5 suites decide.
- Fixtures: `S6AutoAuto` (run route with exact suggestion, replacement alone, grind route, false goal with each
  route's reason, a goal that is no check, sibling goal kept, work limit, commute route, axiom audits).
  `tests/surface_s6_auto_editor_test.py` (in the `surface` suite): real server, code action request at the call
  range, the edit replaces exactly the call, the edited document has no error, warning or suggestion, the
  steps elaborate alone with ordinary axioms only, and a call that no route closes offers no action.

Commit (S5 checker covers claims about programs, 2026-10-27):

- Claims. `#sql_check`, the tactic and the automatic check now accept `Sql.check`, the four equivalence structures
  (`Sql.EquivAt`, `Sql.ObservationEquivAt`, `Sql.View.EquivAt`, `Sql.View.ObservationEquivAt`) and every
  definition that unfolds to them (`FreshEnsures`, `Sql.Equiv`, `Migration.PreservesAt`, `Migration.CommutesOn`, and so on).
  `queryNames` and `querySites` read them: the sites are the scripts that the programs send first
  (`CheckProgram`), at the database of the initial context (`initialDatabase?` unfolds a named context such as
  `initial`). A program with a continuation in Lean code gives the replay of its first scripts only. Its report
  carries a note that says so, and says that the model's run of the whole program gives the failing result
  (`Replay.Report.note`, printed as `Note:`). It is not shown as a failure of one native statement.
- Witness. `Witness.choose` supplies `ExecutionContext.initial database environment` for a context binder.
  `domainDatabases` (`CheckDomain`) adds the databases that an equality premise `db = d` names to the candidates, after
  the empty database, so a claim "for every database equal to `sample`" is refuted at `sample`. `DecidableEq Database`
  and the instances for `ifOk`, `andOk` and `ifOkWith` posts (`AssertionTerms`) and `Migration.Domain`
  (`MigrationPattern`) let the kernel decide these premises and the negated conclusion. A relation whose actual runs
  differ is refuted by the difference of the run, field by field when the run type has no decision procedure
  (`CounterexampleActual`). A relation that agrees on the actual run and differs only on a branch stays unknown.
- Failing observation. `CheckObservation` explains a certified refutation: the check fails on the actual run, or the
  actual run satisfies the check and another branch fails, or the post has no decision procedure; for a relation
  the outputs of both runs. The wording depends on the relation: for `Sql.EquivAt` equal outputs mean a different
  value or connection; for `Sql.ObservationEquivAt` a different value; for the view variants the text says that the
  views project the runs to different observations and shows the runs before the projection.
  The text says where the run starts when the claim fixes a database other than the witness database. It is
  shown as `Failing observation:` and it is best effort within `explanationShare` (nine tenths) of the budget
  that is left.
- Proofs. The default proof attempt is `defaultProof`: the closing tactics of `tryProof` (now also
  `Sql.Equiv.refl` and `Sql.EquivAt.refl`), then the search of `sql_auto` with the hints `rfl` and `⟨_, _, _, rfl⟩` on
  a claim that opens to the check of a program, at most `searchShare` (a third) of the budget. The printed script holds the opening
  and the explicit steps; the checker elaborates it again without a search before it reports `proved`.
- Budget. The shares are named in `CheckBudget` (`shrinkShare` one half, `searchShare` one third,
  `explanationShare` nine tenths of the budget that is left). Before this change a refutation that was certified and
  replayed was lost when shrinking used the rest of the budget (the claim came out `unknown`). Exhaustion of the
  shrinking now keeps the refutation; the fixture block `equiv-shrink-exhausted` (budget 200000) covers this. The
  explanation leaves one tenth of the budget for the rest of the operation, so an exhausted explanation does not
  end it; a check with a budget that is almost used before the explanation can still end as unknown, because the
  checker ends when the whole budget is gone.
  The cost of a candidate that does not refute is high for universal equivalences (about 60 to 80 thousand units
  per database), so the fixtures name the database (`with (db := sample)`) or raise `sql.checkBudget`.
- Fixtures: `S6CheckPrograms` (triple proved, triple false with the failing run, continuation in Lean code,
  equivalence proved by reflexivity, two false equivalences, a false equivalence whose shrinking runs out of budget, an unknown for a too small budget, an unknown for a
  post without a decision procedure, the migration claim for a read of all columns refuted, and an unknown for the
  universal lookup claim that has no default proof) and `S6NotBlocked` (`NOT IN` against `NOT EXISTS`: the three
  counterexamples, each refuted with a replay, and one database that meets the premises where the outputs agree).
  The driver `tests/surface_s6_check_programs_test.py` (the `S6NotBlocked` blocks are read by
  `tests/surface_s6_not_blocked_test.py`; shared helpers are in `tests/s6_check_support.py`) replays the blocks `triple-false`, `equiv-false`, `equiv-at-false` and
  `migration-star-false` in native SQLite and compares the rows (for example 6 and 7 for the two updates, and `[]`
  against `[[1]]` for a NULL blocked id in the `S6NotBlocked` driver). The blocks `lean-continuation-false`,
  `equiv-shrink-exhausted`, `observation-false` and `view-false` check the report text only and do not run their replay scripts in SQLite (the scripts of
  `observation-false` and `view-false` do not show the model-level difference; `equiv-shrink-exhausted` only counts
  its two replays). The driver elaborates each printed proof again with the axiom audit. `S6CheckLabels` holds the marker command.
- Open points. (1) The claim `notBlockedIn ≈ notBlockedEx` under the premises "rowid alias and no NULL blocked id" is
  not proved for every database: the general laws describe `SELECT 1 WHERE x IN (SELECT ...)` and NOT EXISTS
  duplicate-key queries, but not the rows of a filtered scan with a subquery, so a proof needs new row laws
  (more than 200 lines). The fixture shows the counterexamples and one satisfying instance. (2) Guide change: the text
  "`notBlocked_same` where no NULL `customer_id` in `blocked`" omits the second counterexample (NULL `customers.id`
  with a non-NULL blocked id) and the collation counterexample; the claim needs the rowid alias premise too.
  (3) The partial-index invariant is covered by the earlier fixtures `SignupInvariantClaims` and `GlobalSignupInvariant`
  (site, counterexample of the nullable UNIQUE); the tactics do not prove it, because the plain insert rule has
  no law of unique indexes. (4) The automatic default budget (100000 units) is enough to prove a fresh triple and
  to refute a triple, but not always to explain the refutation of an equivalence.
- The code action of `sql_auto` is titled "Replace sql_auto with its steps" and its text is built as a string with
  the layout of the call (a `Try this` edit with syntax objects indented the steps of a multi-line script wrongly).
- The editor test `tests/surface_s6_check_editor_test.py` requests the proof and regression code actions of the
  automatic check on triples (source ranges, namespace, options) and applies the proof action to the document. The
  text of the regression action is elaborated alone with the axiom audit; its insertion into the original document
  is not tested. The test replays the failing script in native SQLite, shows that a too small budget gives no
  report, and shows that an edit of an earlier command cancels a running check of an equivalence.
- Explanations by relation kind: the fixture blocks `observation-false` (`Sql.ObservationEquivAt`, different returned
  values) and `view-false` (`Sql.View.EquivAt` with a quiet view against an identity view) cover the wording of
  the other relation kinds. An exhaustion of the explanation itself has no deterministic fixture: the budget at which
  the explanation runs out depends on the heartbeat cost of the explanation, so the case is not tested.
- Open point (5), universal migration query claim over a site. Not delivered in part 2. The general certificate
  rules need, for every database of the site, the rows that `ALTER TABLE ... ADD COLUMN` and the `UPDATE` with
  `lower(name)` produce, as laws about arbitrary rows. The existing laws describe single statements on fixed
  tables and not these row transformations. The estimate is 150 to 300 lines of new row laws in the model, which is
  at the limit of the planned work, and the table rebuild task owns the neighbouring model files. The fixture
  `S6RulesQueryPattern.lean` keeps the claim for one concrete database and every bound value. Decision needed:
  schedule the row laws after the rebuild task, or accept the concrete claim.
