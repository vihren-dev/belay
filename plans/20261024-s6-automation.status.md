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
  new musts, so work stopped; the owner approved a fifth round on 2026-10-27, and the count starts again. The fixes are prepared and uncommitted in the working copy
  (siblings kept, `PreservesOn` removed from the supported claims, fixture `second_goal_stays` in `S6AutoCommute`;
  the negative fixtures are `example`s, not named theorems);
  the findings are resolved in the next commit.
