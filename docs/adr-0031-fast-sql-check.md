# ADR 0031: A fast `#sql_check`: compiled screening, certification of one hit

Date: 2026-11-05. Status: ACCEPTED (owner, 2026-11-05: "I accept your recommendations").
Owner decisions 1 to 3 follow the recommendations.
Implementation: three slices (D9), each with its own task file, as local commits.
Audience: designers and reviewers.
Related: [ADR 0017](adr-0017-user-surface.md) (S5: counterexamples; the trusted base of the
surface), the S5 task [`plans/20261024-surface-s5.task.md`](../plans/20261024-surface-s5.task.md)
(the contracts of search, certification and replay), [ADR 0030](adr-0030-conditional-creation-and-expression-grouping.md)
(the consumer schema of issue #301), issue #316 (the readable counterexample).

## Overview

The owner asked for a `#sql_check` that is practical for real cases (2026-11-05: "Right now it
is a nice toy, but I don't think that it is practical for real-world cases. It needs to become
much faster."). The measurements below show two problems:

- **Each candidate costs about 0.4 to 2.7 seconds.** For a certified candidate, about 85% of
  that is a dependency audit that the checker repeats for each certificate. The search
  therefore tries few candidates, and a claim with no counterexample found spends 10 to 108
  seconds before it gives `unknown`.
- **A real application schema does not fit.** The consumer schema of issue #301 (6 tables,
  8 indexes, 5 triggers) is 9,457 constructor nodes as Lean data. The checker decodes
  candidates, replays and the counterexample text through Lean's evaluator with a limit of
  8,192 nodes. On that schema the search tries only the empty database, and a counterexample
  that the user supplies is not reported.

This ADR keeps the trust rule of S5: only a kernel-checked proof of `P` or of `¬ P` gives
`proved` or `false`. It changes how candidates are found. Compiled code generates and screens
many candidates; the kernel certifies only the first candidate that the screen accepts. Data
that the checker reads is computed by compiled code and confirmed by the kernel, not reduced
by Lean's evaluator.

## Context

Measured on 2026-11-05 in a local build of main `2b44247a` with the changes of issue #316,
which do not change the search. Each probe is a Lean file run with the surface build of the
workspace (`build/dev/surface`), timed with `IO.monoMsNow` around the checker's own functions
(`checkCandidates`, `visitCandidates`, `refuteWitness`, `replayClaim`, `witnessText`,
`shrinkProposals`, `shrinkCertified`). These are local measurements for the design, not
evidence of the Nix checks.

### The claim of issue #316

`#sql_check uniqueEmail succeeds where noDuplicateEmails` (a unique `NOCASE` index on
`customers(email)`, where no two rows have the same email under `BINARY`). The counterexample
is the two rows `'a'` and `'A'`. With the budget of 1,000,000 that the work of #316 sets
(main has 100,000, which gives `unknown`):

| Phase | Time |
| --- | ---: |
| Proof attempt (`defaultProof`) | 0.02 s |
| Candidate search: 8 candidates, 0.55 to 1.6 s each; the 8th refutes | 11.8 s |
| `replayClaim` | 4.4 s |
| `witnessText` | 0.4 s |
| `shrinkProposals` (20 proposals) | 0.7 s |
| `shrinkCertified` (no smaller witness) | 20.5 s |
| Total | 37.8 s |

A true variant of the claim (`GROUP BY email COLLATE NOCASE`), which `sql_auto` does not
prove, tries 17 candidates in 23.0 s and gives `unknown`.

### The cost of one candidate

`refuteWitness` for the counterexample above takes 1.58 s:

- Kernel work: 91 ms for the premise `Holds`, 16 ms for the negated conclusion, 106 ms for the
  final proof. The decision instances take 1 ms or less.
- `auditDependencies` (`CounterexampleCertificate.lean`): 173 ms for the witness inputs,
  353 ms for the claim, 367 ms for the final proof. The audit walks the closure of each
  expression, 12,060 constants for this claim, including the values of theorems. It keeps no
  result between calls. `refuteWitness` calls it five times: once for the inputs, once in each
  `certify` of its three `decideCertified` calls, and once for the final proof.
  `dataValue` and `databaseValue` (`CheckData.lean`) call it twice for each value.

### Compiled evaluation of the same claim

The claim's binders, instantiated with a database variable and the default environment, give
`fun db => decide premise && decide (¬ conclusion)`. Lean's `evalExpr` compiles it in 3 to
4 ms. Then:

- All 4,369 `customers(email)` tables of up to three rows over the 16 values of
  `Sampling.boundaryValues` are built in 19 ms and screened in 0.94 s, about 215 µs each.
  86 are counterexamples; the first is `'a'`, `'A'`.
- 10,000 seeds of `Sampling.database` (two rows) take 1.8 s. The first counterexample is at
  seed 755. The default search finds the counterexample with the targeted row pair `'a'`,
  `'A'` of `Sampling.boundaryRows` (its 8th candidate). Its 4 random samples
  (`sql.checkRandomSamples`) are unlikely to find it.

### The consumer schema of issue #301

The "Up" sections of the consumer's 12 migrations, as one script. `db!` accepts it in 14 to
23 ms. The claim is that `DELETE FROM messages WHERE id = :id` succeeds on every database with
the consumer's catalog. It is false: when a session has `message_count = 0` and one message,
the delete trigger sets `message_count - 1`, and `CHECK (message_count >= 0)` fails. Native
SQLite 3.51.0 gives `CHECK constraint failed: message_count >= 0 (19)`.

- With the schema that the checker infers from the SQL (only `messages`), no candidate has the
  consumer's catalog: 128 candidates, 108 s, `unknown`. `with (schema := …)` sets the schema of
  the search, but the claim's domain must still say "has this catalog"; the probe wrote
  `fun db => db.raw.catalog = crushSchema.raw.catalog`.
- With the consumer schema supplied, decoding fails with "SQL checking reached its literal
  data limit" (`maxDataNodes` = 8,192 in `CheckBudget.lean`): the schema alone is 9,561 nodes,
  and the targeted candidates 0 to 2 fail in `dataValue` (measured). The search tries only
  the empty database for each of the 16 values: 16 candidates, 9.8 s, `unknown`.
- A counterexample written with `db!` certifies in 2.65 s (`refuteWitness`). `replayClaim`,
  `witnessText` and `shrinkProposals` fail with the same data limit, so
  `#sql_check … with (db := bad) (input id := …)` gives `unknown`.
- Compiled screening: the 96 pairs of a boundary value and a targeted database take 19 ms, and
  5 are counterexamples. Of 2,000 random seeds, 103 give a database that `Sampling.validated`
  accepts, in 1.06 s, and 4 are counterexamples.
- Replay construction: `Replay.databaseSqlWith` (`ReplayDatabaseSql.lean`) gives no SQL for a
  catalog with indexes, triggers or views, or a table with CHECK constraints, foreign keys,
  keys or defaults. In the pinned `sqlite3` 3.51.0, the consumer schema, then
  `.dbconfig enable_trigger off`, the two rows (a session with `message_count = 0` and its
  message) and `.dbconfig enable_trigger on`, gives those rows unchanged, and the DELETE then
  fails with the CHECK error.
- `db!` refuses setup rows when a trigger that reads the clock can fire, even when no row
  matches. The probe created the triggers after the setup INSERTs.

The peak memory of each probe was 1.9 to 2.0 GB. A probe that does little more than import
`Belay` used 1.9 GB, so the check itself adds about 0.1 GB.

### The contracts that stay

The S5 task requires: one checking operation; `proved` and `false` only with kernel-checked
proofs; certification, not the searcher, controls acceptance; replay under the pinned
`sqlite3`; the SQL checker reuses the Plausible samplers; no promise of complete enumeration;
no wall-clock assertions in tests. The certificate audit rejects `sorryAx`, `ofReduceBool`,
`_native` names and the theorem under inspection. ADR 0017 keeps the surface's native code and
automation outside the trusted base.

The docstrings of `CheckRandom.lean` and `CheckData.lean` state a rule of the implementation:
generation uses only normalized literal data, and no supplied expression runs natively. This
ADR replaces that rule (owner decision 1, decided).

## Decision

### D1. One audit for each check

The audit keeps the constants whose closure it has accepted, for the length of one checking
operation. The exclusions (the theorem under inspection and the excluded locals) are fixed
for the operation, so a constant accepted once stays accepted. Local variables are audited
as today. The audit's result for every expression stays the same; only its repeated work goes.

Expected effect: a candidate costs its kernel work, about 0.2 s for the claim of #316.

### D2. Compiled screening

The checker builds one screen from the claim: a function from the inputs that the search
chooses (the database, the environment, the named values) to `Bool`, which decides each
premise and the negated conclusion, in the order of `contradictAt`. It compiles the screen
once with `evalExpr`. A primitive takes a screen that the caller supplies; the default builds
it from the claim.

- The screen only proposes. A candidate that it accepts goes through `refuteWitness`,
  `replayClaim` and the observation as today. A wrong compiled result (an `implemented_by` or
  `extern` that differs from its definition) can only waste time or miss a counterexample.
- Compiled code does not count heartbeats. All compiled work of a check (the screen, the
  generation of D3 and the data of D6) runs in its own task. The checker waits for each task
  with the time limit of the check and checks cancellation while it waits. At the limit it
  stops waiting and gives `unknown` with the reason. Compiled pure code cannot be stopped, so
  an abandoned task runs until its current computation ends (owner decision 3).
- Before it compiles the screen, the checker reads the closure of the screen (the walk of D1).
  If a constant outside Lean's own packages and `Belay` has `implemented_by`, `extern`, or is
  `partial` or `unsafe`, the checker does not compile the screen. The screen then runs only
  code that is compiled from its definitions, or code of Lean and `Belay`.
- A claim whose screen does not compile, or has none of the shapes that `contradictAt` reads,
  gets the explicit witnesses and `unknown` with the reason (owner decision 2).

### D3. Candidates in order of size

Compiled code generates the candidates with the functions of `Sampling`, which the Plausible
instances also use. The order is:

1. Explicit witnesses, then the databases that the claim's equality premises name
   (`domainDatabases`).
2. For each value of the value pool: the empty database, the targeted databases
   (`Sampling.targeted`), then each content of the touched tables (D4) with up to
   `sql.checkMaxRows` rows in each table, fewest rows in total first. Each row puts one value
   of the pool in every column, as `Sampling.uniform` does, with the changes of D4. The
   targeted databases start with the supplied database and its row variants (issue #318,
   added 2026-11-05): for each table with rows, the database with one more row, a variant of
   the first row (each text with its first ASCII letter in the other case, the same row, or
   NULL in a column that allows it). Without `(schema := …)`, the first `(db := …)` is the
   search schema.
3. Seeded random databases.

`sql.checkCandidates` counts screened candidates. Its default comes from the measurements of
D9.

### D4. Touched tables and rows that satisfy constraints

- **Touched tables.** Steps 2 and 3 fill only the tables that the claim's statements read or
  write, closed under the triggers on those tables and their foreign keys. The other tables
  stay empty. Explicit witnesses are not changed.
- **Rows that satisfy constraints.** The generator does not put NULL in a NOT NULL column. For
  a column with a foreign key, it chooses from the parent's key values when the parent has
  rows. It skips a row that repeats a UNIQUE or PRIMARY KEY value. CHECK constraints and the
  remaining rules stay with `Sampling.validated`.

### D5. Shrinking by screening

The checker screens the shrink proposals of a counterexample with the compiled screen, and
certifies only the smallest accepted proposal. It certifies and replays at most two
witnesses, the original and the shrunk one.

### D6. Data computed by compiled code, confirmed by the kernel

`dataValue` and `databaseValue` compute their value with compiled code and keep the kernel
check of `expression = toExpr value`. Lean's evaluator (`reduce`) no longer computes it. The
closure rule of D2 applies; data whose closure fails it is not decoded. A
generated candidate is already a value: its expression is `toExpr` of that value, and its
replay and text use the value. The limits of `CheckBudget.lean` stay as limits on the size of
the data (nodes and bytes), with values from the measurements of D9 that hold the consumer
schema.

The construction SQL of a generated candidate:

- On a schema that the checker infers, the formatter of today (`Replay.databaseSqlWith`).
- On a schema with source text (a `db!` constant, from `with (schema := …)` or D7) that has
  only CREATE and INSERT statements: the statements of the text in their order without the
  INSERTs, with the generated rows of each table right after the statement that creates it.
  A trigger is created after its table, so no trigger fires on these rows, and the model
  validates the whole text as today. This form came first, for issue #318 (2026-11-05).
- On a schema with other source text, such as ALTER TABLE in migrations: the
  schema's source text, then `.dbconfig enable_trigger off`, one INSERT for each generated row,
  and `.dbconfig enable_trigger on`. The formatter of today refuses indexes, triggers, CHECK
  constraints and foreign keys, and an INSERT with the triggers on would fire them. The model
  validates the construction as today for the source text, and runs the INSERTs on the schema
  with its triggers removed from the catalog; the rows must be the candidate's rows.
- Otherwise the candidate has no construction, and the search goes on to the next candidate,
  as for every candidate that does not replay today.

### D7. The schema as the domain

A decidable predicate says that a database has the catalog of a given database:

```lean
def Database.HasCatalog (schema db : Database) : Prop := db.raw.catalog = schema.raw.catalog
```

The search reads a premise `db.HasCatalog schema` as it reads `db = sample`, and uses that
schema for the candidates. A claim on the consumer schema is then
`∀ id, Succeeds (deleteMessage id) (·.HasCatalog consumer)` with no `with (schema := …)`.

### D8. The budget

The heartbeat budget (`sql.checkBudget`) covers the work in Lean's elaborator and kernel: the
proof attempt, the certification and the kernel checks of D6. The time limit of D2 covers the
compiled work: the screen, the generation and the data. The candidate count
(`sql.checkCandidates`) bounds the search. The defaults come from the measurements of D9. The change of #316 to
1,000,000 is measured again then.

### D9. Slices, tests and acceptance

Three slices, in this order, each with its own task file. The ADR changes no model semantics,
corpus or claim, so it has one pull request, after the last slice. Exception (2026-11-05): the
launch blockers #317 and #318 come first, as their own pull requests: slice 1 (D1) for #317,
and the row variants of D3 and the first construction form of D6 for #318.

1. **The audit** (D1).
2. **Screening, compiled data and shrinking** (D2, D3 without D4, D5, D6, D8).
3. **Touched tables, constraint rows and the schema domain** (D4, D7).

Tests, each with a timeout, in the suites of the surface checks:

- The claim of #316 is false with the default budget, with the same text and replay as the
  fixture `tests/surface/CounterexampleReadable.lean` of the work of #316.
- A fixture with an authored schema of the consumer's size and kind (more than 8,192 nodes,
  triggers that write another table, CHECK and foreign keys). It is not the consumer's text.
  Its DELETE claim is false, the counterexample has at most two rows in each touched table, and
  the replay fails in native SQLite with the same CHECK error. Its construction uses
  `.dbconfig enable_trigger off`, and native SQLite rebuilds the candidate's rows. The same
  fixture shows that a counterexample supplied with `db!` is reported.
- The audit: a theorem that uses itself through a lemma is rejected after the audit has
  accepted the lemma's other constants.
- The screening primitive, given a screen that accepts every candidate, gives no `false` for a
  true claim. A claim that uses a fixture constant with `implemented_by` is not screened, and
  its explicit witnesses still certify.
- A claim with a slow screen gives `unknown` with the time-limit reason and no error.
- The existing fixtures of S5 and S6 give the same results. A fixture that changes its result
  is a capability change and goes to the owner.

Acceptance: the status file records, for the claim of #316, its true variant and the
authored consumer-size claim, the time of each phase as in "Context", and the time of the
surface check suites in `just test-full` before and after. These are records, not test
assertions.

## Consequences

- Elaborating a claim runs compiled code of the claim's definitions: user definitions, the
  model and `Belay`. Lean already runs user code at elaboration (`#eval`, macros); the
  automatic check now does so for each theorem statement that mentions SQL.
- `unknown` means that more candidates were tried: the candidates of D3 in their order, until
  the candidate count or the time limit stops the search. They are a subset of the small
  databases, not all of them, and `unknown` is still no proof.
- The checker gets faster only where its time was search, audits and decoding. A claim whose
  kernel certification is slow stays slow.
- The net change of Lean lines is recorded in
  [the simplification goal](lean-simplification-goal.md) at the end. The deleted cooperative
  path offsets part of the new code.
- The rule "no supplied expression runs natively" goes out of the docstrings of
  `CheckRandom.lean` and `CheckData.lean`. `normalizedData` and the cooperative candidate
  path are deleted (owner decision 2).

## Alternatives considered

**Raise `maxDataNodes` and the budget.** Rejected: the consumer schema then decodes, but each
candidate still costs seconds, and a true claim spends the whole budget.

**Only the audit cache (D1).** Kept as slice 1, but alone it leaves about 0.2 s of kernel work
for each candidate and the data limit.

**An SMT solver for candidates.** Not now. Compiled screening tries thousands of small
databases in about a second, which covers what a bounded SMT search would find on these
claims. A solver helps for values that the value pool does not hold; that needs a measured
case first.

**Trust the compiled result (`native_decide`).** Rejected: it puts `ofReduceBool` and the
compiler into the trusted base, which the audit forbids.

## Not decided here

- Values outside the value pool: constants of the claim beyond today's `constants`, and
  boundaries of arithmetic.
- A separate process for the screen, so that a time limit can stop it.
- Faster kernel certification of a single witness.

## Owner decisions

1. **Compiled code at elaboration (D2, D6).** DECIDED (owner, 2026-11-05): yes. The checker compiles the claim's screen
   and computes its data with compiled code. Recommendation: yes. The kernel still decides
   every result, and without it the consumer schema cannot be checked at all.
2. **A claim without a compiled screen (D2).** DECIDED (owner, 2026-11-05): (a). Options: (a) explicit witnesses only, and
   `unknown` with the reason; the cooperative path is deleted; (b) keep the cooperative path as
   a fallback. Recommendation: (a), because the measured cooperative path fails on real
   schemas and doubles the search code. Slice 2 lists every existing fixture whose screen does
   not compile, so that the owner sees the capability effect before the merge.
3. **The time limit of the screen (D2).** DECIDED (owner, 2026-11-05): (a). Options: (a) a wall-clock limit with a default
   from D9, after which the abandoned task runs to the end of its candidate; (b) no time limit,
   only the candidate count. Recommendation: (a), so that the automatic check of a theorem
   cannot keep the editor waiting.
