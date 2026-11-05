# The launch examples answer at the default budget

Created: 2026-11-05. Status: OPEN.
Source: issue #317 ("The default sql.checkBudget does not find the launch example's
counterexample on Linux"). Design: [ADR 0031](../docs/adr-0031-fast-sql-check.md), slice 1 (D1).
Audience: the team.

## Observable behavior

With the default `sql.checkBudget` (100000), on x86_64 Linux with `lake lean`:

- `#sql_check uniqueEmail succeeds where noDuplicateEmails` (the claim of #316 and #317) is
  `false`, with the counterexample `'a'`, `'A'`.
- The rebuild claim of the #317 comment,
  `#sql_check requireNameWrongEnforced preserves allSessions with (db := sample)` with two
  customers and three sessions in `sample`, is `false`.

The certificate audit (`auditDependencies`) gives the same result for every expression as
before. Inside one checking operation, it does not walk again a constant whose closure it has
already accepted with the same exclusions. The default budget is not changed.

## Tests

- `tests/surface/CounterexampleReadable.lean` checks the claim of #316 with the default
  budget (no `set_option sql.checkBudget`), with the same text and replay as before
  (`tests/surface_check_readable_test.py`).
- A new fixture case checks the rebuild claim with three sessions at the default budget.
- A fixture checks the audit with the cache: inside one operation, after the audit has
  accepted a lemma, a theorem that uses the excluded declaration through that lemma is still
  rejected; a record made with other exclusions is not used.
- The existing surface check suites give the same results.

## Tricky points

- Failed candidates run in `attempt`, which restores the elaboration state, environment
  included. A record kept only in the environment would be lost with each failed candidate;
  the accepted set is a reference that the environment extension holds.
- A speculative attempt can add a declaration, discard it, and a later attempt can add
  another declaration with the same name. Only constants of the environment at the start of
  the operation are recorded.
- A constant is accepted relative to the excluded declarations; the record applies only to
  audits with the same exclusions. Locals are not recorded: constants are closed terms.
- Parallel elaboration: the extension state is local to the environment branch
  (`asyncMode := .local`).
- The issue's macOS observation (the first example answered `false` there at the default
  budget) cannot be reproduced here; the fix removes repeated work, so it does not depend on
  the platform's heartbeat count.
