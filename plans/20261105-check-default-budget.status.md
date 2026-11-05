# Status: the launch examples answer at the default budget

Created: 2026-11-05. Status: IN PROGRESS.
Task: [20261105-check-default-budget.task.md](20261105-check-default-budget.task.md).
Issue: #317. Design: ADR 0031, D1.

Sources: `packages/belay/Belay/Sqlite/CertificateAuditCache.lean` (new),
`CounterexampleCertificate.lean` (`auditDependencies`), `CheckOperation.lean` (`check`).

## Progress

- 2026-11-05: task and status files.
- 2026-11-05: the audit record (`withAuditCache`, `AuditCache`; `auditDependencies` reads and
  extends it; `check` opens one for each operation). The fixture `CounterexampleReadable` checks
  the claim of #316 with the default budget; the new fixture `CheckDefaultBudget` checks the
  rebuild with three sessions at the default budget and the audit with a record
  (`tests/surface_check_default_budget_test.py`, suite `surfaceChecks`). Tests run, on the tree
  with this change and the change of #318: `surface_check_readable_test`,
  `surface_check_default_budget_test`, `surface_check_command_test`, `surface_search_test`,
  `surface_sampling_test`, `surface_counterexample_test`, `surface_inference_test`,
  `surface_replay_test`, `surface_rebuild_test`, `surface_automatic_test`,
  `surface_s6_check_programs_test`, `surface_s6_not_blocked_test`, the five
  `surface_editor_*` tests of `surfaceChecks`, `surface_automatic_editor_test`,
  `surface_s6_check_editor_test`.
