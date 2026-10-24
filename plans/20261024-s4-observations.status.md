# S4 claim observation fixtures

Created 2026-10-24. Status: DONE for the observation fixtures and independent review; part 1 Nix evidence is pending.
This record tracks the nonvacuity checks of [the S4 task](20261024-surface-s4.task.md), outcomes 3, 5 and 6.

The work adds positive and negative observations to the existing claim fixtures
for table scans, EXISTS, count, IN, SUM, grouping and table-info queries. It also
checks why a unique lookup requires a single-column key without a filter.
The query error cases are covered by the parent task's shared query-case fixture.

The selected checks are `tests/surface_claims_test.py`, the model import inventory
and `tests/surface_layers_test.py`, with `requires_nix` excluded from diagnostic
local runs. The parent task owns the combined Nix gates and verdict for part 1.

## Progress

- 2026-10-24: added arbitrary-database applications of Empty and non-failure
  laws for scans, count, IN, SUM and table-info. EXISTS and NOT EXISTS each have
  row, empty and non-failure laws. Concrete instances exercise both sides of
  the row and empty equivalences. The grouping fixture checks both group and
  pairwise negative instances and non-failure. Composite and partial unique-key
  fixtures each permit two rows that one lookup matches.
- 2026-10-24: diagnostic commands cover `just dev-build`, the separate
  `lake build VerifierConformance conformance-runner` target, and the selected
  non-Nix tests above. Two initial fixture elaboration failures were corrected:
  existential list membership now stays explicit, and IN names the script's
  integer parameter list explicitly.
  The affected tests were repeated. Authoritative Nix evidence is pending the
  combined parent checks; these local runs are not evidence.
- 2026-10-24: independent review `20261024T122210Z-9791c4ab` has no findings.
  The observation fixtures and their review are complete.
