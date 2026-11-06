# Status: record the provenance of each test execution (#332)

Created: 2026-11-06. Status: DONE (2026-11-06).
Task: [20261106-test-provenance.task.md](20261106-test-provenance.task.md).
Issue: #332. Stacked on the #330 fix.

Sources: `tools/observability_pytest.py`, `tools/observability_nix.py`,
`tools/observability_logs.py`, `tools/observability_spool.py`, `docs/test-observability.md`,
`experiments/observability/README.md`.

## Progress

- 2026-11-06: task and status files.
- 2026-11-06: review of the task file: three R19 findings (shared harness files are suite inputs,
  ADR 0028 recovery of cached results, the local commit is a snapshot), fixed by wording.
- 2026-11-06: `tools/observability_provenance.py` builds the metadata; `tools/observability_nix.py`
  imports only executions that started during the command, with the metadata and the suite of the
  output, and recovers failed builds through a staging spool. ADR 0028 is amended;
  `docs/test-observability.md` lists the fields and the query. The Nix derivations of
  `testReports`, `scheduledTestReports` and `developmentTestReports` are unchanged. Tests run:
  `tests/test_observability_provenance.py` (new), `tests/test_observability.py`,
  `tests/test_observability_identity.py`, `tests/test_recipe_limits.py`, `tests/docs_test.py`.
- 2026-11-06: review: one must (a failed link farm prints no path, so the suites that passed in
  it were lost) and two shoulds (wall-clock test, file length), fixed: after a failed `nix-build`
  the runner queries the outputs of the derivations and their direct inputs. Tests run: the new
  integration test builds a link farm with a passed and a failed suite (it fails without the
  fix), the provenance tests with fixed times, `tests/test_observability.py`.
- 2026-11-06: DONE. On the top commit, after `just dev-build`: `just test-full`, `just verdict`,
  `just test-nix` and `just test-scheduled-checks` pass. The mutant suites were not run locally.
