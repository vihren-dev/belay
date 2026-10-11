# Verifier process overhead status

Created 2026-10-11. Status: IN PROGRESS.
Task: [20261011-verifier-process-overhead.task.md](20261011-verifier-process-overhead.task.md).

## References

- Experiment: `experiments/prepare-latency/README.md` on branch
  `adr/0010-lake-cache` (PR #76).
- Code: `migration_check/source_closure.py`, `migration_check/process.py`,
  `migration_check/runtime.py`, `migration_check/inputs.py`,
  `migration_check/prepare.py`, `migration_check/bundle.py`,
  `migration_check/cli.py`.

## Baseline

Experiment (Linux, local, medians): Atuin `prepare` with an empty workspace
11.69 s, of which 1.71 s in 26 `lean --deps-json` runs; Atuin
`verify-bundle` 6.62 s; small `prepare` 3.20 s; small `verify-bundle` 2.13 s.
The library scan takes 0.09 s and runs three times per command.

CI suite times before this task (the last run that executed each suite):

| Suite | Linux | macOS |
| --- | --- | --- |
| `bundle` (run 38134307051) | 170.8 s | 325.2 s |
| `atuin` (2026-10-10) | 164.6 s | 152.2 s |
| `cli` (2026-10-10) | 83.5 s | 59.3 s |
| `kernel` (2026-10-10) | 57.2 s | 56.0 s |

## Progress

- 2026-10-11: task and status files created.
- 2026-10-11: `run_process` waits with a blocking wait and a deadline timer
  (`wait_with_deadline`). Tests check the blocking wait, the stopped timer and
  the kill of the whole process group.
- 2026-10-11: commands locate the runtime once and pass it to
  `generated_inputs`; `validate_libraries` remembers successfully scanned
  resolved roots (`VALIDATED_LIBRARY_ROOTS`).
- 2026-10-11: header reads: `migration_check/lean_headers.py` reads all new
  headers of a discovery step in one `lean --deps-json` process and keeps
  each result per toolchain, libraries and source bytes. Errors name the real
  source file. `tests/test_lean_headers.py` compares with the pinned Lean.
  Fixed an order regression: an invalid profile is again checked before the
  runtime is located (found by `tests/test_latency_frontend.py`).
- 2026-10-11: sandboxed `bundle` (69), `atuin` (12), `cli` (16) and `kernel`
  suites pass. Local benchmark (5 interleaved runs, medians, quiet host),
  runtime of main against this branch:

  | Command | Before | After |
  | --- | --- | --- |
  | small `prepare` | 3.14 s | 2.03 s |
  | small `verify-bundle` | 1.93 s | 1.35 s |
  | Atuin `prepare` | 11.71 s | 9.64 s |
  | Atuin `verify-bundle` | 6.63 s | 5.47 s |

  Review findings R8 (owner review of `prepare.py` and `bundle.py`) are
  deferred to the owner in the pull request. Next: PR and CI times.
