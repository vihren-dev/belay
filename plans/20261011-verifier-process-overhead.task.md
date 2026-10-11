# Remove process overhead from prepare and verify-bundle

Created 2026-10-11. Status: DONE ([PR #86](https://github.com/vihren-dev/sqlite-verifier/pull/86); owner review of R8 pending).
Owner request: apply the orchestration fixes from the `prepare` latency
experiment that do not depend on ADR 0010 (PR #76,
`experiments/prepare-latency/README.md` on branch `adr/0010-lake-cache`).
They also shorten the `bundle`, `cli` and `atuin` Nix suites, which run these
commands in each test.

## Outcome

1. A command reads the import header of each distinct Lean source text once.
   `lean --deps-json` still parses every header, on the trusted side too.
   Results are kept for the life of the process, keyed by the toolchain and
   the source bytes, so the second read before each compile is not a new
   process. Each discovery step reads all pending headers with one
   `lean --deps-json` call. Discovery order, the dependency graph, compile
   order and every error message stay the same.
2. `run_process` notices the exit of a child process when it happens. The
   deadline, the kill of the whole process group at the deadline and the
   `TimeoutExpired` result stay the same.
3. A command locates the runtime once and passes it to `generated_inputs`.
   `validate_libraries` scans a set of library roots once per process; a
   failed scan is not remembered.
4. Parallel compilation of candidate modules is not part of this task: ADR
   0010 gives it through Lake.

## Tests

- Unit tests: a batch of headers gives the same import lists and the same
  error messages (with the real source path) as one call per file; the cache
  does not run Lean again for the same bytes; different bytes are parsed.
- `run_process`: a fast child returns without the polling delay; a child that
  passes its deadline raises `TimeoutExpired` and its process group is killed.
- `validate_libraries`: a second call for the same roots does not scan; a
  conflict is still refused on every call.
- The existing end-to-end suites (`bundle`, `cli`, `atuin`, `kernel`) and host
  source tests pass without changed expectations.
- CI: before and after times of the `bundle`, `cli` and `atuin` suites.

## Key points

- `migration_check/source_closure.py` (`imports`, `lean_process`,
  `discover_sources`), `migration_check/process.py` (`run_process`),
  `migration_check/runtime.py` (`Runtime.locate`, `validate_libraries`),
  `migration_check/inputs.py` (`generated_inputs`), and the callers in
  `prepare.py`, `bundle.py` and `cli.py`.
- Python 3.14's `Popen.wait(timeout=...)` polls with sleeps of up to 50 ms.
- A header error names the file. A batch uses temporary copies, so the
  message must name the original source path again.
- `lean --deps-json FILE...` returns one record per file, in argument order,
  and exits 0 when a header has errors.
- `verify-bundle` is trusted: headers stay parsed by Lean, not by Python.
- Text follows the writing rules in `AGENTS.md`.
