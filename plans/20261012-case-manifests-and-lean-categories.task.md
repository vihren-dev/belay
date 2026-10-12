# Case folders and Lean file categories

Created 2026-10-12. Status: READY.
Decision: [ADR 0010](../docs/adr-0010-lake-builds-and-artifact-cache.md),
section 7. Accepted on 2026-10-12.

## Outcome

1. Every verification case is a folder with the project configuration file of
   the command line tool, `belay.toml`. Its first version names the schema,
   the contract folder, the migration, the
   candidate modules (`NextInterpretation`, `Proofs`, and any helper modules),
   the SQLite profile and the approval baseline when there is one. Tests keep
   the expected status (`VERIFIED`, `VIOLATED`, ...) in a `[test]` table of
   the same file, which the tool ignores. The case folder
   has the layout of a user's project (ADR 0010 section 7): in the task
   [Lake builds in the verifier](20261012-lake-builds-in-the-verifier.task.md),
   its candidate files become a proofs project. The commands do not read
   `belay.toml` yet; the format must be one they can read later.
2. Checked-in cases keep their places in `examples/`. Cases used only by
   tests are in `tests/cases/<case>/`. Today there are six checked-in cases:
   `add_column_then_table`, `table_then_column`, `missing_required_column`
   (refutation), `allowed_failure`, `application_keys/add_column_then_table`
   and `atuin`.
3. Tests and experiment scripts that run a case without changing it take its
   inputs from `belay.toml`, not from paths and profiles written in the test
   code. Tests that change a case first copy it, as today.
4. One shared reader loads and validates `belay.toml` files. A wrong or missing
   field is an error that names the file and the field.
5. A unit test puts every `.lean` file of the repository in exactly one
   category of ADR 0010 section 7: package, case, direct fixture or excluded.
   Until the verifier library moves under `packages/` (a later task), the
   package category also lists today's locations of package sources explicitly.
   A `.lean` file in no category, or in two, fails the test with its path and
   the categories.
6. No Lean file moves, and the verification results of all cases stay the same.

## Tests

- Unit tests of the reader: a valid `belay.toml`; each missing or wrong
  field, with the file and field named in the error; paths that leave the
  folder that holds the cases (`examples/` or `tests/cases/`) are refused.
  Paths may leave the case folder itself, because three cases share the
  contract in `examples/approved/` (owner decision, 2026-10-12).
- The category test of item 5, with deterministic fixture trees for a file in
  no category and a file in two categories, plus the real repository tree.
- A test that each checked-in case has a `belay.toml`, and that its
  expected status is the status the verifier reports. It runs in the existing
  Nix targets that already verify the examples, so it adds no new compile work.
- The existing suites (`cli_test.py`, `bundle_test.py`, `atuin_cli_test.py`,
  `proof_exporter_test.py`, `runtime_package_test.py`,
  `generated_inputs_test.py`, `test_application_keys.py`) pass with case inputs
  from `belay.toml`.

## Relevant source and constraints

- `conftest.py` (`example_factory`) copies examples from
  `runtime_root / "examples"`, so `belay.toml` files must ship in the runtime:
  `build-support/runtime.nix` copies the repository sources, and
  `build-support/sources.nix` selects them.
- Each Nix test target lists its input files in `build-support/tests.nix`. The
  `belay.toml` files and the reader must be in the inputs of every target that
  uses them, or the target cannot see them.
- `experiments/adr-0003-latency/cases.py` defines three cases in code and is an
  input of the `bundle` target (`tests/test_latency_frontend.py`). It should
  read the `belay.toml` files too, so a case is defined in one place.
- `application_keys` keeps its candidate in a nested folder,
  `application_keys/add_column_then_table`, and its contract in
  `application_keys/approved`; `belay.toml` must express that.
- Atuin uses profile 3.46.0; the others use 3.51.0. Atuin has three candidate
  helper modules.
- Lean files that are not cases or packages today: `tests/kernel_gate/*.lean`
  (the kernel suite compiles trusted and candidate copies separately on
  purpose), `tests/public_doc_inventory/InventoryFixture.lean`,
  `conformance/regressions/*/Regression.lean` (read by
  `conformance/regressions.py`), `tools/PublicDoc*.lean` (built by
  `build-support/default.nix` as `inventoryTools`), and
  `experiments/adr-0003-latency/bench/Main.lean`.
- The file is TOML: Python reads it with `tomllib`, and Nix can read
  it with `builtins.fromTOML` for the seed task.
- `verify` is deprecated in favour of `prepare` and `verify-bundle` (owner
  decision, 2026-10-12). Tests of `verify` still read the `belay.toml` files
  until they move to the two commands, in a separate change.
- CI times: record the baseline and each pull request's job times in the
  status file, and investigate a big increase before the merge (ADR 0010
  section 11).
