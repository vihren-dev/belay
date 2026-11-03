# Lake builds the parser library: task status

Date: 2026-11-03. Status: OPEN.
Audience: the implementation team.
Task: [Lake builds the parser library](20261103-parser-built-by-lake.task.md).
Specification: [ADR 0023](../docs/adr-0023-parser-built-by-lake.md).
Source baseline: main `5cdbc536`.

Relevant files: `packages/belay-sqlite-text/lakefile.lean`, `packages/belay-sqlite-text/c/`,
`parser/`, `build-support/parser-library.nix`, `build-support/default.nix`,
`build-support/lean-package.nix`, `build-support/sources.nix`, `build-support/tests.nix`,
`shell.nix`, `.envrc`, `justfile`, `tests/surface_support.py`, `tests/sql_file_support.py`,
`tests/test_source_identity.py`, `tests/dev_loop_test.py`, `tests/nix_suites.json`.

## Progress

- 2026-11-03: task specified; ADR 0023 accepted by the owner.
- 2026-11-03, slice 1 (committed generated C): `parserLibrary.generated` in
  `build-support/parser-library.nix` builds the tree of `parser/generated/` (one folder per grammar
  named by the 16 digits of the symbol prefix, `library_grammars.inc`, `library_metadata.inc`,
  `manifest.json` with prefix, folder, release source folder and compile flags). Lemon writes the
  store path of the grammar derivation into `#line` directives; the tree removes that path, so the
  committed files do not depend on a store hash or a platform. `just parser-sources` writes the tree
  into the checkout. The suite `parserSources` (`tests/parser_generated_test.py`, entry in
  `tests/nix_suites.json`, definition in `build-support/tests.nix`) compares the tree with the
  committed files. Compile flags in the manifest: `-O1 -std=c99 -fPIC -fvisibility=hidden` and the two
  SQLite options of D2 (kept in the manifest so that Lake and Nix read one copy).
- One-byte failure record (D5, 2026-11-03): one byte of `parser/generated/7c0495821ae35f29/token_names.inc`
  changed (byte 101, replaced by `x`); `nix-build build-support/default.nix -A tests.parserSources`
  failed with exit 1 and the message `parser/generated differs from the generation (run `just
  parser-sources`)` followed by `7c0495821ae35f29/token_names.inc: the committed bytes differ from the
  generation`. The byte was restored; the suite passes (2 tests) on the commit. Log:
  `build/agent-logs/ps-suite-onebyte.log`.

## Slice 1 checks (Nix)

- `just test-full` on the slice-1 tree: test reports `/nix/store/nphbipyfkf0z9h3xqxa0kfw6sw7nix5z-sqlite-verifier-test-reports`; suite `parserSources` output `/nix/store/khrd6dnp0l654rcc8pcasi4awxvgrkca-sqlite-verifier-test-parserSources-1` (2 passed).
- The verdict of slice 1 is covered by the verdict of slice 2 (the working copy moved on before `just verdict` ran).

## Slice 2: Lake compiles the parser library

- Lake compiles the C of `parser/` in `packages/belay-sqlite-text/lakefile.lean` (`extern_lib parserLibrary`), with the headers of `parser/c-headers`; `BELAY_PARSER_LIBRARY` no longer exists in the lakefiles, the Nix builds and the surface tests. The dev loop (`shell.nix`, `tests/dev_loop_test.py`) still uses it until slice 3.
- The Nix workspaces get `parser/` through `extraSources`; `build-support/sources.nix` has the component `parser`; `tests/test_source_identity.py` covers it, including a derivation-level test.
- `textPackage` builds with `withoutSystemCompiler`: the PATH of Lake has no `cc`, `gcc` or `c++`, and `clang` is the one of the Lean toolchain. Output `/nix/store/b04g7k4rlm1j94qaxkfabniqkx4jz0vb-belay-sqlite-text-0.1.0`.
- New test `tests/surface_parser_link_test.py`: no program or library depends on a parser library; the objects call only the ten declared C functions.

## Slice 2 checks (Nix)

- `just test-full` on the slice-2 tree: test reports `/nix/store/pc0d752pw72ypm78h3y4f640j0mivws9-sqlite-verifier-test-reports`.
- `just verdict`: `/nix/store/3z1dl2rs0zvll4wnrv1vl86vqwnqcdal-sqlite-verifier-verdict` (every claimed corpus as claimed).
- Predictions: `/nix/store/8cpzncq4dixkfx35gaax3p3axxlqq0wz-sqlite-verifier-predictions` is byte-identical
  (`diff -r`, no output) to trunk's `/nix/store/y8q8nsgwz1nnq5xw3g4x8qnhb5wcj78p-sqlite-verifier-predictions`
  (main `5cdbc536`): all 55 claimed corpora and the synthetic workload.
- Reviews of slice 2: the findings of `68b5db89`, `a1be0988` and `fafe0294` are resolved; `4556416a` has none.

## Slice 3: the shell, the dev loop, stale text and ADR amendments

- 2026-11-03: the work moved from a subagent to the main session (owner request).
- `shell.nix` imports only `build-support/lean-toolchain.nix` and sets `BELAY_DEV_SHELL=1`; `.envrc`
  watches only the files of the shell's packages and the toolchain; `_dev-shell-warning` tests
  `BELAY_DEV_SHELL`.
- `tests/dev_loop_test.py` finds the shell by `BELAY_DEV_SHELL`, builds from a clean
  `.lake/build` of the text package, finds no missing-header or implicit-declaration message, checks
  the objects' calls with `tests/parser_object_symbols.py` (shared with the Nix link test), and
  prints the metadata with `lake lean`. Local run (not evidence): 1 passed.
- Stale text (D4): `grammarAdvice`, the `TranslationProgram.lean` message, `conformance/progress.py`,
  the `textPackage` comment, `build-support/README.md`, the `conformance-build` comment and the team
  guide. Amendments dated 2026-11-03 in ADRs 0007, 0010, 0016 and 0020.
- Tests of the commits: `tests/dev_loop_test.py`, `tests/test_ci_scope.py`, `tests/test_nix_test_targets.py`,
  `tests/test_test_ownership.py`, `tests/docs_test.py`, `tests/test_source_identity.py`,
  `tests/test_source_identity_derivations.py`.

## Slice 3 checks (Nix)

- `just dev-build` passed; then `just test-full`: test reports `/nix/store/n8jmb7h6yyilv4x8x3h7r3i33d86k6r4-sqlite-verifier-test-reports`.
- `just verdict`: `/nix/store/19gzjajw2kmaadjrdvgll67il2hnx54w-sqlite-verifier-verdict`; predictions
  `/nix/store/bm4lfd3ys7a1nckbl99vsn3q8j88hl8g-sqlite-verifier-predictions` are byte-identical to trunk's.
- Reviews: `92f127b4` has no findings; the one finding of `f7561cb3` (the status named the ADR amendments one
  commit early) is rejected with that reason.
