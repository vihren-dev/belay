# Status: move the Lean code into directories by division and team

Created 2026-11-10. Task: `20261110-ownership-reorganization.task.md`. DONE 2026-11-11.

## Relevant files

- `packages/*/lakefile.lean`: the module lists of the libraries.
- `tests/surface_support.py`: finds a surface test file by its name below `tests/surface`.
- `conformance/*_mutants.py`, `conformance/coverage_catalog.py`: the file of each mutant edit.
- `build-support/tests.nix`: the source files of the Nix suites.
- `docs/lean-simplification-goal.md`: the record of the line count.

## Done

- The move, on main `d9e10661`. `packages/` has 1,593 Lean files (1,194 before): 399 more files, from
  the division of files with declarations of more than one division or team. The 300 Lean files of
  `tests/surface` moved whole.
- A transitive reduction of the imports of the files that the move wrote: an import that another
  import of the same file gives is removed.
- Repairs by hand, each an `import` line or a text reference:
  - `tests/surface/Programs/Tests/ExecutionHelpers.lean` imports
    `Belay.Sqlite.Tooling.Conformance.ProgramQueries` for its `DecidableEq (Except ε α)` instance.
  - `{name}` became `{lit}` in two comments whose declaration is now in another module.
  - The change of #366 to `CounterexampleSearchBudget.lean` is applied to the moved file,
    `tests/surface/Tooling/Tests/CounterexampleSearchBudget.lean`.
- A `README.md` in each division directory and each team directory of the four libraries and of
  `tests/surface` (104 files; owner request, 2026-11-11). It tells in plain words which code belongs
  in the directory. The Nix sources of the packages include only `.lean` and `.toml` files, so the
  files change no package build.
- The judge is unchanged, so `integrity/judge.lock.json` is unchanged.
- Lean code lines (scc 3.7.0, the scope of `docs/lean-simplification-goal.md`, a local count): 93,451
  before the move, 94,728 after it, +1,277 lines (packages +1,323, tests -46). The new lines are the
  header lines of the 399 new files; the reduction of the imports removed lines.

## Check results

Only local runs exist. The first four checks ran before the change of #366 was applied to the one
moved test file; the four `just` commands ran on the final tree.

- Text check: passed.
- Declaration check: 37,460 declarations; 17,510 compared, with 197 `private` names mapped; no
  difference. The other declarations are those that Lean generates for each module (matchers,
  equation lemmas, numbered auxiliary proofs); a division of a file changes their names and number,
  so the check counts them and does not compare them.
- Order check: no import goes up.
- Placement check: no declaration is missing. Two `local instance` declarations of
  `SqlDocInputs.lean` are in the team of their users, because a `local` declaration is visible only
  in its file.
- `just test-full`: all 17 suites passed (1,985 tests; 348 of them in the surface suite).
- `just verdict`: 59 corpora, 5,768 AGREE and 2,100 MODEL_UNSUPPORTED, no disagreement.
- `just test-nix`: 91 passed. `just test-scheduled-checks`: 53 passed.

## Known gaps

- `conformance/regressions/injected-literal-corruption/Regression.lean` names moved modules; no test
  compiles it.
