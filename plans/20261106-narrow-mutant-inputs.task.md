# Give each mutant suite only the Python modules and data that it reads (#330)

Created 2026-11-06. Status: open.
Audience: implementers and reviewers.
Progress: [status](20261106-narrow-mutant-inputs.status.md).
Inspected base: `tasks/publish-per-platform` plus the #328 fix (`knytyxux`), on `main` `1d74dd4e`.

## Present problem

The owner asked for a fix of #330 after the CI bugs. Every mutant suite of
`tests/nix_mutant_suites.json` gets `mutantInputs` of `build-support/tests.nix` as its
inputs: the inputs of the whole model suite (`modelInputs`) plus both Lean packages. Of
the last 80 first-parent commits of `main`, 26 ran all 12 suites again without a change
to a Lean file that the mutant build compiles. 14 of them changed only judge data or
frozen corpora, which no mutant test reads. The others changed test files, case modules
of other suites, proofs or the text package.

#328 (in this stack) lets a suite with an unchanged derivation reuse its accepted
report. With the present inputs, the derivation changes on nearly every commit, so the
reuse seldom applies.

Measured on the base of this task:

- The Python import closures of the 12 mutant test files have 48 to 82 local modules
  each, 161 together. `modelInputs` declares 270 `conformance/*.py` modules and
  the 5 frontend modules for every suite.
- The closure reads no data file of the repository: no `judge/` file, no
  `conformance/cases/*.json`, no `conformance/requirements-3.51.0.json`,
  `conformance/regressions`, `conformance/synthetic-workload`, Tcl script or Nix file.
  The authored cases are Python modules; native SQLite and the translation program come
  from the Nix tools and the runtime.
- `tests/mutant_guards_test.py` and `tests/restriction_registry_test.py` are in
  `mutantInputs`, but no mutant suite runs or imports them.

## Required outcomes

- Each mutant suite gets, as Python inputs, the shared harness files (`common`), its own
  test files and exactly the local modules in the import closure of those test files.
  A change to a Python module that is outside the closure of a suite and is not in
  `common` does not change the derivation of that suite.
- No mutant suite gets the judge claims, the judge files, the frozen corpora, the other
  data files of `modelInputs` or the two unused test files.
- The Lean inputs and the runtime stay as they are: both Lean packages without `.lake`,
  and the `conformance` runtime. See "Not in scope".
- The declared modules of each suite cannot drift from its imports: a check on the host
  fails, with the suite and the missing or extra modules, when a test file or module
  starts or stops importing a local module. The check runs in less than 10 seconds.
- `modelInputs` and the other suites do not change.

## Tests and acceptance

- A unit test compares, for each mutant suite, the declared modules with the import
  closure of its test files (the closure function of `tests/test_conformance_frontend.py`
  or a shared version of it). The failure message names the suite and the modules to
  add or remove.
- A Nix evaluation test reads the source tree of each mutant suite derivation and checks
  that it holds no `judge/` file and no `conformance/cases/` file, and that its Python
  files are exactly `common`, the suite's test files and the closure.
- Before the pull request, a smoke check imports each module of each suite's closure
  in the Nix source tree of that suite, with no other path. It finds a module-level
  import that the analysis misses. It does not run an import inside a function: only the
  analysis (which reads all import statements) and the CI run see those. It cannot find a
  module that the code loads by a computed name (no closure module uses `importlib` or
  `__import__` at the inspected base), and it does not run the tests. The status file
  records this check once; it is not a test. Only the CI run of the suites shows that a
  test reads nothing outside its inputs.
- The validation of #330 after the merge: the first `main` push that changes only judge
  data, a corpus, or a case module of one suite reuses the reports of the other suites
  (#328). The pull request says that this needs the first `main` runs.

## Key points for the implementer

- Nix cannot read Python imports, so the module list of each suite is data that Nix
  reads (for example a JSON file next to `tests/nix_mutant_suites.json`), and the unit
  test checks it. `tests/conformance_frontend.json` is the same pattern for the frontend
  modules. Module names map to `name.replace(".", "/") + ".py"`; `belay/sqlite/__init__.py`
  is a module file, and `conformance` has no `__init__.py`.
- `tests.mutant_sets` is a local test module in the closure of most suites; `tests/__init__.py`
  is already in `common`.
- `import_closure` follows imports inside functions too; keep that, because the mutant
  modules of the closure, such as `conformance/native_connection.py`, import local modules inside functions.
- `build-support/tests.nix` is 375 lines. Do not make it longer than needed; a helper that
  maps a suite name to its inputs keeps the `genAttrs` call short.
- The mutant tests run only on CI (`just test-mutants` overloads this machine). Local
  checks are the unit tests, the evaluation test and the collection above.

## Not in scope

- **Lean inputs.** The mutant build compiles only the import closure of
  `VerifierConformance.Classify` (293 of 900 Lean files). But the suites run the
  translation program of the `conformance` runtime, which Nix builds from the text
  package and the complete model package. So a change to any model Lean file changes
  the runtime and so every mutant derivation; a narrower Lean source list alone changes
  nothing. A narrower runtime needs a second Lake build of a reduced model and text
  package. That is a separate decision with its own cost, after the payoff of this task
  is measured.
- **Split of `functionMutants`.** Each extra suite is one more CI runner that restores
  the Nix store and builds the base model. The split is measured after this task and
  #328 are on `main`.
