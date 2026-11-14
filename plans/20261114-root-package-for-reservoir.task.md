# Task: a root Lake package, so that Reservoir can index Belay, and version 0.2.0

Created 2026-11-14 (status: `20261114-root-package-for-reservoir.status.md`). Owner request,
2026-11-14: release version 0.2.0 and publish Belay on [Reservoir](https://reservoir.lean-lang.org).
Status: OPEN.

## Problem

Reservoir indexes a repository only if a file `lake-manifest.json` is in its top-level directory,
and it indexes only the package of that directory
([inclusion criteria](https://reservoir.lean-lang.org/inclusion-criteria)). This repository has no
lakefile and no manifest in its top-level directory. The package that users require, `belay`, is in
`packages/belay`, and a user must write a `git` requirement with `subDir = "packages/belay"` and
`rev = "main"` (`README.md`, "Install"). The package has no `version`.

The tags `v0.1.0`, `v0.1.0-rc.1`, `v0.1.1` and `v0.1.2` are releases of the removed verifier
product ([ADR 0021](../docs/adr-0021-remove-the-verifier-product.md)). Lake's default pattern for
version tags ("`v`, then a digit") matches all four, so Reservoir would list them as versions of
Belay.

The layout under `packages/` stays. Its reasons are still valid: the model is a package of its own
(ADR 0006), the folder of a Lean file decides how it is built (ADR 0010, section 7), nothing below
the surface imports it (ADR 0016, D2), and each Nix workspace holds only package folders (ADR 0023,
fact 8).

Owner decisions, 2026-11-14:

1. The root package is thin. It has the name `belay` and requires the surface package by the path
   `packages/belay`. The surface does not move.
2. The surface package gets a new name, because the root has the name `belay`. Lake 5.0 accepts
   two packages with the same name when the requirement has a different name, but this behaviour
   is not documented, and `belay-sql-check` identifies packages by name. The new name is
   `belaySurface`, after the word that ADR 0016 uses for this package.
3. The root package has one module of its own that imports `Belay`, so that a build of the root
   package builds the library.
4. The version tags of the root package start at `v0.2`. The old tags stay in the repository.
5. The instructions for users (the root `README.md`, the README of the example and the skill
   template) show the requirement on the repository root. The example `examples/table-rebuild`
   keeps its path requirement on `packages/belay`.

## What must be true when the task is done

### The root package

- The top-level directory has a `lakefile.toml` and a `lake-manifest.json`. The package has the
  name `belay`.
- `lake reservoir-config` in the top-level directory reports the version `0.2.0`, the license
  `MIT`, a description, keywords and the README `README.md`.
- Of the tags `v0.1.0`, `v0.1.0-rc.1`, `v0.1.1`, `v0.1.2`, `v0.2.0` and `v1.0.0`, the version tags
  of the package are `v0.2.0` and `v1.0.0` only.
- `lake build` in the top-level directory, with no target, builds the library `Belay` and its
  shared library, and prints no warning about default targets.
- A Lake project that requires `belay` from the repository root, with no `subDir`:
  - compiles a module that imports `Belay`, defines a schema with `db!` and a script with `sql`,
    and runs `#sql_check`, with the same answer as in a project that requires `packages/belay`;
  - runs `lake exe belay-sql-check` with the same report.
- A project that requires `packages/belay` by path or with `subDir` still builds. The surface
  package stays a complete package that Lake can build from its own folder.

### The surface package

- The package of `packages/belay` has the name `belaySurface`. Its library `Belay`, its modules,
  its executable `belay-sql-check` and its requirements do not change.
- No caller, test or document uses a file name that comes from the old package name (for example
  `libbelay_Belay.so`).
- The model package, the text package, the conformance runner and the judge's subject do not
  change. `integrity/judge.lock.json` does not change.

### Documents

- `README.md` ("Install"), `examples/table-rebuild/README.md` and
  `skills/belay/templates/lakefile.toml` show the requirement on the repository root with the
  release tag: no `subDir`, and `rev = "v0.2.0"`. They also show the Reservoir form of the
  requirement if Lake resolves it for a package that Reservoir has indexed; the README says that
  this form works only after Reservoir lists the package.
- `packages/belay/README.md` and `skills/belay/SKILL.md` agree with the new names and paths.
- ADR 0010 (section 7), ADR 0016 (D3) and ADR 0023 (the text on a `git` requirement with
  `subDir`) get dated amendments that describe the root package, its module and the new name.

## Tests

All tests have timeouts.

- **The root requirement, end to end.** A new test in the surface suite makes a consumer project
  that requires the root package by path, from a copy of the layout that has the root lakefile,
  the root manifest and the root module. It builds a module with a `db!` schema, an `sql` script
  and a `#sql_check` whose answer is `false`, pins the answer, and runs `lake exe belay-sql-check`.
  The Nix sandbox has no network, so the test uses a path requirement; a `git` requirement on the
  root differs only in the folder that Lake clones into.
- **The root build.** A test runs `lake build` with no target in that layout, and requires exit
  code 0, no warning, and the shared library of `Belay` in the output.
- **The package data.** A test runs `lake reservoir-config` in a temporary git repository that
  has the root lakefile and the six tags above, and pins the name, the version, the license and
  the version tags.
- **The category test.** `tests/test_lean_categories.py` places the root module in exactly one
  category, with a rule that matches only that file.
- **Existing suites.** The surface suites, `tests/test_source_identity.py`,
  `tests/surface_layers_test.py` and `tests/test_nix_test_targets.py` pass with the new name.
- At the end of the task: `just test-full`, `just verdict`, `just test-nix` and
  `just test-scheduled-checks`, as `CLAUDE.md` gives them.

## Points that need care

- **Measured on 2026-11-14 in a prototype** (jj change `mxzxnpzq`, not for merge): the thin root
  with the renamed surface builds; a consumer that requires the root runs `#sql_check` through the
  native parser and finds `belay-sql-check`; `just dev-build` passes. The rename rebuilds all 316
  surface modules once, because the build traces contain the package name. No Nix file, CI
  workflow or justfile recipe names the Lake package. `tests/surface_support.py` is the only file
  that names the surface's shared library.
- **A TOML root cannot name a target of a required package as a default target.**
  `defaultTargets = ["belaySurface/Belay"]` fails with "package 'belay' has no target". An empty
  library with `needs` builds nothing. This is the reason for the root module (decision 3). The
  root lakefile must stay TOML or get its own category rule: a root `lakefile.lean` is a Lean
  file in no category.
- **The name of the root module.** It must not be `Belay` or a module below it, because the
  library `Belay` of the surface owns those names. A user must not need to import it.
- **The root build folder.** `lean_libraries` in `tests/runtime_fixtures.py` reads
  `<runtime_root>/.lake/build/lib/lean` as the folder of the conformance runner. In a local run
  the runtime root is the repository root, where the root package now writes its build output.
  The two must not be confused, and `.gitignore` already excludes `.lake/`.
- **Test runtimes.** `installed_layout` in `tests/sql_file_support.py` and `surfaceRoot` in
  `build-support/tests.nix` hold package folders only (ADR 0023, fact 8). The root files and the
  root module must reach the layout of the new tests, and `build-support/sources.nix` must give
  them a source identity, without a change to the identity of the packages.
- **Old build output.** After the rename, `packages/belay/.lake/build/lib` of an existing
  workspace still holds `libbelay_Belay.so`. A local test that names the old file loads old code
  and does not fail.
- **The alias.** Lake does not compare the name of a requirement with the name of the required
  package. So `name = "belay"` with `path = "…/packages/belay"` in the example and in the test
  helpers still resolves after the rename. Replaced names are not kept
  (`CLAUDE.md`, "Replaced code"): use the new name where a file names the surface package.
- **`belay-sql-check`.** It finds packages by name (`packagesNamed`) and SQL files by package
  root (`sqlPackageRoot` in `SqlFileSource.lean`). Check both with the root package in the
  workspace.
- **Reservoir** runs `lake build` on the default branch and records a failed build without
  removing the package from the index (read from Reservoir's indexer on 2026-11-14, not
  observed). A first build takes about 7 minutes on 8 CPUs.

## Not in this task

- The tag `v0.2.0` and the GitHub release. The owner creates them, or asks for them, after the
  pull request is on `main`. Reservoir then needs about one day to list the package.
- The check of the published instructions from a clean machine with elan (launch plan).
- A release workflow and binary archives.
- Separate Reservoir packages for the model and the text package.
