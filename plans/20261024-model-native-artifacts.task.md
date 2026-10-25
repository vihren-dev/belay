# Reuse the model's compiled native artifacts

Created 2026-10-24. Status: DONE on 2026-10-25.
Audience: implementers and reviewers.
Status file: [status](20261024-model-native-artifacts.status.md).
Specifications: ADR 0010 package builds; ADR 0016 package boundaries;
the owner's request to reduce measured development costs during ADR 0017.

## Present problem

A surface-only S6 Nix build compiled 589 `Belay.Sqlite.Model.*:c.o` targets.
Its model derivation was already cached and did not rebuild. The installed
model package contains 589 `.olean` files, but no native object or shared-library
files. The text package builds model native artifacts in its dependency copy;
the next surface build repeats that work. The status file identifies the log
and outputs. This contradicts the intended reuse described in
`build-support/lean-package.nix` and adds measured work to each surface edit.

## Required outcomes

- Native model artifacts needed by the text and surface packages have a cached
  producing derivation. Consumers can replay them with the pinned Lake build.
  A surface-only source edit must not compile unchanged model C objects again.
  This applies when the surface imports a model module outside the translator's
  narrower import closure, as the S6 build does.
- Model source changes invalidate the affected producer and consumers correctly.
  An unchanged input reuses the producer. Source filters retain the existing
  model, text and surface boundaries.
- Use the existing Nix and Lake package mechanism. Keep the change limited to
  this demonstrated missing-artifact problem. SQL behavior, public declarations,
  parser behavior, frozen evidence and judge claims remain unchanged.
- Installed text and surface packages retain the shared libraries needed to load
  and execute their imports. Preserve Linux and Darwin library handling; Linux
  acceptance does not establish an unrun Darwin build.
- Record the before/after native compilation counts and the resulting producer
  artifacts. Report build time and output size if measured, without a promised
  percentage improvement or a flaky timing threshold.

## Tests and acceptance

- Add a bounded regression using existing package/build tests where practical.
  It must detect the observed lost-native-artifact behavior, rather than only
  checking a target-list string. Include subprocess timeouts.
- Demonstrate a real consumer-only edit against an already built producer,
  with build logs showing no unchanged model C-object compilation. Verify that
  a model input edit changes the producer derivation. Retain the exact commands,
  edited input and output paths as acceptance evidence.
- Run the relevant package replay, layer and Nix-target checks. Exercise installed
  imports and the existing translation and surface fixtures under Nix.
- One slice: after source review, run `just test-full` and `just verdict`.
  Compare all frozen predictions with the accepted base; contents must match.
  At task completion run `just test-nix` and `just test-scheduled-checks`.
  Do not run broad local mutant suites for this build-only change.
- Each source commit has independent review. Status records cite Nix acceptance;
  local probes remain diagnostic evidence.

## Important constraints and ownership

`build-support/default.nix` selects producer targets. `lean-package.nix` copies
required package outputs into the workspace, then installs the current package
and selected dependency shared libraries. Lake's native artifacts and traces
must remain replayable after this copy; their mere presence is insufficient.
Inspect `packages/belay-sqlite-model/lakefile.toml`, the text/surface lakefiles,
`tests/lean_packages_test.py`, `tests/dev_loop_test.py`, and existing Nix tests.
The implementer chooses the smallest correct producer/facet change.

Work in a separate jj workspace based on the accepted S6 checkpoint or its
reviewed successor. Own the relevant build-support producer configuration and
native-reuse tests. S5 owns its surface manifest/cold-evaluation correction in
`default.nix`; preserve that independent change during integration. S6 and FK
proof files stay at rest. Coordinate before changing shared package manifests.
No more than two heavy process groups may run across all agents. Keep at least
10 GiB free on both filesystem guards. Do not collect the Nix store without
owner permission.
