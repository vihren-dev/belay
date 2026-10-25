# Model native artifact reuse status

Created 2026-10-24. Status: DONE on 2026-10-25.
Task: [required outcomes](20261024-model-native-artifacts.task.md).
Owner: `text_build_boundaries`, assigned after clean task review.

## Observed baseline

The accepted S6 success-unit Nix log is
`/home/codex/work/sqlite-verifier-s6-execution/build/agent-logs/s6-success-unit-nix-surface-1.log`.
It contains 589 `Built Belay.Sqlite.Model.*:c.o` lines. The Nix build requested
only surface/test derivations; the model derivation was already present.

- Model derivation: `a6nbc3p0sq4y9pkjha8g9ryvvl8xfdrq-belay-sqlite-model-0.1.0.drv`.
- Model output: `/nix/store/c1mfzn508n01i8wkjzqk3vb2srp41k90-belay-sqlite-model-0.1.0`.
  Read-only inventory: 589 `.olean` files, zero `.o` files, zero `.so` files.
- Text output: `/nix/store/bjpvjr0h5yhyjrhwfz1y39mxz56smcbn-belay-sqlite-text-0.1.0`.
  Its installed library directory includes copied model shared libraries.
- Accepted base: S6 `e804dddeaf615ab23a135a7333c4fe57d86b79bd` on PR #248.
- Frozen predictions: `/nix/store/wbpwn1x38fyn3l0g00wg5m011n6ajwq4-sqlite-verifier-predictions`;
  53 files, 7372 cases. Rooted in S4's `build/accepted-cte-artifacts`.

These are observations from an existing Nix gate, not acceptance of a fix.
Task commit `e2a49629` has independent review `20261024T213358Z-e2a49629`: zero must and zero should findings. Root separately verified the cited log count and artifact inventory.

Isolated workspace `model-native-artifacts` starts at accepted S6 `e804ddde`.
Only this task, its status and the named clean review were copied from planning
`fe82c004`. The shell configuration is byte-identical to the accepted S6
workspace and is allowed under the owner's standing authorization. S6 and FK
workspaces remain at rest. Carry commit `02ea4fbb` received independent review
`20261024T213517Z-02ea4fbb`: zero must and zero should findings.

## Producer and replay change

`build-support/default.nix` adds the `shared` facet for each existing model
library. Pinned Lake 4.34.1 builds the complete library's native objects and
their traces through that facet. The copy/install mechanism and platform
library handling are unchanged. `tests/lean_packages_test.py` now requests
those actual facets and requires no compiled targets during replay.

The first Nix producer output is
`/nix/store/mxdz0srr5c8rp8h4k8l5r1b8559fs30f-belay-sqlite-model-0.1.0`.
It contains 589 `.olean` files, 589 `.c.o.export` files and both model shared
libraries under `.lake/build/lib`. Its initial build compiled 589 model C
objects. It took 261 seconds on this host with Nix settings `max-jobs = 1`
and `cores = 2`.
The sum of installed regular-file sizes changed from 279553010 to 333878087
bytes. These observations do not promise a timing ratio on another machine.

Nix package replay passed all three checks in
`/nix/store/2g962nijmc1fl3s99hl6d9j2yp7l1058-sqlite-verifier-test-packages-1`.
The model's native facets replayed with no compiled targets. Exact commands
and logs are in `build/agent-logs/native-focused-gates.sh` and
`native-{producer,packages}.log`.

## Focused acceptance and real source edits

The full installed surface suite passed all 81 checks in
`/nix/store/ypfqx5qns8bl8c16yjw36syqb5d80gwh-sqlite-verifier-test-surface-1`.
This includes translation, layer boundaries, S6 production execution and its
foundations prototype. The text/surface build log contains zero compiled model
C-object targets; the observed baseline had 589. Linux imports and execution
passed. Darwin's existing library handling is unchanged but was not executed.

The same replay regression against the exact old model output fails in Nix:
Lake tries to create its missing `ByteText.c.o.export` in the read-only store.
The expected failing derivation is
`/nix/store/wywbh555d4jr3smb2wix6ikvmyi0aw70-sqlite-verifier-test-packages-1.drv`.
The bounded command is `nix-build build/agent-logs/native-old-regression.nix
--no-out-link --option sandbox true --option sandbox-fallback false
--extra-experimental-features 'nix-command flakes'`; the exact-path failure is
retained in `native-old-exact.log`. The verifier requires this failure rather
than accepting an unrelated evaluation error.

`build/agent-logs/native-reuse-probe.py` copies package and parser sources into
`build/native-reuse-source-2`, where Nix applies the existing filters.
The unmodified copy has identical model, text
and surface derivations. It appends one comment to
`packages/belay/Belay/Sqlite/ExecutionSuccess.lean`, then builds the real surface
derivation. That build compiled the edited module and zero model C objects.
It took 18.55 seconds and produced
`/nix/store/jvi65f5cgr09f5y5i7c7q74da7fxncgg-belay-0.1.0`.
The model and text derivations stayed unchanged. Building the unchanged model
again reused its output. A subsequent comment appended to
`packages/belay-sqlite-model/Belay/Sqlite/Model.lean` changed the model, text
and surface derivations; this deliberately changed model was not built.

`native-reuse-probe.json` retains every command, exact edited input, derivation
identity, output and elapsed time. The model derivation changes from
`zz0vyz8agkrh9h5dw89lfy43s5vcnwqp-belay-sqlite-model-0.1.0.drv` to
`x2ghcz70qzya0blgk1vyl6qc7pwpn900-belay-sqlite-model-0.1.0.drv` only after the
model edit. The surface-only edit changes its derivation from
`sdjxm2dnjhwcsnk1f9vx7dbzzak31v0d-belay-0.1.0.drv` to
`b0paz2vrd5flklwfl31zb2x0k4x6fxdx-belay-0.1.0.drv`.
The private-source probe's initial path-coercion failure is retained in
`build/agent-logs/initial-native-original-identities.log`. Correcting that probe
required no production change.

Source commit `df404e7c` received independent review
`20261024T215327Z-df404e7c`: zero must and one should finding. The selector in
the replay test now uses the documented `MODEL_PACKAGE` constant, resolving
that finding. Replaying the installed runtime after this test-only refactor
is a local diagnostic; the Nix evidence above covers the preceding source
commit. The final combined gate will check the updated test source in Nix.
The producer and all Lean sources are unchanged by the refactor.

The source-equality manifest `build/agent-logs/native-s6-source-equality.json`
records 796 package/surface-fixture files and S6 test drivers byte-equal to
`e804ddde`; the same scoped `jj diff` is empty.

Follow-up review `20261024T215517Z-ebe1c3e9` is clean: zero must and zero should
findings. Implementation source is frozen at `ebe1c3e9` for root's integration.
At that checkpoint full acceptance was pending. Root approved the combined
S5/S6/native gate for this task and S6 part 1, with the S6 sources and fixtures
byte-identical to `e804ddde`. The complete two-part integration has now passed
the final acceptance recorded below. No SQL, Lean declaration, package manifest
or judge file changed in the native-artifact implementation.

## Final integrated acceptance, 2026-10-25

The producer and regression test are unchanged in reviewed integration
`5bc323f0`. Its full Nix report `l53fgdvx2y87xwj1j6q0kvhx1qcqbhj4` passes 937
tests, including installed package replay and surface/translation/layer checks.
Verdict `fdyxvw89hvk8i7sa232c6is81sczb24d` passes; all 53 prediction files and
7,372 cases are unchanged. Task-end Nix checks pass 71, and scheduled report
`j37adzg25s32slqy03advda9hfd02dwx` passes 47. No failures, errors or skips occur
in those reports. The exact integration commands and outputs are retained in
`build/agent-logs/s6-complete-acceptance.json` and its adjacent gate logs.

The real consumer-edit measurement, old-output failure, artifact inspection and
producer invalidation evidence above establish the task's native-reuse behavior.
The final package replay regression checks the reviewed selector correction too.
Linux acceptance is complete; this record does not claim an executed Darwin build.
The task is DONE and publishes with the S6 execution-contract foundation.
