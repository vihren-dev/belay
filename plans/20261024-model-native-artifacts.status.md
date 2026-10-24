# Model native artifact reuse status

Created 2026-10-24. Status: OPEN.
Task: [required outcomes](20261024-model-native-artifacts.task.md).
Owner: `text_build_boundaries`, assignment after task review.

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
No implementation or new heavy build has started. Required regression, native
reuse demonstration, source review and task acceptance remain open.
