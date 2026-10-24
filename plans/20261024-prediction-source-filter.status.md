# Status: prediction source filter

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-prediction-source-filter.task.md).
Relevant files: `integrity/judge.nix`, `tests/test_judge_lock.py`.

## Observed cost

The text-build-boundary agent reported this on 2026-10-24 while running its
Nix acceptance checks, after implementation commit `7d9d7d06`:

- Prediction derivation before Python bytecode appeared:
  `/nix/store/jm12b3chq5j68jl0wk0dp0kk2ipszy9g-sqlite-verifier-predictions.drv`.
  Its Python source tree: `/nix/store/sv52zzb6krbiaa7jip7lcq02fwll5vjy-source`.
- Derivation afterward, rebuilt by `just verdict`:
  `/nix/store/1h9sz1ldfqfm4xzvnsnqbwl94b6ip6hi-sqlite-verifier-predictions.drv`.
  Its Python source tree: `/nix/store/xa5ckc3gi8c8n0b58vx8adf1ipdrfjws-source`.
- Both used `/nix/store/6x07c4hgxnpf4qr4s0ahl4nlvxdcqa5p-sqlite-verifier-conformance`.
  The only source-tree differences were added
  `belay/sqlite/__pycache__/profiles.cpython-314.pyc` and
  `belay/sqlite/__pycache__/quoted_text.cpython-314.pyc`.

The coordinator inspected `subjectSources` and confirmed its unfiltered `belay`
input. These are the motivating observations, not acceptance of a fix.

## Progress

- 2026-10-24: specified the source-filter correction and a focused Nix identity
  regression. Task review is pending. Implementation will be delegated after
  the current build-boundary task is complete, preserving its check boundary.
