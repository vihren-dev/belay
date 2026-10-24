# Status: prediction source filter

Created 2026-10-24. Status: OPEN. Implementation is under validation.
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
  regression. Implementation will be delegated after
  the current build-boundary task is complete, preserving its check boundary.
- 2026-10-24: review `20261024T122630Z-f6abffe7` found no musts and one should.
  The task now names the extra minimal Python inputs and fixed subject stub
  needed to evaluate predictions in the small identity fixture. It still uses
  the production judge expression and does not build the stub runtime.
- 2026-10-24: follow-up review `20261024T122820Z-7eb6003e` found no musts or
  shoulds. The specification is ready for delegation at the prior task boundary.
- 2026-10-24: carried task commit `3808f139` received independent review
  `20261024T124605Z-3808f139`, with no must or should findings, before implementation.
- 2026-10-24: applied the existing Python-file filter to both subject components.
  The focused `tests/test_judge_lock.py` fixture uses the production judge
  expression, minimal Python inputs, and a fixed runtime stub. It tests added,
  edited and removed bytecode plus source edits in both Python components.
  The bytecode regression failed against the original filter and all nine
  targeted Nix evaluation checks passed with the correction. Existing lock
  tamper checks remain in the same suite. No package or lock file changed.

## Current Nix evidence

The baseline prediction build produced
`/nix/store/164jh4a3m2xdajyfqwbbd1b1iilhgldf-sqlite-verifier-predictions`.
`nix-instantiate --eval --strict --json integrity/judge.nix -A current` before
and after the correction produced equal values for all 55 locked parts, and
those values equal `integrity/judge.lock.json`. Outputs are recorded in
`build/agent-logs/lock-{before,after}.json` and `lock-unchanged.log`.
The full gates and frozen-prediction comparison are pending.
