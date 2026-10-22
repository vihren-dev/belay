# Status: the local incremental build loop (ADR 0020)

Created 2026-10-22. Status: OPEN.
Task file: [task](20261022-local-build-loop.task.md).
Specification: [ADR 0020](../docs/adr-0020-local-build-loop.md).
Source files: `shell.nix`, `nix/flake.nix`, `.envrc`, `justfile`, `tools/check_resources.py`,
`build-support/tests.nix`, `AGENTS.md`, `README.md`.

## Progress

- 2026-10-22: the task file. The flake dev shell's derivation before the change is
  `/nix/store/sicj83z1rdc77q5swkgklwzp5lx867h0-nix-shell.drv`.
- 2026-10-22: one package list, two shells (items 1 and 2). `nix/dev-shell.nix` holds the
  packages and variables; `nix/flake.nix` and `shell.nix` import it. The flake dev shell's
  derivation is unchanged on both systems (`sicj83z1…` on x86_64-linux, `2dg63zw2…` on
  aarch64-darwin). `shell.nix` differs from the trial only in the order of two packages.
  `.envrc` loads `shell.nix` with `use nix` and watches its inputs. The four lists of the
  files of `nix/` have the new file. `just test-nix`: 67 passed.
