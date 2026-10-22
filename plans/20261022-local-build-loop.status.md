# Status: the local incremental build loop (ADR 0020)

Created 2026-10-22. Status: OPEN.
Task file: [task](20261022-local-build-loop.task.md).
Specification: [ADR 0020](../docs/adr-0020-local-build-loop.md).
Source files: `shell.nix`, `nix/flake.nix`, `.envrc`, `justfile`, `tools/check_resources.py`,
`build-support/tests.nix`, `AGENTS.md`, `README.md`.

## Progress

- 2026-10-22: the task file. The flake dev shell's derivation before the change is
  `/nix/store/sicj83z1rdc77q5swkgklwzp5lx867h0-nix-shell.drv`.
