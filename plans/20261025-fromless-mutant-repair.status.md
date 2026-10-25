# SELECT-star mutation repair status

Created 2026-10-25. Status: OPEN.
Task: [required outcomes](20261025-fromless-mutant-repair.task.md).
Assigned to `text_build_boundaries` after its checked SQL-doc correction.
Implementation base: published PR #250, `9ac05c46`.

## Evidence and progress

The confirmed original survivor is Nix derivation `6hlzam2x2342xbc0awm5m2x9x8z0w38r`.
The disposable two-site probe passes at `b1cb35nhbg9vdwh0dpdhy9bjzlvr0p4k`:
unchanged native baseline agrees and `fromless-star` kills the intended fault.
These are diagnostic probes, not acceptance of a repository repair.

Detailed evidence is retained outside the repository under
`/home/codex/work/research_notes/Lean model modularity investigation/ci249-mutants/`.
The published failure log is retained in
`/home/codex/work/sqlite-verifier-s4/build/agent-logs/ci249-mutants-linux.log`. Query and JSON local groups pass
at `hvx19aq81d4n444lp9qgyngd1hg337gj` and `bw6qs4f727q8qi1hfhldgghxbfgyi7w2`;
no hosted timeout cause or timing repair is claimed.

Task review is pending. No implementation has started. Heavy-slot assignment
follows completion of the worker's current SQL-doc gate.
