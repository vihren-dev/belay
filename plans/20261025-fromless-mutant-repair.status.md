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

Task review `20261025T003541Z-2997f487` has no must findings. Its two
wording/path shoulds are fixed in `e3779fc9`; review
`20261025T003614Z-e3779fc9` is clean. The isolated workspace
`sqlite-verifier-fromless-mutant-repair` is based on published `9ac05c46`.
Its four dev-shell inputs match the approved configuration and direnv is
authorized. Implementation is assigned now. The migration law worker owns
slot 1; this repair queues its heavy gate after that focused sequence.
