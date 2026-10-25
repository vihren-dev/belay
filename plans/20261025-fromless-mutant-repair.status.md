# SELECT-star mutation repair status

Created 2026-10-25. Status: DONE (2026-10-25).
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
authorized. The implementation and acceptance checks ran in this workspace.

## Implementation boundary

The source adds an explicit group of edits to the existing mutation runner;
single-edit tables keep their current triples. The star fault keeps its name,
`fromless-star` target and baseline/kill assertions, and changes both the result
column and early expansion rejection. Each grouped edit has its own guard link.
The audit checks a unique complete fragment within the linked declaration and
retains restriction/obligation coverage.

Bounded tests exercise single/grouped application in one isolated copy, missing
and duplicate anchors in each position, unchanged shared bases, no classification
after validation failure, wrong/missing second guard links and grouped obligation
coverage. The new tests run in the existing Nix harness suite. Its mutation suites
also receive the existing guard inventory and registry helper as explicit inputs
so a focused gate can replay that audit alongside the real mutants.

No package, native case, judge claim or lock source has changed. Development
Python checks are diagnostics only. The relevant checks are
`tests/mutation_edits_test.py`, `tests/mutant_guards_test.py`, test ownership,
and the existing fromless and parameter mutation tests.

## Focused Nix acceptance

Source snapshot `3a48035ffbe5849fcd332e85deb83d1a836391a1` passed the sequential
gate `build/agent-logs/fromless-focused-gates.sh` (session 67443, exit 0).
The source commit that follows contains the same implementation and these
acceptance records. Commands preserve the existing per-test 300-second limit,
use Nix max-jobs 1 / cores 2 and check the 10 GiB disk floor.

- The harness override selects `-k mutation_edits` with a 600-second outer
  limit: **12 passed**, 234 deselected, at
  `/nix/store/zv6n9rjksjqnzpqwiays4igjxzrcimmx-sqlite-verifier-test-harness-1`.
- The mutant override selects `-k 'fromless or parameter_mutant or mutant_guards'`
  and explicitly includes `tests/mutant_guards_test.py`, with a 900-second outer
  limit: **52 passed**, 25 deselected, at
  `/nix/store/n02c574s3rvy5vzz0bkja5avrigcha4a-sqlite-verifier-test-mutants-1`.
  This checks all 50 guard-inventory cases and kills the four fromless and
  three existing single-edit parameter faults. Baseline agreement and kill
  assertions are unchanged. The two mutation tests took 57.64s and 76.17s.

Logs: `build/agent-logs/fromless-nix-{harness,mutants}.log`. The protected-tree
comparison in `fromless-source-comparison.json` finds no package, native authored
case, judge, corpus, integrity or oracle-source changes from published
`9ac05c469187bde7302e387073381c004739e870`. The judge lock SHA-256 remains
`3ed3054ac313591582e038ecad92b04c81fea33d2559a97ba5a847198196831c`.
The original survivor was measured separately on published PR #249 source
`f808a41a69b9cb2e0f5541e0a5a51362e4a713d1`; its failure is not a result of the
new grouped implementation. Source review and task-end acceptance followed
this focused checkpoint. Slot 1 was released after the focused gate.

Independent review `20261025T004802Z-32198b21` of source commit `32198b21`
found no must findings and one R9 should: the fromless table's docstring had
broken line wrapping. The follow-up separates its edit format, grouped fault
and fault list into three short sentences. Mutation values and assertions are
unchanged from the focused Nix snapshot. The harness, full guard inventory and
ownership tests cover this commit; final Nix acceptance uses the corrected text.
The correction is `e4265048ea883ade3b2f794be20e53645a31165d`; review
`20261025T004856Z-e4265048` is clean (0 must, 0 should). All source findings are
resolved. The task-end sequence used this reviewed source and did not run the
broad mutant suites.

## Final acceptance and handoff

The sequential `build/agent-logs/fromless-acceptance-gates.sh` completed with
exit 0 (session 83904). Its accepted revision is
`0ee899e685164cb50115d02120108df52dcdf1c7`, with implementation exactly equal to
reviewed `e4265048ea883ade3b2f794be20e53645a31165d`; the later changes contain
only status and review records. The bounded commands were `just test-full`
(3000s), `just verdict` (2000s), the predictions build (600s), `just test-nix`
(600s) and `just test-scheduled-checks` (1500s).

- Full Nix: **949 passed**, no failures/errors, at
  `/nix/store/ab66dzjxj9m53hvpyjvpfp68c44pwpdr-sqlite-verifier-test-reports`.
  The suite counts are corpora 54, documentation 12, frozen 153, harness 246,
  model 251, packages 3, parserLibrary 4, sample 23, surface 86 and upstream 117.
  This adds the 12 new harness cases to the accepted 937-test inventory.
- Verdict: **4,869 AGREE / 2,503 MODEL_UNSUPPORTED**, at
  `/nix/store/93lqb1sa4smkvfbcsq95hyyijj90b94f-sqlite-verifier-verdict`.
- Predictions: **53 files / 7,372 cases byte-identical**, comparing baseline
  `/nix/store/v8f8kr8g9i0labdhf6021rpwnp47z939-sqlite-verifier-predictions`
  with `/nix/store/nvd3jnygzz7i4w29wyfx34zfpwbfvjdm-sqlite-verifier-predictions`.
- Task-end Nix checks: **71 passed**, no failures/errors/skips, recorded in
  `build/test-results/nix.xml` (372.79s).
- Scheduled checks: **47 passed**, no failures/errors/skips, at
  `/nix/store/fr5hdf7cri54bqc2ha8f6g5k7h0sd953-sqlite-verifier-scheduled-check-reports`
  (316.49s).

The XML inventories, verdict counts and prediction comparison are under
`build/agent-logs/fromless-*.json`; command logs are the matching
`fromless-{full,verdict,predictions,test-nix,scheduled}.log` files.
`fromless-final-source-comparison.json` confirms unchanged production packages,
native cases, judge claims, frozen corpora, integrity files and oracle sources
against published `9ac05c46`. The judge lock hash remains the value above.

Hosted #250 general-mutant CI failed separately (run 40146867734, job
121029975402). Its log reports query, fromless and JSON-function failures,
then timeout/exit 124 before the failure summaries. This repair addresses the
confirmed fromless fault; the query/JSON causes remain unconfirmed.

The source is at rest and the heavy slot is released. Publication belongs to
the coordinator. The concise PR body is `build/agent-logs/pr-body.md`.
The separate read-only editor readiness note is retained at
`build/agent-logs/editor-part2-readiness.md` for the next assignment; it is not
part of this repair's acceptance.

Completion commit `52e98fd192a33f4e851a83887128166517d56e32` has clean
independent review `20261025T012631Z-52e98fd1` (0 must, 0 should). All required
checks and reviews are complete; no process remains live in this workspace.
