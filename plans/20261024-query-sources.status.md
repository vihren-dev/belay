# Status: queries as sources

Created 2026-10-24. Status: OPEN. Part 1 implementation is in progress.
Task: [task file](20261024-query-sources.task.md).
Specs: ADR 0019 D5/slice 4 and D3 metadata exception; ADR 0017 S6.
Inspected base: `vihren-dev/sqlite-verifier`, PR #239, commit `98a07bfe`.

## Owner decision and observations

On 2026-10-24 the owner selected: "Support nonrecursive CTEs only; reject actual
recursion and retain the exclusion of the RECURSIVE keyword." The ADR and task
record this scope. There is no outstanding CTE-scope decision.

The prerequisite audit used pinned SQLite 3.51.0 from Nix and observed recursion
without the keyword, ordinary forward CTE references, permitted enclosing-query
references versus rejected sibling references, and CREATE VIEW before a referenced
table exists. These informed the specification, not an implementation acceptance.
Native source and implementation paths are recorded in the task.

The audit found derived-source spellings in 25 corpus-v4 and 180 corpus-v5
records, including 0 and 49 current mustAgree records respectively. These are
lexical counts over setup/schema/migration SQL, not evidence of execution or
measured gains. Views also appear in existing corpora. Implementation must use
actual verdict results and inspect each changed prediction.

## Progress

- 2026-10-24: specified all of D5 in three acceptance parts, including D3's
  compound metadata exception and the accepted semantic recursion exclusion.
  No Nix acceptance check has run. Review `20261024T122324Z-cf7aa9a6` completed
  with no must or should findings.
- A separate implementation workspace will start at a clean S4 boundary, with
  ownership reserved for shared model and text files. ALTER/rebuild work waits
  for the final view representation. FK laws must cover new schema statements
  when the two task branches are integrated.
- 2026-10-24: carried the reviewed task and accepted ADR amendment into the
  `query-sources` workspace at S4 part-1 commit `372e6c8f`, rebased onto PR #240.
  Part 1 is delegated separately from S4 part 2. Its agent owns source/query
  syntax, resolution, evaluation, codecs, text translation and required query
  proof adjustments. S4 owns success/program law modules and its registration
  entries. Carry review and the frozen prediction baseline precede model edits.
  The INSERT SELECT streaming question belongs to slice 5 and is not permission
  to change execution semantics outside this slice-4 task.
- 2026-10-24: carry commit `8a89208f` passed independent Claude review
  `20261024T130558Z-8a89208f`, with no findings. Before any model edit, the Nix
  prediction baseline was built at
  `/nix/store/qwfgz46d1pyd10xiypmka4kixvx38k2b-sqlite-verifier-predictions`.
  Its Nix verdict is
  `/nix/store/srv5lc3gnn1s9wzfjy1ilrzsb2ws0881-sqlite-verifier-verdict`:
  all existing claims pass; corpus v4 has 673 AGREE cases and corpus v5 has 2,946.
  The workspace retains links `build/query-sources-baseline-predictions` and
  `build/query-sources-baseline-verdict` for final prediction classification.
- The first implementation unit gives resolved sources an indexed-query payload,
  reuses `EvalContext.subqueries`, and distinguishes complete-row certainty from
  the first-column certainty of IN. Source rows retain the enclosing cells so
  an unmatched right/full row cannot erase them. `DerivedSourceExamples.lean`
  contains kernel checks for joins, uncertain membership, outer cells, parameters,
  counters and the clock. Source translation, metadata and name resolution remain
  unfinished. The task and its first acceptance part are not complete.
- Nix check for this execution unit: `nix-build build-support/default.nix -A
  modelPackage` passed at
  `/nix/store/d8gfbj5myc9v0lpsqm0c5lmmpj6534bl-belay-sqlite-model-0.1.0`.
  The build checks the new `DerivedSourceExamples` kernel examples and existing
  query/S4 proof modules. Full-part acceptance and the final frozen-prediction
  comparison remain pending.

- Execution-unit review `20261024T132633Z-93767a4d` had no must finding and one
  should finding: test a source with a non-success ending and no expression fault.
  The added kernel example checks that this source is refused. Nix `modelPackage`
  passed at `/nix/store/pp68ghibam1vkp4y5cw5nlsfjb171d86-belay-sqlite-model-0.1.0`.

- Review `20261024T133405Z-15a252a8` passed with no findings.
- The metadata unit adds expression affinities for every source column and SQLite's
  compound affinity combination. D3's ORDER BY COLLATE rewrite now supplies IN with
  derived-column affinity/collation; scalar subqueries still supply no collation.
  The removed restriction is also removed from its registry, documentation and
  example, and the existing compound-collation mutant follows the new branch.
- Source metadata exposed an existing output-collation bug: a FULL JOIN USING
  output is a coalesce without collation, and a RIGHT JOIN output reads the right
  column's collation. The shared expression/star metadata now follows those
  operands. Generated USING equalities retain their existing left-column rule.
  `DerivedColumnExamples.lean` checks both joins, three-column metadata, absent
  affinity, compound type conflicts and D3 comparisons. The targeted Python checks
  are `restriction_registry_test.py` and `mutant_guards_test.py -k compound`.
- Nix `modelPackage` for this metadata unit passed at
  `/nix/store/zs2dfp63la9ib1cx7qskny4l9pvdq4b0-belay-sqlite-model-0.1.0`.
  SQL FROM translation, source scope resolution, the authored judge cases and
  final part-1 Nix full/verdict acceptance remain pending.

- Review `20261024T140053Z-649a3021` had no must finding and two should
  findings. Both metadata functions now list all expression constructors instead
  of using catch-all branches, so new syntax must explicitly choose its metadata.
  Nix `modelPackage` passed at
  `/nix/store/24qvzhb6dpmsh27pzgqyjwr921dkkqbp-belay-sqlite-model-0.1.0`.
