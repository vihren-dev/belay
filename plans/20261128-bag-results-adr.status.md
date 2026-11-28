# Status: experiments and ADR for query results as bags

Created 2026-11-28.
Task: [20261128-bag-results-adr.task.md](20261128-bag-results-adr.task.md).
Status: DONE (2026-11-28). The ADR is PROPOSED and waits for the owner's decisions.

Relevant sources: `packages/belay-sqlite-model/Belay/Sqlite/Model/Shared/Execution/Output.lean`,
`packages/belay-sqlite-model/Belay/Sqlite/Model/Shared/Execution/PossibleResults.lean`,
`packages/belay-sqlite-model/Belay/Sqlite/Model/Queries/Evaluation/PossibleResults.lean`,
`packages/belay-sqlite-model/Belay/Sqlite/Model/Schema/Dispatch/PossibleResultsExamples.lean`.

## Progress

- 2026-11-28: task and status files.
- 2026-11-28: review round 2 of the task: negative LIMIT, the order of a FROM subquery, and the
  line count of the prototype.
- 2026-11-28: review round 3 of the task: sort keys that fail, and FROM subqueries in a join.
- 2026-11-28: review round 4 of the task: no findings.
- 2026-11-28: experiments: `CurrentOutputs.lean`, the native probes P0 to P16, the kernel cost
  measurement, and `check.py` with `default.nix`. Nix build
  `/nix/store/2d2xyfsmjx1z8g3l21wi08x4w2ivrdm8-bag-results-experiments`: `CurrentOutputs`
  compiled with 3 audited theorems on the standard axioms, the probe output equals
  `probes/probes.expected`, kernel cost for 10, 50, 100 and 200 rows. Checks: this Nix build.
- 2026-11-28: review of the experiments: audit `byName_eq`, require exit status 1 of the probe
  run, report only the forbidden axioms, name the deadlines, describe the cost baseline. Nix
  build `/nix/store/gn0rarazw0rkw2n42zpb6d4i2d0c9fxc-bag-results-experiments`: 4 audited
  theorems, probe output equal, kernel cost recorded.
- 2026-11-28: the prototype `experiments/bag-results/Bags/` (17 files, 53 audited theorems,
  1,225 code lines) and the findings `experiments/bag-results/README.md`. Review
  20261128T135008Z-27cfc60e: the sqlite3 deadline has a name; two requests for tests of the
  experiment's own scripts rejected. Nix build
  `/nix/store/yrak1zfpf6m2ya1rincc2gjiw0gv5gsv-bag-results-experiments`: 18 Lean files compiled
  without warnings, 57 audited theorems on the standard axioms, probe output equal, kernel cost
  and per-file code lines recorded. Checks: this Nix build.
- 2026-11-28: review 20261128T140202Z-26e9a1e1 of the prototype: `toBag_rank` says which
  readers it covers, proof sketches for four long proofs, `max` under NOCASE is not an example
  of an order-free aggregate, the evaluation order of `select`. Nix build
  `/nix/store/yp3nx9fvvdb9ls9dzrwlmq51112m49b6-bag-results-experiments`: 57 audited theorems on
  the standard axioms, probe output equal, 1,246 code lines.
- 2026-11-28: the integration survey `docs/records/bag-results-integration-survey.md` and the ADR
  `docs/adr/adr-0034-bag-results.md` (PROPOSED, five owner decisions). Review
  20261128T140607Z-9e4281c5: three docstring wordings of the prototype. Nix build
  `/nix/store/zhfh5aq45zr0qrzkcr5bmcy5y6hz7cci-bag-results-experiments`: 57 audited theorems on
  the standard axioms, probe output equal, kernel cost and 1,246 code lines; the findings and
  the ADR cite this build. Tests: `tests/docs_test.py` (links of the new documents).
- 2026-11-28: review 20261128T141028Z-fd8f03f7 (11 must, 3 should), all fixed in the ADR, the
  survey and the findings: enumerations take lists, `Output.ofResults` orders the results by
  their groups in normal form, `possibleResults` ranks the records of `Query.uniqueRecords`,
  `query` and `single` keep their contracts, one task file for two slices with the documentation
  in the same commit, the experiment's evidence stays, the P0 expectation, the full line counts,
  the P7 row, the two normal-form laws, the `outputJson` count and `NativeOutput.fits`. Only
  No input of the experiment's Nix derivation changed (the commit changes Markdown files and adds
  review records), so the Nix build above stays the evidence. Tests: `tests/docs_test.py`.
- 2026-11-28: review 20261128T141746Z-f2863578 (3 must, 2 should), all fixed: ORDER BY has the
  list enumeration `rankLists` with its law for `rank`, which `possibleResults` uses; `query`
  changes only for outputs with rows; D10 and owner decision 5 give the package and the
  full-scope line estimates; the survey describes `NativeOutput.normalRows` without groups; this
  file says which inputs of the Nix build changed. No input of the Nix derivation changed.
  Tests: `tests/docs_test.py`.
- 2026-11-28: review 20261128T142025Z-cba3cd97 (2 must), both fixed: `unmodeled` ends the run
  before `query` gives a value; the line budget counts from the revision before the experiment
  (`1fb455ac` on main), and the decrease from the revision with the experiment includes the
  change of the tests. No input of the Nix derivation changed. Tests: `tests/docs_test.py`.
  The same commit corrects the reason why slice 1 deletes `Bags/` (it imports only the Lean core
  library) and rewraps long lines.
- 2026-11-28: review 20261128T142317Z-0c38b356 (1 must), fixed: the commit that deletes `Bags/`
  writes into the findings the last revision that replays all of the evidence. After four
  rounds in a row with new musts, the owner said to fix the findings and push. No input of the
  Nix derivation changed. Tests: `tests/docs_test.py`.
- 2026-11-28: owner request after the PR was opened: add a sample of each bag, its rows sorted,
  to print results and decide equality. `Bags/Sample.lean` has the model's insertion sort with
  its laws, `SortOrder`, `Bag.sample`, `sample_eq_iff` and `Bag.decEqBySample`; `kernel_cost.py`
  measures a third case, the quotient decided through samples. Nix build
  `/nix/store/2v81bm3h3cdm7402724r0xqb2rk0pwz9-bag-results-experiments`: 62 audited theorems
  on the standard axioms, probe output equal, 1,343 code lines; the decision through samples
  costs the same as normal-form lists (2.375 s and 2.362 s for 100 rows, 9.099 s and 9.167 s
  for 200), the decision by `List.Perm` 3.274 s and 13.198 s. The findings cite this build.
  Tests: the Nix build, `tests/docs_test.py`.
- 2026-11-28: review 20261128T170221Z-22e0e627 (2 must, 2 should). The two musts are on the
  ADR, which this commit updates for the sample: D3 (the module takes the model's sort, and
  slice 2 deletes the model's copy), D4 (the model decides equality of bags of rows through
  samples and shows samples; claims do not read them), the kernel table, D10 with 1,322 and
  1,343 code lines, the alternatives, and owner decisions 2 and 5. The shoulds: the sample
  docstrings name both sorts, and the findings say which examples use which decision. Nix build
  `/nix/store/726kbww46xp160lxvnjig4zkdvhp53xk-bag-results-experiments`: 62 audited theorems,
  probe output equal, 1,343 code lines; through samples 2.507 s and 9.359 s, normal form
  2.428 s and 9.144 s, `List.Perm` 3.276 s and 13.261 s. Tests: the Nix build,
  `tests/docs_test.py`.
- 2026-11-28: review 20261128T170652Z-a5fb1287 (2 must, 2 should). The ADR and the findings now
  give the measured differences between the decision through samples and normal-form lists
  (3% and 2% in the cited build, within 2% in builds `rk6z…` and `2v81…`) and limit the
  conclusion to the benchmark, one equality of two bags. D3 says that the evaluator's list fixes
  the order of an enumeration unless a sort order gives the sample. D4 says that only the claims
  of the surface package do not read the sample, and that a user property on `Bag.sample` is
  about the sorted rows. The status entry above says "equality of bags of rows". Text only; the
  cited Nix build does not change. Tests: `tests/docs_test.py`.
