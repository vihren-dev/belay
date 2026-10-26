# Status: possible write executions

Created 2026-10-26. Status: OPEN. Implementation is in progress; results of Nix checks are below as they come.
Task: [task file](20261026-possible-write-executions.task.md).
Specs: ADR 0019 D4 and its amendment of 2026-10-25, ADR 0012's clarification
of 2026-10-25, and the table-rebuild task.

## Decisions

- 2026-10-25 (owner): plan-dependent INSERT SELECT behavior is represented by
  possible write executions (ADR 0019 D4 amendment).
- 2026-10-26 (owner): the execution interface is a separate task before INSERT
  SELECT, proved on all existing statements as the singleton case, with no new
  SQL. The table-rebuild agent reported the reach of the change.

## Progress

- 2026-10-26: task specified. Review `20261026T094225Z-6cae4c16` had one must (R19,
  the singleton law and query result alternatives), fixed in `0bb7a035`; review
  `20261026T094522Z-0bb7a035` had no findings.
- 2026-10-26: implementation of both parts as one checked unit (the surface cannot
  build on the old run, so the library and fixtures change in the same pass as the
  model). Merge commit `ddbe55df` takes the fixture repair `a55b2818` into this chain.

## Design as built

- Model: `StatementExecution` (`output`, `next`), `StatementExecution.Traced`,
  `ofRun`, `ofAlternatives` and `expand` (`StatementExecution.lean`). `RunStep.continued
  output next others`: the model's own execution first, `others` the further
  executions; `RunStep.executions` lists all of them. `runScriptAllWith`,
  `runScriptAllFrom` (`ScriptRunAll.lean`) give the complete executions of a
  script, each one sequence of executions, each statement run from the connection
  of the execution that reached it. `ScriptRunSingleton.lean` proves the singleton
  law for the current model (`runScriptStep_others`, `runScriptStep_executions`,
  `runScriptAllFrom_eq`) and that the model's own run is admitted
  (`runScriptFrom_mem_runScriptAllFrom`). `Output.oneOf` stays as the special case
  of several results on one unchanged state; `StatementExecution.expand` is its
  correspondence to executions with the same next connection.
- Public run laws: `runScriptFrom_X` became `runScriptAllFrom_X` and quantify over
  `∀ run ∈ runScriptAllFrom ...`. `runScriptStep_valid` is stated for every
  execution of a step. The older halting `runSqlFrom` and `passFrom` stay single
  run, and `runScriptStepFailure` describes the own execution only.
- Conformance: `RunPassStep`, `ExecutionPass`, `runPassAllFrom` (complete executions
  of a case), `classifyPasses` and `Verdict.ofExecutions` compare a native run with
  complete executions; one execution must match all observations. `runPassFrom`
  (the first complete execution) gives the predictions, so all predictions stay as
  they are. Laws are in `RunPassLaws.lean`.
- Surface: `Sql.Branch.continued` chooses an execution of the step; `Sql.Branch.continued_own`
  is the model's own. `Sql.check`, `Sql.SucceedsFrom` and the S6 and S8 laws
  quantify over all executions. `Sql.hasOneBranch` requires that a step has no
  further execution. The replay of a false witness (`ReplayScript.lean`) follows
  the model's own execution and refuses a statement with further executions
  (documented there); `db!` gives a diagnostic for such a statement.

## Manual proof repairs

About 35 manual repairs in the model (the run laws, `runScriptAllFrom_X`) and
about 25 in the surface library and fixtures; under the limit of 80.

## Tests

`PossibleExecutionsExamples` (singleton law per statement kind, admitted-run law,
`Output.oneOf` correspondence, a hand-built two-execution step and script),
`RunPassExecutionsExamples` (accepts a native run that matches one complete
execution, rejects one that matches statement 1 in one execution and statement 2
in another), `tests/admitted_atoms_run_theorems_test.py`,
`tests/valid_atoms_theorems_test.py`, `tests/keys_unique_theorems_test.py`,
`tests/conformance_continuing_case_test.py`, `tests/mutant_guards_test.py`
(`Connection.afterError` moved to `Connection.lean`, two mutant guards follow).

## Checks so far

- `nix-build integrity/judge.nix -A predictions` gives `/nix/store/838s4ypckicdrb9zxry1b23x480b3ar8-sqlite-verifier-predictions`
  with 55 files, byte-identical to the baseline `/nix/store/dzr0k54rmcd6bm0ngvmvvb85a5bayhmy-sqlite-verifier-predictions`
  (`diff -r` is empty), taken before the surface edits; the model did not change after it
  except for docstrings.
