# Possible write executions: one statement, several admitted complete results

Created 2026-10-26. Status: DONE (2026-10-26).
Status: [progress](20261026-possible-write-executions.status.md).
Specs: [ADR 0019](../docs/adr-0019-guide-sql.md), D4 and its amendment of
2026-10-25; [ADR 0012](../docs/adr-0012-query-semantics.md), the clarification
of 2026-10-25; [table-rebuild task](20261024-table-rebuild.task.md), the outcomes
"Plan-dependent executions preserve complete effects" and "Execution and proof
clients share the alternatives".

## Purpose and boundary

On 2026-10-25 the owner decided that plan-dependent INSERT SELECT behavior is
represented by possible write executions. An index can change rowids, partial
FAIL writes and error precedence, so one statement can have several admitted
results, and each result has its own database, counters and connection state.

On 2026-10-26 the owner decided that this interface is a separate task, before
INSERT SELECT: the shared run and proof interfaces change once, and the S6, S8,
editor and conformance clients adapt once. This task adds no SQL. Every
statement that the model supports today has one next state (a query can still
have several permitted results on it), so every prediction and every claim stays
the same. The table-rebuild task then gives
INSERT SELECT more than one execution through this interface.

## Required outcomes

- **A statement run gives its admitted executions.** The model's run of one
  statement gives a list of admitted executions. Each execution is complete:
  its output or error, its database, its connection counters and every other
  state that the statement changes. Two executions are never merged cell by
  cell, and a part of one execution is never combined with a part of another.
- **Every current statement is the singleton case.** A theorem states that each
  statement that the model supports today has one next state: the database,
  counters and connection of the current run. Its output is the current output.
  A query whose current output is `Output.oneOf` keeps its result alternatives:
  either one execution with that output, or, if `Output.oneOf` becomes a case of
  executions (next outcome), one execution for each result, all with the same
  next state. A second theorem states that the model's own run (the
  fixed traversal that execution uses) is always one of the admitted
  executions, also for a statement with more than one.
- **Query result alternatives keep one meaning.** `Output.oneOf` describes
  several permitted results of a query on one unchanged state. Either it stays
  as that special case, with a proved correspondence to executions that share
  the next state, or it becomes a case of the new executions. In both cases the
  run, `Sql.Branch`, the laws and conformance use one meaning of "possible
  result"; there is no second one.
- **A script runs each execution on.** The script run and `RunStep` carry the
  executions of a statement. A later statement runs from the state of the
  execution that reached it. A complete run of a script is one sequence of
  executions, one for each statement that it reached. Raw Lean continuations of
  `Sql` programs receive the output of the execution that reached them, as they
  do now with `OutputChoice`.
- **Public laws cover all executions.** Admitted and Valid preservation, the
  foreign-key run laws, `Succeeds`, ordinary and fresh triples, equivalence and
  migration patterns (S6) and the S8 call proofs quantify over all admitted
  executions. A theorem about one chosen execution cannot stand in for a
  universal claim. The existing theorems keep their meaning; a theorem that
  becomes weaker or stronger in its plain words is a decision for the owner.
  Proofs may be repaired; the status file counts manual repairs, and more than
  80 manual repairs is a signal to stop and report.
- **Conformance observes complete executions.** The conformance classifier
  (`packages/verifier-conformance`) compares a native run of a case with the
  complete executions of the model: a native run agrees when one complete
  execution of the script matches all its observations. It never matches the
  observations of one statement against one execution and those of a later
  statement against another. The harness gets no second evaluator.
- **The surface uses the same executions.** `Sql.Branch`, the S5 checker and
  its counterexamples, the S6 and S8 rules and the editor's run of `db!` use the
  executions of the model. A false witness of the checker identifies the
  execution that it used.

## Tests and acceptance

Kernel examples and theorems cover the singleton law on representative
statements of each kind (query, write with and without foreign keys, DDL,
pragma, transaction control, prepare error), the admitted-run law, and the
correspondence of `Output.oneOf`. Because no SQL has two executions yet, a test
builds a statement run with two executions directly and runs a script with it:
the later statement runs from each execution's own state, a complete run is
one sequence of executions, and the conformance comparison accepts a native run
that matches one complete execution and rejects a native run that matches the
first statement in one execution and the second in another.

All prediction files stay byte-identical: build the files of
`nix-build integrity/judge.nix -A predictions` (55 at the base commit) before
the first model change and compare all of them after each model change. The
corpus, claims and judge lock stay unchanged. Relevant mutants only, by name
with `-k`; a mutant guard that moves to a new declaration keeps its meaning.

Two acceptance parts: the model and conformance; the surface clients (S5, S6,
S8, editor). Each coherent commit gets focused checks, dev-build and
independent review. Each part ends with post-review `just test-full` and
`just verdict`. Task end runs `just test-nix` and `just test-scheduled-checks`.
Only Nix results are acceptance evidence.

## Existing interfaces and tricky points

- `StatementRun` (`StatementRun.lean`), `runStatement` and
  `SqlState.statementRun` (`StatementStep.lean`), `RunStep`,
  `runScriptStepWith` and `runScriptStep` (`ScriptRun.lean`),
  `runScriptStepFailure` (`ScriptRunFailure.lean`), `Output` (`Output.lean`),
  `QueryOutputs.lean` and `PossibleOutput.lean` hold the current single run.
  The exhaustive matches show the reach: `.addColumn` appears in about 100
  files and `.setting` in about 30.
- In the surface, `Sql.Branch` and `OutputChoice` (`ExecutionBranches.lean`),
  `ExecutionStep.lean`, `PlainInsertEffect.lean` and `BranchesCovered`
  (`ScopedAgreement.lean`) read the run.
- The cheapest proof repair for a law about the old run is the singleton
  theorem: rewrite the executions of a current statement to its one run, and
  keep the old proof.
- Parallel work: the table-rebuild agent adds the syntax, translation, codecs
  and resolution of INSERT SELECT (`Syntax`, `Translation`, `Resolution`) and
  owns them; it waits for this task before it produces executions. The editor
  part 2b agent owns the editor modules of `packages/belay` and may edit
  `DbBang.lean`. This task owns the run, output, run-law, conformance and
  surface execution files above; keep edits of shared files narrow, so that
  merges stay simple.
- Files stay below 200 lines, with checked public docstrings and plain-words
  statements. New modules are imported from `Belay/Sqlite/Model.lean`.
