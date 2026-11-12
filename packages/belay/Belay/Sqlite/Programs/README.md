# Programs: programs and claims

The division for scripts and programs of statements, the claims that a user states about them, and
the rules that prove the claims.

The teams of this division in this tree:

- [Automation](Automation/README.md): the tactics for goals about scripts: `sql_run`, `sql_commute`,
  the routes of `sql_auto`, and evaluation by the kernel.
- [Claims](Claims/README.md): claims about the results and the success of queries, and assertions
  about the initial state and the current state.
- [Clock](Clock/README.md): the clock of a connection and the time that a statement reads.
- [Reasoning](Reasoning/README.md): the rules to reason about programs: equivalence of executions,
  weakest preconditions, migration patterns, and the model of application calls.
- [Scripts](Scripts/README.md): the run of statements in sequence: the step semantics, the frame
  laws, the counters, and the preservation of invariants.
- [StatementRunLaws](StatementRunLaws/README.md): facts that connect the run of one statement to the
  semantics of queries, writes and schema changes.

A file of this division can import files of this division and of the divisions below it: Schema,
Queries, Frontend, Values, Shared. It cannot import a file of a division above it.
