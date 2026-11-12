# Programs: programs and claims

The division for scripts and programs of statements, the claims that a user states about them, and
the rules that prove the claims.

The teams of this division in this tree:

- [Automation](Automation/README.md): the tactics for goals about scripts: `sql_run`, `sql_commute`,
  the routes of `sql_auto`, and evaluation by the kernel.
- [Claims](Claims/README.md): claims about the results and the success of queries, and assertions
  about the initial state and the current state.
- [Reasoning](Reasoning/README.md): the rules to reason about programs: equivalence of executions,
  weakest preconditions, migration patterns, and the model of application calls.
- [Scripts](Scripts/README.md): the run of statements in sequence: the step semantics, the frame
  laws, the counters, and the preservation of invariants.
- [Tests](Tests/README.md): tests of runs, programs, claims and migrations, through the public
  interface.

A test file goes to the division and the team of the code that it tests. The import rule of the
libraries does not apply to test files.
