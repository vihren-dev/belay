# Tooling: verification tooling

The division for tools that check the model or the proofs from outside: the search for
counterexamples, the comparison with native SQLite, the cost of proofs, and the Lean commands that
run SQL.

The teams of this division in this tree:

- [Conformance](Conformance/README.md): the comparison of the model with native SQLite: code that
  runs a case on native SQLite, compares the result with the prediction of the model, and the
  command-line programs for this.
- [Counterexamples](Counterexamples/README.md): the search for counterexamples: code that samples
  candidate databases, searches for a counterexample and makes it smaller, replays it, and writes
  the report.

A file of this division can import files of this division and of the divisions below it: Programs,
Schema, Queries, Frontend, Values, Shared. It cannot import a file of a division above it.
