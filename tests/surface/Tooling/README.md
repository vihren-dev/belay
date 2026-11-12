# Tooling: verification tooling

The division for tools that check the model or the proofs from outside: the search for
counterexamples, the comparison with native SQLite, the cost of proofs, and the Lean commands that
run SQL.

The teams of this division in this tree:

- [Counterexamples](Counterexamples/README.md): the search for counterexamples: code that samples
  candidate databases, searches for a counterexample and makes it smaller, replays it, and writes
  the report.
- [ProofCost](ProofCost/README.md): the cost of proofs: code that measures the heartbeats that a
  proof uses and compares two measurements.
- [Tests](Tests/README.md): tests of the counterexample commands and of the certificates, through
  the public interface.

A test file goes to the division and the team of the code that it tests. The import rule of the
libraries does not apply to test files.
