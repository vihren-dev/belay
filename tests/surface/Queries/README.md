# Queries

The division for what a statement means before it runs and what a SELECT returns, with the proofs.

The teams of this division in this tree:

- [Evaluation](Evaluation/README.md): the evaluation of the parts of a query: sources, compound
  queries, windows, expressions, groups, order, aggregates, three-valued logic and collations.
- [Preparation](Preparation/README.md): the resolution of names against the catalog, for all
  statements: scopes, name traces, views, pragma sources, and the precedence of preparation errors.
- [Select](Select/README.md): the result of a SELECT statement and the laws of that result.
- [Tests](Tests/README.md): tests of name resolution and of SELECT, through the public interface,
  and the audits of axioms.

A test file goes to the division and the team of the code that it tests. The import rule of the
libraries does not apply to test files.
