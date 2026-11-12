# Queries

The division for what a statement means before it runs and what a SELECT returns, with the proofs.

The teams of this division in this tree:

- [Evaluation](Evaluation/README.md): the evaluation of the parts of a query: sources, compound
  queries, windows, expressions, groups, order, aggregates, three-valued logic and collations.
- [Fixtures](Fixtures/README.md): example catalogs and example databases that more than one division
  uses.
- [Preparation](Preparation/README.md): the resolution of names against the catalog, for all
  statements: scopes, name traces, views, pragma sources, and the precedence of preparation errors.
- [Select](Select/README.md): the result of a SELECT statement and the laws of that result.

A file of this division can import files of this division and of the divisions below it: Frontend,
Values, Shared. It cannot import a file of a division above it.
