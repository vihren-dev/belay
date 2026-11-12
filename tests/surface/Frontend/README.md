# Frontend: SQL front end

The division for code that turns SQL text into the syntax of the model, and code that puts SQL into
Lean source.

The teams of this division in this tree:

- [Embedding](Embedding/README.md): the code that elaborates SQL literals and SQL files in Lean:
  tokens, source positions, parameters, provenance and warnings.
- [Grammar](Grammar/README.md): the code that parses SQL with the grammar of one SQLite release and
  translates the parse tree to the syntax of the model.
- [Tests](Tests/README.md): tests of SQL syntax, parameter binding and source locations, through the
  public interface.

A test file goes to the division and the team of the code that it tests. The import rule of the
libraries does not apply to test files.
