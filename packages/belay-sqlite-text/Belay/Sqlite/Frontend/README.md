# Frontend: SQL front end

The division for code that turns SQL text into the syntax of the model, and code that puts SQL into
Lean source.

The teams of this division in this tree:

- [Embedding](Embedding/README.md): the code that elaborates SQL literals and SQL files in Lean:
  tokens, source positions, parameters, provenance and warnings.
- [Grammar](Grammar/README.md): the code that parses SQL with the grammar of one SQLite release and
  translates the parse tree to the syntax of the model.

A file of this division can import files of this division and of the divisions below it: Values,
Shared. It cannot import a file of a division above it.
