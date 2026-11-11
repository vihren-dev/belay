# Schema: schema and writes

The division for the constraints, the statements that change data or schema, and the proofs that
these statements keep the database valid.

The teams of this division in this tree:

- [Columns](Columns/README.md): columns: declared types, affinities, default values and STRICT
  tables.
- [Ddl](Ddl/README.md): CREATE, DROP and ALTER as transitions of the catalog, and the change of
  stored SQL text after a rename.
- [ForeignKeys](ForeignKeys/README.md): foreign keys: their enforcement, their actions and their
  metadata.
- [Rows](Rows/README.md): the validity of rows: NOT NULL, CHECK, unique keys and primary keys.
- [Tests](Tests/README.md): tests of constraints, table rebuilds, migrations and foreign keys,
  through the public interface.

A test file goes to the division and the team of the code that it tests. The import rule of the
libraries does not apply to test files.
