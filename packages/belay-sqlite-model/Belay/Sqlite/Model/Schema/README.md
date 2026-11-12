# Schema: schema and writes

The division for the constraints, the statements that change data or schema, and the proofs that
these statements keep the database valid.

The teams of this division in this tree:

- [Columns](Columns/README.md): columns: declared types, affinities, default values and STRICT
  tables.
- [Ddl](Ddl/README.md): CREATE, DROP and ALTER as transitions of the catalog, and the change of
  stored SQL text after a rename.
- [Dispatch](Dispatch/README.md): the code that resolves and runs one statement of any kind: the
  resolver, the step, the connection, and their fixtures.
- [ForeignKeys](ForeignKeys/README.md): foreign keys: their enforcement, their actions and their
  metadata.
- [Rows](Rows/README.md): the validity of rows: NOT NULL, CHECK, unique keys and primary keys.
- [Triggers](Triggers/README.md): the semantics and the execution of triggers.
- [Writes](Writes/README.md): INSERT, UPDATE and DELETE, and the proofs that they keep the
  invariants.

A file of this division can import files of this division and of the divisions below it: Queries,
Frontend, Values, Shared. It cannot import a file of a division above it.
