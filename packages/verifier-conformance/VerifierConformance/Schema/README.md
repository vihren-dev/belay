# Schema: schema and writes

The division for the constraints, the statements that change data or schema, and the proofs that
these statements keep the database valid.

The teams of this division in this tree:

- [Columns](Columns/README.md): columns: declared types, affinities, default values and STRICT
  tables.
- [Dispatch](Dispatch/README.md): the code that resolves and runs one statement of any kind: the
  resolver, the step, the connection, and their fixtures.
- [ForeignKeys](ForeignKeys/README.md): foreign keys: their enforcement, their actions and their
  metadata.
- [Writes](Writes/README.md): INSERT, UPDATE and DELETE, and the proofs that they keep the
  invariants.

A file of this division can import files of this division and of the divisions below it: Queries,
Frontend, Values, Shared. It cannot import a file of a division above it.
