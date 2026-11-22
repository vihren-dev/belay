# The Lean code store: tables, file keys and write order

Date: 2026-11-22.
Status: specification for a proposed design. Nothing in this document is implemented: no
table exists, and no command writes to the store. The queries were not run.
Audience: implementers and reviewers.
Decision: [ADR 0032](../adr/adr-0032-lean-code-store.md). Where this document depends on an
open owner decision of the ADR, it says so.
Evidence: [relationship kinds and extraction sources](lean-relationship-extraction-findings.md).

## Purpose

This document gives the technical decisions of the design discussion of 2026-11-20 to
2026-11-22 in the detail that an implementer needs: the ClickHouse tables, the rule for the
key of a file version, the order of the writes, the sources of each column, and the query
for declarations with one user.

## Terms

- **Declaration:** a named constant that a person wrote in a Lean source file: a definition,
  theorem, structure, inductive type, class, instance, axiom or opaque constant.
- **Generated constant:** a constant that Lean adds for a declaration and that has no source
  text of its own.
- **File version:** one source file with one text, elaborated against one set of import
  versions with one Lean version by one extractor version.
- **Snapshot:** the set of file versions of one source tree at the time of one command.

## Tables

```sql
CREATE DATABASE IF NOT EXISTS lean_code;

-- One row for each completed snapshot. Written last for its snapshot.
CREATE TABLE lean_code.snapshots
(
    snapshot_id UUID,
    project     LowCardinality(String),
    created_at  DateTime64(6, 'UTC')
)
ENGINE = ReplacingMergeTree
ORDER BY snapshot_id;

-- The files of a snapshot and the key of the version of each file.
CREATE TABLE lean_code.snapshot_files
(
    snapshot_id UUID,
    source_path String,
    module_name String,
    file_key    FixedString(64)
)
ENGINE = ReplacingMergeTree
ORDER BY (snapshot_id, source_path);

-- One row for each file version whose extraction is complete. Written last for its file.
CREATE TABLE lean_code.files
(
    file_key FixedString(64)
)
ENGINE = ReplacingMergeTree
ORDER BY file_key;

-- The declarations of a file version.
CREATE TABLE lean_code.entities
(
    file_key    FixedString(64),
    name        String,
    kind        LowCardinality(String),
    text_sha256 FixedString(64)
)
ENGINE = ReplacingMergeTree
ORDER BY (file_key, name);

-- The source text of declarations, one row for each different text.
CREATE TABLE lean_code.entity_texts
(
    text_sha256 FixedString(64),
    text        String CODEC(ZSTD(3))
)
ENGINE = ReplacingMergeTree
ORDER BY text_sha256;

-- Relationships that this file version contributes, from a declaration to a constant.
CREATE TABLE lean_code.entity_references
(
    file_key      FixedString(64),
    user_module   String,
    user_name     String,
    target_module String,
    target_name   String,
    kind          LowCardinality(String)
)
ENGINE = ReplacingMergeTree
ORDER BY (file_key, user_module, user_name, target_module, target_name, kind);
```

The database name and the service are owner decision 2 of the ADR. The engine and the
deduplicating reads (`FINAL`) follow `build-support/observability-schema.sql`.

Column rules:

- `source_path` is relative to the root of the project, with `/` as separator.
- `file_key` and `text_sha256` are lowercase hexadecimal SHA-256 values.
- `name`, `user_name` and `target_name` are exact kernel names. A private declaration keeps
  Lean's private prefix, which contains the module name, so two private declarations with
  the same written name in different files have different names. A report removes the prefix
  for display only.
- `entities.kind` is one of `definition`, `theorem`, `structure`, `inductive`, `class`,
  `instance`, `axiom`, `opaque`. The list can grow.
- `text` is the source text of the full range of the declaration. The range includes the
  docstring, the attributes and the modifiers.
- A declaration is identified by its file version and its name. Two modules of one snapshot
  can declare the same kernel name when no module imports the two; two test files of this
  repository do.
- `file_key` of a relationship row is the file version whose build products contain the
  relationship.
- `user_module` and `user_name` identify the user. `user_name` is a declaration, or empty.
  `user_module` is the module that declares the user. It is the module of the file version,
  with one exception: a generated constant of this module whose parent is in another module
  (see "Generated constants"). When `user_name` is empty, `user_module` is the module of the
  file version.
- `user_name` is empty for a use that no declaration of `entities` contains, for example in
  an `example`, an `attribute` command or `#print`. For a `mention`, the extractor finds the
  user in this order: the container that the `.ilean` file gives, after the folding of
  generated constants, when it is a declaration; if not, the declaration of the file with
  the smallest full range that contains the position of the usage (a `where` function is
  inside its parent), when exactly one declaration has that smallest range; in each other
  case, the empty name. The container alone is not sufficient: it is absent for a usage in a
  docstring and is a generated name (`_example`) for an anonymous `example`.
- `target_module` and `target_name` identify the target: the module that declares the
  constant, and its name. The target can be a declaration of another file of the snapshot,
  or a constant of Lean's library or of a third-party package, which has no row in
  `entities`. A query finds the file version of the target through `module_name` in
  `snapshot_files`.
- `entity_references.kind` is an open list. The first extractor writes `type`, `body`,
  `mention`, `extends` and `instance_of` (ADR D7).

No row is updated. The same row can be written two times after an interrupted command; the
engine removes the copy.

## The key of a file version

```text
file_key = sha256(
    "lean-code-file-key-v1" LF
    extractor_version LF
    lean_version LF
    module_name LF
    sha256(file text) LF
    sha256(build product 1) LF ... sha256(build product m) LF
    key(import 1) LF ... key(import n) LF )
```

- The imports are the direct imports of the file, sorted by module name.
- For an import that is a source file of the snapshot, `key` is its `file_key`. The import
  graph has no cycle, so the keys are computed in dependency order.
- The selection must contain each imported module of the project's own packages. The
  command fails when an import of such a module is not selected. Then each import outside
  the snapshot is a module of Lean's library or of a third-party package.
- For such an import, `key` is the module name. `lean_version` identifies Lean's library. Third-party versions are owner decision 4 of the
  ADR: with option (a), the SHA-256 of the `lake-manifest.json` of the file's package is one
  more line after `lean_version`.
- `extractor_version` is a string in the extractor source. Each change to what the extractor
  writes changes it.
- `lean_version` is the output of `lean --version` of the toolchain that built the tree.
- The build products are the files that the extractor reads for the module: the `.ilean`
  file and each `.olean` part that Lake wrote for the module, sorted by file name. They make
  the key change when elaboration read an input that is not a Lean file, for example the SQL
  file of `sql_module`.

Owner decision 5 of the ADR can remove the keys of the imports from this input.

## Sources

The command first builds the selected modules and stops if the build fails. The extractor
then reads the build products of that build. It does not elaborate a file. The command does
not compare file times: only the completed build shows that the products belong to the
sources.

Limit: the store is as correct as the build. If elaboration reads a file that is not in
Lake's trace of the module, Lake can use an old product after a change to that file, and the
store then has the old data. The SQL files of `sql_module` are such files, and this document
does not establish that each library has them in its trace. Requirement: the command accepts
a file version only when each SQL file that its elaboration read has, on disk, the bytes
that the build read. The record in the compiled module (`SqlSourceUse`) is not sufficient
for this: it contains `sqlTextHash`, the hash after line endings are made the same, and a
change of line endings inside an SQL string of more than one line changes the compiled
value. The implementation needs a check of the bytes: the SQL file as an input of Lake's
trace with `text = false`, so that Lake hashes the bytes (the repository's Lake template
uses `text = true` for SQL inputs, which is not sufficient), or a hash of the bytes in the
compiled record. Its task file says which. Another kind
of file that elaboration reads needs its own check before a module that uses it is selected.

| Data | Source |
| --- | --- |
| Declarations and their full ranges | The constants of the module in the compiled environment, with Lean's declaration ranges |
| Text | The source file, cut at the full range |
| `entities.kind` | The kernel kind of the constant. Lean's structure, class and instance tables replace it: a constant in the instance table is `instance`, also when its kernel kind is `theorem`. |
| `type`, `body` | The constants in the elaborated type and value (`typeReferences`, `bodyReferences` of the exporter) |
| `mention` | `.ilean`, key `references`: the usages that Lean recorded for each name, with position and container. "Column rules" gives the user. |
| `extends`, `instance_of` | Lean's structure and instance tables |

The `decls` of the `.ilean` file are not the list of declarations: for example, they do not
contain the mutual inductive type `Belay.Sqlite.Model.Resolved.Arguments`, which the
environment has with its range.

The extractor reads each module in the environment of that module's own imports and then
combines the rows. One environment for all selected modules is not possible when two
modules declare the same name, as two test files of this repository do; the exporter of the
repository loads one environment and must change for such a selection.

The exporter of the repository (`tools/theorem_dependency_exporter.lean`) supplies today,
for a selected set of modules: the constants, their kernel kinds (a structure and a class
are `inductive`, an instance is `definition` or `theorem`), their selection ranges, and the
constants of type and body. The extractor needs these additions: full declaration ranges; the kinds
`structure`, `class` and `instance`; `extends` and `instance_of`; the folding of generated
constants.

## Generated constants

This section implements ADR D6, which is owner decision 1.

Requirements:

- Each constant of a selected module is a declaration, or has exactly one parent that is a
  declaration, or is reported.
- A declaration has text that a person wrote.

The rules below are the starting point. They were not run. Lean gives ranges to some
generated constants, and the ranges differ between kinds of commands, so the implementation
task must check the rules on the default selection and add a fixture for each case.

The extractor applies the rules to each constant of a module, in this order. The first rule
that applies decides.

1. Constructors, recursors, projections and the other constants that Lean's inductive and
   structure tables give for a type are generated. The parent is the type.
2. A constant whose declaration range is inside the full range of a type of the same file
   and that is not written there with its own name is generated by a `deriving` clause of
   the type. The parent is the type.
3. Each remaining constant that is in the instance table and has a declaration range is a
   declaration. A `deriving instance` command, which can be in another file than its types,
   gives such instances. With Lean 4.34.1, the range of each such instance is the class
   name in the command: instances of the same class for different types have the same
   range, and instances of different classes have different ranges. Some helpers of such an
   instance have the same range as the instance; a helper without a range is a case of
   rule 5. A remaining constant that is not in the instance table and has the range of such
   an instance is a helper of this rule. Its candidate parents are the instances with that range whose name
   is a prefix of the helper's name, and the instances with that range that refer to the
   helper. With exactly one candidate, the helper is generated and the candidate is its
   parent. With no candidate or more than one, the helper is reported.
4. Each other constant with a declaration range is a declaration. This includes a written
   declaration with a name such as `Foo._helper`.
5. A constant without a declaration range is generated when the name without its final
   component is a constant. The parent is that constant, after these rules are applied to
   it. Examples: `_proof_1`, `_sunfold`, a match function (`match_1`), an equation lemma
   (`eq_1`, `eq_def`), and the helper `instInhabitedParseNode.default` of a derived
   instance, which Lean 4.34.1 gives no range.

The text of an instance of a `deriving instance` command is the text of the whole command,
and the instances of one command have the same text hash. The ranges of rule 3 group
instances and helpers; they are not the range of the text. The declaration range of such an
instance is only the class name in the command, and the build products do not give the
range of the command. The extractor finds the command in the source text around the
declaration range. The fixture for this case checks the result.

Rule 5 is wider than the rule `isDeclNeedsAutoDecl` of `import-graph`, which needs a final
component that starts with `_`. The predicate `Environment.isAutoDecl` of Batteries names
more of these constants. The extractor can use the two as checks of rule 5.

A constant to which no rule applies is written to the extractor's
log and is left out. The count of such constants is part of the command's output, so that a
gap in the rules is visible.

The extractor replaces each generated constant by its parent at the two ends of each
relationship, also for targets outside the project. The module of that end becomes the
module of the parent. The two modules can differ: Lean can generate an equation lemma in the
module that first uses it. The row stays with the file version whose build products contain
the relationship, so `user_module` can then differ from the module of `file_key`. The
extractor then removes rows whose target is the user, and duplicate rows.

## Write order

For each file version whose key is not in `lean_code.files`:

1. Insert the texts that the store may not contain into `entity_texts`.
2. Insert the rows of `entities`.
3. Insert the rows of `entity_references`.
4. Insert the row of `files`.

For the snapshot:

5. Insert the rows of `snapshot_files`.
6. Insert the row of `snapshots`.

A reader uses only snapshots that have a row in `snapshots`. The command uses a file
version as complete only when it has a row in `files`. Steps 4 and 6 make each level
complete before a reader can see it. An interrupted command leaves rows without a `files`
row; the next command writes them again, and the engine removes the copies.

## Declarations with one user

```sql
WITH files AS
(
    SELECT file_key, module_name
    FROM lean_code.snapshot_files FINAL
    WHERE snapshot_id IN
        (SELECT snapshot_id FROM lean_code.snapshots FINAL WHERE snapshot_id = {snapshot:UUID})
),
declarations AS
(
    SELECT f.module_name AS module_name, e.name AS name, e.kind AS kind
    FROM lean_code.entities AS e FINAL
    INNER JOIN files AS f ON f.file_key = e.file_key
)
SELECT
    r.target_module,
    r.target_name,
    any(d.kind) AS target_kind,
    anyIf((r.user_module, r.user_name), r.user_name != '') AS only_user,
    countIf(r.kind = 'type') > 0 AS used_in_a_type
FROM lean_code.entity_references AS r FINAL
INNER JOIN declarations AS d
    ON d.module_name = r.target_module AND d.name = r.target_name
WHERE r.file_key IN (SELECT file_key FROM files)
GROUP BY r.target_module, r.target_name
HAVING uniqExactIf((r.user_module, r.user_name), r.user_name != '') = 1
   AND countIf(r.user_name = '') = 0;
```

The query counts the users of each declaration over all relationship kinds. It returns no
row for a snapshot without a row in `snapshots`. A target with a use outside all
declarations (empty `user_name`) is not a candidate. The columns `target_kind` and
`used_in_a_type` let a person narrow the result, for example to theorem targets with no
recorded `type` relationship. `type` has the meaning of ADR D7: it describes the
occurrence before the folding of either end.

The result is a list of candidates. These limits apply, and a report of the result must say
them:

- Uses that leave no trace in the build products are not in the store: a `simp` call that
  tries a lemma and fails, unfolding by the kernel, a lemma that `simp` uses by `rfl`, a
  name in a tactic quotation that Lean does not record as a usage.
  Attribute membership is such a use too: a theorem with `@[simp]` can have many users
  through the `simp` set. The text of the candidate shows its attributes.
- A use in a file outside the snapshot (a test tree that was not selected, another
  repository) is not in the store.

A candidate becomes a refactoring only when the edit builds.

## Columns that were considered and left out

| Column | Reason |
| --- | --- |
| Snapshot label, commit, branch, host | No query of the first refactoring needs them. `project` and `created_at` identify a snapshot for a person. |
| File import list, text hash | They are inputs of `file_key`. The command has them locally. The module name is a column, because the target of a relationship is identified by module and name. |
| File Lean version, extractor version | Inputs of `file_key`. A later column can expose them when a query must separate versions. |
| File line counts | Not needed for the first refactoring. |
| Declaration lines and columns | The text is stored. Positions change with each edit above the declaration and would defeat the reuse of rows in a later design. |
| Docstring as its own column or hash | It is part of the text. |
| Private flag | The name and the text show it. |
| Time of extraction of a file version | No query reads it. The row in `files` is the completion mark. |
| Generated flag, parent name | Not needed with ADR D6. With option (b) of owner decision 1 they return. |
| Attributes | ADR D7: a later table `entity_attributes (file_key, name, attribute)`. |
| Team, division, package | ADR D4: derived from `source_path`. |
| Origin of a relationship row (which tool) | The kind implies the source. |

## Changes after the first version

A new column is added with `ALTER TABLE ... ADD COLUMN` and a new `extractor_version`. The
new version gives new keys to all files, so the next snapshot fills the column. Rows of
older versions keep the default value and belong only to older snapshots.

A new relationship kind needs a new `extractor_version` and no schema change.
