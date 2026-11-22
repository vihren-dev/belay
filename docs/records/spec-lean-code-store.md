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

-- Relationships from a declaration of this file version to a declaration with a name.
CREATE TABLE lean_code.entity_references
(
    file_key    FixedString(64),
    user_name   String,
    target_name String,
    kind        LowCardinality(String)
)
ENGINE = ReplacingMergeTree
ORDER BY (file_key, user_name, target_name, kind);
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
- `user_name` is a declaration of the file version, or empty. It is empty for a use that no
  declaration of `entities` contains, for example in an `example`, an `attribute` command or
  `#print`. Lean 4.34.1 gives the usages of an anonymous `example` a container name
  (`_example`). The extractor writes the empty name for each container that is not a
  declaration after the folding of generated constants.
- `target_name` is a name only. It can be a declaration of another file of the project, or a
  constant of Lean's library or of a third-party package, which has no row in `entities`. A
  query resolves it in the files of one snapshot.
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
- For another import (Lean's library, a third-party package), `key` is the module name.
  `lean_version` identifies Lean's library. Third-party versions are owner decision 4 of the
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

| Data | Source |
| --- | --- |
| Declarations and their full ranges | The constants of the module in the compiled environment, with Lean's declaration ranges |
| Text | The source file, cut at the full range |
| `entities.kind` | The kernel kind of the constant, refined with Lean's structure, class and instance tables |
| `type`, `body` | The constants in the elaborated type and value (`typeReferences`, `bodyReferences` of the exporter) |
| `mention` | `.ilean`, key `references`: each usage names the declaration that contains it |
| `extends`, `instance_of` | Lean's structure and instance tables |

The `decls` of the `.ilean` file are not the list of declarations: for example, they do not
contain the mutual inductive type `Belay.Sqlite.Model.Resolved.Arguments`, which the
environment has with its range.

The exporter of the repository (`tools/theorem_dependency_exporter.lean`) supplies today,
for a selected set of modules: the constants, their kernel kinds (a structure and a class
are `inductive`, an instance is `definition`), their selection ranges, and the constants of
type and body. The extractor needs these additions: full declaration ranges; the kinds
`structure`, `class` and `instance`; `extends` and `instance_of`; the folding of generated
constants.

## Generated constants

This section implements ADR D6, which is owner decision 1.

The extractor applies these rules to each constant of a module, in this order. The first
rule that applies decides.

1. Constructors, recursors, projections and the other constants that Lean's inductive and
   structure tables give for a type are generated. The parent is the type.
2. A constant whose declaration range is inside the full range of a type of the same file
   and that is not written there with its own name is generated by a `deriving` clause of
   the type. The parent is the type.
3. Each other constant with a declaration range is a declaration. This includes a written
   declaration with a name such as `Foo._helper`, and the instance of a `deriving instance`
   command, which can be in another file than its type. The text of such an instance is the
   command.
4. A constant without a declaration range whose final name component starts with `_` (for
   example `_proof_1`, `_sunfold`), or is a match function (`match_1`) or an equation lemma
   (`eq_1`, `eq_def`), is generated when the name without that component is a constant. The
   parent is that constant, after these rules are applied to it.

Rule 4 is the rule `isDeclNeedsAutoDecl` of `import-graph` with the predicate
`Environment.isAutoDecl` of Batteries. The extractor copies them with their source named.

A constant to which no rule applies is written to the extractor's
log and is left out. The count of such constants is part of the command's output, so that a
gap in the rules is visible.

The extractor replaces each generated constant by its parent in `user_name` and in
`target_name`, also for targets outside the project. It then removes rows with
`user_name = target_name` and duplicate rows.

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
    SELECT file_key
    FROM lean_code.snapshot_files FINAL
    WHERE snapshot_id IN
        (SELECT snapshot_id FROM lean_code.snapshots FINAL WHERE snapshot_id = {snapshot:UUID})
),
declarations AS
(
    SELECT name, kind
    FROM lean_code.entities FINAL
    WHERE file_key IN files
)
SELECT
    r.target_name,
    any(d.kind) AS target_kind,
    anyIf(r.user_name, r.user_name != '') AS only_user,
    countIf(r.kind = 'type') > 0 AS used_in_a_type
FROM lean_code.entity_references AS r FINAL
INNER JOIN declarations AS d ON d.name = r.target_name
WHERE r.file_key IN files
GROUP BY r.target_name
HAVING uniqExactIf(r.user_name, r.user_name != '') = 1
   AND countIf(r.user_name = '') = 0;
```

The query counts the users of each declaration over all relationship kinds. It returns no
row for a snapshot without a row in `snapshots`. A target with a use outside all
declarations (empty `user_name`) is not a candidate. The columns `target_kind` and
`used_in_a_type` let a person narrow the result, for example to theorems that only a proof
uses.

The result is a list of candidates. These limits apply, and a report of the result must say
them:

- Uses that leave no trace in the build products are not in the store: a `simp` call that
  tries a lemma and fails, unfolding by the kernel, a lemma that `simp` uses by `rfl`.
  Attribute membership is such a use too: a theorem with `@[simp]` can have many users
  through the `simp` set. The text of the candidate shows its attributes.
- A use in a file outside the snapshot (a test tree that was not selected, another
  repository) is not in the store.

A candidate becomes a refactoring only when the edit builds.

## Columns that were considered and left out

| Column | Reason |
| --- | --- |
| Snapshot label, commit, branch, host | No query of the first refactoring needs them. `project` and `created_at` identify a snapshot for a person. |
| File module name, import list, text hash | They are inputs of `file_key`. The command has them locally. |
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
