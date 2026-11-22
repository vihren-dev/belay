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
    file_key     FixedString(64),
    processed_at DateTime64(6, 'UTC')
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
- `name` is the full name of the declaration. A private declaration keeps the name that the
  user wrote, without Lean's private prefix. Two private declarations with the same name in
  different files are different rows, because the file key differs.
- `entities.kind` is one of `definition`, `theorem`, `structure`, `inductive`, `class`,
  `instance`, `axiom`, `opaque`. The list can grow.
- `text` is the source text of the full range of the declaration. The range includes the
  docstring, the attributes and the modifiers.
- `user_name` is a declaration of the file version. It is empty for a mention that no
  declaration contains, for example in an `example`, an `attribute` command or `#print`.
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

The command reads the imports from the header of each source file. It must not read them
from a build product, because the key must be known before the command reads build products.

## Sources

The extractor reads build products of the same tree. It does not elaborate a file.

| Data | Source |
| --- | --- |
| Declarations and their full ranges | `.ilean`, key `decls` |
| Text | The source file, cut at the full range |
| `entities.kind` | The exporter (the kind of the constant, with structure, class and instance information from the environment) |
| `type`, `body` | The exporter (`typeReferences`, `bodyReferences`) |
| `mention` | `.ilean`, key `references`: each usage names the declaration that contains it |
| `extends`, `instance_of` | The exporter, from Lean's structure and instance tables |

The exporter of the repository (`tools/theorem_dependency_exporter.lean`) writes the first
three exporter items for a selected set of modules. It does not write `extends` and
`instance_of`, and it does not fold generated constants. The extractor needs these additions.

The command must refuse a file whose build products are older than its source, because the
key is computed from the source.

## Generated constants

This section implements ADR D6, which is owner decision 1.

A constant `c` of a module is a declaration if the `decls` of the `.ilean` file contain it
with a range, and it is not generated by the rules below. Each other constant has a parent:

1. Constructors, recursors, projections and the other constants that Lean's inductive and
   structure tables give for a type: the parent is the type.
2. A constant whose final name component starts with `_` (for example `_proof_1`,
   `_sunfold`, `_cstage1`), or is a match function (`match_1`), or an equation lemma
   (`eq_1`, `eq_def`), when the name without that component is a constant: the parent is
   that constant, after the same rule is applied to it.
3. An instance or another constant that a `deriving` clause produced: the parent is the type
   of the clause. Its range is inside the range of the type.

Rule 2 is the rule `isDeclNeedsAutoDecl` of `import-graph` with the predicate
`Environment.isAutoDecl` of Batteries. The extractor copies them with their source named.

A constant with no parent by these rules, and with no range, is written to the extractor's
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

A reader uses only snapshots that have a row in `snapshots`. Steps 4 and 6 make each level
complete before a reader can see it. An interrupted command leaves rows without a `files`
row; the next command writes them again, and the engine removes the copies.

## Declarations with one user

```sql
WITH files AS
(
    SELECT file_key
    FROM lean_code.snapshot_files FINAL
    WHERE snapshot_id = {snapshot:UUID}
)
SELECT
    r.target_name,
    any(r.user_name) AS only_user
FROM lean_code.entity_references AS r FINAL
WHERE r.file_key IN files
  AND r.user_name != ''
  AND r.target_name IN
      (
          SELECT name
          FROM lean_code.entities FINAL
          WHERE file_key IN files AND kind = 'theorem'
      )
GROUP BY r.target_name
HAVING uniqExact(r.user_name) = 1
   AND countIf(r.kind = 'type') = 0;
```

The result is a list of candidates. These limits apply, and the result of the query must say
them:

- A mention with an empty `user_name` is a use. The query above ignores it; a second query
  must exclude targets that have such a mention.
- A private name that two files declare is one name in this query. The query must then
  compare the file of the target with the file of the user.
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
| Private flag | The text shows it. |
| Generated flag, parent name | Not needed with ADR D6. With option (b) of owner decision 1 they return. |
| Attributes | ADR D7: a later table `entity_attributes (file_key, name, attribute)`. |
| Team, division, package | ADR D4: derived from `source_path`. |
| Origin of a relationship row (which tool) | The kind implies the source. |

## Changes after the first version

A new column is added with `ALTER TABLE ... ADD COLUMN` and a new `extractor_version`. The
new version gives new keys to all files, so the next snapshot fills the column. Rows of
older versions keep the default value and belong only to older snapshots.

A new relationship kind needs a new `extractor_version` and no schema change.
