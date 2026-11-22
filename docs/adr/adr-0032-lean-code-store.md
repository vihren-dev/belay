# ADR 0032: A store of Lean declarations and their relationships for continuous refactoring

Date: 2026-11-22. Status: PROPOSED. Owner decisions 1 to 6 are open.
Audience: designers and reviewers.
Related: [ADR 0028](adr-0028-development-observability.md) (the ClickHouse service and its
conventions), [the theorem dependency report](../development/theorem-dependencies.md) (the
exporter that this ADR reuses), [the long-term simplification goal](../development/lean-simplification-goal.md)
(the consumer of the refactorings).
Specification: [the Lean code store](../records/spec-lean-code-store.md) (tables, file keys,
write order, queries).
Evidence: [relationship kinds and extraction sources](../records/lean-relationship-extraction-findings.md).

## Problem and scope

The owner asked (2026-11-20 to 2026-11-22) for a store of the Lean declarations of a project
and of the relationships between them, which a command fills again and again, so that
refactorings become continuous work and not single campaigns. The first refactoring is: find
each declaration that only one other declaration uses, and decide if it can be inlined.

The present problem has this evidence:

- The ownership reorganization of 2026-11-10 needed an inventory of all declarations. Its
  tools were written for that one move and are not in the repository
  ([status record](../../plans/20261110-ownership-reorganization.status.md)). A new
  refactoring starts again from nothing.
- The simplification goal needs many small removals. A local run of the dependency exporter
  on 2026-11-11 gave 37,460 constants in 1,187 modules; tests were not selected. Of these,
  5,344 are theorems that the exporter does not mark as internal. For 2,423 of them, no
  other constant of the export has them in its type or body. For 1,942, exactly one other
  constant has. The users in these counts include generated and internal constants, and no
  check accepted the run. The counts are not the result of the design below; they show only
  that the question is worth an exact answer.

This ADR decides what the store contains, how one version of a file is identified, and which
sources supply the data. It does not decide how a refactoring is executed. An inlining edit
needs the local source tree and a build; the store only finds candidates and shows the effect
of earlier edits.

The store and its extractor are supporting code. They have no part in the model, in the
conformance evidence or in any claim.

## Current basis

- `tools/theorem_dependency_exporter.lean` (`just theorem-dependencies`) loads compiled
  modules and writes for each constant its name, module, kind, source selection and the
  constants in its type and in its body.
- Lake writes one `.ilean` file for each module that it builds. With Lean 4.34.1 (format
  version 5) the file contains the usages of names that Lean recorded during
  elaboration, each with its position. Lean does not record each name of the source text; a
  name in a tactic quotation is an example. It also contains the direct imports and the source ranges of declarations.
  This list of declarations is not complete; the compiled environment is the source of the
  declaration ranges (see the specification).
- ADR 0028 defines the ClickHouse service, its credentials, and the conventions
  `ReplacingMergeTree` and deduplicating reads. Its database `belay_observability` contains
  execution data only.
- No existing table contains declarations.

## D1. Snapshots do not depend on commits

A command creates a snapshot: an identifier, a project label and a list of Lean source files
with one key for each file. A snapshot can describe a tree with changes that are not
committed. A commit identifier is not part of the schema.

The owner's decision was that the command hashes all Lean files. This ADR proposes a
narrower rule, which is owner decision 6: the files are the sources of a selection of
modules that the command built in the working tree. The extractor reads build products, and
the build of the repository's packages does not cover each Lean file of the tree (test and
experiment trees are separate). The default selection is the selection of the dependency
report: the library trees of the packages. A selected source without its build products
makes the command fail.

Reason: the question "what is used once now" is about a tree. A refactoring session changes
the tree many times before it commits.

## D2. A file version is identified by its text, its build products and the versions of its imports

The key of a file version is a SHA-256 over: the extractor version, the Lean version, the
module name, the file text, the build products that the extractor reads for the file, and
the keys of the files that it imports directly. The command extracts only the file versions
whose key the store does not contain.

The text alone is not sufficient, because the same text can elaborate to different
declarations when an import changes:

```lean
-- Limits.lean, new in the second tree
def Shop.limit : Nat := 10

-- Total.lean, same text in the two trees
import Limits
def limit : Nat := 5
namespace Shop
def total : Nat := limit + 1   -- first tree: _root_.limit; second tree: Shop.limit
end Shop
```

A proof by `simp` gives the same problem: its proof term changes when an imported file adds a
`simp` lemma.

The build products are in the key because elaboration can read inputs that are not Lean
files. In this repository, `sql_module` reads an SQL file and generates declarations from
it. When a build reads a changed SQL file, the build products change, and no other key
input changes. The specification gives the condition that the build must satisfy.

Consequence: a change to a file gives new keys to all files that import it, directly or
through other files, and the extractor reads them again. This is the same set that Lake
builds again.

## D3. The text of a declaration is stored one time

The store keeps the full source text of each declaration, with its docstring. A table keyed
by the SHA-256 of the text contains the texts. A declaration row contains only the hash.

Reason: with D2, one edit gives new keys to many files whose text is the same. Their
declaration rows are small. Their texts are already in the store, so no text is written
again.

## D4. The schema is neutral to the project

The schema has no column for team, division, package or another concept of this repository.
A query derives such groups from the source path. The database name is `lean_code`, and the
snapshot has a project label. The same schema can then hold another Lean project, for
example Mathlib.

## D5. The first schema is minimal

A column is in the first schema only if the incremental mechanism (D1 to D3) or the query for
single-use declarations needs it. [The specification](../records/spec-lean-code-store.md)
gives the six tables and, for each column that was considered and left out, the reason.

A later column is added with `ALTER TABLE ... ADD COLUMN` together with a new extractor
version. The new version changes all keys (D2), so the next snapshot fills the column for all
files. Rows of older extractor versions stay valid for their snapshots.

## D6. The store contains written declarations; generated constants are folded into them

Lean generates constants for a written declaration: match functions, `_proof_N` constants,
equation lemmas, recursors, constructors, projections, instances from `deriving`. They have
no source text of their own.

The store has one row for each declaration that a person wrote. The extractor replaces a
generated constant by the written declaration that produced it, at the two ends of each
relationship, and then removes relationships from a declaration to itself.

Reason: an inlining decision is about text that a person maintains. If generated constants
were rows, each count of users would need a join to fold them.

Limit: no function in Lean core maps a generated constant to its parent. The extractor uses
the rule of `import-graph` (final name component starts with `_`, the prefix is a
constant, the constant has no source range) and Lean's own tables for structures and
inductive types. The specification states the rule. This decision is open (owner decision 1).

## D7. Relationships have an open list of kinds; the first extractor supplies the cheap ones

A relationship row is (user, target, kind). The list of kinds is open. The findings record
lists eight groups of relationships in Lean. The first extractor supplies:

| Kind | Meaning | Source |
| --- | --- | --- |
| `type` | The target occurs in the elaborated type of the user. | Exporter |
| `body` | The target occurs in the elaborated value or proof of the user. | Exporter |
| `mention` | Lean recorded a usage of the target's name in the source text of the user. | `.ilean` |
| `extends` | The user is a structure that extends the target. | Exporter |
| `instance_of` | The user is an instance of the class that is the target. | Exporter |

These sources need only a normal build. Relationships that exist only during elaboration
(notations, macros, elaborators, tactics that fail, unfolding) need a second elaboration of
each file, which costs about as much as a build. They are not in the first extractor. Their
kinds can be added later without a schema change.

Attributes (`@[simp]`, `@[ext]`, rule sets of this project) are not in the first schema. The
stored text shows the attributes that are written at the declaration. A table for attribute
membership follows when a refactoring needs it.

## D8. No existing extractor becomes a dependency

The findings record compares jixia, lean-training-data, LeanDojo, doc-gen4, import-graph,
`lake shake`, lean4export and the REPL tools. Each one pins another Lean version, needs
Mathlib or Python services, cannot read a tree with changes that are not committed, or
supplies less than the exporter and `.ilean` together. The extractor is our code. It copies
small parts with their source named: the rule for generated constants (D6) and, later, the
command replay of jixia.

Lean Beam and the language server answer questions about one position in one file. They are
tools for the execution of a refactoring, not for extraction.

## Consequences

- The command needs a completed build of the selected modules, because the two sources are
  build products. A snapshot is not possible when a selected module does not build.
- A use in a file outside the selection is not in the snapshot. A declaration with one user
  in the library trees can have more users in a test tree.
- After a change to a file with many importers, the extractor reads many files again. It
  writes few new texts (D3).
- A change of the extractor version reads all files again.
- Rows are never changed. A wrong extractor version is corrected by a new version, not by an
  update.
- The store grows with each snapshot by one row for each source file, and by the rows of the
  new file versions. No retention rule exists yet.
- The repository gets a second ClickHouse database with its own schema file. ADR 0028's
  database does not change.

## Alternatives considered

- **Snapshot = commit.** Rejected by the owner (D1): it excludes the tree during a
  refactoring.
- **Key = SHA-256 of the file text only.** Fewer extractions, but wrong data in the cases of
  D2, without a signal.
- **Key without the keys of the imports.** The build products of a file contain all that the
  extractor reads from the file, so the keys of the imports are possibly not necessary. Then
  an edit gives new keys only to the files whose build products change. This is owner
  decision 5.
- **Text in the declaration row.** Simple, but D2 would write each text again for each new
  key.
- **Team and division columns.** Rejected by the owner (D4): the path is sufficient, and the
  columns bind the schema to one repository.
- **Generated constants as rows with a parent column.** Keeps the kernel names, but each
  query must fold them (D6). Possible later as an additional table.
- **The SQLite database of doc-gen4.** Our pinned version writes it, with attributes and
  structure parents. It covers only the public modules of the documentation build, and
  `build-support/api-reference.nix` does not install it.
- **Info trees from the start.** Complete for group 6 of the findings record, at the cost of
  a second build for each snapshot.
- **A local SQLite or DuckDB file in place of ClickHouse.** Sufficient for one session. The
  owner asked for ClickHouse, which also keeps the history of snapshots for trends.

## Not decided here

- How a refactoring is executed and checked, and if the tools of the ownership move go into
  the repository.
- When the command runs (by hand, in CI, after each build) and how long it takes. No
  measurement exists.
- Third-party packages: if their files are part of a snapshot. Until then, a change of a
  dependency that leaves each key input of a file the same gives the file no new key, but
  the folding of D6 reads facts about imported constants (see owner decision 4).
- The table for attribute membership and the extraction from info trees.
- Retention of old snapshots and file versions.

## Owner decisions

Decided in the design discussion (owner, 2026-11-20 to 2026-11-22):

- Snapshots do not depend on commits; the command hashes all Lean files and extracts only
  new file versions (D1).
- The store keeps the full text of each declaration with its docstring (D3).
- No team or division in the schema; the schema must serve other Lean projects (D4).
- The first schema is minimal (D5).
- All relationship kinds are recorded in the end; the first extractor takes only what is
  easy to extract (D7).

Open:

1. **Generated constants.** (a) Fold them into the written declaration (D6). (b) Store them
   as rows with a parent column. Recommendation: (a).
2. **Database.** (a) A new database `lean_code` on the ClickHouse service of ADR 0028, with
   the same uploader identity. (b) Tables in `belay_observability`. (c) Another service.
   Recommendation: (a). Its prerequisite: the
   [devops handoff](../records/observability-devops-handoff.md) asks for rights on
   `belay_observability` only, so the uploader identity needs the same rights on `lean_code`.
3. **Extractors.** (a) Our extractor on the exporter and `.ilean`, no new dependency (D8).
   (b) Adopt jixia and follow its Lean pin. Recommendation: (a).
4. **Dependency versions in the key.** (a) Add the SHA-256 of each package's
   `lake-manifest.json` to the key input, so that a dependency upgrade gives new keys.
   (b) Leave it out until third-party files are in snapshots. Recommendation: (a); it costs
   one more input and removes a silent error.
5. **Keys of the imports in the key.** (a) Keep them (D2). (b) Remove them and rely on the
   build products of the file. Recommendation: (a) for the first version. The folding of D6
   reads facts about imported constants, and no measurement shows that the additional
   extractions are a problem. Decide again with a measurement of the extraction time.
6. **Files of a snapshot.** (a) The sources of a selection of built modules; the default is
   the library trees (D1). (b) All Lean files of the tree, as in the design discussion; the
   command must then build the test and experiment trees too. Recommendation: (a), with a
   selection that adds the test trees for the inlining query, because a test can be the
   second user of a declaration. Two modules of a selection can declare the same name (two
   test files do). The schema therefore identifies a target by module and name.
