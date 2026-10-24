# API reference generation beyond 500 module roots

Created 2026-10-24. Status: DONE on 2026-10-24. Implemented by `s4_part1`.
Status: [progress](20261024-reference-compound-limit.status.md).
Scope: the owner's PR #242 CI failure report; ADR 0009's cached API reference.

## Required behavior

The Linux API reference build succeeds for PR #242's 532 public modules and
larger module sets without losing requested roots or their transitive imports.
The current pinned doc-gen4 reader builds a recursive query whose multirow
VALUES seed participates in a UNION and exceeds SQLite's compound SELECT
limit. Fix this observed dependency defect at its narrow query boundary;
preserve the caller's root selection, bound values, import-closure semantics,
single database, and single complete reference generation.

Keep the existing Lean/doc-gen4 dependency revisions and cached-core split.
Every selected public module remains documented with its source URI; core
pages, shared indexes, source-revision linking and the existing recursor-link
correction remain intact. Generation failures still fail the build. Do not
hide the defect by dropping modules, changing the selected root set, raising
SQLite's limit, or accepting incomplete output.

The dependency workaround names the observed failure and pinned source, and
states when it can be removed. Documentation describes this additional known
defect without treating historical statements as current guarantees. No model
semantics, frozen corpus, claim or judge-lock change belongs to this fix.

## Verification

A bounded regression exercises the actual compiled patched doc-gen4 reader,
not a separately copied SQL query. Include the 500/501 boundary and a larger
root set, shared imports, duplicate roots, a cycle and an unrelated module;
compare the exact returned closure. Preserve the reader's empty-root behavior.
The old query must fail the greater-than-500 case, establishing that the test
catches the reported defect. This is a test of a concrete observed dependency
failure, permitted by the repository's testing rules and ADR 0009.

Run the real sandboxed Linux API reference build on the PR #242 descendant
and record its public-module count and output. Existing generator/source-link
tests remain passing. The coordinator carries the fix into PR #242, then
merges that descendant into PR #243 and active S4 without rewriting shared
ancestors; verify reference generation on the resulting stack too.

Each coherent commit has focused checks and independent review. Final
acceptance includes post-review full/verdict, Nix integration and scheduled
checks under the standing cadence; cached unchanged checks may be reused by
Nix. Only Nix results are acceptance evidence. Coordinate heavy builds with
the root agent, retain the disk guard and use finite timeouts throughout.

## Existing boundaries

`tools/api_reference.py:generate_reference` invokes `single` for every source
and one `fromDb` with all roots. `build-support/doc-gen4.nix` builds the pinned
tool, whose revision is recorded in `build-support/doc-gen4-sources.json`.
The faulty query is in `DocGen4/DB/Read.lean:getTransitiveImports`, at pinned
revision `953c8992d174b4e56955e01e101d46668c68f2bb`.

Public doc-gen4 DB APIs permit a small actual-reader fixture: `ensureWriteDb`,
`saveModule`, `saveImport`, `openForReading` and `getTransitiveImports`.
Calling fromDb repeatedly would also write shared indexes repeatedly; calling
it with no roots changes selection to the complete database. Preserve current
selection instead. Keep the workaround and regression small, with modules
under 200 lines; no documentation framework or general batching API is needed.

The status records PR #242's failing CI run and exact exception.
The owner-provided log establishes the observed failure, not a new scope promise.
SQLite documents the limit at <https://www.sqlite.org/limits.html#max_compound_select>.
