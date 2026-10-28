# Proof refactor acceptance repair status

Date: 2026-10-28. Status: IN PROGRESS.
Audience: the implementation team.
Task: [restore acceptance checks](20261028-proof-refactor-ci.task.md).
Source baseline: PR 295, `e8f46dae`; production `3e2212ed`.

## Native replay diagnosis and repair

The model producer already supplies all required native artifacts. Pinned
Lake 4.34.1 expands wildcard module selections through unsorted directory
enumeration (`Lean.Util.Path.forEachModuleInDir`). Its library builder collects
native objects in that order, and the order contributes to the saved link trace.
Thus relocation between filesystems can invalidate the shared facet while each
module and native object remains current. The direct and installed local replay
orders agree; the hosted failure is the acceptance case for relocation.

The producer manifest now uses explicit names for the four former wildcard
selections. It retains all 874 modules of the `Belay.Sqlite.Model` library.
The package's other four modules are `Codec`, `Codec.Resolution`,
`Codec.SyntaxJson` and `Codec.StatementExamples`, each under `Belay.Sqlite.Model`:
878 package modules in total. Both library declarations remain.
No source, object, output trace or installed-package permission is rewritten.
The existing package replay test checks the configuration that avoids this
failure, then requires the real immutable native facets to replay. Retire the
configuration guard when the pinned Lake sorts wildcard expansion.

The installed fixture and its seven consumer test files are unchanged. The
focused Nix invocations select existing tests from `packages`, `surface` and
`surfaceS6`; their source inputs, runtime, environment and deadlines stay intact.
No test owner or permanent runner was added.

## Acceptance

The new Nix model output is
`/nix/store/mfdl4l49m8lv5phl38hmyxfsgdb9gm86-belay-sqlite-model-0.1.0`.
It contains 878 Lean module artifacts and 878 native objects. Current Nix checks:

| Existing owner and selection | Result | Report under `/nix/store/` |
| --- | --- | --- |
| `packages`, all native replay checks | 3 passed, no compiled targets | `lc9hq9b2mrs3yxjh97z0pzvmgk53xlds-sqlite-verifier-test-packages-1/junit.xml` |
| `surface`, SQL files, roots, records, Lake inputs and proof-cost reports | 24 passed | `fzpdbv90f2mmf3j0pw3hh6rhs6l7w69g-sqlite-verifier-test-surface-ci-repair-1/junit.xml` |
| `surfaceS6`, SQL checker and checker-root tests | 6 passed | `p5gl3ssaaxy7gavx9vr388glwma5a6x6-sqlite-verifier-test-surfaceS6-ci-repair-1/junit.xml` |

These runs used `max-jobs = 1`, `cores = 3` and the hardened Nix sandbox.
The selected consumer runs use an untracked expression in
`build/ci-repair/selected.nix` that changes only the existing owner's pytest file
selection. Logs are `/tmp/proof-refactor-ci-{packages-final,consumers}.log`.

Native repair `15a4bd15` received independent Claude review
`20261028T114602Z-15a4bd15`: zero must findings and one should finding. The
finding requested the model-library versus codec module-count distinction
above; it is fixed. Resolver measurement and review remain pending. Whole acceptance
remains with the coordinator. The Linux hosted result is pending and is separate
from local Nix checks. PR 295's earlier API-reference and verdict successes do
not establish acceptance of this repair.
