# Lake artifact cache for `prepare` and `verify-bundle`

Question: can the verifier let Lake compile its generated workspaces, so that
Lake's artifact cache supplies every `.olean` that was compiled before, in
`prepare` and in `verify-bundle`?

Measured 2026-10-09 on one Linux x86_64 host (8 CPUs), Lean and Lake 4.34.1
(Lake 5.0.0), runtime from `just build` at trunk `a6af0b31`. Medians of 3 trials.

## How to reproduce

```sh
nix develop path:./nix -c just build
nix develop path:./nix -c python3 experiments/lake-cache/setup_shim.py build/lake-cache
nix develop path:./nix -c python3 experiments/lake-cache/lake_bench.py build/lake-cache 3
nix develop path:./nix -c python3 experiments/lake-cache/seed_flow.py build/lake-cache
```

The second round (2026-10-12, after `main` was merged at `5f2a3a52`) uses a real
installation instead of the shim:

```sh
nix-build experiments/lake-cache/installation.nix --out-link build/lake-installation \
  --extra-experimental-features 'nix-command flakes'
nix develop path:./nix -c just build
nix develop path:./nix -c python3 experiments/lake-cache/data_path.py build/lake-exp/dp build/lake-installation
nix develop path:./nix -c python3 experiments/lake-cache/check_loop.py build/lake-exp/dp build/lake-installation 5
nix-build experiments/lake-cache/seed.nix -A check --arg work ./build/lake-exp/dp \
  --argstr installation "$(readlink -f build/lake-installation)" --option sandbox true \
  --extra-experimental-features 'nix-command flakes'
```

`lake_bench.py` writes one TOML-only workspace per scenario, in a new directory:
a `lakefile.toml` (data, not Lean code) with one library whose roots are the
approved, generated and candidate modules, plus copies of those sources. The
workspace sets `enableArtifactCache = true` and `restoreAllArtifacts = true` and
requires the `sqliteVerifier` package from `setup_shim.py`.

## Results

| Scenario | small | Atuin | Compiled modules |
| --- | --- | --- | --- |
| Empty cache, all modules | 1.08 s | 4.89 s | 7 / 14 |
| New directory, same sources | 0.18 s | 0.18 s | 0 |
| New directory, `Proofs.lean` edited | 0.38 s | 0.38 s | 1 |
| New directory, contract and generated modules only | 0.15 s | 0.18 s | 0 |
| Same directory again (no-op) | 0.15 s | 0.17 s | 0 |

The same work today (compiles plus `lean --deps-json`, from
`../prepare-latency/README.md`):

| Today | small | Atuin |
| --- | --- | --- |
| `prepare`, empty workspace | 2.35 s | 10.80 s |
| `prepare`, proof edit | 0.66 s | 1.13 s |
| `verify-bundle`, no store | 1.08 s | 2.96 s |

Export (0.4 s), the bundle checker (0.4 s / 3.1 s) and Python orchestration are
outside these tables and do not change.

## Findings

1. **Reuse works across directories.** A new workspace with the same sources
   compiles nothing. The key does not depend on the workspace path.
2. **Only changed output propagates.** A comment added to `Requirements.lean`
   rebuilt `Requirements` only: its `.olean` did not change, so the modules
   that import it came from the cache. The key of a module includes the hashes
   of its imports' outputs.
3. **Lake compiles in parallel and reads headers itself.** No `lean --deps-json`
   processes; Atuin's independent modules build at the same time.
4. **The shipped runtime is not usable as a Lake package as is:**
   - Its `lakefile.toml` requires `lean4export`, which the runtime does not
     ship. The shim uses a library-only lakefile instead.
   - It omits `.lake/build/ir`. Each module trace lists a `.c` output there, so
     Lake treats every `SqliteVerifier` module as not built and tries to
     rebuild it in the read-only Nix store. Belay ships `ir` and works. The
     missing files are 204 KB.
   - Library packages must set `enableArtifactCache = false`. Otherwise Lake
     copies their read-only outputs into the cache and fails.
5. **Compilation is reproducible here.** Lake rebuilt `SqliteVerifier.Contract`
   to a `.olean` byte-identical to the shipped one, with the same trace hash.
6. **A cache on another filesystem works.** With the cache under `/home` and
   the workspace in `/tmp`, Lake copied instead of hard-linking, at the same speed.
7. **Generated `lean-toolchain`.** Without one, Lake writes it and stops with
   "you will need to manually restart Lake". The workspace must include it.
8. **A read-only cache works only for reading.** With a read-only cache
   directory:
   - `enableArtifactCache = true`: hits work; a miss fails with "permission
     denied", because Lake writes the new mapping.
   - `enableArtifactCache = false`: Lake ignores the cache and compiles all
     modules.
   - setting absent: hits work, and a miss compiles locally without writing
     (a proof edit compiled 1 module).
9. **A seed moves between caches with `stage` and `unstage`.** `lake build -o
   mappings.jsonl` records the outputs of the root package; `lake cache stage`
   copies them to a directory (40 KB small, 188 KB Atuin); `lake cache unstage`,
   run inside a generated workspace, copies them into another cache. On that
   cache, new workspaces for both examples compiled nothing, and a proof edit
   compiled only `Proofs` (`seed_flow.py`).
10. **The cache key contains the toolchain's commit hash.** The traces record
    "Lean 4.34.1, commit 5045d00…". A Lean built by Nix that reports a tag
    instead of the commit gets different keys and no cache hits (see
    [ledger/ledger#3270](https://github.com/ledger/ledger/pull/3270)). Ours
    reports the commit.

## Second round: the data path on Lake outputs

Linux x86_64, 2026-10-12. Raw results: `results-round2-Linux-x86_64.jsonl`.

`installation.nix` builds an installation whose libraries are Lake packages
(ADR 0010 section 3) from the repository's own `leanRuntime` and
`modelPackage`: `ir` kept, library-only lakefiles, `enableArtifactCache = false`.

11. **A user's proofs project builds against the installation.** The project has
    its own `lakefile.toml` that requires the installed library by path. Lake
    replays the library (0 library compiles). The contract library's `srcDir`
    points at the approved folder outside the project, and Lake reads the
    contract there in place, so the project needs no copies.
12. **The installed exporter and bundle checker accept Lake's outputs.**
    `data_path.py` builds the proofs project (cache A), exports, builds
    `verify-bundle`'s own workspace (approved and generated modules only, cache
    B) and runs the installed checker on it:

    | Case | Proofs build (compiled) | Export | Verifier build (compiled) | Check | Checker exit |
    | --- | --- | --- | --- | --- | --- |
    | small | 1.04 s (7) | 0.38 s | 0.44 s (3) | 0.44 s | 0, VERIFIED |
    | refutation | 0.84 s (4) | 0.38 s | 0.15 s (0) | 0.49 s | 2, VIOLATED |
    | Atuin | 4.65 s (14) | 0.50 s | 2.45 s (7) | 4.10 s | 0, VERIFIED |

    The refutation shares the small example's contract, so both of its builds
    took it from the caches.
13. **The library package must declare every library the examples import.**
    The small example's proof imports `SqliteVerifier.Demonstration`, which is
    in `EngineeringExamples`, not in the `SqliteVerifier` library. Lake found
    the `.olean` in the package's output folder anyway; a real package declares
    the library, or the examples stop importing it.
14. **The proof loop without the audit is 0.34–0.46 s; the audit adds 0.7–1.1 s.**
    `check_loop.py` adds a new small theorem to `Proofs.lean` for each edit (a
    comment leaves the `.olean` unchanged, and Lake then skips everything that
    imports it):

    | Case | `lake build Candidate` | `lake build Candidate Check` |
    | --- | --- | --- |
    | small | 0.35 s | 1.05 s |
    | refutation | 0.34 s | 1.24 s |
    | Atuin | 0.46 s | 1.56 s |

    The audit command needs Lean's elaborator, so `Check` imports `Lean`, which
    costs about 0.5 s to load (the latency experiment measured 0.67 s for a
    compile importing `Lean` and `SqliteVerifier`, against 0.17 s without
    `Lean`).
15. **The audit catches three of four failures.** It fails the build with a
    clear message for `sorry` (`sorryAx`), a custom axiom, and an import of a
    module the installation does not have (`Lake`). It does not see
    `set_option debug.skipKernelTC true` in `Proofs.lean`: options apply to the
    module that sets them, and the `.olean` does not record them. The proof
    then builds green locally; `verify-bundle`'s kernel replay still checks
    every declaration.
16. **The seed works in the Nix sandbox.** `seed.nix` builds each case's proofs
    project and verify-bundle workspace with one cache, stages them, and a
    second derivation unstages them into a writable cache and builds fresh
    copies: 0 modules compiled for all six workspaces, without network.

## Not covered

- The exporter and the bundle checker were not run on Lake's output. They need
  the workspace's `.lake/build/lib/lean` on their search path.
- Error reporting: today each compile failure becomes a `CompileError` for one
  module. Lake reports failures in its own output format.
- Process bounds: today every `lean` process has its own deadline, output limit
  and minimal environment. Lake starts `lean` itself.
- Cache growth and cleanup, and macOS.
