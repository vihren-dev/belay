# Explore theorem dependencies

The dependency report helps you inspect proof reuse before refactoring. It reads
compiled Lean declarations and produces an offline HTML page and raw JSON.

## Build and open the report

From the repository's development shell, run:

```sh
just theorem-dependencies
```

Open `build/theorem-dependencies/index.html` in a browser. The page embeds its
data and selected Lean source text. You can copy that file to another computer
and use it without a server or a network connection.

The Nix target builds the selected packages with the pinned Lean compiler. It
includes every Lean source in the library trees of the model and codec, text
translation, surface API, and conformance library. Selection includes example
modules in those trees and modules that umbrella imports do not reach. A
selected source without its compiled artifact makes the command fail.

Executable entry points, build tools, and separate test and experiment trees
are excluded from this default selection. Referenced third-party declarations
appear as boundary nodes. Their proof bodies are outside the selected scope.

The output directory contains:

- `index.html`: the searchable offline report.
- `dependencies.json`: all selected declarations, references, source text,
  coverage, artifact hashes, and provenance.
- `manifest.json`: the exact selected module names and source paths.

## Inspect a proof

Search for a theorem and select it. Inspect outgoing dependencies or incoming
users. Type and body references are separate; they can overlap. Expand a path
to follow dependencies through other declarations. Folded helper paths retain
the intervening declarations so you can inspect how a theorem is reached.

The module summary shows references across module boundaries. Candidate views
show wrappers, frequently referenced theorems, matching dependency
neighbourhoods, and declarations without project consumers. These views suggest
places to investigate. A candidate is not proof of redundancy or safe deletion.
The absence of consumers applies only to the report's selected scope.

Source selections are zero-based in the JSON. The report displays source lines
for readers. Generated declarations can have no source selection. Their exact
kernel names remain in the report.

## Select compiled tests or experiments

Create a JSON manifest. Source paths are relative to the manifest file unless
you use absolute paths:

```json
{
  "modules": [
    {"name": "MyProofs", "source": "MyProofs.lean", "package": "experiment"},
    {"name": "Separate", "source": "Separate.lean", "package": "experiment"}
  ]
}
```

Compile those modules first. Then run the exporter with an explicit compiler
and the compiled library directories:

```sh
python3 -m tools.theorem_dependencies \
  --manifest /path/to/manifest.json \
  --lean /path/to/toolchain/bin/lean \
  --lean-path /path/to/experiment/lib/lean:/path/to/model/lib/lean \
  --output build/experiment-dependencies
```

Include the compiled libraries of all imported packages in `--lean-path`,
including third-party dependencies. It uses the platform's path separator
(`:` on Linux and macOS). If omitted, the command uses `LEAN_PATH` when set,
otherwise the four default package build directories below `--root`.
Libraries that share the `Belay` namespace are merged for loading. Conflicting
versions of the same artifact cause an error.

The explicit-manifest mode reads existing artifacts. It does not compile them
or establish that the supplied source text was their build input. Rebuild after
editing sources and select source/artifact pairs from the same build. The Nix
target provides that pairing for the default report. The report records source
and artifact SHA-256 hashes separately so their identities remain inspectable.

## Attach existing proof costs

Add `--proof-costs /path/to/proof-costs.json` to attach an existing proof-cost
report. Create that JSON in a package with compiled proof-cost measurements:

```sh
lake exe belay-sql-check --costs --json > proof-costs.json
```

The exporter does not enable cost collection or rebuild instrumented proofs.
A record must name a selected declaration and match its module, Lean version,
and source hash. It must contain a completed internal-heartbeat measurement.
Stale, incompatible, and unmatched records are listed as unattached. Missing
measurements remain explicit. Retained measurement schemes identify the body
boundary and async mode; compare costs only within a compatible scheme.

## Interpret the graph

A reference means that a constant occurs in the current elaborated type or
proof/value. It does not mean the constant is a mathematically necessary
assumption. Tactic-selected constants can appear even when their names were
absent from the source. Private and generated helpers remain in the raw graph.
The graph can contain cycles, and traversal stops at already visited nodes.

Discarded tactic searches and anonymous proofs that do not survive compilation
are outside this report. Module imports are shown separately; declaration
references alone do not describe rebuild or elaboration costs. For source
usages during editing, Lean's LSP call hierarchy remains a useful companion.
