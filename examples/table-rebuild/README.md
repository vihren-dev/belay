# Table rebuild example

This Lake project is the example of the [Belay README](../../README.md). A
migration makes the table `customers` a STRICT table. It copies the table,
drops the old one and renames the copy.

- `TableRebuild.lean` has the code of the README, in the same order.
  `#sql_check badMigration preserves allSessions on shop` answers `false` and
  shows a database on which the migration deletes the sessions. Two
  `decide +kernel` facts about that database, `found`, show the loss and the
  fix. The theorem `fixed_keeps_sessions` states that `fixedMigration` keeps
  `allSessions` on every database with the schema `shop`.
- `FixedSucceeds.lean` checks the success of `fixedMigration`. The check
  answers `false`: the STRICT copy refuses a customer whose email is a blob.
  The theorem `fixed_succeeds` states success for the databases whose
  customers fit the STRICT types.
- `Proof/` has the proofs of the two theorems. Belay's tactics do not prove
  claims about a table rebuild, so these proofs are written by hand. The
  proof of `fixed_keeps_sessions` starts in `Proof/RebuildKeeps.lean`.

## Build and open

In a clone of the Belay repository, install
[elan](https://github.com/leanprover/elan), then run:

```sh
cd examples/table-rebuild
lake build
```

The first build compiles Belay, the model and SQLite's parser; later builds
reuse them. Then open the folder in an editor with the Lean language server
and open `TableRebuild.lean`. The check and the theorems show their results
in the editor.

## Use a copy outside the clone

`lakefile.toml` requires Belay from this clone by the path
`../../packages/belay`. In a copy of this folder at another place, replace
that requirement with the `git` requirement of the README:

```toml
[[require]]
name = "belay"
git = "https://github.com/vihren-dev/belay"
rev = "main"
subDir = "packages/belay"
```

Then run `lake update` and `lake build`.
