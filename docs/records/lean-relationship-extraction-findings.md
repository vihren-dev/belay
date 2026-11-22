# Relationships between Lean declarations and the tools that can extract them

Date: 2026-11-22.
Status: findings from a reading of sources and of build products. No tool in the comparison
was built or run. The facts about our build products were read from a local build with Lean
4.34.1; no check accepted that build.
Audience: designers and reviewers.
Used by: [ADR 0032](../adr/adr-0032-lean-code-store.md) (D6 to D8).

## Kinds of relationships

"A uses B in its definition" is one of eight groups. The third column says what supplies the
relationship.

| Group | Examples | Supplied by |
| --- | --- | --- |
| 1. Use in the elaborated term | B is in the type of A; B is in the value or proof of A; an instance that elaboration selected; a termination proof | The compiled environment (our exporter) |
| 2. Structure | Constructor and field of a type; `extends`; a `mutual` block; `where` and `let rec` functions; generated constants; namespaces | The environment and its structure tables; `.ilean` ranges |
| 3. Registration in a rule set | `@[simp]`, `@[ext]`, `@[grind]`, instances, `attribute [...]` at a later place, rule sets of this project such as `sql_select_rule` | Environment extensions; one test for each attribute type, because Lean core has no general membership test |
| 4. Replacement and alias | `implemented_by`, `csimp`, `extern`, `export`, `alias`, `deprecated`, `to_additive` | Environment extensions |
| 5. Use without a trace | Unfolding by the kernel or by `decide`; coercions that were unfolded; a lemma that `simp` tried without success; a lemma that `simp` used by `rfl` | Nothing after the build. Partly visible in info trees. |
| 6. Use during elaboration | Notations, macros, elaborators, tactics, `deriving` handlers, commands that set context | Info trees, which need a second elaboration of the file |
| 7. Mention | A name in the source text, also in `example`, `#print`, `open`, and in documentation references that Lean checks | `.ilean` |
| 8. Import | Module imports another module | The file header; `.ilean` |

## Our build products

- `tools/theorem_dependency_exporter.lean` loads compiled modules. For each constant it
  writes name, module, kind, a private flag, a flag for project constants, the source
  selection, and the constants of the type and of the body. It writes module imports and
  source hashes. A run of 2026-11-11 gave 37,460 constants in 1,187 modules.
- `.ilean`: Lake writes one for each module. With Lean 4.34.1 the format version is 5. The
  keys are `module`, `version`, `directImports`, `decls` and `references`. `decls` maps a
  name to its full range and its selection range. The full range starts at the docstring.
  `references` maps a constant to its definition position and to a list of usages; each
  usage has a range and the name of the declaration that contains it.
- Info trees are not written to a file. A program must elaborate the file again and collect
  them. With asynchronous elaboration, the trees of proofs arrive in later snapshots: the
  program must wait for them, as Lean's own frontend does, or set `Elab.async` to `false`.

## Tools

| Tool | What it gives | Why it is not adopted |
| --- | --- | --- |
| jixia (frenzymath/jixia) | Declarations, symbols, info-tree references, one JSON group for each file | Pins Lean 4.29. Elaborates each file again. Has no map from generated constants to their command and no elaborator names. Its issue #24: lemmas that `simp` uses by `rfl` are missing from value references. |
| lean-training-data (kim-em) | Premises of each declaration, tactic states | Pins Lean 4.16 and needs Mathlib. |
| LeanDojo, version 2 | Traced files with premises and tactic states | Supports Lean up to 4.30.1. Clones the repository at a commit, so it cannot read a tree with changes that are not committed. Needs Python services. |
| doc-gen4 | Our pinned version writes a SQLite database with declarations, attributes, instances and structure parents | Covers only the modules of the public documentation build. `build-support/api-reference.nix` installs only the HTML. The attribute list is fixed for each attribute type. |
| import-graph | Import graph; `Shake/DeclNeeds.lean` with kinds of needs between declarations | Its level is the module. Its rule for generated constants is useful (below). |
| `lake shake` | Unused imports, with an explanation for each import | Part of Lake 4.34.1. Answers a question about imports, not about declarations. |
| lean4export | Kernel terms for external checkers | No source positions and no relationships above the kernel term. |
| REPL, Pantograph, LeanInteract | Commands and tactics run one at a time | Made for interaction, not for extraction of a whole tree. |
| Lean language server | References, call hierarchy, for one position | Reads the same `.ilean` files. One request for each position. |
| Lean Beam | Language-server extensions with speculative execution at a position | A tool for the execution of an edit. [ADR 0020](../adr/adr-0020-local-build-loop.md) left its adoption open. |

## Parts worth copying

- `import-graph`, `isDeclNeedsAutoDecl`: a constant is generated when its final name
  component starts with `_`, the name without that component is a constant, and it has no
  source range.
- Batteries, `Environment.isAutoDecl`: about 30 lines that recognize recursors,
  constructors, projections, match functions and equation lemmas.
- jixia, `processCommandsAccum`: the loop that elaborates a file command by command and
  keeps the info trees. Needed only for group 6.
- lean-training-data, `CompilationStep.newDecls`: the constants that one command added,
  found by a comparison of the environment before and after the command. This gives the map
  from a generated constant to its command without a name rule.
- LeanDojo, `visitTermInfo` and `visitTacticInfo`: the info-tree nodes that name constants.

## Limits that no tool removes

- Lean core has no function that gives the parent of a generated constant.
- Lean core has no general test "constant C has attribute A". `getAttributeNames` lists the
  attributes; membership needs the API of each attribute type. The `simp` sets are listed in
  `simpExtensionMapRef`.
- Group 5 leaves no data after the build.
