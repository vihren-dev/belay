# Checked SQL documentation blocks

Created 2026-10-24. Status: OPEN. Implementation follows task review.
Status: [progress](20261024-sql-doc-blocks.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), checked SQL docstrings,
allocated alongside S7 on 2026-10-24; ADR 0016's surface boundary. The owner's
request is to complete ADR17, including the guide's remaining surface behavior.

## Scope and accepted decision

A SQL example in a Lean docstring must be checked against its stated database
and expected result during elaboration. The current surface has no SQL code-block
handler. This task supplies that missing public behavior using native Verso and
the existing SQL frontend and execution model.

On 2026-10-24 the owner accepted double-quoted header strings, such as
`(e := "Ann@Z")`, and named closed Lean values for other value types. Native
Verso parses header arguments before dispatching a block handler. Do not extend
or fork its parser to accept SQL single quotes in headers. The private guide
correction is published at product revision `17666ac9`; the accepted decision
and publication are in [coordination](20261024-adr17-coordination.status.md).
This task implements the behavior.

## Required outcomes

- **A checked block works through an ordinary import.** With `import Belay`
  and `set_option doc.verso true`, a `sql` code block accepts a closed database
  through `(db := start)`, runs the SQL, and compares its observation with the
  trailing expected comments. A match elaborates; a mismatch is an error at the
  block with expected and actual observations. Rendering retains the SQL body
  and expected comments. Blocks execute independently from their own database.
- **Inputs are explicit and flexible.** Header literals and named closed Lean
  values use existing `Value` constructors/coercions. A missing database is an
  actionable header error. Named parameter convenience arguments follow the
  shared parameter plan's first-appearance and numbering rules. In doc blocks,
  all SQL parameters, including `$name`, require explicit supplied values;
  they do not capture an arbitrary declaration binder from the docstring's
  surrounding context. Keep different SQLite parameter signs distinct.
  Reject missing, duplicate, unused and invalid convenience bindings at their
  argument or relevant SQL token; preserve sparse NULL slots.
- **Reserved names do not remove capabilities.** Provide a closed explicit
  per-statement binding-list input, corresponding to `Script.withValues`, for
  parameters whose names collide with fixed header options or with each other.
  It can bind `:db`, `:values`, `:env`, `:expected`, `:error`, numbered aliases
  and distinct `:x`/`@x`. It is exclusive with named convenience bindings.
  Validate statement counts and slot counts so omissions are not accidental
  NULLs; unreferenced sparse slots remain NULL. Do not rewrite SQL parameter
  signs to implement either mode. A closed `Env` input may supply the existing
  clock/counter primitives; omitted environment means `Env.default`.
  The explicit list is needed for the concrete `:db` and `:x`/`@x` collisions
  above. The environment lets existing clock queries, such as
  `SELECT CURRENT_TIMESTAMP`, have a deterministic checked example; the default
  has no clock and must retain its restriction.
- **Expected text has a precise meaning.** In convenience mode, collect result
  rows in statement order. Render cells with the existing `Value.cellText`,
  joined by ` | `, and rows by newlines, without column headers or padding.
  Successful write counts are omitted. Thus a write followed by a one-cell
  SELECT can be checked with one unquoted line. Zero rows and write-only
  scripts contribute no text. Preserve cell contents; do not trim their spaces
  or conflate lines to make a mismatch pass. This mode checks rendered text,
  not storage classes or result-set boundaries; document that distinction.
- **Exact output checking remains available.** A closed typed expectation of
  the complete `List Output` can check types, empty result sets, write counts,
  and individual query boundaries. It is exclusive with expected-text comments
  and uses the actual model outputs without dropping constructors. The pure
  checking primitive takes explicit inputs and observations so the convenience
  renderer is not the only way to state an expectation. A successful block
  requires no error and no unmodeled outcome in either normal mode.
  This is needed to document the existing `Value` and `Output` APIs accurately:
  `SELECT NULL` and `SELECT 'NULL'` render alike, and empty results or multiple
  SELECTs can erase result-set boundaries in text mode.
- **All alternatives are respected.** Text mode passes only when every permitted
  result produces the same expected text, in every statement that has alternatives.
  It must not pick the first member of `Output.oneOf`. Typed mode compares the
  complete `oneOf` output, including its alternatives. Failure diagnostics show
  the differing result or full output rather than claiming determinism.
- **Expected failures are SQL failures.** `+error` requires an SQL syntax,
  preparation or execution error and compares the first such error's diagnostic
  text with the trailing expectation. Normal blocks reject such errors.
  Wrong error text and unexpected success fail the block. Header/binding errors,
  unavailable native libraries and model restrictions remain elaboration errors
  even with `+error`; none counts as an expected SQLite failure. Runtime messages
  use actual bindings and the connection/index before the failing statement.
  Reuse existing failure classification, without adding a second SQL interpreter.
- **Comment boundaries are documented and lexical.** The final contiguous
  group of standalone `--` lines is the expected-text region. Remove the marker
  and at most one following ASCII space; preserve the remaining text, including
  blank expected lines. This convention applies only outside SQL strings,
  quoted names and block comments. Earlier comments remain SQL. In typed mode
  there is no expected-comment region; all body comments remain SQL, which also
  provides an escape for ordinary trailing line comments. No substring search
  or semicolon splitter may mistake quoted content or trigger bodies for a
  comment boundary. A block with no expected region expects empty rendered text.
- **Diagnostics retain source positions.** Parser, parameter, resolution and
  runtime errors point to the original doc block and SQL occurrence where
  available. Account for native Verso's removal of fence indentation. Include
  nested/indented blocks, Unicode and CRLF. Missing or unavailable source spans
  may fall back to the block, with an explanation; do not point into unrelated
  Lean text. A broken database definition does not generate cascading errors.

## Tests and acceptance

Use compiler fixtures under the existing Nix surface harness and finite
subprocess timeouts. Verify the public import and native handler registration,
not only a direct call to its checker. Read the resulting documentation data to
establish that the rendered block retains its content; no new HTML renderer or
external Verso dependency is required.

Cover matching/mismatching values, an UPDATE followed by SELECT, multiple result
sets, zero rows, write-only blocks, NULL versus text `NULL`, BLOB, whitespace and
newline cells, and typed expectations that distinguish rendered-text collisions.
Exercise equal and distinct `oneOf` alternatives. A mutation that changes the
SQL condition or expected value must make the previously passing fixture fail.

Binding fixtures include repeated names, all parameter signs, sparse numbers,
explicit aliases, reserved-name collisions, missing/extra/duplicate bindings,
closed named values and an unevaluable local. Clock input and parameterized
runtime errors must use the actual supplied context. A second block must start
from its own database even when the first changes rows or connection settings.

Failure fixtures distinguish syntax, prepare, runtime, restriction, bad header,
missing parser library, wrong expected message and unexpected success. Comment
fixtures include quoted `--`, block comments, an ordinary earlier line comment,
trailing SQL comments in typed mode, indentation, non-BMP characters and CRLF.
No admitted proof is produced: this is an elaboration check, outside the kernel
trusted base, using the same semantics as ordinary surface execution.

One acceptance boundary covers the whole feature. Each coherent commit has
focused checks, the dev build after package edits and independent review.
After the final code review run `just test-full` and `just verdict`; task end
also runs `just test-nix` and `just test-scheduled-checks`. Only Nix results are
acceptance evidence. Frozen predictions and the judge lock remain unchanged.

## Existing interfaces and ownership

Reuse `SqlTerm.translateText`, `SqlParameters`, `Script.withValues`, `Values`,
`EvalDatabase`, `SqlDiagnostics`, `DbDiagnostics`, `OutputTable` and the existing
run. `failureDiagnostic` currently binds no values; a shared extension must
preserve existing `db!` behavior and cover the new parameterized caller.

Pinned Lean supplies `DocCodeBlockExpander`, raw code-block registration and
`DocM` lifting `TermElabM`. The generated `@[doc_code_block]` wrapper consumes
static arguments before a handler, so arbitrary SQL names need the existing
raw-expander path. Native body source mapping differs from inline `textRange`.

Own new doc-block/checking/formatting modules and compiler fixtures. Reserve
shared `SqlTerm`, `SqlParameters`, `EvalDatabase` and diagnostics edits with
the editor/S7 owners before implementation; their shared contracts must not
fork. Keep Lean/Verso dependencies out of the model and runner. Files stay
under 200 lines with checked public documentation. Report a specification or
native-API contradiction for owner judgment before changing these meanings.
