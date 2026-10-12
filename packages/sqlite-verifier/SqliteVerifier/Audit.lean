import Lean
import SqliteVerifier.AxiomPolicy

set_option doc.verso true

/-!
The proof author's audit (ADR 0010 section 10). A generated module of the proofs
project runs the audit command after the proofs, so a build fails locally for
the reasons the verifier would reject the bundle: an axiom outside the gate's
allowlist (including {name}`sorryAx`), or an import that the verifier does not have.
The audit decides nothing; the verifier's kernel gates do. It cannot see an option
such as {lit}`debug.skipKernelTC` that a proof module sets for itself.

Only this module imports {lit}`Lean`; the library's root module does not import it.
-/

namespace SqliteVerifier.Audit

open Lean Elab Command

/-- The audit command: the theorems to audit, then the allowed module-name
prefixes. Theorems that do not exist are skipped, so one generated command
serves positive proofs and refutations. Example:
{lit}`#belay_audit [Proofs.migrationCorrect] allowing ["Init", "SqliteVerifier"]`. -/
syntax (name := belayAudit) "#belay_audit " "[" ident,* "]" " allowing " "[" str,* "]" : command

/-- The axioms of the theorem {lit}`name` outside {name}`SqliteVerifier.allowedAxioms`, in the
order the kernel finds them; empty when the gate accepts its axioms. -/
def rejectedAxioms (name : Name) : CommandElabM (Array Name) := do
  let axioms ← collectAxioms name
  return axioms.filter fun used => !SqliteVerifier.allowedAxioms.contains used

/-- The imported modules that start with none of the allowed prefixes. -/
def modulesOutside (env : Environment) (prefixes : Array Name) : Array Name :=
  env.header.moduleNames.filter fun module => !prefixes.any (·.isPrefixOf module)

/-- Elaborate {name}`belayAudit`: fail with a message that names the cause and the
next step when an existing theorem depends on a rejected axiom, when no listed
theorem exists, or when the environment imports a module outside the allowed
prefixes. -/
@[command_elab belayAudit] def elabAudit : CommandElab := fun stx => do
  let env ← getEnv
  let requested := stx[2].getSepArgs.map (·.getId)
  let present := requested.filter env.contains
  if present.isEmpty then
    throwError "none of the theorems {requested} exists; prove one of them in the proofs project"
  for name in present do
    let rejected ← rejectedAxioms name
    unless rejected.isEmpty do
      throwError "{name} depends on axioms outside the verifier's allowlist: {rejected}; \
        remove sorry and own axioms from the proof"
  let prefixes := stx[6].getSepArgs.filterMap (·.isStrLit?) |>.map String.toName
  let outside := modulesOutside env prefixes
  unless outside.isEmpty do
    throwError "the proofs import modules that the verifier does not have: {outside}; \
      import only the verifier library, the contract, the generated modules and the project's own modules"

end SqliteVerifier.Audit
