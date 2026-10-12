"""Select kernel replay attacks independently against private compiled fixture copies."""

import pytest

from tests.kernel_gate_support import RECORD, KernelCase, compiled_kernel, kernel, source  # noqa: F401  (fixtures)

pytestmark = [pytest.mark.integration, pytest.mark.kernel, pytest.mark.requires_lean]


def test_missing_sysroot(kernel: KernelCase) -> None:
    """The checker requires an explicit pinned Lean installation even when imports exist."""
    environment = dict(kernel.environment)
    environment.pop("LEAN_SYSROOT")
    result = kernel.check(environment=environment)
    assert result.returncode != 0 and "LEAN_SYSROOT" in result.stderr, result.diagnostic()


def test_relative_library_path(kernel: KernelCase) -> None:
    """A relative application library path cannot redirect the checker's trusted imports."""
    result = kernel.check(application_library=".")
    assert result.returncode != 0 and "absolute existing directory" in result.stderr, result.diagnostic()


@pytest.mark.parametrize("text,diagnostic,accepted", [
    pytest.param("{valid}", "", True, id="valid"),
    pytest.param('{valid}\ninitialize IO.eprintln "CANDIDATE_INITIALIZER_RAN"\n', "", True, id="initializer_ignored"),
    pytest.param("import Lean\nimport Generated\nset_option debug.skipKernelTC true in\n"
                 "run_elab Lean.addDecl (.thmDecl { name := `Proofs.migrationCorrect, levelParams := [], "
                 "type := Lean.mkConst `Generated.expected, value := Lean.mkConst `True.intro })",
                 "while replaying", False, id="forged_kernel_body"),
    pytest.param("import Generated\ntheorem Proofs.migrationCorrect : True := trivial", "reconstructed", False, id="wrong_theorem"),
    pytest.param("import Generated\ntheorem Proofs.migrationCorrect : Generated.expected := by sorry", "sorryAx", False, id="sorry"),
    pytest.param("import Generated\naxiom forbidden : Generated.expected\ndef helper := forbidden\n"
                 "theorem Proofs.migrationCorrect : Generated.expected := helper", "forbidden", False, id="transitive_axiom"),
    *[pytest.param(f"import Lean\ndef {name} : Nat := 0\ntheorem Proofs.migrationCorrect : True := trivial",
                   name, False, id=f"changed_protected_{label}", marks=pytest.mark.approval)
      for label, name in [("contract", "Requirements.contract"), ("SQL", "Generated.script"),
                          ("resolved", "Generated.resolved"), ("catalog", "Generated.startCatalog"),
                          ("profile", "Generated.profile")]],
    pytest.param("import Generated\nunsafe def Proofs.migrationCorrect : True := True.intro",
                 "Proofs.migrationCorrect", False, id="unsafe_proof"),
    # An explicit partial constant avoids elaboration into an ordinary opaque wrapper.
    # Lean.Replay omits partial constants; the required-proof lookup must then reject it.
    pytest.param("import Lean\nimport Generated\nrun_elab Lean.addDecl (.defnDecl { "
                 "name := `Proofs.migrationCorrect, levelParams := [], type := Lean.mkConst `True, "
                 "value := Lean.mkConst `True.intro, hints := .opaque, safety := .partial })",
                 "missing required declaration: Proofs.migrationCorrect", False, id="partial_proof"),
])
def test_proof_attack(kernel: KernelCase, text: str, diagnostic: str, accepted: bool) -> None:
    """Replay honest proofs without initializers and reject forged bodies, axioms and protected substitutions."""
    kernel.compile("candidate", "Proofs", text.replace("{valid}", source("Proofs")))
    result = kernel.check()
    assert (result.returncode == 0) == accepted, result.diagnostic()
    assert diagnostic in result.stderr, result.diagnostic()
    if text.startswith("import Lean\ndef "):
        assert "already contains" in result.stderr or "modified protected" in result.stderr, result.diagnostic()


@pytest.mark.approval
def test_approved_source_substitutes_catalog(kernel: KernelCase) -> None:
    """Even approved logical source cannot replace the generated starting catalog declaration."""
    kernel.compile("trusted", "Requirements", source("Requirements") + "\ndef Generated.startCatalog : Nat := 0\n")
    result = kernel.check()
    assert result.returncode == 1 and "Generated.startCatalog" in result.stderr, result.diagnostic()
    assert "already contains" in result.stderr or "modified protected" in result.stderr, result.diagnostic()


def test_forged_convenience_target(kernel: KernelCase) -> None:
    """A trivial convenience alias cannot replace the independently reconstructed target."""
    kernel.compile("candidate", "Generated", "import SqlInputs\nimport NextInterpretation\ndef Generated.expected : Prop := True")
    kernel.compile("candidate", "Proofs", "import Generated\ntheorem Proofs.migrationCorrect : Generated.expected := trivial")
    result = kernel.check()
    assert result.returncode != 0 and "reconstructed" in result.stderr, result.diagnostic()


@pytest.fixture
def negative_kernel(kernel: KernelCase) -> KernelCase:
    """Prepare a false admitted interpretation independently for either refutation case."""
    kernel.compile("trusted", "Interpretation", source("Interpretation").replace("Prop := True", "Prop := False"))
    for module in ("NextInterpretation", "Generated"):
        kernel.compile("candidate", module, source(module))
    return kernel


def test_checked_refutation(negative_kernel: KernelCase) -> None:
    """A kernel-checked negative argument gets the distinct refutation exit code."""
    negative_kernel.compile("candidate", "Proofs", "import Generated\ntheorem Proofs.migrationViolated : ¬ Generated.expected := by\n"
                            "  intro correct\n  obtain ⟨database, admitted⟩ := correct.nonempty\n  exact admitted.2\n")
    result = negative_kernel.check()
    assert result.returncode == 2, result.diagnostic()


def test_unfinished_refutation(negative_kernel: KernelCase) -> None:
    """An unfinished negative argument is unverified and identifies the unapproved sorry axiom."""
    negative_kernel.compile("candidate", "Proofs", "import Generated\ntheorem Proofs.migrationViolated : ¬ Generated.expected := by sorry")
    result = negative_kernel.check()
    assert result.returncode == 1 and "sorryAx" in result.stderr, result.diagnostic()
