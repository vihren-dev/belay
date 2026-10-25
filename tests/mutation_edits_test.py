"""The shared mutant runner applies complete logical faults and audits each source edit."""

from pathlib import Path

import pytest

from conformance import resolve_mutants
from conformance.mutant_guards import guard_problems, obligation_problems
from conformance.mutation_edits import Guard, Mutation, MutationGroup, SourceEdit

pytestmark = [pytest.mark.unit]

EDITS: tuple[SourceEdit, ...] = (
    ("First.lean", "def first : Nat := 1", "def first : Nat := 11"),
    ("Second.lean", "def second : Nat := 2", "def second : Nat := 22"),
)
"""Distinct files expose a missed second edit and accidental writes to the shared base."""


def base_sources(directory: Path) -> Path:
    """Create the small shared source tree used by the real copy-and-mutate function."""
    base = directory / "base"
    base.mkdir()
    for path, before, _ in EDITS:
        (base / path).write_text(before + "\n")
    return base


@pytest.mark.parametrize("grouped", [False, True], ids=["single", "group"])
def test_mutate_applies_the_complete_fault_to_one_copy(
        tmp_path: Path, monkeypatch: pytest.MonkeyPatch, grouped: bool) -> None:
    """resolve_mutants.mutate applies all selected edits before its sole classification call."""
    base = base_sources(tmp_path)
    mutation: Mutation = MutationGroup(EDITS) if grouped else EDITS[0]
    calls: list[Path] = []

    def classify(copy: Path, lean: Path, program: str) -> list[str]:
        """Observe the actual isolated copy at the unchanged classification boundary."""
        calls.append(copy)
        assert copy == tmp_path / "fault" and copy != base
        assert lean == tmp_path / "lean" and program == "test program"
        assert (copy / "First.lean").read_text() == EDITS[0][2] + "\n"
        assert (copy / "Second.lean").read_text() == EDITS[1][2 if grouped else 1] + "\n"
        return ["changed verdict"]

    monkeypatch.setattr(resolve_mutants, "verdicts", classify)
    assert resolve_mutants.mutate(base, tmp_path, "fault", mutation, tmp_path / "lean", "test program") == [
        "changed verdict"]
    assert calls == [tmp_path / "fault"]
    assert all((base / path).read_text() == before + "\n" for path, before, _ in EDITS)


@pytest.mark.parametrize("index,grouped", [(0, False), (0, True), (1, True)])
@pytest.mark.parametrize("occurrences", [0, 2], ids=["missing", "duplicate"])
def test_bad_anchor_never_classifies_or_changes_the_base(tmp_path: Path,
        monkeypatch: pytest.MonkeyPatch, index: int, grouped: bool, occurrences: int) -> None:
    """mutate rejects either group's stale/repeated anchor, including after a valid first edit."""
    base = base_sources(tmp_path)
    target, before, _ = EDITS[index]
    (base / target).write_text((before + "\n") * occurrences)
    unchanged = {path: (base / path).read_bytes() for path, _, _ in EDITS}

    def unexpected_classification(copy: Path, lean: Path, program: str) -> list[str]:
        """Fail if a partial or invalid mutation reaches compilation/classification."""
        pytest.fail(f"Invalid mutant reached classification: {copy}, {lean}, {program}")

    monkeypatch.setattr(resolve_mutants, "verdicts", unexpected_classification)
    mutation: Mutation = MutationGroup(EDITS) if grouped else EDITS[0]
    with pytest.raises(ValueError) as error:
        resolve_mutants.mutate(base, tmp_path, "fault", mutation, tmp_path / "lean", "test program")
    assert "Mutant fault" in str(error.value) and target in str(error.value)
    assert "exactly one" in str(error.value) and "update its text" in str(error.value)
    assert unchanged == {path: (base / path).read_bytes() for path, _, _ in EDITS}


def test_group_guard_checks_every_fragment(tmp_path: Path) -> None:
    """guard_problems accepts correct per-edit rules and rejects a wrong or missing second link."""
    base = base_sources(tmp_path)
    mutants = {"fault": MutationGroup(EDITS)}
    assert guard_problems(mutants, {"fault": ("rule:first", "rule:second")}, base, set(), set()) == []
    assert guard_problems(mutants, {"fault": ("rule:first", "rule:first")}, base, set(), set()) == [
        "fault: its text is not inside the declaration first of Second.lean"]
    assert guard_problems(mutants, {"fault": "rule:first"}, base, set(), set()) == [
        "fault: needs one guard per source edit; update GUARDS"]


def test_group_restriction_and_obligation_links_keep_their_meaning(tmp_path: Path) -> None:
    """The shared audit checks grouped restriction ids and counts grouped obligation coverage."""
    base = base_sources(tmp_path)
    mutants = {"fault": MutationGroup(EDITS)}
    guards: dict[str, Guard] = {"fault": ("restriction:known", "obligation:second")}
    assert guard_problems(mutants, guards, base, {"known"}, {"second"}) == []
    assert obligation_problems({"second": ("Second.lean", "second", "2")}, {}, guards, base, {"known"}) == []
    assert guard_problems(mutants, guards, base, set(), set()) == [
        "fault: known is not a restriction id of RestrictionKind.id",
        "fault: second is not an obligation conjunct"]


def test_group_cannot_be_empty() -> None:
    """An empty MutationGroup cannot silently classify the unchanged model as a fault."""
    with pytest.raises(ValueError, match="supply at least one source edit"):
        MutationGroup(())


def test_rule_link_covers_the_complete_fragment(tmp_path: Path) -> None:
    """A group cannot label a fragment as one rule when its edit also crosses the next rule."""
    source = "def first : Nat := 1\ndef second : Nat := 2\n"
    (tmp_path / "Rules.lean").write_text(source)
    mutants = {"fault": MutationGroup((("Rules.lean", source, "def first : Nat := 0\n"),))}
    assert guard_problems(mutants, {"fault": ("rule:first",)}, tmp_path, set(), set()) == [
        "fault: its text is not inside the declaration first of Rules.lean"]
