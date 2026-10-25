"""One logical mutant can change one source fragment or an explicit group of fragments."""

from dataclasses import dataclass

SourceEdit = tuple[str, str, str]
"""A package-relative source path, its exact original fragment and its replacement."""


@dataclass(frozen=True)
class MutationGroup:
    """Edits applied together to one copy, such as two guards for the same SQL error."""

    edits: tuple[SourceEdit, ...]

    def __post_init__(self) -> None:
        """Reject an empty group so it cannot classify an unchanged copy as a mutant."""
        if not self.edits:
            raise ValueError("A mutation group has no edits; supply at least one source edit")


Mutation = SourceEdit | MutationGroup
"""A single edit or an explicitly grouped logical fault, through the same mutation runner."""
Guard = str | tuple[str, ...]
"""One rule/restriction/obligation link per edit, in the same order as a mutation group."""


def source_edits(mutation: Mutation) -> tuple[SourceEdit, ...]:
    """Normalize one edit and a group for the shared application and guard audit loops."""
    return mutation.edits if isinstance(mutation, MutationGroup) else (mutation,)


def guard_entries(guard: Guard) -> tuple[str, ...]:
    """Retain each grouped edit's link instead of auditing only the first source fragment."""
    return (guard,) if isinstance(guard, str) else guard
