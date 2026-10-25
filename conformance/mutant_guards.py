"""The links from mutants to what they guard, and their check.

Each mutant table (`resolve_mutants`, `query_mutants`, `number_mutants`,
`write_mutants`, `obligation_mutants`) has a `GUARDS` table that names, for each
mutant, what a surviving mutant would leave untested:

- `rule:NAME`: the Lean declaration `NAME` of the mutated file. The mutant's text
  must lie inside that declaration, so the link cannot point at an unrelated rule.
- `restriction:ID`: a restriction id of the registry (`RestrictionKind.id`).
- `obligation:NAME`: a conjunct of an admission obligation, from the table of
  obligation conjuncts that the caller gives (`obligation_mutants.OBLIGATIONS`).

`guard_problems` lists every link that is missing or names nothing that exists.
"""

from collections.abc import Mapping
from pathlib import Path
import re

from conformance.mutation_edits import Guard, Mutation, guard_entries, source_edits

DECLARATION = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?"
                         r"(?:def|theorem|abbrev|instance|structure|inductive) ([\w.']+)", re.MULTILINE)
"""The start of a top-level Lean declaration and its name."""

GUARD_KINDS = ("rule", "restriction", "obligation")
"""The kinds of guard that the module docstring describes, as the prefix before the colon."""


def declaration_spans(text: str) -> dict[str, list[tuple[int, int]]]:
    """For each declared name in a Lean source, the character ranges from its declaration
    to the next declaration or the end of the file. A `rule:` guard is valid only when the
    mutant's text lies in such a range, so the guard names the rule that the mutant changes."""
    starts = list(DECLARATION.finditer(text))
    spans: dict[str, list[tuple[int, int]]] = {}
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(text)
        spans.setdefault(match.group(1), []).append((match.start(), end))
    return spans


def guard_problems(mutants: Mapping[str, Mutation], guards: Mapping[str, Guard], packages: Path,
                   restriction_ids: set[str], obligations: set[str]) -> list[str]:
    """Each mutant without a guard, each guard without a mutant, and each guard that names
    nothing that exists, as one message per problem. Each grouped edit needs its own link.
    Rule links cover the complete, uniquely matched fragment. `packages` is `packages/`."""
    problems = [f"{name}: no guard; add it to GUARDS" for name in mutants if name not in guards]
    problems += [f"{name}: guard of no mutant; remove it from GUARDS" for name in guards if name not in mutants]
    for name, guard in guards.items():
        entries = guard_entries(guard)
        edits = source_edits(mutants[name]) if name in mutants else ()
        if name in mutants and len(entries) != len(edits):
            problems.append(f"{name}: needs one guard per source edit; update GUARDS")
            continue
        for index, entry in enumerate(entries):
            kind, _, target = entry.partition(":")
            if kind == "restriction" and target not in restriction_ids:
                problems.append(f"{name}: {target} is not a restriction id of RestrictionKind.id")
            elif kind == "obligation" and target not in obligations:
                problems.append(f"{name}: {target} is not an obligation conjunct")
            elif kind == "rule" and name in mutants:
                path, before, _ = edits[index]
                text = (packages / path).read_text()
                position = text.find(before)
                if text.count(before) != 1:
                    problems.append(f"{name}: its text must match exactly once in {path}; update its text")
                elif not any(start <= position and position + len(before) <= end
                             for start, end in declaration_spans(text).get(target, [])):
                    problems.append(f"{name}: its text is not inside the declaration {target} of {path}")
            elif kind not in GUARD_KINDS:
                problems.append(f"{name}: {entry} does not start with rule:, restriction: or obligation:")
    return problems


def obligation_problems(obligations: dict[str, tuple[str, str, str]], covered: dict[str, str],
                        guards: Mapping[str, Guard], packages: Path, restriction_ids: set[str]) -> list[str]:
    """Each obligation conjunct whose text is not inside its declaration, that has neither or
    both of a mutant and an entry of `covered`, and each entry of `covered` that names no
    conjunct, a restriction that does not exist or no reason, as one message per problem.
    `obligations` and `covered` have the forms of `obligation_mutants.OBLIGATIONS` and
    `obligation_mutants.COVERED_ELSEWHERE`."""
    problems = []
    guarded = {entry.partition(":")[2] for guard in guards.values() for entry in guard_entries(guard)
               if entry.startswith("obligation:")}
    for name, (path, declaration, text) in obligations.items():
        source = (packages / path).read_text()
        spans = declaration_spans(source).get(declaration, [])
        if not any(text in source[start:end] for start, end in spans):
            problems.append(f"{name}: its text is not inside the declaration {declaration} of {path}")
        if (name in guarded) == (name in covered):
            problems.append(f"{name}: needs exactly one of a mutant and an entry of COVERED_ELSEWHERE")
    for name, evidence in covered.items():
        kind, _, target = evidence.partition(":")
        if name not in obligations:
            problems.append(f"{name}: covered, but not an obligation conjunct")
        if not (kind == "restriction" and target in restriction_ids or kind == "reason" and target):
            problems.append(f"{name}: {evidence} is neither restriction: with a registry id nor reason: with text")
    return problems
