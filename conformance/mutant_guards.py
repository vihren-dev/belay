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

from pathlib import Path
import re

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


def guard_problems(mutants: dict[str, tuple[str, str, str]], guards: dict[str, str], packages: Path,
                   restriction_ids: set[str], obligations: set[str]) -> list[str]:
    """Each mutant without a guard, each guard without a mutant, and each guard that names
    nothing that exists, as one message per problem. `packages` is the `packages/` folder."""
    problems = [f"{name}: no guard; add it to GUARDS" for name in mutants if name not in guards]
    problems += [f"{name}: guard of no mutant; remove it from GUARDS" for name in guards if name not in mutants]
    for name, guard in guards.items():
        kind, _, target = guard.partition(":")
        if kind == "restriction" and target not in restriction_ids:
            problems.append(f"{name}: {target} is not a restriction id of RestrictionKind.id")
        elif kind == "obligation" and target not in obligations:
            problems.append(f"{name}: {target} is not an obligation conjunct")
        elif kind == "rule" and name in mutants:
            path, before, _ = mutants[name]
            text = (packages / path).read_text()
            position = text.find(before)
            if not any(start <= position < end for start, end in declaration_spans(text).get(target, [])):
                problems.append(f"{name}: its text is not inside the declaration {target} of {path}")
        elif kind not in GUARD_KINDS:
            problems.append(f"{name}: {guard} does not start with rule:, restriction: or obligation:")
    return problems
