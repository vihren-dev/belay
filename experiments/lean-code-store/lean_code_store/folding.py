"""The rules of "Generated constants" of the Lean code store specification, on one module.

Each constant of a module is decided as a written declaration, as a generated constant with
one parent, or as reported. `resolve` then gives the written declaration that a constant
folds into, also across modules.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
import re

from lean_code_store.facts import ConstantFacts, ModuleFacts, Range
from lean_code_store.source import name_components, range_text, user_name

Declaration = tuple[str, str]
"""A written declaration as `(module, name)`."""

ImportedResolver = Callable[[str, str], Declaration | None]
"""Resolves a constant of another selected module through that module's own folding."""

GENERATED_COMPONENT = re.compile(r"^(_.*|match_\d+|eq_\d+|eq_def)$")
"""Final name components of rule 5."""

MAX_DEPTH = 64
"""Bound of a chain of parents; a longer chain is reported as a cycle."""


@dataclass(frozen=True)
class Decision:
    """The decision of the rules for one constant of the module."""

    status: str
    """`declaration`, `generated` or `reported`."""
    rule: str
    """The rule that decided (`1` to `5`), or the cause of a report."""
    parent: str | None = None
    """The direct parent of a generated constant."""


def _contains(outer: Range, inner: Range) -> bool:
    """Whether a range contains another, compared by line and code point column."""
    return (outer[0], outer[1]) <= (inner[0], inner[1]) and (inner[3], inner[4]) <= (outer[3], outer[4])


def _written_with_own_name(facts: ConstantFacts, lines: list[str]) -> bool:
    """Whether the selection range of a constant shows the last component of its name."""
    if facts.selection is None:
        return False
    written = range_text(lines, facts.selection).strip()
    own = name_components(user_name(facts.name))[-1]
    return written == own or written.endswith("." + own) or written == user_name(facts.name)


def _rule_two_parent(facts: ConstantFacts, types: list[ConstantFacts], lines: list[str]) -> str | None:
    """The type whose full range contains the constant that a `deriving` clause generated."""
    if facts.range is None or _written_with_own_name(facts, lines):
        return None
    for candidate in types:
        if candidate.name != facts.name and candidate.range and _contains(candidate.range, facts.range):
            return candidate.name
    return None


def _rule_five_parent(name: str, is_constant: Callable[[str], bool]) -> str | None:
    """The constant that a name without range extends with a generated final component."""
    components = name_components(name)
    if len(components) < 2 or not GENERATED_COMPONENT.match(components[-1]):
        return None
    prefix = name[: len(name) - len(components[-1]) - 1]
    return prefix if is_constant(prefix) else None


def decide_module(facts: ModuleFacts, source: str) -> dict[str, Decision]:
    """Apply rules 1 to 5 in order to each constant of the module; the first rule decides."""
    lines = source.split("\n")
    own = {constant.name: constant for constant in facts.constants}
    types = [c for c in facts.constants if c.kernel_kind == "inductive" and c.range is not None]
    decisions: dict[str, Decision] = {}
    remaining: list[ConstantFacts] = []
    for constant in facts.constants:
        if constant.table_parent is not None:
            decisions[constant.name] = Decision("generated", "1", constant.table_parent)
        elif (parent := _rule_two_parent(constant, types, lines)) is not None:
            decisions[constant.name] = Decision("generated", "2", parent)
        else:
            remaining.append(constant)
    instances = [c for c in remaining if c.is_instance and c.range is not None]
    for constant in remaining:
        if constant.is_instance and constant.range is not None:
            decisions[constant.name] = Decision("declaration", "3")
            continue
        same_range = [i for i in instances if constant.range is not None and i.range == constant.range]
        if same_range:
            candidates = {i.name for i in same_range if constant.name.startswith(i.name + ".")
                          or constant.name in {r[0] for r in i.type_references + i.body_references}}
            if len(candidates) == 1:
                decisions[constant.name] = Decision("generated", "3", candidates.pop())
            else:
                cause = "helper without candidate" if not candidates else "helper with several candidates"
                decisions[constant.name] = Decision("reported", cause)
        elif constant.range is not None:
            decisions[constant.name] = Decision("declaration", "4")
        elif (parent := _rule_five_parent(constant.name,
                                          lambda n: n in own or n in facts.external)) is not None:
            decisions[constant.name] = Decision("generated", "5", parent)
        else:
            decisions[constant.name] = Decision("reported", "no rule")
    return decisions


def _external_parent(facts: ConstantFacts, external: dict[str, ConstantFacts]) -> str | None:
    """The parent of a constant of a module outside the selection, by rules 1 and 5 only."""
    if facts.table_parent is not None:
        return facts.table_parent
    if facts.range is not None:
        return None
    return _rule_five_parent(facts.name, lambda n: n in external)


def resolver(facts: ModuleFacts, decisions: dict[str, Decision],
             imported: ImportedResolver, selected: Callable[[str], bool]) -> Callable[[str, str], Declaration | None]:
    """A function from `(module, name)` to the written declaration that the constant folds into.

    It gives `None` for a reported constant of a selected module. A constant outside the
    selection folds by rules 1 and 5; with no such parent it stays as it is.
    """
    def resolve(module: str, name: str, depth: int = 0) -> Declaration | None:
        if depth > MAX_DEPTH:
            return None
        if module == facts.module:
            decision = decisions.get(name)
            if decision is None or decision.status == "reported":
                return None
            if decision.status == "declaration":
                return (module, name)
            parent = decision.parent or ""
            return resolve(_module_of(parent, facts), parent, depth + 1)
        if selected(module):
            return imported(module, name)
        known = facts.external.get(name)
        parent = _external_parent(known, facts.external) if known else None
        if parent is None:
            return (module, name)
        return resolve(_module_of(parent, facts), parent, depth + 1)
    return resolve


def _module_of(name: str, facts: ModuleFacts) -> str:
    """The declaring module of a constant that the module or its references contain."""
    if any(constant.name == name for constant in facts.constants):
        return facts.module
    known = facts.external.get(name)
    return known.module if known else facts.module
