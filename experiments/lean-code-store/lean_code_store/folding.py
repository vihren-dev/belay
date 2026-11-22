"""The rules of "Generated constants" of the Lean code store specification, on one module.

Each constant of a module is decided as a written declaration, as a generated constant with
one parent, or as reported. `lean_code_store.resolve` then follows the parents to a written
declaration.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
import re

from lean_code_store.facts import ConstantFacts, ModuleFacts, Range
from lean_code_store.source import name_components, range_text, user_name

Declaration = tuple[str, str]
"""A written declaration as `(module, name)`."""

MACRO_SCOPES = re.compile(r"\._@\.")
"""The marker of macro scopes in a Lean name, for example `initFn._@.M._hyg.2`."""

INSTANCE_KEYWORD = re.compile(r"\binstance\b")
"""The keyword of an `instance` command; the range of an instance of a `deriving instance`
command is the class name only and does not contain it."""

MAX_DEPTH = 64
"""Bound of a chain of parents; a longer chain is reported as a cycle."""


@dataclass(frozen=True)
class Decision:
    """The decision of the rules for one constant of the module."""

    status: str
    """`declaration`, `generated` or `reported`."""
    rule: str
    """The rule that decided (`1` to `5`; `5 private` when rule 5 found the parent only after
    the private prefix was removed), or the cause of a report."""
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


def _prefix(name: str) -> str | None:
    """The name without its final component, or `None` for a name of one component."""
    components = name_components(name)
    return name[: len(name) - len(components[-1]) - 1] if len(components) >= 2 else None


def rule_five_parent(name: str, is_constant: Callable[[str], bool]) -> tuple[str, str] | None:
    """The parent of a constant without range, with the rule label, by its name.

    The parent is the name without its final component when that is a constant (`5`).
    Lean gives an equation lemma that it generates in a module that uses a definition of
    another module a private name of the using module, for example
    `_private.U.0.f.match_1.eq_1`. For such a name the parent is looked up also after the
    private prefix is removed (`5 private`).
    """
    prefix = _prefix(name)
    if prefix is not None and is_constant(prefix):
        return prefix, "5"
    public = user_name(name)
    prefix = _prefix(public) if public != name else None
    if prefix is not None and is_constant(prefix):
        return prefix, "5 private"
    return None


def _rule_three_instance(constant: ConstantFacts, facts: ModuleFacts, lines: list[str]) -> Decision:
    """An instance with a range is a declaration, unless its range shows a `deriving instance`
    command (no `instance` keyword) whose range the parser did not give: then it is reported."""
    assert constant.range is not None
    if (constant.name not in facts.deriving_commands
            and not INSTANCE_KEYWORD.search(range_text(lines, constant.range))):
        return Decision("reported", "deriving instance command not parsed")
    return Decision("declaration", "3")


def _macro_scoped_with_range(constant: ConstantFacts, remaining: list[ConstantFacts]) -> Decision:
    """A constant with macro scopes and a range, for example the `initFn` of `initialize`.

    Its parent is the one constant without macro scopes that has the same range; with no such
    constant or more than one, it is reported.
    """
    partners = [c.name for c in remaining if c.range == constant.range and c.name != constant.name
                and not MACRO_SCOPES.search(c.name)]
    if len(partners) == 1:
        return Decision("generated", "4 macro scopes", partners[0])
    cause = "no constant" if not partners else "several constants"
    return Decision("reported", f"macro scopes, {cause} with the same range")


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
            decisions[constant.name] = _rule_three_instance(constant, facts, lines)
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
        elif constant.range is not None and MACRO_SCOPES.search(constant.name):
            decisions[constant.name] = _macro_scoped_with_range(constant, remaining)
        elif constant.range is not None:
            decisions[constant.name] = Decision("declaration", "4")
        elif (found := rule_five_parent(constant.name,
                                         lambda n: n in own or n in facts.external)) is not None:
            decisions[constant.name] = Decision("generated", found[1], found[0])
        else:
            decisions[constant.name] = Decision("reported", "no rule")
    return decisions
