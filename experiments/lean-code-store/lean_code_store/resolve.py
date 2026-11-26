"""Follow the parents of generated constants to the written declaration, also across modules.

The decisions of one module come from `lean_code_store.folding`. A constant of another selected
module folds through that module's own stored fold; a constant outside the selection folds by
rules 1 and 5 only, because the other rules need the ranges of all constants of its file.
"""

from __future__ import annotations

from collections.abc import Callable

from lean_code_store.facts import ConstantFacts, ModuleFacts
from lean_code_store.folding import MAX_DEPTH, Declaration, Decision, rule_five_parent

ImportedResolver = Callable[[str, str], Declaration | None]
"""Resolves a constant of another selected module through that module's own folding."""


def _external_parent(facts: ConstantFacts, external: dict[str, ConstantFacts]) -> str | None:
    """The parent of a constant of a module outside the selection, by rules 1 and 5 only."""
    if facts.table_parent is not None:
        return facts.table_parent
    if facts.range is not None:
        return None
    found = rule_five_parent(facts.name, lambda n: n in external)
    return found[0] if found is not None else None


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
