"""The rows of `entities`, `entity_texts` and `entity_references` for one file version.

This is the functional core of the extractor: it reads the facts of the module, the decisions
of the folding rules, the source text and the `.ilean` usages, and gives rows and counts.
"""

from __future__ import annotations

from collections import Counter
from collections.abc import Callable
from dataclasses import dataclass, field

from lean_code_store.facts import ConstantFacts, ModuleFacts, Range
from lean_code_store.folding import Decision, Declaration
from lean_code_store.keys import sha256_hex
from lean_code_store.mentions import Usage, mention_user
from lean_code_store.source import range_text

Row = dict[str, str]
"""One row of a table, column name to value."""


@dataclass
class FileRows:
    """The rows of one file version and the counts that the findings record reports."""

    entities: list[Row] = field(default_factory=list)
    texts: dict[str, str] = field(default_factory=dict)
    references: list[Row] = field(default_factory=list)
    counts: Counter[str] = field(default_factory=Counter)
    reported: list[tuple[str, str]] = field(default_factory=list)
    decisions: dict[str, str] = field(default_factory=dict)
    """The decision of each constant as `STATUS by RULE`, for the findings report."""


def entity_kind(facts: ConstantFacts) -> str:
    """The `entities.kind`: the class, structure and instance tables replace the kernel kind."""
    if facts.is_class:
        return "class"
    if facts.is_structure:
        return "structure"
    if facts.is_instance:
        return "instance"
    return facts.kernel_kind


def declaration_text(facts: ConstantFacts, command: Range | None, lines: list[str]) -> str:
    """The full range of a declaration; for a `deriving instance` instance, the whole command.

    `command` is the range that Lean's parser gives for the command of the instance.
    """
    assert facts.range is not None
    return range_text(lines, command if command is not None else facts.range)


def build_rows(file_key: str, facts: ModuleFacts, decisions: dict[str, Decision], source: str,
               usages: list[Usage], resolve: Callable[[str, str], Declaration | None]) -> FileRows:
    """All rows of one file version, with generated constants folded at the two ends."""
    rows = FileRows()
    lines = source.split("\n")
    declarations: dict[str, Range] = {}
    for constant in facts.constants:
        decision = decisions[constant.name]
        rows.counts[f"rule {decision.rule} {decision.status}"] += 1
        rows.decisions[constant.name] = f"{decision.status} by {decision.rule}"
        if decision.status == "reported":
            rows.reported.append((constant.name, decision.rule))
        if decision.status == "generated" and resolve(facts.module, constant.name) is None:
            rows.counts["generated, no declaration at the end of its parents"] += 1
            rows.reported.append((constant.name, "generated, no declaration at the end of its parents"))
        if decision.status != "declaration":
            continue
        assert constant.range is not None
        declarations[constant.name] = constant.range
        text = declaration_text(constant, facts.deriving_commands.get(constant.name), lines)
        digest = sha256_hex(text.encode())
        rows.texts[digest] = text
        rows.entities.append({"file_key": file_key, "name": constant.name,
                              "kind": entity_kind(constant), "text_sha256": digest})
    found: set[tuple[str, str, str, str, str]] = set()

    def add(user: Declaration | None, target: tuple[str, str], kind: str) -> None:
        folded = resolve(*target)
        if folded is None:
            rows.counts["target reported, kept unfolded"] += 1
            folded = target
        user_module, user_name = user if user is not None else (facts.module, "")
        if (user_module, user_name) != folded:
            found.add((user_module, user_name, folded[0], folded[1], kind))

    for constant in facts.constants:
        user = resolve(facts.module, constant.name)
        if user is None:
            rows.counts["user reported, relationships left out"] += 1
            continue
        for name, module in constant.type_references:
            add(user, (module, name), "type")
        for name, module in constant.body_references:
            add(user, (module, name), "body")
        if constant.is_structure:
            for name, module in constant.parents:
                add(user, (module, name), "extends")
        if constant.is_instance and constant.instance_class:
            add(user, (_module(constant.instance_class, facts), constant.instance_class), "instance_of")
    own = {constant.name for constant in facts.constants}
    for usage in usages:
        if usage.target_name not in own and usage.target_name not in facts.external:
            rows.counts["mention of a name that is not a constant"] += 1
            continue
        target_module = _module(usage.target_name, facts)
        if target_module != usage.target_module:
            rows.counts["mention whose .ilean module differs from the declaring module"] += 1
        user = mention_user(usage, facts.module, resolve, declarations)
        rows.counts[f"mention user from {user.source}"] += 1
        add(user.user, (target_module, usage.target_name), "mention")
    rows.references = [{"file_key": file_key, "user_module": um, "user_name": un,
                        "target_module": tm, "target_name": tn, "kind": kind}
                       for um, un, tm, tn, kind in sorted(found)]
    return rows


def _module(name: str, facts: ModuleFacts) -> str:
    """The declaring module of a constant of the module or of one that it refers to."""
    known = facts.external.get(name)
    return known.module if known is not None else facts.module
