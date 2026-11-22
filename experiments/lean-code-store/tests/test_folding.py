"""Tests of `lean_code_store.folding`: each rule of "Generated constants" on a small module."""

from __future__ import annotations

import pytest

from factories import constant, module, span
from lean_code_store.folding import Decision, decide_module, resolver

pytestmark = [pytest.mark.unit, pytest.mark.timeout(5)]

SOURCE = "\n".join([
    "inductive Color where",          # line 1
    "  | red",                        # line 2
    "  deriving Repr",                # line 3
    "def helperUser : Nat := 1",      # line 4
    "deriving instance BEq for Color",  # line 5
])


def test_rules_one_and_two_fold_into_the_type() -> None:
    """A constructor (rule 1) and an instance of a `deriving` clause (rule 2) fold into the type."""
    facts = module(constant("Color", kind="inductive", span=span(1, 0, 3, 15), selection=span(1, 10, 1, 15)),
                   constant("Color.red", kind="constructor", span=span(2, 4, 2, 7), table_parent="Color"),
                   constant("instReprColor", span=span(3, 11, 3, 15), instance=True))
    decisions = decide_module(facts, SOURCE)
    assert decisions["Color.red"] == Decision("generated", "1", "Color")
    assert decisions["instReprColor"] == Decision("generated", "2", "Color")
    assert decisions["Color"] == Decision("declaration", "4")


def test_rule_three_gives_a_helper_the_instance_with_its_range_and_name_prefix() -> None:
    """Instances of a `deriving instance` command are declarations; their helpers fold into them."""
    command = span(5, 18, 5, 21)
    facts = module(constant("instBEqColor", span=command, instance=True),
                   constant("instBEqColor.beq", span=command),
                   constant("instBEqTag", span=command, instance=True),
                   constant("lonely", span=span(4, 4, 4, 14)))
    decisions = decide_module(facts, SOURCE)
    assert decisions["instBEqColor"] == Decision("declaration", "3")
    assert decisions["instBEqColor.beq"] == Decision("generated", "3", "instBEqColor")
    assert decisions["lonely"] == Decision("declaration", "4")


def test_rule_three_reports_a_helper_with_several_candidates() -> None:
    """A helper that two instances of its range refer to has no single parent."""
    command = span(5, 18, 5, 21)
    facts = module(constant("instA", span=command, instance=True, references=(("aux", "M"),)),
                   constant("instB", span=command, instance=True, references=(("aux", "M"),)),
                   constant("aux", span=command))
    assert decide_module(facts, SOURCE)["aux"] == Decision("reported", "helper with several candidates")


def test_rule_four_keeps_a_written_name_that_looks_generated() -> None:
    """`Foo._helper` with a range is a declaration, not a generated constant."""
    facts = module(constant("Foo._helper", span=span(4, 0, 4, 20)))
    assert decide_module(facts, SOURCE)["Foo._helper"] == Decision("declaration", "4")


def test_rule_five_folds_a_constant_without_range_into_its_prefix() -> None:
    """`f.match_1` and `f._proof_1` fold into `f`; the fold is followed across modules."""
    facts = module(constant("f", span=span(4, 0, 4, 20)), constant("f.match_1"), constant("f._proof_1"),
                   constant("g.eq_1"), external=(constant("g", module="N", span=span(1, 0, 1, 9)),))
    decisions = decide_module(facts, SOURCE)
    assert decisions["f.match_1"] == Decision("generated", "5", "f")
    assert decisions["g.eq_1"] == Decision("generated", "5", "g")
    resolve = resolver(facts, decisions, lambda m, n: (m, n), lambda m: False)
    assert resolve("M", "f._proof_1") == ("M", "f")
    assert resolve("M", "g.eq_1") == ("N", "g")


def test_rule_five_as_specified_reports_other_generated_names() -> None:
    """The specified rule 5 decides only names whose last component is `_x`, `match_n` or `eq_n`."""
    facts = module(constant("T", kind="inductive", span=span(1, 0, 3, 15)), constant("T.ctorIdx"),
                   constant("_private.N.0.T.eq_1"))
    decisions = decide_module(facts, SOURCE)
    assert decisions["T.ctorIdx"] == Decision("reported", "no rule")
    assert decisions["_private.N.0.T.eq_1"] == Decision("reported", "no rule")
