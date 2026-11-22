"""Tests of `lean_code_store.folding`: each rule of "Generated constants" on a small module."""

from __future__ import annotations

import pytest

from factories import constant, module, span
from lean_code_store.folding import Decision, decide_module
from lean_code_store.resolve import resolver

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
                   constant("lonely", span=span(4, 4, 4, 14)),
                   deriving_commands={"instBEqColor": span(5, 0, 5, 31), "instBEqTag": span(5, 0, 5, 31)})
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


def test_rule_five_reads_any_final_component_and_names_without_private_prefix() -> None:
    """`T.ctorIdx` folds into `T`; the private equation lemma of a match function of another
    module folds into that match function; a match function of an `example` is reported."""
    facts = module(constant("T", kind="inductive", span=span(1, 0, 3, 15)), constant("T.ctorIdx"),
                   constant("_private.M.0.g.match_1.eq_1"), constant("_private.M.0.match_1"),
                   external=(constant("g.match_1", module="N"),))
    decisions = decide_module(facts, SOURCE)
    assert decisions["T.ctorIdx"] == Decision("generated", "5", "T")
    assert decisions["_private.M.0.g.match_1.eq_1"] == Decision("generated", "5 private", "g.match_1")
    assert decisions["_private.M.0.match_1"] == Decision("reported", "no rule")


def test_a_generated_constant_with_a_reported_parent_is_reported() -> None:
    """A helper whose parent is reported is named in the report with its cause, and has no user."""
    from lean_code_store.rows import build_rows
    facts = module(constant("_private.M.0.match_1"), constant("_private.M.0.match_1.eq_1"))
    decisions = decide_module(facts, SOURCE)
    resolve = resolver(facts, decisions, lambda m, n: (m, n), lambda m: False)
    rows = build_rows("k" * 64, facts, decisions, SOURCE, [], resolve)
    assert ("_private.M.0.match_1", "no rule") in rows.reported
    assert ("_private.M.0.match_1.eq_1", "generated, no declaration at the end of its parents") in rows.reported


def test_an_instance_of_an_unparsed_deriving_instance_command_is_reported() -> None:
    """An instance whose range has no `instance` keyword and no parsed command is reported."""
    facts = module(constant("instBEqColor", span=span(5, 18, 5, 21), instance=True))
    assert decide_module(facts, SOURCE)["instBEqColor"] == Decision(
        "reported", "deriving instance command not parsed")


def test_a_macro_scoped_constant_folds_into_the_one_constant_with_its_range() -> None:
    """`initFn` of an `initialize` command folds into the declared constant; with two
    constants of its range, as `register_simp_attr` gives, it is reported."""
    one, two = span(4, 0, 4, 25), span(1, 0, 3, 15)
    facts = module(constant("counter", kind="opaque", span=one),
                   constant("_private.M.0.initFn._@.M.1._hygCtx._hyg.2", span=one),
                   constant("arms", span=two), constant("arms_proc", span=two),
                   constant("ext._@.M.1._hygCtx._hyg.3", span=two))
    decisions = decide_module(facts, SOURCE)
    assert decisions["_private.M.0.initFn._@.M.1._hygCtx._hyg.2"] == Decision(
        "generated", "4 macro scopes", "counter")
    assert decisions["ext._@.M.1._hygCtx._hyg.3"] == Decision(
        "reported", "macro scopes, several constants with the same range")
    assert decisions["arms_proc"] == Decision("declaration", "4")
