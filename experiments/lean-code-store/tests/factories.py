"""Small builders of fact records for the unit tests of the prototype."""

from __future__ import annotations

from lean_code_store.facts import ConstantFacts, ModuleFacts, Range, Reference


def constant(name: str, *, module: str = "M", kind: str = "definition", span: Range | None = None,
             selection: Range | None = None, table_parent: str | None = None,
             instance: bool = False, references: tuple[Reference, ...] = (),
             macro_scopes: bool = False) -> ConstantFacts:
    """A constant record with the given facts and no flags."""
    return ConstantFacts(
        name=name, module=module, kernel_kind=kind, range=span, selection=selection or span,
        table_parent=table_parent, is_structure=False, is_class=False, is_instance=instance,
        instance_class=None, parents=(), is_matcher=False, is_reserved=False, lean_auto_decl=False,
        has_macro_scopes=macro_scopes, type_references=(), body_references=references)


def module(*constants: ConstantFacts, external: tuple[ConstantFacts, ...] = (),
           deriving_commands: dict[str, Range] | None = None) -> ModuleFacts:
    """A module `M` with the given constants, referenced constants and parsed command ranges."""
    return ModuleFacts(module="M", imports=(), constants=constants,
                       external={facts.name: facts for facts in external},
                       deriving_commands=deriving_commands or {})


def span(line: int, column: int, end_line: int, end_column: int) -> Range:
    """A range with UTF-16 columns equal to the code point columns."""
    return (line, column, column, end_line, end_column, end_column)
