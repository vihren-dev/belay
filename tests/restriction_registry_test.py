"""The registry of model restrictions and its documentation table.

`Resolution/Restrictions.lean` lists every model restriction of name resolution as a
constructor of `RestrictionKind`, and `Resolution/RestrictionText.lean` gives each one
its stable id. `docs/semantic-subset.md` must list every id in its restriction table,
so that the documentation cannot drift from the registry, and
`conformance/restriction_examples.py` must have an example script for every id, so that
no restriction is left that SQL cannot reach. Lean checks that the ids are distinct and
that `RestrictionKind.all` holds every kind.
"""

import re
from pathlib import Path

import pytest

from conformance.restriction_examples import EXAMPLES

pytestmark = [pytest.mark.unit]
ROOT = Path(__file__).resolve().parents[1]
RESOLUTION = ROOT / "packages/belay-sqlite/Belay/Sqlite/Resolution"


def registry_ids() -> dict[str, str]:
    """The id of each constructor, read from `RestrictionKind.id`."""
    text = (RESOLUTION / "RestrictionText.lean").read_text()
    section = text.split("def RestrictionKind.id", 1)[1].split("def RestrictionKind.message", 1)[0]
    return dict(re.findall(r'\| \.(\w+) => "([^"]*)"', section))


def constructors() -> list[str]:
    """The constructors of `RestrictionKind`, in order."""
    return re.findall(r"^  \| (\w+)$", (RESOLUTION / "Restrictions.lean").read_text(), re.MULTILINE)


def documented_ids() -> list[str]:
    """The ids in the restriction table of `docs/semantic-subset.md`."""
    text = (ROOT / "docs/semantic-subset.md").read_text()
    section = text.split("### Restriction registry", 1)[1].split("\n## ", 1)[0]
    return re.findall(r"^\| `([^`]+)` \|", section, re.MULTILINE)


def test_every_constructor_has_a_well_formed_id() -> None:
    """Each constructor has exactly one id of lowercase words joined by hyphens."""
    ids = registry_ids()
    assert set(ids) == set(constructors()), set(ids) ^ set(constructors())
    assert all(re.fullmatch(r"[a-z]+(-[a-z0-9]+)*", identifier) for identifier in ids.values()), ids


def test_documentation_lists_every_id_once() -> None:
    """The documentation table and the registry list the same ids, each once."""
    documented = documented_ids()
    assert len(documented) == len(set(documented)), documented
    assert set(documented) == set(registry_ids().values()), set(documented) ^ set(registry_ids().values())


def registries() -> dict[str, str]:
    """The registry of each constructor, read from `RestrictionKind.registry`."""
    text = (RESOLUTION / "RestrictionRegistry.lean").read_text().split("def RestrictionKind.registry", 1)[1]
    return {name: registry for names, registry in re.findall(r"((?:\s*\|\s*\.\w+)+)\s*=>\s*\.(\w+)", text)
            for name in re.findall(r"\.(\w+)", names)}


def test_each_id_is_documented_under_its_registry() -> None:
    """`RestrictionKind.registry` gives every constructor one registry, and the documentation
    lists each id in the table of that registry."""
    assert set(registries()) == set(constructors()), set(registries()) ^ set(constructors())
    text = (ROOT / "docs/semantic-subset.md").read_text().split("### Restriction registry", 1)[1].split("\n## ", 1)[0]
    parts = dict(re.findall(r"#### (\w+)\n(.*?)(?=\n#### |\Z)", text, re.DOTALL))
    for name, registry in registries().items():
        identifier = registry_ids()[name]
        assert f"| `{identifier}` |" in parts[registry.capitalize()], (identifier, registry)


def test_every_id_has_one_example() -> None:
    """`conformance.restriction_examples` has an example for each registry id and for no other name."""
    ids = set(registry_ids().values())
    assert set(EXAMPLES) == ids, set(EXAMPLES) ^ ids
