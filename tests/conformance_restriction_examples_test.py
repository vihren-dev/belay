"""Each example of `conformance.restriction_examples` reaches its restriction.

The registry of model restrictions (`Resolution/Restrictions.lean`) must not keep a
restriction that no SQL reaches: such a restriction is dead code that the
documentation table would still show to users. Each example runs through the
pinned frontend and the `conformance-runner` of the conformance runtime, whose
model must refuse it with the example's restriction id.
"""

from pathlib import Path

import pytest

from conformance.restriction_examples import EXAMPLES, resolve_example

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library")]


@pytest.mark.parametrize("identifier", sorted(EXAMPLES))
def test_example_reaches_its_restriction(runtime_root: Path, identifier: str) -> None:
    """The model refuses the example with its restriction id."""
    schema, migration = EXAMPLES[identifier]
    result = resolve_example(runtime_root, schema, migration)
    assert ("restricted" in result, result.get("restriction")) == (True, identifier), result
