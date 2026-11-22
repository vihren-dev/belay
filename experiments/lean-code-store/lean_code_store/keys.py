"""The key of a file version, as "The key of a file version" of the specification gives it.

The key is computed before the extraction, from the source text, the build products and the
keys of the direct imports, so that a run extracts only file versions that the store lacks.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
import hashlib

KEY_FORMAT = "lean-code-file-key-v1"
"""The first line of the key input."""


@dataclass(frozen=True)
class KeyInput:
    """The inputs of the key of one file version, other than the keys of its imports."""

    module_name: str
    text_sha256: str
    products: tuple[tuple[str, str], ...]
    """`(file name, SHA-256)` of each build product that the extractor reads."""
    imports: tuple[str, ...]
    """The direct imports of the file."""


def sha256_hex(data: bytes) -> str:
    """The lowercase hexadecimal SHA-256 of bytes."""
    return hashlib.sha256(data).hexdigest()


def file_key(extractor_version: str, lean_version: str, key_input: KeyInput,
             import_keys: Mapping[str, str]) -> str:
    """The key of one file version.

    `import_keys` gives the key of each import that is a file of the snapshot; each other
    import contributes its module name.
    """
    lines = [KEY_FORMAT, extractor_version, lean_version, key_input.module_name,
             key_input.text_sha256]
    lines += [digest for _, digest in sorted(key_input.products)]
    lines += [import_keys.get(module, module) for module in sorted(key_input.imports)]
    return sha256_hex("".join(line + "\n" for line in lines).encode())


def dependency_order(inputs: Mapping[str, KeyInput]) -> list[str]:
    """The selected modules, each after the selected modules that it imports.

    A cycle cannot occur in a built tree; it raises an error that names a module of it.
    """
    order: list[str] = []
    state: dict[str, str] = {}

    def visit(module: str) -> None:
        stack = [(module, iter(sorted(inputs[module].imports)))]
        state[module] = "open"
        while stack:
            current, pending = stack[-1]
            following = next((m for m in pending if m in inputs and state.get(m) != "done"), None)
            if following is None:
                stack.pop()
                state[current] = "done"
                order.append(current)
            elif state.get(following) == "open":
                raise ValueError(f"Import cycle through module {following}; check the build")
            else:
                state[following] = "open"
                stack.append((following, iter(sorted(inputs[following].imports))))

    for module in sorted(inputs):
        if state.get(module) != "done":
            visit(module)
    return order


def snapshot_keys(extractor_version: str, lean_version: str,
                  inputs: Mapping[str, KeyInput]) -> dict[str, str]:
    """The key of each selected file version, computed in dependency order."""
    keys: dict[str, str] = {}
    for module in dependency_order(inputs):
        keys[module] = file_key(extractor_version, lean_version, inputs[module], keys)
    return keys
