"""Find commands in approved Lean sources that run code while Lean elaborates them (ADR 0010, "Decisions").

Reuse of cached contract outputs is correct when compiling a module depends only on
its inputs. Code that runs during elaboration can read the clock, the environment
or files, and then a cached output can differ from a fresh one. Such code is easy
to see in a review; `prepare` points the reviewer at it with a warning. It is a
lexical scan of command keywords at the start of a line, not a proof that a module
runs no code: a reviewer still reads the contract.
"""

from collections.abc import Mapping
import re

ELABORATION_COMMANDS = ("#eval", "#eval!", "run_cmd", "run_elab", "run_meta", "initialize", "builtin_initialize",
                        "elab", "elab_rules", "macro", "macro_rules", "syntax")
"""Commands that run user code during elaboration, or define syntax that does."""

COMMAND = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|local|scoped)\s+)*(#?[A-Za-z_!]+)")
"""A command keyword at the start of a line, after optional attributes and modifiers."""


def elaboration_commands(sources: Mapping[str, bytes]) -> list[str]:
    """`Module:line: command` for each elaboration command in the given module sources."""
    found = []
    for module, contents in sorted(sources.items()):
        in_comment = False
        for number, line in enumerate(contents.decode("utf-8", errors="replace").splitlines(), start=1):
            stripped = line.strip()
            if in_comment or stripped.startswith("/-"):
                in_comment = "-/" not in stripped
                continue
            match = COMMAND.match(line)
            if match and match.group(1) in ELABORATION_COMMANDS:
                found.append(f"{module}:{number}: {match.group(1)}")
    return found
