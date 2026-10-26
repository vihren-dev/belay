"""Helpers for the actual Lean server observations of the SQL name information (editor task, part 2b)."""

from tests.lean_server_support import LeanServer, hover, position

Range = dict[str, dict[str, int]]


def span_of(source: str, spelling: str, occurrence: int, token: str) -> Range:
    """The LSP range of `token`, which starts at the given occurrence of `spelling` in the source."""
    start = position(source, spelling, occurrence)
    return {"start": start, "end": {**start, "character": start["character"] + len(token.encode("utf-16-le")) // 2}}


def name_hover(server: LeanServer, uri: str, source: str, spelling: str, occurrence: int, token: str) -> str:
    """The hover text of one SQL name occurrence; the hover range must be exactly the written token."""
    expected = span_of(source, spelling, occurrence, token)
    result = hover(server, uri, expected["start"])
    contents = result["contents"]
    assert isinstance(contents, dict) and isinstance(contents["value"], str), result
    assert result["range"] == expected, result
    return contents["value"]


def hover_text_or_none(server: LeanServer, uri: str, source: str, spelling: str, occurrence: int) -> str:
    """The hover text at one occurrence, or the empty text when the server has no hover there."""
    start = position(source, spelling, occurrence)
    result = server.request("textDocument/hover", {"textDocument": {"uri": uri}, "position": start})
    if not isinstance(result, dict):
        return ""
    contents = result["contents"]
    assert isinstance(contents, dict) and isinstance(contents["value"], str), result
    return contents["value"]


def corrections(server: LeanServer, uri: str, source: str, spelling: str, occurrence: int,
                token: str) -> list[tuple[str, str]]:
    """The (title, new text) pairs of the quick fixes that the server offers for one written name.

    The server gives all suggestions of a line, so the edits are filtered to the range of `token`."""
    expected = span_of(source, spelling, occurrence, token)
    actions = server.request("textDocument/codeAction", {
        "textDocument": {"uri": uri}, "range": expected, "context": {"diagnostics": []}})
    assert isinstance(actions, list), actions
    found: list[tuple[str, str]] = []
    for action in actions:
        for change in action["edit"]["documentChanges"]:
            for edit in change["edits"]:
                if edit["range"] == expected:
                    found.append((action["title"], edit["newText"]))
    return sorted(found)
