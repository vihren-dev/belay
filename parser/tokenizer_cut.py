"""Cut the tokenizer of one SQLite release out of its amalgamation `sqlite3.c`.

The parser library compiles a release's own tokenizer, but needs only a small part of the
265,000 lines of `sqlite3.c`: `sqlite3GetToken`, the keyword code and tables, the character
tables, the token numbers, the fallback table that the window lookahead reads, and the types
and macros that they use. This module takes these parts by name, as unchanged text and in
their order in the amalgamation. It runs no preprocessor, so the cut holds no platform's
choices. For each part, it also keeps the directive lines of every conditional that encloses
the part, so the part is compiled under the same conditions as in the amalgamation.

`parser/slice_check.py` proves that the cut compiles to the same machine code as the whole
file. When a release needs a definition that the lists below do not name, the cut fails to
compile or the slice check fails, and the fix is a new name here (ADR 0029, D2).
"""

from dataclasses import dataclass
import re

REGION_LIMIT = re.compile(r"^SQLITE_PRIVATE int sqlite3RunParser\(Parse \*pParse", re.M)
"""The first function of `tokenize.c` that the tokenizer does not use. Every part of the cut
comes before it, so later copies of SQLite's macros (in extensions) are never taken."""


@dataclass(frozen=True)
class Region:
    """A run of lines from the first match of `start` to the next match of `end`."""

    name: str
    start: str
    end: str
    end_included: bool


REGIONS = (
    Region("the token numbers of parse.h", r"^/\*+ Begin file parse\.h \*+/$",
           r"^/\*+ End of parse\.h \*+/$", True),
    Region("the case-folding table", r"^SQLITE_PRIVATE const unsigned char sqlite3UpperToLower\[\] = \{$",
           r"^\};$", True),
    Region("the character-class table", r"^SQLITE_PRIVATE const unsigned char sqlite3CtypeMap\[256\] = \{$",
           r"^\};$", True),
    Region("the fallback table", r"^static const YYCODETYPE yyFallback\[\] = \{$", r"^\};$", True),
    Region("the fallback function", r"^SQLITE_PRIVATE int sqlite3ParserFallback\(int iToken\)\{$",
           r"^\}$", True),
    Region("the tokenizer and keyword code", r"^/\*+ Begin file tokenize\.c \*+/$",
           REGION_LIMIT.pattern, False),
)
"""The regions of the cut. The last one is `tokenize.c` with `keywordhash.h`, up to
`sqlite3RunParser`: the code that the grammar identity of ADR 0007 digested."""
NAMES = ("u8", "i64", "sqlite_int64", "UINT8_TYPE", "SQLITE_PRIVATE", "NDEBUG", "testcase",
         "SQLITE_DIGIT_SEPARATOR", "sqlite3Isdigit", "sqlite3Isxdigit", "sqlite3Isspace", "SQLITE_ASCII",
         "YYCODETYPE", "YYFALLBACK", "SQLITE_OK", "SQLITE_ERROR", "sqlite3GetToken",
         "deliberate_fall_through")
"""The macros, types and declarations that the regions use. Each name takes every `#define`,
`typedef` or `SQLITE_PRIVATE` declaration of that name before `REGION_LIMIT`."""
HEADERS = ("assert.h",)
"""The C library headers that the regions use, by their `#include` lines."""
CONDITIONAL = re.compile(r"^\s*#\s*(if|ifdef|ifndef|elif|else|endif)\b")
"""A preprocessor conditional directive line."""
TOKEN_DEFINE = re.compile(r"^#define TK_(\w+)\s+(\d+)$", re.M)
"""A token number of `parse.h`."""


def _region_lines(lines: list[str], region: Region) -> range:
    """Return the line numbers of one region, or fail with its name."""
    start = next((i for i, line in enumerate(lines) if re.match(region.start, line)), None)
    end = None if start is None else next(
        (i for i in range(start + 1, len(lines)) if re.match(region.end, lines[i])), None)
    if start is None or end is None:
        raise ValueError(f"Cannot find {region.name} in sqlite3.c; check the release or "
                         "the regions of parser/tokenizer_cut.py")
    return range(start, end + 1 if region.end_included else end)


def _named_lines(lines: list[str], limit: int, name: str) -> set[int]:
    """Return the lines of every definition of name before limit, with continuation lines."""
    escaped = re.escape(name)
    definition = re.compile(rf"^\s*#\s*define\s+{escaped}\b|^\s*typedef\b.*\b{escaped}\s*;"
                            rf"|^SQLITE_PRIVATE [^(]*\b{escaped}\(.*\);$")
    chosen: set[int] = set()
    for index in (i for i in range(limit) if definition.match(lines[i])):
        chosen.add(index)
        while lines[index].endswith("\\"):
            index += 1
            chosen.add(index)
    if not chosen:
        raise ValueError(f"sqlite3.c has no definition of {name}; remove it from NAMES in "
                         "parser/tokenizer_cut.py or check the release")
    return chosen


def _include_line(lines: list[str], limit: int, header: str) -> int:
    """Return the line of the first `#include <header>` before limit."""
    pattern = re.compile(rf"^\s*#\s*include\s+<{re.escape(header)}>")
    found = next((i for i in range(limit) if pattern.match(lines[i])), None)
    if found is None:
        raise ValueError(f"sqlite3.c does not include <{header}>; check HEADERS in parser/tokenizer_cut.py")
    return found


def _enclosing_directives(lines: list[str], chosen: set[int]) -> set[int]:
    """Return all directive lines of each conditional that encloses a chosen line."""
    open_groups: list[int] = []
    groups: dict[int, list[int]] = {}
    enclosing: dict[int, tuple[int, ...]] = {}
    for index, line in enumerate(lines):
        directive = CONDITIONAL.match(line)
        if directive and directive.group(1) in ("if", "ifdef", "ifndef"):
            open_groups.append(index)
            groups[index] = [index]
        elif directive and open_groups:
            groups[open_groups[-1]].append(index)
            if directive.group(1) == "endif":
                open_groups.pop()
        enclosing[index] = tuple(open_groups)
    return {directive for index in chosen for group in enclosing[index] for directive in groups[group]}


def cut_tokenizer(amalgamation: str) -> str:
    """Return the tokenizer parts of the amalgamation, as unchanged lines in their order."""
    lines = amalgamation.split("\n")
    limit_match = REGION_LIMIT.search(amalgamation)
    if limit_match is None:
        raise ValueError("Cannot find sqlite3RunParser in sqlite3.c; check the release")
    limit = amalgamation.count("\n", 0, limit_match.start())
    chosen: set[int] = set()
    for region in REGIONS:
        chosen.update(_region_lines(lines, region))
    for name in NAMES:
        chosen |= _named_lines(lines, limit, name)
    chosen.update(_include_line(lines, limit, header) for header in HEADERS)
    chosen |= _enclosing_directives(lines, chosen)
    return "\n".join(lines[index] for index in sorted(chosen)) + "\n"


def token_numbers(cut: str) -> list[tuple[str, int]]:
    """Return the token names and numbers of the cut, in the order of `parse.h`."""
    tokens = [(name, int(number)) for name, number in TOKEN_DEFINE.findall(cut)]
    if not tokens or len({name for name, _ in tokens}) != len(tokens):
        raise ValueError("The tokenizer cut has no token numbers, or names a token twice")
    return tokens


def tokens_header(cut: str) -> str:
    """Return `tokens.h`: the token numbers, for the parse loop that maps them to the parser's."""
    return "".join(f"#define TK_{name} {number}\n" for name, number in token_numbers(cut))


def token_names(cut: str) -> str:
    """Return `token_names.inc`: the name of each token, for the parse tree."""
    return "".join(f'case TK_{name}: return "{name}";\n' for name, _ in token_numbers(cut))
