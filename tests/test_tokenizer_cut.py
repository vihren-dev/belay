"""The tokenizer cut takes its parts by name, with the conditionals that enclose them.

These tests check `parser/tokenizer_cut.py` on a small synthetic amalgamation. The
generation runs it on each release's `sqlite3.c`, and its slice check compares the compiled
cut with the whole file.
"""

import pytest

from parser.tokenizer_cut import NAMES, cut_tokenizer, token_names, tokens_header

pytestmark = [pytest.mark.unit, pytest.mark.parser]
DEFINITIONS = "".join(f"#define {name} 1\n" for name in NAMES)
"""One definition of each name of the cut."""
AMALGAMATION = f"""#include <assert.h>
#include <stdio.h>
#ifdef SQLITE_ASCII
{DEFINITIONS}#else
#define u8 2
#endif
#define UNUSED 3
/************** Begin file parse.h *******************************************/
#define TK_SEMI 1
#define TK_ID 2
/************** End of parse.h ***********************************************/
SQLITE_PRIVATE const unsigned char sqlite3UpperToLower[] = {{
  0
}};
SQLITE_PRIVATE const unsigned char sqlite3CtypeMap[256] = {{
  0
}};
static int unused(void){{ return 0; }}
static const YYCODETYPE yyFallback[] = {{
  0
}};
SQLITE_PRIVATE int sqlite3ParserFallback(int iToken){{
  return 0;
}}
/************** Begin file tokenize.c ****************************************/
static int getToken(void){{ return 1; }}
SQLITE_PRIVATE int sqlite3RunParser(Parse *pParse, const char *zSql){{
}}
#define u8 4
"""
"""An amalgamation with every part of the cut, some code that the cut leaves out, and a later
definition of a name after `sqlite3RunParser`."""


@pytest.mark.timeout(10)
def test_the_cut_keeps_named_parts_in_order_with_their_conditionals() -> None:
    """The cut has every region and every definition of a name before `sqlite3RunParser`, in
    amalgamation order, with all directive lines of the conditional around them; it leaves out
    other includes, other definitions, other functions and everything after the tokenizer."""
    cut = cut_tokenizer(AMALGAMATION)
    lines = cut.splitlines()
    assert lines[:3] == ["#include <assert.h>", "#ifdef SQLITE_ASCII", "#define u8 1"]
    assert "#else" in lines and "#define u8 2" in lines and "#endif" in lines
    for absent in ("#include <stdio.h>", "#define UNUSED 3", "static int unused", "sqlite3RunParser", "#define u8 4"):
        assert absent not in cut, absent
    assert "static int getToken(void){ return 1; }" in lines
    assert lines.index("#define TK_SEMI 1") < lines.index("}") < lines.index("static int getToken(void){ return 1; }")


@pytest.mark.timeout(10)
def test_the_cut_fails_for_a_missing_part_and_gives_the_token_files() -> None:
    """A missing region or name fails with its name; the token files list the cut's tokens."""
    with pytest.raises(ValueError, match="the fallback table"):
        cut_tokenizer(AMALGAMATION.replace("yyFallback", "yyOther"))
    with pytest.raises(ValueError, match="no definition of testcase"):
        cut_tokenizer(AMALGAMATION.replace("#define testcase 1\n", ""))
    cut = cut_tokenizer(AMALGAMATION)
    assert tokens_header(cut) == "#define TK_SEMI 1\n#define TK_ID 2\n"
    assert token_names(cut) == 'case TK_SEMI: return "SEMI";\ncase TK_ID: return "ID";\n'
