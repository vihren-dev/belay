/* Give the symbols of each parser, tokenizer and grammar a unique prefix, so that one library
** can link several of each.
**
** A parser's functions carry the Lemon prefix that the generation gave it (PARSER_PREFIX, for
** example Syntax_0123456789abcdef). A tokenizer unit is compiled once for each tokenizer
** identity with TOKENIZER_PREFIX, and a grammar unit once for each pair of a parser and a
** tokenizer with all three prefixes. The tokenizer and grammar units include this header first.
*/
#ifndef BELAY_SQLITE_LIBRARY_PREFIX_H
#define BELAY_SQLITE_LIBRARY_PREFIX_H
#ifndef TOKENIZER_PREFIX
#error "TOKENIZER_PREFIX must name the tokenizer's prefix"
#endif
#define LIBRARY_JOIN_(left, right) left##right
#define LIBRARY_JOIN(left, right) LIBRARY_JOIN_(left, right)

#define native_token LIBRARY_JOIN(TOKENIZER_PREFIX, _native_token)
#define native_name LIBRARY_JOIN(TOKENIZER_PREFIX, _native_name)
#define native_space LIBRARY_JOIN(TOKENIZER_PREFIX, _native_space)
#define native_illegal LIBRARY_JOIN(TOKENIZER_PREFIX, _native_illegal)
#define native_semicolon LIBRARY_JOIN(TOKENIZER_PREFIX, _native_semicolon)

#ifdef GRAMMAR_PREFIX
#ifndef PARSER_PREFIX
#error "PARSER_PREFIX must name the Lemon prefix of the grammar's parser"
#endif
#define SyntaxAlloc LIBRARY_JOIN(PARSER_PREFIX, Alloc)
#define SyntaxFree LIBRARY_JOIN(PARSER_PREFIX, Free)
#define Syntax PARSER_PREFIX
#define grammar_parse LIBRARY_JOIN(GRAMMAR_PREFIX, _parse)
#endif
#endif
