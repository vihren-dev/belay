/* The parse loop of one grammar in the parser library: a parser with a tokenizer.
**
** The parse loop feeds the tokenizer's tokens to the parser and adds SQLite's final
** semicolon when the text has none. library.c checks the input and writes the document;
** this file only builds the syntax tree in a Context. tokens.h gives the tokenizer's token
** numbers and syntax.h the parser's.
*/
#include "library_prefix.h"
#include "runtime.h"
#include "syntax.h"
#include "tokens.h"

void *SyntaxAlloc(void *(*allocate)(size_t));
void Syntax(void *parser, int kind, int token, Context *ctx);
void SyntaxFree(void *parser, void (*release)(void *));
int native_token(const char *text, int previous, int *kind);
const char *native_name(int kind);
int native_space(int kind);
int native_illegal(int kind);
int native_semicolon(void);

/* Map each token of the tokenizer to the parser's token of the same name. */
static int parser_token(int kind){
  switch(kind){
#include "token_map.inc"
    default: return 0;
  }
}

/* Build the syntax tree of a checked, NUL-terminated text of size bytes into ctx. */
void grammar_parse(Context *ctx, const char *text, int size){
  void *parser = SyntaxAlloc(malloc);
  int previous = -1;
  if(!parser){ ctx->error = 2; return; }
  while(ctx->offset < size && !ctx->error){
    int kind;
    int length = native_token(text + ctx->offset, previous, &kind);
    if(length <= 0 || native_illegal(kind)){ ctx->error = 1; break; }
    if(!native_space(kind)){
      Node token = {native_name(kind), ctx->offset, ctx->offset + length, 0, NULL};
      int index = append(ctx, token);
      if(!ctx->error) Syntax(parser, parser_token(kind), index, ctx);
      previous = kind;
    }
    if(!ctx->error) ctx->offset += length;
  }
  if(!ctx->error && previous != native_semicolon()){
    Node token = {"SEMI", size, size, 0, NULL};
    int index = append(ctx, token);
    if(!ctx->error) Syntax(parser, P_SEMI, index, ctx);
  }
  if(!ctx->error) Syntax(parser, 0, 0, ctx);
  SyntaxFree(parser, free);
}
