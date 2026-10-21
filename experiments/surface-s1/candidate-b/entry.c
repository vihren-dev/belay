/* The entry point of candidate B: parse with the parser library, read its parse document into
** nodes, translate, and write the result in the form of experiments/surface-s1/texts.py.
**
** A real candidate B would sit in the parser library and read the parser's nodes directly;
** this prototype reads them from the library's parse document instead, so that it builds
** beside the library without changing it. The reader trusts the document, which the library
** writes in one fixed form.
*/
#include <stdlib.h>
#include <string.h>
#include "sqlite-verifier-parser.h"
#include "syntax.h"
#include "translate_b.h"

Vec statements(T *t, int root);

/* Move the cursor past the literal text; 0 when the document has other text there. */
static int expect(const char **cursor, const char *literal){
  size_t size = strlen(literal);
  if(strncmp(*cursor, literal, size)) return 0;
  *cursor += size;
  return 1;
}

/* Read a decimal number at the cursor. */
static int number(const char **cursor){
  char *end;
  long value = strtol(*cursor, &end, 10);
  *cursor = end;
  return (int)value;
}

/* Read the nodes of a PARSED document after its grammar; the root index goes to *root. */
static int read_nodes(T *t, const char *cursor, int *root){
  cursor = strstr(cursor, "\"root\":");
  if(!cursor) return 0;
  cursor += 7;
  *root = number(&cursor);
  if(!expect(&cursor, ",\"nodes\":[")) return 0;
  int capacity = 256;
  t->nodes = malloc(sizeof(PNode) * (size_t)capacity);
  while(t->nodes && *cursor == '{'){
    if(t->count == capacity){ capacity *= 2; PNode *nodes = realloc(t->nodes, sizeof(PNode) * (size_t)capacity); if(!nodes) return 0; t->nodes = nodes; }
    PNode *node = &t->nodes[t->count++];
    memset(node, 0, sizeof *node);
    if(!expect(&cursor, "{\"symbol\":\"")) return 0;
    const char *end = strchr(cursor, '"');
    char *symbol = arena(t, (size_t)(end - cursor) + 1);
    memcpy(symbol, cursor, (size_t)(end - cursor));
    node->symbol = symbol; cursor = end;
    if(!expect(&cursor, "\",\"start\":")) return 0;
    node->start = number(&cursor);
    if(!expect(&cursor, ",\"end\":")) return 0;
    node->end = number(&cursor);
    if(!expect(&cursor, ",\"children\":[")) return 0;
    int children = *cursor == ']' ? 0 : 1;
    for(const char *scan = cursor; *scan != ']'; scan++) children += *scan == ',';
    node->children = arena(t, sizeof(int) * (size_t)(children + 1));
    while(*cursor != ']'){ node->children[node->count++] = number(&cursor); expect(&cursor, ","); }
    if(!expect(&cursor, "]}")) return 0;
    expect(&cursor, ",");
  }
  return t->nodes != NULL;
}

/* Write the refusal of the translation. */
static void write_refusal(Buffer *out, const T *t){
  put_text(out, "{\"refusal\":{\"status\":"); put_json_string(out, t->status, strlen(t->status));
  put_text(out, ",\"message\":"); put_json_string(out, t->message, strlen(t->message));
  put_text(out, ",\"source\":\"measured.sql\",\"start\":"); put_number(out, t->start);
  put_text(out, ",\"end\":"); put_number(out, t->end);
  put_text(out, "}}");
}

/* Translate with a heap state: longjmp leaves the locals that it modified undefined, and the
** state is modified between setjmp and longjmp. */
int belay_translate(const char *grammar, const unsigned char *sql, size_t length, char **document, size_t *document_length){
  char *parsed; size_t parsed_length;
  int status = sqlite_verifier_parser_parse(grammar, sql, length, &parsed, &parsed_length);
  if(status != SQLITE_VERIFIER_PARSER_OK) return status;
  T *t = calloc(1, sizeof(T));
  if(!t){ sqlite_verifier_parser_free(parsed); return SQLITE_VERIFIER_PARSER_NO_MEMORY; }
  t->sql = sql;
  t->refusal = "A subquery is modeled only in SELECT, INSERT VALUES, UPDATE and DELETE; rewrite the statement without it";
  Buffer out = {0};
  const char *cursor = parsed;
  int root = 0;
  if(setjmp(t->fail)) write_refusal(&out, t);
  else if(expect(&cursor, "{\"status\":\"INPUT_ERROR\",\"offset\":")){
    t->status = "INPUT_ERROR"; t->start = number(&cursor);
    t->message = "SQLite's grammar rejects the SQL at this offset; correct the SQL there and run the command again";
    write_refusal(&out, t);
  } else if(expect(&cursor, "{\"status\":\"RESOURCE_LIMIT\",\"offset\":")){
    t->status = "UNVERIFIED"; t->start = number(&cursor);
    t->message = "SQL exceeds the parser's limits of 1 MiB of input and 200,000 syntax-tree nodes; split the SQL into smaller files";
    write_refusal(&out, t);
  } else if(!read_nodes(t, cursor, &root)){
    t->status = "UNVERIFIED"; t->message = "Parser output is unusable"; write_refusal(&out, t);
  } else {
    Vec items = statements(t, root);
    put_text(&out, "{\"statements\":[");
    for(int i = 0; i < items.count; i++){ if(i) put(&out, ",", 1); emit_located(&out, items.items[i]); }
    put_text(&out, "]}");
  }
  sqlite_verifier_parser_free(parsed);
  free(t->nodes);
  while(t->arena){ Block *next = t->arena->next; free(t->arena); t->arena = next; }
  free(t);
  if(out.failed || !out.data){ free(out.data); return SQLITE_VERIFIER_PARSER_NO_MEMORY; }
  *document = out.data;
  *document_length = out.length;
  return SQLITE_VERIFIER_PARSER_OK;
}

void belay_translate_free(char *document){ free(document); }
