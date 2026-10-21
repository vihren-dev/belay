/* Names, literals and the expressions outside queries: the port of
** belay/sqlite/syntax_expressions.py. */
#include <string.h>
#include <stdio.h>
#include "syntax.h"

/* sqlite3Dequote: remove a leading quote up to its closing quote and undouble it. */
char *dequote(T *t, const char *value){
  char close = value[0] == '"' ? '"' : value[0] == '\'' ? '\'' : value[0] == '`' ? '`' : value[0] == '[' ? ']' : 0;
  if(!close) return (char *)value;
  char *result = arena(t, strlen(value) + 1), *cursor = result;
  for(const char *c = value + 1; *c; c++){
    if(*c == close){
      if(c[1] != close) break;
      c++;
    }
    *cursor++ = *c;
  }
  return result;
}

/* The single token of a one-token production, or its refusal. */
PNode *token(T *t, PNode *node){
  if(node->count != 1 || part(t, node, 0)->count){
    static const char suffix[] = "; write a plain name or literal";
    size_t size = strlen(node->symbol) + sizeof suffix + 32;
    char *message = arena(t, size);
    snprintf(message, size, "Unsupported SQL form: %s%s", node->symbol, suffix);
    refuse(t, node, message);
  }
  return part(t, node, 0);
}

/* An nm production or a name token as written, with its quotes removed. */
Located *name(T *t, PNode *node){
  PNode *item = node->count ? token(t, node) : node;
  return leaf_text(t, dequote(t, text(t, item)), node->start, node->end);
}

/* The value of a hexadecimal digit, or -1. */
static int hex(char c){
  return c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1;
}

/* A constructor of one field. */
Located *one(T *t, const char *kind, const char *name, Located *value, int start, int end){
  Fields fields = {0};
  field(&fields, name, value);
  return object(t, kind, fields, start, end);
}

/* A term production: NULL, a numeric, string or blob literal, or a time keyword. */
Located *term(T *t, PNode *node){
  PNode *item = token(t, node);
  char *value = text(t, item);
  const char *symbol = item->symbol;
  if(!strcmp(symbol, "NULL")) return leaf(t, "\"null\"", node->start, node->end);
  if(!strcmp(symbol, "INTEGER") || !strcmp(symbol, "FLOAT") || !strcmp(symbol, "QNUMBER"))
    return one(t, "numeric", "text", leaf_text(t, value, item->start, item->end), node->start, node->end);
  if(!strcmp(symbol, "STRING")){
    char *bytes = dequote(t, value);
    return one(t, "string", "bytes", leaf_bytes(t, (unsigned char *)bytes, strlen(bytes), item->start, item->end),
               node->start, node->end);
  }
  if(!strcmp(symbol, "BLOB")){
    size_t digits = strlen(value) - 3;
    unsigned char *bytes = arena(t, digits / 2 + 1);
    for(size_t i = 0; i < digits; i += 2){
      int high = hex(value[2 + i]), low = i + 1 < digits ? hex(value[3 + i]) : -1;
      if(high < 0 || low < 0) refuse(t, node, "A blob literal needs pairs of hexadecimal digits; correct the literal");
      bytes[i / 2] = (unsigned char)(high * 16 + low);
    }
    return one(t, "blob", "bytes", leaf_bytes(t, bytes, digits / 2, item->start, item->end), node->start, node->end);
  }
  if(!strcmp(symbol, "CTIME_KW"))
    return one(t, "currentTime", "keyword", leaf_text(t, value, item->start, item->end), node->start, node->end);
  static const char prefix[] = "Unsupported literal: ", suffix[] = "; write NULL, a number, a string or a blob";
  size_t size = sizeof prefix + strlen(symbol) + sizeof suffix;
  char *message = arena(t, size);
  snprintf(message, size, "%s%s%s", prefix, symbol, suffix);
  refuse(t, node, message);
  return NULL;
}

/* An identifier token, with how it was quoted. */
Located *identifier(T *t, PNode *node){
  char *value = text(t, node);
  const char *quote = value[0] == '"' ? "\"double\"" : value[0] == '[' ? "\"bracket\"" : value[0] == '`' ? "\"backtick\"" : "\"none\"";
  Fields fields = {0};
  field(&fields, "name", leaf_text(t, dequote(t, value), node->start, node->end));
  field(&fields, "quote", leaf(t, quote, node->start, node->end));
  return object(t, "identifier", fields, node->start, node->end);
}

/* The tokens of SQLite's expr ::= ID|INDEXED|JOIN_KW production: those three and the keywords
** of %fallback ID in the pinned parse.y of 3.51.0. */
static const char IDENTIFIER_TOKENS[] = " ID INDEXED JOIN_KW ABORT ACTION AFTER ANALYZE ASC ATTACH BEFORE BEGIN BY "
  "CASCADE CAST COLUMNKW CONFLICT DATABASE DEFERRED DESC DETACH DO EACH END EXCLUSIVE EXPLAIN FAIL FOR IGNORE "
  "IMMEDIATE INITIALLY INSTEAD LIKE_KW MATCH NO PLAN QUERY KEY OF OFFSET PRAGMA RAISE RECURSIVE RELEASE REPLACE "
  "RESTRICT ROW ROWS ROLLBACK SAVEPOINT TEMP TRIGGER VACUUM VIEW VIRTUAL WITH WITHOUT NULLS FIRST LAST CURRENT "
  "FOLLOWING PARTITION PRECEDING RANGE UNBOUNDED EXCLUDE GROUPS OTHERS TIES GENERATED ALWAYS MATERIALIZED REINDEX "
  "RENAME IF ";

/* Whether a symbol is one of IDENTIFIER_TOKENS. */
int identifier_token(const char *symbol){
  char needle[64];
  if(strlen(symbol) > 60) return 0;
  snprintf(needle, sizeof needle, " %s ", symbol);
  return strstr(IDENTIFIER_TOKENS, needle) != NULL;
}

/* An expr production outside a query: a literal, a column name or a sign, or its refusal. */
Located *expression(T *t, PNode *node){
  if(is(t, node, "term")) return term(t, part(t, node, 0));
  if(node->count == 1 && identifier_token(part(t, node, 0)->symbol)) return identifier(t, part(t, node, 0));
  if(is(t, node, "MINUS expr") || is(t, node, "PLUS expr")){
    const char *kind = !strcmp(part(t, node, 0)->symbol, "MINUS") ? "negate" : "positive";
    return one(t, kind, "operand", expression(t, part(t, node, 1)), node->start, node->end);
  }
  refuse(t, node, "Unsupported expression; write a literal, a column name or a sign");
  return NULL;
}
