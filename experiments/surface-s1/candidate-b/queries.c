/* The expressions and result columns of a query: the port of belay/sqlite/syntax_queries.py. */
#include <string.h>
#include "syntax.h"

/* The Lean constructor of a token in a table of token and constructor pairs, or NULL. */
static const char *lookup(const char *const table[][2], const char *symbol){
  for(int i = 0; table[i][0]; i++) if(!strcmp(table[i][0], symbol)) return table[i][1];
  return NULL;
}

static const char *const COMPARISONS[][2] = {{"EQ", "\"eq\""}, {"NE", "\"ne\""}, {"LT", "\"lt\""}, {"LE", "\"le\""},
  {"GT", "\"gt\""}, {"GE", "\"ge\""}, {NULL, NULL}};
static const char *const CONNECTIVES[][2] = {{"AND", "and"}, {"OR", "or"}, {NULL, NULL}};
static const char *const ARITHMETIC[][2] = {{"PLUS", "\"add\""}, {"MINUS", "\"subtract\""}, {"STAR", "\"multiply\""},
  {"SLASH", "\"divide\""}, {"REM", "\"remainder\""}, {NULL, NULL}};

/* A constructor with an operator and two operands: a comparison or an arithmetic operator. */
static Located *operation(T *t, PNode *node, const char *kind, const char *operator, PNode *left, PNode *right){
  Fields fields = {0};
  field(&fields, "operator", leaf(t, operator, node->start, node->end));
  field(&fields, "left", query_expression(t, left));
  field(&fields, "right", query_expression(t, right));
  return object(t, kind, fields, node->start, node->end);
}

/* A call of the function with its arguments in written order. */
static Located *call(T *t, int start, int end, Located *function, Item arguments){
  Vec items = {0};
  for(int i = 0; i < arguments.count; i++) push(t, &items, query_expression(t, arguments.parts[i]));
  Fields fields = {0};
  field(&fields, "name", function);
  field(&fields, "arguments", sequence(t, items, items.count ? items.items[0]->start : end,
                                       items.count ? items.items[items.count - 1]->end : end));
  return object(t, "call", fields, start, end);
}

/* The given parts as an argument list. */
static Item arguments(T *t, int count, PNode *first, PNode *second, PNode *third){
  Item item = {arena(t, sizeof(PNode *) * 3), count};
  item.parts[0] = first; item.parts[1] = second; item.parts[2] = third;
  return item;
}

/* A call with *, or with zero or more arguments, with the function name as written. */
static Located *function_call(T *t, PNode *node){
  PNode *head = part(t, node, 0);
  Located *function = !strcmp(head->symbol, "ID") ? name(t, head) : leaf_text(t, text(t, head), head->start, head->end);
  int star = node->count == 4 && !strcmp(part(t, node, 1)->symbol, "LP") && !strcmp(part(t, node, 2)->symbol, "STAR")
    && !strcmp(part(t, node, 3)->symbol, "RP");
  if(star) return one(t, "callStar", "name", function, node->start, node->end);
  int listed = node->count == 5 && !strcmp(part(t, node, 1)->symbol, "LP") && !strcmp(part(t, node, 2)->symbol, "distinct")
    && !strcmp(part(t, node, 3)->symbol, "exprlist") && !strcmp(part(t, node, 4)->symbol, "RP");
  if(!listed) refuse(t, node, "A function call with ORDER BY, FILTER or OVER is not modeled; write the call with its arguments only");
  absent(t, part(t, node, 2), "DISTINCT in a function call");
  return call(t, node->start, node->end, function, expression_list(t, part(t, node, 3)));
}

/* x LIKE p [ESCAPE e] and the other likeop operators: a call of the function named by the
** operator, with the pattern first, the operand second and the escape last. */
static Located *like(T *t, PNode *node){
  PNode *operator = part(t, node, 1), *keyword = part(t, operator, operator->count - 1);
  Located *function = leaf_text(t, text(t, keyword), keyword->start, keyword->end);
  Located *called = call(t, node->start, node->end, function, arguments(t, node->count == 5 ? 3 : 2, part(t, node, 2),
                         part(t, node, 0), node->count == 5 ? part(t, node, 4) : NULL));
  if(is(t, operator, "NOT LIKE_KW")) return one(t, "not", "operand", called, node->start, node->end);
  return called;
}

/* RAISE(IGNORE) and RAISE(kind, message). */
static Located *raise_form(T *t, PNode *node){
  Fields fields = {0};
  if(is(t, node, "RAISE LP IGNORE RP")){
    field(&fields, "kind", leaf(t, "\"ignore\"", part(t, node, 2)->start, part(t, node, 2)->end));
    field(&fields, "message", leaf_null(t, node->start, node->end));
  } else {
    PNode *kind = part(t, part(t, node, 2), 0);
    const char *value = !strcmp(kind->symbol, "ROLLBACK") ? "\"rollback\"" : !strcmp(kind->symbol, "ABORT") ? "\"abort\"" : "\"fail\"";
    field(&fields, "kind", leaf(t, value, kind->start, kind->end));
    field(&fields, "message", query_expression(t, part(t, node, 4)));
  }
  return object(t, "raise", fields, node->start, node->end);
}

/* A constructor of one query operand. */
static Located *unary(T *t, PNode *node, const char *kind, PNode *operand){
  return one(t, kind, "operand", query_expression(t, operand), node->start, node->end);
}

/* Map an expr production of a query, or refuse it with its range. */
Located *query_expression(T *t, PNode *node){
  if(is(t, node, "LP expr RP")) return query_expression(t, part(t, node, 1));
  Located *form = subquery_form(t, node);
  if(!form) form = list_form(t, node);
  if(form) return form;
  Fields fields = {0};
  if(node->count == 3 && !strcmp(part(t, node, 0)->symbol, "expr") && !strcmp(part(t, node, 2)->symbol, "expr")){
    const char *symbol = part(t, node, 1)->symbol, *found;
    if((found = lookup(COMPARISONS, symbol))) return operation(t, node, "compare", found, part(t, node, 0), part(t, node, 2));
    if(!strcmp(symbol, "IS")) return operation(t, node, "compare", "\"is\"", part(t, node, 0), part(t, node, 2));
    if((found = lookup(CONNECTIVES, symbol))){
      field(&fields, "left", query_expression(t, part(t, node, 0)));
      field(&fields, "right", query_expression(t, part(t, node, 2)));
      return object(t, found, fields, node->start, node->end);
    }
    if((found = lookup(ARITHMETIC, symbol))) return operation(t, node, "arithmetic", found, part(t, node, 0), part(t, node, 2));
  }
  if(is(t, node, "expr PTR expr")){
    PNode *operator = part(t, node, 1);
    return call(t, node->start, node->end, leaf_text(t, text(t, operator), operator->start, operator->end),
                arguments(t, 2, part(t, node, 0), part(t, node, 2), NULL));
  }
  if(is(t, node, "expr COLLATE ID") || is(t, node, "expr COLLATE STRING")){
    field(&fields, "operand", query_expression(t, part(t, node, 0)));
    field(&fields, "name", name(t, part(t, node, 2)));
    return object(t, "collate", fields, node->start, node->end);
  }
  if(is(t, node, "expr IS NOT expr")) return operation(t, node, "compare", "\"isNot\"", part(t, node, 0), part(t, node, 3));
  if(is(t, node, "MINUS expr")) return unary(t, node, "negate", part(t, node, 1));
  if(is(t, node, "PLUS expr")) return unary(t, node, "positive", part(t, node, 1));
  if(is(t, node, "CAST LP expr AS typetoken RP")){
    PNode *type = part(t, node, 4);
    field(&fields, "operand", query_expression(t, part(t, node, 2)));
    field(&fields, "typeName", leaf_text(t, text(t, type), type->start, type->end));
    return object(t, "cast", fields, node->start, node->end);
  }
  if(is(t, node, "nm DOT nm")){
    field(&fields, "source", name(t, part(t, node, 0)));
    field(&fields, "column", name(t, part(t, node, 2)));
    return object(t, "qualified", fields, node->start, node->end);
  }
  if(is(t, node, "nm DOT nm DOT nm")) refuse(t, node, "A schema-qualified column is not modeled; write source.column");
  if(is(t, node, "NOT expr")) return unary(t, node, "not", part(t, node, 1));
  if(is(t, node, "expr ISNULL") || is(t, node, "expr NOTNULL") || is(t, node, "expr NOT NULL")){
    field(&fields, "operand", query_expression(t, part(t, node, 0)));
    field(&fields, "negated", leaf_bool(t, strcmp(part(t, node, 1)->symbol, "ISNULL") != 0, node->start, node->end));
    return object(t, "isNull", fields, node->start, node->end);
  }
  const char *head = node->count >= 2 && !strcmp(part(t, node, 1)->symbol, "LP") ? part(t, node, 0)->symbol : "";
  if(!strcmp(head, "ID") || !strcmp(head, "LIKE_KW") || !strcmp(head, "IF") || !strcmp(head, "REPLACE")) return function_call(t, node);
  if(is(t, node, "expr likeop expr") || is(t, node, "expr likeop expr ESCAPE expr")) return like(t, node);
  if(is(t, node, "RAISE LP IGNORE RP") || is(t, node, "RAISE LP raisetype COMMA expr RP")) return raise_form(t, node);
  return expression(t, node);
}
