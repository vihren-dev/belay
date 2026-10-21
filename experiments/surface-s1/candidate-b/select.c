/* The result columns and clauses of a SELECT: the port of belay/sqlite/syntax_select.py and of
** result_column and result_columns of syntax_queries.py. */
#include <string.h>
#include "syntax.h"

/* *, source.*, or an expression with its optional alias and its text. */
static Located *result_column(T *t, PNode *node){
  if(node->count == 3 && !strcmp(part(t, node, 1)->symbol, "scanpt") && !strcmp(part(t, node, 2)->symbol, "STAR")){
    PNode *star = part(t, node, 2);
    return leaf(t, "\"star\"", star->start, star->end);
  }
  if(node->count == 5 && !strcmp(part(t, node, 1)->symbol, "scanpt") && !strcmp(part(t, node, 2)->symbol, "nm")
     && !strcmp(part(t, node, 3)->symbol, "DOT") && !strcmp(part(t, node, 4)->symbol, "STAR"))
    return one(t, "sourceStar", "source", name(t, part(t, node, 2)), part(t, node, 2)->start, part(t, node, 4)->end);
  int expression = node->count == 5 && !strcmp(part(t, node, 1)->symbol, "scanpt") && !strcmp(part(t, node, 2)->symbol, "expr")
    && !strcmp(part(t, node, 3)->symbol, "scanpt") && !strcmp(part(t, node, 4)->symbol, "as");
  if(!expression) refuse(t, node, "Only `*` and expressions are modeled as result columns; write the column names");
  PNode *value = part(t, node, 2), *as = part(t, node, 4);
  Located *named = alias(t, as);
  Fields fields = {0};
  field(&fields, "value", query_expression(t, value));
  field(&fields, "alias", named);
  field(&fields, "text", leaf_text(t, text(t, value), value->start, value->end));
  return object(t, "expression", fields, value->start, value->end > as->end ? value->end : as->end);
}

/* The result columns of a selcollist node in text order; like the Python translation, it
** maps them from the last to the first. */
Located *result_columns(T *t, PNode *node){
  Vec reversed = {0};
  for(PNode *current = node;;){
    push(t, &reversed, result_column(t, current));
    PNode *before = part(t, current, 0);
    if(!before->count) break;
    current = part(t, require(t, before, "selcollist COMMA"), 0);
  }
  Vec items = {0};
  for(int i = reversed.count - 1; i >= 0; i--) push(t, &items, reversed.items[i]);
  return sequence(t, items, node->start, node->end);
}

/* The ORDER BY terms of a sortlist in text order, with their direction. */
Vec order_terms(T *t, PNode *node){
  static const Shape shapes[] = {{3, "expr sortorder nulls"}, {5, "sortlist COMMA expr sortorder nulls"}};
  Items items = left_list(t, node, shapes, 2);
  Vec terms = {0};
  for(int i = 0; i < items.count; i++){
    PNode *term = from_end(items.items[i], 3), *direction = from_end(items.items[i], 2);
    absent(t, from_end(items.items[i], 1), "NULLS FIRST or NULLS LAST");
    Fields fields = {0};
    field(&fields, "expression", query_expression(t, term));
    field(&fields, "descending", leaf_bool(t, is(t, direction, "DESC"), direction->start, direction->end));
    push(t, &terms, object(t, NULL, fields, term->start, term->end > direction->end ? term->end : direction->end));
  }
  return terms;
}

/* An optional part: the located value, or a null leaf at the clause. */
static Located *optional(T *t, Located *value, PNode *node){ return value ? value : leaf_null(t, node->start, node->end); }

/* The clauses of a select production, in the order of Syntax.Subquery and of their text. */
Fields query_clauses(T *t, PNode *select){
  static const Shape grouped[] = {{1, "expr"}, {3, "nexprlist COMMA expr"}};
  PNode *one_select = part(t, require(t, part(t, require(t, select, "selectnowith"), 0), "oneselect"), 0);
  require(t, one_select, "SELECT distinct selcollist from where_opt groupby_opt having_opt orderby_opt limit_opt");
  PNode *distinct = part(t, one_select, 1), *source = part(t, one_select, 3), *where = part(t, one_select, 4);
  PNode *group = part(t, one_select, 5), *having = part(t, one_select, 6), *order = part(t, one_select, 7);
  PNode *limit = part(t, one_select, 8);
  Located *columns = result_columns(t, part(t, one_select, 2)), *first, *joins;
  if(source->count) from_clause(t, part(t, require(t, source, "FROM seltablist"), 1), &first, &joins);
  else { Vec none = {0}; first = leaf_null(t, source->start, source->end); joins = sequence(t, none, source->start, source->end); }
  Located *condition = where->count ? query_expression(t, part(t, where, 1)) : NULL;
  Vec grouping = {0}, ordering = {0};
  if(group->count){
    Items items = left_list(t, part(t, group, 2), grouped, 2);
    for(int i = 0; i < items.count; i++) push(t, &grouping, query_expression(t, from_end(items.items[i], 1)));
  }
  if(order->count) ordering = order_terms(t, part(t, order, 2));
  Located *count = NULL, *offset = NULL;
  if(is(t, limit, "LIMIT expr")) count = query_expression(t, part(t, limit, 1));
  else if(is(t, limit, "LIMIT expr OFFSET expr") || is(t, limit, "LIMIT expr COMMA expr")){
    Located *before = query_expression(t, part(t, limit, 1)), *after = query_expression(t, part(t, limit, 3));
    int comma = !strcmp(part(t, limit, 2)->symbol, "COMMA");
    count = comma ? after : before; offset = comma ? before : after;
  } else if(limit->count) refuse(t, limit, "Unsupported LIMIT form; write LIMIT n [OFFSET m]");
  Located *filter = having->count ? query_expression(t, part(t, having, 1)) : NULL;
  Fields fields = {0};
  field(&fields, "columns", columns);
  field(&fields, "source", first);
  field(&fields, "joins", joins);
  field(&fields, "filter", optional(t, condition, where));
  field(&fields, "groupBy", sequence(t, grouping, group->start, group->end));
  field(&fields, "orderBy", sequence(t, ordering, order->start, order->end));
  field(&fields, "limit", optional(t, count, limit));
  field(&fields, "offset", optional(t, offset, limit));
  field(&fields, "having", optional(t, filter, having));
  field(&fields, "distinct", leaf_bool(t, is(t, distinct, "DISTINCT"), distinct->start, distinct->end));
  return fields;
}
