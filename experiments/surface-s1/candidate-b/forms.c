/* The expression forms of a query that hold subqueries or lists: the port of
** belay/sqlite/syntax_forms.py. Each mapping keeps the Python translation's order of
** evaluation, so subqueries get the same indexes and refusals the same node. */
#include <string.h>
#include "syntax.h"

/* Whether an in_op or between_op node has NOT before its keyword. */
static int negated(T *t, PNode *operator, const char *keyword){
  return operator->count == 2 && !strcmp(part(t, operator, 0)->symbol, "NOT") && !strcmp(part(t, operator, 1)->symbol, keyword);
}

/* A constructor with an index of the statement's subquery list. */
static Located *indexed(T *t, const char *kind, int index, PNode *node){
  return one(t, kind, "index", leaf_int(t, index, node->start, node->end), node->start, node->end);
}

/* EXISTS (q), x [NOT] IN (q) and the scalar subquery (q); NULL for another form. */
Located *subquery_form(T *t, PNode *node){
  if(is(t, node, "LP select RP")) return indexed(t, "subquery", lift(t, part(t, node, 1)), node);
  if(is(t, node, "EXISTS LP select RP")) return indexed(t, "exists", lift(t, part(t, node, 2)), node);
  if(!is(t, node, "expr in_op LP select RP")) return NULL;
  Located *operand = query_expression(t, part(t, node, 0));
  PNode *operator = part(t, node, 1);
  int index = lift(t, part(t, node, 3));
  Fields fields = {0};
  field(&fields, "operand", operand);
  field(&fields, "index", leaf_int(t, index, node->start, node->end));
  field(&fields, "negated", leaf_bool(t, negated(t, operator, "IN"), operator->start, operator->end));
  return object(t, "inQuery", fields, node->start, node->end);
}

/* The expressions of an exprlist node, in text order. */
Item expression_list(T *t, PNode *node){
  static const Shape outer[] = {{1, "nexprlist"}}, inner[] = {{1, "expr"}, {3, "nexprlist COMMA expr"}};
  Items listed = left_list(t, node, outer, 1);
  Item values = {0};
  if(!listed.count) return values;
  Items items = left_list(t, listed.items[0].parts[0], inner, 2);
  values.parts = arena(t, sizeof(PNode *) * (size_t)(items.count + 1));
  for(int i = 0; i < items.count; i++) values.parts[values.count++] = from_end(items.items[i], 1);
  return values;
}

/* x [NOT] IN (values); a list of one parenthesized subquery is x IN (SELECT ...). */
static Located *in_list(T *t, PNode *node){
  PNode *operator = part(t, node, 1), *list = part(t, node, 3);
  Located *negation = leaf_bool(t, negated(t, operator, "IN"), operator->start, operator->end);
  Item values = expression_list(t, list);
  Fields fields = {0};
  if(values.count == 1 && is(t, values.parts[0], "LP select RP")){
    int index = lift(t, part(t, values.parts[0], 1));
    field(&fields, "operand", query_expression(t, part(t, node, 0)));
    field(&fields, "index", leaf_int(t, index, node->start, node->end));
    field(&fields, "negated", negation);
    return object(t, "inQuery", fields, node->start, node->end);
  }
  Vec mapped = {0};
  for(int i = 0; i < values.count; i++) push(t, &mapped, query_expression(t, values.parts[i]));
  field(&fields, "operand", query_expression(t, part(t, node, 0)));
  field(&fields, "values", sequence(t, mapped, list->start, list->end));
  field(&fields, "negated", negation);
  return object(t, "inList", fields, node->start, node->end);
}

/* CASE [base] WHEN ... THEN ... [ELSE ...] END, with its operands in text order. */
static Located *case_of(T *t, PNode *node){
  static const Shape arms[] = {{4, "WHEN expr THEN expr"}, {5, "case_exprlist WHEN expr THEN expr"}};
  PNode *base = part(t, node, 1), *otherwise = part(t, node, 3);
  Items items = left_list(t, part(t, node, 2), arms, 2);
  Vec operands = {0};
  if(base->count) push(t, &operands, query_expression(t, part(t, base, 0)));
  for(int i = 0; i < items.count; i++){
    push(t, &operands, query_expression(t, from_end(items.items[i], 3)));
    push(t, &operands, query_expression(t, from_end(items.items[i], 1)));
  }
  if(otherwise->count) push(t, &operands, query_expression(t, part(t, otherwise, 1)));
  Fields fields = {0};
  field(&fields, "operands", sequence(t, operands, base->start, otherwise->end));
  field(&fields, "hasBase", leaf_bool(t, base->count > 0, base->start, base->end));
  return object(t, "caseOf", fields, node->start, node->end);
}

/* x [NOT] IN (values), x [NOT] BETWEEN a AND b, CASE ... END and x || y; NULL for another form. */
Located *list_form(T *t, PNode *node){
  Fields fields = {0};
  if(is(t, node, "expr in_op LP exprlist RP")) return in_list(t, node);
  if(is(t, node, "CASE case_operand case_exprlist case_else END")) return case_of(t, node);
  if(is(t, node, "expr between_op expr AND expr")){
    PNode *operator = part(t, node, 1);
    field(&fields, "operand", query_expression(t, part(t, node, 0)));
    field(&fields, "low", query_expression(t, part(t, node, 2)));
    field(&fields, "high", query_expression(t, part(t, node, 4)));
    field(&fields, "negated", leaf_bool(t, negated(t, operator, "BETWEEN"), operator->start, operator->end));
    return object(t, "between", fields, node->start, node->end);
  }
  if(is(t, node, "expr CONCAT expr")){
    field(&fields, "left", query_expression(t, part(t, node, 0)));
    field(&fields, "right", query_expression(t, part(t, node, 2)));
    return object(t, "concatenate", fields, node->start, node->end);
  }
  return NULL;
}
