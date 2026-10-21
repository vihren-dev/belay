/* Transaction control, INSERT, UPDATE and DELETE: the port of belay/sqlite/syntax_writes.py. */
#include <stdio.h>
#include <string.h>
#include "syntax.h"

/* The refusal of a subquery in RETURNING or ON CONFLICT. */
static const char IN_CLAUSE[] = "A subquery in RETURNING or ON CONFLICT is not modeled; read the value in a separate statement";

/* BEGIN [DEFERRED] [TRANSACTION], COMMIT or END [TRANSACTION], and ROLLBACK [TRANSACTION]. */
Located *transaction(T *t, PNode *command){
  const char *keyword = part(t, command, 0)->symbol;
  PNode *option;
  if(!strcmp(keyword, "BEGIN")){
    require(t, command, "BEGIN transtype trans_opt");
    PNode *mode = part(t, command, 1);
    if(!is(t, mode, "") && !is(t, mode, "DEFERRED")) refuse(t, mode, "Only deferred transactions are modeled; write BEGIN or BEGIN DEFERRED");
    option = part(t, command, 2);
  } else {
    char symbols[64];
    snprintf(symbols, sizeof symbols, "%s trans_opt", keyword);
    option = part(t, require(t, command, symbols), 1);
  }
  if(!is(t, option, "") && !is(t, option, "TRANSACTION")) refuse(t, option, "Named transactions are not modeled; remove the transaction name");
  const char *kind = !strcmp(keyword, "BEGIN") ? "\"begin\"" : !strcmp(keyword, "ROLLBACK") ? "\"rollback\"" : "\"commit\"";
  return leaf(t, kind, command->start, command->end);
}

/* The VALUES rows of an INSERT source in text order; a SELECT source is refused. */
Located *value_rows(T *t, PNode *node){
  static const Shape shapes[] = {{1, "expr"}, {3, "nexprlist COMMA expr"}};
  PNode *one_select = part(t, require(t, part(t, require(t, node, "selectnowith"), 0), "oneselect"), 0);
  if(!is(t, one_select, "values") && !is(t, one_select, "mvalues"))
    refuse(t, one_select, "Only VALUES rows are modeled as an INSERT source; write INSERT ... VALUES (...)");
  PNode *current = part(t, one_select, 0);
  int count = 1;
  for(PNode *walk = current; !strcmp(walk->symbol, "mvalues") && walk->count; walk = part(t, walk, 0)) count++;
  PNode **listed = arena(t, sizeof(PNode *) * (size_t)count);
  int total = 0;
  while(!strcmp(current->symbol, "mvalues")){
    char symbols[64];
    snprintf(symbols, sizeof symbols, "%s COMMA LP nexprlist RP", current->count ? part(t, current, 0)->symbol : "");
    listed[total++] = part(t, require(t, current, symbols), 3);
    current = part(t, current, 0);
  }
  listed[total++] = part(t, require(t, current, "VALUES LP nexprlist RP"), 2);
  Vec rows = {0};
  for(int i = total - 1; i >= 0; i--){
    Items items = left_list(t, listed[i], shapes, 2);
    Vec values = {0};
    for(int j = 0; j < items.count; j++) push(t, &values, query_expression(t, from_end(items.items[j], 1)));
    push(t, &rows, sequence(t, values, listed[i]->start, listed[i]->end));
  }
  return sequence(t, rows, node->start, node->end);
}

/* The returning field of a write: the result columns of RETURNING, a selcollist node, or an
** empty list for NULL. */
static Located *returning(T *t, PNode *command, PNode *columns){
  Vec none = {0};
  if(!columns) return sequence(t, none, command->end, command->end);
  SubqueryList *active = t->active;
  const char *refusal = t->refusal;
  t->active = NULL; t->refusal = IN_CLAUSE;
  Located *result = result_columns(t, columns);
  t->active = active; t->refusal = refusal;
  return result;
}

/* The column list of an idlist_opt node, or none. */
Located *column_list(T *t, PNode *columns){
  static const Shape shapes[] = {{1, "nm"}, {3, "idlist COMMA nm"}};
  if(!columns->count) return leaf_null(t, columns->start, columns->end);
  Items items = left_list(t, part(t, require(t, columns, "LP idlist RP"), 1), shapes, 2);
  Vec names = {0};
  for(int i = 0; i < items.count; i++) push(t, &names, name(t, from_end(items.items[i], 1)));
  return sequence(t, names, columns->start, columns->end);
}

/* INSERT [OR algorithm] INTO table [(columns)] VALUES rows [ON CONFLICT ...] [RETURNING
** columns], and REPLACE INTO. */
Located *insert(T *t, PNode *command){
  require(t, command, "with insert_cmd INTO xfullname idlist_opt select upsert");
  absent(t, part(t, command, 0), "A WITH clause");
  Located *algorithm = insert_algorithm(t, part(t, command, 1));
  SubqueryList *active = t->active, list = {{0}, -1};
  const char *refusal = t->refusal;
  t->active = NULL; t->refusal = IN_CLAUSE;
  PNode *returned;
  Located *conflicts = conflict_clauses(t, part(t, command, 6), &returned);
  t->active = active; t->refusal = refusal;
  PNode *table = part(t, require(t, part(t, command, 3), "nm"), 0);
  Located *columns = column_list(t, part(t, command, 4));
  t->active = &list;
  Located *rows = value_rows(t, part(t, command, 5));
  t->active = active;
  Fields fields = {0}, after = {0};
  field(&fields, "table", name(t, table));
  field(&fields, "columns", columns);
  field(&fields, "rows", rows);
  field(&fields, "conflicts", conflicts);
  field(&fields, "algorithm", algorithm);
  field(&fields, "returning", returning(t, command, returned ? part(t, returned, 1) : NULL));
  return with_subqueries(t, "insert", fields, list.items, command->start, command->end, after);
}

/* The optional WHERE filter of a where_opt_ret node, which UPDATE and DELETE share;
** *returned is its RETURNING columns, or NULL. */
static Located *filter_and_returning(T *t, PNode *where, const char *message, PNode **returned){
  int filtered = is(t, where, "WHERE expr") || is(t, where, "WHERE expr RETURNING selcollist");
  if(!filtered && !is(t, where, "") && !is(t, where, "RETURNING selcollist")) refuse(t, where, message);
  Located *filter = filtered ? query_expression(t, part(t, where, 1)) : leaf_null(t, where->start, where->end);
  *returned = where->count >= 2 && !strcmp(part(t, where, where->count - 2)->symbol, "RETURNING")
    ? part(t, where, where->count - 1) : NULL;
  return filter;
}

/* UPDATE table SET assignments [WHERE expression] [RETURNING columns]. */
Located *update(T *t, PNode *command){
  require(t, command, "with UPDATE orconf xfullname indexed_opt SET setlist from where_opt_ret");
  absent(t, part(t, command, 0), "A WITH clause");
  absent(t, part(t, command, 2), "An OR conflict clause");
  absent(t, part(t, command, 4), "INDEXED BY");
  absent(t, part(t, command, 7), "UPDATE FROM");
  PNode *table = part(t, require(t, part(t, command, 3), "nm"), 0), *returned;
  SubqueryList *active = t->active, list = {{0}, -1};
  t->active = &list;
  Located *assignments = assignment_list(t, part(t, command, 6));
  Located *filter = filter_and_returning(t, part(t, command, 8),
    "Unsupported UPDATE clause; write [WHERE expression] [RETURNING columns]", &returned);
  t->active = active;
  Fields fields = {0}, after = {0};
  field(&fields, "table", name(t, table));
  field(&fields, "assignments", assignments);
  field(&fields, "filter", filter);
  field(&fields, "returning", returning(t, command, returned));
  return with_subqueries(t, "update", fields, list.items, command->start, command->end, after);
}

/* DELETE FROM table [WHERE expression] [RETURNING columns]. */
Located *delete(T *t, PNode *command){
  require(t, command, "with DELETE FROM xfullname indexed_opt where_opt_ret");
  absent(t, part(t, command, 0), "A WITH clause");
  absent(t, part(t, command, 4), "INDEXED BY");
  PNode *table = part(t, require(t, part(t, command, 3), "nm"), 0), *returned;
  SubqueryList *active = t->active, list = {{0}, -1};
  t->active = &list;
  Located *filter = filter_and_returning(t, part(t, command, 5),
    "Unsupported DELETE clause; write [WHERE expression] [RETURNING columns]", &returned);
  t->active = active;
  Fields fields = {0}, after = {0};
  field(&fields, "table", name(t, table));
  field(&fields, "filter", filter);
  field(&fields, "returning", returning(t, command, returned));
  return with_subqueries(t, "delete", fields, list.items, command->start, command->end, after);
}
