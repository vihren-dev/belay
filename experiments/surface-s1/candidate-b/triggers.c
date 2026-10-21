/* CREATE TRIGGER: the port of belay/sqlite/syntax_triggers.py. */
#include <string.h>
#include "syntax.h"

/* The body statement constructor with every field, the subqueries field included. */
static Located *body_statement(T *t, const char *kind, Fields fields, SubqueryList *list, PNode *node, Fields after){
  field(&fields, "subqueries", sequence(t, list->items, node->start, node->end));
  return object(t, kind, join(fields, after), node->start, node->end);
}

/* The table of a body statement, a trnm node; a qualified name is refused. */
static Located *body_table(T *t, PNode *node){
  if(!is(t, node, "nm")) refuse(t, node, "A qualified table name is not allowed in a trigger; write the table name");
  return name(t, part(t, node, 0));
}

/* The optional WHERE filter of a where_opt node, a null leaf without it. */
static Located *body_filter(T *t, PNode *where){
  return where->count ? query_expression(t, part(t, where, 1)) : leaf_null(t, where->start, where->end);
}

/* INSERT ... VALUES rows [ON CONFLICT ...] and REPLACE INTO in a trigger body. */
static Located *body_insert(T *t, PNode *node){
  require(t, node, "scanpt insert_cmd INTO trnm idlist_opt select upsert scanpt");
  SubqueryList *active = t->active, list = {{0}, -1};
  const char *refusal = t->refusal;
  t->active = NULL; t->refusal = "A subquery in ON CONFLICT is not modeled; read the value in a separate statement";
  PNode *returned;
  Located *conflicts = conflict_clauses(t, part(t, node, 6), &returned);
  t->active = active; t->refusal = refusal;
  if(returned) refuse(t, part(t, node, 6), "RETURNING is not allowed in a trigger; remove it");
  Located *columns = column_list(t, part(t, node, 4));
  t->active = &list;
  Located *rows = value_rows(t, part(t, node, 5));
  t->active = active;
  Fields fields = {0}, after = {0};
  field(&fields, "table", body_table(t, part(t, node, 3)));
  field(&fields, "columns", columns);
  field(&fields, "rows", rows);
  field(&fields, "conflicts", conflicts);
  field(&fields, "algorithm", insert_algorithm(t, part(t, node, 1)));
  return body_statement(t, "insert", fields, &list, node, after);
}

/* UPDATE table SET assignments [WHERE expression] in a trigger body. */
static Located *body_update(T *t, PNode *node){
  require(t, node, "UPDATE orconf trnm tridxby SET setlist from where_opt scanpt");
  absent(t, part(t, node, 1), "An OR conflict clause of UPDATE");
  absent(t, part(t, node, 3), "INDEXED BY");
  absent(t, part(t, node, 6), "UPDATE FROM");
  SubqueryList *active = t->active, list = {{0}, -1};
  t->active = &list;
  Located *assignments = assignment_list(t, part(t, node, 5));
  Located *filter = body_filter(t, part(t, node, 7));
  t->active = active;
  Fields fields = {0}, after = {0};
  field(&fields, "table", body_table(t, part(t, node, 2)));
  field(&fields, "assignments", assignments);
  field(&fields, "filter", filter);
  return body_statement(t, "update", fields, &list, node, after);
}

/* DELETE FROM table [WHERE expression] in a trigger body. */
static Located *body_delete(T *t, PNode *node){
  require(t, node, "DELETE FROM trnm tridxby where_opt scanpt");
  absent(t, part(t, node, 3), "INDEXED BY");
  SubqueryList *active = t->active, list = {{0}, -1};
  t->active = &list;
  Located *filter = body_filter(t, part(t, node, 4));
  t->active = active;
  Fields fields = {0}, after = {0};
  field(&fields, "table", body_table(t, part(t, node, 2)));
  field(&fields, "filter", filter);
  return body_statement(t, "delete", fields, &list, node, after);
}

/* A SELECT in a trigger body, with every clause. */
static Located *body_select(T *t, PNode *node){
  require(t, node, "scanpt select scanpt");
  SubqueryList *active = t->active, list = {{0}, -1};
  t->active = &list;
  Fields clauses = query_clauses(t, part(t, node, 1));
  t->active = active;
  return body_statement(t, "select", head(clauses, 8), &list, node, tail(clauses, 8));
}

/* The statements of a trigger_cmd_list node in text order. */
static Located *body(T *t, PNode *node){
  static const Shape shapes[] = {{2, "trigger_cmd SEMI"}, {3, "trigger_cmd_list trigger_cmd SEMI"}};
  Items items = left_list(t, node, shapes, 2);
  Vec statements = {0};
  for(int i = 0; i < items.count; i++){
    PNode *command = from_end(items.items[i], 2);
    const char *first = command->count ? part(t, command, 0)->symbol : "";
    if(!strcmp(first, "UPDATE")) push(t, &statements, body_update(t, command));
    else if(!strcmp(first, "DELETE")) push(t, &statements, body_delete(t, command));
    else if(command->count > 1 && !strcmp(part(t, command, 1)->symbol, "insert_cmd")) push(t, &statements, body_insert(t, command));
    else push(t, &statements, body_select(t, command));
  }
  return sequence(t, statements, node->start, node->end);
}

/* insert, delete, or update with the column names of UPDATE OF. */
static Located *trigger_event(T *t, PNode *node){
  static const Shape shapes[] = {{1, "nm"}, {3, "idlist COMMA nm"}};
  if(is(t, node, "INSERT")) return leaf(t, "\"insert\"", node->start, node->end);
  if(is(t, node, "DELETE")) return leaf(t, "\"delete\"", node->start, node->end);
  Vec columns = {0};
  if(is(t, node, "UPDATE OF idlist")){
    Items items = left_list(t, part(t, node, 2), shapes, 2);
    for(int i = 0; i < items.count; i++) push(t, &columns, name(t, from_end(items.items[i], 1)));
  }
  return one(t, "update", "columns", sequence(t, columns, node->start, node->end), node->start, node->end);
}

/* CREATE TRIGGER [IF NOT EXISTS] name [BEFORE|AFTER] event ON table [FOR EACH ROW] [WHEN
** condition] BEGIN statements END. */
Located *create_trigger(T *t, PNode *command){
  PNode *declaration = require(t, part(t, command, 1), "temp TRIGGER ifnotexists nm dbnm trigger_time trigger_event ON "
                                                       "fullname foreach_clause when_clause");
  absent(t, part(t, declaration, 0), "A TEMP trigger");
  absent(t, part(t, declaration, 4), "A schema name");
  PNode *table = part(t, declaration, 8), *when = part(t, declaration, 10), *time = part(t, declaration, 5);
  if(!is(t, table, "nm")) refuse(t, table, "A schema name is not modeled; remove it");
  SubqueryList *active = t->active;
  const char *refusal = t->refusal;
  t->active = NULL;
  t->refusal = "A subquery in the WHEN condition of a trigger is not modeled; move the test into the trigger's statements";
  Located *condition = when->count ? query_expression(t, part(t, when, 1)) : leaf_null(t, when->start, when->end);
  t->active = active; t->refusal = refusal;
  PNode *exists = part(t, declaration, 2);
  Fields fields = {0};
  field(&fields, "name", name(t, part(t, declaration, 3)));
  field(&fields, "ifNotExists", leaf_bool(t, exists->count > 0, exists->start, exists->end));
  if(is(t, time, "INSTEAD OF"))
    refuse(t, time, "INSTEAD OF triggers are not modeled, as the model has no views; write the statements on the tables instead");
  field(&fields, "time", leaf(t, is(t, time, "AFTER") ? "\"after\"" : "\"before\"", time->start, time->end));
  field(&fields, "event", trigger_event(t, part(t, declaration, 6)));
  field(&fields, "table", name(t, part(t, table, 0)));
  field(&fields, "condition", condition);
  field(&fields, "body", body(t, part(t, command, 3)));
  return object(t, "createTrigger", fields, command->start, command->end);
}
