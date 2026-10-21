/* The commands of a script and their statements: the port of commands, statement and
** statements of belay/sqlite/syntax.py. */
#include <string.h>
#include "syntax.h"

/* Whether the node's first parts are the space-separated symbols. */
static int starts(T *t, PNode *node, const char *symbols){
  char copy[128];
  strncpy(copy, symbols, sizeof copy - 1);
  copy[sizeof copy - 1] = 0;
  int index = 0;
  for(char *word = strtok(copy, " "); word; word = strtok(NULL, " "), index++)
    if(index >= node->count || strcmp(part(t, node, index)->symbol, word)) return 0;
  return 1;
}

/* One command as a statement, or the refusal of a statement that has no syntax constructor. */
static Located *statement(T *t, PNode *command){
  if(is(t, command, "create_table create_table_args")) return create_table(t, command);
  if(starts(t, command, "createkw uniqueflag INDEX")) return create_index(t, command);
  if(starts(t, command, "ALTER TABLE")) return add_column(t, command);
  if(is(t, command, "createkw trigger_decl BEGIN trigger_cmd_list END")) return create_trigger(t, command);
  if(starts(t, command, "DROP TABLE") || starts(t, command, "DROP INDEX") || starts(t, command, "DROP TRIGGER")) return drop(t, command);
  if(starts(t, command, "BEGIN") || starts(t, command, "COMMIT") || starts(t, command, "END") || starts(t, command, "ROLLBACK"))
    return transaction(t, command);
  if(starts(t, command, "with insert_cmd")) return insert(t, command);
  if(starts(t, command, "with UPDATE")) return update(t, command);
  if(starts(t, command, "with DELETE")) return delete(t, command);
  if(is(t, command, "select")){
    SubqueryList list = {{0}, -1};
    t->active = &list;
    Fields clauses = query_clauses(t, part(t, command, 0));
    t->active = NULL;
    return with_subqueries(t, "select", head(clauses, 8), list.items, command->start, command->end, tail(clauses, 8));
  }
  if(starts(t, command, "PRAGMA")) return pragma(t, command);
  refuse(t, command, "This statement is not modeled; the model runs CREATE TABLE, CREATE INDEX, CREATE TRIGGER, "
         "ALTER TABLE ADD COLUMN, DROP TABLE, DROP INDEX, DROP TRIGGER, BEGIN, COMMIT, ROLLBACK, INSERT, UPDATE, DELETE, "
         "SELECT and PRAGMA foreign_keys");
  return NULL;
}

/* Every command of the script from the root, in text order, as a statement; a wrapper such as
** EXPLAIN is refused before any statement is mapped. */
Vec statements(T *t, int root){
  PNode **pending = arena(t, sizeof(PNode *) * (size_t)(t->count + 1)), **commands = arena(t, sizeof(PNode *) * (size_t)(t->count + 1));
  int top = 0, count = 0;
  pending[top++] = &t->nodes[root];
  while(top){
    PNode *node = pending[--top];
    for(int i = node->count - 1; i >= 0; i--) pending[top++] = part(t, node, i);
    if(strcmp(node->symbol, "ecmd") || is(t, node, "SEMI")) continue;
    if(!is(t, node, "cmdx SEMI")) refuse(t, node, "Unsupported command wrapper, such as EXPLAIN; remove it");
    commands[count++] = part(t, part(t, node, 0), 0);
  }
  Vec result = {0};
  for(int i = 0; i < count; i++) push(t, &result, statement(t, commands[i]));
  return result;
}
