/* The subquery list of a statement: the port of belay/sqlite/syntax_subqueries.py. The scope
** (T.active, T.refusal) stands for the Python context variables. */
#include <string.h>
#include "syntax.h"

/* The first count fields. */
Fields head(Fields fields, int count){
  if(fields.count > count) fields.count = count;
  return fields;
}

/* The fields after the first count. */
Fields tail(Fields fields, int count){
  Fields result = {0};
  for(int i = count; i < fields.count; i++) field(&result, fields.names[i], fields.parts[i]);
  return result;
}

/* Add the subquery of a select production to the statement's list and give its index; its own
** subqueries come after it. Refuse it where no list is open. */
int lift(T *t, PNode *select){
  SubqueryList *listed = t->active;
  if(!listed) refuse(t, select, t->refusal);
  int index = listed->items.count, around = listed->current;
  push(t, &listed->items, NULL);
  listed->current = index;
  Fields clauses = query_clauses(t, select);
  listed->current = around;
  Fields fields = head(clauses, 8);
  field(&fields, "parent", around < 0 ? leaf_null(t, select->start, select->end) : leaf_int(t, around, select->start, select->end));
  listed->items.items[index] = object(t, NULL, join(fields, tail(clauses, 8)), select->start, select->end);
  return index;
}

/* Whether a part has the default value of its field, which a statement's JSON omits: no
** subqueries, no HAVING, not DISTINCT. */
static int default_value(const char *name, const Located *part){
  if(!strcmp(name, "subqueries")) return part->kind == LIST && part->count == 0;
  if(!strcmp(name, "having")) return part->kind == LEAF && !strcmp(part->json, "null");
  if(!strcmp(name, "distinct")) return part->kind == LEAF && !strcmp(part->json, "false");
  return 0;
}

/* The statement constructor with its fields, the subqueries field and the fields after it,
** in the order of the Lean constructor; its JSON omits each field that has its default. */
Located *with_subqueries(T *t, const char *kind, Fields fields, Vec items, int start, int end, Fields after){
  field(&fields, "subqueries", sequence(t, items, start, end));
  Located *result = object(t, kind, join(fields, after), start, end);
  for(int i = 0; i < result->count; i++) result->omit[i] = (unsigned char)default_value(result->fields[i], result->children[i]);
  return result;
}
