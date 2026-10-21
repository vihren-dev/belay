/* The SET lists, the ON CONFLICT clauses of INSERT and the algorithm of INSERT OR and
** REPLACE INTO: the port of belay/sqlite/syntax_conflicts.py. */
#include <string.h>
#include "syntax.h"

/* A setlist node as its column = expression pairs in text order. */
Located *assignment_list(T *t, PNode *assignments){
  static const Shape shapes[] = {{3, "nm EQ expr"}, {5, "setlist COMMA nm EQ expr"}};
  Items items = left_list(t, assignments, shapes, 2);
  Vec pairs = {0};
  for(int i = 0; i < items.count; i++){
    PNode *column = from_end(items.items[i], 3), *value = from_end(items.items[i], 1);
    Located *named = name(t, column);
    push(t, &pairs, pair(t, named, query_expression(t, value), column->start, value->end));
  }
  return sequence(t, pairs, assignments->start, assignments->end);
}

/* The target (sortlist) where_opt of a clause as its column names. */
static Located *conflict_target(T *t, PNode *columns, PNode *condition){
  static const Shape shapes[] = {{3, "expr sortorder nulls"}, {5, "sortlist COMMA expr sortorder nulls"}};
  absent(t, condition, "A WHERE clause of an ON CONFLICT target");
  Items items = left_list(t, columns, shapes, 2);
  Vec names = {0};
  for(int i = 0; i < items.count; i++){
    PNode *expression = from_end(items.items[i], 3);
    absent(t, from_end(items.items[i], 2), "A direction in an ON CONFLICT target");
    absent(t, from_end(items.items[i], 1), "NULLS FIRST or NULLS LAST in an ON CONFLICT target");
    Located *located = query_expression(t, expression);
    if(located->kind != CONSTRUCTOR || strcmp(located->name, "identifier"))
      refuse(t, expression, "Only column names are modeled in an ON CONFLICT target; write the column names");
    push(t, &names, located->children[0]);
  }
  return sequence(t, names, columns->start, columns->end);
}

/* DO UPDATE SET setlist where_opt as the update action. */
static Located *update_action(T *t, PNode *assignments, PNode *condition, int start, int end){
  Located *filter = condition->count ? query_expression(t, part(t, condition, 1)) : leaf_null(t, condition->start, condition->end);
  Fields fields = {0};
  field(&fields, "assignments", assignment_list(t, assignments));
  field(&fields, "filter", filter);
  return object(t, "update", fields, start, end);
}

/* The ON CONFLICT clauses of an upsert node in written order; *returning is the node whose
** parts are RETURNING selcollist, or NULL without RETURNING. */
Located *conflict_clauses(T *t, PNode *upsert, PNode **returning){
  Vec clauses = {0};
  PNode *current = upsert;
  for(;;){
    if(!current->count || is(t, current, "RETURNING selcollist")){
      *returning = current->count ? current : NULL;
      return sequence(t, clauses, upsert->start, upsert->end);
    }
    Located *target, *action;
    if(is(t, current, "ON CONFLICT LP sortlist RP where_opt DO NOTHING upsert")){
      target = conflict_target(t, part(t, current, 3), part(t, current, 5));
      action = leaf(t, "\"nothing\"", part(t, current, 6)->start, part(t, current, 7)->end);
    } else if(is(t, current, "ON CONFLICT LP sortlist RP where_opt DO UPDATE SET setlist where_opt upsert")){
      target = conflict_target(t, part(t, current, 3), part(t, current, 5));
      action = update_action(t, part(t, current, 9), part(t, current, 10), part(t, current, 6)->start, part(t, current, 10)->end);
    } else if(is(t, current, "ON CONFLICT DO NOTHING returning")){
      target = leaf_null(t, part(t, current, 1)->end, part(t, current, 1)->end);
      action = leaf(t, "\"nothing\"", part(t, current, 2)->start, part(t, current, 3)->end);
    } else {
      require(t, current, "ON CONFLICT DO UPDATE SET setlist where_opt returning");
      target = leaf_null(t, part(t, current, 1)->end, part(t, current, 1)->end);
      action = update_action(t, part(t, current, 5), part(t, current, 6), part(t, current, 2)->start, part(t, current, 6)->end);
    }
    Fields fields = {0};
    field(&fields, "target", target);
    field(&fields, "action", action);
    push(t, &clauses, object(t, NULL, fields, part(t, current, 0)->start, part(t, current, current->count - 2)->end));
    current = part(t, current, current->count - 1);
  }
}

/* The algorithm of an insert_cmd node: replace, the algorithm of INSERT OR, or none. */
Located *insert_algorithm(T *t, PNode *operation){
  if(is(t, operation, "REPLACE")) return leaf(t, "\"replace\"", operation->start, operation->end);
  PNode *conflict = part(t, require(t, operation, "INSERT orconf"), 1);
  if(!conflict->count) return leaf_null(t, conflict->start, conflict->end);
  return resolve_type(t, part(t, require(t, conflict, "OR resolvetype"), 1));
}
