/* The FROM clause of a SELECT and the aliases: the port of belay/sqlite/syntax_sources.py. */
#include <string.h>
#include "syntax.h"

/* The alias of an as node: AS name, a bare name, or none. */
Located *alias(T *t, PNode *node){
  if(is(t, node, "AS nm")) return name(t, part(t, node, 1));
  if(node->count) return leaf_text(t, dequote(t, text(t, part(t, node, 0))), node->start, node->end);
  return leaf_null(t, node->start, node->end);
}

/* One source of a seltablist: its joined prefix, name, schema, alias and constraint nodes,
** and the mapped arguments of a table-valued function, or NULL for a table. */
typedef struct { PNode *node, *joined, *table, *schema, *alias, *constraint; Located *arguments; } Source;

/* The parts of one source; a subquery or INDEXED BY is refused. Like the Python translation,
** the function arguments are mapped while the list is walked from its end. */
static Source source_parts(T *t, PNode *node){
  static const Shape items[] = {{1, "expr"}, {3, "nexprlist COMMA expr"}};
  Source source = {node, part(t, node, 0), part(t, node, 1), part(t, node, 2), NULL, NULL, NULL};
  if(is(t, node, "stl_prefix nm dbnm as on_using")){
    source.alias = part(t, node, 3); source.constraint = part(t, node, 4);
    return source;
  }
  if(!is(t, node, "stl_prefix nm dbnm LP exprlist RP as on_using"))
    refuse(t, node, "Only tables and table-valued functions, with optional aliases, are modeled in FROM; "
                    "write table names and joins");
  PNode *listed = part(t, node, 4);
  Vec arguments = {0};
  if(listed->count){
    Items found = left_list(t, part(t, listed, 0), items, 2);
    for(int i = 0; i < found.count; i++) push(t, &arguments, query_expression(t, from_end(found.items[i], 1)));
  }
  source.alias = part(t, node, 6); source.constraint = part(t, node, 7);
  source.arguments = sequence(t, arguments, listed->start, part(t, node, 5)->start);
  return source;
}

/* A table or table-valued function with its optional alias; a schema name is refused. */
static Located *table_reference(T *t, Source source){
  absent(t, source.schema, "A schema name");
  Fields fields = {0};
  field(&fields, "table", name(t, source.table));
  field(&fields, "alias", alias(t, source.alias));
  field(&fields, "arguments", source.arguments ? source.arguments : leaf_null(t, source.table->start, source.table->end));
  return object(t, NULL, fields, source.table->start, source.table->end > source.alias->end ? source.table->end : source.alias->end);
}

/* The keywords of a joinop before JOIN, as written. */
static Located *join_operator(T *t, PNode *node){
  Vec words = {0};
  for(int i = 0; i < node->count; i++){
    PNode *word = part(t, node, i);
    if(strcmp(word->symbol, "COMMA") && strcmp(word->symbol, "JOIN")) push(t, &words, leaf_text(t, text(t, word), word->start, word->end));
  }
  return sequence(t, words, node->start, node->end);
}

/* The first source of a seltablist and its joins in order. */
void from_clause(T *t, PNode *tables, Located **first, Located **joins){
  static const Shape names[] = {{1, "nm"}, {3, "idlist COMMA nm"}};
  int count = 0;
  for(PNode *current = tables;; count++){
    PNode *joined = part(t, current, 0);
    if(!joined->count){ count++; break; }
    current = part(t, joined, 0);
  }
  Source *sources = arena(t, sizeof(Source) * (size_t)count);
  PNode *current = tables;
  for(int index = count - 1; index >= 0; index--){
    sources[index] = source_parts(t, current);
    if(!sources[index].joined->count) break;
    current = part(t, require(t, sources[index].joined, "seltablist joinop"), 0);
  }
  absent(t, sources[0].constraint, "ON or USING on the first table");
  *first = table_reference(t, sources[0]);
  Vec items = {0};
  for(int i = 1; i < count; i++){
    PNode *operator = part(t, require(t, sources[i].joined, "seltablist joinop"), 1), *constraint = sources[i].constraint;
    Located *condition = leaf_null(t, constraint->start, constraint->end), *using = condition;
    if(is(t, constraint, "ON expr")) condition = query_expression(t, part(t, constraint, 1));
    else if(is(t, constraint, "USING LP idlist RP")){
      PNode *listed = part(t, constraint, 2);
      Items found = left_list(t, listed, names, 2);
      Vec columns = {0};
      for(int j = 0; j < found.count; j++) push(t, &columns, name(t, from_end(found.items[j], 1)));
      using = sequence(t, columns, listed->start, listed->end);
    }
    Fields fields = {0};
    field(&fields, "operator", join_operator(t, operator));
    field(&fields, "source", table_reference(t, sources[i]));
    field(&fields, "condition", condition);
    field(&fields, "usingColumns", using);
    push(t, &items, object(t, NULL, fields, operator->start, sources[i].node->end));
  }
  *joins = sequence(t, items, sources[0].node->end, tables->end);
}
