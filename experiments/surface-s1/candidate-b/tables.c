/* Column definitions, CREATE TABLE and ALTER TABLE ADD COLUMN: the port of
** belay/sqlite/syntax_definitions.py. */
#include <string.h>
#include "syntax.h"

/* A DEFAULT constraint's value with its text. */
static Located *default_value(T *t, PNode *node, Located *value){
  Fields fields = {0};
  field(&fields, "value", value);
  field(&fields, "sourceText", leaf_text(t, slice(t, value->start, value->end), value->start, value->end));
  return object(t, "default", fields, node->start, node->end);
}

/* One column constraint, with the label of the constraint name in effect for a CHECK. */
static Located *column_constraint(T *t, PNode *node, const char *current){
  if(is(t, node, "CHECK LP expr RP")) return check(t, node, current);
  if(is(t, node, "REFERENCES nm eidlist_opt refargs")) return references(t, node);
  if(is(t, node, "AS generated")) return generated(t, node, part(t, node, 1));
  if(is(t, node, "NOT NULL onconf"))
    return one(t, "notNull", "algorithm", constraint_algorithm(t, part(t, node, 2)), node->start, node->end);
  if(is(t, node, "PRIMARY KEY sortorder onconf autoinc")){
    absent(t, part(t, node, 4), "AUTOINCREMENT");
    PNode *order = part(t, node, 2);
    Fields fields = {0};
    field(&fields, "descending", leaf_bool(t, is(t, order, "DESC"), order->start, order->end));
    field(&fields, "algorithm", constraint_algorithm(t, part(t, node, 3)));
    return object(t, "primaryKey", fields, node->start, node->end);
  }
  if(is(t, node, "UNIQUE onconf"))
    return one(t, "unique", "algorithm", constraint_algorithm(t, part(t, node, 1)), node->start, node->end);
  if(is(t, node, "COLLATE ID") || is(t, node, "COLLATE STRING"))
    return one(t, "collate", "name", name(t, part(t, node, 1)), node->start, node->end);
  if(is(t, node, "DEFAULT scantok term")) return default_value(t, node, term(t, part(t, node, 2)));
  if(is(t, node, "DEFAULT MINUS scantok term") || is(t, node, "DEFAULT PLUS scantok term")){
    PNode *sign = part(t, node, 1), *value = part(t, node, 3);
    const char *kind = !strcmp(sign->symbol, "MINUS") ? "negate" : "positive";
    return default_value(t, node, one(t, kind, "operand", term(t, value), sign->start, value->end));
  }
  if(is(t, node, "DEFAULT scantok ID")) return default_value(t, node, identifier(t, part(t, node, 2)));
  refuse(t, node, "Unsupported column constraint; use NOT NULL, PRIMARY KEY, UNIQUE, COLLATE, CHECK, REFERENCES "
                  "or DEFAULT with a literal");
  return NULL;
}

/* A column's name, declared type and constraints; *current is the constraint name in effect
** after them. CONSTRAINT name maps to no constraint, as it only labels later CHECKs. */
Located *column_definition(T *t, PNode *column, PNode *constraints, const char **current){
  static const Shape shapes[] = {{2, "carglist ccons"}};
  require(t, column, "nm typetoken");
  PNode *type = part(t, column, 1);
  Located *declared = type->count ? leaf_text(t, dequote(t, declared_type(t, text(t, type))), type->start, type->end)
    : leaf_null(t, type->start, type->end);
  Items items = left_list(t, constraints, shapes, 1);
  Vec mapped = {0};
  *current = NULL;
  for(int i = 0; i < items.count; i++){
    PNode *constraint = from_end(items.items[i], 1);
    if(is(t, constraint, "CONSTRAINT nm")) *current = constraint_name(t, part(t, constraint, 1));
    else if(is(t, constraint, "defer_subclause")) push(t, &mapped, deferral(t, part(t, constraint, 0)));
    else push(t, &mapped, column_constraint(t, constraint, *current));
  }
  Fields fields = {0};
  field(&fields, "name", name(t, part(t, column, 0)));
  field(&fields, "declaredType", declared);
  field(&fields, "constraints", sequence(t, mapped, constraints->start, constraints->end));
  return object(t, NULL, fields, column->start, constraints->end);
}

/* A key column list of plain names, without sort order, collation or expressions. */
static Located *sort_names(T *t, PNode *node){
  static const Shape shapes[] = {{3, "expr sortorder nulls"}, {5, "sortlist COMMA expr sortorder nulls"}};
  Items items = left_list(t, node, shapes, 2);
  Vec names = {0};
  for(int i = 0; i < items.count; i++){
    absent(t, from_end(items.items[i], 2), "A sort order in a key");
    absent(t, from_end(items.items[i], 1), "NULLS FIRST or NULLS LAST");
    push(t, &names, name(t, part(t, require(t, from_end(items.items[i], 3), "ID"), 0)));
  }
  return sequence(t, names, node->start, node->end);
}

/* A table PRIMARY KEY or UNIQUE over plain column names, a CHECK, or a FOREIGN KEY. */
static Located *table_constraint(T *t, PNode *node, const char *current){
  if(is(t, node, "CHECK LP expr RP onconf")) return check(t, node, current);
  if(is(t, node, "FOREIGN KEY LP eidlist RP REFERENCES nm eidlist_opt refargs defer_subclause_opt")) return foreign_key(t, node);
  int primary = is(t, node, "PRIMARY KEY LP sortlist autoinc RP onconf");
  if(!primary && !is(t, node, "UNIQUE LP sortlist RP onconf"))
    refuse(t, node, "Unsupported table constraint; use PRIMARY KEY or UNIQUE over column names, CHECK or FOREIGN KEY");
  if(primary) absent(t, part(t, node, 4), "AUTOINCREMENT");
  Fields fields = {0};
  field(&fields, "columns", sort_names(t, part(t, node, primary ? 3 : 2)));
  field(&fields, "algorithm", constraint_algorithm(t, part(t, node, primary ? 6 : 4)));
  return object(t, primary ? "primaryKey" : "unique", fields, node->start, node->end);
}

/* The table options WITHOUT ROWID and STRICT; strict is present only when true. */
static Located *table_options(T *t, PNode *node){
  static const Shape shapes[] = {{1, "table_option"}, {3, "table_option_set COMMA table_option"}};
  Items items = left_list(t, node, shapes, 2);
  int without_rowid = 0, strict = 0;
  for(int i = 0; i < items.count; i++){
    PNode *option = from_end(items.items[i], 1);
    if(is(t, option, "WITHOUT nm") && ascii_equal(text(t, part(t, option, 1)), "rowid")) without_rowid = 1;
    else if(is(t, option, "nm") && ascii_equal(text(t, part(t, option, 0)), "strict")) strict = 1;
    else refuse(t, option, "Unknown table option; use WITHOUT ROWID or STRICT");
  }
  Fields fields = {0};
  field(&fields, "withoutRowid", leaf_bool(t, without_rowid, node->start, node->end));
  if(strict) field(&fields, "strict", leaf_bool(t, 1, node->start, node->end));
  return object(t, NULL, fields, node->start, node->end);
}

/* CREATE TABLE with column definitions and table constraints. */
Located *create_table(T *t, PNode *command){
  static const Shape column_shapes[] = {{2, "columnname carglist"}, {4, "columnlist COMMA columnname carglist"}};
  static const Shape constraint_shapes[] = {{1, "tcons"}, {3, "conslist tconscomma tcons"}};
  PNode *header = require(t, part(t, command, 0), "createkw temp TABLE ifnotexists nm dbnm");
  PNode *body = require(t, part(t, command, 1), "LP columnlist conslist_opt RP table_option_set");
  absent(t, part(t, header, 1), "TEMP");
  absent(t, part(t, header, 3), "IF NOT EXISTS");
  absent(t, part(t, header, 5), "A schema name");
  Items columns = left_list(t, part(t, body, 1), column_shapes, 2);
  Vec definitions = {0}, constraints = {0};
  const char *current = NULL;
  for(int i = 0; i < columns.count; i++)
    push(t, &definitions, column_definition(t, from_end(columns.items[i], 2), from_end(columns.items[i], 1), &current));
  PNode *listed = part(t, body, 2);
  if(listed->count){
    Items items = left_list(t, part(t, require(t, listed, "COMMA conslist"), 1), constraint_shapes, 2);
    for(int i = 0; i < items.count; i++){
      if(items.items[i].count == 2 && items.items[i].parts[0]->count) current = NULL;
      PNode *constraint = from_end(items.items[i], 1), *final = part(t, constraint, constraint->count - 1);
      if(is(t, constraint, "CONSTRAINT nm")){ current = constraint_name(t, part(t, constraint, 1)); continue; }
      push(t, &constraints, table_constraint(t, constraint, current));
      if(!strcmp(final->symbol, "defer_subclause_opt") && final->count) push(t, &constraints, deferral(t, part(t, final, 0)));
    }
  }
  Fields fields = {0};
  field(&fields, "name", name(t, part(t, header, 4)));
  field(&fields, "columns", sequence(t, definitions, part(t, body, 1)->start, part(t, body, 1)->end));
  field(&fields, "constraints", sequence(t, constraints, listed->start, listed->end));
  field(&fields, "options", table_options(t, part(t, body, 4)));
  return object(t, "createTable", fields, command->start, command->end);
}

/* ALTER TABLE ADD [COLUMN] for an unqualified table name. */
Located *add_column(T *t, PNode *command){
  require(t, command, "ALTER TABLE add_column_fullname ADD kwcolumn_opt columnname carglist");
  PNode *table = part(t, require(t, part(t, require(t, part(t, command, 2), "fullname"), 0), "nm"), 0);
  const char *current;
  Fields fields = {0};
  field(&fields, "table", name(t, table));
  field(&fields, "column", column_definition(t, part(t, command, 5), part(t, command, 6), &current));
  return object(t, "addColumn", fields, command->start, command->end);
}
