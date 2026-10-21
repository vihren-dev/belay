/* DROP TABLE, DROP INDEX, DROP TRIGGER, CREATE INDEX and PRAGMA foreign_keys: the port of
** belay/sqlite/syntax_drops.py, syntax_indexes.py and syntax_pragmas.py. */
#include <stdio.h>
#include <string.h>
#include "syntax.h"

/* DROP TABLE|INDEX|TRIGGER [IF EXISTS] name, with the name as written. */
Located *drop(T *t, PNode *command){
  const char *kind = command->count > 1 ? part(t, command, 1)->symbol : "";
  char symbols[64];
  snprintf(symbols, sizeof symbols, "DROP %s ifexists fullname", kind);
  PNode *full = part(t, require(t, command, symbols), 3), *exists = part(t, command, 2);
  if(!is(t, full, "nm")) refuse(t, full, "A schema name is not modeled; remove it");
  Fields fields = {0};
  field(&fields, "name", name(t, part(t, full, 0)));
  field(&fields, "ifExists", leaf_bool(t, exists->count > 0, exists->start, exists->end));
  const char *constructor = !strcmp(kind, "TABLE") ? "dropTable" : !strcmp(kind, "INDEX") ? "dropIndex" : "dropTrigger";
  return object(t, constructor, fields, command->start, command->end);
}

/* CREATE [UNIQUE] INDEX name ON table(terms) [WHERE filter]. */
Located *create_index(T *t, PNode *command){
  require(t, command, "createkw uniqueflag INDEX ifnotexists nm dbnm ON nm LP sortlist RP where_opt");
  absent(t, part(t, command, 3), "IF NOT EXISTS");
  absent(t, part(t, command, 5), "A schema name");
  PNode *where = part(t, command, 11), *unique = part(t, command, 1), *terms = part(t, command, 9);
  Located *filter = where->count ? query_expression(t, part(t, where, 1)) : leaf_null(t, where->start, where->end);
  Fields fields = {0};
  field(&fields, "name", name(t, part(t, command, 4)));
  field(&fields, "unique", leaf_bool(t, unique->count > 0, unique->start, unique->end));
  field(&fields, "table", name(t, part(t, command, 7)));
  field(&fields, "terms", sequence(t, order_terms(t, terms), terms->start, terms->end));
  field(&fields, "filter", filter);
  return object(t, "createIndex", fields, command->start, command->end);
}

/* The refusal of a PRAGMA foreign_keys value that the model does not read. */
static const char VALUES[] = "Only on, off, yes, no, true, false, 0 and 1 are modeled as the value of PRAGMA foreign_keys";

/* The boolean of an nmnum value, 0 or 1, or its refusal. */
static int setting_value(T *t, PNode *node){
  static const char *const words[] = {"on", "yes", "true", "off", "no", "false"};
  if(is(t, node, "plus_num") && is(t, part(t, node, 0), "INTEGER")){
    char *number = text(t, part(t, node, 0));
    if(!strcmp(number, "0") || !strcmp(number, "1")) return number[0] == '1';
  } else if(is(t, node, "ON") || is(t, node, "nm")){
    const char *word = is(t, node, "nm") ? dequote(t, text(t, part(t, node, 0))) : "on";
    for(int i = 0; i < 6; i++) if(ascii_equal(word, words[i])) return i < 3;
  }
  refuse(t, node, VALUES);
  return 0;
}

/* PRAGMA foreign_keys [= value] and PRAGMA foreign_keys(value), whose value is none for the
** query form. */
Located *pragma(T *t, PNode *command){
  if(command->count < 3 || !ascii_equal(dequote(t, text(t, part(t, command, 1))), "foreign_keys") || part(t, command, 2)->count)
    refuse(t, command, "Only PRAGMA foreign_keys is modeled, without a schema name");
  Located *value;
  if(is(t, command, "PRAGMA nm dbnm")) value = leaf_null(t, command->start, command->end);
  else if(is(t, command, "PRAGMA nm dbnm EQ nmnum") || is(t, command, "PRAGMA nm dbnm LP nmnum RP"))
    value = leaf_bool(t, setting_value(t, part(t, command, 4)), command->start, command->end);
  else refuse(t, command, VALUES);
  return one(t, "pragmaForeignKeys", "value", value, command->start, command->end);
}
