/* CHECK, CONSTRAINT names, foreign keys, generated columns and conflict algorithms: the port
** of belay/sqlite/syntax_constraints.py and of resolve_type and constraint_algorithm of
** syntax_definitions.py. Texts are UTF-8 bytes; each word that they compare is ASCII. */
#include <string.h>
#include "syntax.h"

/* Whether a byte is one that sqlite3Isspace accepts. */
static int space(char c){ return c && strchr(" \t\n\f\r\v", c) != NULL; }

/* Whether the last bytes of a text of size bytes are the lowercase ASCII word, each letter in
** either ASCII case, as sqlite3_strnicmp compares a keyword. */
static int ends_with_word(const char *value, size_t size, const char *word){
  size_t length = strlen(word);
  if(length > size) return 0;
  for(size_t i = 0; i < length; i++){
    char c = value[size - length + i];
    if(c != word[i] && c + 32 != word[i]) return 0;
  }
  return 1;
}

/* Whether the text is the lowercase ASCII word, as sqlite3StrICmp compares a table option. */
int ascii_equal(const char *value, const char *word){
  return strlen(value) == strlen(word) && ends_with_word(value, strlen(value), word);
}

/* The size without the sqlite3Isspace bytes at the end. */
static size_t trim_end(const char *value, size_t size){
  while(size && space(value[size - 1])) size--;
  return size;
}

/* The type text without a trailing GENERATED ALWAYS, as sqlite3AddColumn removes it. */
char *declared_type(T *t, const char *value){
  size_t size = strlen(value);
  if(size >= 16 && ends_with_word(value, size, "always")){
    size = trim_end(value, size - 6);
    if(size >= 9 && ends_with_word(value, size, "generated")) size = trim_end(value, size - 9);
  }
  char *result = arena(t, size + 1);
  memcpy(result, value, size);
  return result;
}

/* The name of a CONSTRAINT name production as SQLite reports it: dequoted. */
char *constraint_name(T *t, PNode *node){ return dequote(t, text(t, node)); }

/* The algorithm of a resolvetype node: raisetype, IGNORE or REPLACE. */
Located *resolve_type(T *t, PNode *node){
  PNode *keyword = part(t, node, 0);
  if(!strcmp(keyword->symbol, "raisetype")) keyword = part(t, keyword, 0);
  const char *symbol = keyword->symbol;
  const char *value = !strcmp(symbol, "ROLLBACK") ? "\"rollback\"" : !strcmp(symbol, "ABORT") ? "\"abort\""
    : !strcmp(symbol, "FAIL") ? "\"fail\"" : !strcmp(symbol, "IGNORE") ? "\"ignore\"" : "\"replace\"";
  return leaf(t, value, node->start, node->end);
}

/* The algorithm of an onconf node, ON CONFLICT algorithm, or none. */
Located *constraint_algorithm(T *t, PNode *node){
  if(!node->count) return leaf_null(t, node->start, node->end);
  return resolve_type(t, part(t, require(t, node, "ON CONFLICT resolvetype"), 2));
}

/* CHECK (expr) with its label: the name in effect, else the text between the parentheses,
** trimmed and dequoted. */
Located *check(T *t, PNode *node, const char *current){
  PNode *condition = part(t, node, 2);
  char *inner = slice(t, part(t, node, 1)->end, part(t, node, 3)->start);
  while(space(*inner)) inner++;
  inner[trim_end(inner, strlen(inner))] = 0;
  const char *label = current ? current : dequote(t, inner);
  Fields fields = {0};
  field(&fields, "condition", query_expression(t, condition));
  field(&fields, "label", leaf_text(t, label, condition->start, condition->end));
  return object(t, "check", fields, node->start, node->end);
}

/* An eidlist of plain names, without collation or sort order. */
static Located *plain_names(T *t, PNode *node){
  static const Shape shapes[] = {{3, "nm collate sortorder"}, {5, "eidlist COMMA nm collate sortorder"}};
  Items items = left_list(t, node, shapes, 2);
  Vec names = {0};
  for(int i = 0; i < items.count; i++){
    absent(t, from_end(items.items[i], 2), "A collation in a foreign key");
    absent(t, from_end(items.items[i], 1), "A sort order in a foreign key");
    push(t, &names, name(t, from_end(items.items[i], 3)));
  }
  return sequence(t, names, node->start, node->end);
}

/* An eidlist_opt: the names of (names), or no names. */
static Located *optional_names(T *t, PNode *node){
  Vec none = {0};
  if(!node->count) return sequence(t, none, node->start, node->end);
  return plain_names(t, part(t, require(t, node, "LP eidlist RP"), 1));
}

/* The ON DELETE and ON UPDATE actions of a refargs node, noAction without a clause. */
static void actions(T *t, PNode *node, Located **on_delete, Located **on_update){
  static const Shape shapes[] = {{2, "refargs refarg"}};
  *on_delete = *on_update = leaf(t, "\"noAction\"", node->start, node->end);
  Items items = left_list(t, node, shapes, 1);
  for(int i = 0; i < items.count; i++){
    PNode *argument = from_end(items.items[i], 1);
    int deleting = is(t, argument, "ON DELETE refact");
    if(!deleting && !is(t, argument, "ON UPDATE refact")) continue;
    PNode *action = part(t, argument, 2);
    const char *value = is(t, action, "SET NULL") ? "\"setNull\"" : is(t, action, "SET DEFAULT") ? "\"setDefault\""
      : is(t, action, "CASCADE") ? "\"cascade\"" : is(t, action, "RESTRICT") ? "\"restrict\"" : "\"noAction\"";
    *(deleting ? on_delete : on_update) = leaf(t, value, action->start, action->end);
  }
}

/* AS (expr) [kind] with the kind token as written, or none. */
Located *generated(T *t, PNode *node, PNode *kind){
  int shaped = kind->count >= 3 && kind->count <= 4 && !strcmp(part(t, kind, 0)->symbol, "LP")
    && !strcmp(part(t, kind, 1)->symbol, "expr") && !strcmp(part(t, kind, 2)->symbol, "RP");
  if(!shaped) refuse(t, kind, "Unsupported generated column; write AS (expression) VIRTUAL or STORED");
  Located *word = kind->count == 4 ? leaf_text(t, text(t, part(t, kind, 3)), part(t, kind, 3)->start, part(t, kind, 3)->end)
    : leaf_null(t, kind->end, kind->end);
  Fields fields = {0};
  field(&fields, "expression", query_expression(t, part(t, kind, 1)));
  field(&fields, "kind", word);
  return object(t, "generated", fields, node->start, node->end);
}

/* A column's REFERENCES table [(columns)] with its actions. */
Located *references(T *t, PNode *node){
  Located *on_delete, *on_update;
  actions(t, part(t, node, 3), &on_delete, &on_update);
  Fields fields = {0};
  field(&fields, "table", name(t, part(t, node, 1)));
  field(&fields, "columns", optional_names(t, part(t, node, 2)));
  field(&fields, "onDelete", on_delete);
  field(&fields, "onUpdate", on_update);
  return object(t, "references", fields, node->start, node->end);
}

/* A defer_subclause as deferral, deferred only for DEFERRABLE INITIALLY DEFERRED. */
Located *deferral(T *t, PNode *node){
  int deferred = !strcmp(part(t, node, 0)->symbol, "DEFERRABLE") && is(t, part(t, node, node->count - 1), "INITIALLY DEFERRED");
  return one(t, "deferral", "deferred", leaf_bool(t, deferred, node->start, node->end), node->start, node->end);
}

/* FOREIGN KEY (columns) REFERENCES table [(columns)] with its actions. */
Located *foreign_key(T *t, PNode *node){
  Located *on_delete, *on_update;
  actions(t, part(t, node, 8), &on_delete, &on_update);
  Fields fields = {0};
  field(&fields, "columns", plain_names(t, part(t, node, 3)));
  field(&fields, "table", name(t, part(t, node, 6)));
  field(&fields, "referenced", optional_names(t, part(t, node, 7)));
  field(&fields, "onDelete", on_delete);
  field(&fields, "onUpdate", on_update);
  return object(t, "foreignKey", fields, node->start, node->end);
}
