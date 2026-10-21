/* The arena, the tree helpers and the shape checks of candidate B: the port of
** belay/sqlite/sql_tree.py and syntax_shapes.py. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "syntax.h"

/* The corrective action for a production that has no syntax constructor. */
static const char MODELED_FORMS[] = "rewrite it with the modeled forms: CREATE TABLE, CREATE [UNIQUE] INDEX, "
  "ALTER TABLE ADD COLUMN, BEGIN, COMMIT, ROLLBACK, INSERT ... VALUES, UPDATE ... SET ... [WHERE column = value] "
  "and SELECT ... FROM table [WHERE] [GROUP BY] [ORDER BY] [LIMIT]";

/* Allocate zeroed memory that lives until the translation ends; a failed allocation is a
** resource refusal. */
void *arena(T *t, size_t size){
  size = (size + 15) & ~(size_t)15;
  if(!t->arena || t->arena->used + size > t->arena->size){
    size_t capacity = size > 65536 ? size : 65536;
    Block *block = malloc(sizeof(Block) + capacity);
    if(!block){ t->status = "UNVERIFIED"; t->message = "out of memory"; t->start = t->end = 0; longjmp(t->fail, 1); }
    block->next = t->arena; block->used = 0; block->size = capacity;
    t->arena = block;
  }
  void *result = t->arena->data + t->arena->used;
  t->arena->used += size;
  memset(result, 0, size);
  return result;
}

/* The bytes of a range as a NUL-terminated text. */
char *slice(T *t, int start, int end){
  char *result = arena(t, (size_t)(end - start) + 1);
  memcpy(result, t->sql + start, (size_t)(end - start));
  return result;
}

/* The text of a node. */
char *text(T *t, PNode *node){ return slice(t, node->start, node->end); }

/* The part of a node at an index. */
PNode *part(T *t, PNode *node, int index){ return &t->nodes[node->children[index]]; }

/* Whether the symbols of a node's parts are the space-separated symbols; "" is no parts. */
int is(T *t, PNode *node, const char *symbols){
  const char *cursor = symbols;
  for(int i = 0; i < node->count; i++){
    if(!*cursor) return 0;
    const char *end = strchr(cursor, ' ');
    size_t size = end ? (size_t)(end - cursor) : strlen(cursor);
    const char *symbol = part(t, node, i)->symbol;
    if(strlen(symbol) != size || strncmp(symbol, cursor, size)) return 0;
    cursor += size + (end ? 1 : 0);
  }
  return *cursor == 0;
}

/* End the translation with the refusal of a node. */
__attribute__((noreturn)) void refuse(T *t, PNode *node, const char *message){
  t->status = "UNSUPPORTED"; t->message = message; t->start = node->start; t->end = node->end;
  longjmp(t->fail, 1);
}

/* The refusal of a production whose symbols are not the ones that the translation maps. */
static void unsupported_form(T *t, PNode *node){
  size_t size = strlen(node->symbol) + sizeof MODELED_FORMS + 32;
  char *message = arena(t, size);
  snprintf(message, size, "Unsupported SQL form: %s; %s", node->symbol, MODELED_FORMS);
  refuse(t, node, message);
}

/* The node itself when its parts have exactly these symbols, or its refusal. */
PNode *require(T *t, PNode *node, const char *symbols){
  if(!is(t, node, symbols)) unsupported_form(t, node);
  return node;
}

/* Refuse optional syntax that is present. */
void absent(T *t, PNode *node, const char *feature){
  if(!node->count) return;
  size_t size = strlen(feature) + 32;
  char *message = arena(t, size);
  snprintf(message, size, "%s is not modeled; remove it", feature);
  refuse(t, node, message);
}

/* Whether a list node continues the list: its first part is a list node of the same symbol.
** Each list node must have one of the shapes, or the list is refused. */
static int continues(T *t, PNode *node, const Shape *shapes, int count){
  const char *expected = NULL;
  for(int i = 0; i < count; i++) if(shapes[i].count == node->count) expected = shapes[i].symbols;
  if(!expected || !is(t, node, expected)) unsupported_form(t, node);
  return !strcmp(part(t, node, 0)->symbol, node->symbol);
}

/* Flatten a left-recursive list in text order; an empty list node ends the list. Each item is
** the parts of one list node after the nested list node. */
Items left_list(T *t, PNode *node, const Shape *shapes, int count){
  int total = 0;
  for(PNode *current = node; current->count; current = part(t, current, 0)){
    total++;
    if(!continues(t, current, shapes, count)) break;
  }
  Items result = {arena(t, sizeof(Item) * (size_t)(total + 1)), total};
  int index = total;
  for(PNode *current = node; current->count; current = part(t, current, 0)){
    int nested = continues(t, current, shapes, count);
    Item item = {arena(t, sizeof(PNode *) * (size_t)current->count), 0};
    for(int i = nested; i < current->count; i++) item.parts[item.count++] = part(t, current, i);
    result.items[--index] = item;
    if(!nested) break;
  }
  return result;
}

/* The part at a position from the end of an item: 1 is the last. */
PNode *from_end(Item item, int position){ return item.parts[item.count - position]; }
