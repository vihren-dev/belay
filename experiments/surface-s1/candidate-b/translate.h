/* Candidate B of ADR 0017, S1, prototype 2: the SQL translation in C, beside the parser.
**
** The port of belay/sqlite/syntax*.py. It maps the parse tree of a text to the model's
** statement syntax as the JSON that the codec reads, with the source range of each node
** (belay/sqlite/located.py), or to the refusal of the Python translation. A refusal ends the
** translation with longjmp, as a Python exception does; every allocation is in one arena that
** the entry point releases.
*/
#ifndef BELAY_TRANSLATE_H
#define BELAY_TRANSLATE_H
#include <setjmp.h>
#include <stddef.h>

/* One node of the parse tree: grammar symbol, half-open UTF-8 byte range, child indexes. */
typedef struct { const char *symbol; int start, end, count; int *children; } PNode;

/* The kinds of a located value: a rendered JSON leaf, a list, a structure, a constructor. */
enum { LEAF, LIST, OBJECT, CONSTRUCTOR };

/* One syntax value, its byte range and its located parts in path order. An OBJECT or a
** CONSTRUCTOR names each part; omit marks the parts that its JSON leaves out. */
typedef struct Located {
  int kind, start, end, count;
  const char *json, *name;
  struct Located **children;
  const char **fields;
  unsigned char *omit;
} Located;

/* A growing list of located values. */
typedef struct { Located **items; int count, capacity; } Vec;

/* Named parts of a structure or constructor, in order. */
typedef struct { const char *names[16]; Located *parts[16]; int count; } Fields;

/* One item of a left-recursive list: the parts after the nested list node. */
typedef struct { PNode **parts; int count; } Item;

/* The items of a list in text order. */
typedef struct { Item *items; int count; } Items;

/* The symbols of a list node for one number of parts. */
typedef struct { int count; const char *symbols; } Shape;

/* The subqueries of one statement, and the index of the one being mapped (-1 for none). */
typedef struct { Vec items; int current; } SubqueryList;

/* A growing output text, from malloc, which the caller releases. */
typedef struct { char *data; size_t length, capacity; int failed; } Buffer;

/* An arena block. */
typedef struct Block { struct Block *next; size_t used, size; char data[]; } Block;

/* The translation of one text: the tree, the arena, the refusal and the subquery scope. */
typedef struct {
  const unsigned char *sql;
  PNode *nodes;
  int count;
  Block *arena;
  jmp_buf fail;
  const char *status, *message;
  int start, end;
  SubqueryList *active;
  const char *refusal;
} T;

void *arena(T *t, size_t size);
char *text(T *t, PNode *node);
char *slice(T *t, int start, int end);
PNode *part(T *t, PNode *node, int index);
int is(T *t, PNode *node, const char *symbols);
PNode *require(T *t, PNode *node, const char *symbols);
void absent(T *t, PNode *node, const char *feature);
__attribute__((noreturn)) void refuse(T *t, PNode *node, const char *message);
Items left_list(T *t, PNode *node, const Shape *shapes, int count);
PNode *from_end(Item item, int position);

Located *leaf(T *t, const char *json, int start, int end);
Located *leaf_null(T *t, int start, int end);
Located *leaf_bool(T *t, int value, int start, int end);
Located *leaf_int(T *t, int value, int start, int end);
Located *leaf_text(T *t, const char *value, int start, int end);
Located *leaf_bytes(T *t, const unsigned char *bytes, size_t size, int start, int end);
Located *sequence(T *t, Vec items, int start, int end);
Located *object(T *t, const char *name, Fields fields, int start, int end);
Located *pair(T *t, Located *first, Located *second, int start, int end);
void push(T *t, Vec *vec, Located *item);
void field(Fields *fields, const char *name, Located *part);
Fields join(Fields first, Fields second);
void put(Buffer *buffer, const char *bytes, size_t size);
void put_text(Buffer *buffer, const char *value);
void put_json_string(Buffer *buffer, const char *bytes, size_t size);
void put_number(Buffer *buffer, long value);
void emit_value(Buffer *buffer, const Located *item);
void emit_located(Buffer *buffer, const Located *item);
#endif
