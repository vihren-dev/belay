/* Located values and their JSON: the port of belay/sqlite/located.py and of the JSON that
** experiments/surface-s1/texts.py writes for each node. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "syntax.h"

/* Append bytes to the buffer; after a failed allocation, appends stop. */
void put(Buffer *buffer, const char *bytes, size_t size){
  if(buffer->failed) return;
  if(buffer->length + size + 1 > buffer->capacity){
    size_t capacity = buffer->capacity ? buffer->capacity : 4096;
    while(buffer->length + size + 1 > capacity) capacity *= 2;
    char *data = realloc(buffer->data, capacity);
    if(!data){ buffer->failed = 1; return; }
    buffer->data = data;
    buffer->capacity = capacity;
  }
  memcpy(buffer->data + buffer->length, bytes, size);
  buffer->length += size;
  buffer->data[buffer->length] = 0;
}

/* Append NUL-terminated text. */
void put_text(Buffer *buffer, const char *value){ put(buffer, value, strlen(value)); }

/* Append a decimal number. */
void put_number(Buffer *buffer, long value){
  char digits[24];
  int size = snprintf(digits, sizeof digits, "%ld", value);
  put(buffer, digits, (size_t)size);
}

/* Append UTF-8 bytes as a JSON string, with control characters as \u escapes. */
void put_json_string(Buffer *buffer, const char *bytes, size_t size){
  put(buffer, "\"", 1);
  for(size_t i = 0; i < size; i++){
    unsigned char c = (unsigned char)bytes[i];
    if(c == '"' || c == '\\'){ char escaped[2] = {'\\', (char)c}; put(buffer, escaped, 2); }
    else if(c < 32){ char escaped[8]; snprintf(escaped, sizeof escaped, "\\u%04x", c); put(buffer, escaped, 6); }
    else put(buffer, (const char *)&bytes[i], 1);
  }
  put(buffer, "\"", 1);
}

/* A value without located parts, rendered as JSON. */
Located *leaf(T *t, const char *json, int start, int end){
  Located *item = arena(t, sizeof(Located));
  item->kind = LEAF; item->json = json; item->start = start; item->end = end;
  return item;
}

Located *leaf_null(T *t, int start, int end){ return leaf(t, "null", start, end); }
Located *leaf_bool(T *t, int value, int start, int end){ return leaf(t, value ? "true" : "false", start, end); }

Located *leaf_int(T *t, int value, int start, int end){
  char *json = arena(t, 16);
  snprintf(json, 16, "%d", value);
  return leaf(t, json, start, end);
}

/* A text leaf; the JSON is rendered into the arena. */
Located *leaf_text(T *t, const char *value, int start, int end){
  Buffer buffer = {0};
  put_json_string(&buffer, value, strlen(value));
  if(buffer.failed){ free(buffer.data); return leaf(t, "null", start, end); }
  char *json = arena(t, buffer.length + 1);
  memcpy(json, buffer.data, buffer.length);
  free(buffer.data);
  return leaf(t, json, start, end);
}

/* A list of byte values. */
Located *leaf_bytes(T *t, const unsigned char *bytes, size_t size, int start, int end){
  char *json = arena(t, size * 4 + 3), *cursor = json;
  *cursor++ = '[';
  for(size_t i = 0; i < size; i++) cursor += sprintf(cursor, i ? ",%u" : "%u", bytes[i]);
  *cursor = ']';
  return leaf(t, json, start, end);
}

/* Add an item to a list. */
void push(T *t, Vec *vec, Located *item){
  if(vec->count == vec->capacity){
    int capacity = vec->capacity ? vec->capacity * 2 : 4;
    Located **items = arena(t, sizeof(Located *) * (size_t)capacity);
    if(vec->count) memcpy(items, vec->items, sizeof(Located *) * (size_t)vec->count);
    vec->items = items; vec->capacity = capacity;
  }
  vec->items[vec->count++] = item;
}

/* A list value whose path steps are the item indexes. */
Located *sequence(T *t, Vec items, int start, int end){
  Located *item = arena(t, sizeof(Located));
  item->kind = LIST; item->children = items.items; item->count = items.count; item->start = start; item->end = end;
  return item;
}

/* Add a named part. */
void field(Fields *fields, const char *name, Located *part){
  fields->names[fields->count] = name;
  fields->parts[fields->count++] = part;
}

/* The parts of both, in order. */
Fields join(Fields first, Fields second){
  for(int i = 0; i < second.count; i++) field(&first, second.names[i], second.parts[i]);
  return first;
}

/* A structure, or with a name a constructor encoded as {name: {field: value}}. */
Located *object(T *t, const char *name, Fields fields, int start, int end){
  Located *item = arena(t, sizeof(Located));
  item->kind = name ? CONSTRUCTOR : OBJECT; item->name = name; item->start = start; item->end = end;
  item->count = fields.count;
  item->children = arena(t, sizeof(Located *) * (size_t)(fields.count + 1));
  item->fields = arena(t, sizeof(char *) * (size_t)(fields.count + 1));
  item->omit = arena(t, (size_t)fields.count + 1);
  for(int i = 0; i < fields.count; i++){ item->children[i] = fields.parts[i]; item->fields[i] = fields.names[i]; }
  return item;
}

/* A Lean pair, encoded as a two-element array. */
Located *pair(T *t, Located *first, Located *second, int start, int end){
  Vec items = {0};
  push(t, &items, first);
  push(t, &items, second);
  return sequence(t, items, start, end);
}

/* Append the JSON value of a located value. */
void emit_value(Buffer *buffer, const Located *item){
  if(item->kind == LEAF){ put_text(buffer, item->json); return; }
  if(item->kind == LIST){
    put(buffer, "[", 1);
    for(int i = 0; i < item->count; i++){ if(i) put(buffer, ",", 1); emit_value(buffer, item->children[i]); }
    put(buffer, "]", 1);
    return;
  }
  if(item->kind == CONSTRUCTOR){ put(buffer, "{", 1); put_json_string(buffer, item->name, strlen(item->name)); put(buffer, ":", 1); }
  put(buffer, "{", 1);
  for(int i = 0, first = 1; i < item->count; i++){
    if(item->omit[i]) continue;
    if(!first) put(buffer, ",", 1);
    first = 0;
    put_json_string(buffer, item->fields[i], strlen(item->fields[i]));
    put(buffer, ":", 1);
    emit_value(buffer, item->children[i]);
  }
  put(buffer, item->kind == CONSTRUCTOR ? "}}" : "}", item->kind == CONSTRUCTOR ? 2 : 1);
}

/* Append a located value as {"value", "start", "end", "children"}. */
void emit_located(Buffer *buffer, const Located *item){
  put_text(buffer, "{\"value\":");
  emit_value(buffer, item);
  put_text(buffer, ",\"start\":"); put_number(buffer, item->start);
  put_text(buffer, ",\"end\":"); put_number(buffer, item->end);
  put_text(buffer, ",\"children\":[");
  for(int i = 0; i < item->count; i++){ if(i) put(buffer, ",", 1); emit_located(buffer, item->children[i]); }
  put(buffer, "]}", 2);
}
