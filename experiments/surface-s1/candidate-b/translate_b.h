/* The C API of candidate B: SQL text to the model's statement syntax as JSON, with ranges. */
#ifndef BELAY_TRANSLATE_B_H
#define BELAY_TRANSLATE_B_H
#include <stddef.h>

/* Parse length bytes of SQL with the parser library's grammar and translate them. On success
** (SQLITE_VERIFIER_PARSER_OK), *document holds {"statements": [...]}, each statement located as
** belay/sqlite/located.py keeps it, or {"refusal": diagnostic}; release it with
** belay_translate_free. Other results are the parser library's. */
__attribute__((visibility("default")))
int belay_translate(const char *grammar, const unsigned char *sql, size_t length, char **document, size_t *document_length);

/* Release a document of belay_translate. */
__attribute__((visibility("default"))) void belay_translate_free(char *document);
#endif
