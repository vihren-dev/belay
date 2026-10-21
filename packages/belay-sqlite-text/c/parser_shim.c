/* The parser library's C API with Lean's calling convention, for Belay.Sqlite.ParserLibrary.
** Each function returns an IO result: the JSON document as a string, or an IO error with the
** library's result code. The SQL is a byte array, so that text that is not UTF-8 reaches the
** library, which refuses it. */
#include <lean/lean.h>
#include "sqlite-verifier-parser.h"

/* Lake compiles with hidden symbols; the interpreter finds these two by name. */
#define BELAY_EXPORT __attribute__((visibility("default")))

/* The IO error of a library call that made no document, with the call's name and the reason for
** its result code. It allocates the message; the IO result owns it. */
static lean_obj_res failed(const char *call, int code) {
  const char *reason = code == SQLITE_VERIFIER_PARSER_UNKNOWN_GRAMMAR ? "the library has no such grammar"
    : code == SQLITE_VERIFIER_PARSER_NO_MEMORY ? "the library could not allocate memory" : "unknown result code";
  lean_object *text = lean_mk_string(call);
  text = lean_string_append(text, lean_mk_string(" call of the parser library failed: "));
  text = lean_string_append(text, lean_mk_string(reason));
  return lean_io_result_mk_error(lean_mk_io_user_error(text));
}

/* The IO result of a document that the library allocated: a Lean string with a copy of its bytes.
** It releases the library's document, so the caller keeps no pointer to it. */
static lean_obj_res document(char *bytes, size_t length) {
  lean_object *text = lean_mk_string_from_bytes(bytes, length);
  sqlite_verifier_parser_free(bytes);
  return lean_io_result_mk_ok(text);
}

/* Belay.Sqlite.ParserLibrary.metadata: the library's metadata document, as a Lean string. */
BELAY_EXPORT lean_obj_res belay_parser_metadata(lean_obj_arg world) {
  char *bytes = NULL;
  size_t length = 0;
  int code = sqlite_verifier_parser_metadata(&bytes, &length);
  return code == SQLITE_VERIFIER_PARSER_OK ? document(bytes, length) : failed("metadata", code);
}

/* Belay.Sqlite.ParserLibrary.parse: the parse document of the SQL bytes with the grammar, as a
** Lean string. It borrows the grammar string and the byte array. */
BELAY_EXPORT lean_obj_res belay_parser_parse(b_lean_obj_arg grammar, b_lean_obj_arg sql, lean_obj_arg world) {
  char *bytes = NULL;
  size_t length = 0;
  int code = sqlite_verifier_parser_parse(lean_string_cstr(grammar), lean_sarray_cptr(sql), lean_sarray_size(sql),
                                          &bytes, &length);
  return code == SQLITE_VERIFIER_PARSER_OK ? document(bytes, length) : failed("parse", code);
}
