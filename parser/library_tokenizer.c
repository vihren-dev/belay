/* The tokenizer of one grammar in the parser library.
**
** It reuses tokenizer.c, which includes the release's sqlite3.c. Each grammar of the
** library has its own tokenizer, so SQLite's own symbols must stay internal to this
** translation unit: SQLITE_API makes the public SQLite functions static, and an empty
** SQLITE_EXTERN keeps the "static extern" declarations valid.
*/
#include "library_prefix.h"
#define SQLITE_API static
#define SQLITE_EXTERN
#include "tokenizer.c"

/* SQLITE_OS_OTHER leaves the operating system layer to the application. The tokenizer never opens
** SQLite's library, so these two functions have nothing to set up or release; defining them keeps
** the compile free of warnings about functions that are declared but not defined. */
SQLITE_API int sqlite3_os_init(void){ return SQLITE_OK; }
SQLITE_API int sqlite3_os_end(void){ return SQLITE_OK; }
