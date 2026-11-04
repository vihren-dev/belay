/* The tokenizer of one tokenizer identity in the parser library.
**
** It reuses tokenizer.c, which includes the release's tokenizer cut sqlite3_tokenizer.c.
** Several tokenizers share the library, so SQLite's own symbols must stay internal to this
** translation unit: the cut's definitions are static or SQLITE_PRIVATE, which SQLite defines
** as static, and SQLITE_API makes its few public functions static too.
*/
#include "library_prefix.h"
#define SQLITE_API static
#include "tokenizer.c"
