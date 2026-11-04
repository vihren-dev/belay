/* The compile checks the date functions of sqlite3.c, so `struct tm` has the members that it uses.
** The layout can differ from the C library's: no kept code passes a `struct tm` to the C library. */
typedef long time_t;
struct tm { int tm_sec, tm_min, tm_hour, tm_mday, tm_mon, tm_year, tm_wday, tm_yday, tm_isdst; };
struct tm *localtime(const time_t *);
