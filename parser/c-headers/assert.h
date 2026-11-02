/* Asserts are debug checks. The compile drops them, so the library calls no `__assert_fail`. */
#define assert(condition) ((void)0)
