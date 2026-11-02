#include <stddef.h>
/* The sources use FILE only through pointers, so it stays incomplete. */
typedef struct FILE FILE;
#define FILENAME_MAX 4096
int fprintf(FILE *, const char *, ...);
size_t fwrite(const void *, size_t, size_t, FILE *);
int snprintf(char *, size_t, const char *, ...);
