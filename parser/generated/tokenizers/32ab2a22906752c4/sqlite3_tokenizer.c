#ifndef SQLITE_AMALGAMATION
#ifndef SQLITE_PRIVATE
# define SQLITE_PRIVATE static
#endif
#ifndef SQLITEINT_H
#if defined(__has_attribute)
#  if __has_attribute(fallthrough)
#    define deliberate_fall_through __attribute__((fallthrough));
#  endif
#endif
#if !defined(deliberate_fall_through)
#  define deliberate_fall_through
#endif
#ifndef SQLITE3_H
#ifdef SQLITE_INT64_TYPE
  typedef SQLITE_INT64_TYPE sqlite_int64;
#elif defined(_MSC_VER) || defined(__BORLANDC__)
  typedef __int64 sqlite_int64;
#else
  typedef long long int sqlite_int64;
#endif
#define SQLITE_OK           0   /* Successful result */
#define SQLITE_ERROR        1   /* Generic error */
#endif /* SQLITE3_H */
#if !defined(NDEBUG) && !defined(SQLITE_DEBUG)
# define NDEBUG 1
#endif
#if defined(SQLITE_COVERAGE_TEST) || defined(SQLITE_DEBUG)
# define testcase(X)  if( X ){ sqlite3CoverageCounter += (unsigned)__LINE__; }
#else
# define testcase(X)
#endif
#define SQLITE_DIGIT_SEPARATOR '_'
/************** Begin file parse.h *******************************************/
#define TK_SEMI                             1
#define TK_EXPLAIN                          2
#define TK_QUERY                            3
#define TK_PLAN                             4
#define TK_BEGIN                            5
#define TK_TRANSACTION                      6
#define TK_DEFERRED                         7
#define TK_IMMEDIATE                        8
#define TK_EXCLUSIVE                        9
#define TK_COMMIT                          10
#define TK_END                             11
#define TK_ROLLBACK                        12
#define TK_SAVEPOINT                       13
#define TK_RELEASE                         14
#define TK_TO                              15
#define TK_TABLE                           16
#define TK_CREATE                          17
#define TK_IF                              18
#define TK_NOT                             19
#define TK_EXISTS                          20
#define TK_TEMP                            21
#define TK_LP                              22
#define TK_RP                              23
#define TK_AS                              24
#define TK_COMMA                           25
#define TK_WITHOUT                         26
#define TK_ABORT                           27
#define TK_ACTION                          28
#define TK_AFTER                           29
#define TK_ANALYZE                         30
#define TK_ASC                             31
#define TK_ATTACH                          32
#define TK_BEFORE                          33
#define TK_BY                              34
#define TK_CASCADE                         35
#define TK_CAST                            36
#define TK_CONFLICT                        37
#define TK_DATABASE                        38
#define TK_DESC                            39
#define TK_DETACH                          40
#define TK_EACH                            41
#define TK_FAIL                            42
#define TK_OR                              43
#define TK_AND                             44
#define TK_IS                              45
#define TK_ISNOT                           46
#define TK_MATCH                           47
#define TK_LIKE_KW                         48
#define TK_BETWEEN                         49
#define TK_IN                              50
#define TK_ISNULL                          51
#define TK_NOTNULL                         52
#define TK_NE                              53
#define TK_EQ                              54
#define TK_GT                              55
#define TK_LE                              56
#define TK_LT                              57
#define TK_GE                              58
#define TK_ESCAPE                          59
#define TK_ID                              60
#define TK_COLUMNKW                        61
#define TK_DO                              62
#define TK_FOR                             63
#define TK_IGNORE                          64
#define TK_INITIALLY                       65
#define TK_INSTEAD                         66
#define TK_NO                              67
#define TK_KEY                             68
#define TK_OF                              69
#define TK_OFFSET                          70
#define TK_PRAGMA                          71
#define TK_RAISE                           72
#define TK_RECURSIVE                       73
#define TK_REPLACE                         74
#define TK_RESTRICT                        75
#define TK_ROW                             76
#define TK_ROWS                            77
#define TK_TRIGGER                         78
#define TK_VACUUM                          79
#define TK_VIEW                            80
#define TK_VIRTUAL                         81
#define TK_WITH                            82
#define TK_NULLS                           83
#define TK_FIRST                           84
#define TK_LAST                            85
#define TK_CURRENT                         86
#define TK_FOLLOWING                       87
#define TK_PARTITION                       88
#define TK_PRECEDING                       89
#define TK_RANGE                           90
#define TK_UNBOUNDED                       91
#define TK_EXCLUDE                         92
#define TK_GROUPS                          93
#define TK_OTHERS                          94
#define TK_TIES                            95
#define TK_GENERATED                       96
#define TK_ALWAYS                          97
#define TK_MATERIALIZED                    98
#define TK_REINDEX                         99
#define TK_RENAME                         100
#define TK_CTIME_KW                       101
#define TK_ANY                            102
#define TK_BITAND                         103
#define TK_BITOR                          104
#define TK_LSHIFT                         105
#define TK_RSHIFT                         106
#define TK_PLUS                           107
#define TK_MINUS                          108
#define TK_STAR                           109
#define TK_SLASH                          110
#define TK_REM                            111
#define TK_CONCAT                         112
#define TK_PTR                            113
#define TK_COLLATE                        114
#define TK_BITNOT                         115
#define TK_ON                             116
#define TK_INDEXED                        117
#define TK_STRING                         118
#define TK_JOIN_KW                        119
#define TK_CONSTRAINT                     120
#define TK_DEFAULT                        121
#define TK_NULL                           122
#define TK_PRIMARY                        123
#define TK_UNIQUE                         124
#define TK_CHECK                          125
#define TK_REFERENCES                     126
#define TK_AUTOINCR                       127
#define TK_INSERT                         128
#define TK_DELETE                         129
#define TK_UPDATE                         130
#define TK_SET                            131
#define TK_DEFERRABLE                     132
#define TK_FOREIGN                        133
#define TK_DROP                           134
#define TK_UNION                          135
#define TK_ALL                            136
#define TK_EXCEPT                         137
#define TK_INTERSECT                      138
#define TK_SELECT                         139
#define TK_VALUES                         140
#define TK_DISTINCT                       141
#define TK_DOT                            142
#define TK_FROM                           143
#define TK_JOIN                           144
#define TK_USING                          145
#define TK_ORDER                          146
#define TK_GROUP                          147
#define TK_HAVING                         148
#define TK_LIMIT                          149
#define TK_WHERE                          150
#define TK_RETURNING                      151
#define TK_INTO                           152
#define TK_NOTHING                        153
#define TK_FLOAT                          154
#define TK_BLOB                           155
#define TK_INTEGER                        156
#define TK_VARIABLE                       157
#define TK_CASE                           158
#define TK_WHEN                           159
#define TK_THEN                           160
#define TK_ELSE                           161
#define TK_INDEX                          162
#define TK_ALTER                          163
#define TK_ADD                            164
#define TK_WINDOW                         165
#define TK_OVER                           166
#define TK_FILTER                         167
#define TK_COLUMN                         168
#define TK_AGG_FUNCTION                   169
#define TK_AGG_COLUMN                     170
#define TK_TRUEFALSE                      171
#define TK_FUNCTION                       172
#define TK_UPLUS                          173
#define TK_UMINUS                         174
#define TK_TRUTH                          175
#define TK_REGISTER                       176
#define TK_VECTOR                         177
#define TK_SELECT_COLUMN                  178
#define TK_IF_NULL_ROW                    179
#define TK_ASTERISK                       180
#define TK_SPAN                           181
#define TK_ERROR                          182
#define TK_QNUMBER                        183
#define TK_SPACE                          184
#define TK_COMMENT                        185
#define TK_ILLEGAL                        186

/************** End of parse.h ***********************************************/
#include <assert.h>
#if 'A' == '\301'
#else
# define SQLITE_ASCII 1
#endif
#ifndef UINT8_TYPE
# ifdef HAVE_UINT8_T
#  define UINT8_TYPE uint8_t
# else
#  define UINT8_TYPE unsigned char
# endif
#endif
typedef sqlite_int64 i64;          /* 8-byte signed integer */
typedef UINT8_TYPE u8;             /* 1-byte unsigned integer */
#ifdef SQLITE_ASCII
# define sqlite3Isspace(x)   (sqlite3CtypeMap[(unsigned char)(x)]&0x01)
# define sqlite3Isdigit(x)   (sqlite3CtypeMap[(unsigned char)(x)]&0x04)
# define sqlite3Isxdigit(x)  (sqlite3CtypeMap[(unsigned char)(x)]&0x08)
#else
# define sqlite3Isspace(x)   isspace((unsigned char)(x))
# define sqlite3Isdigit(x)   isdigit((unsigned char)(x))
# define sqlite3Isxdigit(x)  isxdigit((unsigned char)(x))
#endif
SQLITE_PRIVATE int sqlite3GetToken(const unsigned char *, int *);
#endif /* SQLITEINT_H */
SQLITE_PRIVATE const unsigned char sqlite3UpperToLower[] = {
#ifdef SQLITE_ASCII
      0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15, 16, 17,
     18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
     36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
     54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 97, 98, 99,100,101,102,103,
    104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,
    122, 91, 92, 93, 94, 95, 96, 97, 98, 99,100,101,102,103,104,105,106,107,
    108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,
    126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,
    144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,
    162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,
    180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,
    198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,
    216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,
    234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,
    252,253,254,255,
#endif
#ifdef SQLITE_EBCDIC
      0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15, /* 0x */
     16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, /* 1x */
     32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, /* 2x */
     48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, /* 3x */
     64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, /* 4x */
     80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, /* 5x */
     96, 97, 98, 99,100,101,102,103,104,105,106,107,108,109,110,111, /* 6x */
    112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127, /* 7x */
    128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143, /* 8x */
    144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159, /* 9x */
    160,161,162,163,164,165,166,167,168,169,170,171,140,141,142,175, /* Ax */
    176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191, /* Bx */
    192,129,130,131,132,133,134,135,136,137,202,203,204,205,206,207, /* Cx */
    208,145,146,147,148,149,150,151,152,153,218,219,220,221,222,223, /* Dx */
    224,225,162,163,164,165,166,167,168,169,234,235,236,237,238,239, /* Ex */
    240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255, /* Fx */
#endif
/* All of the upper-to-lower conversion data is above.  The following
** 18 integers are completely unrelated.  They are appended to the
** sqlite3UpperToLower[] array to avoid UBSAN warnings.  Here's what is
** going on:
**
** The SQL comparison operators (<>, =, >, <=, <, and >=) are implemented
** by invoking sqlite3MemCompare(A,B) which compares values A and B and
** returns negative, zero, or positive if A is less then, equal to, or
** greater than B, respectively.  Then the true false results is found by
** consulting sqlite3aLTb[opcode], sqlite3aEQb[opcode], or
** sqlite3aGTb[opcode] depending on whether the result of compare(A,B)
** is negative, zero, or positive, where opcode is the specific opcode.
** The only works because the comparison opcodes are consecutive and in
** this order: NE EQ GT LE LT GE.  Various assert()s throughout the code
** ensure that is the case.
**
** These elements must be appended to another array.  Otherwise the
** index (here shown as [256-OP_Ne]) would be out-of-bounds and thus
** be undefined behavior.  That's goofy, but the C-standards people thought
** it was a good idea, so here we are.
*/
/* NE  EQ  GT  LE  LT  GE  */
   1,  0,  0,  1,  1,  0,  /* aLTb[]: Use when compare(A,B) less than zero */
   0,  1,  0,  1,  0,  1,  /* aEQb[]: Use when compare(A,B) equals zero */
   1,  0,  1,  0,  0,  1   /* aGTb[]: Use when compare(A,B) greater than zero*/
};
SQLITE_PRIVATE const unsigned char sqlite3CtypeMap[256] = {
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  /* 00..07    ........ */
  0x00, 0x01, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00,  /* 08..0f    ........ */
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  /* 10..17    ........ */
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  /* 18..1f    ........ */
  0x01, 0x00, 0x80, 0x00, 0x40, 0x00, 0x00, 0x80,  /* 20..27     !"#$%&' */
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  /* 28..2f    ()*+,-./ */
  0x0c, 0x0c, 0x0c, 0x0c, 0x0c, 0x0c, 0x0c, 0x0c,  /* 30..37    01234567 */
  0x0c, 0x0c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  /* 38..3f    89:;<=>? */

  0x00, 0x0a, 0x0a, 0x0a, 0x0a, 0x0a, 0x0a, 0x02,  /* 40..47    @ABCDEFG */
  0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,  /* 48..4f    HIJKLMNO */
  0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,  /* 50..57    PQRSTUVW */
  0x02, 0x02, 0x02, 0x80, 0x00, 0x00, 0x00, 0x40,  /* 58..5f    XYZ[\]^_ */
  0x80, 0x2a, 0x2a, 0x2a, 0x2a, 0x2a, 0x2a, 0x22,  /* 60..67    `abcdefg */
  0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22,  /* 68..6f    hijklmno */
  0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22,  /* 70..77    pqrstuvw */
  0x22, 0x22, 0x22, 0x00, 0x00, 0x00, 0x00, 0x00,  /* 78..7f    xyz{|}~. */

  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* 80..87    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* 88..8f    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* 90..97    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* 98..9f    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* a0..a7    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* a8..af    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* b0..b7    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* b8..bf    ........ */

  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* c0..c7    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* c8..cf    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* d0..d7    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* d8..df    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* e0..e7    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* e8..ef    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,  /* f0..f7    ........ */
  0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40   /* f8..ff    ........ */
};
#define YYCODETYPE unsigned short int
#define YYFALLBACK 1
#ifdef YYFALLBACK
static const YYCODETYPE yyFallback[] = {
    0,  /*          $ => nothing */
    0,  /*       SEMI => nothing */
   60,  /*    EXPLAIN => ID */
   60,  /*      QUERY => ID */
   60,  /*       PLAN => ID */
   60,  /*      BEGIN => ID */
    0,  /* TRANSACTION => nothing */
   60,  /*   DEFERRED => ID */
   60,  /*  IMMEDIATE => ID */
   60,  /*  EXCLUSIVE => ID */
    0,  /*     COMMIT => nothing */
   60,  /*        END => ID */
   60,  /*   ROLLBACK => ID */
   60,  /*  SAVEPOINT => ID */
   60,  /*    RELEASE => ID */
    0,  /*         TO => nothing */
    0,  /*      TABLE => nothing */
    0,  /*     CREATE => nothing */
   60,  /*         IF => ID */
    0,  /*        NOT => nothing */
    0,  /*     EXISTS => nothing */
   60,  /*       TEMP => ID */
    0,  /*         LP => nothing */
    0,  /*         RP => nothing */
    0,  /*         AS => nothing */
    0,  /*      COMMA => nothing */
   60,  /*    WITHOUT => ID */
   60,  /*      ABORT => ID */
   60,  /*     ACTION => ID */
   60,  /*      AFTER => ID */
   60,  /*    ANALYZE => ID */
   60,  /*        ASC => ID */
   60,  /*     ATTACH => ID */
   60,  /*     BEFORE => ID */
   60,  /*         BY => ID */
   60,  /*    CASCADE => ID */
   60,  /*       CAST => ID */
   60,  /*   CONFLICT => ID */
   60,  /*   DATABASE => ID */
   60,  /*       DESC => ID */
   60,  /*     DETACH => ID */
   60,  /*       EACH => ID */
   60,  /*       FAIL => ID */
    0,  /*         OR => nothing */
    0,  /*        AND => nothing */
    0,  /*         IS => nothing */
    0,  /*      ISNOT => nothing */
   60,  /*      MATCH => ID */
   60,  /*    LIKE_KW => ID */
    0,  /*    BETWEEN => nothing */
    0,  /*         IN => nothing */
    0,  /*     ISNULL => nothing */
    0,  /*    NOTNULL => nothing */
    0,  /*         NE => nothing */
    0,  /*         EQ => nothing */
    0,  /*         GT => nothing */
    0,  /*         LE => nothing */
    0,  /*         LT => nothing */
    0,  /*         GE => nothing */
    0,  /*     ESCAPE => nothing */
    0,  /*         ID => nothing */
   60,  /*   COLUMNKW => ID */
   60,  /*         DO => ID */
   60,  /*        FOR => ID */
   60,  /*     IGNORE => ID */
   60,  /*  INITIALLY => ID */
   60,  /*    INSTEAD => ID */
   60,  /*         NO => ID */
   60,  /*        KEY => ID */
   60,  /*         OF => ID */
   60,  /*     OFFSET => ID */
   60,  /*     PRAGMA => ID */
   60,  /*      RAISE => ID */
   60,  /*  RECURSIVE => ID */
   60,  /*    REPLACE => ID */
   60,  /*   RESTRICT => ID */
   60,  /*        ROW => ID */
   60,  /*       ROWS => ID */
   60,  /*    TRIGGER => ID */
   60,  /*     VACUUM => ID */
   60,  /*       VIEW => ID */
   60,  /*    VIRTUAL => ID */
   60,  /*       WITH => ID */
   60,  /*      NULLS => ID */
   60,  /*      FIRST => ID */
   60,  /*       LAST => ID */
   60,  /*    CURRENT => ID */
   60,  /*  FOLLOWING => ID */
   60,  /*  PARTITION => ID */
   60,  /*  PRECEDING => ID */
   60,  /*      RANGE => ID */
   60,  /*  UNBOUNDED => ID */
   60,  /*    EXCLUDE => ID */
   60,  /*     GROUPS => ID */
   60,  /*     OTHERS => ID */
   60,  /*       TIES => ID */
   60,  /*  GENERATED => ID */
   60,  /*     ALWAYS => ID */
   60,  /* MATERIALIZED => ID */
   60,  /*    REINDEX => ID */
   60,  /*     RENAME => ID */
   60,  /*   CTIME_KW => ID */
    0,  /*        ANY => nothing */
    0,  /*     BITAND => nothing */
    0,  /*      BITOR => nothing */
    0,  /*     LSHIFT => nothing */
    0,  /*     RSHIFT => nothing */
    0,  /*       PLUS => nothing */
    0,  /*      MINUS => nothing */
    0,  /*       STAR => nothing */
    0,  /*      SLASH => nothing */
    0,  /*        REM => nothing */
    0,  /*     CONCAT => nothing */
    0,  /*        PTR => nothing */
    0,  /*    COLLATE => nothing */
    0,  /*     BITNOT => nothing */
    0,  /*         ON => nothing */
    0,  /*    INDEXED => nothing */
    0,  /*     STRING => nothing */
    0,  /*    JOIN_KW => nothing */
    0,  /* CONSTRAINT => nothing */
    0,  /*    DEFAULT => nothing */
    0,  /*       NULL => nothing */
    0,  /*    PRIMARY => nothing */
    0,  /*     UNIQUE => nothing */
    0,  /*      CHECK => nothing */
    0,  /* REFERENCES => nothing */
    0,  /*   AUTOINCR => nothing */
    0,  /*     INSERT => nothing */
    0,  /*     DELETE => nothing */
    0,  /*     UPDATE => nothing */
    0,  /*        SET => nothing */
    0,  /* DEFERRABLE => nothing */
    0,  /*    FOREIGN => nothing */
    0,  /*       DROP => nothing */
    0,  /*      UNION => nothing */
    0,  /*        ALL => nothing */
    0,  /*     EXCEPT => nothing */
    0,  /*  INTERSECT => nothing */
    0,  /*     SELECT => nothing */
    0,  /*     VALUES => nothing */
    0,  /*   DISTINCT => nothing */
    0,  /*        DOT => nothing */
    0,  /*       FROM => nothing */
    0,  /*       JOIN => nothing */
    0,  /*      USING => nothing */
    0,  /*      ORDER => nothing */
    0,  /*      GROUP => nothing */
    0,  /*     HAVING => nothing */
    0,  /*      LIMIT => nothing */
    0,  /*      WHERE => nothing */
    0,  /*  RETURNING => nothing */
    0,  /*       INTO => nothing */
    0,  /*    NOTHING => nothing */
    0,  /*      FLOAT => nothing */
    0,  /*       BLOB => nothing */
    0,  /*    INTEGER => nothing */
    0,  /*   VARIABLE => nothing */
    0,  /*       CASE => nothing */
    0,  /*       WHEN => nothing */
    0,  /*       THEN => nothing */
    0,  /*       ELSE => nothing */
    0,  /*      INDEX => nothing */
    0,  /*      ALTER => nothing */
    0,  /*        ADD => nothing */
    0,  /*     WINDOW => nothing */
    0,  /*       OVER => nothing */
    0,  /*     FILTER => nothing */
    0,  /*     COLUMN => nothing */
    0,  /* AGG_FUNCTION => nothing */
    0,  /* AGG_COLUMN => nothing */
    0,  /*  TRUEFALSE => nothing */
    0,  /*   FUNCTION => nothing */
    0,  /*      UPLUS => nothing */
    0,  /*     UMINUS => nothing */
    0,  /*      TRUTH => nothing */
    0,  /*   REGISTER => nothing */
    0,  /*     VECTOR => nothing */
    0,  /* SELECT_COLUMN => nothing */
    0,  /* IF_NULL_ROW => nothing */
    0,  /*   ASTERISK => nothing */
    0,  /*       SPAN => nothing */
    0,  /*      ERROR => nothing */
    0,  /*    QNUMBER => nothing */
    0,  /*      SPACE => nothing */
    0,  /*    COMMENT => nothing */
    0,  /*    ILLEGAL => nothing */
};
#endif /* YYFALLBACK */
SQLITE_PRIVATE int sqlite3ParserFallback(int iToken){
#ifdef YYFALLBACK
  assert( iToken<(int)(sizeof(yyFallback)/sizeof(yyFallback[0])) );
  return yyFallback[iToken];
#else
  (void)iToken;
  return 0;
#endif
}
/************** Begin file tokenize.c ****************************************/
/*
** 2001 September 15
**
** The author disclaims copyright to this source code.  In place of
** a legal notice, here is a blessing:
**
**    May you do good and not evil.
**    May you find forgiveness for yourself and forgive others.
**    May you share freely, never taking more than you give.
**
*************************************************************************
** An tokenizer for SQL
**
** This file contains C code that splits an SQL input string up into
** individual tokens and sends those tokens one-by-one over to the
** parser for analysis.
*/
/* #include "sqliteInt.h" */
/* #include <stdlib.h> */

/* Character classes for tokenizing
**
** In the sqlite3GetToken() function, a switch() on aiClass[c] is implemented
** using a lookup table, whereas a switch() directly on c uses a binary search.
** The lookup table is much faster.  To maximize speed, and to ensure that
** a lookup table is used, all of the classes need to be small integers and
** all of them need to be used within the switch.
*/
#define CC_X          0    /* The letter 'x', or start of BLOB literal */
#define CC_KYWD0      1    /* First letter of a keyword */
#define CC_KYWD       2    /* Alphabetics or '_'.  Usable in a keyword */
#define CC_DIGIT      3    /* Digits */
#define CC_DOLLAR     4    /* '$' */
#define CC_VARALPHA   5    /* '@', '#', ':'.  Alphabetic SQL variables */
#define CC_VARNUM     6    /* '?'.  Numeric SQL variables */
#define CC_SPACE      7    /* Space characters */
#define CC_QUOTE      8    /* '"', '\'', or '`'.  String literals, quoted ids */
#define CC_QUOTE2     9    /* '['.   [...] style quoted ids */
#define CC_PIPE      10    /* '|'.   Bitwise OR or concatenate */
#define CC_MINUS     11    /* '-'.  Minus or SQL-style comment */
#define CC_LT        12    /* '<'.  Part of < or <= or <> */
#define CC_GT        13    /* '>'.  Part of > or >= */
#define CC_EQ        14    /* '='.  Part of = or == */
#define CC_BANG      15    /* '!'.  Part of != */
#define CC_SLASH     16    /* '/'.  / or c-style comment */
#define CC_LP        17    /* '(' */
#define CC_RP        18    /* ')' */
#define CC_SEMI      19    /* ';' */
#define CC_PLUS      20    /* '+' */
#define CC_STAR      21    /* '*' */
#define CC_PERCENT   22    /* '%' */
#define CC_COMMA     23    /* ',' */
#define CC_AND       24    /* '&' */
#define CC_TILDA     25    /* '~' */
#define CC_DOT       26    /* '.' */
#define CC_ID        27    /* unicode characters usable in IDs */
#define CC_ILLEGAL   28    /* Illegal character */
#define CC_NUL       29    /* 0x00 */
#define CC_BOM       30    /* First byte of UTF8 BOM:  0xEF 0xBB 0xBF */

static const unsigned char aiClass[] = {
#ifdef SQLITE_ASCII
/*         x0  x1  x2  x3  x4  x5  x6  x7  x8  x9  xa  xb  xc  xd  xe  xf */
/* 0x */   29, 28, 28, 28, 28, 28, 28, 28, 28,  7,  7, 28,  7,  7, 28, 28,
/* 1x */   28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28,
/* 2x */    7, 15,  8,  5,  4, 22, 24,  8, 17, 18, 21, 20, 23, 11, 26, 16,
/* 3x */    3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  5, 19, 12, 14, 13,  6,
/* 4x */    5,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,
/* 5x */    1,  1,  1,  1,  1,  1,  1,  1,  0,  2,  2,  9, 28, 28, 28,  2,
/* 6x */    8,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,
/* 7x */    1,  1,  1,  1,  1,  1,  1,  1,  0,  2,  2, 28, 10, 28, 25, 28,
/* 8x */   27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27,
/* 9x */   27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27,
/* Ax */   27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27,
/* Bx */   27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27,
/* Cx */   27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27,
/* Dx */   27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27,
/* Ex */   27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 30,
/* Fx */   27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27
#endif
#ifdef SQLITE_EBCDIC
/*         x0  x1  x2  x3  x4  x5  x6  x7  x8  x9  xa  xb  xc  xd  xe  xf */
/* 0x */   29, 28, 28, 28, 28,  7, 28, 28, 28, 28, 28, 28,  7,  7, 28, 28,
/* 1x */   28, 28, 28, 28, 28,  7, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28,
/* 2x */   28, 28, 28, 28, 28,  7, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28,
/* 3x */   28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28,
/* 4x */    7, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 26, 12, 17, 20, 10,
/* 5x */   24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 15,  4, 21, 18, 19, 28,
/* 6x */   11, 16, 28, 28, 28, 28, 28, 28, 28, 28, 28, 23, 22,  2, 13,  6,
/* 7x */   28, 28, 28, 28, 28, 28, 28, 28, 28,  8,  5,  5,  5,  8, 14,  8,
/* 8x */   28,  1,  1,  1,  1,  1,  1,  1,  1,  1, 28, 28, 28, 28, 28, 28,
/* 9x */   28,  1,  1,  1,  1,  1,  1,  1,  1,  1, 28, 28, 28, 28, 28, 28,
/* Ax */   28, 25,  1,  1,  1,  1,  1,  0,  2,  2, 28, 28, 28, 28, 28, 28,
/* Bx */   28, 28, 28, 28, 28, 28, 28, 28, 28, 28,  9, 28, 28, 28, 28, 28,
/* Cx */   28,  1,  1,  1,  1,  1,  1,  1,  1,  1, 28, 28, 28, 28, 28, 28,
/* Dx */   28,  1,  1,  1,  1,  1,  1,  1,  1,  1, 28, 28, 28, 28, 28, 28,
/* Ex */   28, 28,  1,  1,  1,  1,  1,  0,  2,  2, 28, 28, 28, 28, 28, 28,
/* Fx */    3,  3,  3,  3,  3,  3,  3,  3,  3,  3, 28, 28, 28, 28, 28, 28,
#endif
};

/*
** The charMap() macro maps alphabetic characters (only) into their
** lower-case ASCII equivalent.  On ASCII machines, this is just
** an upper-to-lower case map.  On EBCDIC machines we also need
** to adjust the encoding.  The mapping is only valid for alphabetics
** which are the only characters for which this feature is used.
**
** Used by keywordhash.h
*/
#ifdef SQLITE_ASCII
# define charMap(X) sqlite3UpperToLower[(unsigned char)X]
#endif
#ifdef SQLITE_EBCDIC
# define charMap(X) ebcdicToAscii[(unsigned char)X]
const unsigned char ebcdicToAscii[] = {
/* 0   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F */
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  /* 0x */
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  /* 1x */
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  /* 2x */
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  /* 3x */
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  /* 4x */
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  /* 5x */
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 95,  0,  0,  /* 6x */
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  /* 7x */
   0, 97, 98, 99,100,101,102,103,104,105,  0,  0,  0,  0,  0,  0,  /* 8x */
   0,106,107,108,109,110,111,112,113,114,  0,  0,  0,  0,  0,  0,  /* 9x */
   0,  0,115,116,117,118,119,120,121,122,  0,  0,  0,  0,  0,  0,  /* Ax */
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  /* Bx */
   0, 97, 98, 99,100,101,102,103,104,105,  0,  0,  0,  0,  0,  0,  /* Cx */
   0,106,107,108,109,110,111,112,113,114,  0,  0,  0,  0,  0,  0,  /* Dx */
   0,  0,115,116,117,118,119,120,121,122,  0,  0,  0,  0,  0,  0,  /* Ex */
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  /* Fx */
};
#endif

/*
** The sqlite3KeywordCode function looks up an identifier to determine if
** it is a keyword.  If it is a keyword, the token code of that keyword is
** returned.  If the input is not a keyword, TK_ID is returned.
**
** The implementation of this routine was generated by a program,
** mkkeywordhash.c, located in the tool subdirectory of the distribution.
** The output of the mkkeywordhash.c program is written into a file
** named keywordhash.h and then included into this source file by
** the #include below.
*/
/************** Include keywordhash.h in the middle of tokenize.c ************/
/************** Begin file keywordhash.h *************************************/
/***** This file contains automatically generated code ******
**
** The code in this file has been automatically generated by
**
**   sqlite/tool/mkkeywordhash.c
**
** The code in this file implements a function that determines whether
** or not a given identifier is really an SQL keyword.  The same thing
** might be implemented more directly using a hand-written hash table.
** But by using this automatically generated code, the size of the code
** is substantially reduced.  This is important for embedded applications
** on platforms with limited memory.
*/
/* Hash score: 231 */
/* zKWText[] encodes 1007 bytes of keyword text in 667 bytes */
/*   REINDEXEDESCAPEACHECKEYBEFOREIGNOREGEXPLAINSTEADDATABASELECT       */
/*   ABLEFTHENDEFERRABLELSEXCLUDELETEMPORARYISNULLSAVEPOINTERSECT       */
/*   IESNOTNULLIKEXCEPTRANSACTIONATURALTERAISEXCLUSIVEXISTS             */
/*   CONSTRAINTOFFSETRIGGERANGENERATEDETACHAVINGLOBEGINNEREFERENCES     */
/*   UNIQUERYWITHOUTERELEASEATTACHBETWEENOTHINGROUPSCASCADEFAULT        */
/*   CASECOLLATECREATECURRENT_DATEIMMEDIATEJOINSERTMATCHPLANALYZE       */
/*   PRAGMATERIALIZEDEFERREDISTINCTUPDATEVALUESVIRTUALWAYSWHENWHERE     */
/*   CURSIVEABORTAFTERENAMEANDROPARTITIONAUTOINCREMENTCASTCOLUMN        */
/*   COMMITCONFLICTCROSSCURRENT_TIMESTAMPRECEDINGFAILASTFILTER          */
/*   EPLACEFIRSTFOLLOWINGFROMFULLIMITIFORDERESTRICTOTHERSOVER           */
/*   ETURNINGRIGHTROLLBACKROWSUNBOUNDEDUNIONUSINGVACUUMVIEWINDOWBY      */
/*   INITIALLYPRIMARY                                                   */
static const char zKWText[666] = {
  'R','E','I','N','D','E','X','E','D','E','S','C','A','P','E','A','C','H',
  'E','C','K','E','Y','B','E','F','O','R','E','I','G','N','O','R','E','G',
  'E','X','P','L','A','I','N','S','T','E','A','D','D','A','T','A','B','A',
  'S','E','L','E','C','T','A','B','L','E','F','T','H','E','N','D','E','F',
  'E','R','R','A','B','L','E','L','S','E','X','C','L','U','D','E','L','E',
  'T','E','M','P','O','R','A','R','Y','I','S','N','U','L','L','S','A','V',
  'E','P','O','I','N','T','E','R','S','E','C','T','I','E','S','N','O','T',
  'N','U','L','L','I','K','E','X','C','E','P','T','R','A','N','S','A','C',
  'T','I','O','N','A','T','U','R','A','L','T','E','R','A','I','S','E','X',
  'C','L','U','S','I','V','E','X','I','S','T','S','C','O','N','S','T','R',
  'A','I','N','T','O','F','F','S','E','T','R','I','G','G','E','R','A','N',
  'G','E','N','E','R','A','T','E','D','E','T','A','C','H','A','V','I','N',
  'G','L','O','B','E','G','I','N','N','E','R','E','F','E','R','E','N','C',
  'E','S','U','N','I','Q','U','E','R','Y','W','I','T','H','O','U','T','E',
  'R','E','L','E','A','S','E','A','T','T','A','C','H','B','E','T','W','E',
  'E','N','O','T','H','I','N','G','R','O','U','P','S','C','A','S','C','A',
  'D','E','F','A','U','L','T','C','A','S','E','C','O','L','L','A','T','E',
  'C','R','E','A','T','E','C','U','R','R','E','N','T','_','D','A','T','E',
  'I','M','M','E','D','I','A','T','E','J','O','I','N','S','E','R','T','M',
  'A','T','C','H','P','L','A','N','A','L','Y','Z','E','P','R','A','G','M',
  'A','T','E','R','I','A','L','I','Z','E','D','E','F','E','R','R','E','D',
  'I','S','T','I','N','C','T','U','P','D','A','T','E','V','A','L','U','E',
  'S','V','I','R','T','U','A','L','W','A','Y','S','W','H','E','N','W','H',
  'E','R','E','C','U','R','S','I','V','E','A','B','O','R','T','A','F','T',
  'E','R','E','N','A','M','E','A','N','D','R','O','P','A','R','T','I','T',
  'I','O','N','A','U','T','O','I','N','C','R','E','M','E','N','T','C','A',
  'S','T','C','O','L','U','M','N','C','O','M','M','I','T','C','O','N','F',
  'L','I','C','T','C','R','O','S','S','C','U','R','R','E','N','T','_','T',
  'I','M','E','S','T','A','M','P','R','E','C','E','D','I','N','G','F','A',
  'I','L','A','S','T','F','I','L','T','E','R','E','P','L','A','C','E','F',
  'I','R','S','T','F','O','L','L','O','W','I','N','G','F','R','O','M','F',
  'U','L','L','I','M','I','T','I','F','O','R','D','E','R','E','S','T','R',
  'I','C','T','O','T','H','E','R','S','O','V','E','R','E','T','U','R','N',
  'I','N','G','R','I','G','H','T','R','O','L','L','B','A','C','K','R','O',
  'W','S','U','N','B','O','U','N','D','E','D','U','N','I','O','N','U','S',
  'I','N','G','V','A','C','U','U','M','V','I','E','W','I','N','D','O','W',
  'B','Y','I','N','I','T','I','A','L','L','Y','P','R','I','M','A','R','Y',
};
/* aKWHash[i] is the hash value for the i-th keyword */
static const unsigned char aKWHash[127] = {
    84,  92, 134,  82, 105,  29,   0,   0,  94,   0,  85,  72,   0,
    53,  35,  86,  15,   0,  42,  97,  54,  89, 135,  19,   0,   0,
   140,   0,  40, 129,   0,  22, 107,   0,   9,   0,   0, 123,  80,
     0,  78,   6,   0,  65, 103, 147,   0, 136, 115,   0,   0,  48,
     0,  90,  24,   0,  17,   0,  27,  70,  23,  26,   5,  60, 142,
   110, 122,   0,  73,  91,  71, 145,  61, 120,  74,   0,  49,   0,
    11,  41,   0, 113,   0,   0,   0, 109,  10, 111, 116, 125,  14,
    50, 124,   0, 100,   0,  18, 121, 144,  56, 130, 139,  88,  83,
    37,  30, 126,   0,   0, 108,  51, 131, 128,   0,  34,   0,   0,
   132,   0,  98,  38,  39,   0,  20,  45, 117,  93,
};
/* aKWNext[] forms the hash collision chain.  If aKWHash[i]==0
** then the i-th keyword has no more hash collisions.  Otherwise,
** the next keyword with the same hash is aKWHash[i]-1. */
static const unsigned char aKWNext[148] = {0,
     0,   0,   0,   0,   4,   0,  43,   0,   0, 106, 114,   0,   0,
     0,   2,   0,   0, 143,   0,   0,   0,  13,   0,   0,   0,   0,
   141,   0,   0, 119,  52,   0,   0, 137,  12,   0,   0,  62,   0,
   138,   0, 133,   0,   0,  36,   0,   0,  28,  77,   0,   0,   0,
     0,  59,   0,  47,   0,   0,   0,   0,   0,   0,   0,   0,   0,
     0,  69,   0,   0,   0,   0,   0, 146,   3,   0,  58,   0,   1,
    75,   0,   0,   0,  31,   0,   0,   0,   0,   0, 127,   0, 104,
     0,  64,  66,  63,   0,   0,   0,   0,   0,  46,   0,  16,   8,
     0,   0,   0,   0,   0,   0,   0,   0,   0,   0,  81, 101,   0,
   112,  21,   7,  67,   0,  79,  96, 118,   0,   0,  68,   0,   0,
    99,  44,   0,  55,   0,  76,   0,  95,  32,  33,  57,  25,   0,
   102,   0,   0,  87,
};
/* aKWLen[i] is the length (in bytes) of the i-th keyword */
static const unsigned char aKWLen[148] = {0,
     7,   7,   5,   4,   6,   4,   5,   3,   6,   7,   3,   6,   6,
     7,   7,   3,   8,   2,   6,   5,   4,   4,   3,  10,   4,   7,
     6,   9,   4,   2,   6,   5,   9,   9,   4,   7,   3,   2,   4,
     4,   6,  11,   6,   2,   7,   5,   5,   9,   6,  10,   4,   6,
     2,   3,   7,   5,   9,   6,   6,   4,   5,   5,  10,   6,   5,
     7,   4,   5,   7,   6,   7,   7,   6,   5,   7,   3,   7,   4,
     7,   6,  12,   9,   4,   6,   5,   4,   7,   6,  12,   8,   8,
     2,   6,   6,   7,   6,   4,   5,   9,   5,   5,   6,   3,   4,
     9,  13,   2,   2,   4,   6,   6,   8,   5,  17,  12,   7,   9,
     4,   4,   6,   7,   5,   9,   4,   4,   5,   2,   5,   8,   6,
     4,   9,   5,   8,   4,   3,   9,   5,   5,   6,   4,   6,   2,
     2,   9,   3,   7,
};
/* aKWOffset[i] is the index into zKWText[] of the start of
** the text for the i-th keyword. */
static const unsigned short int aKWOffset[148] = {0,
     0,   2,   2,   8,   9,  14,  16,  20,  23,  25,  25,  29,  33,
    36,  41,  46,  48,  53,  54,  59,  62,  65,  67,  69,  78,  81,
    86,  90,  90,  94,  99, 101, 105, 111, 119, 123, 123, 123, 126,
   129, 132, 137, 142, 146, 147, 152, 156, 160, 168, 174, 181, 184,
   184, 187, 189, 195, 198, 206, 211, 216, 219, 222, 226, 236, 239,
   244, 244, 248, 252, 259, 265, 271, 277, 277, 283, 284, 288, 295,
   299, 306, 312, 324, 333, 335, 341, 346, 348, 355, 359, 370, 377,
   378, 385, 391, 397, 402, 408, 412, 415, 424, 429, 433, 439, 441,
   444, 453, 455, 457, 466, 470, 476, 482, 490, 495, 495, 495, 511,
   520, 523, 527, 532, 539, 544, 553, 557, 560, 565, 567, 571, 579,
   585, 588, 597, 602, 610, 610, 614, 623, 628, 633, 639, 642, 645,
   648, 650, 655, 659,
};
/* aKWCode[i] is the parser symbol code for the i-th keyword */
static const unsigned char aKWCode[148] = {0,
  TK_REINDEX,    TK_INDEXED,    TK_INDEX,      TK_DESC,       TK_ESCAPE,
  TK_EACH,       TK_CHECK,      TK_KEY,        TK_BEFORE,     TK_FOREIGN,
  TK_FOR,        TK_IGNORE,     TK_LIKE_KW,    TK_EXPLAIN,    TK_INSTEAD,
  TK_ADD,        TK_DATABASE,   TK_AS,         TK_SELECT,     TK_TABLE,
  TK_JOIN_KW,    TK_THEN,       TK_END,        TK_DEFERRABLE, TK_ELSE,
  TK_EXCLUDE,    TK_DELETE,     TK_TEMP,       TK_TEMP,       TK_OR,
  TK_ISNULL,     TK_NULLS,      TK_SAVEPOINT,  TK_INTERSECT,  TK_TIES,
  TK_NOTNULL,    TK_NOT,        TK_NO,         TK_NULL,       TK_LIKE_KW,
  TK_EXCEPT,     TK_TRANSACTION,TK_ACTION,     TK_ON,         TK_JOIN_KW,
  TK_ALTER,      TK_RAISE,      TK_EXCLUSIVE,  TK_EXISTS,     TK_CONSTRAINT,
  TK_INTO,       TK_OFFSET,     TK_OF,         TK_SET,        TK_TRIGGER,
  TK_RANGE,      TK_GENERATED,  TK_DETACH,     TK_HAVING,     TK_LIKE_KW,
  TK_BEGIN,      TK_JOIN_KW,    TK_REFERENCES, TK_UNIQUE,     TK_QUERY,
  TK_WITHOUT,    TK_WITH,       TK_JOIN_KW,    TK_RELEASE,    TK_ATTACH,
  TK_BETWEEN,    TK_NOTHING,    TK_GROUPS,     TK_GROUP,      TK_CASCADE,
  TK_ASC,        TK_DEFAULT,    TK_CASE,       TK_COLLATE,    TK_CREATE,
  TK_CTIME_KW,   TK_IMMEDIATE,  TK_JOIN,       TK_INSERT,     TK_MATCH,
  TK_PLAN,       TK_ANALYZE,    TK_PRAGMA,     TK_MATERIALIZED, TK_DEFERRED,
  TK_DISTINCT,   TK_IS,         TK_UPDATE,     TK_VALUES,     TK_VIRTUAL,
  TK_ALWAYS,     TK_WHEN,       TK_WHERE,      TK_RECURSIVE,  TK_ABORT,
  TK_AFTER,      TK_RENAME,     TK_AND,        TK_DROP,       TK_PARTITION,
  TK_AUTOINCR,   TK_TO,         TK_IN,         TK_CAST,       TK_COLUMNKW,
  TK_COMMIT,     TK_CONFLICT,   TK_JOIN_KW,    TK_CTIME_KW,   TK_CTIME_KW,
  TK_CURRENT,    TK_PRECEDING,  TK_FAIL,       TK_LAST,       TK_FILTER,
  TK_REPLACE,    TK_FIRST,      TK_FOLLOWING,  TK_FROM,       TK_JOIN_KW,
  TK_LIMIT,      TK_IF,         TK_ORDER,      TK_RESTRICT,   TK_OTHERS,
  TK_OVER,       TK_RETURNING,  TK_JOIN_KW,    TK_ROLLBACK,   TK_ROWS,
  TK_ROW,        TK_UNBOUNDED,  TK_UNION,      TK_USING,      TK_VACUUM,
  TK_VIEW,       TK_WINDOW,     TK_DO,         TK_BY,         TK_INITIALLY,
  TK_ALL,        TK_PRIMARY,
};
/* Hash table decoded:
**   0: INSERT
**   1: IS
**   2: ROLLBACK TRIGGER
**   3: IMMEDIATE
**   4: PARTITION
**   5: TEMP
**   6:
**   7:
**   8: VALUES WITHOUT
**   9:
**  10: MATCH
**  11: NOTHING
**  12:
**  13: OF
**  14: TIES IGNORE
**  15: PLAN
**  16: INSTEAD INDEXED
**  17:
**  18: TRANSACTION RIGHT
**  19: WHEN
**  20: SET HAVING
**  21: MATERIALIZED IF
**  22: ROWS
**  23: SELECT
**  24:
**  25:
**  26: VACUUM SAVEPOINT
**  27:
**  28: LIKE UNION VIRTUAL REFERENCES
**  29: RESTRICT
**  30:
**  31: THEN REGEXP
**  32: TO
**  33:
**  34: BEFORE
**  35:
**  36:
**  37: FOLLOWING COLLATE CASCADE
**  38: CREATE
**  39:
**  40: CASE REINDEX
**  41: EACH
**  42:
**  43: QUERY
**  44: AND ADD
**  45: PRIMARY ANALYZE
**  46:
**  47: ROW ASC DETACH
**  48: CURRENT_TIME CURRENT_DATE
**  49:
**  50:
**  51: EXCLUSIVE TEMPORARY
**  52:
**  53: DEFERRED
**  54: DEFERRABLE
**  55:
**  56: DATABASE
**  57:
**  58: DELETE VIEW GENERATED
**  59: ATTACH
**  60: END
**  61: EXCLUDE
**  62: ESCAPE DESC
**  63: GLOB
**  64: WINDOW ELSE
**  65: COLUMN
**  66: FIRST
**  67:
**  68: GROUPS ALL
**  69: DISTINCT DROP KEY
**  70: BETWEEN
**  71: INITIALLY
**  72: BEGIN
**  73: FILTER CHECK ACTION
**  74: GROUP INDEX
**  75:
**  76: EXISTS DEFAULT
**  77:
**  78: FOR CURRENT_TIMESTAMP
**  79: EXCEPT
**  80:
**  81: CROSS
**  82:
**  83:
**  84:
**  85: CAST
**  86: FOREIGN AUTOINCREMENT
**  87: COMMIT
**  88: CURRENT AFTER ALTER
**  89: FULL FAIL CONFLICT
**  90: EXPLAIN
**  91: CONSTRAINT
**  92: FROM ALWAYS
**  93:
**  94: ABORT
**  95:
**  96: AS DO
**  97: REPLACE WITH RELEASE
**  98: BY RENAME
**  99: RANGE RAISE
** 100: OTHERS
** 101: USING NULLS
** 102: PRAGMA
** 103: JOIN ISNULL OFFSET
** 104: NOT
** 105: OR LAST LEFT
** 106: LIMIT
** 107:
** 108:
** 109: IN
** 110: INTO
** 111: OVER RECURSIVE
** 112: ORDER OUTER
** 113:
** 114: INTERSECT UNBOUNDED
** 115:
** 116:
** 117: RETURNING ON
** 118:
** 119: WHERE
** 120: NO INNER
** 121: NULL
** 122:
** 123: TABLE
** 124: NATURAL NOTNULL
** 125: PRECEDING
** 126: UPDATE UNIQUE
*/
/* Check to see if z[0..n-1] is a keyword. If it is, write the
** parser symbol code for that keyword into *pType.  Always
** return the integer n (the length of the token). */
static int keywordCode(const char *z, int n, int *pType){
  int i, j;
  const char *zKW;
  assert( n>=2 );
  i = ((charMap(z[0])*4) ^ (charMap(z[n-1])*3) ^ n*1) % 127;
  for(i=(int)aKWHash[i]; i>0; i=aKWNext[i]){
    if( aKWLen[i]!=n ) continue;
    zKW = &zKWText[aKWOffset[i]];
#ifdef SQLITE_ASCII
    if( (z[0]&~0x20)!=zKW[0] ) continue;
    if( (z[1]&~0x20)!=zKW[1] ) continue;
    j = 2;
    while( j<n && (z[j]&~0x20)==zKW[j] ){ j++; }
#endif
#ifdef SQLITE_EBCDIC
    if( toupper(z[0])!=zKW[0] ) continue;
    if( toupper(z[1])!=zKW[1] ) continue;
    j = 2;
    while( j<n && toupper(z[j])==zKW[j] ){ j++; }
#endif
    if( j<n ) continue;
    testcase( i==1 ); /* REINDEX */
    testcase( i==2 ); /* INDEXED */
    testcase( i==3 ); /* INDEX */
    testcase( i==4 ); /* DESC */
    testcase( i==5 ); /* ESCAPE */
    testcase( i==6 ); /* EACH */
    testcase( i==7 ); /* CHECK */
    testcase( i==8 ); /* KEY */
    testcase( i==9 ); /* BEFORE */
    testcase( i==10 ); /* FOREIGN */
    testcase( i==11 ); /* FOR */
    testcase( i==12 ); /* IGNORE */
    testcase( i==13 ); /* REGEXP */
    testcase( i==14 ); /* EXPLAIN */
    testcase( i==15 ); /* INSTEAD */
    testcase( i==16 ); /* ADD */
    testcase( i==17 ); /* DATABASE */
    testcase( i==18 ); /* AS */
    testcase( i==19 ); /* SELECT */
    testcase( i==20 ); /* TABLE */
    testcase( i==21 ); /* LEFT */
    testcase( i==22 ); /* THEN */
    testcase( i==23 ); /* END */
    testcase( i==24 ); /* DEFERRABLE */
    testcase( i==25 ); /* ELSE */
    testcase( i==26 ); /* EXCLUDE */
    testcase( i==27 ); /* DELETE */
    testcase( i==28 ); /* TEMPORARY */
    testcase( i==29 ); /* TEMP */
    testcase( i==30 ); /* OR */
    testcase( i==31 ); /* ISNULL */
    testcase( i==32 ); /* NULLS */
    testcase( i==33 ); /* SAVEPOINT */
    testcase( i==34 ); /* INTERSECT */
    testcase( i==35 ); /* TIES */
    testcase( i==36 ); /* NOTNULL */
    testcase( i==37 ); /* NOT */
    testcase( i==38 ); /* NO */
    testcase( i==39 ); /* NULL */
    testcase( i==40 ); /* LIKE */
    testcase( i==41 ); /* EXCEPT */
    testcase( i==42 ); /* TRANSACTION */
    testcase( i==43 ); /* ACTION */
    testcase( i==44 ); /* ON */
    testcase( i==45 ); /* NATURAL */
    testcase( i==46 ); /* ALTER */
    testcase( i==47 ); /* RAISE */
    testcase( i==48 ); /* EXCLUSIVE */
    testcase( i==49 ); /* EXISTS */
    testcase( i==50 ); /* CONSTRAINT */
    testcase( i==51 ); /* INTO */
    testcase( i==52 ); /* OFFSET */
    testcase( i==53 ); /* OF */
    testcase( i==54 ); /* SET */
    testcase( i==55 ); /* TRIGGER */
    testcase( i==56 ); /* RANGE */
    testcase( i==57 ); /* GENERATED */
    testcase( i==58 ); /* DETACH */
    testcase( i==59 ); /* HAVING */
    testcase( i==60 ); /* GLOB */
    testcase( i==61 ); /* BEGIN */
    testcase( i==62 ); /* INNER */
    testcase( i==63 ); /* REFERENCES */
    testcase( i==64 ); /* UNIQUE */
    testcase( i==65 ); /* QUERY */
    testcase( i==66 ); /* WITHOUT */
    testcase( i==67 ); /* WITH */
    testcase( i==68 ); /* OUTER */
    testcase( i==69 ); /* RELEASE */
    testcase( i==70 ); /* ATTACH */
    testcase( i==71 ); /* BETWEEN */
    testcase( i==72 ); /* NOTHING */
    testcase( i==73 ); /* GROUPS */
    testcase( i==74 ); /* GROUP */
    testcase( i==75 ); /* CASCADE */
    testcase( i==76 ); /* ASC */
    testcase( i==77 ); /* DEFAULT */
    testcase( i==78 ); /* CASE */
    testcase( i==79 ); /* COLLATE */
    testcase( i==80 ); /* CREATE */
    testcase( i==81 ); /* CURRENT_DATE */
    testcase( i==82 ); /* IMMEDIATE */
    testcase( i==83 ); /* JOIN */
    testcase( i==84 ); /* INSERT */
    testcase( i==85 ); /* MATCH */
    testcase( i==86 ); /* PLAN */
    testcase( i==87 ); /* ANALYZE */
    testcase( i==88 ); /* PRAGMA */
    testcase( i==89 ); /* MATERIALIZED */
    testcase( i==90 ); /* DEFERRED */
    testcase( i==91 ); /* DISTINCT */
    testcase( i==92 ); /* IS */
    testcase( i==93 ); /* UPDATE */
    testcase( i==94 ); /* VALUES */
    testcase( i==95 ); /* VIRTUAL */
    testcase( i==96 ); /* ALWAYS */
    testcase( i==97 ); /* WHEN */
    testcase( i==98 ); /* WHERE */
    testcase( i==99 ); /* RECURSIVE */
    testcase( i==100 ); /* ABORT */
    testcase( i==101 ); /* AFTER */
    testcase( i==102 ); /* RENAME */
    testcase( i==103 ); /* AND */
    testcase( i==104 ); /* DROP */
    testcase( i==105 ); /* PARTITION */
    testcase( i==106 ); /* AUTOINCREMENT */
    testcase( i==107 ); /* TO */
    testcase( i==108 ); /* IN */
    testcase( i==109 ); /* CAST */
    testcase( i==110 ); /* COLUMN */
    testcase( i==111 ); /* COMMIT */
    testcase( i==112 ); /* CONFLICT */
    testcase( i==113 ); /* CROSS */
    testcase( i==114 ); /* CURRENT_TIMESTAMP */
    testcase( i==115 ); /* CURRENT_TIME */
    testcase( i==116 ); /* CURRENT */
    testcase( i==117 ); /* PRECEDING */
    testcase( i==118 ); /* FAIL */
    testcase( i==119 ); /* LAST */
    testcase( i==120 ); /* FILTER */
    testcase( i==121 ); /* REPLACE */
    testcase( i==122 ); /* FIRST */
    testcase( i==123 ); /* FOLLOWING */
    testcase( i==124 ); /* FROM */
    testcase( i==125 ); /* FULL */
    testcase( i==126 ); /* LIMIT */
    testcase( i==127 ); /* IF */
    testcase( i==128 ); /* ORDER */
    testcase( i==129 ); /* RESTRICT */
    testcase( i==130 ); /* OTHERS */
    testcase( i==131 ); /* OVER */
    testcase( i==132 ); /* RETURNING */
    testcase( i==133 ); /* RIGHT */
    testcase( i==134 ); /* ROLLBACK */
    testcase( i==135 ); /* ROWS */
    testcase( i==136 ); /* ROW */
    testcase( i==137 ); /* UNBOUNDED */
    testcase( i==138 ); /* UNION */
    testcase( i==139 ); /* USING */
    testcase( i==140 ); /* VACUUM */
    testcase( i==141 ); /* VIEW */
    testcase( i==142 ); /* WINDOW */
    testcase( i==143 ); /* DO */
    testcase( i==144 ); /* BY */
    testcase( i==145 ); /* INITIALLY */
    testcase( i==146 ); /* ALL */
    testcase( i==147 ); /* PRIMARY */
    *pType = aKWCode[i];
    break;
  }
  return n;
}
SQLITE_PRIVATE int sqlite3KeywordCode(const unsigned char *z, int n){
  int id = TK_ID;
  if( n>=2 ) keywordCode((char*)z, n, &id);
  return id;
}
#define SQLITE_N_KEYWORD 147
SQLITE_API int sqlite3_keyword_name(int i,const char **pzName,int *pnName){
  if( i<0 || i>=SQLITE_N_KEYWORD ) return SQLITE_ERROR;
  i++;
  *pzName = zKWText + aKWOffset[i];
  *pnName = aKWLen[i];
  return SQLITE_OK;
}
SQLITE_API int sqlite3_keyword_count(void){ return SQLITE_N_KEYWORD; }
SQLITE_API int sqlite3_keyword_check(const char *zName, int nName){
  return TK_ID!=sqlite3KeywordCode((const u8*)zName, nName);
}

/************** End of keywordhash.h *****************************************/
/************** Continuing where we left off in tokenize.c *******************/


/*
** If X is a character that can be used in an identifier then
** IdChar(X) will be true.  Otherwise it is false.
**
** For ASCII, any character with the high-order bit set is
** allowed in an identifier.  For 7-bit characters,
** sqlite3IsIdChar[X] must be 1.
**
** For EBCDIC, the rules are more complex but have the same
** end result.
**
** Ticket #1066.  the SQL standard does not allow '$' in the
** middle of identifiers.  But many SQL implementations do.
** SQLite will allow '$' in identifiers for compatibility.
** But the feature is undocumented.
*/
#ifdef SQLITE_ASCII
#define IdChar(C)  ((sqlite3CtypeMap[(unsigned char)C]&0x46)!=0)
#endif
#ifdef SQLITE_EBCDIC
SQLITE_PRIVATE const char sqlite3IsEbcdicIdChar[] = {
/* x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF */
    0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0,  /* 4x */
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0,  /* 5x */
    0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0,  /* 6x */
    0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0,  /* 7x */
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0,  /* 8x */
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0,  /* 9x */
    1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0,  /* Ax */
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  /* Bx */
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1,  /* Cx */
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1,  /* Dx */
    0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1,  /* Ex */
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0,  /* Fx */
};
#define IdChar(C)  (((c=C)>=0x42 && sqlite3IsEbcdicIdChar[c-0x40]))
#endif

/* Make the IdChar function accessible from ctime.c and alter.c */
SQLITE_PRIVATE int sqlite3IsIdChar(u8 c){ return IdChar(c); }

#ifndef SQLITE_OMIT_WINDOWFUNC
/*
** Return the id of the next token in string (*pz). Before returning, set
** (*pz) to point to the byte following the parsed token.
*/
static int getToken(const unsigned char **pz){
  const unsigned char *z = *pz;
  int t;                          /* Token type to return */
  do {
    z += sqlite3GetToken(z, &t);
  }while( t==TK_SPACE );
  if( t==TK_ID
   || t==TK_STRING
   || t==TK_JOIN_KW
   || t==TK_WINDOW
   || t==TK_OVER
   || sqlite3ParserFallback(t)==TK_ID
  ){
    t = TK_ID;
  }
  *pz = z;
  return t;
}

/*
** The following three functions are called immediately after the tokenizer
** reads the keywords WINDOW, OVER and FILTER, respectively, to determine
** whether the token should be treated as a keyword or an SQL identifier.
** This cannot be handled by the usual lemon %fallback method, due to
** the ambiguity in some constructions. e.g.
**
**   SELECT sum(x) OVER ...
**
** In the above, "OVER" might be a keyword, or it might be an alias for the
** sum(x) expression. If a "%fallback ID OVER" directive were added to
** grammar, then SQLite would always treat "OVER" as an alias, making it
** impossible to call a window-function without a FILTER clause.
**
** WINDOW is treated as a keyword if:
**
**   * the following token is an identifier, or a keyword that can fallback
**     to being an identifier, and
**   * the token after than one is TK_AS.
**
** OVER is a keyword if:
**
**   * the previous token was TK_RP, and
**   * the next token is either TK_LP or an identifier.
**
** FILTER is a keyword if:
**
**   * the previous token was TK_RP, and
**   * the next token is TK_LP.
*/
static int analyzeWindowKeyword(const unsigned char *z){
  int t;
  t = getToken(&z);
  if( t!=TK_ID ) return TK_ID;
  t = getToken(&z);
  if( t!=TK_AS ) return TK_ID;
  return TK_WINDOW;
}
static int analyzeOverKeyword(const unsigned char *z, int lastToken){
  if( lastToken==TK_RP ){
    int t = getToken(&z);
    if( t==TK_LP || t==TK_ID ) return TK_OVER;
  }
  return TK_ID;
}
static int analyzeFilterKeyword(const unsigned char *z, int lastToken){
  if( lastToken==TK_RP && getToken(&z)==TK_LP ){
    return TK_FILTER;
  }
  return TK_ID;
}
#endif /* SQLITE_OMIT_WINDOWFUNC */

/*
** Return the length (in bytes) of the token that begins at z[0].
** Store the token type in *tokenType before returning.
*/
SQLITE_PRIVATE int sqlite3GetToken(const unsigned char *z, int *tokenType){
  int i, c;
  switch( aiClass[*z] ){  /* Switch on the character-class of the first byte
                          ** of the token. See the comment on the CC_ defines
                          ** above. */
    case CC_SPACE: {
      testcase( z[0]==' ' );
      testcase( z[0]=='\t' );
      testcase( z[0]=='\n' );
      testcase( z[0]=='\f' );
      testcase( z[0]=='\r' );
      for(i=1; sqlite3Isspace(z[i]); i++){}
      *tokenType = TK_SPACE;
      return i;
    }
    case CC_MINUS: {
      if( z[1]=='-' ){
        for(i=2; (c=z[i])!=0 && c!='\n'; i++){}
        *tokenType = TK_COMMENT;
        return i;
      }else if( z[1]=='>' ){
        *tokenType = TK_PTR;
        return 2 + (z[2]=='>');
      }
      *tokenType = TK_MINUS;
      return 1;
    }
    case CC_LP: {
      *tokenType = TK_LP;
      return 1;
    }
    case CC_RP: {
      *tokenType = TK_RP;
      return 1;
    }
    case CC_SEMI: {
      *tokenType = TK_SEMI;
      return 1;
    }
    case CC_PLUS: {
      *tokenType = TK_PLUS;
      return 1;
    }
    case CC_STAR: {
      *tokenType = TK_STAR;
      return 1;
    }
    case CC_SLASH: {
      if( z[1]!='*' || z[2]==0 ){
        *tokenType = TK_SLASH;
        return 1;
      }
      for(i=3, c=z[2]; (c!='*' || z[i]!='/') && (c=z[i])!=0; i++){}
      if( c ) i++;
      *tokenType = TK_COMMENT;
      return i;
    }
    case CC_PERCENT: {
      *tokenType = TK_REM;
      return 1;
    }
    case CC_EQ: {
      *tokenType = TK_EQ;
      return 1 + (z[1]=='=');
    }
    case CC_LT: {
      if( (c=z[1])=='=' ){
        *tokenType = TK_LE;
        return 2;
      }else if( c=='>' ){
        *tokenType = TK_NE;
        return 2;
      }else if( c=='<' ){
        *tokenType = TK_LSHIFT;
        return 2;
      }else{
        *tokenType = TK_LT;
        return 1;
      }
    }
    case CC_GT: {
      if( (c=z[1])=='=' ){
        *tokenType = TK_GE;
        return 2;
      }else if( c=='>' ){
        *tokenType = TK_RSHIFT;
        return 2;
      }else{
        *tokenType = TK_GT;
        return 1;
      }
    }
    case CC_BANG: {
      if( z[1]!='=' ){
        *tokenType = TK_ILLEGAL;
        return 1;
      }else{
        *tokenType = TK_NE;
        return 2;
      }
    }
    case CC_PIPE: {
      if( z[1]!='|' ){
        *tokenType = TK_BITOR;
        return 1;
      }else{
        *tokenType = TK_CONCAT;
        return 2;
      }
    }
    case CC_COMMA: {
      *tokenType = TK_COMMA;
      return 1;
    }
    case CC_AND: {
      *tokenType = TK_BITAND;
      return 1;
    }
    case CC_TILDA: {
      *tokenType = TK_BITNOT;
      return 1;
    }
    case CC_QUOTE: {
      int delim = z[0];
      testcase( delim=='`' );
      testcase( delim=='\'' );
      testcase( delim=='"' );
      for(i=1; (c=z[i])!=0; i++){
        if( c==delim ){
          if( z[i+1]==delim ){
            i++;
          }else{
            break;
          }
        }
      }
      if( c=='\'' ){
        *tokenType = TK_STRING;
        return i+1;
      }else if( c!=0 ){
        *tokenType = TK_ID;
        return i+1;
      }else{
        *tokenType = TK_ILLEGAL;
        return i;
      }
    }
    case CC_DOT: {
#ifndef SQLITE_OMIT_FLOATING_POINT
      if( !sqlite3Isdigit(z[1]) )
#endif
      {
        *tokenType = TK_DOT;
        return 1;
      }
      /* If the next character is a digit, this is a floating point
      ** number that begins with ".".  Fall thru into the next case */
      /* no break */ deliberate_fall_through
    }
    case CC_DIGIT: {
      testcase( z[0]=='0' );  testcase( z[0]=='1' );  testcase( z[0]=='2' );
      testcase( z[0]=='3' );  testcase( z[0]=='4' );  testcase( z[0]=='5' );
      testcase( z[0]=='6' );  testcase( z[0]=='7' );  testcase( z[0]=='8' );
      testcase( z[0]=='9' );  testcase( z[0]=='.' );
      *tokenType = TK_INTEGER;
#ifndef SQLITE_OMIT_HEX_INTEGER
      if( z[0]=='0' && (z[1]=='x' || z[1]=='X') && sqlite3Isxdigit(z[2]) ){
        for(i=3; 1; i++){
          if( sqlite3Isxdigit(z[i])==0 ){
            if( z[i]==SQLITE_DIGIT_SEPARATOR ){
              *tokenType = TK_QNUMBER;
            }else{
              break;
            }
          }
        }
      }else
#endif
        {
        for(i=0; 1; i++){
          if( sqlite3Isdigit(z[i])==0 ){
            if( z[i]==SQLITE_DIGIT_SEPARATOR ){
              *tokenType = TK_QNUMBER;
            }else{
              break;
            }
          }
        }
#ifndef SQLITE_OMIT_FLOATING_POINT
        if( z[i]=='.' ){
          if( *tokenType==TK_INTEGER ) *tokenType = TK_FLOAT;
          for(i++; 1; i++){
            if( sqlite3Isdigit(z[i])==0 ){
              if( z[i]==SQLITE_DIGIT_SEPARATOR ){
                *tokenType = TK_QNUMBER;
              }else{
                break;
              }
            }
          }
        }
        if( (z[i]=='e' || z[i]=='E') &&
             ( sqlite3Isdigit(z[i+1])
              || ((z[i+1]=='+' || z[i+1]=='-') && sqlite3Isdigit(z[i+2]))
             )
        ){
          if( *tokenType==TK_INTEGER ) *tokenType = TK_FLOAT;
          for(i+=2; 1; i++){
            if( sqlite3Isdigit(z[i])==0 ){
              if( z[i]==SQLITE_DIGIT_SEPARATOR ){
                *tokenType = TK_QNUMBER;
              }else{
                break;
              }
            }
          }
        }
#endif
      }
      while( IdChar(z[i]) ){
        *tokenType = TK_ILLEGAL;
        i++;
      }
      return i;
    }
    case CC_QUOTE2: {
      for(i=1, c=z[0]; c!=']' && (c=z[i])!=0; i++){}
      *tokenType = c==']' ? TK_ID : TK_ILLEGAL;
      return i;
    }
    case CC_VARNUM: {
      *tokenType = TK_VARIABLE;
      for(i=1; sqlite3Isdigit(z[i]); i++){}
      return i;
    }
    case CC_DOLLAR:
    case CC_VARALPHA: {
      int n = 0;
      testcase( z[0]=='$' );  testcase( z[0]=='@' );
      testcase( z[0]==':' );  testcase( z[0]=='#' );
      *tokenType = TK_VARIABLE;
      for(i=1; (c=z[i])!=0; i++){
        if( IdChar(c) ){
          n++;
#ifndef SQLITE_OMIT_TCL_VARIABLE
        }else if( c=='(' && n>0 ){
          do{
            i++;
          }while( (c=z[i])!=0 && !sqlite3Isspace(c) && c!=')' );
          if( c==')' ){
            i++;
          }else{
            *tokenType = TK_ILLEGAL;
          }
          break;
        }else if( c==':' && z[i+1]==':' ){
          i++;
#endif
        }else{
          break;
        }
      }
      if( n==0 ) *tokenType = TK_ILLEGAL;
      return i;
    }
    case CC_KYWD0: {
      if( aiClass[z[1]]>CC_KYWD ){ i = 1;  break; }
      for(i=2; aiClass[z[i]]<=CC_KYWD; i++){}
      if( IdChar(z[i]) ){
        /* This token started out using characters that can appear in keywords,
        ** but z[i] is a character not allowed within keywords, so this must
        ** be an identifier instead */
        i++;
        break;
      }
      *tokenType = TK_ID;
      return keywordCode((char*)z, i, tokenType);
    }
    case CC_X: {
#ifndef SQLITE_OMIT_BLOB_LITERAL
      testcase( z[0]=='x' ); testcase( z[0]=='X' );
      if( z[1]=='\'' ){
        *tokenType = TK_BLOB;
        for(i=2; sqlite3Isxdigit(z[i]); i++){}
        if( z[i]!='\'' || i%2 ){
          *tokenType = TK_ILLEGAL;
          while( z[i] && z[i]!='\'' ){ i++; }
        }
        if( z[i] ) i++;
        return i;
      }
#endif
      /* If it is not a BLOB literal, then it must be an ID, since no
      ** SQL keywords start with the letter 'x'.  Fall through */
      /* no break */ deliberate_fall_through
    }
    case CC_KYWD:
    case CC_ID: {
      i = 1;
      break;
    }
    case CC_BOM: {
      if( z[1]==0xbb && z[2]==0xbf ){
        *tokenType = TK_SPACE;
        return 3;
      }
      i = 1;
      break;
    }
    case CC_NUL: {
      *tokenType = TK_ILLEGAL;
      return 0;
    }
    default: {
      *tokenType = TK_ILLEGAL;
      return 1;
    }
  }
  while( IdChar(z[i]) ){ i++; }
  *tokenType = TK_ID;
  return i;
}

/*
** Run the parser on the given SQL string.
*/
#endif /* SQLITE_AMALGAMATION */
