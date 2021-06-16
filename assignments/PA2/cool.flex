/*
 *  The scanner definition for COOL.
 */

/*
 *  Stuff enclosed in %{ %} in the first section is copied verbatim to the
 *  output, so headers and global definitions are placed here to be visible
 * to the code in the file.  Don't remove anything that was here initially
 */
%{
#include <cool-parse.h>
#include <stringtab.h>
#include <utilities.h>
#include <string>

/* The compiler assumes these identifiers. */
#define yylval cool_yylval
#define yylex  cool_yylex

/* Max size of string constants */
#define MAX_STR_CONST 1025
#define YY_NO_UNPUT   /* keep g++ happy */

extern FILE *fin; /* we read from this file */

/* define YY_INPUT so we read from the FILE fin:
 * This change makes it possible to use this scanner in
 * the Cool compiler.
 */
#undef YY_INPUT
#define YY_INPUT(buf,result,max_size) \
	if ( (result = fread( (char*)buf, sizeof(char), max_size, fin)) < 0) \
		YY_FATAL_ERROR( "read() in flex scanner failed");

char string_buf[MAX_STR_CONST]; /* to assemble string constants */
char *string_buf_ptr;

extern int curr_lineno;
extern int verbose_flag;

extern YYSTYPE cool_yylval;

/*
 *  Add Your own definitions here
 */
using std::string;
static int comment_depth = 0;
static int should_exit = 0;
static string str;
static const int max_str_len = 1024;
%}

/*
 * Define names for regular expressions here.
 */

CLASS           (?i:class)
ELSE            (?i:else)
FI              (?i:fi)
IF              (?i:if)
IN              (?i:in)
INHERITS        (?i:inherits)
LET             (?i:let)
LOOP            (?i:loop)
POOL            (?i:pool)
THEN            (?i:then)
WHILE           (?i:while)
CASE            (?i:case)
ESAC            (?i:esac)
OF              (?i:of)
DARROW          =>
NEW             (?i:new)
ISVOID          (?i:isvoid)
STR_FOOTER      \"
STR_CONTENT     [^"]*
INT_CONST       [0-9]+
BOOL_CONST      t(?i:rue)|f(?i:alse)
TYPEID          [A-Z][a-zA-Z0-9_]*
OBJECTID        [a-z][a-zA-Z0-9_]*
ASSIGN          "<-"
NOT             (?i:not)
LE              "<="
COMMENT_BEGIN   "(*"
COMMENT_CONTENT .|\n
COMMENT_END     "*)"
SINGLE_CHAR     "{"|"}"|"("|")"|";"|","|":"|"+"|"-"|"*"|"/"|"~"|"="|"."|"<"|"@"
DASH_COMMENT    "--"
WHITESPACE      [ \t\r\n\v\f]+
ERROR_CHAR      .
%x      COMMENT STRING STR_ERROR
%%
    if (should_exit) {
        should_exit = 0;
        return 0;
    }
 /*
  *  Nested comments
  */


 /*
  *  The multiple-character operators.
  */
<INITIAL>{CLASS}         { return (CLASS); }
<INITIAL>{ELSE}          { return (ELSE); }
<INITIAL>{FI}            { return (FI); }
<INITIAL>{IF}            { return (IF); }
<INITIAL>{IN}            { return (IN); }
<INITIAL>{INHERITS}      { return (INHERITS); }
<INITIAL>{LET}           { return (LET); }
<INITIAL>{LOOP}          { return (LOOP); }
<INITIAL>{POOL}          { return (POOL); }
<INITIAL>{THEN}          { return (THEN); }
<INITIAL>{WHILE}         { return (WHILE); }
<INITIAL>{CASE}          { return (CASE); }
<INITIAL>{ESAC}          { return (ESAC); }
<INITIAL>{NOT}           { return (NOT); }
<INITIAL>{OF}            { return (OF); }
<INITIAL>{DARROW}		{ return (DARROW); }
<INITIAL>{NEW}           { return (NEW); }
<INITIAL>{ISVOID}        { return (ISVOID); }
<INITIAL>{STR_FOOTER}   { BEGIN(STRING); }
<STRING>{STR_FOOTER} {
    // all done
    cool_yylval.symbol = stringtable.add_string(&str[0]);
    str.clear();
    BEGIN INITIAL;
    return (STR_CONST);
}
<STR_ERROR>{STR_FOOTER} {
    str.clear();
    BEGIN INITIAL;
}

<STRING>\n  {
    // a lonely \n :)
    curr_lineno++;
    cool_yylval.error_msg = "Unterminated string constant";
    str.clear();
    BEGIN INITIAL;
    return (ERROR);
}
<STR_ERROR>\n {
    curr_lineno++;
    str.clear();
    BEGIN INITIAL;
};
<STR_ERROR>. {}
<STRING>\\(.|\n) {
    switch(yytext[1]) {
        case 'b':str += '\b';break;
        case 't':str += '\t';break;
        case 'n':str += '\n';break;
        case 'f':str += '\f';break;
        case '\n':{
            str += '\n';
            curr_lineno++;
            break;
        }
        case '\0':{
            cool_yylval.error_msg = "String contains null character";
            BEGIN STR_ERROR;
            return (ERROR);
        }
        default: str += yytext[1];break;
    }
    if (str.length() > max_str_len) {
        BEGIN STR_ERROR;
        cool_yylval.error_msg = "String constant too long";
        return (ERROR);
    }
}
<STRING>\0 {
    cool_yylval.error_msg = "String contains null character";
    BEGIN STR_ERROR;
    return (ERROR);
}
<STRING>[^\\\n\"\0]+	  {
    for (int i = 0; i < yyleng; i++) {
        str += yytext[i];
    }
    if (str.length() > max_str_len) {
        BEGIN STR_ERROR;
        cool_yylval.error_msg = "String constant too long";
        return (ERROR);
    }
}

<STRING><<EOF>>     {
    // turn off the STRING
    // or there will be infinite loop
    cool_yylval.error_msg = "EOF in string constant";
    should_exit = 1;
    return (ERROR);
}

<INITIAL>{INT_CONST}     {
    cool_yylval.symbol = inttable.add_string(yytext);
    return (INT_CONST);
}
<INITIAL>{BOOL_CONST}    {
    for (unsigned int i = 0; i < yyleng; i++) {
        yytext[i] = tolower(yytext[i]);
    }
    if (strcmp(yytext,"true") == 0) {
        cool_yylval.boolean = true;
    } else {
        cool_yylval.boolean = false;
    }
    return (BOOL_CONST);
}
<INITIAL>{TYPEID}    {
    cool_yylval.symbol = stringtable.add_string(yytext);
    return (TYPEID);
}
<INITIAL>{OBJECTID}    {
    cool_yylval.symbol = stringtable.add_string(yytext);
    return (OBJECTID);
}
<INITIAL>{ASSIGN}    {
    return (ASSIGN);
}
<INITIAL>{LE}    {
    return (LE);
}

<COMMENT>{COMMENT_BEGIN} { comment_depth++;BEGIN COMMENT; }
<INITIAL>{COMMENT_BEGIN} { comment_depth++;BEGIN COMMENT; }
<COMMENT>{COMMENT_CONTENT}   {
    if (yytext[0] == '\n') {
        curr_lineno++;
    }
}
<COMMENT>{COMMENT_END}  {
    comment_depth--;
    if (comment_depth == 0) {
    BEGIN INITIAL;
    }
}
<INITIAL>{COMMENT_END}  {
    cool_yylval.error_msg = "Unmatched *)";
    return (ERROR);
}

<COMMENT><<EOF>>    {
    // turn off the COMMENT
    // or there will be infinite loop
    cool_yylval.error_msg = "EOF in comment";
    should_exit = 1;
    return (ERROR);
}

<INITIAL>{SINGLE_CHAR}   {
    return (int)yytext[0];
}

<INITIAL>{DASH_COMMENT}.*  {}
<INITIAL>{WHITESPACE}    {
    for (int i = 0; i < yyleng; i++) {
        if (yytext[i] == '\n') {
            curr_lineno++;
        }
    }
}
<INITIAL>{ERROR_CHAR}    {
    cool_yylval.error_msg = yytext;
    return (ERROR);
}

 /*
 * Keywords are case-insensitive except for the values true and false,
 * which must begin with a lower-case letter.
 */


 /*
  *  String constants (C syntax)
  *  Escape sequence \c is accepted for all characters c. Except for
  *  \n \t \b \f, the result is c.
  *
  */


%%
