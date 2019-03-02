%{
/***** modex: gram.y *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/* grammar based on "C - A Reference Manual" (4th Ed.),  */
/* by Samuel P Harbison, and Guy L Steele Jr.            */

//#define	alloca	e_malloc
#define	YYERROR_VERBOSE

#include <setjmp.h>

#include "lexer.h"
#include "tree.h"
#include "symtab.h"
#include "globals.h"

#define YYDEBUG 1

static int debug = 0;
#if 0
int  yydebug = 1;
#endif

int structfieldflag;

extern int errno, err_cnt, Verbose;
extern char *progname;
extern int yylex(YYSTYPE *lvalp);
extern void name_scope(context_t *, char *, int);
extern void add_constant(char *, int);
extern char *toksym(int tok, int white);

static void insert_decl     (leafnode *, treenode *, treenode *);
static void insert_typedef  (leafnode *, treenode *, treenode *);
static void insert_component(leafnode *, treenode *, treenode *);
static void add_params_to_symtab(treenode *);
void *e_malloc(uint);

%}

/* The next line makes the parser re-entrant. */
%define api.pure full
// %pure_parser

%start program

%token <leaf> IDENT STRING FIELD_NAME TYPEDEF_NAME TAG
%token <leaf> CHAR_CONST
%token <leaf> INUM
%token <leaf> RNUM
%token <leaf> COMMENT
%token <leaf> PP_LINE PP_INCLUDE PP_DEFINE PP_UNDEF PP_ERROR
%token <leaf> PP_IF PP_IFDEF PP_IFNDEF PP_ELSE PP_ELIF PP_ENDIF
%token <leaf> PP_IDENT PP_PRAGMA
%token <tok>  INVALID

/* reserved words */
%token <node> AUTO BREAK CASE CHAR CONST CONT DEFLT DO DOUBLE ELSE ENUM EXTRN
%token <ifn>  IF
%token <forn> FOR
%token <node> FLOAT GOTO INT LONG REGISTR RETURN SHORT SGNED
%token <node> STATIC STRUCT SWITCH TYPEDEF UNION UNSGNED VOID VOLATILE WHILE

%token <node> PLUS_EQ MINUS_EQ STAR_EQ DIV_EQ MOD_EQ
%token <node> B_NOT_EQ B_AND_EQ B_OR_EQ B_XOR_EQ
%token <node> L_SHIFT_EQ R_SHIFT_EQ
%token <node> EQUAL LESS_EQ GRTR_EQ NOT_EQ 
 
%token <node> RPAREN RBRCKT LBRACE RBRACE
%token <node> SEMICOLON COMMA ELLIPSIS
	
%token <node> LB_SIGN DOUB_LB_SIGN
%token <node> BACKQUOTE AT DOLLAR
%token <node> CPP_INCLUDE CPP_DEFINE CPP_LINE

/* precedence rules to solve dangling else s/r conflict */
%nonassoc IF
%nonassoc ELSE

/* operator tokens and their precedences. */
%left         COMMA_OP
%right <node> EQ ASSIGN
%right <node> QUESTMARK COLON COMMA_SEP
%left  <node> OR
%left  <node> AND
%left  <node> B_OR
%left  <node> B_XOR
%left  <node> B_AND
%left  <node> COMP_EQ
%left  <node> COMP_ARITH LESS GRTR
%left  <node> L_SHIFT R_SHIFT
%left  <node> PLUS MINUS
%left  <node> STAR DIV MOD
%right        CAST
%right <node> UNARY NOT B_NOT SIZEOF ALIGNOF INCR DECR  
%left         HYPERUNARY
%left  <node> ARROW DOT LPAREN LBRCKT

%type  <node> declaration decl_specs opt_decl_specs
%type  <node> storage_class type_spec type_qual
%type  <node> opt_init_decl_list init_decl_list init_decl
%type  <node> declarator opt_declarator
%type  <node> direct_declarator opt_comma
%type  <node> pointer pointer_start
%type  <node> simple_decl type_qual_list opt_type_qual_list
%type  <node> decl_list opt_decl_list
%type  <leaf> constant strings
%type  <node> comp_decl_specs opt_comp_decl_specs

%type  <node> param_list param_decl
%type  <node> opt_param_type_list param_type_list
%type  <node> ident_list
%type  <leaf> ident
%type  <node> field_ident
%type  <node> abs_decl
%type  <node> direct_abs_decl

%type  <node> array_decl opt_const_expr const_expr expr
%type  <node> comma_expr assign_expr
%type  <node> prim_expr paren_expr postfix_expr
%type  <node> subscript_expr comp_select_expr postinc_expr postdec_expr
%type  <node> func_call opt_expr opt_expr_list expr_list

%type  <node> top_level_decl func_def func_spec cmpnd_stemnt
%type  <node> stemnt_list opt_stemnt_list stemnt
%type  <node> expr_stemnt labeled_stemnt cond_stemnt
%type  <node> opt_comment
%type  <node> iter_stemnt switch_stemnt break_stemnt continue_stemnt
%type  <node> return_stemnt goto_stemnt null_stemnt
%type  <node> do_stemnt while_stemnt for_stemnt
%type  <node> cond_expr if_stemnt if_else_stemnt

%type  <node> log_or_expr log_and_expr log_neg_expr
%type  <node> bitwise_or_expr bitwise_and_expr bitwise_neg_expr
%type  <node> bitwise_xor_expr cast_expr equality_expr
%type  <node> relational_expr shift_expr additive_expr mult_expr
%type  <node> unary_expr unary_minus_expr unary_plus_expr
%type  <node> sizeof_expr alignof_expr addr_expr indirection_expr
%type  <node> preinc_expr predec_expr 

%type  <node> direct_comp_select indirect_comp_select

%type  <node> add_op mult_op equality_op relation_op shift_op assign_op
%type  <node> label named_label case_label deflt_label

%type  <node> type_name typedef_name typename_as_ident
%type  <node> enum_type_spec struct_type_spec union_type_spec

%type  <node> tag opt_tag
%type  <node> opt_trailing_comma
%type  <node> enum_type_define enum_type_ref enum_def_list
%type  <node> enum_const_def enum_constant
%type  <node> struct_type_define struct_type_ref field_list
%type  <node> union_type_define union_type_ref

%type  <node> comp_decl comp_decl_list comp_declarator
%type  <node> simple_comp bit_field width

%type  <node> initializer_list initializer

%type  <node> program trans_unit

%%
program:  /* empty */ 
	{	if (err_cnt == 0)
			fprintf(stderr, "Empty source file?\n");
		Parse_TOS->parse_tree= (treenode *) NULL;
		$$ = (treenode *) NULL;
	}
	| trans_unit
	{
		if (err_cnt)
			fprintf(stderr,"%d errors\n",err_cnt);
		Parse_TOS->parse_tree = $$;
	}
	| error
	{
		fputs("Aborting\n",stderr);
		Parse_TOS->parse_tree= (treenode *) NULL;
		YYABORT;
	}

trans_unit: top_level_decl
	| trans_unit top_level_decl
	{	if ($2)
		{	treenode *tmp_node = make_node(TN_TRANS_LIST);
			tmp_node->lnode = $1;
			tmp_node->rnode = $2;
			$$ = tmp_node;
		} else
		{	$$ = $1;
		}
	}
	;

top_level_decl: declaration
	{	exit_scopes(ParseStack->contxt, FILE_SCOPE);
	}
	| func_def
	{	exit_scopes(ParseStack->contxt, FILE_SCOPE);
	}
	| SEMICOLON	/* gjh */
/*
	| error SEMICOLON
	{	free_tree($2);
		$$ = (treenode *) NULL;
	}
*/
	| error RBRACE
	{	free_tree($2);
		$$ = (treenode *) NULL;
	}

func_def: func_spec cmpnd_stemnt
	{	leafnode *lm, *rm = (leafnode *) 0;
		for_node *tmpnode = (for_node *) $1;
		symentry_t *nmtbl;
		int scoped = EXTERN_SCOPE;

		tmpnode->stemnt = $2;

		if (ParseStack->contxt)
		{	rm = find_func_name($$);
			if (rm)	/* if null, an error msg was printed */
			{	lm = leftmost($$);
				if (lm && (lm->hdr.tok == STATIC))
					scoped = FILE_SCOPE;

				nmtbl = mk_funcdef(rm->data.sval, $$);

				nmtbl = symtab_insert_at(ParseStack->contxt->syms, nmtbl, scoped);

				rm->syment = nmtbl;	/* can replace prototype entry for real one */
				rm->syment->nes = ParseStack->contxt->syms->current;
				rm->syment->decl_level = ParseStack->contxt->syms->clevel;

				if (!nmtbl)
					yyerr("Duplicate function");

				name_scope(ParseStack->contxt,
					rm->data.sval->str,	/* fct name */
					TN_FUNC_DEF);
		}	}
		exit_scope(ParseStack->contxt);
	}

func_spec:  decl_specs declarator opt_decl_list
	{
            for_node *tmp_node = make_for(TN_FUNC_DEF);

            tmp_node->init = $1;
            tmp_node->test = $2;
            tmp_node->incr = $3;
            add_params_to_symtab($2);
            $$ = (treenode *) tmp_node;
	}
	|  declarator opt_decl_list
	{
            /* return type defaults to int */
            for_node *tmp_node = make_for(TN_FUNC_DEF);

            tmp_node->init = (treenode *) NULL;
            tmp_node->test = $1;
            tmp_node->incr = $2;
            add_params_to_symtab($1);
            $$ = (treenode *) tmp_node;
	}

opt_decl_list:  /* Nothing */
	{
            $$ = (treenode *) NULL;
	}
	|  decl_list
        ;

decl_list:  declaration
	|  decl_list declaration
	{
            treenode *tmp_node = make_node(TN_DECL_LIST);
            tmp_node->lnode = $1;
            tmp_node->rnode = $2;
            $$ = tmp_node;
	}

cmpnd_stemnt:	LBRACE
	{
            enter_scope(ParseStack->contxt);
	}
		opt_decl_list opt_stemnt_list RBRACE
	{
            $1->hdr.type = TN_BLOCK;
            $1->lnode = $3;
            $1->rnode = $4;
            free_tree($5);
            exit_scope(ParseStack->contxt);
	}
	|  error RBRACE
	{
            $$ = (treenode *) NULL;
            free_tree($2);
	}

opt_stemnt_list:
	{
            $$ = (treenode *) NULL;
	}
	|  stemnt_list
        ;

stemnt_list: stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT_LIST);
            tmp_node->lnode = $1;
            tmp_node->rnode = NULL;
            $$ = tmp_node;
	}
	| stemnt_list stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT_LIST);
            tmp_node->lnode = $1;
            tmp_node->rnode = $2;
            $$ = tmp_node;
	}

stemnt:  declaration
	| expr_stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = $1;
            $$ = tmp_node;
	}
	|  labeled_stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = $1;
            $$ = tmp_node;
	}
	|  cmpnd_stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = $1;
            $$ = tmp_node;
	}
	|  cond_stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = $1;
            $$ = tmp_node;
	}
	|  iter_stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = $1;
            $$ = tmp_node;
	}
	|  switch_stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = $1;
            $$ = tmp_node;
	}
	|  break_stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = $1;
            $$ = tmp_node;
	}
	|  continue_stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = $1;
            $$ = tmp_node;
	}
	|  return_stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = $1;
            $$ = tmp_node;
	}
	|  goto_stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = $1;
            $$ = tmp_node;
	}
	|  null_stemnt
	{
            treenode *tmp_node = make_node(TN_STEMNT);
            tmp_node->rnode = $1;
            $$ = tmp_node;
	}
	|  error SEMICOLON
	{
            $$ = (treenode *) NULL;
            free_tree($2);
	}

expr_stemnt:  expr SEMICOLON opt_comment
	{
            free_tree($2);
	}

labeled_stemnt: label COLON stemnt
	{
            $2->hdr.type = TN_LABEL;
            $2->lnode = (treenode *) $1;
            $2->rnode = $3;
            $$ = $2;
	}
	;

cond_stemnt:  if_stemnt
	|  if_else_stemnt
        ;

iter_stemnt:  do_stemnt
	|  while_stemnt
	|  for_stemnt
        ;

switch_stemnt: SWITCH LPAREN expr RPAREN stemnt
	{
            $1->hdr.type = TN_SWITCH;
            $1->lnode = (treenode *) $3;
            $1->rnode = (treenode *) $5;
            free_tree($2);
            free_tree($4);
	}

break_stemnt: BREAK SEMICOLON
	{
            $1->hdr.type = TN_JUMP;
            free_tree($2);
	}

continue_stemnt: CONT SEMICOLON
	{
            $1->hdr.type = TN_JUMP;
            free_tree($2);
	}

return_stemnt:  RETURN opt_expr SEMICOLON
	{
            $1->hdr.type = TN_JUMP;
            $1->lnode = $2;
            free_tree($3);
	}

goto_stemnt:  GOTO ident SEMICOLON
	{
		if (ParseStack->contxt)
		{	symentry_t *nmtbl, *y;
			nmtbl = mk_label($2->data.sval, $$);

			y = symtab_insert_at(ParseStack->contxt->labels,
					nmtbl, FUNCTION_SCOPE);
			if (!y)
				printf("not really a Duplicate label\n");

			$2->syment = y;
		}

		if (0) printf("goto %s, $2=%s (%p)\n",
			$2->data.sval->str,
			name_of_node($2->hdr.type),
			$2->syment);


            $1->hdr.type = TN_JUMP;
            $1->lnode = (treenode *) $2;
            free_tree($3);
	}

null_stemnt:  SEMICOLON
	{
            $$ = (treenode *) NULL;
            free_tree($1);
	}

if_stemnt:  IF LPAREN expr RPAREN stemnt    %prec IF
	{
            $1->hdr.type = TN_IF;
            $1->cond = $3;
            $1->then_n = $5;
            $$ = (treenode *) $1;
            free_tree($2);
            free_tree($4);
	}

if_else_stemnt:  IF LPAREN expr RPAREN stemnt ELSE stemnt
	{
            $1->hdr.type = TN_IF;
            $1->cond = $3;
            $1->then_n = $5;
            $1->else_n = $7;
            $$ = (treenode *) $1;
            free_tree($2);
            free_tree($4);
            free_tree($6);
	}

do_stemnt:  DO stemnt WHILE LPAREN expr RPAREN SEMICOLON
	{
            $1->hdr.type = TN_DOWHILE;
            $1->lnode = $5;
            $1->rnode = $2;
            free_tree($3);
            free_tree($4);
            free_tree($6);
            free_tree($7);
	}

while_stemnt:  WHILE LPAREN expr RPAREN stemnt
	{
            $1->hdr.type = TN_WHILE;
            $1->lnode = $3;
            $1->rnode = $5;
            free_tree($2);
            free_tree($4);
	}

for_stemnt: FOR LPAREN opt_expr SEMICOLON
            opt_expr SEMICOLON opt_expr RPAREN stemnt
	{
            $1->hdr.type = TN_FOR;
            $1->init = $3;
            $1->test = $5;
            $1->incr = $7;
            $1->stemnt = $9;
            free_tree($2);
            free_tree($4);
            free_tree($6);
            free_tree($8);
	}

label:  named_label
	|  case_label
	|  deflt_label
        ;

cond_expr:  log_or_expr
	|  log_or_expr QUESTMARK expr COLON cond_expr
	{
            if_node *tmpnode = make_if(TN_COND_EXPR);
		tmpnode->hdr.tok = QUESTMARK;
            tmpnode->cond = $1;
            tmpnode->then_n = $3;
            tmpnode->else_n = $5;
            $$ = (treenode *) tmpnode;
            free_tree($2);
            free_tree($4);
	}

log_or_expr:  log_and_expr
	|  log_or_expr OR log_and_expr
	{
            $2->hdr.type = TN_EXPR;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

log_and_expr:  bitwise_or_expr
	|  log_and_expr AND bitwise_or_expr
	{
            $2->hdr.type = TN_EXPR;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

log_neg_expr:  NOT cast_expr
	{
            $1->hdr.type = TN_EXPR;
            $1->rnode = $2;
	}

bitwise_or_expr:  bitwise_xor_expr
	|  bitwise_or_expr B_OR bitwise_xor_expr
	{
            $2->hdr.type = TN_EXPR;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

bitwise_xor_expr:  bitwise_and_expr
	|  bitwise_xor_expr B_XOR bitwise_and_expr
	{
            $2->hdr.type = TN_EXPR;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

bitwise_and_expr:  equality_expr
	|  bitwise_and_expr B_AND equality_expr
	{
            $2->hdr.type = TN_EXPR;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

bitwise_neg_expr:  B_NOT cast_expr
	{
            $1->hdr.type = TN_EXPR;
            $1->rnode = $2;
	}

cast_expr:  unary_expr
	|  LPAREN type_name RPAREN cast_expr     %prec CAST
	{
            $1->hdr.type = TN_CAST;
            $1->lnode = $2;
            $1->rnode = $4;
            free_tree($3);
	}

equality_expr:  relational_expr
	|  equality_expr equality_op relational_expr
	{
            $2->hdr.type = TN_EXPR;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

relational_expr:  shift_expr
	|  relational_expr relation_op shift_expr 
	{
            $2->hdr.type = TN_EXPR;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

shift_expr:  additive_expr
	|  shift_expr shift_op additive_expr
	{
            $2->hdr.type = TN_EXPR;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

additive_expr:  mult_expr
	|  additive_expr add_op mult_expr
	{
            $2->hdr.type = TN_EXPR;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

mult_expr:  cast_expr
	|  mult_expr mult_op cast_expr
	{
            $2->hdr.type = TN_EXPR;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

unary_expr:  postfix_expr
	|  sizeof_expr
	|  alignof_expr
	|  unary_minus_expr
	|  unary_plus_expr
	|  log_neg_expr
	|  bitwise_neg_expr
	|  addr_expr
	|  indirection_expr
	|  preinc_expr
	|  predec_expr
        ;

sizeof_expr:  SIZEOF LPAREN type_name RPAREN   %prec HYPERUNARY
	{
            $1->hdr.type = TN_EXPR;
            $1->rnode = $3;
            free_tree($2);
            free_tree($4);
	}
	|  SIZEOF unary_expr 
	{
            $1->hdr.type = TN_EXPR;
            $1->rnode = $2;
	}

alignof_expr:  ALIGNOF LPAREN type_name RPAREN   %prec HYPERUNARY
	{
            $1->hdr.type = TN_EXPR;
            $1->rnode = $3;
            free_tree($2);
            free_tree($4);
	}
	|  ALIGNOF unary_expr 
	{
            $1->hdr.type = TN_EXPR;
            $1->rnode = $2;
	}

unary_minus_expr:  MINUS cast_expr    %prec UNARY
	{
            $1->hdr.type = TN_EXPR;
            $1->rnode = $2;
	}

unary_plus_expr:  PLUS cast_expr      %prec UNARY
	{
            /* Unary plus is an ISO addition (for symmetry) - ignore it */
            $$ = $2;
            free_tree($1);
	}

addr_expr:  B_AND cast_expr           %prec UNARY
	{
            $1->hdr.type = TN_EXPR;
            $1->rnode = $2;
	}

indirection_expr:  STAR cast_expr     %prec UNARY
	{
            $1->hdr.type = TN_DEREF;
            $1->rnode = $2;
	}

preinc_expr:  INCR unary_expr
	{
            $1->hdr.type = TN_EXPR;
            $1->rnode = $2;
	}

predec_expr:  DECR unary_expr
	{
            $1->hdr.type = TN_EXPR;
            $1->rnode = $2;
	}

assign_expr:  cond_expr
	|  unary_expr assign_op assign_expr
	{
            $2->hdr.type = TN_ASSIGN;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

opt_const_expr:    /* Nothing */
	{
            $$ = (treenode *) NULL;
	}
	| const_expr
        ;

const_expr: expr
        ;

opt_expr:  /* Nothing */
	{
           $$ = (treenode *) NULL;
	}
	|  expr
        ;

expr:    comma_expr
        ;

comma_expr:  assign_expr
	|  comma_expr COMMA assign_expr    %prec COMMA_OP
	{
           $2->hdr.type = TN_EXPR;
           $2->lnode = $1;
           $2->rnode = $3;
           $$ = $2;
	}

prim_expr:  ident
	{
           $$ = (treenode *) $1;
	}
	|  paren_expr
	|  constant
	{
           $$ = (treenode *) $1;
	}

paren_expr: LPAREN expr RPAREN
	{
           $$ = $2;
           free_tree($1);
           free_tree($3);
	}
	| LPAREN error RPAREN
	{
           $$ = (treenode *) NULL;
           free_tree($1);
           free_tree($3);
	}

postfix_expr: prim_expr
	| subscript_expr
	| comp_select_expr
	| func_call
	| postinc_expr
	| postdec_expr
        ;

subscript_expr: postfix_expr LBRCKT expr RBRCKT
	{
            $2->hdr.type = TN_INDEX;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
            free_tree($4);
	}

comp_select_expr: direct_comp_select
	| indirect_comp_select
        ;

postinc_expr: postfix_expr INCR
	{
            $2->hdr.type = TN_EXPR;
            $2->lnode = $1;
            $$ = $2;
	}

postdec_expr: postfix_expr DECR
	{
            $2->hdr.type = TN_EXPR;
            $2->lnode = $1;
            $$ = $2;
	}

opt_expr_list:  /* Nothing */
	{
            $$ = (treenode *) NULL;
	}
	| expr_list
        ;

expr_list:  assign_expr
	|  expr_list COMMA assign_expr    %prec COMMA_SEP
	{
            $2->hdr.type = TN_EXPR_LIST;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}
	|  LPAREN type_name RPAREN LBRACE initializer_list RBRACE
	{	$$ = (treenode *) 0; }	/* gjh don't choke on structs as parameters */
	|  expr_list COMMA LPAREN type_name RPAREN LBRACE initializer_list RBRACE
	{	$$ = $1; }		/* gjh */


named_label:  IDENT
	{
		$$ = (treenode *) $1;
		if (ParseStack->contxt)
		{	symentry_t *nmtbl, *y;
			nmtbl = mk_label($1->data.sval, $$);

			if (0) printf("named label %s %p\n", $1->data.sval->str, nmtbl);

			y = symtab_insert_at(ParseStack->contxt->labels,
					nmtbl, FUNCTION_SCOPE);
			if (!y)
				yyerr("Duplicate label.");

	/*		$$->syment = y;	*/
		}
	}

case_label:  CASE const_expr
	{
            $1->hdr.type = TN_EXPR;
            $1->rnode = $2;
            $$ = (treenode *) $1;
	}

deflt_label:  DEFLT
        ;

add_op:  PLUS
	|  MINUS
        ;

mult_op:  STAR
	|  DIV
	|  MOD
        ;

equality_op:  COMP_EQ
        ;

relation_op:  COMP_ARITH
        ;

shift_op:  L_SHIFT
	|  R_SHIFT
        ;

declaration: decl_specs opt_init_decl_list SEMICOLON
	{
            leafnode *lm;
            $3->hdr.type = TN_DECL;
            $3->lnode = $1;
            $3->rnode = $2;
            $$ = $3;

            lm = leftmost($$);
            if (lm)
            {
              if (lm->hdr.tok == TYPEDEF)
              {
                /* Decl is a typedef. Scan the subtree for the
                   ident naming the new type.  Don't use rightmost()
                   since it doesn't give the ident for complex
                   types (like arrays). */
                find_typedef_name($$,$$,insert_typedef);
              } else {
                /* Find the identifier for a normal declaration. */
                find_ident_name($$,$$,NULL,insert_decl);
              }
            }
	}
	|  COMMENT
	{
           $$ = (treenode *) $1;
	}

opt_comment:  /* Nothing */
	{
           $$ = (treenode *) NULL;
	}
	|     COMMENT 
	{
           $$ = (treenode *) $1;
	}

opt_decl_specs:   /* Nothing */
	{
           $$ = (treenode *) NULL;
	}
	| decl_specs
        ;

decl_specs:  storage_class opt_decl_specs
	{
            treenode *tmpnode = make_node(TN_TYPE_LIST);
            tmpnode->lnode = $1;
            tmpnode->rnode = $2;
            $$ = tmpnode;
	}
	|  type_spec opt_decl_specs
	{
            treenode *tmpnode = make_node(TN_TYPE_LIST);
            tmpnode->lnode = $1;
            tmpnode->rnode = $2;
            $$ = tmpnode;
	}
	|  type_qual opt_decl_specs
	{
            treenode *tmpnode = make_node(TN_TYPE_LIST);
            tmpnode->lnode = $1;
            tmpnode->rnode = $2;
            $$ = tmpnode;
	}
        ;

comp_decl_specs:  type_spec opt_comp_decl_specs
	{
            treenode *tmpnode = make_node(TN_TYPE_LIST);
            tmpnode->lnode = $1;
            tmpnode->rnode = $2;
            $$ = tmpnode;
	}
	|  type_qual opt_comp_decl_specs
	{
            treenode *tmpnode = make_node(TN_TYPE_LIST);
            tmpnode->lnode = $1;
            tmpnode->rnode = $2;
            $$ = tmpnode;
	}
        ;

opt_comp_decl_specs:   /* Nothing */
	{
           $$ = (treenode *) NULL;
	}
	| comp_decl_specs
        ;

init_decl: declarator
	| declarator EQ initializer
	{
           $2->hdr.type = TN_ASSIGN;
           $2->lnode = $1;
           $2->rnode = $3;
           $$ = $2;
	}

opt_init_decl_list:  /* Nothing */
	{
          $$ = (treenode *) NULL;
	}
	|  init_decl_list
        ;

init_decl_list: init_decl
	| init_decl_list COMMA init_decl        %prec COMMA_OP
	{
            $2->hdr.type = TN_DECLS;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

initializer_list:  initializer
	|  initializer_list COMMA initializer    %prec COMMA_OP
	{
            $2->hdr.type = TN_INIT_LIST;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

initializer:  assign_expr
	|  LBRACE initializer_list opt_comma RBRACE
	{
            $2->hdr.type = TN_INIT_BLK;
            $$ = $2;
            free_tree($1);
            free_tree($3);
            free_tree($4);
	}
	| LBRCKT assign_expr RBRCKT initializer		/* gjh allow [] field initializers */
	{	$$ = $4;
	}
	| DOT field_ident EQ initializer		/* gjh allow .n field initializers */
	{	$$ = $3;
	}
	;

opt_comma:    /* Nothing */
	{
           $$ = (treenode *) NULL;
	}
	|  COMMA    %prec COMMA_SEP
        ;

type_qual_list: type_qual
	| type_qual_list type_qual
	{
            treenode *tmpnode = make_node(TN_TYPE_LIST);
            tmpnode->lnode = $1;
            tmpnode->rnode = $2;
            $$ = tmpnode;
	}
        ;

opt_type_qual_list:    /* Nothing */
	{
            $$ = (treenode *) NULL;
	}
	|   type_qual_list
        ;
        
storage_class: AUTO
	| EXTRN
	| REGISTR
	| STATIC
	| TYPEDEF
        ;

type_spec:  enum_type_spec
	|  struct_type_spec
	|  typedef_name
	|  union_type_spec
	|  VOID
	|  CHAR
	|  SHORT
	|  INT
	|  LONG
	|  FLOAT
	|  DOUBLE
	|  SGNED
	|  UNSGNED
        ;

enum_type_spec:  enum_type_define
	|  enum_type_ref
        ;

struct_type_spec:  struct_type_define
	|  struct_type_ref
        ;

typedef_name:  TYPEDEF_NAME
	{
           $$ = (treenode *) $1;
	}

union_type_spec:  union_type_define
	|  union_type_ref
        ;

opt_tag:  /* Nothing */
	{
           $$ = (treenode *) NULL;
	}
	|  tag
        ;

tag:    IDENT
	{
          $$ = (treenode *) $1;
	}
	| typename_as_ident
        ;

enum_type_define:  ENUM opt_tag LBRACE enum_def_list opt_trailing_comma RBRACE
	{
		$1->hdr.type = TN_OBJ_DEF;
		$1->lnode = $2;
		$1->rnode = $4;
		free_tree($3);
		free_tree($5);
		free_tree($6);

		if (ParseStack->contxt && $2)
		{	leafnode *leaf = (leafnode *) $2;
			symentry_t *nmtbl;

			nmtbl = mk_tag(leaf->data.sval, $$);	/* enum name */
			/* fprintf(stderr, "ENUMdef: %s\n", nmtbl->nme->str); */
			if (leaf->syment) printf("typename redefined: %s\n", leaf->syment->nme->str);

			leaf->syment = nmtbl;
			if (!symtab_insert(ParseStack->contxt->tags, nmtbl))
				yyerr("Duplicate tag.");
			leaf->syment->nes = ParseStack->contxt->syms->current;
			leaf->syment->decl_level = ParseStack->contxt->syms->clevel;
		}
	}
 
enum_type_ref:  ENUM tag
	{
            $1->hdr.type = TN_OBJ_REF;
            $1->lnode = $2;
	}

enum_def_list:  enum_const_def
	|  enum_def_list COMMA enum_const_def        %prec COMMA_OP
	{
           $2->hdr.type = TN_ENUM_LIST;
           $2->lnode = (treenode *) $1;
           $2->rnode = $3;
           $$ = $2;
	}

enum_const_def:  enum_constant
	|  enum_constant EQ assign_expr 
	{
            $2->hdr.type = TN_ASSIGN;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

enum_constant:  IDENT
	{
		$$ = (treenode *) $1;
		if (ParseStack->contxt)
		{	symentry_t *nmtbl = mk_enum_const($1->data.sval, $$);

			add_constant(nmtbl->nme->str, 0);	/* gjh */

			if (!symtab_insert(ParseStack->contxt->syms, nmtbl))
				yyerr("Duplicate enumeration constant.");
		}
	}

opt_trailing_comma:    /* Nothing */
	{
            $$ = (treenode *) NULL;
	}
	| COMMA    %prec COMMA_SEP
	;

struct_type_define: STRUCT opt_tag LBRACE
	{
            enter_scope(ParseStack->contxt);
	}
		field_list RBRACE
	{
		$1->hdr.type = TN_OBJ_DEF;
		$1->lnode = $2;
		$1->rnode = $5;
		free_tree($3);
		free_tree($6);
		if (ParseStack->contxt && $2)
		{	leafnode *leaf = (leafnode *) $2;
			symentry_t *nmtbl;

			nmtbl = mk_tag(leaf->data.sval, $$);
			leaf->syment = nmtbl;

			if (!symtab_insert(ParseStack->contxt->tags, nmtbl))
				yyerr("Duplicate tag.");

			leaf->syment->nes = ParseStack->contxt->syms->current;
			leaf->syment->decl_level = ParseStack->contxt->syms->clevel;
		}
    
		find_components($5,$1,$1,insert_component);
		{	char *foobar;
			if (!$2)
			{	static int unnamed_structs = 0;
				foobar = (char *) e_malloc(strlen("_UnNamed_") + 6);
				sprintf(foobar, "_UnNamed_%d", unnamed_structs++);
			} else
			{	foobar = ((leafnode *) $2)->data.sval->str;
			}
			name_scope(ParseStack->contxt, foobar, TN_OBJ_DEF);
		}
		exit_scope(ParseStack->contxt);
	}

struct_type_ref:  STRUCT tag
	{
            $1->hdr.type = TN_OBJ_REF;
            $1->lnode = $2;
	}

union_type_define: UNION opt_tag LBRACE
	{
            enter_scope(ParseStack->contxt);
	}
		field_list RBRACE
	{
            $1->hdr.type = TN_OBJ_DEF;
            $1->lnode = $2;
            $1->rnode = $5;
            free_tree($3);
            free_tree($6);
            if (ParseStack->contxt && $2)
            {	leafnode *leaf = (leafnode *) $2;
		symentry_t *nmtbl;

		nmtbl = mk_tag(leaf->data.sval, $$);
		leaf->syment = nmtbl;

            	if (!symtab_insert(ParseStack->contxt->tags, nmtbl))
			yyerr("Duplicate tag.");

		leaf->syment->nes = ParseStack->contxt->syms->current;
		leaf->syment->decl_level = ParseStack->contxt->syms->clevel;
            }

            find_components($5,$1,$1,insert_component);
		if ($2)
		{
		name_scope(ParseStack->contxt,
			((leafnode *) $2)->data.sval->str,
			TN_OBJ_DEF);
		}
            exit_scope(ParseStack->contxt);
	}

union_type_ref:  UNION tag
	{
            $1->hdr.type = TN_OBJ_REF;
            $1->lnode = $2;
	}

field_list:  comp_decl
	|  field_list comp_decl
	{
           treenode *tmpnode = make_node(TN_FIELD_LIST);
           tmpnode->lnode = $1;
           tmpnode->rnode = $2;
           $$ = tmpnode;
	}

comp_decl:  comp_decl_specs comp_decl_list SEMICOLON
	{
          $3->hdr.type = TN_COMP_DECL;
          $3->lnode = $1;
          $3->rnode = $2;
          $$ = $3;
	}

comp_decl_list:  comp_declarator
	|  comp_decl_list COMMA comp_declarator     %prec COMMA_OP
	{
            $2->hdr.type = TN_DECLS;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}
	| SEMICOLON	/* gjh - condone unnamed sub-structs */
	{	extern FILE *yyin;
		ungetc(';', yyin);
		$$ = (treenode *) 0;
	}

comp_declarator:  simple_comp
	|  bit_field
        ;


simple_comp:  declarator
        ;

bit_field:  opt_declarator COLON width
	{
            $2->hdr.type = TN_BIT_FIELD;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}
        ;

width:  assign_expr
        ;

type_qual: CONST
	| VOLATILE
        ;

type_name:  decl_specs
	{
            treenode *tmpnode = make_node(TN_TYPE_NME);
            tmpnode->lnode = $1;
            $$ = tmpnode;
	}
	| decl_specs abs_decl
	{
            treenode *tmpnode = make_node(TN_TYPE_NME);
            tmpnode->lnode = $1;
            tmpnode->rnode = $2;
            $$ = tmpnode;
	}

opt_declarator:  /* Nothing */
	{
           $$ = (treenode *) NULL;
	}
	|  declarator
        ;

declarator: pointer direct_declarator
	{
            treenode *tmpnode = make_node(TN_DECL);
            tmpnode->lnode = $1;
            tmpnode->rnode = $2;
            $$ = tmpnode;
	}
	| direct_declarator
        ;

direct_declarator:  field_ident
	{	/* gjh: was simple_decl - should be field_ident
		 * to allow typedef'ed names as identifiers
		 * but this introduces 5 shift reduce and 23 reduce/reduce conflicts
		 */
		$$ = $1;
	}
	|  LPAREN declarator RPAREN
	{
            $$ = $2;
            free_tree($1);
            free_tree($3);
	}
	|  array_decl
	|  direct_declarator LPAREN param_type_list RPAREN
	{
            $2->hdr.type = TN_FUNC_DECL;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
            free_tree($4);
	}
	|  direct_declarator LPAREN ident_list RPAREN
	{
            $2->hdr.type = TN_FUNC_DECL;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
            free_tree($4);
	}
	|  direct_declarator LPAREN RPAREN
	{
            $2->hdr.type = TN_FUNC_DECL;
            $2->lnode = $1;
            $$ = $2;
            free_tree($3);
	}
        ;

simple_decl:  IDENT 
	{
	/* NYI - Need error check code here
           leafnode *ln = $1;
           fprintf(stdout,"Value: %s\n", nmestr(ln->data.sval));
	*/
	}

pointer_start:  STAR opt_type_qual_list
	{
            $1->hdr.type = TN_PNTR;
            $1->lnode = $2;
            $1->rnode = NULL;
	}

pointer:  pointer_start
	|  pointer_start pointer
	{
            $1->hdr.type = TN_PNTR;
            $1->rnode = $2;
	}

opt_param_type_list:  /* Nothing */
	{
           $$ = (treenode *) NULL;
	}
	|  param_type_list
        ;

param_type_list: param_list
	| param_list COMMA ELLIPSIS        %prec COMMA_OP
	{
            $2->hdr.type = TN_PARAM_LIST;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

param_list: param_decl
	| param_list COMMA param_decl        %prec COMMA_OP
	{
            $2->hdr.type = TN_PARAM_LIST;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
	}

param_decl: decl_specs declarator
	{
            treenode *tmpnode = make_node(TN_DECL);
            tmpnode->lnode = $1;
            tmpnode->rnode = $2;
            $$ = tmpnode;
	}
	| decl_specs abs_decl
	{
            treenode *tmpnode = make_node(TN_DECL);
            tmpnode->lnode = $1;
            tmpnode->rnode = $2;
            $$ = tmpnode;
	}
	| decl_specs
	{
            treenode *tmpnode = make_node(TN_DECL);
            tmpnode->lnode = $1;
            $$ = tmpnode;
	}

ident_list: ident
	{
           $$ = (treenode *) $1;
	}
	| ident_list COMMA ident        %prec COMMA_OP
	{
            $2->hdr.type = TN_IDENT_LIST;
            $2->lnode = $1;
            $2->rnode = (treenode *) $3;
            $$ = $2;
	}
        ;

ident: IDENT
        ;

field_ident: simple_decl
	| typename_as_ident
        ;

typename_as_ident: typedef_name
	{
            /* Convert a TYPEDEF_NAME back into a normal IDENT */
            $1->hdr.type = TN_IDENT;
            $1->hdr.tok  = IDENT;
            $$ = (treenode *) $1;
	}
        ;

abs_decl:  pointer
	|  direct_abs_decl
	{
            treenode *tmpnode = make_node(TN_DECL);
            tmpnode->rnode = $1;
            $$ = tmpnode;
	}
	|  pointer direct_abs_decl
	{
            treenode *tmpnode = make_node(TN_DECL);
            tmpnode->lnode = $1;
            tmpnode->rnode = $2;
            $$ = tmpnode;
	}

direct_abs_decl:  LPAREN abs_decl RPAREN
	{
            $$ = $2;
            free_tree($1);
            free_tree($3);
	}
	|  LBRCKT opt_const_expr RBRCKT
	{
            $1->hdr.type = TN_ARRAY_DECL;
            $1->rnode = $2;
            free_tree($3);
	}
	|  direct_abs_decl LBRCKT opt_const_expr RBRCKT
	{
            $2->hdr.type = TN_ARRAY_DECL;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
            free_tree($4);
	}
	|  LPAREN opt_param_type_list RPAREN
	{
            $1->hdr.type = TN_FUNC_DECL;
            $2->rnode = $2;
            free_tree($3);
	}
	|  direct_abs_decl LPAREN opt_param_type_list RPAREN
	{
            $2->hdr.type = TN_FUNC_DECL;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
            free_tree($4);
	}

array_decl: direct_declarator LBRCKT opt_const_expr RBRCKT
	{
            $2->hdr.type = TN_ARRAY_DECL;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
            free_tree($4);
	}

direct_comp_select: postfix_expr DOT
	{   /* gjh */ structfieldflag = 1;
	}
	field_ident
	{   /* gjh */ structfieldflag = 0;
	
            $2->hdr.type = TN_SELECT;
            $2->lnode = $1;
            $2->rnode = (treenode *) $4;
            $$ = $2;
	}

indirect_comp_select: postfix_expr ARROW
	{   /* gjh */ structfieldflag = 1;
	}
	field_ident
	{   /* gjh */ structfieldflag = 0;
	
            $2->hdr.type = TN_SELECT;
            $2->lnode = $1;
            $2->rnode = (treenode *) $4;
            $$ = $2;
	}

func_call: postfix_expr LPAREN opt_expr_list RPAREN
	{
            $2->hdr.type = TN_FUNC_CALL;
            $2->lnode = $1;
            $2->rnode = $3;
            $$ = $2;
            free_tree($4);
	}

assign_op:  EQ
	|  ASSIGN
        ;

strings:  STRING
	| strings STRING	/* should concatenate the strings */
	;

constant:   INUM
	| RNUM
	| CHAR_CONST
	| strings		/* was STRING, changed gjh 11/11/01 */
        ;

%%

static void
insert_decl(leafnode *leaf, treenode *def, treenode *container)
{
	if (leaf
	&& (leaf->hdr.tok == IDENT)
	&&  ParseStack->contxt)
	{	symentry_t *nmtbl = mk_vardecl(leaf->data.sval, def);

		leafnode *lm = leftmost(def);
		if (lm
		&& (lm->hdr.tok != STATIC)
		&& ParseStack->contxt->syms->clevel == FILE_SCOPE)
		{	leaf->syment = symtab_insert_at(ParseStack->contxt->syms, nmtbl, EXTERN_SCOPE);
			if (Verbose&2)
			printf("%s: line %d lifting %s to extern scope\n",
				progname, leaf->hdr.line,
				nmestr(leaf->data.sval));
		} else
			leaf->syment = symtab_insert(ParseStack->contxt->syms, nmtbl);

		if (0) fprintf(stdout, "\tinsert_decl: %s -- %d -- line %d\n",
			nmestr(leaf->data.sval),
			ParseStack->contxt->syms->clevel,
			leaf->hdr.line);
		leaf->syment->nes = ParseStack->contxt->syms->current;
		leaf->syment->decl_level = ParseStack->contxt->syms->clevel;
		if (0)
		{	extern char *x_stmnt(treenode *);
			printf("insert decl for %s - nes=%p, owner=%s - <%s>\n",
			nmestr(leaf->data.sval),
			leaf->syment->nes,
			leaf->syment->nes && leaf->syment->nes->owner ? leaf->syment->nes->owner : "no owner",
			x_stmnt(leaf->syment->node));
	}	}
}

extern void print_tree(treenode *, FILE *);

static void
insert_typedef(leafnode *leaf, treenode *def, treenode *container)
{
	if (leaf && (leaf->hdr.tok == IDENT))
	{	if (ParseStack->contxt)
		{	symentry_t *entry = mk_typedef(leaf->data.sval, def);
			// entry->kind == TYPEDEF_ENTRY
			leaf->syment = symtab_insert(ParseStack->contxt->syms, entry);
			leaf->syment->nes = ParseStack->contxt->syms->current;
			leaf->syment->decl_level = ParseStack->contxt->syms->clevel;
			if (0)
			{	fprintf(stderr, "%s:%d, Insert Typedef: %s (%d)\n",
					leaf->hdr.fnm, leaf->hdr.line,
					entry->nme->str, entry->kind);
			//	print_tree(def, stdout);
		}	}
	} else if (leaf)	/* gh */
	{	printf("modex: %s:%d: cannot happen, insert_typedef for %s - %s\n",
			leaf->hdr.fnm, leaf->hdr.line,
			name_of_node(leaf->hdr.type),
			toksym(leaf->hdr.tok,1));
	}
}

static void
insert_component(leafnode *leaf, treenode *def, treenode *container)
{
	if (leaf && (leaf->hdr.tok == IDENT))
	if (ParseStack->contxt)
	{	symentry_t *entry = mk_component(leaf->data.sval, def, container);
		leaf->syment = symtab_insert(ParseStack->contxt->syms, entry);
		leaf->syment->nes = ParseStack->contxt->syms->current;
		leaf->syment->decl_level = ParseStack->contxt->syms->clevel;
	}
}

static void
add_params_to_symtab(treenode *funcdecl)
{
	/* Parameters are defined at prototype/function scope */
	enter_scope(ParseStack->contxt);

	while (funcdecl->hdr.type == TN_DECL)
		funcdecl = funcdecl->rnode;	/* e.g., fct returns ptr */

	if (funcdecl->hdr.type != TN_FUNC_DECL)
	{	if (debug)
		printf("%s: line %d, unexpected, funcdecl = %s (%s)\n",
			progname, funcdecl->hdr.line,
			name_of_node(funcdecl->hdr.type),
			((leafnode *)funcdecl)->data.sval->str);
		return;
	}

	find_params(funcdecl, insert_decl);
}

int
current_linenumber(void)
{
	if (Parse_TOS)
		return Parse_TOS->yylineno;
	return 0;
}

char *
current_filename(void)
{	static char *CurFile = (char *) 0;

	if (Parse_TOS
	&& (!CurFile
	||  strcmp(CurFile, Parse_TOS->filename) != 0))
	{	CurFile = (char *) e_malloc(strlen(Parse_TOS->filename)+1);
		strcpy(CurFile, Parse_TOS->filename);
	}
	return CurFile;
}
