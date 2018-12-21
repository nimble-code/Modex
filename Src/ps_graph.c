/***** modex: ps_graph.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include "prnttree.h"
#include "gram.h"
#include "symtab.h"

/* generates DOT input from parsetree. e.g.:
 *	modex -u file.c | dot -Tps > ptree.ps
 */

static void	dot_if(if_node *);
static void	dot_for(for_node *);
static void	dot_node(treenode *);
       void	dot_tree(treenode *);
extern void	dump_defuse(DefUse *, FILE *);
extern char	*toksym(int tok, int white);

extern char	*progname;

#define DDEBUG	if (0)
#define DTREE	if (1)

void
dot_leaf(leafnode *leaf)
{
	if (!leaf) return;

DTREE	printf("N%lu -> L%lu;\n", (unsigned long) leaf, (unsigned long) leaf);
DTREE	printf("L%lu [label=\"", (unsigned long) leaf);

	switch (leaf->hdr.type) {
	case TN_IDENT:
DDEBUG		printf("%s", leaf->data.sval->str);
DTREE		printf("%s", leaf->data.sval->str);
		break;

	case TN_LABEL:
		if (leaf->hdr.tok == DEFLT)
		{
DDEBUG		printf("default:");
DTREE		printf("Default:");
		} else
		{
DDEBUG		printf("%s:", leaf->data.sval->str);
DTREE		printf("%s:", leaf->data.sval->str);
		}
		break;

	case TN_COMMENT:
DTREE		printf("/* %s */", leaf->data.str);
		break;

	case TN_STRING:
DDEBUG		printf("\'%s\'", leaf->data.str);	/* \"%s\" */
DTREE		printf("\'%s\'", leaf->data.str);	/* \"%s\" */
		break;

	case TN_TYPE:
		if (leaf->hdr.tok != TYPEDEF_NAME)
		{	/* including: leaf->hdr.tok == TYPEDEF */
DDEBUG			printf("%s", toksym(leaf->hdr.tok,1));
DTREE			printf("%s", toksym(leaf->hdr.tok,1));
		} else
		{
DDEBUG			printf("%s", leaf->data.sval->str);
DTREE			printf("%s", leaf->data.sval->str);
		}
		break;
	case TN_REAL:
DDEBUG		printf("%f", leaf->data.dval);
DTREE		printf("%f", leaf->data.dval);
		break;

	case TN_INT:
		if (leaf->hdr.tok == CHAR_CONST)
		{
DDEBUG			printf("'%c'", leaf->data.ival);
DTREE			printf("'%c'", leaf->data.ival);
		} else
		{
DDEBUG			printf("%d", leaf->data.ival);
DTREE			printf("%d", leaf->data.ival);
		}
		break;

	case TN_ELLIPSIS:
DDEBUG		printf("...");
DTREE		printf("...");
		break;

	default:
		fprintf(stderr, "%s: unexpected leaf %s\n",
			progname, name_of_node(leaf->hdr.type));
		break;
	}

DTREE	printf("\"];\n");
}

static void
dot_node(treenode *root)
{
	if (!root) return;

	if (root->lnode)
	{
DTREE		printf("N%lu -> N%lu [label=\"L\"];\n",
			(unsigned long) root,
			(unsigned long) root->lnode);
	}
	if (root->rnode)
	{
DTREE		printf("N%lu -> N%lu [label=\"R\"];\n",
			(unsigned long) root,
			(unsigned long) root->rnode);
	}

	switch (root->hdr.type) {
	case TN_TYPE_NME:
	case TN_TRANS_LIST:
	case TN_NAME_LIST:
	case TN_FIELD_LIST:
	case TN_IDENT_LIST:
	case TN_TYPE_LIST:
		dot_tree(root->lnode);
DDEBUG		printf(" ");
		dot_tree(root->rnode);
		break;

	case TN_FUNC_CALL:
		dot_tree(root->lnode);		/* fct name */
DDEBUG		printf(" ( ");
		dot_tree(root->rnode);		/* actual params */
DDEBUG		printf(" ) ");
		break;

	case TN_ASSIGN:
		dot_tree(root->lnode);		/* lhs = */
DDEBUG		printf(" %s ", toksym(root->hdr.tok,1));	/* operator */
		dot_tree(root->rnode);		/* = rhs */
		break;

	case TN_DECL:
DDEBUG		printf("\n=====Declaration: ");	/* start of declaration */
		dot_tree(root->lnode);
DDEBUG		printf(" ");	/* separator between type and varname */
		dot_tree(root->rnode);
DDEBUG		printf(" =====\n");	/* end of declaration */
		break;

	case TN_EXPR:
		switch (root->hdr.tok) {
		case CASE:
DDEBUG			printf(" %s ", toksym(root->hdr.tok,1));
			dot_tree(root->lnode);
			dot_tree(root->rnode);	/* continuation */
			break;
		case SIZEOF:
DDEBUG			printf(" %s ", toksym(root->hdr.tok,1));
			dot_tree(root->lnode);
DDEBUG			printf(" ");
			dot_tree(root->rnode);
			break;
		case INCR:
		case DECR:
			dot_tree(root->lnode);
DDEBUG			printf(" %s ", toksym(root->hdr.tok,1));
			dot_tree(root->rnode);
			break;
		case B_AND:
			if (!root->lnode)
			{
DDEBUG				printf(" %s ", toksym(root->hdr.tok,1)); /* operator */
				dot_tree(root->rnode);	/* operand */
				break;
			} /* else fall thru */
		default:
DDEBUG			printf(" ( ");
			dot_tree(root->lnode);		/* l operand */
DDEBUG			printf(" %s ", toksym(root->hdr.tok,1)); /* operator */
			dot_tree(root->rnode);		/* r operand */
DDEBUG			printf(" ) ");
			break;
		}
		break;

	case TN_SELECT:
		dot_tree(root->lnode);
		if (root->hdr.tok == ARROW)
		{
DDEBUG			printf(" -> ");
		} else
		{
DDEBUG			printf(" . ");
		}
		dot_tree(root->rnode);
		break;

	case TN_INDEX:
		dot_tree(root->lnode);	/* base */
DDEBUG		printf(" [ ");
		dot_tree(root->rnode);	/* index */
DDEBUG		printf(" ] ");
		break;

	case TN_DEREF:	/* (*x) */
DDEBUG		printf(" * ");
		dot_tree(root->lnode);
DDEBUG		printf(" ( ");
		dot_tree(root->rnode);	/* operand */
DDEBUG		printf(" ) ");
		break;

	case TN_FUNC_DECL:
		if (root->lnode
		&& (root->lnode->hdr.type == TN_IDENT))
		{
			dot_tree(root->lnode);
		} else
		{
DDEBUG			printf(" ( ");
			dot_tree(root->lnode);
DDEBUG			printf(" ) ");
		}
DDEBUG		printf(" ( ");
		dot_tree(root->rnode);
DDEBUG		printf(" ) ");
		break;

	case TN_ARRAY_DECL:
		dot_tree(root->lnode);	/* basename */
DDEBUG		printf(" [ ");
		dot_tree(root->rnode);	/* array size */
DDEBUG		printf(" ] ");
		break;

	case TN_BLOCK:
DDEBUG		printf(" {\n");
		dot_tree(root->lnode);
DDEBUG		printf(" ");
		dot_tree(root->rnode);
DDEBUG		printf(" }\n");
		break;

	case TN_INIT_LIST:
	case TN_PARAM_LIST:
	case TN_DECL_LIST:
	case TN_DECLS:
	case TN_ENUM_LIST:
	case TN_EXPR_LIST:
		dot_tree(root->lnode);
DDEBUG		printf(" , ");
		dot_tree(root->rnode);
		break;

	case TN_STEMNT_LIST:
		dot_tree(root->lnode);
		dot_tree(root->rnode);
		break;

	case TN_COMP_DECL:
		dot_tree(root->lnode);
DDEBUG		printf(" ? ");
		dot_tree(root->rnode);
DDEBUG		printf(" ;?\n");			/* ? */
		break;

	case TN_STEMNT:
		dot_tree(root->lnode);
DDEBUG		printf(" ");
		dot_tree(root->rnode);
DDEBUG		printf(" ;\n");			/* STMNT SEPARATOR */
		break;

	case TN_BIT_FIELD:
		dot_tree(root->lnode);	/* name */
DDEBUG		printf(" : ");
		dot_tree(root->rnode);	/* nr bits */
		break;

	case TN_PNTR:
DDEBUG		printf(" * ");
		dot_tree(root->lnode);
DDEBUG		printf(" ");
		dot_tree(root->rnode);
		break;

	case TN_OBJ_DEF:
DDEBUG		printf(" %s ", toksym(((leafnode *)root)->hdr.tok,1));
		dot_tree(root->lnode);
DDEBUG		printf(" { ");
		dot_tree(root->rnode);
DDEBUG		printf(" } ");
		break;

	case TN_OBJ_REF:
DDEBUG		printf(" %s ", toksym(((leafnode *)root)->hdr.tok,1));
		dot_tree(root->lnode);
DDEBUG		printf(" ");
		dot_tree(root->rnode);
		break;

	case TN_CAST:
DDEBUG		printf(" ( ");
		dot_tree(root->lnode);	/* type */
DDEBUG		printf(" ) ");
		dot_tree(root->rnode);	/* operand */
		break;

	case TN_JUMP:
DDEBUG		printf(" %s ", toksym(root->hdr.tok,1));
		dot_tree(root->lnode);	/* destination */
		/* no rnode? */

		break;
	case TN_LABEL:
		dot_tree(root->lnode);	/* labelname */
DDEBUG		printf(" : ");
		dot_tree(root->rnode);	/* continuation */
		break;

	case TN_INIT_BLK:
DDEBUG		printf(" { ");
		dot_tree(root->lnode);
DDEBUG		printf(" , ");
    		dot_tree(root->rnode);
DDEBUG		printf(" } ");
		break;

	case TN_SWITCH:
	case TN_WHILE:
	case TN_DOWHILE:
		dot_tree(root->lnode);
		dot_tree(root->rnode);
		break;
	case TN_EMPTY:
		break;
	default:
		fprintf(stderr, "%s: line %3d unexpected node %s\n",
			progname, root->hdr.line, name_of_node(root->hdr.type));
		break;
	}
}

static void
dot_if(if_node *ifn)
{
	if (!ifn) return;

	if (ifn->cond)
	{
DTREE	{
	printf("N%lu -> N%lu", (unsigned long) ifn, (unsigned long) ifn->cond);
	printf(" [label=\"cond\"];\n");
	}
	}
	if (ifn->then_n)
	{
DTREE	{
	printf("N%lu -> N%lu", (unsigned long) ifn, (unsigned long) ifn->then_n);
	printf(" [label=\"then_n\"];\n");
	}
	}
	if (ifn->else_n)
	{
DTREE	{
	printf("N%lu -> N%lu", (unsigned long) ifn, (unsigned long) ifn->else_n);
	printf(" [label=\"else_n\"];\n");
	}
	}

	if (ifn->hdr.tok == QUESTMARK)		/* cond expr */
	{
		dot_tree(ifn->cond);
DDEBUG		printf(" ? ");
		dot_tree(ifn->then_n);
DDEBUG		printf(" : ");
		dot_tree(ifn->else_n);

	} else					/* normal if */
	{
DDEBUG		printf(" if ");
		dot_tree(ifn->cond);
DDEBUG		printf(" then ");
		dot_tree(ifn->then_n);
DDEBUG		printf(" else ");
		dot_tree(ifn->else_n);
DDEBUG		printf(" fi;\n");
	}
}

static void
dot_for(for_node *forn)
{
	if (!forn) return;

	if (forn->init)
	{
DTREE	{
	printf("N%lu -> N%lu", (unsigned long) forn, (unsigned long) forn->init);
	printf(" [label=\"init\"];\n");
	}
	}
	if (forn->test)
	{
DTREE	{
	printf("N%lu -> N%lu", (unsigned long) forn, (unsigned long) forn->test);
	printf(" [label=\"test\"];\n");
	}
	}
	if (forn->incr)
	{
DTREE	{
	printf("N%lu -> N%lu", (unsigned long) forn, (unsigned long) forn->incr);
	printf(" [label=\"incr\"];\n");
	}
	}
	if (forn->stemnt)
	{
DTREE	{
	printf("N%lu -> N%lu", (unsigned long) forn, (unsigned long) forn->stemnt);
	printf(" [label=\"stemnt\"];\n");
	}
	}

	if (forn->hdr.type == TN_FUNC_DEF)
	{
#if 0
DDEBUG		printf("\n=====Function: ");
		dot_tree(forn->test);	/* fct name and parameter decls */
DDEBUG		printf("=====\n");
#else
DDEBUG		printf("\n");
		dot_tree(forn->init);	/* type returned by fct */
		dot_tree(forn->test);	/* fct name and parameter decls */

		if (forn->test
		&&  forn->test->hdr.which == LEAF_T)
		{
DDEBUG				printf(" ()\n");
		}
		dot_tree(forn->incr);	/* not used ? */
DDEBUG		printf("\n");
		dot_tree(forn->stemnt);	/* Fct Body: */
DDEBUG		printf("\n");
#endif

	} else	/* normal for-loop */
	{
	/*	push_dostack(forn->incr);	*/

DDEBUG		printf(" for ( ");
		dot_tree(forn->init);
DDEBUG		printf(" ; ");
		dot_tree(forn->test);
DDEBUG		printf(" ; ");
		dot_tree(forn->incr);
DDEBUG		printf(" ) { ");
		dot_tree(forn->stemnt);
DDEBUG		printf(" }\n");

	/*	pop_dostack();			*/
	}
}

void
dot_start(treenode *root)
{
DTREE	{
	printf("digraph dodot {\n");
	printf("	ratio=auto;\n");
	/* printf("	page=\"8.3x11.7\";\n");	*/
	}

	dot_tree(root);

DTREE	printf("\n}\n");
}

void
dot_tree(treenode *root)
{
	if (!root) return;

DTREE	printf("N%lu [label=\"%s\"];\n",
		(unsigned long) root,
		name_of_node(root->hdr.type));
DTREE	if (root->hdr.defuse) {
		printf("N%lu -> f%lu;\n",
			(unsigned long) root,
			(unsigned long) root);
		printf("f%lu [shape=box,label=\"",
			(unsigned long) root);
		dump_defuse(root->hdr.defuse, stdout);
		printf("\"];\n");
	}

	switch (root->hdr.which) {
	case IF_T:
		dot_if((if_node *) root);
		break;

	case FOR_T:
		dot_for((for_node *) root);
		break;

	case LEAF_T:
		dot_leaf((leafnode *) root);
		break;

	case NODE_T:
		dot_node(root);
		break;

	default:
		fprintf(stderr, "%s: unhandled type %s\n",
			progname, name_of_nodetype(root->hdr.which));
		break;
	}
}
