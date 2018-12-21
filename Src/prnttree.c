/***** modex: prnttree.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#include    <string.h>
#include    "prnttree.h"
#include    "gram.h"
#include    "symtab.h"

static int	decl_cnt;
static int	just_left_blk;
static int	enum_list_cnt;
static FILE	*can_flush;
extern char	*progname;
extern char	*toksym(int tok, int white);

static char	PBuf[8000];

static void
indented(int levels)
{	int j;

	for (j = levels; j > 0; j--)
		strcat(PBuf, " ");
}

static void
fput_meta(int c, int in_str)
{	char s[2];

	switch (c) {
	case '\'':
		strcat(PBuf, in_str ? "'" : "\\'");
		break;
	case '"':
		strcat(PBuf, in_str ? "\\\"" : "\"");
		break;
	case '\0':
		strcat(PBuf, "\\0");
		break;
	case '\\':
		strcat(PBuf, "\\\\");
		break;
	case '\n':
		strcat(PBuf, "\\n");
		break;
	case '\t':
		strcat(PBuf, "\\t");
		break;
	case '\r':
		strcat(PBuf, "\\r");
		break;
	case '\f':
		strcat(PBuf, "\\f");
		break;
	case '\b':
		strcat(PBuf, "\\b");
		break;
	case '\v':
		strcat(PBuf, "\\v");
		break;
	case '\a':
		strcat(PBuf, "\\a");
		break;
	case '%':
		strcat(PBuf, "%%");	/* NEW */
		break;
	default:
		s[0] = c; s[1] = '\0';
		strcat(PBuf, s);
		break;
	}
}

static void
fput_meta2(char *str)
{
	while (*str)
		fput_meta((int) *str++, 1);
}

static void
do_recur(treenode *root, int level)
{	if_node  *ifn;
	for_node *forn;
	leafnode *leaf;

	if (!root) return;

	if (can_flush)	/* avoid overflow */
	{	fprintf(can_flush, "%s", PBuf);
		strcpy(PBuf, "");
	}
	just_left_blk = 0;

    switch (root->hdr.which){
   
    default:
    case NONE_T:
        fprintf(stderr, "%s: error: Node with no type\n", progname);
        return;

    case LEAF_T:
        leaf = (leafnode *) root;
        switch (leaf->hdr.type) {
        case TN_LABEL:
            if (leaf->hdr.tok == DEFLT)
              strcat(PBuf, "default");
            else
              strcat(PBuf, leaf->data.sval->str);
            strcat(PBuf, ":\n");
            break;

        case TN_IDENT:
            strcat(PBuf, leaf->data.sval->str);
            break;

        case TN_COMMENT:
            strcat(PBuf, "\n");
            strcat(PBuf, leaf->data.str);
            strcat(PBuf, "\n");
            break;

        case TN_ELLIPSIS:
            strcat(PBuf, "...");
            break;

        case TN_STRING:
            strcat(PBuf, "\"");
            fput_meta2(leaf->data.str);
            strcat(PBuf, "\"");
            break;

        case TN_TYPE:
            if (leaf->hdr.tok != TYPEDEF_NAME)
	    {
              strcat(PBuf, toksym(leaf->hdr.tok,1));
            } else
	    {
              strcat(PBuf, leaf->data.sval->str);
              strcat(PBuf, " ");
            }
            break;

        case TN_INT:
            if (leaf->hdr.tok == CHAR_CONST)
	    { strcat(PBuf, "'");
              fput_meta(leaf->data.ival, 0);
              strcat(PBuf, "'");
            } else
            { char nr[64];
	      sprintf(nr, "%d", leaf->data.ival);
	      strcat(PBuf, nr);
	    }
            break;

        case TN_REAL:
            { char nr[64];
              sprintf(nr, "%f", leaf->data.dval);
	      strcat(PBuf, nr);
	    }
            break;

        default:
            fprintf(stderr, "%s: Unknown leaf value %d\n", progname, leaf->hdr.type);
            break;
        }
        break;

    case IF_T:
        ifn = (if_node *) root;
        switch (ifn->hdr.type) {

        case TN_IF:
            strcat(PBuf, "if (");
            do_recur(ifn->cond, level);
            strcat(PBuf, ")\n");
            do_recur(ifn->then_n, level+1);
            if (ifn->else_n) {
                if (!just_left_blk)
                  strcat(PBuf, ";\n");
                indented(level);
                strcat(PBuf, "else\n");
                do_recur(ifn->else_n, level+1);
            }
            break;

        case TN_COND_EXPR:
            strcat(PBuf, "(");
            do_recur(ifn->cond, level);
            strcat(PBuf, ") ? (");
            do_recur(ifn->then_n, level);
            strcat(PBuf, ") : (");
            do_recur(ifn->else_n, level);
            strcat(PBuf, ")");
            break;

        default:
            fprintf(stderr, "%s: Unknown type of if node %d\n", progname, ifn->hdr.which);
            break;
        }
        break;

    case FOR_T:
        forn = (for_node *) root;
        switch (forn->hdr.type) {

        case TN_FUNC_DEF:
            do_recur(forn->init, level);
            do_recur(forn->test, level);
            if (forn->test->hdr.which == LEAF_T)
                strcat(PBuf, "()");
            do_recur(forn->incr, level);
            strcat(PBuf, "\n");
            do_recur(forn->stemnt, level);
            strcat(PBuf, "\n");
            break;

        case TN_FOR:
            strcat(PBuf, "for (");
            do_recur(forn->init, level);
            strcat(PBuf, "; ");
            do_recur(forn->test, level);
            strcat(PBuf, "; ");
            do_recur(forn->incr, level);
            strcat(PBuf, ")\n");
            do_recur(forn->stemnt, level+1);
            break;

        default:
            fprintf(stderr, "%s: Unknown type of for node %d\n", progname, forn->hdr.which);
            break;
        }
        break;

    case NODE_T:
        switch (root->hdr.type) {

        case TN_TRANS_LIST:
            do_recur(root->lnode, level);
            do_recur(root->rnode, level);
            break;

        case TN_FUNC_DECL:
            decl_cnt++;
            if (root->lnode && (root->lnode->hdr.type == TN_IDENT))
                do_recur(root->lnode, level);
            else {
                strcat(PBuf, "(");
                do_recur(root->lnode, level);
                strcat(PBuf, ")");
            }
            strcat(PBuf, "(");
            do_recur(root->rnode, level);
            strcat(PBuf, ")");
            decl_cnt--;
            break;

        case TN_FUNC_CALL:
	    do_recur(root->lnode, level);
            strcat(PBuf, "(");
            do_recur(root->rnode, level);
            strcat(PBuf, ")");
            break;

        case TN_BLOCK:
            strcat(PBuf, "{\n");
            do_recur(root->lnode, level+1);
            do_recur(root->rnode, level+1);
            indented(level);
            strcat(PBuf, "}\n");
            just_left_blk = 1;
            break;

        case TN_ARRAY_DECL:
            do_recur(root->lnode, level);
            strcat(PBuf, "[");
            do_recur(root->rnode, level);
            strcat(PBuf, "]");
            break;

        case TN_EXPR_LIST:
            do_recur(root->lnode, level);
            if (root->rnode)
              strcat(PBuf, ",");
            do_recur(root->rnode, level);
            break;

        case TN_NAME_LIST:
            do_recur(root->lnode, level);
            do_recur(root->rnode, level);
            break;

        case TN_ENUM_LIST:
            if (root->lnode
            && (root->lnode->hdr.type != TN_ENUM_LIST))
              indented(level);
            enum_list_cnt++;
            do_recur(root->lnode, level);
            if (root->rnode)
              strcat(PBuf, ",\n");
            indented(level);
            do_recur(root->rnode, level);
            if (--enum_list_cnt == 0)
              strcat(PBuf, "\n");
            break;

        case TN_FIELD_LIST:
            do_recur(root->lnode, level);
            do_recur(root->rnode, level);
            break;

        case TN_PARAM_LIST:
            do_recur(root->lnode, level);
            if (root->rnode)
              strcat(PBuf, ",");
            do_recur(root->rnode, level);
            break;

        case TN_IDENT_LIST:
            do_recur(root->lnode, level);
            do_recur(root->rnode, level);
            break;

        case TN_TYPE_LIST:
            do_recur(root->lnode, level);
            do_recur(root->rnode, level);
            break;

        case TN_DECL:
            if (decl_cnt == 0)
              indented(level);
            decl_cnt++;
            do_recur(root->lnode, level);
            do_recur(root->rnode, level);
            if (--decl_cnt == 0)
            {  strcat(PBuf, ";");
	       if (can_flush) strcat(PBuf, "\n");
	    }
            break;

        case TN_DECL_LIST:
            do_recur(root->lnode, level);
            if ((root->rnode
	    && (root->rnode->hdr.type == TN_IDENT))
            || (root->rnode->lnode
            && ((root->rnode->lnode->hdr.type == TN_IDENT)
            || (root->rnode->lnode->hdr.type == TN_PNTR))) )
              strcat(PBuf, ",");
            do_recur(root->rnode, level);
            break;

        case TN_DECLS:
            do_recur(root->lnode, level);
            if ((root->rnode && (root->rnode->hdr.type == TN_IDENT))
            || (root->rnode->lnode
            && ((root->rnode->lnode->hdr.type == TN_IDENT)
            || (root->rnode->lnode->hdr.type == TN_PNTR))) )
              strcat(PBuf, ",");
            do_recur(root->rnode, level);
            break;

        case TN_STEMNT_LIST:
            do_recur(root->lnode, level);
            if (root->lnode
            && (!just_left_blk)
            && (root->lnode->hdr.type != TN_STEMNT_LIST))
                strcat(PBuf, ";\n");

            if (root->rnode != NULL) {
                do_recur(root->rnode, level);
                if (!just_left_blk)
                    strcat(PBuf, ";\n");
            }
            break;

        case TN_STEMNT:
            if (root->rnode
	    && (root->rnode->hdr.type == TN_LABEL))
              indented(level-1);
            else
              indented(level);
            do_recur(root->lnode, level);
            do_recur(root->rnode, level);
            break;

        case TN_COMP_DECL:
            indented(level);
            do_recur(root->lnode, level);
            do_recur(root->rnode, level);
            strcat(PBuf, ";");
	    if (can_flush) strcat(PBuf, "\n");
            break;

        case TN_BIT_FIELD:
            do_recur(root->lnode, level);
            strcat(PBuf, ":");
            do_recur(root->rnode, level);
            break;

        case TN_PNTR:
            strcat(PBuf, "*");
            do_recur(root->lnode, level);
            do_recur(root->rnode, level);
            break;

        case TN_TYPE_NME:
            do_recur(root->lnode, level);
            do_recur(root->rnode, level);
            break;

        case TN_INIT_LIST:
            do_recur(root->lnode, level);
            strcat(PBuf, ",");
            do_recur(root->rnode, level);
            break;

        case TN_INIT_BLK:
            strcat(PBuf, "{");
            do_recur(root->lnode, level);
            strcat(PBuf, ",");
            do_recur(root->rnode, level);
            strcat(PBuf, "}");
            break;

        case TN_OBJ_DEF:
            leaf = (leafnode *) root;
            strcat(PBuf, toksym(leaf->hdr.tok,1));
            do_recur(root->lnode, level);
            strcat(PBuf, " {\n");
            do_recur(root->rnode, level+1);
            strcat(PBuf, "}");
            break;

        case TN_OBJ_REF:
            leaf = (leafnode *) root;
            strcat(PBuf, toksym(leaf->hdr.tok,1));
            do_recur(root->lnode, level);
            strcat(PBuf, " ");
            do_recur(root->rnode, level);
            break;

        case TN_CAST:
            decl_cnt++;    /* Not really, it's a hack. */
            strcat(PBuf, "(");
            do_recur(root->lnode, level);
            strcat(PBuf, ")");
            decl_cnt--;
            do_recur(root->rnode, level);
            break;

        case TN_JUMP:
            strcat(PBuf, toksym(root->hdr.tok,1));
            if ((root->hdr.tok == RETURN)
	    || (root->hdr.tok == GOTO))
               do_recur(root->lnode, level);
            break;

        case TN_SWITCH:
            strcat(PBuf, "switch (");
            do_recur(root->lnode, level);
            strcat(PBuf, ")\n");
            do_recur(root->rnode, level+1);
            break;

        case TN_INDEX:
            do_recur(root->lnode, level);
            strcat(PBuf, "[");
            do_recur(root->rnode, level);
            strcat(PBuf, "]");
            break;

        case TN_DEREF:
            strcat(PBuf, "*");
            do_recur(root->lnode, level);
            if (root->rnode && (root->rnode->hdr.type == TN_IDENT))
              do_recur(root->rnode, level);
            else
            { strcat(PBuf, "(");
              do_recur(root->rnode, level);
              strcat(PBuf, ")");
            }
            break;

        case TN_SELECT:
            do_recur(root->lnode, level);
            strcat(PBuf, (root->hdr.tok == ARROW)? "->" : ".");
            do_recur(root->rnode, level);
            break;

        case TN_ASSIGN:
            do_recur(root->lnode, level);
            strcat(PBuf, toksym(root->hdr.tok,1));
            do_recur(root->rnode, level);
            break;

        case TN_EXPR:
            switch (root->hdr.tok) {
              case CASE:
                strcat(PBuf, toksym(root->hdr.tok,1));
                do_recur(root->lnode, level);
                do_recur(root->rnode, level);
                break;

              case SIZEOF:
                strcat(PBuf, toksym(root->hdr.tok,0));
                strcat(PBuf, "(");
                do_recur(root->lnode, level);
                do_recur(root->rnode, level);
                strcat(PBuf, ")");
                break;

              case INCR:
              case DECR:
                do_recur(root->lnode, level);
                strcat(PBuf, toksym(root->hdr.tok,1));
                do_recur(root->rnode, level);
                break;

              case B_AND:
                if (root->lnode == NULL) {
                  strcat(PBuf, toksym(root->hdr.tok,1));
                  strcat(PBuf, "(");
                  do_recur(root->rnode, level);
                  strcat(PBuf, ")");
                  break;
                }

              default:
                strcat(PBuf, "(");
                do_recur(root->lnode, level);
                strcat(PBuf, toksym(root->hdr.tok,1));
                do_recur(root->rnode, level);
                strcat(PBuf, ")");
                break;
            }
            break;

        case TN_WHILE:
            strcat(PBuf, "while (");
            do_recur(root->lnode, level);
            strcat(PBuf, ")\n");
            do_recur(root->rnode, level+1);
            break;

        case TN_DOWHILE:
            strcat(PBuf, "do\n");
            do_recur(root->rnode, level+1);
            if ((root->rnode->hdr.type == TN_STEMNT)
                    && (root->rnode->rnode->hdr.type != TN_BLOCK))
                strcat(PBuf, ";");
            strcat(PBuf, "\n");
            indented(level);
            strcat(PBuf, "while (");
            do_recur(root->lnode, level);
            strcat(PBuf, ")");
            break;

        case TN_LABEL:
            do_recur(root->lnode, level);
            if (root->lnode && (root->lnode->hdr.type != TN_LABEL))
              strcat(PBuf, ":\n");
            do_recur(root->rnode, level);
            break;

        case TN_EMPTY:
        default:
            fprintf(stderr, "%s: Unknown type of tree node (%d).\n",
		progname, root->hdr.type);
            break;
        }
        break;
    }
}

void
print_recur(treenode *root, FILE *fp)
{
	can_flush = fp;
	strcpy(PBuf, "");
	do_recur(root, 0);
	fprintf(fp, "%s", PBuf);
	can_flush = (FILE *) 0;
}

char *
print2buf(treenode *root)
{	// small fragments
	strcpy(PBuf, "");
	do_recur(root, 0);
	return PBuf; // read only
}

void
print_tree(treenode *root, FILE *fp)
{
	print_recur(root, fp);
}

void
wrapper(treenode *root)
{
	do_recur(root, 0);
}
