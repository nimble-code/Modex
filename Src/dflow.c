/***** modex: dflow.c *****/

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

extern int	Verbose, allprocs, preview;
extern int	visu, show_funcs;
extern char	*want, *progname;

       void	bugger(char *, treenode *, int);
extern char	*e_malloc(unsigned int);
extern char	*x_stmnt(treenode *);
extern int	find_symbol(scopetab_t *, symentry_t *);
extern symentry_t *new_symentry(void);

static char SaveMe[1024];

char	*Fct_name;
int	RealDecls;
DuG	*du_g;

char *
doit(leafnode *leaf, int how)
{	scopetab_t *z;
	static char bstr[1024];
	static char lstr[1024];

	if (!leaf) return (char *) 0;

	if (leaf->syment && leaf->syment->nes)
		z = leaf->syment->nes;
	else
		z = (scopetab_t *) 0;

	strcpy(lstr, "");
	switch (how) {
	case 2:	sprintf(bstr, "%d:", leaf->hdr.line);
		strcat(lstr, bstr);	/* fall thru */
	case 0:	sprintf(bstr, "%s::", z?z->owner:"-");
		strcat(lstr, bstr);	/* fall thru */
	case 1:	sprintf(bstr, "%s%s", nmestr(leaf->data.sval), (!how)?" ":"");
		strcat(lstr, bstr);
	}
	return &lstr[0];
}

DuG *
dep_node(SymList *a, int imark)
{	DuG *g;

	for (g = du_g; g; g = g->nxt)
		if (g->sm == a->sm)
		{	g->marks |= imark;
			goto done;
		}

	g = (DuG *) e_malloc(sizeof(DuG));

	if (!a->sm) printf("%s: dep_node without symbol\n", progname);

	g->sm = a->sm;
	g->marks = imark;
	g->rdcls |= RealDecls;
	g->d_e = (DuGP *) 0;
	g->nxt = du_g;
	du_g = g;
done:
	return g;
}

int
dep_edge(DuG *a, DuG *b, int dist)
{	DuGP *e;

	if (a->sm == b->sm)
		return 0;		/* self-loop */

	for (e = a->d_e; e; e = e->nxt)
	{	if (e->ptr == b)
			return 0;	/* already there */
	}

	e = (DuGP *) e_malloc(sizeof(DuGP));
	e->ptr = b;
	e->dist = dist;
	e->nxt = a->d_e;
	a->d_e = e;

	return 1;
}

void
dep_trans(void)	/* transitive closure */
{	DuG *g, *t;
	DuGP *s, *u;
	int dist, cnt;

	do {	cnt = 0;
		for (g = du_g; g; g = g->nxt)
		for (s = g->d_e; s; s = s->nxt)			/* successors */
		{	t = s->ptr;				/* one successor in DuG */
			for (u = t->d_e; u; u = u->nxt)		/* the successors of this */
			{	dist = s->dist + u->dist;
				if (dep_edge(g, u->ptr, dist))
					cnt++;
			}
		}
	} while (cnt > 0);
}

void
dep_warn(int m)
{
	if (!(m&DEF) || !(m&USE))
	{
		if (!(m&DEF))
			fprintf(stdout, "\t%snever defined",
				(m&USE)?"used but ":"never used and ");
		else if (!(m&USE))
			fprintf(stdout, "\tdefined but never used");
	}
	fprintf(stdout, "%s\n", (m&HIDE)?" hidden":"");
}

void
dep_show(void)
{	DuG  *g;
	DuGP *s;

	dep_trans();
	fprintf(stdout, "\n");

	for (g = du_g; g; g = g->nxt)
	{	if (!g->d_e
		||  !g->rdcls)
			continue;

		fprintf(stdout, "%s:\n", g->sm->nme->str);
		for (s = g->d_e; s; s = s->nxt)
			fprintf(stdout, "\t-%s-> %s\n",
				(s->dist>1)?"*":"",
				s->ptr->sm->nme->str);
	}
	fprintf(stdout, "\n");

	for (g = du_g; g; g = g->nxt)
	{	if (!g->marks
		||  !g->rdcls
		|| (!(Verbose&2) && (g->marks&HIDE)))
			continue;

		if (!(g->marks&DEF)
		||  !(g->marks&USE))
		{

			if (g->sm
			&&  find_symbol(g->sm->nes, g->sm))
			{	fprintf(stdout, " %s", g->sm->nme->str);
				dep_warn(g->marks);
			}	/* else it's not a reportable item */
		}
	}
}

void
dep_graph(DefUse *d)
{	SymList *s, *t;
	DuG *a, *b;

	if (!d || preview) return;

	if (!d->def)
	for (t = d->use; t; t = t->nxt)
		dep_node(t, USE);

	for (s = d->def; s; s = s->nxt)
	{	a = dep_node(s, DEF);
		for (t = d->use; t; t = t->nxt)
		{	b = dep_node(t, USE);
			if (s->sm != t->sm)
				dep_edge(a, b, 1);
		}
	}
}

void
mark_defs(DefUse *d, int how, FILE *fp)	/* how=0: keep or map, HIDE: comment, print or hide */
{	SymList *s;
	DuG *g;

	for (s = d->def; s; s = s->nxt)
	for (g = du_g; g; g = g->nxt)
		if (g->sm == s->sm)
		{
			if ((g->marks & (DEF|(how&~HIDE))) != (DEF|(how&~HIDE)))
				fprintf(fp, "markdefs:%s: %d <-> %d | %d\n",
					g->sm->nme->str, g->marks, DEF, (how&~HIDE));
			g->marks |= (DEF|how);
		}

	for (s = d->use; s; s = s->nxt)
	for (g = du_g; g; g = g->nxt)
		if (g->sm == s->sm)
		{
			if ((g->marks & USE) != USE)
				fprintf(fp, "markdefs:%s: %d <-> %d\n",
					g->sm->nme->str, g->marks, USE);
			g->marks |= USE;	/* no hide's here */
		}
}

void
dump_defuse(DefUse *d, FILE *fp)
{	SymList *s;

	if (!d) return;

	if (d->def)
	{	fprintf(fp, "[D: ");
		for (s = d->def; s; s = s->nxt)
			fprintf(fp, "%s ", s->sm->nme->str);
		fprintf(fp, "] ");
	}
	if (d->use)
	{	fprintf(fp, "[U: ");
		for (s = d->use; s; s = s->nxt)
			fprintf(fp, "%s ", s->sm->nme->str);
		fprintf(fp, "] ");
	}
	if (d->other)
	{	fprintf(fp, "[O: ");
		for (s = d->other; s; s = s->nxt)
		{	fprintf(fp, "%s=", s->sm->nme->str);
			if (s->mark & DEF)	fprintf(fp, "D");
			if (s->mark & USE)	fprintf(fp, "U");
			if (s->mark & FCALL)	fprintf(fp, "F");
			if (s->mark & (REF0|REF1)) fprintf(fp, "r");
			if (s->mark & REF2)	fprintf(fp, "R");
			if (s->mark & DEREF)	fprintf(fp, "*");
			if (s->mark & ALIAS)	fprintf(fp, "&");
			if (s->mark & ARRAY_DECL)	fprintf(fp, "A");
			if (s->mark & HIDE)	fprintf(fp, "H");
			if (s->mark & DECL)	fprintf(fp, "T");

			if (s->mark & USEafterdef)	fprintf(fp, "Ua");
			if (s->mark & USEbeforedef)	fprintf(fp, "Ub");
			if (s->mark & PARAM)	fprintf(fp, "P");

		/*	fprintf(fp, " <%d>", s->sm->decl_level);	*/
			fprintf(fp, " ");
		}
		fprintf(fp, "] ");
	}
}

static int
same_defuse(DefUse *a, DefUse *b)
{	SymList *s, *t;

	if (!a && !b)
		return 1;
	if (!a || !b)
		return 0;

	for (s = a->def, t = b->def; s && t; s = s->nxt, t = t->nxt)
		if (s->sm != t->sm)
			return 0;
	if (s || t)
		return 0;
	for (s = a->use, t = b->use; s && t; s = s->nxt, t = t->nxt)
		if (s->sm != t->sm)
			return 0;
	if (s || t)
		return 0;

	for (s = a->other, t = b->other; s && t; s = s->nxt, t = t->nxt)
		if (s->sm != t->sm
		||  s->mark != t->mark)
			return 0;

	if (s || t)
		return 0;
	return 1;
}

void
attach_defuse(treenode *n, char *t, DefUse *d)
{
	if (!d || !n) return;

	if (d->def || d->use)
		dep_graph(d);	/* update the graph */

	if (n->hdr.defuse)
	{	if (n->hdr.defuse != d
		&&  !same_defuse(d, n->hdr.defuse))
		{	printf("%s: %s:%d attach_defuse conflict %s %s\n",
				progname, n->hdr.fnm, n->hdr.line,
#ifdef DEFTYP
				n->hdr.deftyp,
#else
				"",
#endif
				t);
			printf("OLD:\n");
			dump_defuse(n->hdr.defuse, stdout);
			printf("\nNEW:\n");
			dump_defuse(d, stdout);
			printf("\n");
		}
	} else
	{	n->hdr.defuse = d;
#ifdef DEFTYP
		n->hdr.deftyp = t;
#endif
	}
}

static SymList *freesyml;
static SymList *allsym;

SymList *
symadd(symentry_t *sm, int mark)
{	SymList *sl;

	if (freesyml)
	{	sl = freesyml;
		freesyml = freesyml->all;
		memset(sl, 0, sizeof(SymList));
	} else
		sl = (SymList *) e_malloc(sizeof(SymList));

	sl->nxt = (SymList *) 0;
	sl->mark = mark;
	sl->sm  = sm;

	sl->all = allsym;
	allsym = sl;

	return sl;
}

static SymList *
merge_syms(SymList *s1, SymList *s2)
{	SymList *s, *t, *ns;
	SymList *add_to_s1 = (SymList *) 0;
	SymList *last_in   = (SymList *) 0;

	/* static int mcnt=1; */

	if (!s1) return s2;
	if (!s2) return s1;
#if 0
	printf("merge%d:\t", mcnt++);
	for (t = s1; t; t = t->nxt)
	printf("%s, ", t->sm->nme->str);
	printf("\nand:\t");
	for (t = s2; t; t = t->nxt)
	printf("%s, ", t->sm->nme->str);
	printf("\n\n");
	/* if (mcnt > 11) abort(); */
#endif

	for (t = s2; t; t = t->nxt)
	{	for (s = s1; s; s = s->nxt)
			if (s->sm == t->sm
			&&  s->mark == t->mark)
				break;

		if (!s) /* add t */
		{	ns = symadd(t->sm, t->mark);
			/* preserve relative order */
			if (!last_in)
				add_to_s1 = last_in = ns;
			else
			{	last_in->nxt = ns;
				last_in = ns;
			}
	}	}

	if (!last_in)
		return s1;

	last_in->nxt = s1;
	s1 = add_to_s1;
	return s1;
}

static DefUse *
merge_lists(DefUse *d1, DefUse *d2)
{	DefUse *nd;

	if (!d1) return d2;
	if (!d2) return d1;

	nd = (DefUse *) e_malloc(sizeof(DefUse));
	if (!preview)
	{	nd->def   = merge_syms(d1->def, d2->def);
		nd->use   = merge_syms(d1->use, d2->use);
	}
	nd->other = merge_syms(d1->other, d2->other);

	return nd;
}

static int
def_and_use(int tok)
{
	switch (tok) {
	case PLUS_EQ:
	case MINUS_EQ:
	case STAR_EQ:
	case DIV_EQ:
	case MOD_EQ:
	case B_NOT_EQ:
	case B_AND_EQ:
	case B_OR_EQ:
	case B_XOR_EQ:
	case L_SHIFT_EQ:
	case R_SHIFT_EQ:
		return 1;
	}
	return 0;
}

static char ref1_pref[1024];

static char *
set_u(struct symentry *x, char *nu)
{	char *u;

	if (!Fct_name) goto isglob;

	if (!x)
	{	u = (char *) e_malloc(strlen(nu)+strlen(Fct_name)+1-1);
		sprintf(u, "%s%s", Fct_name, &nu[1]);
	} else if (x->decl_level == 0)
	{	u = (char *) e_malloc(strlen(nu)+strlen("fct")+1-1);
		sprintf(u, "%s%s", "fct", &nu[1]);
	} else if (x->decl_level == 3)	/* is local */
	{	u = (char *) e_malloc(strlen(nu)+strlen(Fct_name)+1-1);
		sprintf(u, "%s%s", Fct_name, &nu[1]);
	} else	/* extern 1 or global 2 */
	{
isglob:		u = (char *) e_malloc(strlen(nu)+strlen("glob")+1-1);
		sprintf(u, "%s%s", "glob", &nu[1]);
	}
	return u;
}

typedef struct Fbase {
	char *nm;
	int   ln;
	struct Fbase *fcalls;
	struct Fbase *nxt;
} Fbase;

Fbase *fbase;

void
set_fbase(int ln, char *s)
{	Fbase *f;

	if (!show_funcs) fbase = (Fbase *) 0;

	f = (Fbase *) e_malloc(sizeof(Fbase));
	f->nm = (char *) e_malloc(strlen(s)+1);
	strcpy(f->nm, s);
	f->ln = ln;
	f->fcalls = (Fbase *) 0;
	f->nxt = fbase;
	fbase = f;
}

static void
add_fbase(int ln, char *s)
{	Fbase *f, *g;

	if (!visu && !show_funcs) return;

	if (!fbase)
		set_fbase(0, want);

	f = (Fbase *) e_malloc(sizeof(Fbase));
	f->nm = (char *) e_malloc(strlen(s)+1);
	strcpy(f->nm, s);
	f->ln = ln;
	f->nxt = f->fcalls = (Fbase *) 0;

	for (g = fbase->fcalls; g; g = g->fcalls)
		if (strcmp(g->nm, s) == 0)	/* follows a match */
		{	f->fcalls = g->fcalls;
			g->fcalls = f;
			return;
		}

	f->fcalls = fbase->fcalls;	/* or at the front */
	fbase->fcalls = f;
}

void
act_fcall(FILE *fd, Fbase *f)
{
	if (!f) return;
	act_fcall(fd, f->fcalls);

	if (!f->fcalls
	||  strcmp(f->fcalls->nm, f->nm) != 0)
		fprintf(fd, "\n	%s\t", f->nm);
	fprintf(fd, "%d ", f->ln);
}

void
act_fbase(FILE *fd, Fbase *f)
{
	if (!f) return;
	act_fbase(fd, f->nxt);

/*	fprintf(fd, "%s	%d", f->nm, f->ln);	*/
	act_fcall(fd, f->fcalls);	/* reverse order */
	fprintf(fd, "\n");
}

void
show_fbase(FILE *fd)
{
	act_fbase(fd, fbase);	/* reverse order */
}

void
storefname(treenode *child)
{
	strcpy(SaveMe, "");
	bugger(SaveMe, child->lnode, 1);
	add_fbase(child->hdr.line, SaveMe);
}

void
dflow_mark(FILE *fd, int mark)
{	int i;

	for (i = 1; i <= ANY; i *= 2)
		switch (mark&i) {
		case   DEF: fprintf(fd, "DEF "); break;
		case FCALL: fprintf(fd, "FCALL "); break;
		case   USE: fprintf(fd, "USE "); break;
		case  REF0: fprintf(fd, "REF0 "); break;
		case  REF1: fprintf(fd, "REF1 "); break;
		case  REF2: fprintf(fd, "REF2 "); break;
		case DEREF: fprintf(fd, "DEREF "); break;
		case ALIAS: fprintf(fd, "ALIAS "); break;
		case ARRAY_DECL: fprintf(fd, "ARRAY_DECL "); break;
		case HIDE: fprintf(fd, "HIDE "); break;
		case DECL: fprintf(fd, "DECL "); break;
		case USEafterdef: fprintf(fd, "USEafterdef "); break;
		case USEbeforedef: fprintf(fd, "USEbeforedef "); break;
		case PARAM: fprintf(fd, "PARAM "); break;
		}
}

static void
sym_babble(leafnode *leaf, unsigned long mark)
{	char *q = "--";
	scopetab_t *s = (scopetab_t *) 0;

	if (!leaf) return;

	if (leaf->syment
	&&  leaf->syment->nes)
		s = leaf->syment->nes;	/* name enclosing scope */

	fprintf(stdout, "%3d, %s::%s\t",
		leaf->hdr.line, s?s->owner:"-",
		nmestr(leaf->data.sval));
	if (s)
	switch (s->owner_t) {
	case TN_OBJ_DEF: q = "struct/union"; break;
	case TN_FUNC_DEF: q = "fnct"; break;
	}

	fprintf(stdout, "(%s) ", q);
	dflow_mark(stdout, mark);

	if (s && leaf->syment)
	{	find_symbol(leaf->syment->nes, leaf->syment);
		if (s->owner_t == TN_OBJ_DEF)
			printf(" prior use: %d",
				leaf->syment->used);
	}
	fprintf(stdout, "\n");
}

DefUse *
walk_tree(treenode *child, unsigned long markin)
{	leafnode *leaf;
	if_node *ifn;
	for_node *forn;
	unsigned long mark = markin;
	DefUse *d1 = (DefUse *) 0;
	DefUse *d2 = (DefUse *) 0;
	char *u = "";	/* first bug found by uno 8/9/2001 */
	char *nu;

	if (0 && child)
	{	printf("%s\t", name_of_node(child->hdr.type));
		dflow_mark(stdout, markin);
		printf("\n");
	}

	if (child)
	switch (child->hdr.which) {
	case NONE_T:
		break;
	case LEAF_T:
		leaf = (leafnode *) child;
		if (leaf->hdr.type == TN_IDENT)
		{
			if (0 || (Verbose&2))
				sym_babble(leaf, mark);

			if (leaf->syment)
				leaf->syment->used = 1;

			if (!leaf->syment
			&&  preview && mark
			&&  leaf->data.sval)
			{	symentry_t *t;

				t = new_symentry();
				t->nme = leaf->data.sval;
				t->node = child;
				t->fn = child->hdr.fnm;
				t->used = 1;
				leaf->syment = t;
				goto go4it;
			}

			if (!leaf->syment
			||  is_typedef(leaf->syment)
			||  (leaf->syment->nes
			&&   leaf->syment->nes->owner_t == TN_OBJ_DEF))	/* ?? */
			{
				if (0 || (Verbose&2))
				{	fprintf(stdout, "--tn_ident - %s -- mark %d\n",
						nmestr(leaf->data.sval), (int) mark);
					if (!leaf->syment)
						fprintf(stdout, "\tignored (zero syment)\n");
					else if (!leaf->syment->nes)
						fprintf(stdout, "\tignored (zero syment->nes)\n");
					else
						fprintf(stdout, "\tignored (%d==%d)\n",
						leaf->syment->nes->owner_t, TN_OBJ_DEF);
				}
				return (DefUse *) 0; /* defuse info not relevant */
			}
			if (0)
			{
			fprintf(stdout, "--TN_ident - %s -- mark %d - decl_level %d\t",
			nmestr(leaf->data.sval), (int) mark, leaf->syment->decl_level);
			dflow_mark(stdout, mark);
			printf("\n");
			}

			if (!mark)
			{	if (0) fprintf(stdout, "no mark -- ");
				if (0) fprintf(stdout, "%d:%s\n",
					leaf->hdr.line, nmestr(leaf->data.sval));

				if (Verbose&2) printf("using default mark\n");

				mark |= USE;	/* expr with 1 ident */
			}

			if (mark&(REF0|REF1|REF2))
			{
				if (0) fprintf(stdout, "saw a %s: %s\n",
					(mark&REF1)?"ref1":"ref2", doit(leaf, 0));

				if (mark&(REF1|REF0))	/* lhs of struct reference: ref0->x, ref1.x */
				{	strcat(ref1_pref, doit(leaf, 1));
				} else if (mark&REF2)	/* rhs of struct reference: x->ref2, x.ref2 */
				{	strcat(ref1_pref, doit(leaf, 1));
				}

				if (leaf
				&&  leaf->syment
				&&  leaf->syment->nes
				&&  leaf->syment->nes->owner)
				{	if (leaf->syment->nes->owner[0]  == '-')
						u = set_u(leaf->syment, u);
					else
					{	u = (char *) e_malloc(strlen(leaf->syment->nes->owner)
								+strlen(ref1_pref)+2+1);
						strcpy(u, leaf->syment->nes->owner);
					}
				} else
				{	u = (char *) e_malloc(1+strlen(ref1_pref)+2+1);
					strcpy(u, "-");
				}
				strcat(u, "::");
				strcat(u, ref1_pref);

				strcpy(ref1_pref, "");
				goto go4it;
			} else
			{	nu = doit(leaf, 0);
				if (nu[0] == '-')
				{	u = set_u(leaf->syment, nu);
				} else
				{	u = (char *) e_malloc(strlen(nu)+1);
					strcpy(u, nu);
				}
go4it:
 if (0)
 {	printf("WT %s:%d\t%s\t",
		child->hdr.fnm,
		child->hdr.line,
		nmestr(leaf->data.sval));

	dflow_mark(stdout, mark);

	if (leaf->syment)
	printf("\t(owner %s) -- (%s)\n", x_stmnt(leaf->syment->container), u);
}
				d1 = (DefUse *)  e_malloc(sizeof(DefUse));
				if (preview)
				{	if (mark)
					d1->other = symadd(leaf->syment, mark);
				} else
				{	d1->special = 0;

					if (!(mark&FCALL)
					&&  strncmp(u, "fct", strlen("fct")) != 0)
					{
						if ((mark&USE) && !(mark&ALIAS))
							d1->use   = symadd(leaf->syment, mark);
						if ((mark&DEF) && !(mark&DEREF))
							d1->def   = symadd(leaf->syment, mark);
						if (mark&(DEREF|ALIAS|DECL|ARRAY_DECL))
							d1->other = symadd(leaf->syment, mark);
					}
			}	}
 if (0) {
	fprintf(stderr, "tn_ident - %s -- mark %d\t", nmestr(leaf->data.sval), (int) mark);
	dump_defuse(d1, stderr);
	fprintf(stderr, "\n");
 }
			return d1;
		}

		break;

	case IF_T:
		ifn = (if_node *) child;
		switch (ifn->hdr.type) {
		case TN_IF:
			d1 = walk_tree(ifn->cond, mark|USE);
			attach_defuse(ifn->cond, "if_cond", d1);	/* was child i.s.o. ifn->cond */
			d2 = walk_tree(ifn->then_n, mark);
			d1 = merge_lists(d1, d2);
			d2 = walk_tree(ifn->else_n, mark);
			break;
		case TN_COND_EXPR:
			d1 = walk_tree(ifn->cond, mark|USE);
			d2 = walk_tree(ifn->then_n, mark);
			d1 = merge_lists(d1, d2);
			d2 = walk_tree(ifn->else_n, mark);
			/* alas an uninit var in the else branch can be
			   obscured by an assign in the then branch */
			d1 = merge_lists(d1, d2);
			attach_defuse(child, "c_expr", d1);
			return d1;
		default:
			fprintf(stderr, "cannot happen - bad if_t\n");
			exit(1);
		}
		break;

	case FOR_T:	/* either a function or a for-loop */
		RealDecls++;
		forn = (for_node *) child;
		d1 = walk_tree(forn->init, mark);
		if (forn->hdr.type == TN_FUNC_DEF)
			d2 = walk_tree(forn->test, mark);
		else
			d2 = walk_tree(forn->test, mark|USE);
		if (forn->hdr.type == TN_FOR)
			attach_defuse(forn->test, "cond", d2);
		d1 = merge_lists(d1, d2);
		d1 = merge_lists(d1, walk_tree(forn->incr, mark));
		d2 = walk_tree(forn->stemnt, mark);	/* body */
		RealDecls--;
		break;

	case NODE_T:
		switch(child->hdr.type){
		case TN_FUNC_DECL:	/* name on lnode, params on rnode */
			if (child->lnode
			&&  child->lnode->hdr.which == LEAF_T
			&&  child->lnode->hdr.type == TN_IDENT)
				Fct_name = nmestr(((leafnode *)(child->lnode))->data.sval);

			if (RealDecls
			&& (allprocs || strcmp(Fct_name, want) == 0))
			{	if (visu || show_funcs)
					set_fbase(child->hdr.line, Fct_name);
				if (0) fprintf(stdout, "%3d: %s\n",
					child->hdr.line, Fct_name);
			}
			d1 = walk_tree(child->rnode, mark|DEF|PARAM);
			attach_defuse(child, "decl1", d1);
			return d1;

		case TN_DECLS:
			d1 = walk_tree(child->lnode, mark|DECL);
			d2 = walk_tree(child->rnode, mark|DECL);
			d1 = merge_lists(d1, d2);
			attach_defuse(child, "decls", d1);
			return d1;

		case TN_DECL:
			if (!child->lnode) break;	/* prototype */
			if (child->lnode->hdr.type == TN_PNTR)
				d1 = walk_tree(child->rnode, mark|DEREF|DECL);
			else /* lnode has type information only */
				d1 = walk_tree(child->rnode, mark|DECL);

			attach_defuse(child, "decl2", d1);
			return d1;

		case TN_ARRAY_DECL:
			d1 = walk_tree(child->lnode, mark|ARRAY_DECL); /* base name */
			d2 = walk_tree(child->rnode, USE);
			d1 = merge_lists(d1, d2);
			attach_defuse(child, "decl3", d1);
			return d1;

		case TN_SELECT:	/* access of structure element */
			if (child->hdr.tok == ARROW)
			{	d1 = walk_tree(child->lnode, mark|REF0);
				strcat(ref1_pref, "->");
			} else
			{	d1 = walk_tree(child->lnode, mark|REF1);
				strcat(ref1_pref, ".");
			}
			d2 = walk_tree(child->rnode, mark|REF2);
			d1 = merge_lists(d1, d2);
			attach_defuse(child, "select", d1);
			return d1;

		case TN_CAST:	/* e.g.,: (void) fcall(args); */
			d1 = walk_tree(child->rnode, mark);
			attach_defuse(child, "cast", d1);
			return d1;

		case TN_FUNC_CALL:
			storefname(child);

			d1 = walk_tree(child->lnode, mark|FCALL);
			d2 = walk_tree(child->rnode, mark|USE);
			d1 = merge_lists(d1, d2);
			attach_defuse(child, "fnct", d1);
			return d1;

		case TN_EXPR:	
			switch (child->hdr.tok) {
			case INCR:
			case DECR:	/* either --x (rnode) or x-- (lnode) */
				/* for structs, only rightmost member gets DEF */

				if (child->rnode
				&&  child->rnode->hdr.type == TN_SELECT)
				{	if (child->rnode->hdr.tok == ARROW)
						d1 = walk_tree(child->rnode->lnode, mark|USE|REF0);
					else
						d1 = walk_tree(child->rnode->lnode, mark|USE|REF1);
					d2 = walk_tree(child->rnode->rnode, mark|USE|DEF|REF2);
					d1 = merge_lists(d1, d2);
					d2 = (DefUse *) 0;
				} else
					d1 = walk_tree(child->rnode, mark|DEF|USE);

				if (child->lnode
				&&  child->lnode->hdr.type == TN_SELECT)
				{	if (child->lnode->hdr.tok == ARROW)
						d1 = walk_tree(child->lnode->lnode, mark|USE|REF0);
					else
						d1 = walk_tree(child->lnode->lnode, mark|USE|REF1);
					d2 = walk_tree(child->lnode->rnode, mark|USE|DEF|REF2);
					d1 = merge_lists(d1, d2);
					d2 = (DefUse *) 0;
				} else
					d2 = walk_tree(child->lnode, mark|DEF|USE);

				d1 = merge_lists(d1, d2);

				attach_defuse(child, "incr", d1);
				return d1;

			case ALIGNOF:
			case SIZEOF:
				d1 = walk_tree(child->rnode, mark|PARAM);
				/* tag meant to avoid complaints on things like sizeof (*ptr) */
				attach_defuse(child, "sizeof", d1);
				return d1;

			case CASE:
				if (child->lnode)
				{	fprintf(stderr, "%s: unexpected lnode, case\n", progname);
					d1 = walk_tree(child->lnode, mark);
					d2 = walk_tree(child->rnode, mark|USE);
					d1 = merge_lists(d1, d2);
				} else
					d1 = walk_tree(child->rnode, mark|USE);
				attach_defuse(child, "case", d1);
				break;

			case B_AND:
				if (child->lnode == NULL) /* aliasing - takes address of name */
					return walk_tree(child->rnode, mark|ALIAS);

				/* else part of an expression */
				mark |= USE;
				/* fall through */

			default:	/* all other forms of an expression */
				d1 = walk_tree(child->lnode, mark);
				d2 = walk_tree(child->rnode, mark);
				d1 = merge_lists(d1, d2);
				attach_defuse(child, "expr", d1);
#if 0
	printf("TN_EXPR: ");
	dump_defuse(d1, stdout);
	printf("\n");
#endif
				return d1;
			}
			break;

		case TN_SWITCH:
		case TN_WHILE:
		case TN_DOWHILE:
			d1 = walk_tree(child->lnode, mark|USE);	/* condition */
			attach_defuse(child->lnode, "cond", d1);
			d2 = walk_tree(child->rnode, mark);
			d1 = merge_lists(d1, d2);
			return d1;

		case TN_ASSIGN:
		{	int watch = 0;

			if (watch) printf("A - mark = %d -- %s\n", (int) mark, x_stmnt(child));

			if (def_and_use(child->hdr.tok))
			{
				d1 = walk_tree(child->lnode, mark|DEF|USE);
			}
			else
			{	int nmark = mark;

				if (watch) printf("B - mark = %d -- %s\n", nmark, x_stmnt(child->lnode));

				if (nmark&USE)
				{	nmark &= ~USE;
					nmark |= USEafterdef;
				}
				if (watch) printf("C - mark = %d -- %s -- lnode=%s\n",
					nmark, x_stmnt(child->lnode),
					name_of_node(child->lnode->hdr.type));
				d1 = walk_tree(child->lnode, nmark|DEF);
				if (watch) { printf("Bd1: "); dump_defuse(d1, stdout); printf("\n"); }
			}
			d2 = walk_tree(child->rnode, (mark&~DECL)|USE);

			if (watch)	{ printf("D1: "); dump_defuse(d1, stdout); printf("\n");
				  printf("D2: "); dump_defuse(d2, stdout); printf("\n");
				}

			d1 = merge_lists(d2, d1);	/* d1 after d2 */

			if (watch)	{ printf("D1+D2: "); dump_defuse(d1, stdout); printf("\n"); }

			attach_defuse(child, "asgn", d1);

			return d1;
		}

		case TN_DEREF:
			d1 = walk_tree(child->lnode, mark|DEREF);
			d2 = walk_tree(child->rnode, mark|DEREF);
			d1 = merge_lists(d1, d2);
			return d1;

		case TN_JUMP:
			if (child->hdr.tok != RETURN)
				goto out;	/* no var refs */
			d1 = walk_tree(child->lnode, mark|USE);
			attach_defuse(child, "return", d1);
			return d1;

		case TN_INDEX:
			d1 = walk_tree(child->lnode, mark | DEREF);	/* indexing an array derefs basename */
			if (strlen(ref1_pref) > 0)
				strcat(ref1_pref, "[");
			d2 = walk_tree(child->rnode, (mark&(~(DEF|ALIAS|DEREF))));
			if (strlen(ref1_pref) > 0)
				strcat(ref1_pref, "]");
			d1 = merge_lists(d1, d2);
			return d1;

		case TN_TRANS_LIST:
			walk_tree(child->lnode, mark);
			walk_tree(child->rnode, mark);
			return d1;

		default:
			break;
		}
		d1 = walk_tree(child->lnode, mark);
		d2 = walk_tree(child->rnode, mark);
		break;
	}
out:
	return merge_lists(d1, d2);
}

void
bugger(char *store, treenode *root, int top)
{	leafnode *leaf;

	if (!root) return;

	switch (root->hdr.which) {
	case LEAF_T:
		leaf = (leafnode *) root;
		switch (leaf->hdr.type) {
		case TN_IDENT:
			strcat(store, leaf->data.sval->str);
			break;
		default:
			goto bad;
		}
		break;
	case NODE_T:
		switch (root->hdr.type) {
		case TN_SELECT:
			bugger(store, root->lnode, 0);
			if (root->hdr.tok == ARROW)
				strcat(store, "->");
			else
				strcat(store, ".");
			bugger(store, root->rnode, 0);
			break;
		case TN_FUNC_CALL:
			bugger(store, root->lnode, 0);
			strcat(store, "()");
			break;
		default:
			goto bad;
		}
		break;
	default:
bad:		strcat(store, "<unknown type>");
		break;
	}

	if (top) strcat(store, "()");
}
