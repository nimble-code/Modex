/***** modex: xtract.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */
/* Extensions (c) 2004-2014 by Caltech/JPL Pasadena, CA 91109             */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <ctype.h>
#include "prnttree.h"
#include "gram.h"
#include "symtab.h"
#include "modex_cpp.h"

#define Banner		"# Modex Lookup Table"
#define EnCode		"_P_E_R_C_E_N_T_"
#define NeCode		":P_E_R_C_E_N_T_"
#define ZN		(treenode *)0
#define ND_CHOICE	"rand("
#define NONPRINT	"hidden"
#define NONSTATE	"NonState"
#define BigEnough	4096
#define MAXLEVEL	64

#ifndef DEFAULT_LUT
	#ifdef PC
		#define DEFAULT_LUT	"c:/cygwin/usr/local/share/defaults.lut"
	#else
		#define DEFAULT_LUT	"/usr/local/modex/defaults.lut"
	#endif
#endif
#ifndef GLOBAL_LUT
	/* generated from an unnamed %L command */
	#define GLOBAL_LUT	"_modex_.lut"
#endif

typedef struct Cache {
	char *s;
	char *t;
	unsigned int udef, hit, printed;
	int level;
	struct Cache *nxt;
} Cache;

typedef struct Fcts {
	char	*nm;
	char	*tg;
	char	*dt;
	char	*full;
	int	purged;
	int	derived;
	int	wanted;
	int	level;	/* include level*/
	int	fc;	/* 1=fct name, 2=fct arg, 0=other */
	int	lno;
	struct Fcts *nxt;
} Fcts;

typedef struct PreC {
	treenode *n;
	struct PreC *nxt;
} PreC;

typedef struct NameL {
	char	*nm;
	int	purged;
	struct NameL *nxt;
} NameL;

typedef struct Decor {
	char *from;
	short ln;
	struct Decor *nxt;
} Decor;

typedef struct Spress {
	char	*vn;
	char	*pn;
	int	hit, mustgen;
	int	purged;
	struct	Spress *nxt;
} Spress;

static treenode *keep_pars;
static treenode **keep_root;

static int	decl_cnt, in_call, in_args, in_pars, is_label, check_type;
static int	just_left_blk;
static int	enum_list_cnt;
static int	taboffset;
static int	sawdefault, Down;
static int	FreshLut = 0, needreturn = 0, sawreturn = 0;
static int	ByPass = 0, PosElse = 0;
static char	fct_name[1024] = ":global:";
static char	fct_type[512] = "long";
static char	tbuf[BigEnough];
static char	Bounds[BigEnough];
static int	extra_comment;
static int	owf, owt, owe, owh;
static int	debug = 0;
static int	lastln, lastpb;
static int	pending = 0, import_all = 0;
static int	is_do_condition;

static char	OutBuf[BigEnough];	/* to save up text of 1 statement at a time */
static char	IntBuf[BigEnough];
static char	AltBuf[BigEnough];
static char	OrigBuf[BigEnough];
static char	Rem[BigEnough];		/* temp storage */
static char	Rem2[BigEnough];	/* temp storage */
static char	Rem3[BigEnough];	/* temp storage */
static char	Rem4[BigEnough];	/* temp storage */
static char	PreBuf[BigEnough];	/* precondition */
static char	c_file[512];		/* last .pml file */

static int	ishidden;
static int	wasfalse, wastrue, waselse, nreturns=0;
static FILE	*fp;
static int	linenr;

static Cache	*cache, *comms, *commstail;

static Fcts	*fcts, *maps, *incls;
static Fcts	*modex_globals;
static Fcts	*modex_hidden;
static Fcts	*modex_locals;
static Spress	*spress, *externals;
static PreC	*prec;
static NameL	*namel;
static NameL	*globchans;

static int do_level, sw_level, sw_first;
static int do_uniq, o_cnt;
static int nblanks = 0;
static char *DoLabel[MAXLEVEL];
static treenode *DoIncr[MAXLEVEL];
static char *SwLabel[MAXLEVEL];
static Decor *decors, *fdecors;

static char derscope[32];
static char dertype[512];
static char dername[512];
static char derproc[512];
static char Ldertype[512];
static char Ldername[512];
static int with_decorations;
static int ax_prop_nr = 0;

extern int vis, show_funcs, add_printfs;

extern char cur_in[];
extern char *VERSION;
extern char o_base[512];
extern char *suffix, *progname;
extern char *want, *wanttype;
extern int nostructs;
extern int new_lut, Verbose, Verbose_cmds, printall, fallout, show_deps;
extern int Warnings, allprocs, suppress, i_assert;
extern int use_c_code, allkeep, globals_only, dynamic;
extern int omissions, redundancies, do_inc_locals, do_inc_globals;
extern int extended, preview, flike, used_spin_malloc, spin_heap_size;

extern int du_mode;	/* TRIAL */

static void handle_fct(treenode *, int);
static void modex_if(if_node *,    int);
static void modex_for(for_node *,  int);
static void modex_any(treenode *,  int);
static void modex_node(treenode *, int);
static void modex_recur(treenode *);
static void vis_direct(char *);
static void do_externals(FILE *);
static int precomputable(treenode *);
extern char *toksym(int tok, int white);
extern void find_typedefs(scopetab_t *, FILE *);

#if 0
extern void debug_node(treenode *, int, char *);
#endif

int	imported(char *, char *, int);
void	print_recur(treenode *, FILE *);
symentry_t  *find_glob_symentry(scopetab_t *, char *);
void	add_imported(char *, char *, int);
void	ax_doprops(FILE *, scopetab_t *);
void	ax_new_assert(const int, treenode *);
void	dotree(treenode *, int, int);
void	dump_defuse(DefUse *, int, FILE *);
void	mark_defs(DefUse *, int, FILE *);
void	set_fbase(int, char *);
void	show_fbase(FILE *);
void	storefname(treenode *);
void	vis_indent(int, char *);
void	x_scopetab(scopetab_t *, FILE *, char *);
void	*e_malloc(unsigned int);

extern void	add_constant(char *, int);
extern void	add_icall(char *);
extern int	is_constant(char *);
extern int	is_icall(char *);
extern int	is_pname(char *);
extern void	do_constants(FILE *);
extern void	bugger(char *, treenode *, int);
extern void	Fclose(FILE *);

extern int debug_io;

struct {
	char *pat;	char *val;
} deflts[] = {
	{ "case ",	"keep" },	/* condition */
	{ "default:",	"keep" },	/* condition */
	{ "C: ",	"true"  },	/* condition */

	{ "D: ",	"hide" },

	{ "A: ",	"comment" },
	{ "F: ",	"comment" },
	{ "I: ",	"comment" },	/* remove? */

	{ "",		"print" },	/* everything else */

	{ 0,		0 }
};

char tempfile_M[1024];

char *
x_stmnt(treenode *n)	/* service routine for lts.c */
{	char *p;

	if (!n) return "--";
	if (n->hdr.type == TN_STEMNT)
		return "<stmnt>";
	if (n->hdr.type == TN_BLOCK)
		return "<block>";

	fp = 0;
	do_level = 0;
	vis = 1;
	OutBuf[0] = '\0';
	modex_recur(n);
	vis = 0;
	for (p = OutBuf; *p != '\0'; p++)
		if (*p == '"') *p = '\'';

	return OutBuf;
}

extern char *rm_decor(char *);

char *
nx_stmnt(treenode *n)
{
	if (!n
	||  n->hdr.type == TN_STEMNT
	||  n->hdr.type == TN_BLOCK)
	{	return "";
	}

	do_level = 0;

	vis = 1;
	OutBuf[0] = '\0';
	modex_recur(n);
	vis = 0;

	strcpy(fct_name, "--");
	IntBuf[0] = '\0';

	return rm_decor(OutBuf);
}

#if 0
void
dep_dflts(FILE *sd)
{	int i;

	for (i = 0; deflts[i].pat; i++)
	{	fprintf(sd, "%s\t%s\n", deflts[i].pat, deflts[i].val);
	}
}
#endif
void
handle_lf(FILE *lf, char *s)
{	char *t, *v;

	v = s;
if (0)
	while ((t = strstr(v, "\\n")))
	{	if (t[2] == '"') break;
		*t = '\0';
		fprintf(lf, "%s", v);
		fprintf(lf, "\\\\n");
		*t = '_';
		v = t+strlen("\\n");
	}
	fprintf(lf, "%s", v);
}

void
handle_double(FILE *lf, char *s)
{	char *t, *v;

	v = s;
	while ((t = strstr(v, NeCode)) != NULL)
	{	*t = '\0';
		handle_lf(lf, v);
		fprintf(lf, "%%%%");
		*t = '_';
		v = t+strlen(NeCode);
	}
	handle_lf(lf, v);
}

void
handle_special(FILE *lf, char *s, char *last)
{	char *t, *v;

	if ((t = strstr(s, "%")) != NULL)
	{	if (*(t+1) != '%')
			return;	/* rogue % slipped through */
	}

	v = s;
	while ((t = strstr(v, EnCode)) != NULL)
	{	*t = '\0';
		handle_double(lf, v);
		fprintf(lf, "%%");
		*t = '_';
		v = t+strlen(EnCode);
	}
	handle_double(lf, v);

	fprintf(lf, "%s", last);
}

void
vis_direct(char *s)	/* the gateway for generated model code */
{
	if (vis
	&& fp
	&& s
	&& !globals_only
	&& !show_deps
	&& !new_lut)
	{	handle_special(fp, s, "");
		if (strstr(s, "goto Return"))
			sawreturn++;
	}

	tbuf[0] = '\0';
}

static void
add_comment(int nr, char *s)
{	Cache *d;

	if (strncmp(s, Banner, strlen(Banner)) == 0)
		return;

	d = (Cache *) e_malloc(sizeof(Cache));
	d->level = Down;
	d->s = (char *) e_malloc(strlen(s)+1);
	strcpy(d->s, s);
	d->hit = nr-1;	/* -1 correction */
	d->printed = 0;
	d->nxt = (Cache *) 0;
	if (!commstail)
		comms = commstail = d;
	else
	{	commstail->nxt = d;
		commstail = d;
	}
}

static void
replace_lut(char *r, char *t)
{	Cache *c;

	for (c = cache; c; c = c->nxt)
		if (strcmp(c->s, r) == 0
		&&  strlen(c->s) == strlen(r))
		{	c->t = (char *) e_malloc(strlen(t)+1);
			if (Verbose&2)
				printf("%s: replacing %s -> %s -> %s\n", progname, r, c->t, t);
			strcpy(c->t, t);
			return;
		}

	printf("%s: no lut entry for %s\n", progname, r);
}

void
add_decor(Decor *d)
{	Decor *f, *lf = (Decor *) 0;

	for (f = decors; f; lf = f, f = f->nxt)
		if (d->from < f->from)
		{	/* insert d before f */
			if (lf)
			{	d->nxt = f;
				lf->nxt = d;
			} else
			{	d->nxt = decors;
				decors = d;
			}
			return;
		}
	if (lf)
		lf->nxt = d;
	else
		decors = d;
}

void
new_decor(char *p, int n)
{	Decor *f;

	if (fdecors)
	{	f = fdecors;
		fdecors = f->nxt;
	} else
		f = (Decor *) e_malloc(sizeof(Decor));
	f->from = p;
	f->ln = (short) n;
	f->nxt = (Decor *) 0;
	add_decor(f);
}

char *
rm_decor(char *R)	/* strip "P...->"  and "now." decorations */
{	char *z, *y, *r;
	char patt[512];
	Decor *d;

	sprintf(patt, "Pp_%s->", fct_name);

	r = R;
	fdecors = decors;
	decors = (Decor *) 0;

	while ((z = strstr(r, patt)) != NULL)
	{	new_decor(z, strlen(patt));
		r = z+strlen(patt);
	}
	r = R;
	while ((z = strstr(r, "now.")) != NULL)
	{	new_decor(z, strlen("now."));
		r = z+strlen("now.");
	}
	if (!decors) return R;

	z = &IntBuf[0];
	y = R;

	if (0)
	{	for (d = decors; d; d = d->nxt)
			fprintf(stderr, "\t%d .. %d, %s\n",
				(int)(d->from - y), d->ln, d->from);
		fprintf(stderr, "\n");
	}
	for (d = decors; d; d = d->nxt)
	{	r = d->from;
		strncpy(z, y, (r-y));
		z += (r-y);
		y = r + d->ln; /* skip over decoration */
	}
	strcpy(z, y);

	if (0)
	{	fprintf(stderr, "in : %s\n", R);
		fprintf(stderr, "out: %s\n\n", IntBuf);
	}
	return &IntBuf[0];
}

static char *
look_lut(char *R, char *T, int ihit)
{	Cache *c, *d, *lc = (Cache *) 0;
	int m; char *y, *z = NULL;
	char r[1024];
	static char t[2048];	/* can be returned */

// if (strstr(R, "printf")) printf("LOOK_LUT %s %s %d\n", R, T, ihit);

	while (R[strlen(R)-1] == ' ')
		R[strlen(R)-1] = '\0';

	if (ihit) R = rm_decor(R);

	r[0] = t[0] = '\0';
	while ((z = strchr(R, '%')) != NULL)
	{	*z = '\0';
		strcat(r, R);
		*z = '%';
		strcat(r, EnCode);
		R = z+1;
	}
	while ((z = strchr(T, '%')) != NULL)
	{	*z = '\0';
		strcat(t, T);
		*z = '%';
		strcat(t, EnCode);
		T = z+1;
	}
	strcat(r, R);
	strcat(t, T);

	for (c = cache; c; lc = c, c = c->nxt)
	{
// a regular expression match on c->s would go here
		if ((z = strstr(c->s, "...")) != NULL)
		{	*z = '\0';
		}
		if (strncmp(c->s, r, strlen(c->s)) == 0)
		{	m = 0;
			if (z)
			{	if (Verbose&2)
				printf("%s: prefix match1 %s -> %s\n",
					progname, r, c->s);
			} else if (strlen(c->s) != strlen(r))
			{	m = 1;
			}
		} else
		{	m = 1;
		}

		if (z)
		{	*z = '.';
			z = NULL;
		}

		if (m == 0)
		{	c->hit++;
			goto done;
	}	}
// if (strstr(R,"printf")) printf("--<<%p>>\n", c);
#if 1
	y = strstr(r, ": ");
	if (y && ihit)
	{	y += strlen(": ");
		for (c = cache; c; c = c->nxt)
		{
// a regular expression match on c->s would go here
			if ((z = strstr(c->s, "...")) != NULL)
			{	*z = '\0';
			}
			if (strncmp(c->s, y, strlen(c->s)) == 0)
			{	c->hit++;
				if (z)
				{	if (Verbose&2)
					printf("%s: prefix match2 %s -> %s\n",
						progname, y, c->s);
					if (z) { *z = '.'; z = NULL; }

// if (strstr(R,"printf")) printf("--oh no\n");
					goto done;
				} else if (strlen(c->s) == strlen(y))
				{
// if (strstr(R,"printf")) printf("--Bingo\n");
					goto done;
			}	}
			if (z)
			{	*z = '.';
				z = NULL;
	}	}	}
#endif
// if (strstr(R,"printf")) printf("--A\n");

	if (ihit && allprocs)	/* avoid out-of-context matches */
	{
// if (strstr(R, "printf")) printf("R1	%s\n", t);
		return t;
	}

	d = (Cache *) e_malloc(sizeof(Cache));
	d->level = Down;
	d->s = (char *) e_malloc(strlen(r)+1);
	strcpy(d->s, r);
	d->t = (char *) e_malloc(strlen(t)+1);
	strcpy(d->t, t);
	d->udef = 1-ihit;	/* this field cannot change */
	d->hit = ihit;	/* this field can change */
	d->printed = 0;

	if (!lc)
	{	d->nxt = cache;
		cache = d;
// printf("Addded to cache1 <%s> <%s>\n", r, t);
	} else
	{	d->nxt = c;
		lc->nxt = d;
// printf("Addded to cache2 <%s> <%s>\n", r, t);
	}

	if (ihit && omissions)
	{	printf("Omission: ");
		handle_special(stdout, r, "\t");
		handle_special(stdout, t, "\n");
	}
	c = d;
done:
// if (strstr(R, "printf")) printf("R2	%s\n", c->t);
	return c->t;
}

void
add_fct(char *s, char *t)	/* names of fcts used in expressions */
{	Fcts *f;

	f = (Fcts *) e_malloc(sizeof(Fcts));
	f->nm = (char *) e_malloc(strlen(s)+1);
	strcpy(f->nm, s);
	f->level = Down;

	f->tg = (char *) e_malloc(strlen(t)+1);
	strcpy(f->tg, t);
	f->nxt = fcts;
	fcts = f;
}

void
add_include(char *s)
{	Fcts *f;

	f = (Fcts *) e_malloc(sizeof(Fcts));
	f->nm = (char *) e_malloc(strlen(s)+1);
	strcpy(f->nm, s);
	f->level = Down;

	f->nxt = incls;
	incls = f;
}

void
dump_fct(FILE *fd)
{	Fcts *f;

	for (f = fcts; f; f = f->nxt)
	{	if (f->level == 0)
		{	if (f->nm[0] != '(')
			fprintf(fd, "Function	%s\n", f->nm);
	}	}

	for (f = incls; f; f = f->nxt)
	{	if (f->level == 0)
			fprintf(fd, "Include	%s\n", f->nm);
	}
}

static Fcts *
modex_fct_el(char *s)
{	Fcts *f;

	f = (Fcts *) e_malloc(sizeof(Fcts));
	memset(f, 0, sizeof(Fcts));
	f->nm = (char *) e_malloc(strlen(s)+1);
	strcpy(f->nm, s);

	if (allprocs
	||  strcmp(fct_name, want) == 0)
		f->wanted = 1;

	if (in_call > 0) f->fc = 1;
	else if (in_args > 0) f->fc = 2;
	else if (is_label > 0) f->fc = 3;
	else f->fc = 0;

	return f;
}

void
add_substitute(char *s, char *t)	/* substitute rules defined in lut */
{	Fcts *f;

	if (strstr(t, s))
	{	fprintf(stderr, "%s: error: lhs of Substitute Rule may not appear on rhs\n",
			progname);
		return;
	}
if (0) fprintf(stderr, "map %s -> %s\n", s, t);

	f = modex_fct_el(s);
	f->level = Down;

	if (t)
	{	f->tg = (char *) e_malloc(strlen(t)+1);
		strcpy(f->tg, t);
	} else
		f->tg = (char *) 0;
	f->nxt = maps;
	maps = f;

	if (0) printf("Sub <%s> <%s>\n", s, t);
}

static char *
sep_decor(char *t, Fcts *g)
{	static char prep[512];

	if (strchr(t, '*')
	||  strchr(t, '['))	/* has decorations */
	{
		g->full = (char *) e_malloc(strlen(t)+1);
		strcpy(g->full, t);

		strcpy(prep, t);
		while ((t = strchr(prep, '*')) != NULL)
			*t = ' ';
		if ((t = strchr(prep, '[')) != NULL)
			*t = '\0';

		t = prep;
		while (isspace((int) *t))
			t++;
	}
	return t;
}

void
add_hidden(char *s, char *t, int d, int ln)
{	Fcts *g;

	if (strlen(s) == 0)
		return;

	for (g = modex_hidden; g; g = g->nxt)
		if (strcmp(g->dt, s) == 0
		&&  (strcmp(g->nm, t) == 0
		||   (g->full && strcmp(g->full, t) == 0)))
			return;

if (debug)
	fprintf(stderr, "%3d: add_hidden typ=%s nam=%s deriv=%d (incall=%d,inargs=%d,islabel=%d)\n",
		ln, s, t, d, in_call, in_args, is_label);

	g = modex_fct_el(s);
	g->dt = g->nm;
	g->derived = d;
	g->lno = ln;

	t = sep_decor(t, g);

	g->nm = (char *) e_malloc(strlen(t)+1);
	strcpy(g->nm, t);
if (debug)
	fprintf(stderr, "---name %s -- \n", t);

	g->tg = (char *) e_malloc(strlen(fct_name)+1);
	strcpy(g->tg, fct_name);	/* to record where we saw the reference */

	g->nxt = modex_hidden;
	modex_hidden = g;
}

void
add_global(char *s, char *t, int d, int ln)	/* s=type, t=varname, d=derived */
{	Fcts *g, *h; char *z;

if (0)	printf("::%3d: addglobal <%s> <%s> %d -- %d -- line %d\n",
			ln, s, t, d, with_decorations, ln);

	if (strncmp(s, "void", strlen("void")) == 0
	&& !strchr(s, '*')
	&& !strchr(t, '*'))	/* void star */
	{	return;
	}

	if (strncmp(s, "static", strlen("static")) == 0)
	{	s += strlen("static");	/* can't have this in State */
		while (*s == ' ' || *s == '\t')
			s++;
	}
if (0) { if (strcmp(t, "uint") == 0) abort(); }
	if (strlen(s) == 0
	||  strlen(t) == 0)
	{	return;
	}

if (0)
	printf("%3d: addglobal <%s> <%s> %d -- %d -- line %d\n",
			ln, s, t, d, with_decorations, ln);

	while (*t == ' ' || *t == '\t')
		t++;

	if (strncmp(s, "extern", strlen("extern")) == 0
	||  strncmp(t, "=", 1) == 0
/*	||  (strncmp(t, "*", 1) == 0 && d != 0) */ )	// llist example
	{	return;
	}

	if (strstr(s, "struct")
	&&  (z = strchr(s, '{')))	/* assign z */
	{
		do	z++;
		while (isspace((int) *z));
		if (*z == '}')	/* empty struct declaration */
			return;
	}

	g = modex_fct_el(s);
	g->dt = g->nm;
	g->lno = ln;
	t = sep_decor(t, g);

	if (strcmp(s, "unsigned unsigned ") == 0)
	{	s += strlen("unsigned ");
	}

	if (0)
		fprintf(stderr, "%3d:	 addglobal <%s> <%s> %d -- %d\n",
			ln, s, t, d, with_decorations);

	for (h = modex_globals; h; h = h->nxt)
	{	if (	/* strcmp(h->dt, s) == 0 &&	*/
		    strcmp(h->nm, t) == 0)
			return;
	}
	if (0) fprintf(stderr, "	ok\n");

	g->nm = (char *) e_malloc(strlen(t)+1);
	strcpy(g->nm, t);
	g->derived = d;

	g->nxt = modex_globals;
	modex_globals = g;
}
void
add_full_global(char *s, char *t, int derived, int ln)
{	Fcts *g;
	char *z;
	int cnt = 0;

	if (strlen(s) == 0
	||  strlen(t) == 0)
		return;

if (0)
	printf("addfullglobal <%s> <%s> derived %d, ln %d\n",
		s, t, derived, ln);

tryagain:
	for (g = modex_globals; g; g = g->nxt)
		if (	/* strcmp(g->dt, s) == 0 &&	*/
		   (z = strstr(t, g->nm)))
		{
			if ((z == t
			&&  (*(z+strlen(g->nm)) == '['
			||   *(z+strlen(g->nm)) == ']'
			||   *(z+strlen(g->nm)) == '\0'
			||   *(z+strlen(g->nm)) == ' '))
			||  (*(z-2) == '*' && *(z-1) == ' '))
			{
				if (g->full
				&&  strcmp(g->full, t) == 0)
					return;

				if (Verbose&2)
					printf("add_full_global %s %s (%s)\n",
					s, t, g->full);

				g->full = (char *) e_malloc(strlen(t)+1);
				strcpy(g->full, t);

				if  (g->full[strlen(g->nm)] == ']')
				{	g->full[strlen(g->nm)] = '\0';
				}
				return;
			}
		}
if (0)
	printf("%s: add_full_global not-found: <%s> <%s> <%d>\n", progname, s, t, cnt);

	if (cnt++ == 0)
	{	add_global(s, t, derived, ln);
		goto tryagain;
	}
}

char *
which_var(char *s)
{	Fcts *g;
	char *x, *y, *z;
	int i;

	if (strlen(s) == 0)
		return (char *) 0;

	for (g = modex_locals; g; g = g->nxt)
		if (strcmp(g->nm, s) == 0
		&&  strcmp(g->tg, fct_name) == 0)
		{	if (Verbose&2)
			printf("		%s -L-> %s %s %s\n",
				s, g->dt, g->tg, g->full?g->full:g->nm);
			goto found;
		}

	for (g = modex_globals; g; g = g->nxt)
		if (strcmp(g->nm, s) == 0)
		{	if (Verbose&2)
			printf("		%s -G-> %s %s %s\n",
				s, g->dt, g->tg, g->full?g->full:g->nm);
			goto found;
		}

	for (g = modex_hidden; g; g = g->nxt)
		if (strcmp(g->nm, s) == 0)
		{	if (Verbose&2)
			printf("		%s -H-> %s %s %s\n",
				s, g->dt, g->tg, g->full?g->full:g->nm);
			goto found;
		}
notfound:
	if (0)	/* could be field in struct - beyond our scope */
	fprintf(stderr, "		%s -?-> not found\n", s);
	return (char *) 0;
found:
	i = 0; z = g->full?g->full:g->nm;
	while (*z) { if (*z++ == '[') i++; }

	if (i != 1	/* can't tell apart multiple indices - yet */
	||  !(z = strrchr(g->full?g->full:g->nm, '['))
	||  !(y = strrchr(g->full?g->full:g->nm, ']'))
	||  !(z < y))
		goto notfound;
	*y = '\0';
	x = (char *) e_malloc(strlen(z+1)+1);
	strcpy(x, z+1);
	*y = ']';
	return x;
}

void
array_bound(treenode *bnm, treenode *indx)
{	int ov = with_decorations;
	char *z;

	if (!vis) return;

	with_decorations = 0;
	strcpy(dername, "");

	dotree(bnm, 0, 0);

	z = which_var(dername);

	strcpy(dername, "");
	with_decorations = ov;

	if (!z || strlen(z) == 0) return;	/* can't find the bound */

	strcpy(Rem4, OutBuf);		/* save */
	strcpy(OutBuf, "");

	modex_recur(indx);

	if (isdigit((int) OutBuf[0])		/* 2 < 100 */
	&&  isdigit((int) z[0]))
	{	int n1, n2;
		n1 = atoi(OutBuf);
		n2 = atoi(z);
		if (Verbose&2)
		printf("%s: precondition (%d < %d == %s)\n",
			progname, n1, n2, (n1 < n2)?"true":"false");
		if (n1 < n2) goto notfound;
	}

	if (strlen(Bounds) > 0)
		strcat(Bounds, " && ");
	strcat(Bounds, "(");
	strcat(Bounds, OutBuf);
	strcat(Bounds, " < ");
	strcat(Bounds, z);
	strcat(Bounds, ")");

	if (Verbose&2) fprintf(stderr, "	Bound %s\n", Bounds);

notfound:
	strcpy(OutBuf, Rem4);		/* restore */
	return;
}

void
add_local(char *s, char *t, char *r, int d, int ln, int which)
{	Fcts *g;

if (0) fprintf(stderr, "Add_Local <%s> <%s> <%s> which=%d\n", s, t, r, which);

	if (strncmp(s, "static", strlen("static")) == 0)
	{	s += strlen("static");	/* can't have this in a State vector decl. */
		while (*s == ' ' || *s == '\t')
			s++;
		add_global(s, t, d, ln);	/* static local becomes global */
		if (Warnings)
		fprintf(stderr, "%s: %3d, warning, treating <%s %s> in <%s> as global\n",
			progname, ln, s, t, r);
		return;
	}

	if (strlen(s) == 0
	||  strlen(t) == 0
	||  strcmp(r, "-") == 0)
		return;

	while (*t == ' ' || *t == '\t')
		t++;

	if (strncmp(s, "extern", strlen("extern")) == 0
	||  strncmp(t, "=", 1) == 0
	||  strncmp(t, "*", 1) == 0)
		return;

	if (strcmp(s, "unsigned unsigned ") == 0)
	{	s += strlen("unsigned ");
	}

if (0)	printf("%3d: {%d} addlocal <%s> <%s> <%s> %d -- want=%s -- inargs=%d\n",
		ln, which, s, t, r, d, want, in_args);

	for (g = modex_locals; g; g = g->nxt)
	{
if (0) printf("\tcheck <%s> <%s> <%s>\n", g->dt, g->nm, g->tg);
		if (strcmp(g->dt, s) == 0 && strlen(g->dt) == strlen(s)
		&&  strcmp(g->nm, t) == 0 && strlen(g->nm) == strlen(t)
		&&  strcmp(g->tg, r) == 0 && strlen(g->tg) == strlen(r))
		{	if (allprocs
			||  strcmp(r, want) == 0)
				g->wanted = 1;
if (0)	printf("	found %s\n", t);
			return;
		}
	}

	g = modex_fct_el(s);
	g->dt = g->nm;
	g->lno = ln;

	t = sep_decor(t, g);

	g->nm = (char *) e_malloc(strlen(t)+1);
	strcpy(g->nm, t);

	g->tg = (char *) e_malloc(strlen(r)+1);
	strcpy(g->tg, r);

	g->derived = d;

if (0) printf("%3d: added dt=%s nm=%s tg=%s (s=%s t=%s r=%s d=%d)\n",
		g->lno, g->dt, g->nm, g->tg, s, t, r, d);

	g->nxt = modex_locals;
	modex_locals = g;
}
void
add_full_local(char *s, char *t, char *r, int derived, int ln)
{	Fcts *g;
	char *z;
	char cnt = 0;

	if (strlen(s) == 0
	||  strlen(t) == 0
	||  strcmp(r, "-") == 0)
		return;

if (0) printf("add_full_local <%s> %s %s\n", s, t, r);
	if (strcmp(s, "unsigned unsigned ") == 0)
	{	s += strlen("unsigned ");
	}


tryagain:
	for (g = modex_locals; g; g = g->nxt)
		if (strcmp(g->dt, s) == 0 && strlen(g->dt) == strlen(s)
		&&  strcmp(g->tg, r) == 0 && strlen(g->tg) == strlen(r)
		&& (z = strstr(t, g->nm)))
		{
			if (allprocs
			||  strcmp(r, want) == 0)
				g->wanted = 1;

if (0)			fprintf(stderr, "consider add_full_local <s=%s t=%s r=%s> g->full=%s g->nm=%s {%d} %d\n",
					s, t, r, g->full, g->nm, *(z+strlen(g->nm)), z==t);

			if ((z == t
			&&  (*(z+strlen(g->nm)) == '['
			||   *(z+strlen(g->nm)) == '\0'
			||   *(z+strlen(g->nm)) == ' '))	/* asgn, ival */
			||  (*(z-2) == '*' && *(z-1) == ' '))
			{
				if (isalnum((int) *(z+strlen(g->nm))))
					continue;

				if (g->full
				&&  (strcmp(g->full, t) == 0
				||   strlen(g->full) >= strlen(t)))
					return;
#if 0
			if (g->full)
				fprintf(stderr, "override add_full_local <%s> <with:%s> <%s> (is:%s) nm=%s {%d} %d\n",
					s, t, r, g->full, g->nm, *(z+strlen(g->nm)), z==t);
			else
				fprintf(stderr, "fillin add_full_local <s=%s (%s) t=%s r=%s (%s)> g->nm=%s {%d} %d\n",
					s, g->dt, t, r, g->tg, g->nm, *(z+strlen(g->nm)), z==t);
#endif
				g->full = (char *) e_malloc(strlen(t)+1);
				strcpy(g->full, t);
				return;
			}
		}

if (debug)		fprintf(stderr, "%s: add_full_local not-found: %s %s %s\n", progname, s, t, r);

	if (++cnt == 1)
	{	add_local(s, t, r, derived, ln, 10);
		goto tryagain;
	}
}
void
dump_decls(FILE *fd)
{	Fcts *g;

	for (g = modex_globals; g; g = g->nxt)
		if (!strstr(g->dt, "typedef")
		&&  !strstr(g->dt, "extern"))
		fprintf(fd, "Global	%s	%s\n",
			g->dt, g->nm);

	for (g = modex_hidden; g; g = g->nxt)
		if (!strstr(g->dt, "typedef")
		&&  !strstr(g->dt, "extern"))
		fprintf(fd, "%s	%s	%s\n",
			NONSTATE, g->dt, g->nm);

	for (g = modex_locals; g; g = g->nxt)
		if (!strstr(g->dt, "typedef")
		&&  !strstr(g->dt, "extern"))
		fprintf(fd, "Local	%s	%s	%s\n",
			g->dt, g->nm, g->tg);
}

char *
spintype(char *s, char *t)
{	static struct {
		char *tp; char *mp;
	} StS[] = {
		{ "bit ",	"bit" },	/* trailing space */
		{ "bool ",	"bool" },
		{ "byte ", 	"byte" },
		{ "pid ", 	"pid" },
		{ "int ",	"int" },
		{ "short ",	"short" },
		{ "uchar ", 	"byte" },
		{ "chan ", 	"chan" },

		{ "bit",	"bit" },	/* no trailing space */
		{ "bool",	"bool" },
		{ "byte", 	"byte" },
		{ "pid", 	"pid" },
		{ "int",	"int" },
		{ "short",	"short" },
		{ "uchar", 	"byte" },
		{ "chan", 	"chan" },
		{ (char *) 0,	 (char *) 0 }
	};
	int i;

	for (i = 0; StS[i].tp; i++)
		if (strcmp(s, StS[i].tp) == 0)
		{	if (!t
			||  strcmp(StS[i].mp, "chan") == 0
			||  (!strchr(t, '*')
			&&   !strstr(t, "sizeof")
			&&   !strstr(t, "->")
			&&   !strchr(t, '.')
			&&   !strchr(t, '{')
			&&  (!strchr(t, '[')
			||   (strchr(t, '[') == strrchr(t, '[')
			&&   !strchr(t, '=')))))
			{	return StS[i].mp;
			}
			break;
		}

	return (char *) 0;
}

void
do_hidden(FILE *fd)
{	Fcts *g;

	if (suppress)
		return;

	for (g = modex_hidden; g; g = g->nxt)
	{
		if (g->purged)
		{	continue;
		}
		g->purged = 1;

		if (g->derived)
		{	if (g->fc == 3		/* labelname */
			||  show_deps
			||  (!allprocs
			&&   strcmp(want, g->tg) != 0))
				continue;

			if (!(Verbose&2)
			&&  strcmp(g->tg, ":global:") == 0)
				continue;

			if (!Warnings)
				continue;

			fprintf(stderr, "%s: ", progname);
			if (g->lno > 0)
				fprintf(stderr, "line %3d, ", g->lno);

			switch (g->fc) {
			case 0:
				fprintf(stderr, "may need declaration for: ");
				break;
			case 1:	/* fct call */
				fprintf(stderr, "function call: ");
				break;
			case 2:
				fprintf(stderr, "initialize parameter: ");
				break;
			default:
				fprintf(stderr, "cannot happen fc ");
				break;
			}
			if (strcmp(g->dt, "Global") != 0)
				fprintf(stderr, "%s ", g->dt);
			fprintf(stderr, "%s (%s)\n", g->nm, g->tg);

		} else if (strcmp(g->dt, NONPRINT) != 0)
		{	fprintf(fd, "	c_code { %s %s; };	/*  %s */\n",
				g->dt, g->full?g->full:g->nm, NONSTATE);
	}	}
}

char *
checkfull(char *r, char *s, int ln)
{	char *t = (char *) 0;
	char *nt, *z;

	if (s
	&& (t = strchr(s, '=')))	/* assigns t */
	{	nt = t;
		*t++ = '\0';
		while (*t == ' ' || *t == '\t')
			t++;
	}
	if (t && *t)
	{	z = nt = (char *) e_malloc(2*strlen(t)+1);

		if (strchr(t, ','))
			*z++ = '{';

		for ( ; *t; t++)
		{	if (*t == '\"')
				*z++ = '\\';
			*z++ = *t;
		}

		if (*nt == '{')
			*z++ = '}';

		*z = '\0';
		t = nt;
	}
	return t;
}

void
cleanse(char *p)
{	char *z;

	while ((z = strstr(p, "\n")) != NULL)
		*z = ' ';

	while ((z = strstr(p, "\\n")) != NULL)
	{	*z++ = ' ';
		*z = ' ';
	}
}

static char *SomeCode[] = {
	"extern void (*Uerror)(char *);",
	"char *",
	"spin_malloc(int n)",
	"{	char *spin_heap_ptr = &(now.spin_heap[now.spin_heap_n]);",
	"	if (now.spin_heap_n + n >= sizeof(now.spin_heap))",
	"	{	Uerror(\"spin_heap limit reached\");",
	"	}",
	"	now.spin_heap_n += n;",
	"	return spin_heap_ptr;",
	"}",
	"void",
	"spin_free(char *unused)",
	"{	unused;",
	"}",
	0
};

void
add_nomap_locals(FILE *fd)
{	Fcts *g;
	char *t;

	for (g = modex_locals; g; g = g->nxt)
	{
		if (spintype(g->dt, g->full?g->full:g->nm))
			continue;

		if (!allprocs && !g->wanted)
			continue;

		if (!imported(g->nm, g->tg, 1))
			continue;

		if (g->purged)
		{	continue;
		}
		g->purged = 1;
		if (!strstr(g->dt, "typedef")
#if 0
		&&  !strstr(g->dt, "struct")
#endif
		)
		{	t = checkfull(g->dt, g->full, g->lno);
			cleanse(g->dt);

if (0)		fprintf(stderr, "%3d: (%d) add_nomap_locals fct %s: dt %s nm %s tg %s full %s fc (%d,%p) want %s [%d]\n",
			g->lno, du_mode, fct_name, g->dt, g->nm, g->tg,
			g->full, g->fc,
			spintype(g->dt, g->full?g->full:g->nm), want, allprocs);

			if (du_mode)
			{	char *yy, *y = g->full?g->full:g->nm;
				while (*y == '*' || *y == ' ' || *y == '\t')
					y++;
				if ((yy = strstr(y, "[]")) != NULL)
				{	*yy = '\0';
				}
				fprintf(fd, "int %s;	/* local to %s */\n",
					y, g->tg);
			} else
			{	fprintf(fd, " c_state \"%s %s\" \"Local p_%s\"",
					g->dt, g->full?g->full:g->nm, g->tg);
				if (t)
				{	fprintf(fd, " \"%s\"", t);
					fprintf(stderr, "modex: error: local %s is ", g->full?g->full:g->nm);
					fprintf(stderr, "initialized in declaration in instrumented %s()\n", g->tg);
				}
				fprintf(fd, " /* nomap */\n");
	}	}	}

	if (used_spin_malloc)
	{	static int not_twice = 0;
		if (not_twice++ == 0)
		{	int i;
			fprintf(fd, " c_state \"char spin_heap[%d]\" \"Global\"\n",
				spin_heap_size);
			fprintf(fd, " c_state \"int  spin_heap_n\" \"Global\"\n");
			fprintf(fd, " c_code {\n");
			for (i = 0; SomeCode[i]; i++)
			{	fprintf(fd, "\t\t%s\n", SomeCode[i]);
			}
			fprintf(fd, " }\n");
	}	}
}

void
add_fnm(char *s)
{	NameL *nl;

	nl = (NameL *) e_malloc(sizeof(NameL));
	nl->nm = (char *) e_malloc(strlen(s)+1);
	strcpy(nl->nm, s);
	nl->nxt = namel;
	namel = nl;
}

char *globfilename;

void
setglobfile(void)
{
	globfilename = "_modex_.h";
}

void
do_globals(int setup, scopetab_t *that, int lastcall)
{	Fcts *g;
	char *z;
	FILE *fd;
	NameL *nl;

	if (suppress)
	{	return;
	}

	if (Verbose_cmds)
	{	printf("-- do globals [%d %d %d %s]\n", setup, do_inc_globals, allprocs, globfilename);
	}

	if (setup)
	{	setglobfile();
		if (do_inc_globals && allprocs)
		{	sprintf(tbuf, "#include \"%s\"	/* global header file */\n\n",
				globfilename);
			vis_direct(tbuf);
		}	/*  else created but not #include'd */
		return;
	}
	if (!globfilename)	/* no functions matched, user forgot -x */
	{	setglobfile();
	}

	#ifdef PC
		#define AFLAGS	"ab"
	#else
		#define AFLAGS	"a"
	#endif

	if ((fd = fopen(globfilename, AFLAGS)) == NULL)
	{	fprintf(stderr, "%s: error, cannot create global header file %s\n",
			progname, globfilename);
		return;
	}
if (debug_io) fprintf(stderr, ":: open %s -> %p\n", globfilename, fd);
	add_fnm(globfilename);

	fprintf(fd, "/** globals **/\n\n");

	do_constants(fd);
	fprintf(fd, "/** done with constants... **/\n\n");

	for (g = modex_globals; g; g = g->nxt)
	{
		if (strlen(g->full?g->full:g->nm) == 0)
			continue;

		if (!imported(g->nm, "Global", 1))
			continue;

		if (g->purged)
		{	continue;
		}
		g->purged = 1;

		if (0)
		printf("nm %s, dt %s, full %s\n", g->nm, g->dt, g->full);

		if ((z = spintype(g->dt, g->full?g->full:g->nm)) != NULL)
		{	sprintf(tbuf, "%s %s;\t/* derived <%s> */\n",
				z, g->full?g->full:g->nm, g->nm);
		} else if (strstr(g->dt, "typedef"))
		{	continue;
		} else
		{	z = checkfull(g->dt, g->full, g->lno);
			cleanse(g->dt);

			if (du_mode)
			{	char *yy, *y = g->full?g->full:g->nm;
				while (*y == '*' || *y == ' ' || *y == '\t')
					y++;
				if ((yy = strstr(y, "[]")) != NULL)
				{	*yy = '\0';
				}
				sprintf(tbuf, "int %s;	/* global */\n", y);
			} else
			{	if (z)
				sprintf(tbuf, " c_state \"%s %s\" \"Global\" \"%s\"\n",
					g->dt, g->full?g->full:g->nm, z);
				else
				sprintf(tbuf, " c_state \"%s %s\" \"Global\"\n",
					g->dt, g->full?g->full:g->nm);
		}	}
		fprintf(fd, "%s", tbuf);
	}

	for (nl = globchans; nl; nl = nl->nxt)
	{
		if (nl->purged)
		{	continue;
		}
		nl->purged = 1;

		fprintf(fd, "%s\n", nl->nm);
	}

	add_nomap_locals(fd);
	do_externals(fd);

	do_hidden(fd);			/* hidden vars */
	if (that)
	{	x_scopetab(that, fd, want);	/* extra c_state decls */
	}

	if (i_assert)
	{	ax_doprops(fd, that);
	}

	if (that && !nostructs)	/* import global structure declarations */
	{	extern void put_structs(scopetab_t *, FILE *);
		if (lastcall)				/* new 2.8 */
		{	find_typedefs(that, fd);	/* new 2.6 */
			put_structs(that, fd);
	}	}
if (debug_io) fprintf(stderr, "close z %p\n", fd);
	Fclose(fd);
}

void
spitnames(FILE *fid)
{	NameL *nl;
	FILE *fd;

	if (!namel) return;

	if (Warnings)
	{	fprintf(fid, "modex files created:\n");
		for (nl = namel; nl; nl = nl->nxt)
		{	fprintf(fid, "\t%s", nl->nm);
			if (globfilename
			&&  strcmp(nl->nm, globfilename) == 0)
				fprintf(fid, " (global header file)");
			fprintf(fid, "\n");
		}
		fprintf(fid, "\t_modex_.cln # cleanup script\n");
	}

	if ((fd = fopen("_modex_.cln", MFLAGS)) == NULL)
	{	fprintf(stderr, "%s: cannot create .cln file\n", progname);
		return;
	}
if (debug_io) fprintf(stderr, "open .cln -> %p\n", fd);
	for (nl = namel; nl; nl = nl->nxt)
		fprintf(fd, "%s %s\n", RM, nl->nm);

	fprintf(fd, "%s _modex_.cln\n", RM);
	fprintf(fd, "%s %s *.I\n", RM, tempfile_M);
	fprintf(fd, "%s pan.? pan pan.exe _spin_nvr.tmp\n", RM);
if (debug_io) fprintf(stderr, "close y %p\n", fd);
	Fclose(fd);

	namel = (NameL *) 0;
}

void
def_inc_spn(FILE *fd)
{	NameL *nl;

	for (nl = namel; nl; nl = nl->nxt)
		if (strstr(nl->nm, ".pml"))
			fprintf(fd, "#include \"%s\"\n", nl->nm);
}

void
new_globchan(char *s)
{	NameL *nl;

	nl = (NameL *) e_malloc(sizeof(NameL));
	nl->nm = (char *) e_malloc(strlen(s)+1);
	strcpy(nl->nm, s);
	nl->nxt = globchans;
	globchans = nl;
}

void
ini_formals(void)
{	Fcts *g;
	int cnt = 0;
	char buf0[1024];	/* build up a type decl for param chan */
	char buf1[1024];

	for (g = modex_locals; g; g = g->nxt)
	{	if (strcmp(g->tg, fct_name) == 0
		&&  g->fc == 2)
		{	cnt++;
			if (0) fprintf(stderr, "\t%s\thas formal param: %s %s\n",
				fct_name, g->dt, g->full?g->full:g->nm);
	}	}

	if (!extended
	||  strcmp(fct_name, "main") == 0
	||  strcmp(fct_name, "modex_main") == 0)
	{	vis_direct("\n#if 0\n");
	}
	vis_direct("endRestart:\n");
	if (flike
#define SV_COMP
#ifdef SV_COMP
	||  strstr(fct_name, "_atomic_")
#endif
	    )
	{	vis_direct("atomic { /* function like */\n");
	}

	if (vis && extended)
	{	sprintf(buf0, "chan req_cll_p_%s = [1] of { pid };", fct_name);
		new_globchan(buf0);
		sprintf(buf0, "chan exc_cll_p_%s = [0] of { pid };", fct_name);
		new_globchan(buf0);
		sprintf(buf0, "chan ret_p_%s = [1] of { pid };", fct_name);
		new_globchan(buf0);

		sprintf(buf1, "lck_p_%s", fct_name);
		add_global("bool", buf1, 1, 0);	/* lck_ */
		add_imported(buf1, "Global", 1);

		strcat(buf1, "_ret");
		add_global("bool", buf1, 1, 0);	/* _ret */
		add_imported(buf1, "Global", 1);

		sprintf(buf1, "lck_id");
		add_local("pid", buf1, fct_name, 1, 0, 20);
		add_imported(buf1, fct_name, 1);

		sprintf(buf1, "res_p_%s", fct_name);
#if 0
		add_global("long", buf1, 1, 0);	/* shouldn't be just long */
#else
		add_global(fct_type, buf1, 1, 0);
#endif
		add_imported(buf1, "Global", 1);
	}

	sprintf(buf1, "\tatomic {\n\tnempty(req_cll_p_%s) && !lck_p_%s -> ",
		fct_name, fct_name);
	vis_direct(buf1);
	sprintf(buf1, "lck_p_%s = 1;\n", fct_name);
	vis_direct(buf1);
	sprintf(buf1, "\treq_cll_p_%s?lck_id; ", fct_name);
	vis_direct(buf1);
	sprintf(buf1, "exc_cll_p_%s?eval(lck_id);\n", fct_name);
	vis_direct(buf1);

	for (g = modex_locals, cnt = 0; g; g = g->nxt)
		if (strcmp(g->tg, fct_name) == 0
		&&  g->fc == 2)
			cnt++;
	if (vis && extended)
	for (g = modex_locals; g; g = g->nxt)
		if (strcmp(g->tg, fct_name) == 0
		&&  g->fc == 2)
		{	sprintf(buf1, "\tc_code { Pp_%s->%s = ", g->tg, g->nm);
			vis_direct(buf1);
			sprintf(buf1, "now.par%d_%s; };\n", --cnt, g->tg);
			vis_direct(buf1);

			/* add and import global now.par%d_%s: */

			if (strcmp(g->tg, "main") == 0
			||  strcmp(g->tg, "modex_main") == 0)
			{	continue;
			}

			sprintf(buf1, "par%d_%s", cnt, g->tg);
			add_global(g->dt, buf1, 1, 0);	/* par */
			add_imported(buf1, "Global", 1);
			if (g->full)
			{	char *z, *y;
				z = strstr(g->full, g->nm);
				y = z + strlen(g->nm);
				if (z > g->full)
				{	strcpy(buf0, g->full);
					buf0[z - g->full] = '\0';
				} else
					strcpy(buf0, "");
				strcat(buf0, buf1);
				if (*y) strcat(buf0, y);
				strcpy(buf1, buf0);
				add_full_global(g->dt, buf1, 1, 0);
				add_imported(buf1, "Global", 1);	/* needed? */
			}
		}
#if 1
	sprintf(buf1, "\tlck_p_%s = 0;\n\t};\n", fct_name);
#else
	sprintf(buf1, "\n\t};\n");
#endif
	vis_direct(buf1);

	if (!extended
	|| strcmp(fct_name, "main") == 0
	|| strcmp(fct_name, "modex_main") == 0)
		vis_direct("#endif\n");
}

int did_parameters;

void
do_parameters(void)
{	Fcts *g;
	char *z;
	char xx[128];

	if (suppress || globals_only)
	{	return;
	}

	for (g = modex_locals; g; g = g->nxt)
	{	if (g->fc == 2 && strcmp(fct_name, g->tg) == 0)
		{	if (!spintype(g->dt, g->full?g->full:g->nm))
			{	/* at least one param not spin mappable */
				if (Verbose)
				{	fprintf(stderr, "params of %s converted to local vars\n",
						g->tg);
				}
				return;
	}	}	}

	for (g = modex_locals; g; g = g->nxt)
	{	if (strcmp(fct_name, g->tg) == 0
		&&  g->fc == 2)	/* spin-mappable formal params */
		{	z = spintype(g->dt, g->full?g->full:g->nm);
			if (z)
			{	if (did_parameters)
				{	vis_direct(", ");
				}
				if (strcmp(wanttype, "inline") == 0)
				{	sprintf(xx, "%s", g->full?g->full:g->nm);
				} else
				{	sprintf(xx, "%s %s", z, g->full?g->full:g->nm);
				}
				vis_direct(xx);
				did_parameters = 1;
	}	}	}
}

void
do_locals(int d)
{	FILE *fd;
	Fcts *g;
	char *z;

	if (suppress || globals_only
	||  (strcmp(wanttype, "body") == 0
	&&   import_all == 0))
		return;

if (0) fprintf(stderr, "===> %d %d %d\n", suppress, globals_only, import_all);

	if (!d)
	{	if (do_inc_locals)
		{	sprintf(tbuf, "\n#include \"%s_%d.h\"\n\n", o_base, o_cnt);
			vis_direct(tbuf);
		}
		return;
	}

	sprintf(tbuf, "%s_%d.h", o_base, o_cnt++);
	if ((fd = fopen(tbuf, MFLAGS)) == NULL)
	{	fprintf(stderr, "%s: error, cannot create local header file %s\n",
			progname, tbuf);
		return;
	}
if (debug_io) fprintf(stderr, "open %s -> %p\n", tbuf, fd);

	fprintf(fd, "/** locals of %s **/\n\n", fct_name);

	for (g = modex_locals; g; g = g->nxt)
	{
if (0)		printf("%3d: %s: %s %s %s (%s) (%d,%d)\n",
		g->lno, fct_name, g->dt, g->nm, g->tg, g->full, g->fc, g->derived);
		if (strcmp(fct_name, g->tg) != 0
		||  (allkeep && g->fc != 2))	/* formal params only */
			continue;

		if (g->fc == 2 && !show_deps && Warnings)
		{	fprintf(stderr, "%s: ", progname);
			if (g->lno > 0)
			fprintf(stderr, "line %3d, ", g->lno);
			fprintf(stderr, "initialize parameter to %s: %s %s\n",
				fct_name, g->dt, g->full?g->full:g->nm);
		}

		if (!imported(g->nm, g->tg, 1))
		{	if (Warnings)
			fprintf(stderr, "Not imported %s <%s>\n", g->nm, g->tg);
			continue;
		}

		if (!did_parameters)
		if ((z = spintype(g->dt, g->full?g->full:g->nm)) != NULL)
		{	char *w, *x, *y = g->full?g->full:g->nm;
			if (y && strstr(y, "pan_rand()"))
			{	x = e_malloc(strlen(y)+strlen("c_expr { } ") + 1);
				strcpy(x, y);
				w = strstr(x, "pan_rand()");
				*w = '\0';
				w += strlen("pan_rand()");
				fprintf(fd, "%s %s", z, x);
				fprintf(fd, "c_expr { pan_rand() }");
				fprintf(fd, "%s;\t/*mapped */\n", w);
			} else
			{	fprintf(fd, "%s %s;\t/* mapped */\n",
					z, g->full?g->full:g->nm);
			}
			/* others printed in add_nomap_locals */
	}	}
	fprintf(fd, "\n");
if (debug_io) fprintf(stderr, "close x %p\n", fd);
	Fclose(fd);

	z = (char *) e_malloc(strlen(o_base)+10);
	sprintf(z, "%s_%d.h", o_base, o_cnt-1);
	add_fnm(z);
}

int
map_type(char *s, symentry_t *nmtbl)
{	Fcts *f = (Fcts *) 0;
	int ret_val = 0;	/* 0 = undefined */

	if (nmtbl->kind == ENUM_CONST_ENTRY && is_constant(s))
	{	ret_val = 3;	/* same as hidden */
		goto done;
	}

	if (nmtbl->kind != VARDECL_ENTRY)
		goto shortcut;
	/* else its a typedef, structname, fctname, labelname */

	/* local */
	for (f = modex_locals; f; f = f->nxt)
	{	if (strcmp(s, f->nm) == 0
		&&  strcmp(fct_name, f->tg) == 0)
		{	if (strcmp(fct_name, want) == 0)
				f->wanted = 1;
			if (!imported(s, f->tg, 0))
				ret_val = 3;
			else
				ret_val = 1;
			goto done;
	}	}

	/* global */
	for (f = modex_globals; f; f = f->nxt)
	{	if (strcmp(s, f->nm) == 0)
		{	if (!imported(s, "Global", 0))
				ret_val = 3;
			else
				ret_val = 2;
			goto done;
	}	}
shortcut:
	/* hidden */
	for (f = modex_hidden; f; f = f->nxt)
	{	if (strcmp(f->dt, "Global") != 0	/* structure member */
		&&  strcmp(s, f->nm) == 0)
		{	ret_val = 3;
			goto done;
	}	}

done:
#if 0
	if (vis && check_type && ret_val)
	{	if (f				/* was missing, found by uno 10/18/01 */
		&&  strcmp(f->dt, "int") != 0
		&&  strcmp(f->dt, "int ") != 0
		&&  strcmp(f->dt, "short") != 0
		&&  strcmp(f->dt, "short ") != 0)
		{	fprintf(stderr, "%s: %d: error, return var %s must be int (saw %s)\n",
				progname, f->lno, s, f->dt);
	}	}
#endif
	return ret_val;
}

void
dump_substitute(FILE *fd)
{	Fcts *f;
	for (f = maps; f; f = f->nxt)
	{	if (f->level > 0)
			continue;
		if (f->tg)
			fprintf(fd, "Substitute	%s	%s\n", f->nm, f->tg);
		else
			fprintf(fd, "Substitute	%s\n", f->nm);
	}
}

void
via_substitute(char *into, char *z)
{	char *q, nbuf[BigEnough];
	Fcts *f;
if (0) fprintf(stderr, "via_sub '%s'\n", into);
	strcpy(into, z);

	if (in_args)
	{	q = z;
		while (*q == ' ')
			q++;
		if (strncmp(q, "void", strlen("void")) == 0)
		{	q += strlen("void");
			while (*q == ' ' || *q == '*')
				q++;
			if (*q == '\0')
			{	strcpy(into, "");
				return;	/* e.g.: main(void *) */
		}	}
	}

	for (f = maps; f; f = f->nxt)
	while ((q = strstr(into, f->nm)) != NULL)
	{	*q = '\0';
		strcpy(nbuf, into);
		if (f->tg) strcat(nbuf, f->tg);
		strcat(nbuf, &q[strlen(f->nm)]);
		strcpy(into, nbuf);
	}
}

void
add_imported(char *p, char *q, int mustgenerate)
{	Spress *s;

	for (s = spress; s; s = s->nxt)
	{	if (strcmp(p, s->vn) == 0
		&&  strcmp(q, s->pn) == 0)
		{	return;
	}	}

	s = (Spress *) e_malloc(sizeof(Spress));
	s->vn = (char *) e_malloc(strlen(p)+1);
	s->pn = (char *) e_malloc(strlen(q)+1);
	strcpy(s->vn, p);
	strcpy(s->pn, q);
	s->hit = 0;
	s->mustgen = mustgenerate;
	s->nxt = spress;
	spress = s;

	if (strcmp(p, "_all_") == 0
	&&  strcmp(q, "_all_") == 0)
	{	import_all++;
	}

if (0) fprintf(stderr, "add imported %s %s %d\n", p, q, mustgenerate);
}

void
add_external(char *p, char *q)
{	Spress *s;

	for (s = externals; s; s = s->nxt)
		if (strcmp(p, s->vn) == 0
		&&  strcmp(q, s->pn) == 0)
			return;
	s = (Spress *) e_malloc(sizeof(Spress));
	s->vn = (char *) e_malloc(strlen(p)+1);
	s->pn = (char *) e_malloc(strlen(q)+1);
	strcpy(s->vn, p);
	strcpy(s->pn, q);
	s->hit = 0;
	s->nxt = externals;
	externals = s;
}

void
do_externals(FILE *fd)
{	Spress *s;

	for (s = externals; s; s = s->nxt)
	{	if (s->purged)
		{	continue;
		}
		s->purged = 1;
		fprintf(fd, "c_track \"%s\" \"%s\"\n",
			s->vn, s->pn);
	}
}

char*
nextarg(char *p)
{
	while (*p && /* *p != ' ' && */ *p != '\t')
		p++;
	while (*p == ' ' || *p == '\t')
		*p++ = 0;
	return p;
}

void
add_constants(char *p)
{	char *q;

	q = nextarg(p);
	if (*q != '\0')
		add_constants(q);
	add_constant(p, 1);
}

int
imported(char *p, char *q, int about_to_generate)
{	Spress *s;

	for (s = spress; s; s = s->nxt)
		if ((strcmp(q, s->pn) == 0
		||   strcmp(s->pn, "_all_") == 0)
		&&  (strcmp(p, s->vn) == 0
		||   strcmp(s->vn, "_all_") == 0))
		{	s->hit = 1;
			if (about_to_generate)
				return s->mustgen;
			return 1;
		}
	return 0;
}

void
notimported(FILE *fd)
{	Spress *s;

	for (s = spress; s; s = s->nxt)
		if (!s->hit
		&&  !strstr(s->pn, "Global"))	/* covers unused global declarations */
			fprintf(fd, "Redundant: Import %s %s\n", s->vn, s->pn); 
}

void
read_more(FILE *fd, char *buf)
{	char *p, more[1024];


	while (fgets(more, 1024, fd))
	{	buf[strlen(buf)-1] = '\0';
		p = &more[strlen(more)-1];

		while (*p == '\n'
		||     *p == '\r'
		||     *p == '\t'
		||     *p == ' ')
			*p-- = '\0';

		p = &more[0];
		while (*p == ' ' || *p == '\t')
			p++;

		strcat(buf, " ");
		strcat(buf, p);
		if (buf[strlen(buf)-1] != '\\')
			break;
	}
}

int saw_import = 0;

void
get_lut(char *o_base, char *lut)
{	FILE *lf;
	char buf[2048], *p, *q, *r;
	char nbuf[2048];
	int cnt=0;

// printf("GET LUT '%s'\n", lut?lut:"");

	if (!lut)
	{	lut = (char *) e_malloc(strlen(o_base)+strlen(".lut")+1);
		strcpy(lut, o_base);
		strcat(lut, ".lut");
	} else
	{	if (!strstr(lut, ".lut"))
			strcat(lut, ".lut");
	}

	if (Verbose)
		printf("get lut %s\n", lut);

	add_hidden(NONPRINT, "__iob", 0, 0);

	if ((lf = fopen(lut, "rb")) == NULL)
	{	if (!new_lut
		&&  Warnings
		&&  strncmp(lut, "none", strlen("none")) != 0)
			fprintf(stderr, "%s: warning, no file '%s'\n", progname, lut);
		FreshLut = 1;
		goto done;
	} else if (!new_lut && Warnings)
		fprintf(stderr, "%s: using '%s'\n", progname, lut);

if (debug_io) fprintf(stderr, "open lut -> %p\n", lf);

	while (fgets(buf, sizeof(buf), lf))
	{	while ((p = strrchr(buf, '\n'))
		||     (p = strrchr(buf, '\r')))
			*p = '\0';

		while (buf[strlen(buf)-1] == '\t'
		||     buf[strlen(buf)-1] == ' ')
			buf[strlen(buf)-1] = '\0';

		if (buf[strlen(buf)-1] == '\\')
			read_more(lf, buf);

		if (buf[0] == '#' || !strchr(buf, '\t'))
		{	add_comment(cnt++, buf);
			continue;
		}

		if (strncmp(buf, "Include", strlen("Include")) == 0)
		{	p = nextarg(buf);
			(void) nextarg(p);
			add_include(p);
			Down += 2;
			get_lut("", p);	/* recursive call -- not visible */
			Down -= 2;
			continue;
		}

		if (strncmp(buf, "Suppress", strlen("Suppress")) == 0)
		{	fprintf(stderr, "Suppress command obsolete (ignored, use Import)\n");
			continue;
		}

		if (strncmp(buf, "Insert",  strlen("Insert")) == 0
		||  strncmp(buf, "Declare", strlen("Declare")) == 0)
		{	p = nextarg(buf);
			q = nextarg(p);
			r = nextarg(q);
			if (*r == '\0')
			{	fprintf(stderr, "usage:	Insert\ttype\tvname\tpname/Global\n");
				fprintf(stderr, "or:	Declare\ttype\tvname\tpname/Global\n");
				exit(1);
			}
			(void) nextarg(r);
			add_imported(q, r, 1);
			if (strcmp(r, "Global") == 0)
			{	add_full_global(p, q, 1, 0);
			} else
			{	add_full_local(p, q, r, 1, 0);
			}
			continue;
		}
		if (strncmp(buf, "Promela", strlen("Promela")) == 0)
		{	p = nextarg(buf);
			q = nextarg(p);
			if (*q == '\0')
			{	fprintf(stderr, "usage: Promela\tvname\tpname/Global\n");
				exit(1);
			}
			(void) nextarg(q);
			add_imported(p, q, 0);	/* 0 - do not generate declaration */
			continue;
		}
		if (strncmp(buf, "Import", strlen("Import")) == 0)
		{	p = nextarg(buf);
			q = nextarg(p);
			if (*q == '\0')
			{	fprintf(stderr, "usage: Import\tvname\tpname/Global\n");
				exit(1);
			}
			(void) nextarg(q);
if (0) fprintf(stderr, "A%d %s\n", saw_import, wanttype);
			add_imported(p, q, 1);
			saw_import++;
if (0) fprintf(stderr, "B%d %s\n", saw_import, wanttype);
			continue;
		}
		if (strncmp(buf, "Constant", strlen("Constant")) == 0)
		{	add_constants(nextarg(buf));
			continue;
		}
		if (strncmp(buf, "ICALL", strlen("ICALL")) == 0
		||  strncmp(buf, "Icall", strlen("Icall")) == 0)
		{	/* instrumented procedure calls */
			p = nextarg(buf);
			q = nextarg(p);
			if (*q != '\0')
			{	fprintf(stderr, "usage: Icall\tfct_name\n");
				exit(1);
			}
			add_icall(p);
			continue;
		}
		if (strncmp(buf, "Global", strlen("Global")) == 0)
		{	p = nextarg(buf);
			q = nextarg(p);
			if (*q == '\0')
			{	fprintf(stderr, "usage: Global\ttype\tvarname\n");
				exit(1);
			}
			(void) nextarg(q);
			add_global(p, q, 0, 0);
			continue;
		}
		if (strncmp(buf, "External", strlen("External")) == 0)
		{	fprintf(stderr, "External is obsolete, use Track\n");
			exit(1);
		}
		if (strncmp(buf, "Track", strlen("Track")) == 0)
		{	p = nextarg(buf);
			q = nextarg(p);
			if (*q == '\0')
			{	fprintf(stderr, "usage: Track\t&n\tsizeof(int)\n");
				exit(1);
			}
			(void) nextarg(q);
			add_external(p, q);
			continue;
		}
		if (strncmp(buf, NONSTATE, strlen(NONSTATE)) == 0)
		{	p = nextarg(buf);
			q = nextarg(p);
			if (*q == '\0')
			{	fprintf(stderr, "usage: %s\ttype\tvarname\n", NONSTATE);
				exit(1);
			}
			(void) nextarg(q);
			add_hidden(p, q, 0, 0);
			continue;
		}
		if (strncmp(buf, "Local", strlen("Local")) == 0)
		{	p = nextarg(buf);
			q = nextarg(p);
			r = nextarg(q);
			if (*r == '\0')
			{	fprintf(stderr, "usage: Local\ttype\tvarname\tprocname\n");
				exit(1);
			}
			(void) nextarg(r);
			add_local(p, q, r, 0, 0, 30);
			continue;
		}
		if (strncmp(buf, "Function", strlen("Function")) == 0)
		{	p = nextarg(buf);
			(void) nextarg(p);
			add_fct(p, p);

			sprintf(nbuf, "(%s", p);
			add_fct(nbuf, p);

			sprintf(nbuf, "(!%s", p);
			add_fct(nbuf, p);
			continue;
		}
		if (strncmp(buf, "Substitute", strlen("Substitute")) == 0)
		{	p = nextarg(buf);
			q = nextarg(p);
			(void) nextarg(q);
			add_substitute(p, q);
			continue;
		}

		p = nextarg(buf);	/* regular mapping src -> dst */
		if (*p != '\0')
		{	look_lut(buf, p, 0);	/* store it */
			cnt++;
		}
	}
if (debug_io) fprintf(stderr, "close w %p\n", lf);
	Fclose(lf);

done:
if (0) fprintf(stderr, "C%d %s\n", saw_import, wanttype);
	if (!saw_import)
	{	add_imported("_all_", "_all_", 1);
	}
}

extern char *ulut;

void
get_defaults(char *lut)
{	Cache *c;

	for (c = cache; c; c = c->nxt)
		c->hit |= 5;		/* mark */

	if (ulut)
	{	get_lut("", ulut);	/* once */
		ulut = 0;
	}

	Down++;
	if (strcmp(lut, GLOBAL_LUT) != 0)
		get_lut("", GLOBAL_LUT);
	Down++;
	get_lut("", DEFAULT_LUT);	/* loaded last - lowest priority */

	Down -= 2;

	for (c = cache; c; c = c->nxt)
	{	if (c->hit & 5)
			c->hit &= ~5;	/* unmark */
		else
			c->hit = 1;	/* consider hit */
	}
}

void
add_padding(FILE *lf, char *s)
{	int j;
	j = strlen(s);
	if (j < 40) fprintf(lf, "\t");
	if (j < 32) fprintf(lf, "\t");
	if (j < 24) fprintf(lf, "\t");
	if (j < 16) fprintf(lf, "\t");
	if (j <  8) fprintf(lf, "\t");
}

#if 0
void
debug_lut()
{	Cache *c;

	for (c = cache; c; c = c->nxt)
		printf("%d: %s\t%s	(%d,%d,%d)\n",
			c->level, c->t, c->s,
			c->hit, c->udef, c->printed);
}
#endif

void
trav_lut(FILE *lf, char *zz)
{	Cache *c, *x;
	char ubuf[64];
	int cnt, printline;

	cnt = 0;
	x = comms;

	if (FreshLut && nblanks == 0)
	{	fprintf(lf, "\n");
		nblanks++;
	}
	for (c = cache; c; c = c->nxt)
	{	if (c->level > 1)	/* 2 and up not visible */
			continue;

		while (x && cnt >= (int) x->hit)
		{	printline = 0;
			if (strlen(x->s) > 0)
				printline = 1;
			else if (nblanks++ == 0)
				printline = 1;

			if (printline)
				fprintf(lf, "%s\n", x->s); /* user-defined comments */

			x = x->nxt;
			cnt++;
		}
		if (c->printed == 0
		&& (!zz
		|| strlen(zz) == 0
		|| strncmp(c->s, zz, strlen(zz)) == 0))
		{	c->printed = 1;

			if (!c->udef
			&& !strncmp(c->s, "D: ", 3)
			&&  use_c_code
			&& !(Verbose&2))
				continue;	/* don't print declarations */

			if (!c->hit)
			{	if (!(Verbose&2))
					continue;
				fprintf(lf, "## ");
			}
			handle_special(lf, c->s, "\t");
			add_padding(lf, c->s);
			if (!c->udef)
				sprintf(ubuf, "	/* default-rule */\n");
			else
				sprintf(ubuf, "\n");
			handle_special(lf, c->t, ubuf);
			nblanks = 0;
		}
		cnt++;
	}
}

void
dump_lut(void)
{	int n;
	FILE *lf;
	char nlutfl[512];
	static char *prefs[] =
	{ "D: ", "C: ", "A: ", "F: ", "R: ", "case ", "", 0 };

	sprintf(nlutfl, "%s.%s", want, suffix);
	if (1 || Verbose_cmds)
		fprintf(stderr, "%s: writing %s\n", progname, nlutfl);

	if ((lf = fopen(nlutfl, MFLAGS)) == NULL)
	{	fprintf(stderr, "%s: cannot create %s\n", progname, nlutfl);
		return;
	}
if (debug_io) fprintf(stderr, "open %s -> %p\n", nlutfl, lf);
	fprintf(lf, "%s for target <%s>\n", Banner, want);
	dump_fct(lf);
	dump_substitute(lf);

	if (Verbose&2)
		dump_decls(stdout);

	for (n = 0; prefs[n]; n++)
		trav_lut(lf, prefs[n]);
if (debug_io) fprintf(stderr, "close v %p\n", lf);
	Fclose(lf);
	add_fnm(nlutfl);
}

void
check_lut(FILE *fd)
{	Cache *c;
	int identified = 0;

	if (!cache)
		fprintf(fd, "%s: empty lookup table\n", progname);

	for (c = cache; c; c = c->nxt)
		if (!c->hit)
		{	if (!identified)
			{	fprintf(fd, "<%s>:\n", want);
				identified = 1;
			}
			fprintf(fd, "Redundant: %s\t%s\n",
				c->s, c->t);
		}
}

void
vis_start(void)
{
	OutBuf[0] = '\0';
}

void
modex_mark(treenode *n, int how)
{
	if (!n || !n->hdr.defuse) return;

	if (Verbose&2)
	{	sprintf(tbuf, " /* [%d] ", how);
		vis_direct(tbuf);
		dump_defuse(n->hdr.defuse, 0, stdout);
	}
	mark_defs(n->hdr.defuse, how, stderr);

	if (Verbose&2) vis_direct(" */ ");
}

char *
form_c_tag(char *frst, int i, char *lst)
{	char *p;
	int j = strlen(frst)+strlen(OutBuf)-i+strlen(lst)+strlen(" }")+1;
	p = (char *) e_malloc(j*sizeof(char));
	sprintf(p, "%s%s%s }", frst, &OutBuf[i], lst);
	return p;
}

void
do_mine(SymList *s)
{	char mine[BigEnough];
	if (s->mark)
	{	sprintf(mine, "	%s = %s | %d;\n",
			s->sm->nme->str,
			s->sm->nme->str,
			s->mark&(DEF|USE|
			FCALL|REF0|REF1|REF2|DEREF|
			ALIAS|ARRAY_DECL|HIDE|DECL|
			USEafterdef|USEbeforedef|PARAM));
		vis_direct(mine);
	}
}

char *
do_dumode(treenode *n)
{	SymList *s;

	if (in_call || in_args || in_pars)
		goto out;

	if (!n)
	{	vis_direct("/* --no node-- */\n");
		abort();
	} else
	{	if (!n->hdr.defuse)
			return "comment";
	}

	for (s = n->hdr.defuse->def; s; s = s->nxt)
		do_mine(s);
	for (s = n->hdr.defuse->use; s; s = s->nxt)
		do_mine(s);
	for (s = n->hdr.defuse->other; s; s = s->nxt)
		do_mine(s);
out:
	return "comment";
}

char *
do_ccode(int lno)
{	char *tag, *p, *lst = "";
	int i = 0, nn, mm;

	if (strncmp(OutBuf, "C: ", strlen("C: ")) == 0)
	{	i = strlen("C: ");
		tag = "c_expr { ";

		if (strstr(OutBuf, ND_CHOICE)
		||  strcmp(&OutBuf[i], "1") == 0)
		{	p = "true";
			goto sc;
		}
	} else if (strncmp(OutBuf, "case ", strlen("case ")) == 0)
	{	i = strlen("case ");
		tag = "c_expr { ";

		if (strstr(OutBuf, ND_CHOICE))
		{	p = "true";
			goto sc;
		}
	} else if (strncmp(OutBuf, "R: ", 3) == 0)
	{	p = "goto Return";

		if (strlen(OutBuf) > strlen("R: return"))
		{	if (extended)
			{	char *z, more[1024];

				for (z = &OutBuf[strlen("R: return")]; *z; z++)
				{	if (*z == ' ' || *z == '\t')
						continue;
					else
						break;
				}
				/*
				   if there are multiple instantiations of this proctype/function,
				   then we want to make sure that the return value that is
				   written into a global temporary var cannot change until it is
				   picked up by the caller -- so we use a lck_fctname_ret that the
				   caller resets to zero when the value has been retrieved.
				   assumes there is only one possible return value of type long
				   should instead:
					find the var reference - determine its type and
					declare the global res_%s accordingly
				 */
				sprintf(more, "\tatomic { !lck_p_%s_ret -> lck_p_%s_ret = 1 };\n\t",
					fct_name, fct_name);
				vis_direct(more);
				if (strlen(z) > 0)
				{
#if 0
					sprintf(more, "c_code { now.res_p_%s = (long) %s; }; ",
						fct_name, z);
#else
					sprintf(more, "c_code { now.res_p_%s = (%s) %s; }; ",
						fct_name, fct_type, z);
#endif
					vis_direct(more);
				}
			} else if (!show_deps && Warnings)
			{	fprintf(stderr, "%s: line %3d, warning, args on"
					" return not preserved: ", progname, lno);
				fprintf(stderr, " %s\n", rm_decor(OutBuf));
			}
			extra_comment = 1;
		}
		goto sc;
	} else  if (OutBuf[1] == ':' && OutBuf[2] == ' '
		&& (OutBuf[0] == 'A' || OutBuf[0] == 'F'))
	{	i = strlen("A: ");

		if (strncmp(&OutBuf[i], "assert(", strlen("assert(")) == 0
		&&   strcmp(&OutBuf[strlen(OutBuf)-1], ")") == 0)
		{	int nx = strlen(OutBuf)-1;
			OutBuf[nx] = '\0';
			mm =  strlen("F: assert(");
			nn =  strlen("c_code [] { ; };") + strlen(&OutBuf[mm]) + 1;
			p = (char *) e_malloc(nn * sizeof(char));
			sprintf(p, "c_code [%s] { ; }", &OutBuf[mm]);

			OutBuf[nx] = ')';
			goto sc;
		}

		if (strncmp(&OutBuf[i], "printf(", strlen("printf(")) == 0)
		{	nn =  strlen(&OutBuf[i]) + 1 + strlen("c_code { P") + strlen(" } ");
			p = (char *) e_malloc(nn * sizeof(char));
			sprintf(p, "c_code { P%s;", &OutBuf[i+1]);	/* map to Printf */
			strcat(p, " }");
			/* fprintf(stderr, "p length %d nn %d, p=%s\n", strlen(p), nn, p); */
			goto sc;
		}
		goto same;
	} else if (strncmp(OutBuf, "D: ", 3) == 0)
	{	p = "comment"; /* no locals in c_code fragments */
		goto sc;
	} else
	{	i = 0;
same:		if (strlen(PreBuf) > 0)
		{	tag = (char *) e_malloc(strlen("c_code [] { ")+strlen(PreBuf)+1);
			sprintf(tag, "c_code [%s] { ", PreBuf);
		} else
			tag = "c_code { ";
		lst = ";";
	}
	p = form_c_tag(tag, i, lst);
sc:
	return p;
}

char *
vis_lookup(treenode *n)
{	char *p = "", *tag = "print";
	int i;

	extra_comment = 0;

	if (!vis
	||  strlen(OutBuf) == 0)
		return p;

	if (allkeep)
	{	if (strncmp(OutBuf, "R: ", 3) == 0)
			p = "goto Return";
		else
			p = "keep";
		goto sc;
	}
	if (strncmp(OutBuf, "default:", strlen("default:")) == 0)
	{	p = "keep";	/* mapped to 'else ->' later */
	} else if (du_mode)	/* def/use mode */
	{	p = do_dumode(n);
		goto sc;
	} else if (use_c_code)	/* all c_code mode, similar to allkeep mode */
	{	p = do_ccode(n?n->hdr.line:0);
		goto sc;
	} else
	{	for (i = 0; deflts[i].pat; i++)
			if (strncmp(OutBuf, deflts[i].pat, strlen(deflts[i].pat)) == 0)
			{	p = tag = deflts[i].val;
				break;
			}
		if (!strstr(OutBuf, "default:"))
		{
sc:			tag = p;
			if (PosElse)
				tag = "else";
			p = look_lut(OutBuf, tag, 1);	/* the one and only lookup in lut */
			via_substitute(AltBuf, p);
			p = AltBuf;
	}	}

	if (n && n->hdr.defuse)
	{	if (n->hdr.defuse->special)	/* touches data defined in .dat file */
		{	if (Verbose&2)
				printf("%d: <%s> .dat overrides .lut <%s> -> ",
				n->hdr.line, OutBuf, p);

			if (n->hdr.defuse->special == 8)	/* 8=keep (pure) */
				p = "keep";
			else if (n->hdr.defuse->special & 4)	/* 4=print   */
				p = "print";	/* highest priority */
			else if (n->hdr.defuse->special & 2)	/* 2=comment */
				p = "comment";	/* next highest */
			else if (n->hdr.defuse->special & 1)	/* 1=hide    */
				p = "hide";	/* lowest */

			if (Verbose&2)
				printf("<%s>\n", p);

			replace_lut(OutBuf, p);

			if (strstr(OutBuf, "C: "))
			{	static char OutBuf2[BigEnough];
				strcpy(OutBuf2, "C: !");	/* .dat override */
				strcat(OutBuf2, &OutBuf[3]);
				replace_lut(OutBuf2, p);
			}
		}
#if 0
		  else printf("%d: <%s> .dat preserve .lut <%s> -> special==0\n",
			n->hdr.line, OutBuf, p);
#endif
	}
#if 0
	  else printf("%d: <%s> .dat -> .lut <%s> nodefuse %d\n",
		n?n->hdr.line:0, OutBuf, p, (n && n->hdr.defuse)?n->hdr.defuse->special:0);
#endif
	ishidden = (strcmp(p, "print") == 0	/* no match for printf, only for print */
		||  strncmp(p, "comment", strlen("comment")) == 0
		||  strncmp(p, "hide",  strlen("hide"))  == 0);

	wasfalse = (strncmp(p, "false", strlen("false")) == 0);

// disabled, because it is not correctly processed in all cases:
//	wastrue  = (strncmp(p, "true",  strlen("true"))  == 0);
	waselse  = (strncmp(p, "else",  strlen("else"))  == 0);

	return p;
}

char *
do_difficult(char *s, int delta)
{
	if (strstr(SwLabel[sw_level-delta], ND_CHOICE))
		return "true ->";
	return s;
}

void
precondition(treenode *n)
{	PreC *p;

	p = (PreC *) e_malloc(sizeof(PreC));
	p->n = n;
	p->nxt = prec;
	prec = p;
if (0) fprintf(fp, "add prec\n");
}

void
act_prec(void)
{	PreC *p;
#if 0
	if (!prec)
	{	strcpy(PreBuf, "");
		return;
	}
#endif
if (0) fprintf(fp, "act prec\n");
	strcpy(Rem, OutBuf);	/* save */
	strcpy(OutBuf, "");

	for (p = prec; p; p = p->nxt)
	{	modex_recur(p->n);
		if (p->nxt)
		{	strcat(OutBuf, " && ");
	}	}
	if (strlen(OutBuf) > 0
	&&  strlen(Bounds) > 0)
	{	strcat(OutBuf, " && ");
	}
	strcat(OutBuf, Bounds);

if (0) fprintf(fp, " [[[ (%s) <==> [%s] ]]] ", OutBuf, Rem);

	strcpy(PreBuf, OutBuf);
	strcpy(OutBuf, Rem);	/* restore */
}

void
zap_prec(void)
{
if (0) fprintf(fp, "zap prec\n");
	prec = (PreC *) 0;
	strcpy(Bounds, "");
}

void
vis_flush(treenode *n)
{	char *w1, *w2, *p, *rd, *z;
	int realprint;

//fprintf(fp, " <<<VIS_FLUSH %d %d '%s'>>> ", vis, ByPass, OutBuf);

	if (!vis
	||  strlen(OutBuf) == 0)
	{	goto done;
	}
	if (ByPass)
	{	fprintf(fp, "%s", OutBuf);
		goto done;
	}

	act_prec();

	p  = vis_lookup(n);	/* does mapping through lut */
	rd = rm_decor(OutBuf);

	realprint = 0;
	if (strcmp(p, "warn") == 0)
	{	if (Warnings)
		fprintf(stderr, "%s: line %3d, warning, must abstract <%s>\n",
			progname, n->hdr.line, rd);
		p = "print";
	}

	if (strcmp(p, "print") == 0)
	{	realprint = 1;
anyway:		w1 = &rd[0];
		while ((w2 = strstr(w1, EnCode)) != NULL)
			*w2 = ':';
		w1 = &rd[0];
		while ((w2 = strchr(w1, '\"')) != NULL)
			*w2 = '\'';

		if (linenr)
			sprintf(tbuf, "printf(\"line %3d: %s\\n\"); ", n->hdr.line, rd);
		else
			sprintf(tbuf, "printf(\"%s\\n\"); ", rd);
		vis_direct(tbuf);
		if (realprint)
			modex_mark(n, HIDE);
		goto done;
	} else if (add_printfs && strncmp(rd, "D: ", 3) != 0)
	{	if (linenr)
			sprintf(tbuf, "printf(\"line %3d: %s\\n\"); ", n->hdr.line, rd);
		else
			sprintf(tbuf, "printf(\"%s\\n\"); ", rd);
		vis_direct(tbuf);
	}

	if (strncmp(p, "C_expr", strlen("C_expr")) == 0
	&& (strncmp(OutBuf, "A: ", strlen("A: ")) == 0
	||  strncmp(OutBuf, "F: ", strlen("F: ")) == 0))
	{	char *tag = "c_expr { ";
		if (strlen(PreBuf) > 0)	/* precondition [] */
		{	tag = (char *) e_malloc(strlen("c_expr [] { ")+strlen(PreBuf)+1);
			sprintf(tag, "c_expr [%s] { ", PreBuf);
		}
		p = form_c_tag(tag, strlen("A: "), "");
		goto mkstmnt;
	} else if (strncmp(p, "C_code", strlen("C_code")) == 0)
	{	p = do_ccode(n?n->hdr.line:0);
		goto mkstmnt;
	} else if (strncmp(p, "keep", strlen("keep")) == 0)
	{	if (allkeep && in_args)
		{	p = "comment";	/* override */
			goto mkinstead;
		}
		if (strncmp(rd, "case ", strlen("case ")) == 0)
		{	z = &rd[strlen("case ")];
			if (strstr(rd, ND_CHOICE))
			{	z = "true";	/* all cases become true */
			}
		} else if (strncmp(rd, "default:", strlen("default:")) == 0)
		{	z = do_difficult("else ->", 1);
			sawdefault = 1;
		} else if ((z = strchr(rd, ':')) != NULL)	/* A:, C:, etc. */
		{	z++;
		} else
		{	z = rd;
		}
		if (!strchr(z, ';') && !strstr(z, "->"))	/* new 12/18/00 */
		{	p = z;
			goto mkstmnt;
		}
		strcpy(tbuf, z); /* substitute happens in vis_lookup */
		goto mkafter;
	} else	if (strncmp(p, "hide", strlen("hide")) == 0
		||  strncmp(p, "comment", strlen("comment")) == 0)
	{
mkinstead:	modex_mark(n, HIDE);
	} else				/* mapped */
	{
mkstmnt:	sprintf(tbuf, "%s; ", p);
mkafter:	vis_direct(tbuf);
		modex_mark(n, 0);
	}

	if (linenr)
	{	if (extra_comment
		||  strcmp(p, "comment") == 0)
			sprintf(tbuf, "\t/* %d: %s */ ", linenr, rd);
		else
			sprintf(tbuf, "\t/* line %3d */ ", linenr);
	} else if (strcmp(p, "comment") == 0)
	{	sprintf(tbuf, "\t/* %s */ ", rd);
	}


	vis_direct(tbuf);
	if (printall && !in_pars && !in_args)
	{	goto anyway;
	}
done:
	zap_prec();
#if 0
 if (n)
 { sprintf(tbuf, "	/**** <%d> ****/\n", n->hdr.line);
   vis_direct(tbuf);
 }
#endif
	fflush(fp);
	return;
}

void
vis_print_d(int d)
{	char nw[64];

	if (!vis) return;

	sprintf(nw, "%d", d);
	strcat(OutBuf, nw);
}

void
vis_print_g(double d)
{	char nw[64];

	if (!vis) return;

	sprintf(nw, "%g", d);
	strcat(OutBuf, nw);
}

void
vis_print(char *nw)
{	char w0[1024], *w1, *w2;

	if (!vis || !nw) return;

	/* avoid modifying the argument, because
	   it could be a fixed string, like "\n"
	   which may be read-only
	 */
	w1 = (char *) w0;
	strncpy(w1, nw, sizeof(w0));
	while ((w2 = strchr(w1, '\n')) != NULL)
	{	*w2 = '\0';
		strcat(OutBuf, w1);
		strcat(OutBuf, "\\");
		strcat(OutBuf, "n");
		*w2 = '\n';
		w1 = ++w2;
	}
	strcat(OutBuf, w1);
}

void
vis_indent(int tb, char *s)	/* not via lookup table */
{	int j;

	if (!vis) return;

	for (j = tb-taboffset; j > 0; j--)
		vis_direct("  ");

	vis_direct(s);
}

void
check_fct(char *s, int tabs)
{	Fcts *f;

	for (f = fcts; f; f = f->nxt)
		if (strstr(s, f->nm))
		{	vis_indent(tabs, "fct_");
			vis_direct(f->tg);
			vis_direct("();\n");	/* inline call */
			break;
		}
}

#if 0
int
is_function(treenode *node)
{
	if (node && node->hdr.which == LEAF_T)
	{	leafnode *leaf = (leafnode*) node;
		if ((leaf->hdr.type == TN_IDENT)
		&&   leaf->syment)
		{	/* should check symbol table for the entry. */
			treenode *def = leaf->syment->node;
			if (def)
			{	return (def->hdr.type == TN_FUNC_DEF);
	}	}	}
	return 0;
}
#endif

void
push_dostack(treenode *tn)
{	char *nl;

	nl = (char *) e_malloc(16);
	sprintf(nl, "L_%d", do_uniq++);
	DoIncr[do_level] = tn;
	DoLabel[do_level++] = nl;
	vis_direct(nl);
	vis_direct(":\n");
}
void
use_dostack(int tabs)
{
	if (do_level < 1 || do_level > MAXLEVEL)
	{	if (preview) return;
		fprintf(stderr, "dolevel error %d\n", do_level);
		exit(1);
	}

	if (DoIncr[do_level-1])
		modex_any(DoIncr[do_level-1], tabs);

	vis_indent(tabs, "goto ");
	vis_direct(DoLabel[do_level-1]);
	vis_direct(";\n");
}
void
pop_dostack(void)
{
	do_level--;
}

void
push_swstack(char *s)
{	char *nl;

	nl = (char *) e_malloc(strlen(s)+1);
	strcpy(nl, s);
	SwLabel[sw_level++] = nl;
	sw_first = 0;
}
void
use_swstack(void)
{
	if (sw_level < 0 || sw_level > MAXLEVEL)
	{	fprintf(stderr, "swlevel error\n");
		exit(1);
	}
	vis_print(SwLabel[sw_level-1]);
	sw_first++;
}
void
pop_swstack(void)
{
	sw_level--;
	sw_first = 10;
}

void
fputs_metachr(char c, int in_str)
{	char cstr[2];
	
	if (vis)
	switch (c) {
	case '\'': if (in_str) vis_print("'"); else vis_print("\\'"); break;
	case '"':  if (in_str) vis_print("\\\""); else vis_print("\""); break;
	case '\0': vis_print("\\0"); break;
	case '\\': vis_print("\\\\"); break;
	case '\n': vis_print("\\n"); break;
	case '\t': vis_print("\\t"); break;
	case '\r': vis_print("\\r"); break;
	case '\f': vis_print("\\f"); break;
	case '\b': vis_print("\\b"); break;
	case '\v': vis_print("\\v"); break;
	case '\a': vis_print("\\a"); break;
	default:   cstr[0] = c;
		   cstr[1] = '\0';
		   vis_print(cstr);
		   break;
	}
}

void
fputs_metastr(char *str)
{
	if (!vis) return;

	while (*str)
	{	fputs_metachr(*str,1);
		str++;
	}
}

void
doindent(int depth)
{	int i;

	if (Verbose&2)
	for (i = 0; i < depth; i++)
		fprintf(stderr, "  ");
}

void
saw_variable(int ln, int which)
{
if (0) fprintf(stderr, "XXX {%d} '%s' '%s'\n", which, dername, dertype);
	if (strlen(dername) == 0)
	{	strcpy(dername, Ldername);
	}
	if (strlen(dertype) == 0)
	{	strcpy(dertype, Ldertype);
	}

if (0)	fprintf(stderr, "%3d:========name%d: '%s' '%s' '%s' ('%s') [obuf: %s] decor %d\n",
		ln, which, derscope, dertype, dername, derproc, OutBuf, with_decorations);

	if (!with_decorations)
	{	if (strcmp(derscope, "Global") == 0)
		{	add_global(dertype, dername, 1, ln);
		} else
		{	add_local(dertype, dername, derproc, 1, ln, 40);
		}
	} else
	{	if (strcmp(derscope, "Global") == 0)
		{	add_full_global(dertype, dername, 1, ln);
		} else
		{	add_full_local(dertype, dername, derproc, 1, ln);
	}	}

//	strcpy(Ldername, dername);
//	strcpy(Ldertype, dertype);
//	fprintf(stderr, "zap_2222 <%s> %d\n", dername, decl_cnt);
//	strcpy(dername, "");
//	strcpy(dertype, "");
}

int
istypedef(treenode *n)
{	treenode *nn;

	for (nn = n; nn; nn = nn->lnode)
	{	if (nn->hdr.which == LEAF_T)
		{	break;
		}
		if (nn->hdr.type == TN_TYPE)
		{
//if (nn->hdr.tok == EXTRN)
// fprintf(stderr, "Mumble\n");
			switch (nn->hdr.tok) {
			case TYPEDEF:
 if (0)
 { printf("saw Typedef\n");
   print_tree(n, stdout);
 }
				return 1;
			case TYPEDEF_NAME:
 if (0)
 { printf("saw Typedef Name\n");
   print_tree(n, stdout);
 }
				break;
			case CHAR:	/* constant */
			case CHAR_CONST:
			case INUM:
			case RNUM:
			case STRING:
				break;
			}
		} else if (nn->hdr.type == TN_IDENT)
		{	break;
	}	}

	return 0;
}

void
dotree(treenode *n, int depth, int nf)
{	char ebuf[256];

	if (!n) return;

	if (debug)
	{	doindent(depth);
		fprintf(stderr, "N-%p which = '%s', type = '%s' -- str '%s' (dtp '%s' dnm '%s')\n", n,
		name_of_nodetype(n->hdr.which),
		name_of_node(n->hdr.type),
		(((leafnode *)n)->data.sval)?((leafnode *)n)->data.sval->str:"-xx-",
		dertype, dername);
	}

	if (n->hdr.which == LEAF_T)
	{	leafnode *leaf = ((leafnode *)n);
		switch (n->hdr.type) {
		case TN_TYPE:
//fprintf(stderr, "Here (TN_TYPE %s) ", leaf->data.sval?leaf->data.sval->str: "??");
			doindent(depth);
			if (leaf->hdr.tok == TYPEDEF_NAME)
			{	if (debug) fprintf(stderr, "	%s\n",
					leaf->data.sval->str);
//fprintf(stderr, "TDN[%s] ", dername);
#if 0
				if (strlen(dername) > 0)
				{	strcat(dername, leaf->data.sval->str);
					break;
				}
#else
				strcpy(dername, "");
#endif
				if (strcmp(dertype, "Local") == 0)
				{	strcpy(dertype, "");
				}
				strcat(dertype, leaf->data.sval->str);
			} else
			{	if (debug) fprintf(stderr, ".	%s\n",
					toksym(leaf->hdr.tok,1));
//fprintf(stderr, "NTD ");
#if 0
				if (strlen(dername) > 0)
				{ strcat(dername, toksym(leaf->hdr.tok,1));
				  break;
				}
#endif
				if (strstr(dertype, "typedef"))
				{	strcat(dertype, " ");
					strcat(dertype, toksym(leaf->hdr.tok,1));
				} else
				{	if (strcmp(dertype, "Local") == 0)
					{	strcpy(dertype, "");
					}
					strcat(dertype, toksym(leaf->hdr.tok,1));
			}	}
			break;

		case TN_IDENT:
			if (debug)
			{	doindent(depth);
				fprintf(stderr, "\t%s {%s,%s}\n",
					leaf->data.sval->str, dername, dertype);
				doindent(depth);
				fprintf(stderr, "\tN-%p L-%p R-%p\n", n, n->lnode, n->rnode);
if (0)
fprintf(stderr, "lnode: %d %d\n", n->lnode->hdr.which, n->lnode->hdr.line);
			}
#if 0
			if (strncmp(dertype, "enum ", strlen("enum ")) == 0)
			{	if (strcmp(dertype, "enum ") == 0
				&&  strlen(dername) == 0)
				{	strcat(dertype, leaf->data.sval->str);
					break;
				}
				if (strstr(dertype, leaf->data.sval->str))
				{	break;
			}	}
#endif
			if (dername[0] != '\0'
			&&  dername[strlen(dername)-1] != '.'
			&&  dername[strlen(dername)-1] != '>')
			{	if (dername[strlen(dername)-1] == '*')
				{	strcat(dername, " ");
				} else
				{	if (strchr(dername, '[') != NULL)
 					{	fprintf(stderr, "%s: %s:%d: warning: ",
							progname, n->hdr.fnm, n->hdr.line);
						fprintf(stderr, "variable in array bound '%s %s %s ]'\n",
							dertype, dername, leaf->data.sval->str);
						fprintf(fp, "/* %s %s %s ] ** variable in array bound */\n",
							dertype, dername, leaf->data.sval->str);
					} else
					{
//						saw_variable(n->hdr.line, 2);	/* dubious */
						strcpy(dername, "");
			}	}	}

			strcat(dername, leaf->data.sval->str);

			if (nf
			&&  (!n->syment || n->syment->kind != TYPEDEF_ENTRY)	/* 2.6 new */
			&&  !strstr(dertype, "typedef")
			&&   strcmp(dertype, "enum ")   != 0
			&&   strcmp(dertype, "struct ") != 0)
			{
if (0) fprintf(stderr, "'%s' '%s'\tTyPe %d\n", dertype, dername, (n && n->syment)?n->syment->kind:-2);
				saw_variable(n->hdr.line, 20);	/* regular decl */
			}
			break;

		case TN_REAL:
			sprintf(ebuf, "%f", ((leafnode *) n)->data.dval);
			strcat(dername, ebuf);
			break;

		case TN_INT:
			/* always a decoration */
			sprintf(ebuf, "%d", leaf->data.ival);
			strcat(dername, ebuf);
			break;

		case TN_STRING:
			strcat(dername, "\"");
			strcat(dername, leaf->data.str);
			strcat(dername, "\"");
			break;

		case TN_EMPTY:
			break;

		default:
			fprintf(stderr, "%s: line %3d, unhandled leaftype, dotree %s\n",
				progname, n->hdr.line, name_of_node(n->hdr.type));
			exit(1);
			break;
		}

	} else if (n->hdr.which == NODE_T)
	{
		switch (n->hdr.type) {
		case TN_DECLS:
			dotree(n->rnode, depth+1, nf);

if (debug || ((Verbose&2) && with_decorations))
				fprintf(stderr, "%3d: decl1: %s %s %s (%s)\n",
				n->hdr.line, derscope, dertype, dername, derproc);

if (debug) fprintf(stderr, "zap_2340 <%s> %d\n", dername, decl_cnt);

			strcpy(dername, "");

			dotree(n->lnode, depth+1, nf);

if (debug || ((Verbose&2) && with_decorations))
				fprintf(stderr, "%3d: decl2: %s %s %s (%s)\n",
				n->hdr.line, derscope, dertype, dername, derproc);
			return;

		case TN_PNTR:
			if (with_decorations)
			{
				if (strlen(dername) > 0
				&&  dername[strlen(dername)-1] != '*')
				{	saw_variable(n->hdr.line, 25);
					strcpy(dername, "*");
				} else
					strcat(dername, "*");
			}
			break;

		case TN_ARRAY_DECL:
			if (!with_decorations)
				dotree(n->lnode, depth+1, 1);
			else
			{	dotree(n->lnode, depth+1, 0);
				if (strlen(dername) == 0)	/* int a[6][7] */
					strcpy(dername, Ldername);
				strcat(dername, "[");
				dotree(n->rnode, depth+1, 0);
				strcat(dername, "]");
				saw_variable(n->hdr.line, 3);	/* array decl */
			}
			return;

		case TN_TYPE_LIST:
			if (n->lnode
			&&  n->lnode->hdr.which == LEAF_T
			&&  ((leafnode *) n->lnode)->hdr.tok == EXTRN)
			{	return;		// was: break;
			}
			if (n->lnode && n->lnode->hdr.which == LEAF_T
			&&  strcmp(dertype, "unsigned ") == 0)
			{	// strcat(dertype, toksym(n->lnode->hdr.tok, 1));	/* new */
			} else
			{	strcpy(dertype, "");
			}
			break;
		case TN_TYPE_NME:
			break;

		case TN_DECL:
			if (istypedef(n->lnode))
				return;

			dotree(n->lnode, depth+1, nf);
if (0)			fprintf(stderr, "%3d: -decl: %s %s %s (%s) ..%d\n",
				n->hdr.line, derscope, dertype, dername, derproc, nf);

			dotree(n->rnode, depth+1, nf);
if (0)			fprintf(stderr, "%3d: +decl: %s %s %s (%s) ..%d.. ",
				n->hdr.line, derscope, dertype, dername, derproc, nf);


			if (nf
			&& (strcmp(dertype, "enum") == 0
			||  strcmp(dertype, "struct") == 0))
				saw_variable(n->hdr.line, 1);	/* enum or struct decl */
			
			return;
		case TN_ASSIGN:	/* initializer */

			dotree(n->lnode, depth+1, nf);	/* the name */
			if (with_decorations)
			{ int ovis = vis;
				strcat(dername, " = ");
				vis = 1;
				strcpy(Rem2, OutBuf);
				vis_start();	/* loss of D: type prefix */
				modex_recur(n->rnode);
				strcat(dername, OutBuf);
				vis_start();
				strcpy(OutBuf, Rem2);
				vis = ovis;

				if (strcmp(derscope, "Global") == 0)
				{	add_full_global(dertype, dername, 1, n->hdr.line);
				} else
				{	add_full_local(dertype, dername, derproc, 1, n->hdr.line);
			}	}
			return;
		case TN_FUNC_DECL:
			if (0) fprintf(stderr, "ignore -- a fucntion declaration\n");
			return;	/* ignore function declararions */

		case TN_PARAM_LIST:
			break;	/* return; */

		case TN_OBJ_REF:
if (debug || ((Verbose&2) && with_decorations))
				fprintf(stderr, "objref: <%s> <%s> <%s>	%s before\n",
					derscope, dertype, dername,
					toksym(((leafnode *)n)->hdr.tok,1));
// fprintf(stderr, "XX: %s -> %s\n", dertype, toksym(((leafnode *)n)->hdr.tok,1));
			strcpy(dertype, toksym(((leafnode *)n)->hdr.tok,1));
			dotree(n->lnode, depth+1, nf);

			strcat(dertype, dername);	/* enum opt_tag */
			strcpy(dername, "");

if (debug || ((Verbose&2) && with_decorations))
				fprintf(stderr, "objref: <%s> <%s> <%s>	%s between\n",
					derscope, dertype, dername,
					toksym(((leafnode *)n)->hdr.tok,1));

			dotree(n->rnode, depth+1, nf); /* definitions list */

if (debug || ((Verbose&2) && with_decorations))
				fprintf(stderr, "objref: <%s> <%s> <%s>	%s after\n\n",
				derscope, dertype, dername,
				toksym(((leafnode *)n)->hdr.tok,1));

if (0) fprintf(stderr, "\tTYPE %d\n", (n && n->lnode && n->syment)?n->lnode->syment->kind:-1);

			strcpy(Ldername, dername);
if (debug) fprintf(stderr, "zap_2439 <%s> %d\n", dername, decl_cnt);
			strcpy(dername, "");
			return;

		case TN_EXPR:
			switch (n->hdr.tok) {
			case CASE:
				strcat(dername, toksym(n->hdr.tok,1));
				break;
			case SIZEOF:
				strcat(dername, toksym(n->hdr.tok,0));
				strcat(dername, "(");
				dotree(n->lnode, depth+1, nf);
				dotree(n->rnode, depth+1, nf);
				strcat(dername, ")");
				return;
			case INCR:
			case DECR:
				dotree(n->lnode, depth+1, nf);
				strcat(dername, toksym(n->hdr.tok,1));
				dotree(n->rnode, depth+1, nf);
				return;
			case B_OR:
tryonce:			if (preview)
				{	int x = precomputable(n);
					if (x)
					{	char buf[256];
						sprintf(buf, "%d", x);
						vis_print(buf);
						break;
				}	}
				goto same;
			case B_AND:
				if (!n->lnode)
				{	strcat(dername, toksym(n->hdr.tok,1));
					strcat(dername, "(");
					dotree(n->rnode, depth+1, nf);
					strcat(dername, ")");
					return;
				}
				goto tryonce;
			default:
same:				strcat(dername, "(");
				dotree(n->lnode, depth+1, nf);
				strcat(dername, toksym(n->hdr.tok,1));
				dotree(n->rnode, depth+1, nf);
				strcat(dername, ")");
				return;
			}
			break;

		case  TN_OBJ_DEF:
			strcat(dertype, toksym(((leafnode *) n)->hdr.tok,1));
			dotree(n->lnode, depth+1, 0);
			strcat(dertype, " {\n");
			dotree(n->rnode, depth+1, 0);
			strcat(dertype, "}");
			return;

		case TN_SELECT:
			dotree(n->lnode, depth+1, 0);
			if (n->hdr.tok == ARROW)
				strcat(dername, "->");
			else
				strcat(dername, ".");
			dotree(n->rnode, depth+1, 0);
			return;

		case TN_CAST:
#if 0
/* this creates a syntax error
   in spin for mapped declarations.
   should allow it for nonmappables though
*/
			strcat(dername, "(");
			dotree(n->lnode, depth+1, nf);
			strcat(dername, ")");
#endif
			dotree(n->rnode, depth+1, nf);
			return;

		case  TN_COMP_DECL:
		case  TN_FIELD_LIST:
		case  TN_INDEX:
			return;
		default:
			if (vis
			&& !preview
			&&  strcmp(fct_name, "") != 0
			&&  (lastln != n->hdr.line
			||  lastpb != n->hdr.type))
			fprintf(stderr, "%s: line %3d, skipping unhandled case (%s)\n",
				progname, n->hdr.line, name_of_node(n->hdr.type));

			lastln = n->hdr.line;
			lastpb = n->hdr.type;

			return;
		}

if (debug)
		{	doindent(depth);
			fprintf(stderr, "L: ");
		}
		dotree(n->lnode, depth+1, nf);

if (debug)
		{	doindent(depth);
			fprintf(stderr, "R: ");
		}
		dotree(n->rnode, depth+1, nf);
	}
}

void
derive_type(char *s, treenode *n)
{
	strcpy(derscope, s);
	strcpy(dertype, "");
	strcpy(dername, "");
	dotree(n, 0, 1);	/* calls 'add_global' and 'add_local'
				 * to instantiate rewrite rules
				 */
	strcpy(derscope, s);
	strcpy(dertype, "");
	strcpy(dername, "");
	with_decorations = 1;	/* reproduce the full declarations */
	dotree(n, 0, 1);
	with_decorations = 0;	/* such as [] and '*' with initialization */
}

void
do_prefix(leafnode *n)
{	Fcts *g;
	static char buf[1024];
	char *s;

	s = n->data.sval->str;
	/* fp=stdout; */
	if (0 && fp)	fprintf(fp, "\n<<%3d: do_prefix --%s-- <%s> <%s> <%s> (%d,%d,%d) [%s] (%d,%d)>>\n",
		n->hdr.line, s, dertype, derproc, dername,
		in_call, in_args, is_label, OutBuf, in_call, ByPass);

	if (strlen(OutBuf) > 2
	&& (strstr(&OutBuf[strlen(OutBuf)-2], "->")
	||  strstr(&OutBuf[strlen(OutBuf)-1], ".")))
		return;	/* no prefix here */

	if (ByPass)
	{	if(0) fprintf(stderr, "	bypass (%d)\n", ByPass);
		return;	/* in the middle of a struct reference */
	}

	if (!n->syment)	/* not a variable name - i.e., no declaration appears in the source */
	{
if (debug)		fprintf(stderr, "%3d: --not a varname --%s-- <%s> <%s> <%s> (%d,%d,%d)\n",
			n->hdr.line, s, dertype, derproc, dername,
			in_call, in_args, is_label);

		/* it could have been declared in the lut... */
		for (g = modex_globals; g; g = g->nxt)
			if (!g->derived && strcmp(g->nm, s) == 0)
				goto b;

		add_hidden("Global", s, 1, n->hdr.line);
		return;
	}

	if (n->syment->kind == LABEL_ENTRY
	||  n->syment->kind == TAG_ENTRY)
		return;

if (0 && fp) fprintf(fp, "\n\t/* maptype=%d - kind=%d - decl_level=%d - owner_t=%d owner=%s */\n",
		map_type(s, n->syment),
		n->syment->kind,
		n->syment->decl_level,
		n->syment->nes && n->syment->nes->owner ? n->syment->nes->owner_t : -1,
		n->syment->nes && n->syment->nes->owner ? n->syment->nes->owner : "no owner");

	switch (map_type(s, n->syment)) {
	case 1:	/* local */
a:		if (strcmp(wanttype, "inline") != 0)
		{	sprintf(buf, "Pp_%s->", fct_name);
			vis_print(buf);
		}
		break;

	case 2:	/* global */
b:		vis_print("now.");
		break;

	case 3:	/* hidden global */
c:		break;

	default: /* undefined */
		if (in_call) return;	/* function name */

		if (n->syment->decl_level < 3)	/* global scope */
		{	char oder[512];
			strcpy(oder, derproc);
			strcpy(derproc, "");
			derive_type("Global", n->syment->node);
			if (strcmp(dertype, "extern ") == 0)
				break;
			strcpy(derproc, oder);

			if (!imported(dername, "Global", 0))
				goto c;

			if (n->syment->kind == TYPEDEF_ENTRY)	/* 2.6 new */
				goto c;

			add_full_global(dertype, dername, 1, n->hdr.line);
			goto b;
		} else if (n->syment->nes && n->syment->nes->owner)
		{
			if (in_args)
				strcpy(derproc, fct_name);
			else
				strcpy(derproc, n->syment->nes->owner);
			derive_type("Local", n->syment->node);
			if (Verbose&2)
			fprintf(stderr, "%3d, ==s=%s, proc=%s, type=%s, name=%s, own=%s, [obuf= %s]\n",
			n->hdr.line, s, derproc, dertype, dername, n->syment->nes->owner, OutBuf);

			if (strcmp(n->syment->nes->owner, "-") != 0)
			{
				if (!imported(dername, derproc, 0))
					goto c;
			
				add_full_local(dertype, dername, derproc, 1, n->hdr.line);
				goto a;
			}

			if (strcmp(dername, "") != 0
			&&  dername[strlen(dername)-1] != '*')
			{	if (debug || (Verbose&2))
				fprintf(stderr, "%3d: derived hidden <%s> <%s> <%s> <%s> (%d %d %d)\n",
					n->hdr.line,
					dertype, dername, derproc, fct_name,
					in_call, in_args, is_label);

				if (strlen(fct_name) > 0
				&&  in_args)	/* formal params */
					add_local(dertype, dername, fct_name, 1, n->hdr.line, 50);
				else
					add_hidden(dertype, dername, 1, n->hdr.line);
			}
			break;
		}
		/* else leave it hidden -- shouldn't happen */
		if (0 /* (Verbose&2) */)
		{	fprintf(stderr, "%s: unexpected (var %s) kind=%d\n", s,
				progname, n->syment->kind);
			if (fp) fprintf(fp, "  /* unexpected (var %s) */", s);
		}

		break;
	}
}

static int par_cnt = 0;

static void
fct_params(treenode *fct, treenode *pars)
{
	if (!fct || !pars || !vis) return;

	switch (pars->hdr.which) {
	case NODE_T:
		switch (pars->hdr.type) {
		case TN_PARAM_LIST:
		case TN_EXPR_LIST:
			fct_params(fct, pars->lnode);
			if (pars->rnode)
			{	fct_params(fct, pars->rnode);
			}
			break;
		default:
			goto A;
		}
		break;
	default:
A:		fprintf(fp, "\t\tc_code { now.par%d_", par_cnt++);
		print_tree(fct, fp);
		fprintf(fp, " = ");
#if 1
		strcpy(AltBuf, OutBuf);
		strcpy(OutBuf, "");
		modex_recur(pars);
		fprintf(fp, "%s", OutBuf);	// fct_params()
		strcpy(OutBuf, AltBuf);
		strcpy(AltBuf, "-x-x-");
#else
		if (((leafnode *) pars)->hdr.type == TN_IDENT)
		{	strcpy(AltBuf, OutBuf);
			strcpy(OutBuf, "");
			do_prefix((leafnode *)pars);
			fprintf(fp, OutBuf);	// fct_params()
			strcpy(OutBuf, AltBuf);
			strcpy(AltBuf, "-x-x-");
		}
		print_recur(pars, fp);
#endif
		fprintf(fp, "; };\n");
		break;
	}
}

static int
precomputable(treenode *n)
{	int lft, rgt;

	if (!n) return 0;

	switch (n->hdr.tok) {
	case INUM:
		return ((leafnode *) n)->data.ival;
	case B_OR:
		lft = precomputable(n->lnode);
		rgt = precomputable(n->rnode);
		if (!lft || !rgt) return 0;
		return (lft|rgt);
	case B_AND:
		lft = precomputable(n->lnode);
		rgt = precomputable(n->rnode);
		if (!lft || !rgt) return 0;
		return (lft&rgt);
	default:
		fprintf(stderr, "modex: %s:%d unexpected token, precomputable '%s'\n",
			n->hdr.fnm, n->hdr.line, toksym(n->hdr.tok,0));
	case DOT:
	case ARROW:
	case IDENT:
		return 0;
	}
#if 0
	debug_node(n, 1, "");
#endif
	return 0;
}

static char *thread_id;
static char *thread_arg;
static char *join_id;

void
set_join_id(void)	// from first '(' til first ',' in OutBuf
{	char *s, *e;

	join_id = 0;
	s = strchr(OutBuf, '(');
	if (!s) { return; };
	e = strchr(s+1, ',');
	if (!e || e-s <= 1) { return; }

	join_id = (char *) e_malloc((e-s) * sizeof(char));
	strncpy(join_id, s+1, (e-s)-1);
}

void
set_create_id(void)	// from the 1st '&(' to the 1st '),' in OutBuf
{	char *s, *e;

	join_id = 0;
	s = strchr(OutBuf, '&');
	e = strchr(s+1, ')');
	if (!e || e-s <= 1) { return; }

	join_id = (char *) e_malloc((e-s) * sizeof(char));
	strncpy(join_id, s+2, (e-s)-1-1);
}

void
set_thread_id(void)	// from the 2nd ',' to the third ',' in OutBuf
{	char *s, *e;

	thread_id = 0;
	s = strchr(OutBuf, ',');	// 1st
	if (!s) { return; }
	s = strchr(s+1, ',');		// 2nd
	if (!s) { return; }
	e = strchr(s+1, '>');		// Pmain->threadname
	if (!e)
	{	s = strchr(s+1, '.');	// now.threadname
		if (!s) { return; }
	} else
	{	s = e;
	}
	e = strchr(s+1, ',');		// 3rd
	if (!e || e-s <= 1) { return; }

	if (*(e-1) == ')') e--;		// &(Pmain->funcA),

	thread_id = (char *) e_malloc((e-s) * sizeof(char));
	strncpy(thread_id, s+1, (e-s)-1);
}

void
set_thread_arg(void)	// from the 3rd ',' to the closing ')' in OutBuf
{	char *s, *e;

	thread_arg = 0;
	s = strchr(OutBuf, ',');	// 1st
	if (!s) { return; }
	s = strchr(s+1, ',');		// 2nd
	if (!s) { return; }
	s = strchr(s+1, ',');		// 3rd
	if (!s) { return; }
	e = strrchr(s+1, ')');
	if (!e) { return; }

	thread_arg = (char *) e_malloc(((e-s)+1) * sizeof(char));
	strncpy(thread_arg, s+1, (e-s)-1);
}

typedef struct Map {
	char *from;
	char *to;
	struct Map *nxt;
} Map;
Map *mapped;

void
remember(char *s, char *t)
{	Map *m;

	m = (Map *) e_malloc(sizeof(Map));
	m->from = s;
	m->to = t;
	m->nxt = mapped;
	mapped = m;
if (0)	fprintf(stderr, "remember: '%s' / '%s'\n", s, t);
}

char *
look_map(char *s)
{	Map *m;

	for (m = mapped; m; m = m->nxt)
	{	if (strcmp(m->from, s) == 0)
		{	return m->to;
	}	}
	fprintf(stderr, "modex: error: failed to recognize pthread_create call: '%s'\n", s);
	return "_unknown_";
}

static int special_case;

static void
fix_side_effect(char *t)
{
	do {	--t;
		if (*t != ' ' && *t != '\t')
		{	break;
		}
	} while (t > OutBuf);

	if (*t == '=' && t > OutBuf && isalnum((int)*(t-1)))	// found it
	{	int n, m = 0;
		for (n = 0; n < strlen(OutBuf); n++)
		{	if (OutBuf[n] == '(')
			{	m++;
			} else if (OutBuf[n] == ')')
			{	m--;
		}	}
		strcpy(OutBuf, "C: ");
		while (m-- > 0)
		{	strcat(OutBuf, "(");
		}
		strcat(OutBuf, "0");
	}
}

static void
strip_pthread_fct(char *what)
{	char *q, *r, *s, *t;

	q = t = strstr(OutBuf, what);
	if (!q) return;

	q += strlen(what);
	r = strrchr(q, ')');
	if (!r) return;

	for (s = t; s <= r; s++)
	{	*s = ' ';	// erase the fct call
	}
	*t = '0';
	// in the model no error is returned from pthread_create or pthread_join

	// sample result in OutBuf at this point: "C: (0!=(Pmain->err=0"
	// the original condition had a call to 'what()' inside this condition
	// the 'what()' call was moved outside the condition
	//
	// we replace the removed function call with 0, meaning non-failure
	// if the original condition had an embedded assignment of the result
	// we need to remove that side-effect as well (hoping that the variable
	// assigned zero does not get reused somewhere later -- this is a hack

	// look if there was an assignment operator directly before 'what()'
	fix_side_effect(t);
}

static void
replace_pthread_join(void)
{	char *q, *r;

	q = strstr(OutBuf, "pthread_join(");
	if (!q) return;

	r = q + strlen("pthread_join(");
	// keep the arguments
	// and make this a blocking statement
	fprintf(fp, "	c_expr { spin_join(%s }\n", r);

	strip_pthread_fct("pthread_join(");
}

static int
thread_has_params(char *s)
{	Fcts *g;

	for (g = modex_locals; g; g = g->nxt)
	{	if (strcmp(g->tg, s) == 0
		&&  g->fc == 2)
		{	return 1;
	}	}
	return 0;
}

static void
handle_pthread_create(int which)
{
	// F:  pthread_create(&(t2),0,"thr2",0);
	set_create_id();
	set_thread_id();
	set_thread_arg();
	remember(join_id, thread_id);

	if (!fp) return;

	// fprintf(stderr, "handle %d: %s\n", which, OutBuf);

	if (0)
	{	fprintf(stderr, "join_id '%s', thread_id '%s', thread_arg '%s'\n",
			join_id?join_id:"?",
			thread_id?thread_id:"?",
			thread_arg?thread_arg:"?");
	}

	if (thread_id && thread_arg)
	{	if (dynamic)
		{	fprintf(fp, "\tatomic { _nr_pr < %d -> run p_%s() };\n",
				dynamic, thread_id);
		}
		fprintf(fp, "\tatomic {\n");
		fprintf(fp, "\t	lck_p_%s == 0 && empty(req_cll_p_%s) -> req_cll_p_%s!_pid;\n",
			thread_id, thread_id, thread_id);

		if (thread_has_params(thread_id))
		{	fprintf(fp, "\t	c_code { now.par0_%s = %s; };\n",
				thread_id, thread_arg);
		}
		fprintf(fp, "\t	exc_cll_p_%s!_pid;\n", thread_id);
		fprintf(fp, "\t}\n");
		fprintf(fp, "//\tret_p_%s?eval(_pid);\n", thread_id);
		fprintf(fp, "//\tc_code { now.lck_p_%s_ret = 0; };\n", thread_id);
	} else
	{	char *q, *r, *s, *t;
		q = &OutBuf[strlen("F: pthread_create(&(")];
					if (!q) goto bad;
		r = strchr(q, ')');	if (!r) goto bad;
		*r = '\0';
		s = strchr((r+1), '"');	if (!s) goto bad;
		t = strchr((s+1), '"');	if (!t) goto bad;
		*t = '\0';
		fprintf(fp, "\t%s%c = run p_%s();\n",
			q,
			(*q == '(')?')':' ',
			s+1);
bad:
		if (strlen(OutBuf) > 0)
		{	fprintf(stderr, "warning: unhandled type of %s (%s/%s/%s)\n",
				OutBuf,
				thread_id?thread_id:"--",
				thread_arg?thread_arg:"--",
				join_id?join_id:"--");
		}
	}
	OutBuf[0] = '\0';
}

static void
setup_fct_call(treenode *root, char *s)
{
	if (dynamic)
	{	fprintf(fp, "\n\n\trun p_%s();", s);
	}
	fprintf(fp, "\n\n\tatomic {\n");
	fprintf(fp, "\t\tlck_p_%s == 0 && empty(req_cll_p_%s) -> ", s, s); 
	fprintf(fp, "req_cll_p_%s!_pid; /* req to call */\n", s);
	fct_params(root->lnode, root->rnode);	/* set params */
	fprintf(fp, "\t\texc_cll_p_%s!_pid; /* start call */\n", s);
	fprintf(fp, "\t}\n"); /* end of atomic */
	fprintf(fp, "\tret_p_%s?eval(_pid);\n\n\t", s);
}

static void
handle_instrumented(treenode *root, char *my_fname)
{	int noreset = 0;

	if (in_pars == 1)	/* parentheses */
	{	par_cnt = 0;

		setup_fct_call(root, my_fname);

		// handle a possible return value from the call

		if (strncmp(OrigBuf, "A: ", 3) == 0)	// called in assignment
		{	char *pq1, *pq2;
			pq1 = strrchr(OrigBuf, '[');
			pq2 = strrchr(OrigBuf, ']');
			if (pq1 && (!pq2 || pq1 > pq2))
			{	goto here;
			}

			strcat(OrigBuf, " now.res_p_");
			strcat(OrigBuf, my_fname);
		} else if (strncmp(OrigBuf, "C: ", 3) == 0) // called in condition
		{	strcat(OrigBuf, " now.res_p_");
			strcat(OrigBuf, my_fname);

			// already generated the return value of the call
			// fprintf(fp, " ret_%s?eval(_pid);\n", my_fname);
			// reset the return lock early -- it is otherwise done below
			// this risks a race-condition if another caller of the function
			// completes, and sets the return value to a different value
			// before this caller can read the current one
			// we have to reset early though, because this cannot appear inside
			// the condition

			fprintf(fp, " lck_p_%s_ret = 0;\n", my_fname);
			noreset = 1;	// dont reset again
			if ((Verbose&2) && is_do_condition)
			{	fprintf(stderr, "%s: %s:%d: warning, calling instrumented ",
					progname, root->hdr.fnm, root->hdr.line);
				fprintf(stderr, "function %s() in a loop-condition\n", my_fname);

			}

		} else if (strncmp(OrigBuf, "D: ", 3) == 0) // called in declaration
		{	strcat(OrigBuf, " now.res_p_");
			strcat(OrigBuf, my_fname);
			
			fprintf(stderr, "%s: %s:%d: error, cannot use instrumented ",
				progname, root->hdr.fnm, root->hdr.line);
			fprintf(stderr, "function call %s() inside a declaration\n",
				my_fname);
		} else if (strncmp(OrigBuf, "R: ", 3) == 0)	// called in return stmnt */
		{	// fprintf(stderr, "No problem: %s\n", OrigBuf);
			goto here;
		} else	/* F: */
		{	char *p1, *p2;
here:			p1 = strrchr(OrigBuf, '[');
			p2 = strrchr(OrigBuf, ']');
			if (p1 && (!p2 || p1 > p2))
			{
				fprintf(stderr, "%s: %s:%d: warning, using instrumented ",
					progname, root->hdr.fnm, root->hdr.line);
				fprintf(stderr, "function call %s() in array index (%s)\n",
					my_fname, OrigBuf);

				fprintf(fp, " lck_p_%s_ret = 0;\n", my_fname);
				noreset = 1;	// dont reset again

				/* assuming there's just one function call... */
				strcat(OrigBuf, " now.res_p_");
				strcat(OrigBuf, my_fname);
				strcat(OrigBuf, " ");
			}
		//	strcat(OrigBuf, " /* ");
		//	strcat(OrigBuf, my_fname); /* no return val */
		//	strcat(OrigBuf, "()  */");
		}

		// lck_ is set when the function returns a value
		// the lock should be reset, whether or not the return
		// value is picked up by the caller, i.e., for both A: and F:

		if (!noreset)	// if not already done
		{	strcat(OrigBuf, "; now.lck_p_");
			strcat(OrigBuf, my_fname);
			strcat(OrigBuf, "_ret = 0");
		}
		strcpy(OutBuf, OrigBuf);
	} else
	{	fprintf(fp, "\t/* fct call in paramlist: %s */", my_fname);
		fprintf(stderr, "%s: %s:%d: error, cannot use call to ",
			progname, root->hdr.fnm, root->hdr.line);
		fprintf(stderr, "instrumented fct %s() in a param list\n", my_fname);
	}
}

static void
modex_recur(treenode *root)
{	leafnode *leaf;

	if (!root) return;

if (0)
	fprintf(fp, "\n\trecur %3d: type %s -- %s <%s>\n",
		root->hdr.line,
		name_of_nodetype(root->hdr.which),
		name_of_node(root->hdr.type),
		OutBuf);

	if (debug && vis)
	{	printf(" {%s} ", name_of_node(root->hdr.type));
	}
	switch (root->hdr.which) {
	case LEAF_T:
		leaf = (leafnode *) root;
if (0) fprintf(fp, "	%s: recur: leaf %s\n",
			progname, name_of_node(leaf->hdr.type));

		switch (leaf->hdr.type) {
		case TN_IDENT:	/* modex_recur */
			if (!preview)
			{	if (in_call && !strcmp(leaf->data.sval->str, "malloc"))
				{	strcat(OutBuf, "spin_malloc");
					used_spin_malloc++;
					break;
				}
				if (in_call && !strcmp(leaf->data.sval->str, "free"))
				{	strcat(OutBuf, "spin_free");
					used_spin_malloc++;
					break;
				}
				if (in_pars && is_pname(leaf->data.sval->str))
				{	strcat(OutBuf, "\"");
					strcat(OutBuf, leaf->data.sval->str);
					strcat(OutBuf, "\"");
					break;
				} else
				{	do_prefix(leaf);
			}	}
			vis_print(leaf->data.sval->str);
if (0) fprintf(fp, "Done: <<%s>>\n", OutBuf);
			if (Warnings && enum_list_cnt > 0)
			fprintf(stderr, "%s: line %3d, provide initialization for enum %s = %d\n",
				progname, root->hdr.line, leaf->data.sval->str, enum_list_cnt);
			break;

		case TN_LABEL:
			if (leaf->hdr.tok == DEFLT)
				vis_print("default");
			else
				vis_print(leaf->data.sval->str);
			vis_print(": ");
			break;
		case TN_STRING:
			vis_print("\"");
			fputs_metastr(leaf->data.str);
			vis_print("\"");
			break;
		case TN_TYPE:
			if (leaf->hdr.tok != TYPEDEF_NAME)
			{	vis_print(toksym(leaf->hdr.tok,1));
if (0 && vis) printf("%s:%3d: saw TN_TYPE %s\n",
	leaf->hdr.fnm, leaf->hdr.line,
	toksym(leaf->hdr.tok,1));
			} else
			{	vis_print(leaf->data.sval->str);
				vis_print(" ");
if (0 && vis) printf("%s:%3d: saw TYPEDEF_NAME %s\n",
	leaf->hdr.fnm, leaf->hdr.line,
	leaf->data.sval->str);
			}
			break;
		case TN_REAL:
			vis_print_g(leaf->data.dval);
			break;
		case TN_INT:
			if (leaf->hdr.tok == CHAR_CONST)
			{	vis_print("'");
				fputs_metachr((char) leaf->data.ival, 0);
				vis_print("'");
			} else
				vis_print_d(leaf->data.ival);
			break;
		case TN_COMMENT:
			vis_print("\n");
			vis_print(leaf->data.str);
			vis_print("\n");
			break;
		case TN_ELLIPSIS:
			vis_print("...");
			break;
		default:
			fprintf(stderr, "%s: recur: unexpected leaf %s\n",
				progname, name_of_node(leaf->hdr.type));
			break;
		}
		break;
	case NODE_T:
if (0) fprintf(fp, "	%s: recur: node %s <%s>%d\n",
			progname, name_of_node(root->hdr.type), OutBuf, do_level);
		switch (root->hdr.type) {
		case TN_TYPE_NME:
		case TN_TRANS_LIST:
		case TN_NAME_LIST:
		case TN_FIELD_LIST:
		case TN_IDENT_LIST:
		case TN_TYPE_LIST:
			if (root->lnode
			&&  root->lnode->hdr.which == LEAF_T
			&&  ((leafnode *) root->lnode)->hdr.tok == EXTRN)
			{	break;
			}
			modex_recur(root->lnode);
			modex_recur(root->rnode);
			break;
		case TN_FUNC_CALL:
			storefname(root);
			if (vis && in_pars == 0)
			{
				strcpy(OrigBuf, OutBuf);
			}
			in_call++;
			modex_recur(root->lnode);
			in_call--;

			if (preview)
			{	vis_print("()");
				break;
			}

			vis_print("(");
			if (strcmp(OutBuf, "F: assert_r(") == 0)
			{	ax_new_assert(0, root->rnode);
				if (i_assert)
				{	sprintf(OutBuf, "F: _ax_start(_nq%d_, _q%d_)",
						ax_prop_nr, ax_prop_nr);
				} else
				{	sprintf(OutBuf, "D: _ax_start(_nq%d_, _q%d_)",
						ax_prop_nr, ax_prop_nr);
				}
				ax_prop_nr++;
			} else if (strcmp(OutBuf, "F: assert_p(") == 0)
			{	ax_new_assert(1, root->rnode);
				if (i_assert)
					sprintf(OutBuf, "F: _ax_start(_q%d_, _r%d_)",
					ax_prop_nr, ax_prop_nr);
				else	/* map to comment */
					sprintf(OutBuf, "D: _ax_start(_q%d_, _r%d_)",
					ax_prop_nr, ax_prop_nr);
				ax_prop_nr++;
			} else
			{	if (strcmp(OutBuf, "F: pthread_join(") == 0)
				{	strcpy(OutBuf, "C: spin_join(");
#ifdef SV_COMP
				} else if (strncmp(OutBuf, "F: __VERIFIER_assert", 20) == 0)
				{	strcpy(OutBuf, "F: assert(");
				} else if (strncmp(OutBuf, "F: __VERIFIER_error", 19) == 0)
				{	strcpy(OutBuf, "F: assert(2==1");
				} else if (strncmp(OutBuf, "F: __VERIFIER_assume", 20) == 0)
				{	strcpy(OutBuf, "C: (");
#endif
				} else if (strncmp(OutBuf, "F: pthread_mutex_lock(", 22) == 0)
				{	special_case = 1;
					fprintf(fp, "atomic { ");
					strcpy(OutBuf, "C: spin_mutex_free(");
				} else if (strncmp(OutBuf, "F: pthread_cond_wait(", 21) == 0)
				{	static int new_labs = 0;
					special_case = 3;
					strcpy(OutBuf, "");
					in_pars++;
					modex_recur(root->rnode);	/* 2 arguments */
					in_pars--;
					char *z = strchr(OutBuf, ',');	/* 2nd arg */
					if (!z)
					{	fprintf(stderr, "error: bad call to %s\n", OutBuf);
						fflush(fp);
						exit(1);
					}
					*z = '\0'; z++;
					new_labs++;
					fprintf(fp, "byte wait_var_%d\n", new_labs);
					fprintf(fp, "L_wait_%d:\n", new_labs);
					fprintf(fp, "\tc_code { Pp_%s->wait_var_%d = spin_cond_wait(%s, %s); }\n",
						fct_name, new_labs, OutBuf, z);
					fprintf(fp, "\tif\n");
					fprintf(fp, "\t:: c_expr { (Pp_%s->wait_var_%d == 0) }\n", fct_name, new_labs);
					fprintf(fp, "\t   /* reaquire the lock and try again */\n");
					fprintf(fp, "\t   atomic { c_expr { spin_mutex_free(%s) }\n", z);
					fprintf(fp, "\t		c_code { spin_mutex_lock(%s); } }\n", z);
					fprintf(fp, "\t		goto L_wait_%d\n", new_labs);
					fprintf(fp, "\t:: else /* good to go */\n");
					fprintf(fp, "\tfi\n");

					strcpy(OutBuf, "");
				} else if (strncmp(OutBuf, "F: pthread_mutex_unlock(", 24) == 0)
				{	strcpy(OutBuf, "F: spin_mutex_unlock(");
				} else if (strncmp(OutBuf, "F: pthread_mutex_destroy(", 25) == 0)
				{	strcpy(OutBuf, "F: spin_mutex_destroy(");
				} else if (strncmp(OutBuf, "F: pthread_cond_signal(", 23) == 0)
				{	strcpy(OutBuf, "F: spin_cond_signal(");
				} else if (strncmp(OutBuf, "F: pthread_mutex_init(", 22) == 0)
				{	strcpy(OutBuf, "F: spin_mutex_init(");
				} else if (strncmp(OutBuf, "F: pthread_cond_init(", 21) == 0)
				{	strcpy(OutBuf, "F: spin_mutex_init(");
				} else if (strstr(OutBuf, "pthread_self("))
				{	char *xx = strstr(OutBuf, "pthread_self(");
					if (xx)
					{	special_case = 2;
						strcpy(xx, "((int)(((P0 *)this)->_pid))");
					}
				} else
				{
					if (strstr(OutBuf, "spin_free("))
					{	strcat(OutBuf, "(char *) ");
					}
#if 0
					else if (strstr(OutBuf, "spin_malloc("))
					{	strcat(OutBuf, "(int) ");
					}
#endif
#ifdef SV_COMP
					char *xx;
					xx = strstr(OutBuf, "__VERIFIER_nondet_int(");
					if (xx)
					{	strcpy(xx, " pan_rand(");
						goto nomore;
					}
					xx = strstr(OutBuf, "__VERIFIER_nondet_uint(");
					if (xx)
					{	strcpy(xx, " pan_rand(");
						goto nomore;
					}
					xx = strstr(OutBuf, "__VERIFIER_nondet_long(");
					if (xx)
					{	strcpy(xx, " pan_rand(");
						goto nomore;
					}
					xx = strstr(OutBuf, "__VERIFIER_nondet_ulong(");
					if (xx)
					{	strcpy(xx, " pan_rand(");
						goto nomore;
					}
					xx = strstr(OutBuf, "__VERIFIER_nondet_char(");
					if (xx)
					{	strcpy(xx, " pan_rand()%256 + (0");
						goto nomore;
					}
					xx = strstr(OutBuf, "__VERIFIER_nondet_bool(");
					if (xx)
					{	strcpy(xx, " pan_rand()%2 + (0");
						goto nomore;
					}
nomore:					/* done */;
#endif
				}
				in_pars++;
				if (special_case != 3)
				{	modex_recur(root->rnode);
				} else
				{	special_case = 2;
				}
				if (special_case == 1)	// pthread_mutex_lock
				{	special_case = 0;
					strcat(OutBuf, ") }; c_code { spin_mutex_lock(");
					modex_recur(root->rnode);
					strcat(OutBuf, "); };");
				} else if (special_case == 2)
				{	special_case = 0;
				} else if (strstr(OutBuf, "spin_join"))
				{	set_join_id();
					if (0)
					{	fprintf(stderr, "Join '%s' (OutBuf '%s') -> '%s'\n",
							join_id, OutBuf, look_map(join_id));
					}
					fprintf(fp, "\tret_p_%s?eval(_pid);\n", look_map(join_id));
					fprintf(fp, "\tc_code { now.lck_p_%s_ret = 0; };\n",
						look_map(join_id));
					OutBuf[0] = '\0';
				} else if (strstr(OutBuf, "pthread_exit"))
				{	fprintf(fp, "\tgoto Return;\n");
					OutBuf[0] = '\0';
				} else
				{	vis_print(")");
				}

				if (strstr(OutBuf, "F: pthread_create("))
				{	handle_pthread_create(0); // standalone call
				} else if (strstr(OutBuf, "pthread_create("))
				{	handle_pthread_create(0); // in assignment, losing assigned value
				} else if (strncmp(OutBuf, "C: ", 3) == 0
				       &&  strstr(OutBuf, "pthread_create"))
				{	// left-over embedded in condition C:
					strip_pthread_fct("pthread_create(");
				} else if (strncmp(OutBuf, "C: ", 3) == 0
				       &&  strstr(OutBuf, "pthread_mutex_init"))
				{	// left-over embedded in condition C:
					strip_pthread_fct("pthread_mutex_init(");
				} else if (strncmp(OutBuf, "C: ", 3) == 0
				       &&  strstr(OutBuf, "pthread_mutex_lock"))
				{	// left-over embedded in condition C:
					strip_pthread_fct("pthread_mutex_lock(");
				} else if (strncmp(OutBuf, "C: ", 3) == 0
				       &&  strstr(OutBuf, "pthread_mutex_unlock"))
				{	// left-over embedded in condition C:
					strip_pthread_fct("pthread_mutex_unlock(");
				} else if (strstr(OutBuf, "pthread_join"))
				{	replace_pthread_join();
				}

				if (vis && !suppress)
				{	char my_fname[512];
					strcpy(my_fname, "");
					bugger(my_fname, root->lnode, 0);
					if ((extended
					&&   allprocs
					&&   is_fctnm(my_fname))
					|| is_icall(my_fname))
					{	handle_instrumented(root, my_fname);
				}	}
				in_pars--;
			}
			break;
		case TN_ASSIGN:
			modex_recur(root->lnode);
			vis_print(toksym(root->hdr.tok,1));
			modex_recur(root->rnode);
			break;
		case TN_DECL:
			decl_cnt++;
			modex_recur(root->lnode);
			modex_recur(root->rnode);
			if (--decl_cnt == 0 && in_args == 0)
				vis_print("; ");
			break;
		case TN_EXPR:
			switch (root->hdr.tok) {
			case CASE:
				vis_print(toksym(root->hdr.tok,1));
				modex_recur(root->lnode);
				modex_recur(root->rnode);
				break;
			case SIZEOF:
				vis_print(toksym(root->hdr.tok,0));
				vis_print("(");
				modex_recur(root->lnode);
				modex_recur(root->rnode);
				vis_print(")");
				break;
			case INCR:
			case DECR:
				modex_recur(root->lnode);
				vis_print(toksym(root->hdr.tok,1));
				modex_recur(root->rnode);
				break;
			case B_OR:
tryonce:			if (preview)
				{	int x = precomputable(root);
					if (x)
					{	char buf[256];
						sprintf(buf, "%d", x);
						vis_print(buf);
						break;
				}	}
				goto same;
			case B_AND:
				if (!root->lnode)
				{	vis_print("(");	// 10/27/17 produces ptr
					vis_print(toksym(root->hdr.tok,1));
					vis_print("(");
					modex_recur(root->rnode);
					vis_print(")");
					vis_print(")");	// 10/27/17
					break;
				}
				goto tryonce;
			default:
same:				vis_print("(");
				if (root->lnode
				&&  root->lnode->hdr.type == TN_ASSIGN)
				{	vis_print("(");
					modex_recur(root->lnode);
					vis_print(")");
				} else
					modex_recur(root->lnode);

				vis_print(toksym(root->hdr.tok,1));

				if (root->rnode
				&&  root->rnode->hdr.type == TN_ASSIGN)
				{	vis_print("(");
					modex_recur(root->rnode);
					vis_print(")");
				} else
					modex_recur(root->rnode);

				vis_print(")");
				break;
			}
			break;
		case TN_SELECT:
			if (debug && vis) printf(" <<tns-l>> ");
			modex_recur(root->lnode);
			if (debug && vis) printf(" <<tns-r>> ");
			if (root->hdr.tok == ARROW)
			{	vis_print("->");
				precondition(root->lnode);	/* (x->) */
			} else
			{	vis_print(".");
			}
			modex_recur(root->rnode);
			if (debug && vis) printf(" <<tns>> ");
			break;
		case TN_INDEX:
			array_bound(root->lnode, root->rnode);
			modex_recur(root->lnode);
			vis_print("[");
			modex_recur(root->rnode);
			vis_print("]");
			break;
		case TN_DEREF:
			precondition(root->rnode);	/* (*x) */
			vis_print("(*");
			modex_recur(root->lnode);	/* always null */
			if (root->rnode
			&& (root->rnode->hdr.type == TN_IDENT))
				modex_recur(root->rnode);
			else
			{	vis_print("(");
				modex_recur(root->rnode);
				vis_print(")");
			}
			vis_print(")");
			break;
		case TN_FUNC_DECL:
			if (0) fprintf(stderr, "funct declaration\n");
			break;
		case TN_ARRAY_DECL:
			modex_recur(root->lnode);
			vis_print("[");
			modex_recur(root->rnode);
			vis_print("]");
			break;
		case TN_EXPR_LIST:
			modex_recur(root->lnode);
			if (root->rnode)
				vis_print(",");
			modex_recur(root->rnode);
			break;
		case TN_ENUM_LIST:
			enum_list_cnt++;
			modex_recur(root->lnode);
			if (root->rnode)
				vis_print(", ");
			modex_recur(root->rnode);
			if (--enum_list_cnt == 0)
				vis_print("\n");
			break;
		case TN_PARAM_LIST:
			modex_recur(root->lnode);
			if (root->rnode)
			{	vis_print(",");
				modex_recur(root->rnode);
			}
			break;
		case TN_DECL_LIST:
			modex_recur(root->lnode);
			if ((root->rnode
			&& (root->rnode->hdr.type == TN_IDENT))
			|| (root->rnode
			&&  root->rnode->lnode
			&& ((root->rnode->lnode->hdr.type == TN_IDENT)
			|| (root->rnode->lnode->hdr.type == TN_PNTR))) )
				vis_print(",");
			modex_recur(root->rnode);
			break;
		case TN_DECLS:
			modex_recur(root->lnode);
			if ((root->rnode && (root->rnode->hdr.type == TN_IDENT))
			|| (root->rnode->lnode
			&& ((root->rnode->lnode->hdr.type == TN_IDENT)
			|| (root->rnode->lnode->hdr.type == TN_PNTR))) )
				vis_print(",");
			modex_recur(root->rnode);
			break;
		case TN_STEMNT_LIST:
			modex_recur(root->lnode);
			if (root->lnode
			&& (!just_left_blk)
			&& (root->lnode->hdr.type != TN_STEMNT_LIST))
			{	vis_print(";\n");
			}
			if (root->rnode != NULL)
			{	modex_recur(root->rnode);
				if (!just_left_blk)
				{	vis_print(";\n");
				}
			}
			break;
		case TN_STEMNT:
			modex_recur(root->lnode);
			modex_recur(root->rnode);
			break;
		case TN_COMP_DECL:
			modex_recur(root->lnode);
			modex_recur(root->rnode);
			vis_print(";\n");
			break;
		case TN_BIT_FIELD:
			modex_recur(root->lnode);
			vis_print(":");
			modex_recur(root->rnode);
			break;
		case TN_PNTR:
			vis_print("*");
			modex_recur(root->lnode);
			modex_recur(root->rnode);
			break;
		case TN_INIT_LIST:
			modex_recur(root->lnode);
			vis_print(",");
			modex_recur(root->rnode);
			break;
		case TN_OBJ_DEF:
			leaf = (leafnode *) root;
			vis_print(toksym(leaf->hdr.tok,1));
			modex_recur(root->lnode);
			vis_print(" {\n");
			modex_recur(root->rnode);
			vis_print("}");
			break;
		case TN_OBJ_REF:
			leaf = (leafnode *) root;
			vis_print(toksym(leaf->hdr.tok,1));
			modex_recur(root->lnode);
			vis_print(" ");
			modex_recur(root->rnode);
			break;
		case TN_CAST:
			decl_cnt++;
		//	vis_print("(");	// 10/17
				vis_print("(");
				modex_recur(root->lnode);
				vis_print(")");
				decl_cnt--;
				modex_recur(root->rnode);
		//	vis_print(")");
			break;
		case TN_JUMP:
			vis_print(toksym(root->hdr.tok,1));
			if ((root->hdr.tok == RETURN)
			||  (root->hdr.tok == GOTO))
			{	is_label++;
				modex_recur(root->lnode);
				is_label--;
			}
			break;
		case TN_LABEL:
			is_label++;
			modex_recur(root->lnode);
			if (root->lnode
			&& (root->lnode->hdr.type != TN_LABEL))
				vis_print(":\n");
			is_label--;
			modex_recur(root->rnode);
			break;

		case TN_INIT_BLK:
			modex_recur(root->lnode);
			vis_print(", ");
	    		modex_recur(root->rnode);
			break;

		case TN_WHILE:
		case TN_DOWHILE:
			if (!vis) break;
			if (!preview)
				printf("%s: unexpected - call from outside\n", progname);
			modex_recur(root->lnode);
			break;

		default:
			if (vis && !preview)
			fprintf(stderr, "%s: recur: line %3d unexpected node %s\n",
				progname, root->hdr.line, name_of_node(root->hdr.type));
			break;
		}
		break;

	case IF_T:
		modex_if((if_node *) root, 0);
		break;
	default:
		if (!preview)
			fprintf(stderr, "recur: unhandled type %s\n",
			name_of_nodetype(root->hdr.which));
		break;
	}
	if (debug && vis) printf(" <<UP>> ");
}

void
x_frag(treenode *root, FILE *fd)
{	FILE *ofp = fp;

	if (!root
	||  root->hdr.type == TN_FUNC_DEF
	||  root->hdr.type == TN_FOR)	/* was FOR_T */
		return;

	fp = fd;
	ByPass = 1;	/* bypass the lookup table */
	decl_cnt = 1;

	vis_start();
	modex_recur(root);

	if (root->hdr.line >= 0
	&&  strlen(OutBuf) > 0
	&&  (strstr(OutBuf, "enum ") || strstr(OutBuf, "struct ")))	/* reason? */
	{	cleanse(OutBuf);
		/* fprintf(stderr, "x_frag OutBuf=<%s> want=<%s>\n", OutBuf, want); */
		if (imported(OutBuf, want, 1))
		{	if (du_mode)	/* -defuse */
			{	char *yy, *y = OutBuf;
				while (*y == '*' || *y == ' ' || *y == '\t')
				{	y++;
				}
				if ((yy = strstr(y, "[]")) != NULL)
				{	*yy = '\0';
				}
				fprintf(fp, "int %s; /* Local to %s from symtab */\n",
					y, want);
			} else
			{	if (!strchr(OutBuf, '='))	// should prevent this
				fprintf(fp, "c_state \"%s\" \"Local %s\"\t/* from symtab */\n",
					OutBuf, want);
	}	}	}

	root->hdr.line = -root->hdr.line - 1;	/* mark visited */
	decl_cnt = 0;
	ByPass = 0;
	fp = ofp;
}

void
modex_leaf(leafnode *leaf, int tabs)
{
	if (leaf == NULL || !vis) return;

	/* normally not called */
	linenr = leaf->hdr.line;
	vis_indent(tabs, "");

	switch(leaf->hdr.type){
	case TN_IDENT:	/* modex_leaf */
		vis_print(nmestr(leaf->data.sval));
		break;
	case TN_TYPE:
		if (Verbose&2)
		{	vis_print("Type ");
			vis_print(toksym(leaf->hdr.tok,0));
			if (leaf->hdr.tok == TYPEDEF_NAME)
			{	vis_print(" ");
				vis_print(nmestr(leaf->data.sval));
		}	}
		break;
	case TN_INT:
		vis_print("Int ");
		vis_print_d(leaf->data.ival);
		vis_print("\n");
		break;
	case TN_REAL:
		vis_print("Real ");
		vis_print_g(leaf->data.dval);
		vis_print("\n");
		break;
	case TN_STRING:
		if (0)
		fprintf(stderr, "STRING (%s) at line %3d\n",
			leaf->data.str, leaf->hdr.line);
		vis_print("\"");
		fputs_metastr(leaf->data.str);
		vis_print("\"");
		break;
	case TN_ELLIPSIS:
		vis_print("Ellipsis\n");
		break;
	case TN_LABEL:
		vis_print("Label\n");
		break;
	default:
		fprintf(stderr, "%s: error: unknown leaf type %d\n", progname, leaf->hdr.type);
		break;
	}
}

static char *
map_neg(treenode *n, char *oO)
{	char *p;

	vis_start();
	vis_print("C: !");
	vis_print(oO);

	owf = wasfalse;
	owt = wastrue;
	owe = waselse;
	owh = ishidden;
	if (!strstr(oO, ND_CHOICE))
		PosElse = 1;
	p = vis_lookup(n);		/* map */
	PosElse = 0;
	return p;
}

static int
handle_cond(treenode *n, treenode *m, treenode *incr, char *oO, int tabs, char *prefix)
{	static char oA[1024];
#if 0
	filter out frequently occurring cases:
		if :: false :: true fi	->	done
		if :: false :: false fi	->	done
		if :: true :: false fi	->	done
		if :: true :: true  fi	->	not handled
#endif
	vis_start();	/* clean start */

	if (!n)
	{	/* e.g., a missing cond in a for (;;), treated as deterministic 'true' */
		strcpy(oO, "");		/* in handle_neg treated as 'false' */
					/* in handle_shortcut ditto */
		if (strncmp(prefix, "do", strlen("do")) == 0)
		{	vis_indent(tabs, prefix);
			vis_indent(tabs, ":: ");
			modex_any(m, tabs+2);	/* action part */
			modex_any(incr,tabs+2);	/* loop increment */
			return 1;
		}
just_act:
		modex_any(m, tabs+2);	/* action part */
		return 0;
	}
	vis_print("C: ");

	if (strncmp(prefix, "do", strlen("do")) == 0)
	{	is_do_condition = 1;
	}
	modex_recur(n);				/* condition part */
	is_do_condition = 0;

	if (strncmp(OutBuf, "C: ", strlen("C: ")) != 0)
		goto just_act;

	strcpy(oO, &OutBuf[strlen("C: ")]);	/* save */
	vis_lookup(n);				/* map  */

	if (wasfalse)
	{	/* if :: false ... :: ? ...  fi */
		char *p;
		p = map_neg(n, oO);	/* check negation */
		if (wasfalse)	/* if :: false :: false fi */
			vis_indent(tabs, "false; /* dead stop */ ");
		wasfalse = owf;
		wastrue = owt;
		waselse = owe;
		ishidden = owh;

		if (strcmp(p, "else") != 0)	/* unless the other option maps to else */
			vis_flush(n);
		else
			vis_indent(tabs, "skip; ");

		vis_start();
		zap_prec();
		return 0;
	}

	if (wastrue)
	{	strcpy(oA, OutBuf);	/* save state */
		map_neg(n, oO);		/* check negation */
		wastrue = owt;
		ishidden = owh;
		if (wasfalse || waselse) /* no need to print guard or if boilerplate */
		{	/* if :: true ... :: false ...  fi */
			wasfalse = owf;
			waselse = owe;
			vis_start();
			zap_prec();
			if (strncmp(prefix, "do", strlen("do")) == 0)
			{	vis_indent(tabs, prefix);
				vis_indent(tabs, ":: ");
				modex_any(m, tabs+2);	/* action part */
				modex_any(incr,tabs+2);	/* loop increment */
				return 2;
			}
			modex_any(m, tabs+2);	/* action part */
			return 0;	/* neg is false - should be treated as skip */
		}
		wasfalse = owf;
		waselse  = owe;
		strcpy(OutBuf, oA);		/* restore state */
	}

	check_fct(oO, tabs);

	vis_indent(tabs, prefix);	/* the normal case */
	vis_indent(tabs, ":: ");
	vis_flush(n);			/* prints the guard */
	vis_direct("\n");
	vis_start();
	zap_prec();
	modex_any(m, tabs+2);	/* action part */

	/* to cover the case where an instrumented function call
	   was moved in front of the loop: we jump back to the
	   label just before that -- this is correct also if there
	   was no such call
	 */
	if (strncmp(prefix, "do", strlen("do")) == 0)
	{	vis_direct("	/* Jump Back */\n");
		use_dostack(2);
		vis_direct("	/* End Jump */\n");
	}
	modex_any(incr,tabs+2);	/* loop increment */
	return 1;
}

static void
handle_shortcut(treenode *n, char *oO, treenode *m, int tabs)
{	/* the positive if cond mapped to false */

	vis_start();
	if (strlen(oO) == 0)
		return;	/* don't print anything */

	map_neg(n, oO);
	if (wastrue || waselse)	/* no need for guard */
	{	vis_start();
		modex_any(m, tabs);
	} else if (wasfalse)
	{	vis_start(); /* null if/do */
	} else
	{	vis_indent(tabs, "");
		vis_flush(m);	/* print guard */
		vis_direct("\n");
		modex_any(m, tabs);
	}
}

static void
handle_neg(treenode *n, char *oO, char *suff, treenode *m, int tabs, char *closing)
{	static char oA[1024];

	if (strlen(oO) == 0)
	{	wasfalse = 1;
		goto more;
	}
	map_neg(n, oO);
	vis_direct("\n");

	if (wastrue)
	{	strcpy(oA, OutBuf);	/* save */
		vis_start();
		vis_print("C: ");
		vis_print(oO);
		owf = wasfalse;
		owe = waselse;
		owt = wastrue;
		owh = ishidden;
		vis_lookup(ZN);	/* peek back */
		if (wasfalse)	/* no need to print guard */
		{	vis_start();
			vis_indent(tabs, ":: /* true */ ");
			vis_direct(suff);
			goto more;
		}
		/* else restore */
		strcpy(OutBuf, oA);
		wasfalse = owf;
		waselse  = owe;
		wastrue  = owt;
		ishidden = owh;
	}
	if (!wasfalse)
	{	vis_indent(tabs, ":: ");
		vis_flush(n);
		vis_direct(suff);
	}
more:
	vis_start();
	if (m && !wasfalse)
		modex_any(m, tabs+1);	/* an else leg */

	vis_indent(tabs, closing);
}

void
doreturn(int fromwhere)
{	char sbuf[512];

	if (!vis) return;

	do_locals(1);	/* write local decls of last procedure */

	vis_direct("\n");

	nreturns++;
	if ((sawreturn && needreturn) || extended)
	{	vis_direct("Return");
		if (nreturns > 1)
		{	sprintf(sbuf, "%d", nreturns);
			vis_direct(sbuf);
		}
		vis_direct(":	skip;\n");
		if (!extended
		|| strcmp(fct_name, "main") == 0
		|| strcmp(fct_name, "modex_main") == 0)
			vis_direct("#if 0\n");
		sprintf(sbuf, "\tret_p_%s!lck_id;\n", fct_name);
		vis_direct(sbuf);
		
		if (!dynamic)
		{	vis_direct("\tgoto endRestart\n");
		}
		if (flike
#ifdef SV_COMP
		||  strstr(fct_name, "_atomic_")
#endif
		   )
		{	vis_direct(" } /* function like */\n");
		}
		if (!extended
		|| strcmp(fct_name, "main") == 0
		|| strcmp(fct_name, "modex_main") == 0)
			vis_direct("#endif\n");
	}
	if (fp)
	{	fprintf(fp, "\n/* function-calls:");
		show_fbase(fp);
		fprintf(fp, "*/\n");
	}

	if (strcmp(wanttype, "body") != 0)
		vis_direct("}\n");
	else
		vis_direct(";\n");

	if (0) { 
		sprintf(sbuf, "/* from %d */\n", fromwhere);
		vis_direct(sbuf);
	}

	strcpy(fct_name, "--");
	vis_start();
}

static void
handle_fct(treenode *node, int tabs)
{
	if (!node->lnode)
		return;

	if (allprocs)
	{	vis = 1;			// no output before first procedure
		if (strchr(wanttype, '[')	// more than one instantiation
		&&  extended
		&&  (strcmp(nmestr(((leafnode *)(node->lnode))->data.sval), "main") == 0
#ifdef SV_COMP
		 ||  strstr(nmestr(((leafnode *)(node->lnode))->data.sval), "__VERIFIER_atomic_") != NULL
#endif
		 ||  strcmp(nmestr(((leafnode *)(node->lnode))->data.sval), "modex_main") == 0)
		&&  strstr(wanttype, "active")	// active proctypes
		&&  strstr(wanttype, "proctype"))
		{	sprintf(tbuf, "\n\nactive proctype p_%s(",
				nmestr(((leafnode *)(node->lnode))->data.sval));
			vis_direct(tbuf);
		} else
		{	char *a = tbuf;
			sprintf(tbuf, "\n\n%s p_%s(", wanttype,
				nmestr(((leafnode *)(node->lnode))->data.sval));

			if (dynamic
			&&  !strstr(tbuf, "p_main(")
			&&  !strstr(tbuf, "p_modex_main(") )
			{	a = strstr(tbuf, "active ");
				if (a != NULL)
				{	a += strlen("active ");
				} else
				{	a = tbuf;
			}	}
			vis_direct(a);
		}

		nreturns = 0;
	} else
	{	vis_print("FctDecl:\n");	/* vis is 0 here */

		if (node->lnode->hdr.which == LEAF_T
		&&  node->lnode->hdr.type == TN_IDENT	/* fct-name */
		&& !strcmp(want, nmestr(((leafnode *)(node->lnode))->data.sval))
		&&  strlen(want) == strlen(nmestr(((leafnode *)(node->lnode))->data.sval)))
		{	vis = 1;
			taboffset = tabs-1;
			strcpy(fct_name, nmestr(((leafnode *)(node->lnode))->data.sval));
			if (strcmp(wanttype, "body") != 0)
			{	sprintf(tbuf, "\n\n%s p_%s(", wanttype, want);
				vis_direct(tbuf);
			}
			nreturns = 0;
		} else
		{	doreturn(2);	/* needed? */
			taboffset = 0;
			if (!allprocs) vis = 0;
		}
	}
	strcpy(fct_name, nmestr(((leafnode *)(node->lnode))->data.sval));
	strcpy(derproc, fct_name);
	if (vis && show_funcs)
		set_fbase(node->hdr.line, fct_name);
}

static int Cunique = 0;

static void
modex_node(treenode *node, int tabs)
{	int ovis = vis, osaw, xtmp;
	char jumploc[32];

	if (!node)
	{	if (0) { printf("no node\n"); fflush(stdout); }
		return;
	}

	if (0)
	{	printf("%3d: modex_node %s (%p) tabs %d\n", node->hdr.line,
		name_of_node(node->hdr.type), node, tabs);
		fflush(stdout);
	}

	switch (node->hdr.type) {
	case TN_DECL_LIST:
	case TN_STEMNT_LIST:
	case TN_STEMNT:
	case TN_BLOCK:
	case TN_EXPR:
		break;
	default:	/* everything else is indented */
		linenr = node->hdr.line;
		vis_indent(tabs, "");
		break;
	}

	switch(node->hdr.type){
	case TN_ASSIGN:
		vis_start();
		vis_print("A: ");
same:		pending++;
//		fprintf(stderr, "B4 <%s>\n", OutBuf);
		modex_recur(node);	/* 1 - stmnt/decl/expr txt */
//		fprintf(stderr, "A4 <%s>\n", OutBuf);
		pending--;
		if (pending==0)
		{	/* intercept typenames without varnames */
			/* as in "main(void)" */
			if (node->hdr.type != TN_DECL
			||  !strstr(OutBuf, " ;"))
			{
				vis_flush(node);
			}
			vis_start();
			if (!in_args)
			{	vis_direct("\n");
		}	}
		return;

	case TN_FUNC_CALL:
		vis_print("F: ");
		goto same;

	case TN_STEMNT:
		if (node->hdr.which == LEAF_T)
		{	vis_start();
			goto same;
		}
		break;

	case TN_DECL:
		vis_start();
		vis_print("D: ");
		goto same;

	case TN_ARRAY_DECL:
		vis_start();
		vis_print("AD: ");
		goto same;

	case TN_EXPR:
		goto same;

	case TN_COND_EXPR:
		vis_start();
		vis_print("CE: ");
		goto same;

	case TN_FUNC_DECL:
		handle_fct(node, tabs);
		in_args++;
		modex_any(node->rnode, 0);	/* formal parameters */
		in_args--;
		return;

	case TN_WHILE:
		vis_indent(tabs, "/* while */\n");
		push_dostack(ZN);

	{	char oO[1024];

		xtmp = handle_cond(node->lnode, node->rnode, ZN, oO, tabs, "do\n");
		switch (xtmp) {
		case 2:
			vis_indent(tabs, "od;\n");
			break;
		case 1:
			if (node->lnode)
			{	handle_neg(node->lnode, oO, " -> break\n", ZN, tabs, "od;\n");
			} else
			{	vis_indent(tabs, "od;\n");
			}
			break;
		case 0:
			vis_direct("\t\t");
			vis_flush(node);
			vis_direct("/* XX? */\n");
			vis_start();
			break;
		}
	}
		pop_dostack();
		return;

	case TN_DOWHILE:
		vis_direct("\n");
		vis_flush(node);
		vis_start();
		push_dostack(ZN);
		vis_indent(tabs, "do	/* do-while */\n");
		vis_indent(tabs, ":: ");
		modex_any(node->rnode, tabs);	/* body */

	{	char oO[1024];

		if (node->lnode)
		{	xtmp = handle_cond(node->lnode, ZN, ZN, oO, tabs+2, "if\n");
			switch (xtmp) {
			case 2:
				vis_indent(tabs, "\n\tfi;\n");
				break;
			case 1:
				handle_neg(node->lnode, oO, "break\n", ZN, tabs+2, "\n\tfi\n");
				break;
			case 0:
				vis_direct("\t\t");
				vis_flush(node->lnode);
				vis_direct("break\n");
				vis_start();
				break;
	}	}	}

		vis_indent(tabs, "od;\n");
		vis_flush(node);
		vis_start();
		pop_dostack();
		return;

	case TN_JUMP:
		vis_start();
		switch (node->hdr.tok) {
		case CONT:
			use_dostack(tabs);
			goto moveon;
		case RETURN:
			vis_print("R: return "); /* goto Return */
			if (extended)
				check_type++;
			modex_recur(node->lnode);
			if (extended)
				check_type--;
			needreturn++;
			vis_flush(node);
			vis_start();
			goto moveon;
		case BREAK:
			vis_indent(tabs, "break;\n");
			goto moveon;
		case GOTO:
			vis_indent(tabs, "goto ");
			break;
		default:
			vis_print("J: ");
			vis_flush(node);
			vis_start();
			break;
		}
		modex_recur(node->lnode);	/* 3 - gotolabel */
		sprintf(tbuf, "%s;\n", OutBuf);
		vis_direct(tbuf);
moveon:		modex_any(node->rnode,tabs);
		return;

	case TN_SWITCH:
		vis_start();
		vis_direct("\n");

		modex_recur(node->lnode);	/* 2 - switch expr*/

		check_fct(OutBuf, tabs);

		vis_indent(tabs,"do /* switch */");

		osaw = sawdefault;
		push_swstack(OutBuf);		/* remember expr */
		modex_any(node->rnode, tabs);	/* handle the cases */

		/* fall out of switch - if break is missing */
		if (sw_first > 0)
		{	sprintf(jumploc, "goto C_%d /* fall out */\n",
				Cunique);
			vis_indent(tabs+1,jumploc);
		} else
			strcpy(jumploc, "");

		pop_swstack();
		if (!sawdefault)
		{	static int newnr = 0;
			char makeup[64];

			if (fallout)
			{	sprintf(makeup, ":: %s assert(%d == 0); break\n",
					do_difficult("else ->", 0), ++newnr);
			} else
			{	/* handle semantics of alt(x) in plan9 code */
				if (strncmp(SwLabel[sw_level], "alt(", strlen("alt(")) == 0)
					strcpy(makeup, "/* else suppressed for alt */\n");
				else
					sprintf(makeup, ":: %s break\n",
						do_difficult("else ->", 0));	
			}
			vis_indent(tabs, makeup);
		}
		sawdefault = osaw;

		vis_start();
		vis_indent(tabs,"od;\n");

		/* fall out of switch destination */
		if (strlen(jumploc) != 0)
		{	sprintf(tbuf, "C_%d:	skip;", Cunique++);
			vis_direct(tbuf);
		}

		return;

	case TN_LABEL:
		vis_start();
		vis_direct("\n");
		is_label++;
		modex_recur(node->lnode);	/* 4 - generate caselabel */
		is_label--;
		if (vis)
		{	if (strncmp(OutBuf, "case", strlen("case")) == 0
			||  strncmp(OutBuf, "default", strlen("default")) == 0)
			{	if (sw_first > 0)
				{	sprintf(jumploc, "goto C_%d /* fall thru */\n",
						Cunique);
					vis_indent(tabs+1,jumploc);
				}

				vis_indent(tabs, ":: ");
				/* case integer from lnode is in OutBuf */
				vis_print(" == ");	/* add == */
				use_swstack();	/* add switch expr */
				vis_flush(node->lnode);
				vis_direct("\n");

				if (sw_first > 1)
				{	if (ishidden)
					vis_indent(tabs+2,"skip; /* syntax */\n");
					sprintf(tbuf, "C_%d:", Cunique++);
					vis_direct(tbuf);
				}
				tabs += 2;
			} else
			{	sprintf(tbuf, "%s:\n", OutBuf);
				vis_direct(tbuf);
			}
			vis_start();
		}
		modex_any(node->rnode,tabs);		/* labeled block */
		return;

	case TN_INDEX:
		modex_recur(node->lnode);	/* 5a - array base */
		vis_print("[");
		modex_recur(node->rnode);	/* 5b - array index */
		vis_print("]");
		return;

	case TN_TRANS_LIST:
#if 0
	added in Feb. 2003, but this seems to break
	the examples int the example directory...
	removed in March 2004 -- gjh
		modex_any(node->lnode,tabs);	/* ?? fails to return on iproto.c */
		modex_any(node->rnode,tabs);
		break;
#endif
	case TN_DEREF:
	case TN_SELECT:
	case TN_FUNC_DEF:
	case TN_DECLS:
	case TN_EXPR_LIST:
	case TN_NAME_LIST:
	case TN_FIELD_LIST:
	case TN_IDENT_LIST:
	case TN_COMP_DECL:
	case TN_BIT_FIELD:
	case TN_PNTR:
	case TN_TYPE_LIST:
	case TN_TYPE_NME:
	case TN_INIT_LIST:
	case TN_INIT_BLK:
	case TN_OBJ_DEF:
	case TN_OBJ_REF:
	case TN_CAST:
	case TN_IF:
	case TN_FOR:
	case TN_ELLIPSIS:
	case TN_ENUM_LIST:
	case TN_PARAM_LIST:
	case TN_EMPTY:
		break;

	case TN_DECL_LIST:
	case TN_BLOCK:
	case TN_STEMNT_LIST:
		modex_any(node->lnode,tabs);
		modex_any(node->rnode,tabs);
		return;

	default:
		fprintf(stderr, "%s: unexpected node %s\n",
			progname, name_of_node(node->hdr.type));
		exit(1);
	}

	if (node->lnode)
	{	if (!ovis) doreturn(4);
		vis = ovis;
	}

	modex_any(node->lnode, tabs);

	if (node->rnode)
	{	if (!ovis) doreturn(5);
		vis = ovis;
	}
	modex_any(node->rnode, tabs);
}

static char *
has_instrumented(treenode *root, char *s)
{	char *efn;

	if (!root) return NULL;

	// printf("%s\t%s\n", s, name_of_node(root->hdr.type));
	if (root->hdr.type == TN_EXPR
	||  root->hdr.type == TN_ASSIGN)
	{	efn = has_instrumented(root->lnode, "L ");
		if ((efn = has_instrumented(root->lnode, "L ")) != NULL)
		{	return efn;
		}
		if ((efn = has_instrumented(root->rnode, "R ")) != NULL)
		{	return efn;
	}	}
	if (root->hdr.type == TN_FUNC_CALL)
	{	char *lft, *rgt;
		// XXX check func call for pthread_creat
		lft = has_instrumented(root->lnode, "L ");
		rgt = has_instrumented(root->rnode, "R ");
		if (lft) // fct is pthread_create, pthread_join, or pthread_mutex_init
		{	// capture the call + args here, from rnode...
			keep_root = &root;
			keep_pars = root->rnode;
			if (0)
			{	fprintf(stderr, "Set keep_root to %p -> %p (%s)\n",
					keep_root, root, lft);
			}
			return lft;
		}
		return rgt;
	} else  if (root->hdr.type == TN_IDENT)
	{
		if (strcmp(((leafnode *)root)->data.sval->str, "pthread_create") == 0)
		{	// fprintf(stderr, "XXX\t\t%s\n", ((leafnode *)root)->data.sval->str);
			return "pthread_create";
		}
		if (strcmp(((leafnode *)root)->data.sval->str, "pthread_join") == 0)
		{	// fprintf(stderr, "XXX\t\t%s\n", ((leafnode *)root)->data.sval->str);
			return "pthread_join";
		}
		if (strcmp(((leafnode *)root)->data.sval->str, "pthread_mutex_init") == 0)
		{	// fprintf(stderr, "XXX\t\t%s\n", ((leafnode *)root)->data.sval->str);
			return "pthread_mutex_init";
		}
		if (strcmp(((leafnode *)root)->data.sval->str, "pthread_mutex_lock") == 0)
		{	// fprintf(stderr, "XXX\t\t%s\n", ((leafnode *)root)->data.sval->str);
			return "pthread_mutex_lock";
		}
		if (strcmp(((leafnode *)root)->data.sval->str, "pthread_mutex_unlock") == 0)
		{	// fprintf(stderr, "XXX\t\t%s\n", ((leafnode *)root)->data.sval->str);
			return "pthread_mutex_unlock";
		}
	}
	return NULL;
}

static void
modex_if(if_node *ifn, int tabs)
{	char oO[1024];
	int xtmp;
	char *efn = NULL;

	if (vis != 0 && ((efn = has_instrumented(ifn->cond, "")) != NULL))
	{	char MBuf[BigEnough];

		// move instrumented function call out of conditional test

		strcpy(MBuf, OutBuf);	// remember

		sprintf(OutBuf, "F: %s(", efn);
		modex_recur(keep_pars);
		strcat(OutBuf, ")");

		if (strcmp(efn, "pthread_create") == 0)
		{	handle_pthread_create(1);
		} else if (strcmp(efn, "pthread_mutex_init") == 0)
		{	char *z;
			z = strchr(OutBuf, '(');
			if (z)
			{	fprintf(fp, "\t\tc_code { spin_mutex_init%s; }\n", z);
			}
		} else if (strcmp(efn, "pthread_mutex_lock") == 0)
		{	char *z;
			z = strchr(OutBuf, '(');
			if (z)
			{	fprintf(fp, "\t\tc_code { spin_mutex_lock%s; }\n", z);
			}
		} else if (strcmp(efn, "pthread_mutex_unlock") == 0)
		{	char *z;
			z = strchr(OutBuf, '(');
			if (z)
			{	fprintf(fp, "\t\tc_code { spin_mutex_unlock%s; }\n", z);
			}
		}

		strcpy(OutBuf, MBuf);	// restore

		keep_root = 0;
		keep_pars = 0;
	}

	if (ifn->hdr.tok == QUESTMARK)		/* cond expr */
	{	vis_print("(");
		modex_recur(ifn->cond);
		if (use_c_code)			/* should be stmnt specific */
			vis_print(" ? ");	/* c-syntax */
		else
			vis_print(" -> ");	/* promela-syntax */
		modex_any(ifn->then_n, 0);
		vis_print(" : ");
		modex_any(ifn->else_n, 0);
		vis_print(")");
	} else
	{	xtmp = handle_cond(ifn->cond, ifn->then_n, ZN, oO, tabs, "if\n");
		switch (xtmp) {
		case 2:
			vis_indent(tabs, "\n\tfi;\n");
			break;
		case 1:
			handle_neg(ifn->cond, oO, "\n", ifn->else_n, tabs, "\n\tfi;\n");
			break;
		case 0:
			handle_shortcut(ifn->cond, oO, ifn->else_n, tabs);
			break;
	}	}
}

extern char *print2buf(treenode *);

static void
modex_for(for_node *forn, int tabs)
{	char oO[1024], *rev;
	int xtmp;

	if (!forn) return;

	if (forn->hdr.type == TN_FUNC_DEF)
	{	if (forn->test)
		{	if (forn->test->hdr.which != NODE_T)
			{	fprintf(stderr, "%s: cannot happen fct decl1\n", progname);
				exit(1);
			}

			rev = print2buf(forn->init);
			if (strlen(rev) >= sizeof(fct_type))
			{	fprintf(stderr, "%s:%d: type '%s' too long\n",
					forn->hdr.fnm, forn->hdr.line, rev);
			} else
			{	strcpy(fct_type, rev);
			}
			*rev = '\0';

			if (forn->test->hdr.type == TN_FUNC_DECL)	/* void fct(...) */
			{
				modex_any(forn->test, 0);
			} else if (forn->test->hdr.type == TN_DECL)	/* float *fct(...) */
			{
				rev = print2buf(forn->test->lnode);
				if (strlen(rev) + strlen(fct_type) >= sizeof(fct_type))
				{	fprintf(stderr, "%s:%d: type '%s %s' too long\n",
						forn->hdr.fnm, forn->hdr.line, fct_type, rev);
				} else
				{	strcat(fct_type, rev);
				}
				*rev = '\0';

				if (forn->test->rnode
				&&  forn->test->rnode->hdr.which == NODE_T
				&&  forn->test->rnode->hdr.type == TN_FUNC_DECL)
				{	modex_any(forn->test->rnode, 0);
				} else
				{	fprintf(stderr, "%s: unexpected fct decl2\n", progname);
					exit(1);
				}
			} else
			{	fprintf(stderr, "%s: cannot happen fct decl3\n", progname);
				exit(1);
			}

			if (strcmp(wanttype, "body") != 0)
			{	did_parameters = 0;
				if (strcmp(wanttype, "proctype") == 0
				||  strcmp(wanttype, "inline") == 0)
				{	do_parameters();
				}
				vis_direct(")\n{");
			}
			vis_flush((treenode *)forn);
		}
		do_locals(0);			/* prepare include file */
		ini_formals();
		modex_any(forn->stemnt,tabs+1);	/* Fct Body: */
	} else	/* FOR */
	{	linenr = forn->hdr.line;
		vis_indent(tabs, "/* for-loop: */\n");
		modex_any(forn->init,tabs);
		push_dostack(forn->incr);

		xtmp = handle_cond(forn->test, forn->stemnt, forn->incr, oO, tabs, "do\n");
		switch (xtmp) {
		case 2:
			vis_indent(tabs, "od;\n");
			break;
		case 1:
			if (forn->test)
				handle_neg(forn->test, oO, " -> break\n", ZN, tabs, "od;\n");
			else
				vis_indent(tabs, "od;\n");
			/* fall thru */
		case 0:
			break;
		}
		pop_dostack();
	}
}

int cnt;

static void
modex_any(treenode *child, int tabs)
{
	if (!child)
	{
if (0) { printf("no child\n"); fflush(stdout); }
		return;
	}

if (0) printf("modex_any %d (%d = %s) %s, %s\n",
		tabs,
		child->hdr.tok, toksym(child->hdr.tok, 0),
		name_of_nodetype(child->hdr.which),
		name_of_node(child->hdr.type));

	switch (child->hdr.which){
	case NODE_T:
if (0) { printf("%d	>%d>%s>\n", cnt++, vis, OutBuf); fflush(stdout); }
		modex_node(child, tabs);
if (0) { printf("%d	<%d<%s<\n", --cnt, vis, OutBuf); fflush(stdout); }
		break;
	case LEAF_T:
		modex_leaf((leafnode *) child, tabs);
		break;
	case IF_T:
		modex_if((if_node *) child, tabs);
		break;
	case FOR_T:
		modex_for((for_node *) child, tabs);
		break;
	default:
		fprintf(stderr, "%s: error: unknown type %d\n",
			progname, child->hdr.which);
		break;
	}
}

void
modex_reset(void)
{
	if (Verbose_cmds)
	{	printf(" -- Modex Reset\n");
	}

	decl_cnt = in_call = in_args = is_label = 0;
	just_left_blk = enum_list_cnt = taboffset = 0;
	sawdefault = Down = 0;
	FreshLut = needreturn = sawreturn = 0;
	ByPass = PosElse = 0;
	extra_comment = owf = owt = owh = 0;
	debug = lastln = lastpb = pending = 0;
	ishidden = wasfalse = wastrue = waselse = nreturns = 0;
	linenr = do_level = sw_level = sw_first = 0;
	do_uniq = o_cnt = vis = 0;
	nblanks = with_decorations = 0;
	cache = comms = commstail = (Cache *) 0;
	fcts = maps = incls = (Fcts *) 0;
	prec = (PreC *) 0;
	decors = fdecors = (Decor *) 0;

	strcpy(fct_name, ":global:");
	strcpy(derscope, "");
	strcpy(dertype,  "");
	strcpy(dername,  "");
	strcpy(derproc,  "");
}

void
alldone(void)
{
	if (fp)
	{
if (debug_io) fprintf(stderr, "close .. %p\n", fp);
		Fclose(fp);
fp = 0;
	}
}

void
modex_tree(treenode *root, char *lut)
{	char t_file[512];

	modex_reset();
	get_lut(o_base, lut);
	get_defaults(lut);

	if (!globals_only
	&&  !show_deps
	&&  !new_lut)
	{	strcpy(t_file, o_base);
		strcat(t_file, ".pml");

		if (strlen(c_file) > 0
		&&  strcmp(c_file, t_file) == 0)	/* e.g. _modex_all.pml */
		{	fprintf(fp, "\n/* extracted from %s */\n\n", cur_in);
		} else
		{	strcpy(c_file, t_file);
			if (fp)
			{
if (debug_io) fprintf(stderr, "close ... %p\n", fp);
				Fclose(fp);
				fp = 0;
			}
	
			if ((fp = fopen(t_file, MFLAGS)) == NULL)
			{	fprintf(stderr, "%s: cannot create '%s'\n", progname, t_file);
				exit(1);
			}
if (debug_io) fprintf(stderr, "open %s -> %p\n", t_file, fp);
			fprintf(fp, "/* %s */\n", VERSION);
			fprintf(fp, "/* extracted from %s */\n\n", cur_in);
			fflush(fp);
			add_fnm(t_file);
		}
	} else
		suppress = 1;

	if (is_icall(want))
	{	extended = 1;
	}

	if (Verbose_cmds)
	printf("want %s, wanttype %s, lut %s\n", want, wanttype, lut);

	modex_any(root, 1);	/* want, wanttype, lut */

	if (new_lut)
	{	dump_lut();
	}

	if (!globals_only
	&&  !show_deps)
	{	if (!new_lut)
		{	doreturn(3);	/* local decls to fp */
		}
		if (redundancies)
		{	check_lut(stdout);
	}	}
}

void
prop_debug(treenode *n, int level, char letter)
{	int i;

	if (!n) return;

	printf("%c: ", letter);

	for (i = 0; i < level; i++)
		printf("  ");

	printf("(%s) %s, %s",
		toksym(n->hdr.tok, 0),
		name_of_nodetype(n->hdr.which),
		name_of_node(n->hdr.type));

	if (n->hdr.type == TN_IDENT)
	{	printf("\t(%s)\n", ((leafnode *)n)->data.sval->str);
		return;
	}
	printf("\n");
	prop_debug(n->lnode, level+1, 'L');
	prop_debug(n->rnode, level+1, 'R');
}

int
cnt_commas(treenode *n)
{
	if (!n) return 0;

	if (n->hdr.type == TN_IDENT)
		return 0;

	return cnt_commas(n->lnode)
	     + cnt_commas(n->rnode)
	     + (n->hdr.tok == COMMA);
}

typedef struct Ax_Props {
	int		t;	/* 0 or 1, assert_r or assert_p */
	int		nr;
	treenode	*n;
	char		*terms[2];
	struct Ax_Props	*nxt;
} Ax_Props;

Ax_Props *all_props;

void
ax_terms(Ax_Props *np, treenode *n)
{
	if (!n) return;

	if (n->hdr.tok == COMMA)
	{	ax_terms(np, n->lnode);
		ax_terms(np, n->rnode);
	} else
	{	int i;
		for (i = 0; i < 2; i++)
			if (!np->terms[i])
			{	strcpy(Rem3, OutBuf);
				strcpy(OutBuf, "");
				modex_recur(n);
				np->terms[i] = (char *) e_malloc(strlen(OutBuf)+1);
				strcpy(np->terms[i], OutBuf);
				strcpy(OutBuf, Rem3);
				return;
			}
		fprintf(stderr, "%s: Error, too many npterms\n", progname);
		exit(1);	/* cannot happen */
	}
}

void
ax_new_assert(const int t, treenode *n)
{	Ax_Props *np;

	if (Verbose&2) prop_debug(n, 0, 'T');

	if (t > 1 || t < 0 || !n || cnt_commas(n) != t)
	{	if (n) fprintf(stderr, "%s: error, %s:%d, assert_%s, ",
			progname, n->hdr.fnm, n->hdr.line, t?"r":"p");
		fprintf(stderr, " (saw %d commas)\n", cnt_commas(n));
		return;
	}

	np = (Ax_Props *) e_malloc(sizeof(Ax_Props));
	np->t = t;
	np->n = n;
	np->nr = ax_prop_nr;
	np->terms[0] = (char *) 0;
	np->terms[1] = (char *) 0;
	ax_terms(np, n);

	np->nxt = all_props;
	all_props = np;
}

static void
ax_decorate(scopetab_t *that, treenode *n)	/* set n->syment on all TN_IDENT leafs */
{	leafnode *m;

	if (!n) return;

	if (n->hdr.type != TN_IDENT)
	{	ax_decorate(that, n->lnode);
		ax_decorate(that, n->rnode);
	}
	m = (leafnode *) n;

	if (m->hdr.which == LEAF_T
	&&  m->hdr.type  == TN_IDENT)
	{	symentry_t *old = m->syment;

		m->syment = find_glob_symentry(that, m->data.sval->str);

		if (!old)
		{	printf("old symentry not set\n");
same:			printf("new:\t%s symtable entry for glob::%s\n",
				m->syment?"found":"missing",
				m->data.sval->str);
		} else if (m->syment != old)
		{	printf("new symentry differs from old:\n");
			printf("old:\t%s symtable entry for glob::%s\n",
				m->syment?"found":"missing",
				m->data.sval->str);
			goto same;
		} else
		{	printf("old and new both set and equal\n");
			goto same;
		}
	}
}

void
ax_proposition(FILE *fd, Ax_Props *p)
{
	if (p->t == 0)
	{	fprintf(fd, "c_code {	/* assert_r */\n");
		fprintf(fd, "	int _nq%d_(void) { return !(%s); }\n",
			p->nr, p->terms[0]);
		fprintf(fd, "	int _q%d_(void) { return (%s); }\n}\n",
			p->nr, p->terms[0]);
	} else
	{	fprintf(fd, "c_code {	/* assert_p */\n");
		fprintf(fd, "	int _q%d_(void) { return (%s); }\n",
			p->nr, p->terms[0]);
		fprintf(fd, "	int _r%d_(void) { return (%s); }\n}\n",
			p->nr, p->terms[1]);
	}
}

void
ax_fixed(FILE *fd)
{
	fprintf(fd, "bool _ax_runs;\n");
	fprintf(fd, "c_code {\n");
	fprintf(fd, "	int (*_ax_q)(void), (*_ax_r)(void);\n\n");
	fprintf(fd, "	void _ax_start(int (*q)(void), int (*r)(void))\n");
	fprintf(fd, "	{	_ax_q = q;\n");
	fprintf(fd, "		_ax_r = r;\n");
	fprintf(fd, "		now._ax_runs = 1;\n");
	fprintf(fd, "}	}\n\n");
	fprintf(fd, "never {\n");
	fprintf(fd, "start:	/* assert_p(q,r) or ![](p -> (q U r)) */\n");
	fprintf(fd, "	do\n");
	fprintf(fd, "	:: c_expr { now._ax_runs && !_ax_r() } -> break\n");
	fprintf(fd, "	:: else\n");
	fprintf(fd, "	od;\n");
	fprintf(fd, "accept:\n");
	fprintf(fd, "	do\n");
	fprintf(fd, "	:: c_expr {  _ax_r() } -> _ax_runs = 0; goto start\n");
	fprintf(fd, "	:: c_expr { !_ax_r() && !_ax_q() } -> break	/* safety */\n");
	fprintf(fd, "	:: else						/* liveness */\n");
	fprintf(fd, "	od\n");
	fprintf(fd, "}\n");
}

void
ax_doprops(FILE *fd, scopetab_t *that)
{	Ax_Props *p;

	if (ax_prop_nr == 0) return;

	ax_fixed(fd);

	for (p = all_props; p; p = p->nxt)
	{	ax_decorate(that, p->n);	/* redundant? */
		ax_proposition(fd, p);
	}
}

void
x_hashtab(hashtab_t *that, FILE *fp)
{	symentry_t *list;
	int j;

	for (j = 0; j < that->tsize; j++)
	for (list = that->tab[j]; list; list = list->next)
		x_frag(list->node, fp);
}

void
x_scopetab(scopetab_t *that, FILE *fp, char *want)
{	scopetab_t *z;
	int j;

	if (that->htab && that->level > 3)
	for (z = that->parent; z; z = z->parent)
		if (z->owner && strcmp(z->owner, "-") != 0
		&&  z->owner_t == TN_FUNC_DEF
		&&  strcmp(z->owner, want) == 0)
		{	x_hashtab(that->htab, fp);
			break;
		}

	for (j=0; j < that->nchild; j++)
		x_scopetab(that->children[j], fp, want);
}
