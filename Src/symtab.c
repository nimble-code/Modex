
/***** modex: symtab.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/* Original version by Shaun Flisakowski, Jul 15, 1997 */

#include  <stdio.h>
#include  <stdlib.h>
#include  <string.h>
#include  <assert.h>
#include  "utype.h"
#include  "symtab.h"
#include  "nmetab.h"
#include  "prnttree.h"

#define DBG	0	/* debugging */

static int	child_insert(scopetab_t *mom, scopetab_t *kid);
static symentry_t *mk_g(str_t *sym, treenode *tn, int knd);
       void	show_hashtab(hashtab_t *that, int, FILE *fp);
static void	show_scopetab(scopetab_t *that, int, FILE *fp);
static void	show_symentry(symentry_t *that, int, FILE *fp);

extern char	*current_filename(void);
extern int	current_linenumber(void);
extern int	must_ignore(symentry_t *);
extern char	*x_stmnt(treenode *);

extern void	x_frag(treenode *, FILE *);
extern int	Verbose;
extern char	*progname;

#define CHUNK	(1<<20)			/* allocate memory in 1 Mb increments */
#define ALGN	sizeof(long)		/* secure word alignment */

static long memcnt;
static long memwaste;

void e_free(void *m) { return; }

static long left;
static char *have;
static symentry_t *fses;

static hashtab_t *freehtab;
static scopetab_t *freestab;
static symtab_t *freesymt;

int visu;

static char *
not_malloc(uint n)
{	char *tmp;

	if (left < n)
	{	int grow = (n < CHUNK) ? CHUNK : n;
		have = (char *) malloc(grow);
		if (!have)
		{	fprintf(stderr, "%s: out of memory\n", progname);
			exit(1);
		}
		memset(have, 0, grow);
		left = grow;
	}
	tmp = have;
	have += n;
	left -= n;

	return tmp;
}

void *
e_malloc(uint m)
{	char *tmp;
	long n = m + ALGN;	/* for possible alignment */

	assert(m != 0);

	tmp = not_malloc(n);

	if (((ulong) tmp)&(ALGN-1))
	{	tmp += (long) (ALGN  - (((ulong) tmp)&(ALGN-1)));
		memwaste += ALGN;
	} else
	{	left += ALGN;	/* return the extra bytes */
		have -= ALGN;
	}

	memcnt += m;

	return (void *) tmp;
}

#if 0
void
memstats(void)
{
	printf("modex: %6d memory used", memcnt);
	if (memwaste && memcnt)
	printf(", %d%% memory wasted for alignments\n", 100*memwaste/memcnt);
}
#endif

static void
dotabs(int tabs, FILE *fp)
{	int j;

	for (j = 0; j < tabs; j++)
		fprintf(fp, "|\t");
}

static void
print_frag(treenode *root, FILE *fd)
{
	fprintf(fd, "\t[");	/* source text */
	if (root && (root->hdr.which != FOR_T))
		fprintf(fd, "%s", x_stmnt(root));
	else
		fprintf(fd, "fct");
	fprintf(fd, "]");
}

static void
show_symentry(symentry_t *that, int tabs, FILE *fp)
{
	dotabs(tabs+1, fp);
	fprintf(fp, "%s", that->nme->str);
	print_frag(that->node, fp);
	if (that->node
	&&  that->node->hdr.type != TN_FUNC_DEF
	&& !that->used)
		fprintf(fp, " unused");
	fprintf(fp, "\n");
#if 0
	if (that->container)
	{	fputs("Container:\n", fp);
		print_frag(that->container, fp);
	}
#endif
}

symentry_t *
new_symentry(void)
{	symentry_t *that;

	if (fses)
	{	that = fses;
		fses = fses->next;
		memset(that, 0, sizeof(symentry_t));
	} else
		that = (symentry_t *) e_malloc(sizeof(symentry_t));

	that->ln = current_linenumber();	/* gjh */
	that->fn = current_filename();		/* gjh */
	return that;
}

static symentry_t*
mk_g(str_t *sym, treenode *tn, int knd)	/* mk_generic */
{	symentry_t *that;

	that = new_symentry();

	that->kind = knd;
	that->nme  = sym;
	that->node = tn;
	that->nes = (scopetab_t *) 0;
	that->decl_level = 0;
	that->container = NULL;

	return that;
}

symentry_t *
mk_typedef(str_t *sym, treenode *tn) { return mk_g(sym,tn,TYPEDEF_ENTRY); }

symentry_t *
mk_funcdef(str_t *sym, treenode *tn) { return mk_g(sym,tn,FUNCDEF_ENTRY); }

symentry_t *
mk_vardecl(str_t *sym, treenode *tn) { return mk_g(sym,tn,VARDECL_ENTRY); }

symentry_t *
mk_enum_const(str_t *sym, treenode *tn) { return mk_g(sym,tn,ENUM_CONST_ENTRY); }

symentry_t *
mk_label(str_t *sym, treenode *tn) { return mk_g(sym,tn,LABEL_ENTRY); }

symentry_t *
mk_tag(str_t *sym, treenode *tn) { return mk_g(sym,tn,TAG_ENTRY); }

symentry_t *
mk_component(str_t *sym, treenode *tn, treenode *container)
{	symentry_t *entry = mk_g(sym,tn,COMP_ENTRY);

	entry->container = container;
	return entry;
}

int
is_typedef(symentry_t *that)
{
	return that && (that->kind == TYPEDEF_ENTRY);
}

hashtab_t *
new_hashtab(void)
{	hashtab_t *that;

	if (freehtab)
	{	that = freehtab;
		freehtab = that->nxt;
		if (that->tsize != INIT_HASHTAB_SIZE)
		{	fprintf(stderr, "cannot happen nht\n");
			exit(1);
		}
		memset(that->tab, 0, sizeof(symentry_t*) * that->tsize);
	} else
	{	that = (hashtab_t *) e_malloc(sizeof(hashtab_t));
		that->tsize = INIT_HASHTAB_SIZE;
		that->tab = (symentry_t **) e_malloc( sizeof(symentry_t*) * that->tsize );
	}
	that->nent = 0;

	return that;
}

symentry_t *
hashtab_lookup(hashtab_t *that, str_t *nme)
{	symentry_t *curr;
	int j;
  
	if (!nme || !that) return NULL;

	j = nme->hash % that->tsize;
	for (curr = that->tab[j]; curr; curr = curr->next)
		if (curr->nme
		&&  strcmp(curr->nme->str, nme->str) == 0) 
			return curr;

	return NULL;
}

symentry_t*
hashtab_insert(hashtab_t *that, symentry_t *entry)
{	int j;
	symentry_t *ret;

	if ((ret = hashtab_lookup(that, entry->nme)))
	{
		return ret;
	}

	if (0) printf("insert in hashtab %p -- %s\n",
		that, entry->nme->str);

	j = entry->nme->hash % that->tsize;
	entry->next = that->tab[j];
	that->tab[j] = entry;

	return entry;
}

void
show_hashtab(hashtab_t *that, int tabs, FILE *fp)
{	symentry_t *t;
	int j;

	for (j = 0; j < that->tsize; j++)
	for (t = that->tab[j]; t; t = t->next)
		show_symentry(t, tabs, fp);
}

static symentry_t *
find_hashtab(hashtab_t *that, char *s)
{	symentry_t *list;
	int j;

	for (j = 0; j < that->tsize; j++)
	for (list = that->tab[j]; list; list = list->next)
		if (list->nme
		&&  strcmp(s, list->nme->str) == 0)
			return list;

	return (symentry_t *) 0;
}

typedef struct Scoop Scoop;
struct Scoop {
	int		n;
	scopetab_t	**g;
	Scoop		*nxt;
};

static Scoop *scoop, *freescoop;

scopetab_t **
getscoop(int n)
{	Scoop *s, *prevs = (Scoop *) 0;
	scopetab_t **g = (scopetab_t **) 0;

	for (s = scoop; s; prevs = s, s = s->nxt)
		if (s->n == n)
		{	g = s->g;
			if (!prevs)
				scoop = s->nxt;
			else
				prevs->nxt = s->nxt;
				
			s->n = 0;
			s->g = (scopetab_t **) 0;
			s->nxt = freescoop;
			freescoop = s;
			break;
		}
	if (!g)
		g = (scopetab_t **) e_malloc( sizeof(scopetab_t*) * n );

	return g;
}

scopetab_t*
new_scopetab(scopetab_t *mom)
{	scopetab_t *that;

	if (freestab)
	{	that = freestab;
		freestab = that->parent;
		memset(that, 0, sizeof(scopetab_t));
	} else
		that = (scopetab_t *) e_malloc(sizeof(scopetab_t));

	if (0)
	printf("new scope tab %p, level %d\n", that, mom?mom->level+1:EXTERN_SCOPE);

	that->size = INIT_CHILD_SIZE;

	that->children = getscoop(that->size);

	that->parent = mom;
	if (mom)
		that->level = mom->level + 1;
	else
		that->level = EXTERN_SCOPE;

	return that;
}

symentry_t*
scopetab_find(scopetab_t *that, str_t *nme)
{	symentry_t *ret = NULL, *oret = NULL;
	int j;
	extern int structfieldflag;

if (DBG) {	printf("scopetab_find %s -- hashtab: <%p> -- ", nme->str, that?that->htab:0);
		printf("scopetab: %p, level: %d  nsyms: %d  nchild: %d -- structfield: %s -- owner_t: %d\n",
			that, that?that->level:-1, that?that->nsyms:-1, that?that->nchild:-1,
			structfieldflag?"YES":"no",
			that?that->owner_t:-1);
	}

	if (that)
	{	if (that->visited)
			return NULL;
		that->visited = 1;	/* prevent circularity */

		if (that->htab)
		{	if (!structfieldflag
			||   (that->level >= 3
			&&    that->owner_t == TN_OBJ_DEF))	/* Struct/Union, must have owner_t before ref */
			{	ret = hashtab_lookup(that->htab, nme);
			}
		}

		if (!ret && structfieldflag)	/* gjh */
		for (j = 0; j < that->nchild; j++)
		{	ret = scopetab_find(that->children[j], nme);
			if (ret)
			{	ret->used = 1;	/* set for all matches, return last */
				oret = ret;
if (DBG)			printf("Candidate Match %s: %p - %s:%d nes: %s\n",
					nme->str, ret, ret->fn, ret->ln,
					ret->nes && ret->nes->owner ? ret->nes->owner : "no owner");
		}	}
		if (!ret && oret) ret = oret;

		if (!ret) ret = scopetab_find(that->parent,nme);	/* goes up one level */

		that->visited = 0;
	}
	if (ret && structfieldflag) ret->used = 1;

	return ret;
}

symentry_t *
scopetab_insert(scopetab_t *that, symentry_t *entry)
{
#if DBG
	int i;
	printf("	Inserting '%s' at level %d -- owner %s (%d) -- nchild %d\n",
		entry->nme->str, that->level, that->owner, that->owner_t, that->nchild);
	printf("	scopetab: %u; ", that);
	for (i = 0; i < that->nchild; i++)
		printf("%u, ", that->children[i]);
	printf("\n");
	
#endif
	if (!that->htab)
	{	that->htab = new_hashtab();
		if (!that->htab)
			return 0;
	}

	return hashtab_insert(that->htab,entry);
}

static int
child_insert(scopetab_t *mom, scopetab_t *kid)
{	int j;

	if (0)
	printf("		child insert - level %d\n", mom->level);

	if (mom->nchild >= mom->size)
	{	scopetab_t **oldkids = mom->children;
		mom->size += mom->size;
		mom->children = (scopetab_t **) e_malloc( sizeof(scopetab_t*) * mom->size );

		for (j=0; j < mom->nchild; j++)
			mom->children[j] = oldkids[j];
	}

	mom->children[mom->nchild] = kid;
	(mom->nchild)++;

	return 1;
}

symentry_t *
find_glob_symentry(scopetab_t *that, char *s)
{	int j;
	symentry_t *fnd = (symentry_t *) 0;

	if (that->htab
	&&  that->level <= 2)
 		fnd = find_hashtab(that->htab, s);

	if (!fnd)
	for (j = 0; j < that->nchild; j++)
	{	if ((fnd = find_glob_symentry(that->children[j], s)) != NULL)
		{	break;
	}	}

	return fnd;
}

int
find_symbol(scopetab_t *st, symentry_t *se)
{	int i;
	hashtab_t *h;
	symentry_t *e;

	if (!st || !se) { printf("<%p,%p> ",st,se); return 0; }

	h = st->htab;

	if (h)
	for (i = 0; i < h->tsize; i++)
	for (e = h->tab[i]; e; e = e->next)
	{	if (e == se)
		{
same:			printf("%s:%d: (scopetab %p symentry %p)", se->fn, se->ln, st, se);

			if (se->container)
			{	printf("cont:<%s> ",
					x_stmnt(se->container));
			}

			if (Verbose&2)
			{	switch (st->level) {
				case  0: printf("Top"); break;
				case  1: printf("Global"); break;
				case  2: printf("File"); break;
				case  3: printf("Struct/FctParams"); break;
				default: printf("Block"); break;
				}
			}
			return 1;
		} else if (strcmp(e->nme->str, se->nme->str) == 0)
		{	if (1 || (Verbose&2))
			{	printf("<rogue match> ");
				goto same;
			}
			return 0;
	}	}

	if (find_symbol(st->parent, se))
		return 1;

	printf("\n===couldn't find it:===\n");
	visu = 1;
	show_scopetab(st, 0, stdout);
	visu = 0;
	printf("===\n\t");

	return 0;
}

extern char *nx_stmnt(treenode *);

static void
remove_newlines(char *s)
{	char *u;
	for (;;)
	{	u = strstr(s, "\\n");
		if (u) { *u++ = ' '; *u = ' '; }
		else { break; }
	}
}

void
remove_struct(char *s)
{	char *p, *q, *x;
	int cnt, m = 0, n = strlen(s);

	p = strstr(s, "struct");

	if (p)	/* check if struct is unnamed */
	{	x = p + strlen("struct");
		while (*x == ' ' || *x == '\t')
		{	x++;
		}
		if (*x == '{')	/* unnamed */
		{	return;
	}	}

	cnt = 0;
	for (q = p; q-p < n; q++)
	{	switch (*q) {
		case '{': cnt++; m++; break;
		case '}': cnt--; break;
		default: break;
		}
		if (m > 0)
		{	*q = ' ';
			if (cnt == 0)
			{	break;
	}	}	}
}

void
find_typedefs(scopetab_t *that, FILE *fp)
{	scopetab_t *z;
	symentry_t *t;
	char *s;
	int j;

	if (that->htab)
	{	for (z = that; z; z = z->parent)
		for (j = 0; j < that->htab->tsize; j++)
		for (t = that->htab->tab[j]; t; t = t->next)
		{	if (t->kind == TYPEDEF_ENTRY
			&&  t->generated == 0)
			{	s = nx_stmnt(t->node);
				if (strstr(s, "struct"))
				{	t->generated = 1;
					remove_newlines(s);
					remove_struct(s);	/* if named, it will be declared separately below */
					fprintf(fp, "c_decl { %s } /* find_typedefs %p, %p */\n", s, z, t);
	}	}	}	}

	for (j = 0; j < that->nchild; j++)
		find_typedefs(that->children[j], fp);
}

void
put_structs(scopetab_t *that, FILE *fp)
{	scopetab_t *z;
	symentry_t *t;
	char *s;
	int j;

	if (that->htab)
	{	for (z = that; z; z = z->parent)
		{	if (z->owner
			&&  z->owner_t == TN_OBJ_DEF
			&&  strcmp(z->owner, "-") != 0)
			{	/* sanity pretest */
				int shouldshow = 1;
				for (j = 0; j < that->htab->tsize && shouldshow; j++)
				for (t = that->htab->tab[j]; t; t = t->next)
				{	s = nx_stmnt(t->node);
					if (strstr(s, "->")
					||  strstr(s, "[]"))	/* both would produce invalid code */
					{	shouldshow = 0;
						break;
				}	}
				if (!shouldshow) break;
				/* end pretest */

				/* a possible issue:
				 * this does not reproduce the fields in
				 * the same order as the original
				 * struct declaration
				 */
				fprintf(fp, "c_decl {	/* put_structs */\n");
				fprintf(fp, "	struct %s {\n", z->owner);
				for (j = 0; j < that->htab->tsize; j++)
				for (t = that->htab->tab[j]; t; t = t->next)
				{	s = nx_stmnt(t->node);
					remove_newlines(s);

					while (strlen(s) > 0
					&& (s[strlen(s)-1] == ';'
					 || s[strlen(s)-1] == ' '))
					{	s[strlen(s)-1] = '\0';
					}
					fprintf(fp, "\t\t%s; /* P: %p */\n", s, z);
				}
				fprintf(fp, "\t};\n");
				fprintf(fp, "} /* end c_code. */\n");
				break;
		}	}
	}

	for (j = 0; j < that->nchild; j++)
		put_structs(that->children[j], fp);
}

static void
show_scopetab(scopetab_t *that, int tabs, FILE *fp)
{	int j;
#if DBG
	fprintf(fp, "scopetab %u, level: %d  nsyms: %d  nchild: %d\n",
		that, that->level, that->nsyms, that->nchild);
#endif

	if (that->htab)
	{	scopetab_t *z;
		char prepped[512];
#if 1
		prepped[0] = '\0';
#else
		switch (that->level) {
		case  0: strcpy(prepped, "scope level 0?"); break;
		case  1: strcpy(prepped, "Global scope:"); break;
		case  2: strcpy(prepped, "File scope:"); break;
		case  3: strcpy(prepped, "Struct/FctParams:"); break;
		default: strcpy(prepped, "Block:"); break;
		}
#endif
		for (z = that; z; z = z->parent)
			if (z->owner
			&&  strcmp(z->owner, "-") != 0)
			{	strcat(prepped, "\t");
				strcat(prepped, z->owner);
				switch (z->owner_t) {
				case TN_OBJ_DEF:  strcat(prepped, " [struct/union]"); break;
				case TN_FUNC_DEF: strcat(prepped, " [fct]"); break;
				case 0: strcat(prepped, " [global]"); break;
				default: strcat(prepped, " [block]"); break;
				}
				break;
			}
#if DBG
			else strcat(prepped, "-u-");
#endif
		dotabs(tabs, fp);
		fprintf(fp, "%s\n", prepped);
		show_hashtab(that->htab, tabs, fp);
		fprintf(fp, "\n");
	}

	for (j = 0; j < that->nchild; j++)
		show_scopetab(that->children[j], tabs+1, fp);
}

void
set_owner(scopetab_t *p, char *s, int tp)
{	int i;

	if (0) printf("	setowner for %p %s %d (%s)\n", p, s, tp,
			p->owner?p->owner:"not yet set");

	if (p->owner) return;	/* already named */

	p->owner = s;
	p->owner_t = tp;

	for (i = 0; i < p->nchild; i++)		/* propagate to nested unnamed scopes */
		set_owner(p->children[i], s, tp);
}

void
name_scope(context_t *q, char *s, int tp)
{	symtab_t *p = q->syms;

	if (DBG) printf("name_scope %p -- owner=%s (owner_t=%d) clevel %d, level %d\n",
		p->current,
		s, tp,
		p->clevel,
		p->current->level);
	set_owner(p->current, s, tp);

	if (Verbose&2)
	printf("SET level %d,%d, %s\n",
		p->clevel,  p->current->level,  s);
}

symtab_t*
new_symtab(void)
{	symtab_t *that;

	if (freesymt)
	{	that = freesymt;
		freesymt = that->nxt;
		memset(that, 0, sizeof(symtab_t));
	} else
		that = (symtab_t *) e_malloc(sizeof(symtab_t));

	that->root = new_scopetab(NULL);
	that->clevel = EXTERN_SCOPE;
	that->current = that->root;

	return that;
}

symentry_t*
symtab_lookup(symtab_t *that, str_t *nme)
{	symentry_t *ret = NULL;

	if (that->current)
		ret = scopetab_find(that->current, nme);

	return ret;
}

symentry_t*
symtab_insert(symtab_t *that, symentry_t *entry)
{	symentry_t *t;
#if DBG
	printf("	symtab insert %s (clevel %d currentlevel %d) %u\n",
		entry->nme->str, that->clevel, that->current->level, entry);
#endif
	while (that->clevel > that->current->level)
	{	scopetab_t *child = new_scopetab(that->current);

		if (!child || !child_insert(that->current,child))
			return NULL;

		that->current = child;
	}
	t = scopetab_insert(that->current,entry);
#if DBG
	printf("	inserted at %u\n", t);
#endif
	return t;
}

symentry_t *
symtab_insert_at(symtab_t *that, symentry_t *entry, int level)
{	scopetab_t *scp;
	scopetab_t *child;

#ifdef  MORE_VERBOSE
	printf("scope level %d; ",   that->current->level);
	printf("current level %d; ", that->clevel);
	printf("request level %d\n", level);
#endif

	while ((that->clevel >  that->current->level)
	    && (that->clevel >= level))
	{
		child = new_scopetab(that->current);

		if (!child
		||  !child_insert(that->current,child))
			return (symentry_t *) 0;

		that->current = child;
	}

	scp = that->current;

	while (scp && (scp->level > level))
		scp = scp->parent;

	if (scp)
		return scopetab_insert(scp,entry);

	return (symentry_t *) 0;
}

int
st_enter_scope(symtab_t *that)
{
	return ++(that->clevel);
}

void
st_exit_scope(symtab_t *that)
{
	(that->clevel)--;
	if (that->current->level > that->clevel)
		that->current = that->current->parent;
}

void
show_symtab(symtab_t *that, FILE *fp)
{
	visu = 1;
	show_scopetab(that->root, 0, fp);
}

typedef struct NameList NameList;
struct NameList {
	char *nm;
	NameList *nxt;
} *fctnms;

void
add_fctnm(char *s)
{	NameList *f;
	for (f = fctnms; f; f = f->nxt)
	{	if (strcmp(f->nm, s) == 0)
		{	return;
	}	}
	f = (NameList *) e_malloc(sizeof(NameList));
	f->nm = s;
	f->nxt = fctnms;
	fctnms = f;
}

int
is_fctnm(char *s)
{	NameList *f;
	for (f = fctnms; f; f = f->nxt)
	{	if (strcmp(f->nm, s) == 0)
		{	return 1;
	}	}
	return 0;
}

void
save_fcts(scopetab_t *that, FILE *fp)
{	scopetab_t *z;
	int j;

	for (z = that; z; z = z->parent)
	{	if (z->owner
		&&  z->owner_t == TN_FUNC_DEF
		&&  strcmp(z->owner, "-") != 0)
		{	add_fctnm(z->owner);
	}	}

	for (j = 0; j < that->nchild; j++)
		save_fcts(that->children[j], fp);
}

context_t*
new_context(void)
{	context_t *that = (context_t *) e_malloc( sizeof(context_t) );

	that->labels = new_symtab();
	that->tags   = new_symtab();
	that->syms   = new_symtab();

	return that;
}

int
enter_scope(context_t *that)
{
#ifdef  MORE_VERBOSE
	printf("	Enter Scope: %d\n", that->syms->clevel + 1);
#endif
	st_enter_scope(that->labels);
	st_enter_scope(that->tags);

	return st_enter_scope(that->syms);
}

void
exit_scope(context_t *that)
{
#ifdef  MORE_VERBOSE
	printf("	Exit Scope: %d\n", that->syms->clevel);
#endif
	st_exit_scope(that->labels);
	st_exit_scope(that->tags);
	st_exit_scope(that->syms);
}

void
exit_scopes(context_t *that, int newlev)
{
	if (newlev < EXTERN_SCOPE)
		newlev = EXTERN_SCOPE;

	while (newlev < that->syms->current->level)
		exit_scope(that);
}

typedef struct Cname {
	char	*vn;
	int	hit;
	int 	isvis;
	int	purged;
	struct	Cname *nxt;
} Cname;

static Cname	*cnames, *icalls, *pnames;

void
add_constant(char *p, int isvis)
{	Cname *s;

	for (s = cnames; s; s = s->nxt)
		if (strcmp(p, s->vn) == 0)
			return;
	s = (Cname *) e_malloc(sizeof(Cname));
	s->vn = (char *) e_malloc(strlen(p)+1);
	strcpy(s->vn, p);
	s->hit = 0;
	s->isvis = isvis;
	s->nxt = cnames;
	cnames = s;
}

int
is_constant(char *p)
{	Cname *s;

	for (s = cnames; s; s = s->nxt)
		if (strcmp(p, s->vn) == 0)
		{	s->hit = 1;
			return 1;
		}
	return 0;
}

void
do_constants(FILE *fd)
{	Cname *s;
	int i = 1;

	if (!cnames) return;

	fprintf(fd, "\n");
	for (s = cnames; s; s = s->nxt)
	{	if (s->purged)
		{	continue;
		}
		s->purged = 1;
		if (s->isvis)
		{	fprintf(fd, "hidden int %s = %d;\n", s->vn, i++);
	}	}
	fprintf(fd, "\n");
}

void
add_icall(char *p)
{	Cname *s;

	for (s = icalls; s; s = s->nxt)
		if (strcmp(p, s->vn) == 0)
			return;
	s = (Cname *) e_malloc(sizeof(Cname));
	s->vn = (char *) e_malloc(strlen(p)+1);
	strcpy(s->vn, p);
	s->hit = 0;
	s->nxt = icalls;
	icalls = s;
}

int
is_icall(char *p)
{	Cname *s;

	for (s = icalls; s; s = s->nxt)
		if (strcmp(p, s->vn) == 0)
		{	s->hit = 1;
			return 1;
		}
	return 0;
}

void
add_pname(char *p)
{	Cname *s;

	for (s = pnames; s; s = s->nxt)
		if (strcmp(p, s->vn) == 0)
			return;
	s = (Cname *) e_malloc(sizeof(Cname));
	s->vn = (char *) e_malloc(strlen(p)+1);
	strcpy(s->vn, p);
	s->hit = 0;
	s->nxt = pnames;
	pnames = s;
}

int
is_pname(char *p)
{	Cname *s;

	for (s = pnames; s; s = s->nxt)
		if (strcmp(p, s->vn) == 0)
		{	s->hit = 1;
			return 1;
		}
	return 0;
}
