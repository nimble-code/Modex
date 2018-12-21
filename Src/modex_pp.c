/***** modex: modex_pp.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include "dflow.h"
#include "modex_cpp.h"

/* modex preprocessing */

extern int	sysoverride, nopre, Verbose, debug_io;
extern char	*preproc_info, *sedproc_info;
extern char	*master_dfn, *progname;
extern char	tempfile_M[];

extern char	*e_malloc(unsigned int);
extern int	unlink(const char *);
extern void	Fclose(FILE *);

static void
avoid_name_clash(char *p, char *s)
{	char *q;
	int n = strlen(s);
	int m = strlen(p);

	while (m > 0 && (q = strstr(p, s)) != NULL)
	{	if (*(q-1) != '_'
		&& !isalnum((int)*(q-1))
		&&  *(q+n) != '_'
		&& !isalnum((int)*(q+n)))
		{	*q = toupper((int) *q);
		}
		p = q+n;
		m = strlen(p);
	}
}

void
strip_sys_includes(char *z, char *f, char *m)
{	FILE	*fd, *fo;
	char	buf[1024];
	char	*p;
	char	*match_what = NULL;
	char	*curfile    = NULL;
	int	first_directive = 1;

	*z = 'I';

	if ((fo = fopen(f, MFLAGS)) == NULL)	/* .I intermediate */
	{	fprintf(stderr, "modex: cannot create %s\n", f);
		goto clean;
	}
if (debug_io) fprintf(stderr, "fopen %s -> %p\n", f, fo);
	fprintf(fo, "#define pthread_t	int\n");
	fprintf(fo, "#define thread_t	int\n");
	fprintf(fo, "#define pthread_mutex_t	int\n");
	fprintf(fo, "#define pthread_cond_t	int\n");
	fprintf(fo, "#define mutex_t	int\n");
	fprintf(fo, "#define key_t	int\n");

	if ((fd = fopen(m, "r")) != NULL)	/* .dfn file -- if any */
	{	fprintf(fo, "#define UnoType	typedef int\n");
if (debug_io) fprintf(stderr, "fopen %s -> %p\n", m, fd);
		while (fgets(buf, 1024, fd))
			fprintf(fo, "%s", buf);
if (debug_io) fprintf(stderr, "close xx %p\n", fd);
		Fclose(fd);
	}
	fprintf(fo, "typedef int __builtin_va_list;\n"); /* gcc-ism */
	fprintf(fo, "typedef int __w64;\n");		 /* cl-ism */
	fprintf(fo, "typedef int _Bool;\n");		 /* c99 */
	fprintf(fo, "#define __restrict\n");		 /* gcc-ism */

	if (master_dfn)
	if ((fd = fopen(master_dfn, "r")) != NULL)	/* possible master .dfn file */
	{
if (debug_io) fprintf(stderr, "fopen %s -> %p\n", master_dfn, fd);
		while (fgets(buf, 1024, fd))
			fprintf(fo, "%s", buf);
if (debug_io) fprintf(stderr, "close yy %p\n", fd);
		Fclose(fd);
	}

	*z = 'c';
	if ((fd = fopen(f, "r")) == NULL)	/* .c file */
	{	fprintf(stderr, "%s: cannot open %s\n", progname, f);
		*z = 'I';	/* remove .I intermediate */
		unlink(f);
clean:		unlink("_modex_.run");
		exit(1);
	}
if (debug_io) fprintf(stderr, "--fopen %s -> %p\n", f, fd);

	fprintf(fo, "#line 1 \"%s\"\n", f);	/* restore linenumber and filename */

	while (fgets(buf, 1024, fd))
	{	if (buf[0] == '#')
		{	char *op;
			p = &buf[1];
			while (*p == ' ' || *p == '\t')
			{	p++;
			}
			op = p;

			/* eliminat output from external preprocessing
			   of system include files -- pan.c
			   will include the necessary files separately
			 */
			if (isdigit((int) *p)
			||  strncmp(p, "line", strlen("line")) == 0)	/* it is preprocessor output */
			{	char *q;
				q = p = strchr(p, '"');
				if (p)
				{	p++; q++;
					q = strchr(q, '"');
					if (q)
					{	*q = '\0';
						if (first_directive)
						{	match_what = (char *) e_malloc(strlen(p)+1);
							/* remember original filename: */
							strcpy(match_what, p);
							first_directive = 0;
						}
						curfile = (char *) e_malloc(strlen(p)+1);
						strcpy(curfile, p);
						continue;
				}	}
				p = op;
			}

			if (strncmp(p, "include", strlen("include")) == 0)
			{	p += strlen("include");
				while (*p == ' ' || *p == '\t')
					p++;
				if (sysoverride == 0
				&&  *p == '<')			/* system header file */
				{	fprintf(fo, "\n");	/* maintain linecount */
					continue;		/* skip it */
		}	}	}

		if (match_what
		&&  curfile
		&&  strcmp(match_what, curfile) != 0)
		{	continue;		/* preprocessed headers */
		}

		avoid_name_clash(buf, "empty");	/* empty -> Empty */
		avoid_name_clash(buf, "full");	/* full  -> Full */
		avoid_name_clash(buf, "init");	/* init  -> Init */
		avoid_name_clash(buf, "len");	/* len   -> Len */
		avoid_name_clash(buf, "skip");	/* skip  -> Skip */

		fprintf(fo, "%s", buf);
	}

if (debug_io) fprintf(stderr, "close 2x %p %p\n", fd, fo);

	Fclose(fd);
	Fclose(fo);
	fo = NULL;
}

int
modex_pp(char *f, char *m)
{	char	*cpp_cmmd;
	char	*g, origf[1024], *z;
	int	retval;

	g = &tempfile_M[0];

	if (!f || (z = strstr(f, ".c")) == NULL)
	{	fprintf(stderr, "%s: cannot happen <%s>\n", progname, f);
		exit(1);
	}
	strcpy(origf, f);		/* origf = .c original */
	z++;

	strip_sys_includes(z, f, m);	/* creates .I from .dfn(s), .c and prop */

	*z = 'M';
	strcpy(g, f);			/* g = .M intermediate */
	*z = 'I';			/* f = .I intermediate */

	cpp_cmmd = (char *)
		e_malloc((unsigned int)(sizeof(char)*
			(32
			+ strlen(preproc_info)
			+ strlen(sedproc_info)
			+ strlen(f)
			+ strlen(g))));

	if (nopre)
	{	sprintf(cpp_cmmd, "cat %s | %s | grep -v \"^ *#\" >%s",
			f, sedproc_info, g);

		if (Verbose) printf("<%s>\n", cpp_cmmd);

		retval = system(cpp_cmmd);
	} else
	{
#define NO_REDEF_ASSERT
#ifdef NO_REDEF_ASSERT
		// remove an undesired code patch from the tacas contest files
		sprintf(cpp_cmmd, "cat %s | %s | grep -v -e \"#define assert\" > _m_tmp_",
			f, sedproc_info);

		if (Verbose) printf("<%s>\n", cpp_cmmd);

		system(cpp_cmmd);

		sprintf(cpp_cmmd, "%s -DMODEX %s _m_tmp_ >%s",
			CPP, preproc_info, g);
#else
		sprintf(cpp_cmmd, "cat %s | %s | %s -x c -DMODEX %s >%s",
			f, sedproc_info, CPP, preproc_info, g);
#endif
		retval = system(cpp_cmmd);			/* produce .M */

		if (Verbose) printf("<%s>\n", cpp_cmmd);

#ifdef NO_REDEF_ASSERT
		unlink("_m_tmp_");	// remove intermediate file
#endif
	}

	if (!Verbose) unlink(f);				/* remove the .I file */

	*z = 'c';	/* restore */
	return retval;
}
