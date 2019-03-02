/***** modex: modex.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */
/* Extensions (c) 2004-2014 by Caltech/JPL Pasadena, CA 91109             */

#include <sys/types.h>
#include <sys/stat.h>
#include <math.h>
#include <ctype.h>
#include "version.h"

#define DEFINE_GLOBALS
#include "globals.h"
#undef DEFINE_GLOBALS
#include "modex_cpp.h"

#ifdef PC
#include <process.h>
#else

#if defined(PLAN9) || defined(PC)
#include "utype.h"
#endif

#endif
#define Banner	"# Modex Lookup Table"

#include "gram.h"
#include "tree.h"
#include "prnttree.h"

char	o_base[512], cur_in[512];
char	*suffix = "nlut", *progname = "modex";
char	*want = "main";
char	*wantpre, *lut = "none.lut", *ulut;
char	*wanttype = "active proctype";
char	*modelname = "_modex_";
char	*lnkage_info;
char	*preproc_info="";
char	*runtime = "";
char	*sedproc_info="cat";
char	*master_dfn;
char	*optimized="";
int	new_lut, globals_only;
int	show_syms, Verbose, show_deps, show_code, printall, fallout;
int	allprocs, show_funcs, allkeep, suppress, omissions, redundancies;
int	sawFile, do_dflow, hasaction, Verbose_cmds, Warnings;
int	sysoverride;	/* don't strip <> headers when set */
int	extended;	/* with support for param passing */
int	flike;		/* atomic, more or less like a function */
int	predot;		/* dot input from parse tree */
int	nopre, preview, anybody, used_spin_malloc, spin_heap_size=256;
int	tagrun;
int	dynamic;	/* use dynamic process/thread creation for default models, if set */
			/* if non-zero: also gives bound on max nr threads */
int	nostructs;	/* dont generate additional typedefs and structs if set */
int	do_inc_locals = 1, do_inc_globals = 1;
int	use_c_code = 1, i_assert = 1, must_preprocess = 1;
int	du_mode, nrprocs = 1, nrprocs_default = 1;

int	quality = 9;	/* 1..10 - 10=exhaustive, 9=HC, <9=bitstate  */
int	maxdepth = 10000;
int	memlim   = 15000;
int	vectorsz = 1024;
int	loops, np_loops, noend, noassert;
int	shortest, exhaustive, bfs, bfs_par;
int	add_printfs;
int	debug_io = 0;

treenode	*parse_tree;
context_t	*contxt;

void	process_input(char *, int);
char	*current_filename(void);

extern int	modex_pp(char *, char *);
extern void	add_fnm(char *);
extern void	add_icall(char *);
extern void	add_pname(char *);
extern void	add_imported(char *, char *, int);
extern void	name_scope(context_t *, char *, int);
extern DefUse	*walk_tree(treenode *, unsigned long);
extern void	show_fbase(FILE *);
extern void	dep_show(void);
extern void	notimported(FILE *);
extern void	do_globals(int, scopetab_t *, int);
extern void	def_inc_spn(FILE *);
extern void	spitnames(FILE *);
extern void	alldone(void);
extern void	*e_malloc(uint);
extern void	dot_start(treenode *);
extern int	unlink(const char *);

void
Fclose(FILE *fd)
{
if (debug_io) fprintf(stderr, "-Close %p\n", fd);

	fclose(fd);
}

void
Usage(char *prog)
{	FILE *fd = stderr;
	fprintf(fd, "Model Extractor for ANSI-C code\n");
	fprintf(fd, "%s\n", VERSION);
	fprintf(fd, "==========================\n");
	fprintf(fd,"Usage: %s ..options.. file.c\n", prog);

	fprintf(fd,"\nGlobal Modes\n");
	fprintf(fd,"\t-A\tadd print statements to all steps (*after* the step, see also -printf)\n");
	fprintf(fd,"\t-b fname.c\tchange input to fname.c\n");
	fprintf(fd,"\t-c\tturn off c_code mode, and use builtin defaults\n");
	fprintf(fd,"\t-t\ttreat falling out of a switch stmnt as an error\n");
	fprintf(fd,"\t-g\tgenerate (only) a global declarations file for all fcts\n");
	fprintf(fd,"\t-G\tinvert default on #including globals (defaults to off with -n)\n");
	fprintf(fd,"\t-H\tinvert default on #including locals  (defaults to on)\n");
	fprintf(fd,"\t-K\tmap everything to 'keep'\n");
	fprintf(fd,"\t-P\tuse previously preprocessed .M file unless .c is newer\n");
	fprintf(fd,"\t-S\tsuppress generation of variable declarations\n");
	fprintf(fd,"\t-Z\tinvert default on checking assert_p and assert_r (defaults to on)\n");
	fprintf(fd,"\t-z\tdo not strip system include files before parsing target sources\n");
	fprintf(fd,"\t-heapsize N\tset spin heapsize for spin_malloc to N byte (default 256)\n");

	fprintf(fd,"\t-master x\tprepend file x to source before parsing\n");
	fprintf(fd,"\t-nopre \tremove all preprocessing directives\n");
	fprintf(fd,"\t-nostructs\tdont generate default data structures and typedefs\n");
	fprintf(fd,"\t-qN    \tset verification quality to N (1..10)\n");
	fprintf(fd,"\t\t1..8 = bitstate, 9 = hashcompact 10 = full, default %d\n", quality);
	fprintf(fd,"\t-run \tdo all processing and then run the verification\n");
	fprintf(fd,"\t-printf\tadd a printf statement to all imported C code in model (*before* the step, see also -A)\n");

	fprintf(fd,"\nPreprocessing Directives\n");
	fprintf(fd,"\t-D\tdefine a name,   e.g. -DDEBUG\n");
	fprintf(fd,"\t-U\tundefine a name, e.g. -UDEBUG\n");
	fprintf(fd,"\t-I\tadd directory to search for include files, e.g. -I. -IPublic\n");
	fprintf(fd,"\t-O\tadd directives for compilation of pan, e.g. -O \"-DVECTORSZ=4096\"\n");
	fprintf(fd,"\t-Q\tset series of preprocessing macros, e.g. -Q \"-DDEBUG -I. -IPublic\"\n");
	fprintf(fd,"\t-R \"...\" define additional ./pan runtime flags for verification\n");
	fprintf(fd,"\t-T\tset preprocessing sed cmd, e.g. -T \"s;replace;with;g\"\n");

	fprintf(fd,"\nLookup Table	(default: use but do not update lookup table if present)\n");
	fprintf(fd,"\t-k\t\tcreate new lookup tables, use extension .nlut (-V adds decls on stdout)\n");
	fprintf(fd,"\t-L lname\tuse lookup table in lname\n");
	fprintf(fd,"\t-M suffix\tlike -k, but use suffix instead of nlut\n");

	fprintf(fd,"\nTargets\n");
	fprintf(fd,"\t-a[n] pname\tgenerate 1 (or n) active proctype(s) for fct pname\n");
	fprintf(fd,"\t-i pname\tlike -a but generates an inline definition\n");
	fprintf(fd,"\t-n pname\tlike -a but generates only the proctype body\n");
	fprintf(fd,"\t-p pname\tlike -a but generates a passive proctype\n");
	fprintf(fd,"\t-e pname\tlike -a with parameter passing support\n");
	fprintf(fd,"\t-E pname\tlike -p with parameter passing support\n");
	fprintf(fd,"\t-x[n]\t\textract all fcts as active proctypes\n");
	fprintf(fd,"\t-xE\t\textract all fcts as extended proctypes\n");
	fprintf(fd,"\t-xe[n]\t\textract all fcts (except main) as extended active proctypes\n");
	fprintf(fd,"\t-xp\t\textract all fcts as proctypes\n");
	fprintf(fd,"\t-xi\t\textract all fcts as inlines\n");
	fprintf(fd,"\t-m mname\tuse mname as a basename for the generated files\n");
	fprintf(fd,"\t-Nn\tset the default nr of active processes to instantiate per fct to n\n");

	fprintf(fd,"\nInfo\n");
	fprintf(fd,"\t-C\tattempt to reproduce input\n");
	fprintf(fd,"\t-F\tprint all fct names encountered on stdout\n");
	fprintf(fd,"\t-o\tprint all omissions in the lookup table\n");
	fprintf(fd,"\t-r\tprint all redundant entries in the lookup table\n");
	fprintf(fd,"\t-s\tshow symbol table information on stdout\n");
	fprintf(fd,"\t-V\tprint version information and exit\n");
	fprintf(fd,"\t-X\tshow dependency graph, including trans. closure\n");
	fprintf(fd,"\t-Y\tprint commands as they are executed\n");
	fprintf(fd,"\t-v\tverbose\n");
	fprintf(fd,"\t-w\tprint warnings\n\n");

	fprintf(fd, "\t-parsetree\tgenerate dot output of parsetree\n");
	fprintf(fd, "\t-cfg\t\tgenerate dot output for control-flow graph\n");
	fprintf(fd, "\t-fcg\t\tgenerate dot output for function-call graph\n");

#if 0
	fprintf(fd,"\nExperimental\n");
	fprintf(fd, "\t-defuse\ttry to generate a def/use model\n");
#endif
	exit(1);
}

typedef struct Cmd {
	int	cmd;
	int	n;
	char	*arg;
	struct Cmd *nxt;
} Cmd;

Cmd *cmds;
Cmd *ncmd;

void
new_cmd(char c, char *s, int h)
{	Cmd *cmd;

	if (!s)
	{	fprintf(stderr, "modex: bad argument to '%c'\n", c);
		exit(1);
	}

	if (c == 'e')	// instrumented function
	{	add_icall(s);
	}
	if (c == 'p')	// passive proctype
	{	add_pname(s);
	}

	cmd = (Cmd *) e_malloc(sizeof(Cmd));
	memset(cmd, 0, sizeof(Cmd));
	cmd->cmd = c;
	cmd->n = nrprocs;
	cmd->arg = (char *) e_malloc(strlen(s)+1);
	strcpy(cmd->arg, s);

	if (Verbose_cmds)
	{	printf("New cmd <%c> <%s> <called from: %d> (nrprocs %d)\n", c, s, h, nrprocs);
	}

	if (cmds)
	{	cmds->nxt = cmd;
	}
	cmds = cmd;

	if (!ncmd)
	{	ncmd = cmds;
	}
}

void
expand_cmd(char c, char *s, int h)	// e.g., s="one,two,three"
{	char *z = s;

	while (s != NULL && (z = strchr(s, ',')) != NULL)
	{	*z = '\0';
		new_cmd(c, s, h);
		s = z+1;
	}
	if (s != NULL)	// last one in list
	{	new_cmd(c, s, h);
	}
}

int
BldCmds(int argc, char **argv)
{	char *arg;

	argc--; 
	argv++;

	while(argc-- > 0)
	{	arg = *argv++;

		if (arg[0] == '-')
		{	if (strncmp(arg, "-dynamic", strlen("-dynamic")) == 0)
			{	if (isdigit((int) *(arg+strlen("-dynamic"))))
				{	dynamic = atoi(arg+(int)strlen("-dynamic"));
					if (dynamic > 250)
					{	dynamic = 250;
					} else if (dynamic < 1)
					{	dynamic = 1;
					}
				//	printf("modex: max nr of threads: %d\n", dynamic);
				} else
				{	dynamic = 250;
				}
				continue;
			} else if (strcmp(arg, "-parsetree") == 0) /* dot output of parsetree */
			{	predot = 1;
				do_dflow=1;
				continue;
			} else if (strcmp(arg, "-cfg") == 0)	/* dot output control flow graph */
			{	preview     = 2;
				do_dflow    = 1;
				sysoverride = 1;
				continue;
			} else if (strcmp(arg, "-fcg") == 0)	/* dot output fct call graph */
			{	preview     = 3;
				do_dflow    = 1;
				sysoverride = 1;
				continue;
			} else if (strcmp(arg, "-nopre") == 0)
			{	nopre = 1;
				continue;
			} else if (strcmp(arg, "-nostructs") == 0)
			{	nostructs = 1;
				continue;
			} else if (strcmp(arg, "-master") == 0)
			{	master_dfn = (char *) e_malloc(strlen(*argv)+1);
				strcpy(master_dfn, *argv);
				continue;
			} else if (strcmp(arg, "-defuse") == 0)
			{	do_dflow = 1;
				du_mode = 1;
				continue;
			} else if (strcmp(arg, "-heapsize") == 0)
			{	spin_heap_size = atoi(*argv);
				argc--; argv++;
				continue;
			} else if (strcmp(arg, "-run") == 0)
			{	tagrun = 1;
				continue;
			} else if (strcmp(arg, "-printf") == 0)
			{	add_printfs = 1;
				continue;
			}

			nrprocs = nrprocs_default;

			switch (arg[1]) {
			case 'x':
				want = "all";
				hasaction = 1;
				// fall thru
				if (isdigit((int) arg[strlen(arg)-1]))
				{	nrprocs = atoi(&arg[strlen(arg)-1]);
				} else
				{	nrprocs = nrprocs_default;
				}
			default:
				new_cmd(arg[1], arg, 1);
				break;

			/* commands with arguments */
			case 'a':
			case 'e':	/* -e or -eN or -ex */
			case 'N':
				if (isdigit((int) arg[2]))
				{	nrprocs = atoi(&arg[2]);
				} else
				{	nrprocs = 1;
				}
				if (arg[1] == 'N')
				{	nrprocs_default = nrprocs;
					break;
				}
				// fall thru
			case 'E':
			case 'f':
			case 'n':
			case 'i':
			case 'p':
				want = *argv;
				hasaction = 1;
				// fall thru
			case 'L':
			case 'M':
			case 'm':
			case 'b':
				if (!*argv)
				{	Usage("modex");
				}
				if (*argv != NULL && strchr(*argv, ',') != NULL)
				{	expand_cmd(arg[1], *argv, 20);
				} else
				{	new_cmd(arg[1], *argv, 2); // argv points to next arg
				}
				argc--; argv++;
				break;

			/* immediate commands */
			case 'C': show_code  = do_dflow = allprocs = 1; break;
			case 'X': show_deps  = do_dflow = allprocs = 1; break;
			case 'F': show_funcs = do_dflow = allprocs = 1; break;
			case 's': show_syms  = do_dflow = allprocs = 1; break;

			case 'q':
				if (arg[2] != '\0' && isdigit((int) arg[2]))
				{	quality = atoi(&arg[2]);
				} else
				{	if (isdigit((int) *argv[0]))
					{	quality = atoi(*argv);
					} else
					{	Usage("bad q flag parameter");
				}	}
				break;

			case 'O': /* -O "-DMEMLIM=8000 -O2" etc. compiler directives for pan.c */
				if (strlen(optimized) > 0)
				{	Usage("modex: multiple use of -O");
				}
				if (isdigit((int) arg[2]))	/* e.g., a plain -O3 */
				{	optimized = (char *) e_malloc(strlen(arg)+1);
					strcpy(optimized, arg);	/* older version */
					break;
				}
				/* new 2.6 */
				arg = *argv;	/* next argument */
				if (arg)
				{	while (*arg == ' ' || *arg == '\t')
					{	arg++;
					}
					optimized = (char *) e_malloc(strlen(arg)+1);
					strcpy(optimized, arg);
					argc--; argv++;
				} else
				{	Usage("modex");
				}
				break;

			case 'Q':	/* source compilation e.g.: -Q "-DDEBUG -I. -IPublic" */
				if (strlen(preproc_info) > 0)
				{	Usage("modex: multiple use of -Q");
				}
				arg = *argv;	/* next argument */
				if (arg)
				{	while (*arg == ' ' || *arg == '\t')
					{	arg++;
					}
					preproc_info = (char *) e_malloc(strlen(arg)+1);
					strcpy(preproc_info, arg);
					argc--; argv++;
				} else
				{	Usage("modex");
				}
				break;
			case 'R':	/* pan runtime flags, e.g.: -R "-E" */
				arg = *argv;
				if (arg)
				{	while (*arg == ' ' || *arg == '\t')
					{	arg++;
					}
					runtime = (char *) e_malloc(strlen(arg)+2);
					strcpy(runtime, arg);
					strcat(runtime, " ");
					argc--; argv++;
				} else
				{	Usage("modex");
				}
				break;
			case 'T':	/* e.g.: -T "s;replace;with;g" or %T sed "...." */
				arg = *argv;
				if (arg)
				{	char *tmp;
					while (*arg == ' ' || *arg == '\t')
					{	arg++;
					}
					tmp = (char *) e_malloc(strlen(sedproc_info) + strlen(arg)+1+6+3);
					// 6 = "sed '' 3=" | "
					sprintf(tmp, "%s | sed '%s'", sedproc_info, arg);
					sedproc_info = tmp;
					argc--; argv++;
				} else
				{	Usage("modex");
				}
				break;

			case 'U':	/* undefine symbol */
			case 'D':	/* define symbol */
			case 'I':	/* set include directory */
				if (strlen(preproc_info) == 0)
				{	preproc_info = (char *) e_malloc(strlen(arg)+1);
					strcpy(preproc_info, arg);
				} else
				{	char *pp = (char *) e_malloc(strlen(arg)+strlen(preproc_info)+1+1);
					strcpy(pp, preproc_info);
					strcat(pp, " ");
					strcat(pp, arg);
					preproc_info = pp;
				}
				/* printf("arg: <%s>\n", preproc_info); */
				break;

			case 'P':
				must_preprocess = 0;
				break;
			case 'Z':
				i_assert = 1 - i_assert;
				break;
			case 'z':
				sysoverride = 1 - sysoverride;
				break;
			case 'V':
				printf("%s\n", VERSION);
				exit(0);
			case 'Y':
				Verbose_cmds = 1;
				break;
			case 'v':
				Verbose = 1;	/* Verbose |= 2 or 4 for debugging verbosity */
				break;
			case 'w':
				Warnings = 1;
				break;
			case '?':
			case '-':
				Usage("modex");

			}
		} else if (arg)
		{	char *p;

			if (!preview
			||  ((p = strstr(arg, ".c")) != NULL
			&&   strcmp(p, ".c") == 0))
			{	if (Verbose_cmds)
				{	printf("-- setting file_name to %s\n", arg);
				}
				file_name = arg;
			}
			break;
		} else
			return 0;
	}

	return 1;
}

int
ActCmds(void)
{	int done = 0;

	strcpy(o_base, "_modex_");
	do {
		if (!ncmd)
		{	if (Verbose_cmds)
				printf("Act cmd : no more commands\n");
			return 0;
		}

		if (Verbose_cmds)
		printf("Act cmd -%c %s\n",
			ncmd->cmd, ncmd->arg ? ncmd->arg : "");

		extended = flike = 0;

		switch (ncmd->cmd) {
		case 'E': extended = 1;
			  wanttype = "proctype";
			  want = ncmd->arg;
			  done = 1;
			  break;
		case 'f': flike = 1; /* atomic more or less like a function */
			  /* fall through */
		case 'e': extended = 1;
			  /* fall through */
		case 'a': wanttype = "active proctype";
			  if (ncmd->n > 1)
			  {	char *p = e_malloc(strlen(wanttype)+8);
				sprintf(p, "active [%d] proctype", ncmd->n);
				wanttype = p;
			  }
			  want = ncmd->arg;
			  done = 1;
			  break;
		case 'b': process_input(ncmd->arg, 1); break;
		case 'i': wanttype = "inline"; want = ncmd->arg; done = 1; break;
		case 'n': wanttype = "body";   want = ncmd->arg; done = 1;
			  do_inc_globals = 0; anybody = 1;
			  break;
		case 'p': wanttype = "proctype"; want = ncmd->arg; done = 1; break;
		case 'g': globals_only = 1;
			  /* fall through */
		case 'x': allprocs = 1;
			  want = "all";
			  if (ncmd->n > 1)
			  {	char *p = e_malloc(strlen(wanttype)+8);
				sprintf(p, "active [%d] proctype", ncmd->n);
				wanttype = p;
			  } else
			  {	wanttype = "active proctype";
			  }
			  if (ncmd->arg)
			  switch (ncmd->arg[2]) {
			  case 'f': flike = 1;
			  case 'e': extended = 1; break;
			  case 'E': extended = 1; /* fall thru */
			  case 'p': wanttype = "proctype"; break;
			  case 'i': wanttype = "inline"; break;
			  }
			  done = 1;
			  break;

		case 'A': printall       = 1 - printall;       break;
		case 'C': show_code      = 1; allprocs = 1;    break;
		case 'c': use_c_code     = 1 - use_c_code;     break;
		case 'X': show_deps      = 1; allprocs = 1;    break;
		case 'F': show_funcs     = 1; allprocs = 1;    break;
		case 't': fallout        = 1 - fallout;        break;
		case 'G': do_inc_globals = 1 - do_inc_globals; break;
		case 'H': do_inc_locals  = 1 - do_inc_locals;  break;
		case 'K': allkeep        = 1 - allkeep;        break;
		case 'k': new_lut        = 1; break;
		case 'L': if (!ulut) { ulut = ncmd->arg; } break;
		case 'M': new_lut        = 1; suffix = ncmd->arg; break;
		case 'm': strcpy(o_base, ncmd->arg); break;
		case 'o': omissions      = 1 - omissions;      break;
		case 'r': redundancies   = 1 - redundancies;   break;
		case 'S': suppress       = 1 - suppress;       break;
		case 's': show_syms      = 1; allprocs = 1;    break;

		default:	Usage("modex");
		}
		ncmd = ncmd->nxt;
	} while (!done);

	strcat(o_base, want);
	wantpre = (char *) e_malloc(strlen(want)+strlen("::")+1);
	strcpy(wantpre, want);
	strcat(wantpre, "::");

	return 1;
}

static int inlut, incode, inspn, indfn, nfls;
static int ingui, haspml, hasdrv, hasltl, inltl;
static FILE *fo, *fdrv;

void
mkfo(char *fnm)
{
	if ((fo = fopen(fnm, MFLAGS)) == NULL)
	{	fprintf(stderr, "modex: checkprx: cannot create %s\n", fnm);
		exit(1);
	}
if (debug_io) fprintf(stderr, "Open %s -> %p\n", fnm, fo);

	add_fnm(fnm);
	/* printf("	%s\n", fnm); */
	nfls++;
}

void
header(char *bnm, char *suffix1)
{	char *fnm;

	if (fo)
	{	if (incode && !inltl) fprintf(fo, "}\n");
		if (fo != fdrv)
		{	if (debug_io)
			{	fprintf(stderr, "close 3 %p\n", fo);
			}
			Fclose(fo);
	}	}
	inlut = incode = inspn = indfn = ingui = inltl = 0;

	fnm = (char *) e_malloc(strlen(bnm)+strlen(suffix1)+1);
	strcpy(fnm, bnm);
	strcat(fnm, suffix1);

	if (strcmp(suffix1, ".drv") == 0)
	{	if (!hasdrv)
		{	mkfo(fnm);
			fdrv = fo;
			hasdrv = 1;
			/* include global header file by default */
			fprintf(fdrv, "#include \"_modex_.h\"\n");
		} else
			fo = fdrv;
	} else
	{	mkfo(fnm);
	}
}

static int Argc = 1;
static char *Argv[128];	/* prepare argc and *argv[] for BldCmds */

void
Arg_Add(char *s, char *t)
{
	if (strlen(s) == 0) return;

	if (Verbose_cmds)
		printf("add arg %s %s\n", s, t);

	if (Argc >= 128)
	{	fprintf(stderr, "modex: too many arguments\n");
		exit(1);
	}
	Argv[Argc] = (char *) e_malloc(strlen(s)+strlen(t)+1);
	strcpy(Argv[Argc], s);
	strcat(Argv[Argc], t);

	if (Verbose_cmds)
		printf("	[%d] -> <%s>\n", Argc, Argv[Argc]);
	Argc++;
}

void
Add_Args(char *s)
{	char *t, *v;

	if (Verbose_cmds)
		printf("add args <%s>\n", s);

	for (t = v = s; *t; t++)
		if (*t == ' ' || *t == '\t')
		{	*t = '\0';
			Arg_Add(v, "");
			v = t+1;
			while (*v == ' ' || *v == '\t')
				v++;
			t = v;
		}
	Arg_Add(v, "");
}

int
no_explicits(void)
{
	return hasaction == 0 && strcmp(want, "main") == 0;
}

struct {
	char *descr; int *val;
} params[] = {
	{ "bfs:",	&bfs },
	{ "bfs_par:",	&bfs_par },
	{ "exhaustive:", &exhaustive },
	{ "loops:",	&loops },
	{ "maxdepth:",	&maxdepth },
	{ "memlim:",	&memlim },
	{ "noend:",	&noend },
	{ "noassert:",	&noassert },
	{ "np_loops:",	&np_loops },
	{ "quality:",	&quality },
	{ "shortest:",	&shortest },
	{ "vectorsz:",	&vectorsz },
	{ "zflag:",	&sysoverride },
	{ 0, 0 }
};

void
boiler_plate(FILE *fd, int pre)
{
	fprintf(fd, "\t\tif [ -f _modex_.drv ]\n");
	fprintf(fd, "\t\tthen	true\n");
	fprintf(fd, "\t\telse	echo \"error: no ./_modex_.drv file\"\n");
	fprintf(fd, "\t\t	exit 1\n");
	fprintf(fd, "\t\tfi\n\n");
	fprintf(fd, "\t\t%s model pan.? pan pan.exe _spin_nvr.tmp\n\n", RM);
	fprintf(fd, "\t\tif [ -f _modex_.h ]\n");
	fprintf(fd, "\t\tthen	true\n");
	fprintf(fd, "\t\telse	echo \"\" > _modex_.h\n");
	fprintf(fd, "\t\tfi\n\n");
	fprintf(fd, "\t\techo \"// Generated by %s\" > model\n", VERSION);
	fprintf(fd, "\t\techo \"// `date` from %s\" >> model\n", file_name);
	fprintf(fd, "\t\techo \"\" >> model\n");
	fprintf(fd, "\t\tif [ -f _modex_.b4g ]\n");
	fprintf(fd, "\t\tthen	cat _modex_.b4g >> model\n");
	fprintf(fd, "\t\tfi\n");
	fprintf(fd, "\t\t%s _modex_.drv | grep -v -e '^$' -e '^# ' >> model", CPP);
	if (pre)
	{	fprintf(fd, " 2>&1");
	}
	fprintf(fd, "\n");
}

void
mkruncmd(void)
{	FILE *fd;
	char buf[1024];
	char buf_w[32];

	if ((fd = fopen("_modex_.run", MFLAGS)) == NULL)
	{	fprintf(stderr, "modex: cannot create run cmd\n");
		return;
	}
if (debug_io) fprintf(stderr, "Open %s -> %p\n", "_modex_.run", fd);

	sprintf(buf, "%s -DVECTORSZ=%d -DMEMLIM=%d %s ", CC, vectorsz, memlim, optimized);

	if (exhaustive)
	{	quality = 10;
	}

	if (quality < 0)
	{	fprintf(stderr, "quality parameter must be 1..10, assuming 1\n");
		quality = 1;
	}
	if (quality > 10)
	{	fprintf(stderr, "quality parameter must be 1..10, assuming 10\n");
		quality = 10;
	}
	if (quality == 9)
	{	if (!bfs_par)
		{	strcat(buf, "-DHC4 ");
		}
	} else if (quality < 9)
	{	strcat(buf, "-DBITSTATE ");
	}

	if (bfs_par)
	{	strcat(buf, "-DBFS_PAR ");
	} else if (bfs)
	{	strcat(buf, "-DBFS ");
	}

	/* liveness */
	if (!loops && !np_loops)
	{	/* strcat(buf, "-DSAFETY "); */
		/* misses presence of ltl formula */
	} else if (np_loops)
	{	if (bfs_par || bfs)
		{	fprintf(stderr, "np_loops disabled by bfs%s\n", (bfs_par)?"_par":"");
		} else
		{	strcat(buf, "-DNP ");
	}	}

	/* shortest */
	if (shortest && !bfs && !bfs_par)
	{	strcat(buf, "-DREACH ");
	}

	strcat(buf, "-o pan pan.c");

	fprintf(fd, "## generated by %s\n## from %s\n\n", VERSION, file_name);
	if (0) fprintf(fd, "set -v\n");

	fprintf(fd, "r_flags=\"\"\n");
	fprintf(fd, "while [ $# -gt 0 ]\n");
	fprintf(fd, "do\n");
	fprintf(fd, "	case $1 in\n");
	fprintf(fd, "	\"-E\")\n");
	fprintf(fd, "		r_flags=\"$r_flags -E\"\n");
	fprintf(fd, "		shift\n");
	fprintf(fd, "		;;\n");
	fprintf(fd, "	\"-A\")\n");
	fprintf(fd, "		r_flags=\"$r_flags -A\"\n");
	fprintf(fd, "		shift\n");
	fprintf(fd, "		;;\n");
	fprintf(fd, "	\"-a\")\n");
	fprintf(fd, "		r_flags=\"$r_flags -a\"\n");
	fprintf(fd, "		shift\n");
	fprintf(fd, "		;;\n");
	fprintf(fd, "	*)\n");
	fprintf(fd, "		break\n");
	fprintf(fd, "		;;\n");
	fprintf(fd, "	esac\n");
	fprintf(fd, "done\n\n");

	fprintf(fd, "if [ $# -eq 1 ]\n");
	fprintf(fd, "then\n");
	fprintf(fd, "	case $1 in\n");
	fprintf(fd, "	pprep)\n");
				boiler_plate(fd, 1);
	fprintf(fd, "		exit 0	# preserve tmp files\n");
	fprintf(fd, "		;;\n");
	fprintf(fd, "	prep)\n");
				boiler_plate(fd, 0);
	fprintf(fd, "		if [ -f _modex_.cln ]\n");
	fprintf(fd, "		then %s _modex_.cln # cleanup\n", SH);
	fprintf(fd, "		fi\n");
	fprintf(fd, "		exit 0\n");
	fprintf(fd, "		;;\n");
	fprintf(fd, "	*)\n");
	fprintf(fd, "		if [ -f _modex_.cln ]\n");
	fprintf(fd, "		then	%s _modex_.cln # cleanup and run\n", SH);
	fprintf(fd, "		fi\n");
	fprintf(fd, "		;;\n");
	fprintf(fd, "	esac\n");
	fprintf(fd, "fi\n\n");

	fprintf(fd, "if [ -f model ]\n");
	fprintf(fd, "then	true\n");
	fprintf(fd, "else\n");
	fprintf(fd, "	echo \"no model file\"\n");
	fprintf(fd, "	exit 1\n");
	fprintf(fd, "fi\n");

	fprintf(fd, "if %s model && %s %s\n", SPIN,
		buf, lnkage_info?lnkage_info:"");
	fprintf(fd, "then\n\t");

	if (bfs || bfs_par)
	{	sprintf(buf, "./pan -n ");
	} else
	{	sprintf(buf, "./pan $r_flags -n -m%d ", maxdepth);
	}
#if 0
	int wmax = (int) log2( ((double)memlim / (double)vectorsz)*1024.*1024. );
	int wmin = (int) log2( ((double)memlim / (double)8)*1024.*1024. );
	fprintf(stderr, "w: %d .. %d (%d)\n", wmax, wmin, sizeof(long));
#endif

	if (quality >= 9)
	{	sprintf(buf_w, "-w%d ",
			(int) log2( ((double)memlim / (double)8)*1024.*1024. ) - 1);
	} else
	{	sprintf(buf_w, "-w%d ", 20+quality); /* 21 .. 28 */
	}
	strcat(buf, buf_w);

	if (np_loops)
		strcat(buf, "-l ");
	else if (loops)
		strcat(buf, "-a ");
	if (noend)
		strcat(buf, "-E ");
	if (noassert)
		strcat(buf, "-A ");
	if (shortest && !bfs && !bfs_par)
		strcat(buf, "-i ");
	if (strlen(runtime) > 0)	/* can override builtin options */
		strcat(buf, runtime);

	fprintf(fd, "%s\n", buf);

	fprintf(fd, "else\n");
	fprintf(fd, "	exit 1\n");

	fprintf(fd, "fi\n");
	fprintf(fd, "exit 0\n");
if (debug_io) fprintf(stderr, "close 4 %p\n", fd);
	Fclose(fd);
}

void
add_to_file(char *buf)
{	char *z;
	int i;

	if (fo && (inlut || incode || inspn || indfn))
	{	if (inspn && (z = strstr(buf, "\\#")) != NULL)
			*z = '\n';
		fprintf(fo, "%s\n", buf);
	} else if (ingui)
		for (i = 0; params[i].descr; i++)
		{	z = params[i].descr;
			if (!strncmp(buf, z, strlen(z)))
				*params[i].val = atoi(&buf[strlen(z)]);
		}
}

void
close_file(void)
{
	if (incode && !inltl)  fprintf(fo, "}\n");
	if (fo && fo != fdrv)
	{
if (debug_io) fprintf(stderr, "close 5 %p\n", fo);
		Fclose(fo);
	}
	fo = NULL;
	inlut = incode = inspn = inltl = 0;
}

void
check_param(char *cmd)		/* check for filename param */
{	FILE *fd;
	char buf[1024], *fnm;

	fnm = &cmd[2];
	while (*fnm == ' ' || *fnm == '\t')
		fnm++;

	if (!*fnm) return;	/* must be inline contents */

	if ((fd = fopen(fnm, "r")) == NULL)
	{	if (cmd[1] != 'L')
			fprintf(stderr, "modex: no such file %s\n", cmd);
		return;
	}
if (debug_io) fprintf(stderr, "Open %s -> %p\n", fnm, fd);

	while (fgets(buf, sizeof(buf), fd))
		add_to_file(buf);

if (debug_io) fprintf(stderr, "close 6 %p\n", fd);
	Fclose(fd);
	close_file();
}

void
add_sed(char *z)
{	char *n;
	int ln = strlen(z);
	if (strcmp(sedproc_info, "cat") == 0)
	{	n = (char *) e_malloc(ln + 1);
		strcpy(n, z);
	} else
	{	ln += strlen(sedproc_info) + strlen(" | ");
		n = (char *) e_malloc(ln + 1);
		sprintf(n, "%s | %s", sedproc_info, z);
	}
	sedproc_info = n;
}

void
checkprx(char *f)	/* pick up the arguments from a .prx file */
{	FILE *fd;
	char buf[2048];
	char *mnm, *z, *pz;

	if ((z = strstr(f, ".prx")) == NULL
	&&  (z = strstr(f, ".c")) == NULL)
		return;

	Argv[0] = "modex_prex";
	Arg_Add("-m", "");
	Arg_Add(modelname, "");
	Arg_Add("-L", "");
	Arg_Add(modelname, ".lut");

	*z = '\0';
	sprintf(buf, "%s.prx", f);
	*z = '.';	/* restore */
	if ((fd = fopen(buf, "r")) == NULL)	/* no .prx file */
	{	if (Verbose
		||  Verbose_cmds)
		{	fprintf(stderr, "modex: no prx file '%s', default rules apply\n", buf);
		}
		if (no_explicits())		/* no explicit extract command given */
		{	Arg_Add("-xe", "");	/* default model extraction of all fcts */
		}
		add_imported("_all_", "_all_", 2);	/* 1? */
		goto go_here;
	}

if (debug_io) fprintf(stderr, "Open %s -> %p\n", ".prx", fd);

	while (fgets(buf, sizeof(buf), fd))
	{
		if ((z = strstr(buf, "//")) != NULL)
		{	*z = '\0';	/* comment delimiter */
		}
		if (buf[0] == '\0')
		{	continue;
		}
		while (buf[strlen(buf)-1] == '\n'
		||     buf[strlen(buf)-1] == '\r'
		||     buf[strlen(buf)-1] == ' '
		||     buf[strlen(buf)-1] == '\t')
		{	buf[strlen(buf)-1] = '\0';
		}

		if (buf[0] != '\0' && buf[0] != '%')
			add_to_file(buf);
		else
		{	switch (buf[1]) {
			case 'A':	/* add something to the model text */
				header(modelname, ".ltl");
				incode = hasltl = inltl = 1;
				fprintf(fo, "/* added stuff */\n");
				break;
			case 'C':
				header(modelname, ".drv");
				incode = 1;
				fprintf(fo, "c_code {\n");
				break;
			case 'D':	/* after globals */
				header(modelname, ".drv");
				incode = 1;
				fprintf(fo, "c_decl {\n");
				break;
			case 'B':	/* before globals */
				header(modelname, ".b4g");
				incode = 1;
				fprintf(fo, "c_decl {\n");
				break;
			case 'F':
				Arg_Add("-b", "");
				z = &buf[2];
				while (*z == ' ' || *z == '\t')
					z++;
				Arg_Add(z, "");
				sawFile = 1;
				break;
			case 'G':	/* %GUI definitions */
				ingui = 1;
				close_file();
				break;
			case 'H':
				header(modelname, ".dfn");
				indfn = 1;
				break;
			case 'L':
				z = &buf[2];
				while (*z == ' ' || *z == '\t')
					z++;
				if (*z == '\0')
					mnm = modelname;
				else
				{	mnm = (char *) e_malloc(strlen(z)+1);
					strcpy(mnm, z);
				}
				header(mnm, ".lut");
				fprintf(fo, "# Modex %s\n", file_name);
				fprintf(fo, "%s for target <%s>\n", Banner, mnm);

				inlut  = 1;
				break;
			case 'N':
				pz = &buf[2];
				while (*pz == ' ' || *pz == '\t')
				{	pz++;
				}
				if (isdigit((int) *pz))
				{	nrprocs = atoi(pz);
				} else
				{	nrprocs = 1;
				}
				nrprocs_default = nrprocs;
				break;
			case 'O':
				z = &buf[2];
				while (*z == ' ' || *z == '\t')
					z++;
				lnkage_info = (char *) e_malloc(strlen(z)+1);
				strcpy(lnkage_info, z);
				break;
			case 'P':
				header(modelname, ".drv");
				haspml = inspn  = 1;
				break;
			case 'Q':
				z = &buf[2];
				while (*z == ' ' || *z == '\t')
					z++;
				preproc_info = (char *) e_malloc(strlen(z)+1);
				strcpy(preproc_info, z);
				break;
			case 'R':
				z = &buf[2];
				while (*z == ' ' || *z == '\t')
					z++;
				runtime = (char *) e_malloc(strlen(z)+2);
				strcpy(runtime, z);
				strcat(runtime, " ");
				break;
			case 'T':	// %T sed "s/replace/with/"
				z = &buf[2];
				while (*z == ' ' || *z == '\t')
					z++;
				add_sed(z);
				break;
			case '%':
				close_file();
				break;
			case 'X':
				hasaction = 1;
				Add_Args(&buf[2]);
				break;
			default:
				add_to_file(buf);
				break;
			}

			if (buf[1] == 'L' || buf[1] == 'H'
			||  buf[1] == 'D' || buf[1] == 'C'
			||  buf[1] == 'P')
				check_param(buf);
	}	}
if (debug_io) fprintf(stderr, "close A %p\n", fd);
	Fclose(fd);

go_here:
	mkruncmd();
	Arg_Add(file_name, "");
	if (!BldCmds(Argc, Argv))
	{	fprintf(stderr, "modex: checkprx: error in .prx file\n");
		exit(1);
	}
	if (no_explicits())
	{	new_cmd('x', "-xe", 10);
		add_imported("_all_", "_all_", 2);	/* 1? */
		if (Verbose_cmds)
		{	printf("modex: saw no explicit extraction commands -- assuming -xe\n");
	}	}

	if (fo && fo != fdrv)
	{
if (debug_io) fprintf(stderr, "close B %p\n", fo);
		Fclose(fo);
		fo = NULL;
	}
}

static int
newer(char *f1, char *f2)
{	struct stat x, y;

	if (stat(f1, (struct stat *)&x) < 0) return 0; /* no .c file */
	if (stat(f2, (struct stat *)&y) < 0) return 1; /* no .M file */
	if (x.st_mtime < y.st_mtime) return 0;
	
	return 1;
}

void
process_input(char *f, int phase2)
{	FILE *fp;
	char	cpp_file[512], *z, m[64];

	if (f && Verbose_cmds)
		printf("modex: process_input %s (phase %d)\n", f, phase2);

	if (!f || (z = strstr(f, ".c")) == NULL)
	{	fprintf(stderr, "modex: not a .c file <%s>\n", f);
		goto bad;
	}
	strcpy(cur_in, f);
	z++;
	*z = 'M';	/* preprocessor output */
	strcpy(cpp_file, f);
	*z = 'c';	/* restore */

	if (must_preprocess
	|| (fp = fopen(cpp_file, "r")) == NULL
	||  newer(f, cpp_file))		/* n.b. cannot see when included files change... */
	{	if (!must_preprocess
		&&  fp != NULL)
		{
if (debug_io) fprintf(stderr, "close 1 %p\n", fp);
			Fclose(fp);	/* .c newer than .M */
			fp = 0;
		}
		sprintf(m, "%s.dfn", modelname);

		modex_pp(f, m);	/* preprocessing - produce .M file */

		if ((fp = fopen(cpp_file, "r")) == NULL)
		{	fprintf(stderr, "modex: cannot open '%s'\n", cpp_file);
			goto bad;
	}	}
if (debug_io) fprintf(stderr, "Open %s -> %p\n", cpp_file, fp);

	init_nmetab();
	ParseStack = new_treestk();
	DoneStack  = new_treestk();
	contxt     = new_context();

	ParseStack->contxt = contxt;
	handle_new_file(ParseStack, fp, file_name);
	enter_scope(contxt);

	tree_parse(ParseStack, 0);			/* gram.y */

	name_scope(ParseStack->contxt, current_filename(), NONE_T);
	parse_tree = (top_of_stack(DoneStack))->parse_tree;

if (debug_io) fprintf(stderr, "close 2 %p - parsetree %p\n", fp, parse_tree);

	if (parse_tree)
	{	Fclose(fp);
		fp = 0;
		if (do_dflow)
			walk_tree(parse_tree, 0);	/* dflow.c */
	} else
	{	fprintf(stderr, "modex: no parsetree for %s\n", f);
		if (preview) unlink(cpp_file);
		phase2 = 1;	/* always exit */
		goto bad;
	}
	exit_scope(contxt);

	if (preview && !Verbose) unlink(cpp_file);

	return;
bad:
	if (phase2) exit(1);
}

int
main(int argc, char **argv)
{	FILE *fd;
	char cmd[256];

	context_t *o_ctx = NULL;

	file_name = "-";			/* default only */

	if (!BldCmds(argc,argv))		/* sets file_name */
	{	Usage(argv[0]);			/* command-line options */
	}

	printf("%s\n", VERSION);

	if ((!do_dflow || du_mode) && !preview && !predot)
	{	checkprx(file_name);		/* prx file options */
	} else
	{	new_cmd('x', "", 4);
	}

	if (!sawFile)				/* no %F command in prx file */
	{	char *z;
		if ((z = strstr(file_name, ".prx")) != NULL)
		{	z++; *z++ = 'c'; *z = '\0';	/* default .c */
			if ((fd = fopen(file_name, "r")) != NULL)
			{
if (debug_io) fprintf(stderr, "Open %s -> %p\n", file_name, fd);
				Fclose(fd);
				if (Verbose_cmds)
				{	printf("-- saw no %%F commands in prx file\n");
				}
				process_input(file_name, 0);
			} else
			{	printf("modex: warning: no file %s\n", file_name);
				exit(1);
			}
			*z-- = 'r'; *z = 'p';		/* restore */
	}	}

	strcpy(cur_in, file_name);

	if (strcmp(file_name, "-") != 0
	&&  strstr(file_name, ".prx") == NULL)
	{	process_input(file_name, 0);	/* parses file */
	}

	if (predot)
	{	dot_start(parse_tree);		/* ps_graph.c */
		exit(0);
	}

	/* model extraction functionality: */

	while (ActCmds())
	{	if (do_dflow && !du_mode)
		{	if (Verbose_cmds)
			fprintf(stdout, "/*** %s :: %s %s%s%s%s***/\n\n",
				file_name,
				parse_tree?parse_tree->hdr.fnm:"--",
				show_funcs?"+fcs ":"",
				show_syms?"+syms ":"",
				show_deps?"+deps ":"",
				show_code?"+code ":"");

			if (show_funcs)	show_fbase(stdout);
			if (show_syms)	show_symtab(contxt->syms, stdout);
			if (show_deps)	dep_show();
			if (show_code)  print_tree(parse_tree, stdout);
			fprintf(stdout, "\n");
			exit(0);
		} else
		{	if (0) fprintf(stderr, "Act %d %d -- %s\n", extended, flike, want);
			if (contxt)
			save_fcts(contxt->syms->root, stdout);
			modex_tree(parse_tree, lut);	/* xtract.c */

			// call do_globals here to avoid losing the info
			// if a different file is parsed next
			if (o_ctx != NULL && contxt != o_ctx && o_ctx->syms)
			{	do_globals(0, o_ctx->syms->root, 0);
			}
			o_ctx = contxt;
	}	}

	if (redundancies)
	{	notimported(stdout);
	}

	if (contxt && contxt->syms)
	{	do_globals(0, contxt->syms->root, 1);
	} else
	{	do_globals(0, (scopetab_t *) 0, 1);
	}

	if (!hasdrv || !haspml)
	{	header(modelname, ".drv");
		def_inc_spn(fdrv);
		if (hasltl) fprintf(fdrv, "#include \"_modex_.ltl\"\n");
	} else if (!anybody) /* added Oct 20, 2012 */
	{	def_inc_spn(fdrv);
		if (hasltl) fprintf(fdrv, "#include \"_modex_.ltl\"\n");
	}

	if (fdrv)
	{
if (debug_io) fprintf(stderr, "close C %p\n", fdrv);
		Fclose(fdrv);
	}

	if (Verbose || Warnings || Verbose_cmds || new_lut)
	{	add_fnm("_modex_.run");
	}

	spitnames(stderr);
	alldone();

	if (Verbose || Verbose_cmds || Warnings || new_lut)
	{	fprintf(stderr, "./_modex_.run pprep\n");
		sprintf(cmd, "%s _modex_.run pprep", SH);
		system(cmd); /* preserve temp files */
	} else
	{	sprintf(cmd, "%s _modex_.run prep", SH);
		if (system(cmd) != 0)
		{	fprintf(stderr, "modex: model creation failed\n");
		}
		if (tagrun)
		{	sprintf(cmd, "%s _modex_.run run", SH);
			system(cmd);
		} else
		{	printf("created: model and _modex_.run\n");
	}	}
	exit(0);
}

#if 0
typedef struct EX	EX;

struct EX {
	char	*f;
	EX	*nxt;
};
#endif
