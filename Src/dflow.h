/***** modex: dflow.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#ifndef DFLOW
#define DFLOW

typedef struct SymList	SymList;
typedef struct DefUse	DefUse;
typedef struct DuG	DuG;
typedef struct DuGP	DuGP;

struct SymList {
	int	selected;
	int	mark;
	struct symentry *sm;
	SymList	*nxt;
	SymList *all;
};

struct DefUse {
	int	special;	/* for override markings */
	SymList	*def;
	SymList	*use;
	SymList *other;
};

struct DuG {		/* variable dependency graph */
	struct	symentry *sm;	/* ptr to symbol table */
	int	marks;		/* decl, def, use, hide info */
	int	rdcls;		/* set inside or outside procedure */
	DuGP	*d_e;	/* llist of outgoing edges */
	DuG	*nxt;	/* llist of all nodes */
};

struct DuGP {
	DuG	*ptr;
	int	dist;		/* distance in dependency chain */
	DuGP	*nxt;
};

/* dataflow tags used in dflow.c: */

#define DEF		1
#define FCALL		(1<<1)		/*    2 */
#define USE		(1<<2)		/*    4 */
#define REF0		(1<<3)		/*    8 */
#define REF1		(1<<4)		/*   16 */
#define REF2		(1<<5)		/*   32 */
#define DEREF		(1<<6)		/*   64 */
#define ALIAS		(1<<7)		/*  128 */
#define ARRAY_DECL	(1<<8)		/*  256 */
#define HIDE		(1<<9)		/*  512 */
#define DECL		(1<<10)		/* 1024 */
#define USEafterdef	(1<<11)		/* 2048 */
#define USEbeforedef	(1<<12)		/* 4096 */
#define PARAM		(1<<13)		/* 8192 */
#define ANY		((1<<14)-1)

#endif
