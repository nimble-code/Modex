/***** modex: globals.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

#ifndef GLOBALSH
#define GLOBALSH

#include    <stdio.h>
#include    <string.h>
#include    <stdlib.h>
#include    <assert.h>
#include    <errno.h>

#include    "heap.h"
#include    "treestk.h"

#ifdef DEFINE_GLOBALS
	#define   EXT_DEF
	#define   EXT_INIT(VarDef,Init)    VarDef = Init
#else
	#define   EXT_DEF                  extern
	#define   EXT_INIT(VarDef,Init)    extern VarDef
#endif

EXT_DEF char *file_name;
EXT_INIT(TreeStack *ParseStack, NULL);
EXT_INIT(Stk_Item *Parse_TOS, NULL);
EXT_INIT(TreeStack *DoneStack, NULL);    /* Parse trees for included files */

#undef EXT_DEF
#undef EXT_INIT

#endif
