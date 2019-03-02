/***** modex: prnttree.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/* Original version by Shawn Flisakowski, March 27, 1995 */

#ifndef PRNTREEH
#define PRNTREEH

#include <stdio.h>
#include "tree.h"

void  fputs_metachr(char c, int in_str);
void  fputs_metastr(char *str);
char *print_ptr(void *ptr);
void  print_tree(treenode*, FILE *);
void  modex_leaf(leafnode*, int tabs);
void  modex_tree(treenode*, char *);

#endif
