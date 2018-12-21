/***** modex: nmetab.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/* Original version by Shawn Flisakowski, Jan 11, 1995 */

#ifndef     NMETAB_H
#define     NMETAB_H

#define MAX_HASH_BCKTS	1023

typedef struct string_str {
    unsigned int   hash;
    char          *str;
} str_t;

typedef struct hi {
    str_t      sym;
    struct hi *next;
} HashItem;

#define HASH_ITEM_SZE	(sizeof(HashItem))

extern HashItem  *NmeTab[MAX_HASH_BCKTS];

void   init_nmetab(void);
void   free_nmetab(void);
str_t *nmelook(char *sym, int len);
int    nmehash(str_t *sym);
void   nmeshow(void);
char  *nmestr(str_t *sym);

#endif    /* NMETAB_H */
