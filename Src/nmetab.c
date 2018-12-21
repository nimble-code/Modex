/***** modex: nmetab.c *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/* Original version by Shaun Flisakowski, Jan 11, 1995 */

#include    "globals.h"
#include    "lexer.h"
#include    "nmetab.h"

HashItem  *NmeTab[MAX_HASH_BCKTS];

extern void	*e_malloc(uint);
extern void	e_free(void *);

#if 0
int
nmehash( str_t *sym )
{
    if (sym)
      return sym->hash;
    else
      return 0;
}
#endif

char *
nmestr( str_t *sym )
{
    if (sym)
      return sym->str;
    else
      return NULL;
}

#if 0

unsigned int
calc_hash(char *str)	/* original version in ctree */
{	unsigned int hsh = 0;

	while (*str)
		hsh = (hsh << 1) ^ (hsh >> 20) ^ *str++;

	return hsh;
}

#else

#include <limits.h>
#define BITS_IN_int	( sizeof(int) * CHAR_BIT )
#define THREE_QUARTERS	((int) ((BITS_IN_int * 3) / 4))
#define ONE_EIGHTH	((int) (BITS_IN_int / 8))
#define HIGH_BITS	( ~((unsigned int)(~0) >> ONE_EIGHTH ))

unsigned int
calc_hash(char *str)	/* pjw's hash */
{	unsigned int hsh = 0, i;

	while (*str)
	{	hsh = (hsh << ONE_EIGHTH) + *str++;
		if ((i = hsh & HIGH_BITS) != 0)
			hsh = (hsh ^ ( i >> THREE_QUARTERS)) & ~HIGH_BITS;
	}
	return hsh;
}

#endif

void
init_nmetab(void)
{	int j;

	for (j = 0; j < MAX_HASH_BCKTS; j++)
		NmeTab[j] = (HashItem *) NULL;
}

#if 0
void
free_nmetab(void)
{	int j;
	HashItem  *hptr, *hfree;

    for (j=0; j < MAX_HASH_BCKTS; j++){

        hfree = (HashItem *) NULL;

        for (hptr=NmeTab[j]; hptr; hptr=hptr->next){
            if (hptr->sym.str)
                e_free(hptr->sym.str);
            if (hfree)
                e_free(hfree);
            hfree = hptr;
        }

        if (hfree)
            e_free(hfree);
    }
}
#endif

str_t *
nmelook(char *sym, int len)
{	HashItem *hptr;
	unsigned int hsh;
	int bckt;

	hsh  = calc_hash(sym);
	bckt = hsh % MAX_HASH_BCKTS;

	for (hptr=NmeTab[bckt]; hptr; hptr=hptr->next)
	{	if ((hptr->sym.hash == hsh)
		&&  (strcmp(sym, hptr->sym.str) == 0))
			return(&(hptr->sym));
	} 

	hptr = (HashItem *) e_malloc(HASH_ITEM_SZE);

	if (!len) len = strlen(sym);

	hptr->sym.str = e_malloc(len+1);
	hptr->sym.hash = hsh;
	strncpy(hptr->sym.str, sym, len);

	hptr->next = NmeTab[bckt];
	NmeTab[bckt] = hptr;

	return(&(hptr->sym));
}

#if 0
void
nmeshow(void)
{	int  j;
	HashItem *hptr;

    fprintf(stdout,"        Name Table\n");
    fprintf(stdout,"       ------------\n\n");

    for (j=0; j < MAX_HASH_BCKTS; j++){
    fprintf(stdout,"Examining bucket: %d\n", j);
        for (hptr=NmeTab[j]; hptr; hptr=hptr->next){
            fprintf(stdout,"Name: %s\n",hptr->sym.str);
        } 
    } 

    fputs("\n\n",stdout);
}
#endif
