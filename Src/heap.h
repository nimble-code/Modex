/***** modex: heap.h *****/

/* Copyright (c) 2000-2003 by Lucent Technologies - Bell Laboratories     */
/* All Rights Reserved.  This software is for educational purposes only.  */
/* Permission is given to distribute this code provided that this intro-  */
/* ductory message is not removed and no monies are exchanged.            */
/* No guarantee is expressed or implied by the distribution of this code. */
/* Software written by Gerard J. Holzmann based on the public domain      */
/* ANSI-C parser Ctree Version 0.14 from Shaun Flisakowski                */

/* Original version by Shawn Flisakowski, Apr 27, 1994 */

#ifndef max
#define max(a,b)	((a)>=(b)?(a):(b))
#endif

#ifndef    HEAP_H
#define    HEAP_H

#include "utype.h"

#define MIN_HUNK_ARRY	  8
#define DEFLT_RATIO	256

 /*  The following macros are machine-dependent.
     On many machines, a pointer is 4 bytes long,
     and 4-byte alignment suffices for most things.
     However, this is NOT true on an Alpha, where
     pointers are 8 bytes, and 8 byte alignment is
     the useful minimum.  Now that there are 64-bit
     MIPS, PowerPC, and SPARC systems as well as
     Alphas, we can no longer tolerate all-the-world's-a-VAX.
     We DO assume that all pointers are the same size;
     which is KNOWN to be false in several C systems.
     8 byte alignment will do no harm on 32-bit machines.
*/

#define PNTR_SZE	(sizeof (void *))
#define ALGN_SZE	(sizeof (double))
#define MIN_SZE		max(PNTR_SZE,ALGN_SZE)

typedef struct  hp_strt {
	uint    chnk_sze;
	uint    ch_ratio;

	uint    num_alloc;
	uint    num_free;
	uint    num_hunks;

	uint    hunk_array_sze;
	uint    next_chunk;

	void   *free_list;
	void  **hunks;
} Heap;

Heap *CreateHeap(uint, uint);
void  DestroyHeap(Heap *);
void *HeapAlloc_Gen(Heap *);
void *HeapAlloc(Heap *);
void  HeapFree(Heap *, void *);

#endif    /* HEAP_H  */
