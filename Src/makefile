#	(c) 2000-2012 Bell Labs, Lucent Technologies
#	Unix/Linux Makefile for MODEX,  a Model eXtractor for C code 
#	bug reports: gerard@spinroot.com
#
#	This makefile requires: gcc, bison, flex
#
#	Use the script make_pc to compile for a Windows PC
#
CC     = gcc # -Wall # -m32
CFLAGS = -g
CPPFLAGS =
# default values:
# CPPFLAGS = -UPC -DCPP=\"gcc -E\" -DDEFAULT_LUT=\"/usr/local/modex/defaults.lut\"
LD_LIBRARY_PATH=/usr/lib32:$LD_LIBRARY_PATH
BINDIR = /usr/local/bin

COMMON = heap.o nmetab.o symtab.o modex.o xtract.o \
	token.o tree.o treestk.o lexer.o gram.o dflow.o \
	prnttree.o modex_pp.o ps_graph.o

modex:	gram.h $(COMMON)
	$(CC) -o modex $(COMMON) -lm

install: modex
	cp modex $(BINDIR)
	mkdir -p /usr/local/modex
	cp defaults.lut /usr/local/modex

modex.o:	modex.c modex_cpp.h version.h utype.h globals.h lexer.h gram.h tree.h prnttree.h

modex_pp.o:	modex_pp.c dflow.h modex_cpp.h

dflow.o:	dflow.c dflow.h prnttree.h gram.h symtab.h

prnttree.o:	prnttree.c prnttree.h gram.h symtab.h

treestk.o:	treestk.c globals.h treestk.h

heap.o:		heap.c utype.h heap.h

nmetab.o:	nmetab.c globals.h lexer.h nmetab.h

xtract.o:	xtract.c prnttree.h gram.h symtab.h

symtab.o:	symtab.c utype.h symtab.h nmetab.h prnttree.h

token.o:	token.c gram.h

tree.o:		tree.c tree.h gram.h globals.h prnttree.h

ps_graph.o:	ps_graph.c gram.h prnttree.h symtab.h

lexer.c: lexer.l gram.h globals.h lexer.h nmetab.h symtab.h heap.h
	flex lexer.l
	mv lex.yy.c lexer.c

lexer.o: lexer.c

gram.o: gram.c

gram.c gram.h:	gram.y tree.h symtab.h globals.h
	bison -v -d gram.y
	mv gram.tab.c gram.c
	cp gram.tab.h gram.h

clean:
	rm -f gram.[ch] *.o lexer.c modex gram.output
