// some operating system dependencies
// used in system() calls in modex.c and xtract.c
// and in generated shell scripts _modex_.run, _modex_.cln

#ifndef CC	// compilation
	#define CC	"gcc -w -g"      // -DCC="cl /nologo"
#endif
#ifndef CPP	// preprocessing
	#define CPP	"gcc -E -x c" // -DCPP="cl /nologo /DMODEX /EP"
#endif
#ifndef RM
	#define RM	"rm -f"
#endif
#ifndef SPIN
	#define SPIN	"spin -a"
#endif
#ifndef SH
	#define SH	"sh"
#endif
#ifdef PC
	#define MFLAGS	"wb"
#else
	#define MFLAGS	"w"
#endif
