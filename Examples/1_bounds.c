#include <stdio.h>

// verify 1_bounds.c

#define N	5
#define M	4

int
main(void)
{	int i, q[M], *p[N][M];

	for (i = 0; i < N; i++)
		p[i][3] = &q[i];
}
