#include <pthread.h>
#include <limits.h>

// verify 5_incdec.c # uses 5_incdec.prx

#define uint	unsigned int

volatile uint value = 0;
volatile uint inc_flag = 0;
volatile uint dec_flag = 0;

uint
inc(void)
{	uint inc_v, inc_vn, inc_casret;

	do {
		inc_v = value;
		if (inc_v == UINT_MAX)
		{	return 0;	// fail, return min
		}
		inc_vn = inc_v + 1;
		cas(&value, inc_v, inc_vn, &inc_casret, &inc_flag);
	} while (inc_casret==0);

	assert(dec_flag || value > inc_v);

	return inc_vn;
}

uint
dec(void)
{	uint dec_v, dec_vn, dec_casret;

	do {
		dec_v = value;
		if (dec_v == 0)
		{	return UINT_MAX; // fail, return max
		}
		dec_vn = dec_v - 1;
		cas(&value, dec_v, dec_vn, &dec_casret, &dec_flag);
	}
	while (dec_casret==0);

	assert(inc_flag || value < dec_v);

	return dec_vn;
}

void *
thread(void *arg)
{	int r;

	r = rand();

	if (r)
	{	inc();
	} else
	{	dec();
	}

	return 0;
}

int
main(void)
{	pthread_t t;

	while(1) {
		pthread_create(&t, 0, thread, 0);
	}
	exit(0);
}
