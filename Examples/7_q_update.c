#include <pthread.h>
#include <assert.h>

//  verify -p -E 7_q_update.c # using embedded printfs
// or:
//  modex -run 7_q_update.c; verify replay
//
// illustrates importing a data structure
// and defining an atomic function (cas)
// both are done with a .prx file

typedef struct Entry Entry;

struct Entry {
	Entry	*next;
	Entry	*temp;	/* used during insertion */
	Entry	*tail;	/* used when it's queue head */
	int	value;
};

Entry head;
Entry *nil = (Entry *) 0;

void *
rtl_put(void *arg)
{	Entry *q, *new, *prev, sample[4];
	int val, x;

	q = &head;

	for (val = 0; val < 2; val++)
	{	new = &sample[val];
		new->value = val+1;

		do {
			new->next = nil;
			prev = q->tail;
			prev->temp = new;
			x = cas(&q->tail, prev, new);
		} while (x == 0);

		prev->next = new;
	}
}

void *
rtl_get(void *arg)
{	Entry *q, *next, *e;
	int val1 = 0;
	int val2 = 0;
	int x;

	q = &head;
again:
	do {
		next = q->next;
		if (next == nil)
			goto again;
		e = next->next;

		x = cas(&q->next, next, e);

	} while (x == 0);

	if (q->next == nil && e == 0)
	{	x = cas(&q->tail, next, q);
		if (x == 0)
		{	cas(&next->next, nil, next->temp);
			next->temp = 0;
			q->next = next->next;
	}	}
done:
	assert(next->value == val1 + 1 || next->value == val2 + 1);
	if (next->value == val1 + 1)
		val1++;
	else
		val2++;
	goto again;
}

int
main(void)
{	pthread_t a, b, c;

	head.tail = &head;	// initialize

	pthread_create(&a, 0, rtl_put, 0);
	pthread_create(&b, 0, rtl_put, 0);
	pthread_create(&c, 0, rtl_get, 0);

	return 0;
}
