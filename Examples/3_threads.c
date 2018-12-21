#include <pthread.h>
#include <assert.h>

// verify 3_threads.c

int shared = 0;
int *ptr;

void *
thread1(void *arg)
{	int tmp;

	ptr = &shared;
	tmp = shared;
	tmp++;
	shared = tmp;
	return 0;
}

void *
thread2(void *arg)
{	int tmp;

	if (ptr)
	{	tmp = shared;
		tmp++;
		shared = tmp;
	}
	return 0;
}

int
main(void)
{	pthread_t t[2];

	pthread_create(&t[0], 0, thread1, 0);
	pthread_create(&t[1], 0, thread2, 0);

	pthread_join(t[0], 0);
	pthread_join(t[1], 0);

	assert(shared == 2);

	return 0;
}
