#include <pthread.h>
#include <assert.h>

//  verify 4_mutex.c
// or
//  modex -xe2 -run 4_mutex.c; verify replay

pthread_t x, y, z;
int cnt;

void
lock(pthread_t Pid)
{
busywait:
	x = Pid;
	if (y != 0 && !pthread_equal(Pid, y))
		goto busywait;

	z = Pid;
	if (!pthread_equal(x, Pid))
		goto busywait;

	y = Pid;
	if (!pthread_equal(z, Pid))
		goto busywait;
}

void
unlock()
{
	x = 0;
	y = 0;
	z = 0;
}

void *
thread(void *arg)
{
	lock(pthread_self());
	cnt++;
	assert(cnt == 1);
	cnt--;
	unlock();
}

int
main(void)
{	pthread_t t[2];

        pthread_create(&t[0], 0, thread, 0);
        pthread_create(&t[1], 0, thread, 0);

	pthread_join(t[0], 0);
	pthread_join(t[1], 0);

	return 0;
}
