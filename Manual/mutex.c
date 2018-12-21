/* Fig 4. Bad Mutex Algorithm */

int x, y;

int
lock(int Pid)
{
	x = Pid;
	if (y != 0 && y != Pid)
		return 0;/* fail */
	y = Pid;
	if (x != Pid)
		return 0;/* fail */
	return 1;/* success */
}

void
unlock(void)
{	x = 0;
	y = 0;/* reset */
}

/* add: test routine */

int count;

void
user(int Pid)
{
	while (1)
	{	lock(Pid);
		count++;
		assert(count == 1);
		count--;
		unlock();
	}
}
