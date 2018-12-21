#if 0
	Hands On: C/C++ Programming and Unix Application Design: 
	UNIX System Calls and Subroutines using C, Motif, C++ 
	
	Copyright © 1993-1997, Nikos Drakos,
	Computer Based Learning Unit, University of Leeds. 
	
	Dave Marshall 1/5/1999 http://www.cs.cf.ac.uk/Dave/C/node32.html
	
	Deadlock 
	This example demonstrates how a deadlock can occur in
	multithreaded programs that use synchronization variables.
	In this example a thread is created that continually adds
	a value to a global variable. The thread uses a mutex
	lock to protect the global data. 
	
	The main thread creates the counter thread and then loops,
	waiting for user input. When the user presses the Return key,
	the main thread suspends the counter thread and then prints
	the value of the global variable. The main thread prints
	the value of the global variable under the protection of
	a mutex lock. 
	
	The problem arises in this example when the main thread
	suspends the counter thread while the counter thread is
	holding the mutex lock. After the main thread suspends
	the counter thread, it tries to lock the mutex variable.
	Since the mutex variable is already held by the counter
	thread, which is suspended, the main thread deadlocks. 
	
	This example may run fine for a while, as long as the
	counter thread just happens to be suspended when it is
	not holding the mutex lock. The example demonstrates how
	tricky some programming issues can be when you deal
	with threads.

	This example uses non-Posix threads, and features that
	are not supported in a standard thread model (e.g., thr_suspend)
	Modex can handle this example with overrides in a .prx file.
#endif

// verify 6_suspend.c # uses 6_suspend.prx

#include <stdio.h>
#include <thread.h>

int count;
mutex_t count_lock;

void *
counter(void *arg)
{	int i;
	
	while (1) {
	        printf("."); fflush(stdout);
	
	        mutex_lock(&count_lock);
	        count++;
	
	        for (i=0;i<50000;i++);
	
	        mutex_unlock(&count_lock);
	
	        for (i=0;i<50000;i++);
	}
	
	return((void *)0);
}

main()
{	char str[80];
	thread_t ctid;

	/* create the thread counter subroutine */
	thr_create(NULL, 0, counter, 0, THR_NEW_LWP|THR_DETACHED, &ctid);

	while(1) {
	        gets(str);
	        thr_suspend(ctid);
	
	        mutex_lock(&count_lock);
	        printf("\n\nCOUNT = %d\n\n", count);
	        mutex_unlock(&count_lock);
	
	        thr_continue(ctid);
        }

	return(0);
}
