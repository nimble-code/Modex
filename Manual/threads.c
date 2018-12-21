/* Fig.1 */
int shared = 0; int *ptr;

void
thread1(void)
{       int tmp;
        ptr = &shared;
        tmp = shared;
        tmp++;
        shared = tmp;
}

void
thread2(void)
{       int tmp;
        if (ptr)
        {       tmp = shared;
                tmp++;
                shared = tmp;
                assert(shared == 1);
        }
}
