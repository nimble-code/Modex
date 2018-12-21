// verify 2_pointers.c

void
main(void)
{	int x=12, y=34, z, w;
	int *p,*q,*i,*j,*k;
	int *****a;

	p = &z;
	q = &x;
	x = 56;
	*p = *q;
	i = p;
	p = &y;
	****a = i;
	j = ****a;
	i = q;
}
