/* fig. 9 */

typedef struct Msg Msg;
struct Msg {
	short seq;	/* sequence number  */
	char  *cont;	/* message contents */
};

int
abp_snd(Msg in)
{	Msg out;

	if (in.seq == out.seq)
	{
		if (!get_data(out.cont))	/* more data  */
			return 0;		/* we're done */
		out.seq = 1 - out.seq;		/* flip sequence number */
	}
	send(out);				/* send message */
	return 1;
}

void
abp_rcv(Msg in)
{	Msg out;
	int expect = 0;

	out.seq  = in.seq;
	out.cont = (char *) 0;
	send(out);				/* always acknowledge */
	if (in.seq == expect)
	{	put_data(in.cont);		/* accept data recvd */
		expect = 1 - expect;		/* flip sequence number */
	}
}
