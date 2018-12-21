/* fig. 9 */

typedef struct Msg Msg;
struct Msg {
	short seq;	/* sequence number  */
	char  *cont;	/* message contents */
};

void
abp_sender()
{	Msg m, ack;

	m.seq = 0;
	ack.seq = 0;

	for (;;)
	{	if (ack.seq == m.seq)
		{	if (fetch_data(&m.cont))
			{	m.seq = 1 - m.seq;
			} else
			{	break;	/* no more data: done */
		}	}
		send(m);
		receive(&ack);
	}
}

void
abp_receiver()
{	Msg m, ack;
	short expect = 1;

	for (;;)
	{	receive(&m);	/* get new msg */
		ack.seq  = m.seq;
		send(ack);
		if (m.seq == expect)
		{	store_data(m.cont);
			expect = 1 - expect;
	}	}
}
