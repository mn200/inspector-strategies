/*! \file
  \authors Nick Mitchell and Michelle Strout
  \version $Id: timer.c,v 1.2 2005/06/02 21:15:15 mstrout Exp $

  Copyright ((c)) 2004, University of Chicago
  Copyright ((c)) 2001-2003, The Regents of the University of California
  All rights reserved.
  See ../COPYING for copyright details.

	These functions are written in C and not C++ to reduce overhead.

	TIMER mytimer;

	timer_start(&mytimer);
	timer_end(&mytimer);
	secs = timer_numsecs(&mytimer);	

	// speed should be in MHz
	num = timer_numcycles(&mytimer,speed);
	cycles_iter = timer_cycles_per_iter(&mytimer,speed,iters);
	
	// other general things, got moved to exp_util.h
	my_strftime(char* str,int MAXSIZE); // str=Thu Feb 11 10:44:48 1999
*/
#include "timer.h"

/* _timer returns microseconds */
double timer_()
{
  double retval;
  struct timeval tv;
  struct timezone tz;//void *ptr;
  
  gettimeofday (&tv, &tz);
  retval = (double)tv.tv_sec + (double)tv.tv_usec/1.0E6;
  return retval;
} /* timer_ */

void timer_start( TIMER * aTimer )
{
	aTimer->start = timer_();
}

void timer_end( TIMER * aTimer )
{
	aTimer->end = timer_();
}

double timer_numsecs( TIMER * aTimer )
{
	return (aTimer->end - aTimer->start);
}

double timer_numcycles( TIMER * aTimer, unsigned int speed )
{
	return timer_numsecs(aTimer)*(double)speed*(double)1.0E6;
}

double timer_cycles_per_iter( TIMER * aTimer, unsigned int speed,
	long iters )
{
	return timer_numcycles(aTimer,speed)/(double)iters;
}

/* Got from man strftime page */
void  my_strftime(char* nowstr, int SLENGTH)
{
	time_t nowbin;
	const struct tm *nowstruct;

	(void)setlocale(LC_ALL, "");

	if (time(&nowbin) == (time_t) - 1)
		printf("Could not get time of day from time()\n");

	nowstruct = localtime(&nowbin);
	/* "%A %x" */
	if (strftime(nowstr, SLENGTH, "%c", nowstruct) == (size_t) 0)
		printf("Could not get string from strftime()\n");

	/*printf("Today's date is %s\n", nowstr);*/
}
