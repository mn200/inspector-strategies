/*! \file
  \authors Nick Mitchell and Michelle Strout
  \version $Id: timer.h,v 1.2 2005/06/02 21:15:15 mstrout Exp $

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

/* timer returns microseconds */
#ifndef _TIMER_H
#define _TIMER_H

#include <sys/time.h>
#include <time.h>
#include <locale.h>
#include <stdio.h>

double _timer();

typedef struct {
        double start;
        double end;
} TIMER;


void timer_start( TIMER * aTimer );

void timer_end( TIMER * aTimer );

double timer_numsecs( TIMER * aTimer );

double timer_numcycles( TIMER * aTimer, unsigned int speed );

double timer_cycles_per_iter( TIMER * aTimer, unsigned int speed,
	long iters );

/* Got from man strftime page */
void  my_strftime(char* nowstr, int SLENGTH);

#endif
