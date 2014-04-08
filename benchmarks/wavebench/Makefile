# Makefile for creating wavebench executable

CCFLAGS = -O3 -fopenmp

ifeq ($(OSTYPE),darwin)
    CC = g++-mp-4.7
else
    ifeq ($(HOSTNAME),tg-login1.blacklight.psc.teragrid.org)
        CC = icpc
        CCFLAGS = -O3 -g -openmp -openmp-report2
    else
        CC = g++
    endif
endif

#CCFLAGS = -O3 -fopenmp \
#    -I/Users/mstrout/package/IntelPerformanceCounterMonitorV2.6


# wavebench specific files
H_FILES = CmdParams.h timer.h COO_mat.h mmio.h
CPP_FILES = CmdParams.cpp timer.cpp COO_mat.cpp mmio.cpp wavebench-driver.cpp
OBJS = CmdParams.o timer.o COO_mat.o mmio.o wavebench-driver.o

%.o : %.cpp
	$(CC) -c $(CCFLAGS) $< -o $@

wavebench: $(H_FILES) $(OBJS)
	$(CC) $(CCFLAGS) $(OBJS) -o wavebench

# not sure why have to break this out but do on blacklight
# maybe because of hyphen?
#wavebench-driver.o: wavebench-driver.cpp
#	${CC} -c $(CCFLAGS) $< -o $@


clean:
	-/bin/rm -rf *.o wavebench wavebench.dSYM 2> /dev/null
