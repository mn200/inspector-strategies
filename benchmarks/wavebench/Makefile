# Makefile for creating wavebench executable

ifeq ($(OSTYPE),darwin)
	CC = g++-mp-4.7
else
    CC = g++
endif

#CCFLAGS = -O3 -fopenmp \
#    -I/Users/mstrout/package/IntelPerformanceCounterMonitorV2.6
CCFLAGS = -O0 -g -fopenmp

# wavebench specific files

UTIL_H_FILES = CmdParams.h timer.h COO_mat.h mmio.h
UTIL_CPP_FILES = CmdParams.cpp timer.cpp COO_mat.cpp mmio.cpp
UTIL_OBJS = CmdParams.o timer.o COO_mat.o mmio.o

wavebench: wavebench-driver.o ${UTIL_CPP_FILES} ${UTIL_H_FILES} ${UTIL_OBJS}
	${CC} ${CCFLAGS} wavebench-driver.o ${UTIL_OBJS} -o wavebench

%.o : %.cpp %.h
	${CC} -c ${CCFLAGS} $< -o $@


clean:
	-/bin/rm -rf *.o wavebench wavebench.dSYM 2> /dev/null
