# Makefile for creating wavebench executable

ifeq ($(OSTYPE),darwin)
	CC = g++-mp-4.7
else
    CC = g++
endif


UTIL_CPP_FILES = util/CmdParams.cpp util/timer.cpp util/COO_mat.cpp util/mmio.cpp
                 
UTIL_H_FILES = util/CmdParams.h util/timer.h util/COO_mat.h util/mmio.h

wavebench: wavebench-driver.cpp ${UTIL_CPP_FILES} ${UTIL_H_FILES}
	${CC} -O3 -fopenmp wavebench-driver.cpp ${UTIL_CPP_FILES} -o wavebench
#	g++-mp-4.7 -O3 -fopenmp wavebench-driver.cpp ${UTIL_CPP_FILES} -o wavebench

clean:
	-/bin/rm -rf *.o wavebench wavebench.dSYM 2> /dev/null
