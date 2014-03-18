# Makefile for creating wavebench executable

UTIL_CPP_FILES = util/CmdParams.cpp util/timer.cpp util/COO_mat.cpp util/mmio.cpp
                 
UTIL_H_FILES = util/CmdParams.h util/timer.h util/COO_mat.h util/mmio.h

wavebench: wavebench-driver.cpp ${UTIL_CPP_FILES} ${UTIL_H_FILES}
	g++-mp-4.7 -O3 -fopenmp wavebench-driver.cpp ${UTIL_CPP_FILES} -o wavebench
#	g++ -O3 wavebench-driver.cpp ${UTIL_CPP_FILES} -o wavebench

clean:
	-/bin/rm -rf *.o wavebench wavebench.dSYM 2> /dev/null
