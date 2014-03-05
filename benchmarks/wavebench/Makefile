# Makefile for creating wavebench executable

wavebench: wavebench-driver.cpp CmdParams.h CmdParams.cpp
	g++ -O0 -g -Wno-write-strings wavebench-driver.cpp CmdParams.cpp -o wavebench


clean:
	-/bin/rm *.o wavebench 2> /dev/null
