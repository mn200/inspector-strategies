#! /usr/bin/env python
#################################################################
# matrix-and-numwavefronts.py
#
# usage: ./numthreads-vs-speedup-graph.py runname.dat
#
# Prints to standard out a tab-delimited table that can be read into
# excel:
#       matrix  numrows nnz memfootprint    numwaves    avgperwavemin   max min
#       ...                 8*nnz + 8*numrows
#
# Assumptions
#     Field names are at top of .dat file, but could just take in
#     a .fields file and use some of the utilities I already wrote?
#     Looked at that, but don't really have utilities I want.
#     Easier to start out with field names at the top of .dat file
#     and just use csv library.  FIXME: Later will want to read in .dat file
#     and fields and concatenate them into an input file for .csv
#     to avoid this step.
#   
#################################################################

import csv
import sys

# read dat file
if len(sys.argv) > 1:
    datfilename = sys.argv[1]
else:
    print "The .dat filename must be specified\n"
    sys.exit(0)

infile = open(datfilename,'r')


# Read the datafile in as a list of dictionaries with keys
# being the field names in the first row of the file.
infile_dict_list = csv.DictReader(infile,delimiter='\t')

sys.stdout.write("matrix\tnumrows\tnnz\t")
sys.stdout.write("memfootprint\tnumwaves\tavgperwave\tstddev\tmin\tmax\n")

# print out matrix info and number of iterations per wave info
matrixinfo = {}
for row in infile_dict_list:
    if not(row['matrixfilename'] in matrixinfo):
        matrixinfo[row['matrixfilename']] = row
        
for matrix in sorted(matrixinfo.iterkeys()):
    row = matrixinfo[matrix]
    sys.stdout.write(row['matrixfilename'])
    sys.stdout.write("\t"+row['N'])
    sys.stdout.write("\t"+row['nnz'])
    memfootprint = float(8*( int(row['N']) + int(row['nnz']) ))/float(1024*1024)
    sys.stdout.write("\t"+str(memfootprint))
    sys.stdout.write("\t"+row['numwave'])
    sys.stdout.write("\t"+row['avgIterPerWave'])
    sys.stdout.write("\t"+row['stddevIterPerWave'])
    sys.stdout.write("\t"+row['minIterPerWave'])
    sys.stdout.write("\t"+row['maxIterPerWave'])

    sys.stdout.write("\n")






