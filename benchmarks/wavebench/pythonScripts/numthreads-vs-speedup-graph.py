#! /usr/bin/env python
#################################################################
# numthreads-vs-speedup-graph.py
#
# usage: ./numthreads-vs-speedup-graph.py runname.dat
#
# Prints to standard out a tab-delimited table that can be read into
# excel:
#       mat,work    1       2       4       8
#       mat1-0      speedup
#       mat1-1      ...
#       ...
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

# List of original times for each sparse matrix and work amount.
# Also lists of inspector and executor times.
baselines = {}
inspectortimes = {}
executortimes = {}
last_mat_work = ("init",0)
for row in infile_dict_list:
    mat_work = (row['matrixfilename'],int(row['workPerIter']))
    last_mat_work = mat_work
    
    # baselines indexed by (matrix,work)
    if mat_work in baselines:
        baselines[mat_work].append( float(row['originalTime']) )
    else:
        baselines[mat_work] = [ float(row['originalTime']) ]
        
    # inspector and executor times indexed by numthreads,
    # and then (matrix,work)
    numthreads = int(row['numthreads'])
    
    if  mat_work in inspectortimes and numthreads in inspectortimes[mat_work]:
        inspectortimes[mat_work][numthreads].append(float(row['inspectorTime']))
        executortimes[mat_work][numthreads].append(float(row['executorTime']))
    elif mat_work in inspectortimes:
        inspectortimes[mat_work][numthreads] = [float(row['inspectorTime'])]
        executortimes[mat_work][numthreads] = [float(row['executorTime'])]
    else:
        inspectortimes[mat_work] = {}
        inspectortimes[mat_work][numthreads] = [float(row['inspectorTime'])]
        executortimes[mat_work] = {}
        executortimes[mat_work][numthreads] = [float(row['executorTime'])]

# calculate statistics and print out table for excel
import sys
import numpy
# print num threads headers
sys.stdout.write("mat,work")
for numthreads in sorted(executortimes[last_mat_work].iterkeys()):
    sys.stdout.write("\t" + str(numthreads))
sys.stdout.write("\n")
# print numthreads and then speedup for each matrix, work combo
for (mat,work) in sorted(executortimes.iterkeys()):
    sys.stdout.write(mat + "," + str(work))
    for numthreads in sorted(executortimes[(mat,work)].iterkeys()):
        timelist = executortimes[(mat,work)][numthreads]
        avg = numpy.mean(numpy.array(timelist))
        baseline_avg = numpy.mean(numpy.array(baselines[(mat,work)]))
        sys.stdout.write("\t" + str( baseline_avg/avg ))
    sys.stdout.write("\n")






