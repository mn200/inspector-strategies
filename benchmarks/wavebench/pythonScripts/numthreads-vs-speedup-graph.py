#! /usr/bin/env python
#################################################################
# numthreads-vs-speedup-graph.py
#
# usage: ./numthreads-vs-speedup-graph.py runname.dat
#
# Prints to standard out a tab-delimited table that can be read into
# excel:
#       numthreads  mat1-work1-speedup  mat1-work2-speedup  ...
#       1           1.0                 1.0     ...
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
import numpy

infile = open('opt1-li-fwd500.dat','r')

# Read the datafile in as a list of dictionaries with keys
# being the field names in the first row of the file.
infile_dict_list = csv.DictReader(infile,delimiter='\t')

# List of original times for each sparse matrix and work amount.
# Also lists of inspector and executor times.
baselines = {}
inspectortimes = {}
executortimes = {}
for row in infile_dict_list:
    mat_work = (row['matrixfilename'],int(row['workPerIter']))
    
    # baselines indexed by (matrix,work)
    if mat_work in baselines:
        baselines[mat_work].append( float(row['originalTime']) )
    else:
        baselines[mat_work] = [ float(row['originalTime']) ]
        
    # inspector and executor times indexed by numthreads,
    # and then (matrix,work)
    numthreads = int(row['numthreads'])
    if numthreads in inspectortimes and mat_work in inspectortimes[numthreads]:
        inspectortimes[numthreads][mat_work].append(float(row['inspectorTime']))
        executortimes[numthreads][mat_work].append(float(row['executorTime']))
    elif numthreads in inspectortimes:
        inspectortimes[numthreads][mat_work] = [float(row['inspectorTime'])]
        executortimes[numthreads][mat_work] = [float(row['executorTime'])]
    else:
        inspectortimes[numthreads] = {}
        inspectortimes[numthreads][mat_work] = [float(row['inspectorTime'])]
        executortimes[numthreads] = {}
        executortimes[numthreads][mat_work] = [float(row['executorTime'])]

# calculate statistics
import sys
for numthreads in sorted(executortimes.iterkeys()):
    sys.stdout.write(str(numthreads))  # avoiding newline
    for (mat,work) in sorted(executortimes[numthreads].iterkeys()):
        timelist = executortimes[numthreads][(mat,work)]
        sys.stdout.write("\t" + str(numpy.mean(numpy.array(timelist))))
    sys.stdout.write("\n")






