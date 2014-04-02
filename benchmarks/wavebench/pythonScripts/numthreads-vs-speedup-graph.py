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

# Find the average original time for each sparse matrix and work amount.
baselines = {}
baselines = {}
for row in infile_dict_list:
    mat_work = (row['matrixfilename'],row['workPerIter'])
    if mat_work in baselines:
        baselines[mat_work].append( float(row['originalTime']) )
    else:
        baselines[mat_work] = [ float(row['originalTime']) ]

print baselines

# numpy.mean( numpy.array( list ) )




baseline_dict_avg = {}
baseline_dict_count = {}
for row in infile_dict_list:
    mat_work = (row['matrixfilename'],row['workPerIter'])
    if mat_work in baseline_dict_count:
        baseline_dict_avg[mat_work] = \
            (baseline_dict_avg[mat_work]*baseline_dict_count[mat_work] \
            + float(row['originalTime']) ) / (baseline_dict_count[mat_work]+1)
        baseline_dict_count[mat_work] += 1
    else:
        baseline_dict_avg[mat_work] = float(row['originalTime'])
        baseline_dict_count[mat_work] = 1

print baseline_dict_avg



