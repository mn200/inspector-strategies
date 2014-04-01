#! /usr/bin/env python
########################################################################
# create_run.py
#
# Will generate a run script which iterates over all the possible
# values of parameters to given executable and executables.
# Using "NONE" instead of an executable or list of executables
# indicates that just a list of command line parameters should be
# generated to the given outfilename.
#
# usage: create_run.py outfilename exec1,exec2,etc 
#                          param:start:end:by 'param(val1,val2)'
#        create_run.py outfilename NONE
#                          param:start:end:by 'param(val1,val2)'
#
# param:start:end:by - start and end are inclusive
#
# example: 	create_run.py run e1,e2 l:0:2:1 'b(a,b)'
#
# note: have to put quotes around b(a,b) because of parentheses
#
# results in run:  
# e1 -l 0 -b a
# e1 -l 1 -b a
# e1 -l 2 -b a
# e1 -l 0 -b b
# e1 -l 1 -b b
# e1 -l 2 -b b
# e2 -l 0 -b a
# e2 -l 1 -b a
# e2 -l 2 -b a
# e2 -l 0 -b b
# e2 -l 1 -b b
# e2 -l 2 -b b
########################################################################
import sys
import string

##### Read in command line parameters #######
usagestring = """
# usage: create_run.py outfilename exec1,exec2,etc 
#                          param:start:end:by 'param(val1,val2)'
#        create_run.py outfilename NONE
#                          param:start:end:by 'param(val1,val2)'
"""

# run script filename
if len(sys.argv) > 1:
	outfilename = sys.argv[1]
else:
	print "The the runscript filename must be specified"
	print usagestring
	sys.exit(0)

# executable names
if len(sys.argv) > 2:
	executables = string.split(sys.argv[2],',')
	if executables == ['NONE']:
		executables = ['']
else:
	print """The executable names must be specified 
		 	 or NONE to specify no executables.\n"""
	print usagestring
	sys.exit(0)

#### keep getting parameter value specifications
param_names = []
param_values = []
for index in range(3,len(sys.argv)):

	# if we have a range parameter specification, paramname:start:end:by
	if string.find(sys.argv[index],':') != -1:	
		spec = string.split(sys.argv[index],':')
		param_names.append(spec[0])
		start = string.atoi(spec[1])
		end = string.atoi(spec[2])
		by = string.atoi(spec[3])
		values = range(start,end+1,by)

	# if we have an element parameter specification, paramname(elem1,elem2,etc)
	else:
		spec = string.split(sys.argv[index],'(')
		param_names.append(spec[0])
		values = string.split(spec[1][:-1],',')
		
	# take values list generated above and
	# append each value of the current parameter onto
	# all the existing parameter lists, after this
	# operation there will be len(values)*len(param_values)
	# lists in param_values in other words 
	# len(param_values) <- len(values)*len(param_values)
	# example:
	#	if use theses l:0:2:1 'b(x,y)'
	#	after parsing l:0:2:1 param_values will be
	#	[[0], [1], [2]]
	#	after parsing 'b(x,y)' it will be
	#	[[0, 'x'], [1, 'x'], [2, 'x'], [0, 'y'], [1, 'y'], [2, 'y']]
	if len(param_values) == 0:	
		# if we haven't started param_values list already
		for x in values:
			param_values.append([x])
			
	else:
		# if there are values already in param_values
		new_param_values = []
		for x in values:
			for currlist in param_values:
				new_param_values.append(currlist+[x])

		param_values = new_param_values
	

#print param_names
#print param_values
		
#### Next I need to generate the execution command lines using the sets
#### of parameter values I constructed above

outfile = open(outfilename,"w")
		
for execfile in executables:
	for value_tuple in param_values:
		# write name of executable
		outfile.write(execfile)

		option_count = 0
		for option in param_names:
			outfile.write(" -%s %s" % (option,value_tuple[option_count]))
			option_count = option_count + 1

		# write out a newline
		outfile.write("\n")

	
