#! /usr/bin/env python
######################################################################
# create_printf.py
#
# Reads a filename.fields file as input.   
# The filename.fields file will specify the fields with their datatypes,
# and comments for each field.  Using this information it will
# generate 3 files.
#
# filenameOutput.h
# This script will generate a printf statement for all of the fields.
# Above the printf statement it will have doxygen style comments
# for each field.  
# This script will ignore anything in the fields file other than
# a field:: line.
#
# filenameVarDecl.h
# A list of extern variable declarations that the printf statement in
# filenameOutput.h will need.  These guys will be global variables.
#
# filenameVarInit.h
# A list of variable initializations that the printf statement in
# filenameOutput.h will need.  The character arrays just point at
# NULL. The integers and floats are set to 0.
#
#
# usage:      create_printf.py filename.fields
#
##### Example .fields file
#
#    # specify database info
#    database::mymc
#    hostname::localhost
#    username::root
#    password::something
#    portnum::3010
#    unix_socket_file::/home/mstrout/Temp/mysqld.3010
#
#    # specify new table name
#    table::practice
#
#    # field names and datatypes (float, int, or string)
#    # 1 field per line, order matters
#    field::version(string) ! a comment about this field
#    field::datadir(string) ! a comment about this field
#    field::maxiter(int)    ! a comment on all fields
#    field::residual(float) ! example of a float
#    field::cycles(ulong)   ! example of an unsigned long
# 
######################################################################
#import MySQLdb
import sys
import string

##### read in .fields file
if len(sys.argv) > 1:
    fieldsfilename = sys.argv[1]
else:
    print "usage: create_printf filename.fields\n"
    sys.exit(0)

fieldsfile = open(fieldsfilename)
filelines = fieldsfile.readlines()

# create the various output files
vardeclfilename = string.split(fieldsfilename,'.')[0] + "VarDecl.h"
varinitfilename = string.split(fieldsfilename,'.')[0] + "VarInit.h"
printffilename = string.split(fieldsfilename,'.')[0] + "Output.h"

vardeclfile = open(vardeclfilename,"w")
varinitfile = open(varinitfilename,"w")
printffile = open(printffilename,"w")


##### remove comment lines and blank lines
def notcomment(line):
    if (line[0] == '#') or (string.strip(line) == ''): return 0
    else: return 1
   
filelines = filter(notcomment,filelines)

##### field keyword
# for each field add some text to the comment string,
# the vardecl string, the varinit string,
# the format string, and the varlist string.
# start with an empty string and build up list of field defs
comment = \
    "    This file was automatically generated by calling " + \
    "\n        ../create_printf.py %s\n\n" % fieldsfilename

comment = comment + "<dl>\n";

vardecl = ''
varinit = ''

format = 'fprintf(%sOutfile, ' % string.split(fieldsfilename,'.')[0]

varlist = '",\n'


for line in filelines:
    if string.find(line,"field::") != -1:
        # first take off 'field::' then take off '(datatype)'
        tempstr = string.strip(string.split(line,"::")[1])
        fieldname = string.split(tempstr,'(')[0]
        # get datatype
        tempstr = string.split(tempstr,'(')[1]
        type = string.split(tempstr,')')[0]
        # get comment
        commentstr = string.split(tempstr,'!')[1]

        # determine C type
        if type == 'string':    
            Ctype = "char"
            initfieldname = fieldname + '[MAXLINESIZE] = ""'
            declfieldname = fieldname + '[MAXLINESIZE]'
            #initfieldname = '*' + fieldname + ' = NULL'
            #declfieldname = '*' + fieldname
            formatstr = "%s"
        elif type == 'float':   
            Ctype = "double"
            initfieldname = fieldname + "=0.0"
            declfieldname = fieldname
            formatstr = "%15.8e"
        elif type == 'ulong':   
            Ctype = "unsigned long"
            initfieldname = fieldname + "=0"
            declfieldname = fieldname
            formatstr = "%ld"
        else:                   
            Ctype = "int"
            initfieldname = fieldname + "=0"
            declfieldname = fieldname
            formatstr = "%d"

        # now add to comment string
        comment = comment + "    <dt>%s\n    <dd>%s\n" % (fieldname,commentstr)

        # next add to vardecl and varinit
        vardecl = vardecl + "extern %s    %s;\n" %(Ctype,declfieldname)
        varinit = varinit + "%s    %s;\n" %(Ctype,initfieldname)

        # next add to format string
        format = format + '\t\t\t"%s\\t"\n' % formatstr

        # finally add to var list
        varlist = varlist + "\t\t\t%s,\n" % fieldname

# finish up comment
comment = comment + "\n</dl>\n*/\n"

# take last tab off format string
format = format[:-4] + '\\n'

# take last comma off the varlist
varlist = varlist[:-2] + ');\n'

# write stuff to output files
vardeclfile.write('/* %s */\n' % vardeclfilename)
vardeclfile.write("/*! \\file\n    Comments for the variables this " \
    + "include file declares.\n\n")
vardeclfile.write(comment)
vardeclfile.write("#ifndef MAXLINESIZE\n#define MAXLINESIZE 256\n#endif\n")
vardeclfile.write(vardecl)

varinitfile.write('/* %s */\n' % varinitfilename)
varinitfile.write("/* see %s for comments on variables */\n" % vardeclfilename)
varinitfile.write("#ifndef MAXLINESIZE\n#define MAXLINESIZE 256\n#endif\n")
varinitfile.write(varinit)

printffile.write('/* %s */\n' % printffilename)
printffile.write("/*! \\file\n    Comments for the variables this " \
    + "printf statement expects to be defined.\n\n")
printffile.write(comment + format + varlist)