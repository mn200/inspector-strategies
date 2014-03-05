#! /usr/bin/env python
######################################################################
# create_table.py
#
# Reads a .fields file as input.   The .fields file will specify the
# MySQL database that the new table should be put into.  Also the
# .fields file will specify the MySQL server host, username and 
# password, port and unix socket.  The port and unix socket do not
# need to be specified if using defaults.
# Finally, the .fields file will specify the table name 
# and fields with their datatypes.
#
# usage:      create_table.py filename.fields
#
##### Example .fields file
#
#    # specify database info
#    database::mymc
#    hostname::yeah.mcs.anl.gov
#    username::root
#    password::something
#
#    # specify new table name
#    table::practice
#
#    # field names and datatypes (float, int, ulong, or string)
#    # 1 field per line, order matters
#    field::version(string)     ! must have comments
#    field::datadir(string)     ! comment
#    field::maxiter(int)        ! comment
#    field::residual(float)     ! comment
#    field::cycles(ulong)       ! comment
# 
######################################################################
import MySQLdb
import sys
import string

##### Constants
varcharsize = 80

##### read in .fields file
if len(sys.argv) > 1:
    fieldsfilename = sys.argv[1]
else:
    print "The fields filename must be specified\n"
    sys.exit(0)

fieldsfile = open(fieldsfilename)
filelines = fieldsfile.readlines()

##### remove comment lines and blank lines
def notcomment(line):
    if (line[0] == '#') or (string.strip(line) == ''): return 0
    else: return 1
   
filelines = filter(notcomment,filelines)

##### database keyword
for line in filelines:
    if string.find(line,"database::") != -1:
        database = string.strip(string.split(line,"::")[1])

##### host keyword
for line in filelines:
    if string.find(line,"host::") != -1:
        hostname = string.strip(string.split(line,"::")[1])

##### username keyword
for line in filelines:
    if string.find(line,"username::") != -1:
        username = string.strip(string.split(line,"::")[1])

##### password keyword
for line in filelines:
    if string.find(line,"password::") != -1:
        password = string.strip(string.split(line,"::")[1])

##### table keyword
for line in filelines:
    if string.find(line,"table::") != -1:
        table = string.strip(string.split(line,"::")[1])

##### portnum keyword
foundportnum = 0
for line in filelines:
    if string.find(line,"portnum::") != -1:
        portnum = string.atoi(string.split(line,"::")[1])
        foundportnum = 1

##### unix_socket_file keyword
foundunix_socket_file = 0
for line in filelines:
    if string.find(line,"unix_socket_file::") != -1:
        unix_socket_file = string.strip(string.split(line,"::")[1])
        foundunix_socket_file = 1

##### field keyword
# start with an empty string and build up list of field defs
defstring = ''

for line in filelines:
    if string.find(line,"field::") != -1:
        # first take off 'field::' then take off '(datatype)'
        tempstr = string.strip(string.split(line,"::")[1])
        fieldname = string.split(tempstr,'(')[0]
        # get datatype in parenthesese
        type = string.split(tempstr,'(')[1]
        type = string.split(type,')')[0]

        # determine mysqltype
        if type == 'string':    mysqltype = "VARCHAR(%d)" % varcharsize
        elif type == 'float':   mysqltype = "FLOAT(8)"
        elif type == 'ulong':   mysqltype = "BIGINT"
        else:                   mysqltype = "INT"

        # now add to defstring
        defstring = defstring + (" %s %s, " % (fieldname,mysqltype))

# take last comma off the def string
defstring = defstring[:-2]

###########################################################
##### Connect to database and create table

if (foundportnum):
    DB = MySQLdb.connect(user=username,passwd=password, db=database, \
                         port=portnum,unix_socket=unix_socket_file) 
else:
    DB = MySQLdb.connect(host=hostname,user=username,passwd=password, db=database)
                      
DBC = DB.cursor()
DBC.execute("create table " + table + " ( " + defstring + " )" )
