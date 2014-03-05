#! /usr/bin/env python
#################################################################
# create_rec.py
#
# usage: create_rec.py runname.fields runname.dat
#
# Creates a mysql database record using the runtime params and results
# which are in the .dat file.  The .fields file specifies the field
# names and their order in the MySQL database.  
#
# Any lines starting with a pound sign will be ignored as comments.
# The created record will be put into
# the specified mysql table and database (as specified in .fields).
#
##### see create_table.py for an Example fields file
#   
#################################################################
import sys
import string

############# just read in all lines, these files aren't that big

# read fields file
if len(sys.argv) > 1:
    fieldsfilename = sys.argv[1]
else:
    print "The .fields filename must be specified\n"
    sys.exit(0)

fieldsfile = open(fieldsfilename)
fieldslines = fieldsfile.readlines()

# read dat file
if len(sys.argv) > 2:
    datfilename = sys.argv[2]
else:
    print "The .dat filename must be specified\n"
    sys.exit(0)

datfile = open(datfilename)
datlines = datfile.readlines()

############################ first parse the fields file
#### remove comment lines and blank lines
def notcomment(line):
    if (line[0] == '#') or (string.strip(line) == ''): return 0
    else: return 1
    
fieldslines = filter(notcomment,fieldslines)

#### database keyword
for line in fieldslines:
    if string.find(line,"database::") != -1:
        database = string.strip(string.split(line,"::")[1])

#### host keyword
for line in fieldslines:
    if string.find(line,"host::") != -1:
        hostname = string.strip(string.split(line,"::")[1])

#### username keyword
for line in fieldslines:
    if string.find(line,"username::") != -1:
        username = string.strip(string.split(line,"::")[1])

#### password keyword
for line in fieldslines:
    if string.find(line,"password::") != -1:
        password = string.strip(string.split(line,"::")[1])

#### table keyword
for line in fieldslines:
    if string.find(line,"table::") != -1:
        table = string.strip(string.split(line,"::")[1])

##### portnum keyword
foundportnum = 0
for line in fieldslines:
    if string.find(line,"portnum::") != -1:
        portnum = string.atoi(string.split(line,"::")[1])
        foundportnum = 1

##### unix_socket_file keyword
for line in fieldslines:
    if string.find(line,"unix_socket_file::") != -1:
        unix_socket_file = string.strip(string.split(line,"::")[1])

#### field keyword, get all fields and their types and put into
#### a list called fieldorder
fieldorder = []
for line in fieldslines:
    if string.find(line,"field::") != -1:
        tempstr = string.strip(string.split(line,"::")[1])
        fieldorder.append(string.strip(string.split(tempstr,"!")[0]))
#print fieldorder

############################ Generate records

# first connect to database
import MySQLdb
if (foundportnum):
    DB = MySQLdb.connect(user=username,passwd=password, db=database, \
                         port=portnum,unix_socket=unix_socket_file)
else:
    DB = MySQLdb.connect(host=hostname,user=username,passwd=password, db=database)

DBC = DB.cursor()

dict = {}
# for each record in the .dat file
for line in datlines:

    # read values from dat file and insert into dict
    values = string.strip(line)
    values = string.split(line,'\t')
    #print "values= ", values
    i = 0
    for datfield in fieldorder:
        fieldname = string.split(datfield,'(')[0]
        #print "i=",i," fieldname=",fieldname,"values[i]=",values[i]
        dict[fieldname] = values[i]
        i = i+1

    # then create an insert string for each dat record
    insertstring = ''
    columnstring = ''
    for field in fieldorder:
        type = string.split(field,'(')[1]
        type = string.split(type,')')[0]
        fieldname = string.split(field,'(')[0]
        #print "fieldname=",fieldname," type=",type
    
        # do something different for the 3 different types
        # for now treating float and int the same
        if fieldname in dict.keys():
            columnstring = columnstring + ("%s," % fieldname)
            if type == 'string':    
                insertstring = insertstring + ("'%s'," % dict[fieldname])   
            else:
                insertstring = insertstring + ("%s," % dict[fieldname]) 

    
    # take off last comma
    insertstring = insertstring[:-1]
    columnstring = columnstring[:-1]
    #print "insert into %s (%s) values (%s)" % (table,columnstring,insertstring)
    DBC.execute("insert into %s (%s) values (%s)" % (table,columnstring,insertstring))

