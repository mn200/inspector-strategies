#################################################################
# util.py
#
# Various functions which most of the report, graph, and table
# scripts use.
#
# usage: 
#   import util
#   util.GetDictListFromTable
#
#################################################################
import sys
import os
import string
import MySQLdb
from types import *
#import numpart

subdir = 'GraphData/'

#################################################################
def tuple2ValDict(tuple):

# Returns a dictionary based on the tuple of pairs.
# Oppisite of valDict2Tuple
#################################################################
    valDict = {}
    for pair in tuple:
        valDict[pair[0]] = pair[1]
    return valDict


#################################################################
def valDict2Tuple(valDict, fieldlist):

# Returns a tuple with a tuple of tuples based on the given 
# dictionary and an ordered list of the keys in the dictionary.
# For example, if valDict = {'bye': 'good', 'hello': 3}
# and fieldlist = ["bye","hello"] then this function
# returns (('bye', 'good'), ('hello', 3))
# 
# example usage:
#   valTuple = valDict2Tuple(valDict,fieldlist)
#
# input:
#   valDict - dictionary
#   fieldlist - key names in dictionary separated by commas
#
#################################################################
    tmplist = []
    for key in fieldlist:
        tmplist.append((key,valDict[key]))
    return tuple(tmplist)


#################################################################
def getDictListFromTable(dbcursor, fieldnamestring):

# Returns a list of dictionaries.  One dictionary for each record in
# the results that dbcursor is pointing at.
# Only call this after doing a select.
# The fieldnamestring should be the list of fields that were given to
# the select statement which generated dbcursor.
# 
# example usage:
#   dbcursor.execute("select %s from Table1" % (fieldnamestring))
#   recList = getDictListFromTable(dbcursor,fieldnamestring)
#
# input:
#   dbcursor - mySQL database cursor
#   fieldnamestring - field names separated by commas
#
#################################################################
    dictlist = []
    fieldnames = string.split(fieldnamestring,',')
    rec_count=0
    for rec in dbcursor.fetchall():
        dictlist.append( {} )   # empty dictionary
        field_count=0
        for fname in fieldnames:
            dictlist[rec_count]["%s" % (fname)] = rec[field_count]
            field_count = field_count+1
        rec_count = rec_count+1
    return dictlist


#################################################################
def notcomment(line):

# Returns 0 if line is a comment or a blank line, returns 1
# if the line isn't a comment or a blank line
# usage: filelines = filter(notcomment,filelines)
#################################################################
    if (line[0] == '#') or (string.strip(line) == ''): return 0
    else: return 1



#################################################################
def parseKeyword(keyword,linelist):

# returns list of strings which comes after
# keyword:: in the set of lines, will return a list of strings
# which follow all instances of keyword:: in the list of lines
#################################################################
    retlist = []
    # first remove comment lines
    linelist = filter(notcomment,linelist)

    # then look at each line for the given keyword
    for line in linelist:
        if string.find(line,"%s::" % keyword) != -1:
            retlist.append(string.strip(string.split(line,"::")[1]))
    return retlist

#################################################################
def getDictFromFile(infile,keywordstring):

# Returns a dictionary containing a list of values for each instance
# of the keywords in the keywordstring.
#
# input:
#   infile - file handle
#   keywordstring - field names separated by commas
#################################################################
    retdict = {}
    keywords = string.split(keywordstring,',')
    filelines = infile.readlines()
    for keyword in keywords:
        retdict['%s' % keyword] = parseKeyword(keyword,filelines)

    return retdict

#################################################################
def parseMainfieldValues(mainfieldList):

# Returns a dictionary with an entry for each
# mainfield::fieldname::values and the entry is the list of values
# that mainfield can take on if the mainfield can take on all
# values it has an empty list?
#
# input:
#   mainfieldList - each item in the list is of the form
#       "fieldname:values".
#
# returns:
#   dictionary with fields as keys and
#   values being the list of values each field can have
#################################################################
    retdict = {}
    for line in mainfieldList:
        # get mainfield name
        line = string.strip(line)
        #print "line=",line
        name = string.split(line,':')[0]
        # get values list
        values = string.split(string.split(line,':')[1]) 

        # if all values are allowed then don't need to make a list
        if values[0] == 'ALL':
            continue
        # if the first element in the values list is ALL
        # then do a search in the database for all values
        # which the field takes on
            #values = []
            #c.execute("select %s from %s" % (name,maintable))

            #valdict = getDict(c,"%s" % name,maintable)

            #for rec in valdict:
            #    if rec['%s.%s' % (maintable,name)] not in values: 
            #        values.append(rec['%s.%s' % (maintable,name)])

        # assign the list of values to the name
        retdict[name] = values

    return retdict

#################################################################
def createWhereClause(fieldValuesDict):

# Returns a dictionary with an entry for each
# mainfield::fieldname::values and the entry is the list of values
# that mainfield can take on if the mainfield can take on all
# values it has an empty list?
#
# input:
#   fieldValuesDict - dictionary with fields as keys and
#   values being the list of values each field can have
#
# example:
# if use 
#   mainfield::T:2 3
#   mainfield::N:10 20 30
# then "WHERE (T==2 or T==3) and (N==10 or N==20 or N==30)"
#################################################################
    whereclause = ''
    for name in fieldValuesDict.keys():
        whereclause = whereclause + '('
        for value in fieldValuesDict[name]:
            if type(value) is LongType:       
                whereclause = whereclause + " %s=%d " % (name,value) + "or"
            else:
                whereclause = whereclause + " %s=%s " % (name,value) + "or"
        # take off last or
        whereclause = whereclause[:-2] + ') and '

    # take off last and
    whereclause = whereclause[:-5]

    return whereclause


#################################################################
def createFileName(prefix,fieldList,recDict,suffix):

# Returns a string filename using the given prefix and suffix.
# In the middle will be fieldnamevalue_ pairs.
#
# input:
#   prefix - string prefix for file name
#   fieldList - list of fields
#   recDict - the dictionary for a record, should have a value for all
#       of the fields in the fieldList
#   suffix - string suffix for file name
#################################################################
    filename = prefix
    for name in fieldList:
        value = recDict["%s" % (name)]
        if (type(value) is LongType) or (type(value) is IntType):       
            filename = filename + name
            filename = filename + "%d_" % value
        else:
            filename = filename + "%s_" % value
    # take off last underscore
    filename = filename[:-1] + suffix
    return filename

#################################################################
def getAllVals(dbc,tablename,field):

# Returns a list of values that the field has in the given table and 
# database.
#
# input:
#   dbc - database cursor
#   field - fieldname
#################################################################
    values = []
    dbc.execute("select %s from %s" % (field,tablename))

    valdict = getDictListFromTable(dbc,"%s" % field)

    for rec in valdict:
        if rec['%s' % (field)] not in values: 
            values.append(rec['%s' % (field)])

    return values

#################################################################
def cartesianProduct(listOfSets):

#  "The collection of all ordered n-tuples that can be formed so 
#  that they contain one element of the first set, one element 
#  of the second,..., and one element of the n-th set."
#
# Returns a list of lists which have the n-tuples described above. 
# The listOfSets is really a list of lists where each list has
# represents one of our sets.
#
# input:
#   listOfSets - list of lists
#
# example
#   input: [[0,1,2],['x','y']]
#	output: [[0, 'x'], [1, 'x'], [2, 'x'], [0, 'y'], [1, 'y'], [2, 'y']]
#
#################################################################
    # starts out with just one empty list in the list
    Ntuples = [[]]

    # puts entries from each set onto the end of existing Ntuples    
    for eachset in listOfSets:
        new_Ntuples = []
        for value in eachset:
            for eachtuple in Ntuples:
                new_Ntuples.append(eachtuple+[value])

        Ntuples = new_Ntuples

    return Ntuples

