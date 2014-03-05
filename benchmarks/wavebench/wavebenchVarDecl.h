/* wavebenchVarDecl.h */
/*! \file
    Comments for the variables this include file declares.

    This file was automatically generated by calling 
        ../create_printf.py wavebench.fields

<dl>
    <dt>datadir
    <dd> parent directory for matrix dir
    <dt>matrixfilename
    <dd> matrix filename
    <dt>outfilename
    <dd> name of output file to append records
    <dt>workPerIter
    <dd> number of exp
    <dt>inspectorStr
    <dd> which inspector implementation to use
    <dt>computername
    <dd> computer which we are running on
    <dt>datetime
    <dd> date time stamp
    <dt>N
    <dd> number of rows and columns in the matrix
    <dt>numwave
    <dd> number of waves found
    <dt>avgIterPerWave
    <dd> average number of iterations per wavefront
    <dt>minIterPerWave
    <dd> minimum number of iterations per wavefront
    <dt>maxIterPerWave
    <dd> maximum number of iterations per wavefront
    <dt>stddevIterPerWave
    <dd> standard deviation of iterations per wavefront
    <dt>originalTime
    <dd> time to execute original loop
    <dt>inspectorTime
    <dd> time to execute inspector in seconds
    <dt>executorTime
    <dd> time to execute executor in seconds

</dl>
*/
#ifndef MAXLINESIZE
#define MAXLINESIZE 256
#endif
extern char    datadir[MAXLINESIZE];
extern char    matrixfilename[MAXLINESIZE];
extern char    outfilename[MAXLINESIZE];
extern int    workPerIter;
extern char    inspectorStr[MAXLINESIZE];
extern char    computername[MAXLINESIZE];
extern char    datetime[MAXLINESIZE];
extern int    N;
extern int    numwave;
extern double    avgIterPerWave;
extern double    minIterPerWave;
extern double    maxIterPerWave;
extern double    stddevIterPerWave;
extern double    originalTime;
extern double    inspectorTime;
extern double    executorTime;
