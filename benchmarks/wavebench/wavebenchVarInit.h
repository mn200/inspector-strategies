/* wavebenchVarInit.h */
/* see wavebenchVarDecl.h for comments on variables */
#ifndef MAXLINESIZE
#define MAXLINESIZE 256
#endif
char    datadir[MAXLINESIZE] = "";
char    matrixfilename[MAXLINESIZE] = "";
char    outfilename[MAXLINESIZE] = "";
int    workPerIter=0;
char    inspectorStr[MAXLINESIZE] = "";
char    computername[MAXLINESIZE] = "";
char    datetime[MAXLINESIZE] = "";
int    numthreads=0;
int    N=0;
int    nnz=0;
int    numwave=0;
double    avgIterPerWave=0.0;
double    stddevIterPerWave=0.0;
int    minIterPerWave=0;
int    maxIterPerWave=0;
double    originalTime=0.0;
double    inspectorTime=0.0;
double    executorTime=0.0;
