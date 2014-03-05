/*!
 * \file wavebench-driver.cpp
 *
 * \brief Driver for synthetic wavebench microbenchmark.
 *
 * wavebench reads in a square, sparse matrix in mmx format (-f filename)
 * and uses that sparse matrix to provide the doacross loop dependence pattern
 * in a synthetic loop with a specified number of exp() calls to dial
 * the amount of work per iteration (-w #).  If there is a non-zero at location 
 * A_{ij} in the sparse matrix and i<j, then there is a dependence between 
 * iteration i and j (i must execute before j).  If the amount of work is set
 * to zero, then no exp() calls will occur but 2 multiplications and 2 adds will
 * occur each iteration.
 *
 *
 * Pseudocode, sum should converge to 1.4(?) as w increases
 *      foreach non-zero A_{ij} in sparse matrix:
 *          sum = Sum_{k=0}^{w-1} 1 / exp( data[i] * data[j] )
 *          data[ i ] += data[i]*data[j] + sum;
 *                       
 *          data[ j ] += data[i]*data[j] + sum; 
 *
 * The loop has reduction dependencies.  Race conditions have to be
 * avoided between two iterations that share a dependence, but they
 * could be reordered.  The wavefront inspectors we investigate in
 * this driver, treat all of the dependences between iterations in this
 * loop as creating a partial ordering between i and j where A_{i,j}
 * is a non-zero in the sparse matrix and i<j.
 *
 * \date Started: March 5, 2014
 *
 * \authors Michelle Strout
 *
 * Copyright (c) 2014, Colorado State University <br>
 * All rights reserved. <br>
 */
#include <stdlib.h>
#include "util/CmdParams.h"
#include "util/COO_mat.h"
#include "util/timer.h"

// Useful global flags
bool debug = false;
bool verify = true;

// Variable declarations from fields file.
#include "wavebenchVarDecl.h"
#include "wavebenchVarInit.h"

// wave.fields:
//      Inspector types and default inspector type.
typedef enum {
    naive_inspector,
    Rauchwerger95_inspector,
    Zhuang09_inspector
} inspector_type;
inspector_type inspectorChoice = naive_inspector;
#define num_IPairs 3
static EnumStringPair IPairs[] = {{naive_inspector,"pipelined_4x4x4"},
                        {Rauchwerger95_inspector,"Rauchwerger95_inspector"},
                        {Zhuang09_inspector,"Zhuang09_inspector"}
                };

//*** function prototypes for command line parsing ***
//*** defined at the bottom of this file
void initParams(CmdParams *cmdparams);
void getParamValues(CmdParams *cmdparams);
void fullFilePath(char *returnStr,char * path,char * filename);

//*** function prototypes for utilities
//*** defined at the bottom of this file
void verify_results(int N, double *data_org, double *data);


//============================================== Inspectors
// Want to move each of these into separate file.


/*--------------------------------------------------------------*//*!
  Naive Inspector
*//*--------------------------------------------------------------*/


//============================================== Driver


int main(int argc, char ** argv) {
    TIMER original_timer;
    TIMER inspector_timer;
    TIMER executor_timer;

    // Do command-line parsing.
    CmdParams *cmdparams = CmdParams_ctor(1);
    initParams(cmdparams);
    CmdParams_parseParams(cmdparams,argc,argv);
    getParamValues(cmdparams);

    // Load the matrix from the specified file
    COO_mat *mat;
    char matrix_file_path[MAXLINESIZE] = "";
    fullFilePath(matrix_file_path,datadir,matrixfilename);
    printf("==== Loading MM sparse matrix %s ====\n",matrix_file_path);
    mat=COO_mat_load_from_MM(matrix_file_path);

    // initialize the data vectors
    printf("==== Creating data_org and data vectors ====\n");
    double* data_org=(double*)malloc(sizeof(double)*(mat->nrows));
    double* data=(double*)malloc(sizeof(double)*(mat->nrows));
    for(int i=0; i<mat->nrows; i++) {
      data_org[i] = data[i]=i;
    }

    // Query information about the sparse matrix.
    double *val = mat->val; // nnz values in COO matrix representation
    int *row    = mat->row; // nnz rows in COO matrix representation
    int *col    = mat->col; // nnz rows in COO matrix representation
    int nnz     = mat->nnz; // number of nonzeros
    if (mat->nrows != mat->ncols) assert(0);// only dealing with square matrices
    // wavebench.fields var N
    N = mat->nrows;

    // Original Computation
    timer_start(&original_timer);
    /* 
 *      foreach non-zero A_{ij} in sparse matrix:
 *          sum = Sum_{k=0}^{w-1} 1 / exp( data[i] * data[j] )
 *          data[ i ] += data[i]*data[j] + sum;
 *                       
 *          data[ j ] += data[i]*data[j] + sum; 
*/
    timer_end(&original_timer);    

    // One of the wavefront inspectors
    timer_start(&inspector_timer);    
    timer_end(&inspector_timer);    

    // The wavefront executor
    timer_start(&executor_timer);    
    timer_end(&executor_timer);    

    // Verify the above computation by comparing original with 
    // wavefront executor results.
    verify_results(N, data_org, data);

    // Compute wavebench.fields results of this run.
    // The other fields are initialized when command
    // line parameters are read.
    // numwave is initialized by the inspector.
    gethostname(computername, MAXLINESIZE);
    my_strftime(datetime, MAXLINESIZE);
    N = mat->nrows;
//    avgIterPerWave = compute_avg( wave );
//    minIterPerWave = compute_min( wave );
//    maxIterPerWave = compute_max( wave );
//    stddevIterPerWave = compute_stddev( wave );
    originalTime = timer_numsecs(&original_timer);
    inspectorTime = timer_numsecs(&inspector_timer);
    executorTime = timer_numsecs(&executor_timer);
    
    // printf statement for wavebench.fields
    FILE * wavebenchOutfile = fopen(outfilename,"a");
    #include "wavebenchOutput.h"  

    // Clean up after the computation (deallocate memory, etc.)
    CmdParams_dtor(&cmdparams);
    COO_mat_dtor(&mat);
    free(data);
    free(data_org);
    
    return 0;
}

//==============================================


void initParams(CmdParams* cmdparams)
/*--------------------------------------------------------------*//*!
  Uses a CmdParams object to describe all of the command line
  parameters, see wavebench.fields.

  \author Michelle Strout 3/5/14
*//*--------------------------------------------------------------*/
{

    CmdParams_describeNumParam(cmdparams,(char*)"workPerIter", 'w', 1,
        (char*)"number of exp() calls per iteration of loop",
        0, 10000, 1);  // default value is 1

    CmdParams_describeStringParam(cmdparams,(char*)"datadir", 'd', 1,
            (char*)"directory where sparse matrix files can be found",
            (char*)".");

    CmdParams_describeStringParam(cmdparams,(char*)"matrixfilename", 'm', 1,
            (char*)"filename for sparse matrix (in MM format)",
            (char*)"small_test_5x5.mm");

    CmdParams_describeStringParam(cmdparams,(char*)"outfilename", 'o', 1,
            (char*)"name for output file",
            (char*)"wavebench.dat");

    CmdParams_describeEnumParam(cmdparams, (char*)"inspectorChoice", 'i', 1,
            "wavefront inspector",
            IPairs, num_IPairs, naive_inspector);

}

void getParamValues(CmdParams *cmdparams)
/*--------------------------------------------------------------*//*!
  Uses the given CmdParams object to load all of the command line
  parameters, see wavebench.fields.

  \author Michelle Strout 3/5/14
*//*--------------------------------------------------------------*/
{

    strncpy(datadir, CmdParams_getString(cmdparams,'d'), MAXLINESIZE);
    
    strncpy(matrixfilename, CmdParams_getString(cmdparams,'m'), MAXLINESIZE);

    strncpy(outfilename, CmdParams_getString(cmdparams,'m'), MAXLINESIZE);

    workPerIter = CmdParams_getValue(cmdparams,'w');

    inspectorChoice = (inspector_type)CmdParams_getValue(cmdparams,'i');
    strncpy(inspectorStr, (char*)CmdParams_getString(cmdparams,'i'),
            MAXLINESIZE);

}

void fullFilePath( char *returnStr, char * path, char * filename)
/*------------------------------------------------------------*//*!
  Concatenate the path to the filename and return the result.
  Puts result in returnStr.  Does not change path or
  filename strings.

  input:
  \param  returnStr path/filename will be in this string upon return
  \param  path      path to find the file
  \param  filename  input file

  \author Michelle Strout 10/26/02
*//*--------------------------------------------------------------*/
{
    strcpy(returnStr,path);
    strcat(returnStr,"/");
    strcat(returnStr,filename);
}

void verify_results(int N, double *data_org, double *data)
/*--------------------------------------------------------------*//*!
  Compares the data array generated by the original code
  with the data generated by the executor.  Should be equal.
*//*--------------------------------------------------------------*/
{
    printf("==== Running verification wavefront computation ====\n");
    int i;
    double diff,diffsum;

    diffsum=0.0;
    for(i=0;i<N;i++) {
        diff=abs(data_org[i]-data[i]);
        diffsum+=diff;

        // if have more than 0.1% diff, then print an error message
        if((diff/data_org[i])>0.001) {
            printf("diff over 0.1%%, i=%d, diff = %lf, "
                   "data_org= %lf, data=%lf\n",
                  i, diff, data_org[i], data[i]);
        }
    }
    printf("verify: diffsum = %lf\n", diffsum);
        
}
