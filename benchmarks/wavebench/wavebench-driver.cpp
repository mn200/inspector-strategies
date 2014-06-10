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
 * to zero, then no exp() calls will occur but 2 adds will occur each iteration.
 *
 * Pseudocode, 
 *      foreach non-zero A_{ij} in sparse matrix:
 *          sum = Sum_{k=0}^{w-1} 1 / exp( k*data[i]*data[j] )
 *          data[ i ] += 1.0 + sum                     
 *          data[ j ] += 1.0 + sum
 *
 * Let nnz[v] be the number of non-zeros A_{vw} or A{wv}.  Essentially the
 * number of nonzeros were v is the column or the row.  The value of each 
 * data[v] will be less than (nnz[v] + nnz[v]*1.58).
 * Here is why:
 *  Ratio test: lim_{n->inf} abs(a_{n+1}/a_n) < 1
 * 
 *  Sum_{x to inf} 1/exp(x) converges because r = (1/exp(x+1)) / (1/exp(x)) 
 *     = exp(x)/exp(x+1) = exp(x)/exp(x)*exp(1) = 1/e < 1
 *     Since r is a constant, we have a geometric sequence that converges to
 *     1/(1-r), which in this case is 1/(1-1/e) = e/(e-1) = 1.58.
 *
 *  The above value "sum" is 
 *      Sum_{x to inf} 1/exp(x*y*z), where 1<=y and 1<=z
 *      a_{n+1} / a_n = exp(n*y*z)/exp((n+1)*y*z) = 1/exp(y*z)
 *  As n goes to infinity, the ratio is 1/exp(y*z), which is less than 1.
 *  It is at most 1/e, so the summation converges to 1.58.
 *
 * \date Started: March 5, 2014
 *
 * \authors Michelle Strout
 *
 * Copyright (c) 2014, Colorado State University <br>
 * All rights reserved. <br>
 */
#include <stdlib.h>
#include <math.h>
//#include <cpucounters.h>  // For Intel Performance Counter Monitor

#include "CmdParams.h"
#include "COO_mat.h"
#include "timer.h"

#define MAX(x,y) ((x)>(y)?(x):(y))

// Useful global flags
bool debug = false;
bool diff = true;

// Variable declarations from fields file.
#include "wavebenchVarDecl.h"
#include "wavebenchVarInit.h"

// wave.fields:
//      Inspector types and default inspector type.
typedef enum {
    byhandfast_inspector,
    fast_inspector,
    Rauchwerger95_inspector,
    Zhuang09_inspector
} inspector_type;
inspector_type inspectorChoice = byhandfast_inspector;
#define num_IPairs 4
static EnumStringPair IPairs[] = 
                        {{byhandfast_inspector,"byhandfast_inspector"},
                         {fast_inspector,"fast_inspector"},
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
void diff_results(int N, double *data_org, double *data);


//================================= Generated Inspectors and Executors
#include "PIESgen.c"

/*
void find_waves_fast_gen(COO_mat *mat, int nnz, int * row, int *col,
                          int *max_wave_ptr, int **wavestart_ptr, 
                          int **wavefronts_ptr)
{
    int max_wave = 0;
    int* wavestart=(int*)calloc((max_wave+2),sizeof(int));
    int *wavefronts=(int*)malloc(sizeof(int)*nnz);
    

    // epilogue to capture outputs
    (*max_wave_ptr) = max_wave;
    (*wavestart_ptr) = wavestart;
    (*wavefronts_ptr) = wavefronts;
}

void rauchwerger95(COO_mat *mat, int nnz, int * row, int *col,
                          int *max_wave_ptr, int **wavestart_ptr, 
                          int **wavefronts_ptr)
{
    int max_wave = 0;
    int* wavestart=(int*)calloc((max_wave+2),sizeof(int));
    int *wavefronts=(int*)malloc(sizeof(int)*nnz);
    

    // epilogue to capture outputs
    (*max_wave_ptr) = max_wave;
    (*wavestart_ptr) = wavestart;
    (*wavefronts_ptr) = wavefronts;
}

void zhuang09(COO_mat *mat, int nnz, int * row, int *col,
                          int *max_wave_ptr, int **wavestart_ptr, 
                          int **wavefronts_ptr)
{
    int max_wave = 0;
    int* wavestart=(int*)calloc((max_wave+2),sizeof(int));
    int *wavefronts=(int*)malloc(sizeof(int)*nnz);
    

    // epilogue to capture outputs
    (*max_wave_ptr) = max_wave;
    (*wavestart_ptr) = wavestart;
    (*wavefronts_ptr) = wavefronts;
}
*/


/*--------------------------------------------------------------*//*!
  byhandfast_inspector: Efficient, Handwritten Serial Inspector
*//*--------------------------------------------------------------*/
void find_waves_fast(COO_mat *mat, int nnz, int * row, int *col,
                          int *max_wave_ptr, int **wavestart_ptr, 
                          int **wavefronts_ptr)
{
    //===== find_waves_fast variant, see 3/17/14 in SPFproofs-log.txt
    // see 5/14/14 for optimizations, combining mallocs hurt perf on Mac
    
    // need lw_iter and lr_iter for each element in data array
    int* lw_iter=(int*)malloc(sizeof(int)*(mat->nrows));
    int* lr_iter=(int*)malloc(sizeof(int)*(mat->nrows));
    // initializing them all to -1 to represent bottom (no iter has R or W yet)
    for (int i=0; i<mat->nrows; i++) { lw_iter[i] = -1; lr_iter[i] = -1; }
    // initialize all iteration wavefronts to 0
    int* wave=(int*)malloc(sizeof(int)*nnz);
    for (int i=0; i<nnz; i++) { wave[i] = 0; }
    // will keep a count per wave, max number of waves is number of iterations
    int max_wave = 0;
    
    // Iterating over iterations and how those iterations access data
    // the read and write access relations have been hardcoded here
    // for wavebench computation.
    // One optimization included here is a count of how many iterations
    // are put into each wave.
    // p=0 will always be in wave 0 and its lr_iter and lw_iter will
    // be taken care of when p=1.
    for (int p=1; p<nnz; p++) {
        // last iteration read and wrote row[p-1] and col[p-1]
        lr_iter[row[p-1]] = p-1;
        lr_iter[col[p-1]] = p-1;
        lw_iter[row[p-1]] = p-1;
        lw_iter[col[p-1]] = p-1;

        // reading and writing to indices r and c for iter p
        int r = row[p];
        int c = col[p];
        
        // the wavefront for this iteration needs to be +1 from
        // the wavefront of previous iterations that have overlapping
        // reads and writes
        if (lw_iter[r]>=0) { wave[p] = MAX(wave[p],wave[lw_iter[r]]+1); }
        if (lr_iter[r]>=0) { wave[p] = MAX(wave[p],wave[lr_iter[r]]+1); }
        if (lw_iter[c]>=0) { wave[p] = MAX(wave[p],wave[lw_iter[c]]+1); }
        if (lr_iter[c]>=0) { wave[p] = MAX(wave[p],wave[lr_iter[c]]+1); }

        // count up number of iterations in each wave
        max_wave = MAX(max_wave,wave[p]);
    }
    
    // collect iterations per wave in CSR-like data structure
    int* wavestart=(int*)calloc((max_wave+2),sizeof(int));
    // first count up number of iterations in each wave
    for (int p=0; p<nnz; p++) {
        wavestart[wave[p]]++;
    }
    // prefix sum so that wavestart[i] now has index where iterations
    // for wavefront i+1.
    // wavestart[max_wave+1] should be 0, so that entry will get nnz,
    // which is the total number of iterations.
    for (int w=1; w<=max_wave+1; w++) {
        wavestart[w] = wavestart[w-1] + wavestart[w];
    }
    // Place iterations into wavefront.
    int *wavefronts=(int*)malloc(sizeof(int)*nnz);
    for (int p=nnz-1; p>=0; p--) {
        int w = wave[p];
        
        wavefronts[--wavestart[w]] = p;
        
        if (debug) {
            printf("w=%d, wavestart[w]=%d, p=%d\n", w, wavefronts[w], p);
        }
    }
    
    // epilogue to capture outputs
    (*max_wave_ptr) = max_wave;
    (*wavestart_ptr) = wavestart;
    (*wavefronts_ptr) = wavefronts;
    
}

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
      // Need to start at 1.0 instead of 2.0.  
      // See convergence argument in header, 1<=y and 1<=z.
      data_org[i] = data[i] = 1.0;
    }

    // Query information about the sparse matrix.
    double *val = mat->val; // nnz values in COO matrix representation
    int *row    = mat->row; // nnz rows in COO matrix representation
    int *col    = mat->col; // nnz rows in COO matrix representation
    if (mat->nrows != mat->ncols) assert(0);// only dealing with square matrices
    // wavebench.fields
    // FIXME: check if getenv works.  If not then exist with an error indicating
    // need to set OMP_NUM_THREADS.
    if (char* numthreads_str=getenv("OMP_NUM_THREADS")) {
        numthreads  = atoi(numthreads_str);
    } else {
        numthreads = 1;
    }
    nnz         = mat->nnz; // number of nonzeros
    N           = mat->nrows;

    // Original Computation
    printf("==== performing original computation ====\n");
    timer_start(&original_timer);
    // foreach non-zero A_{ij} in sparse matrix:
    for (int p=0; p<nnz; p++) {
        int i = row[p];
        int j = col[p];
        if (debug) {
            printf("original: i=%d, j=%d\n", i, j);
        }
        // sum = Sum_{k=0}^{w-1} 1 / exp( k * data[i] * data[j] )
        double sum = 0.0;
        for (int k=0; k<workPerIter; k++) {
            if (debug) { printf("\tsum = %lf\n", sum); }
            sum += 1.0 / exp( (double)k * data_org[i] * data_org[j] );
        }
        data_org[ i ] += 1.0 + sum;
        data_org[ j ] += 1.0 + sum; 
    }
    timer_end(&original_timer); 

    // Select a wavefront inspectors
    printf("==== performing wavefront inspector ====\n");
    timer_start(&inspector_timer);

    // Variables where outputs will be placed.
    int max_wave;
    int *wavestart;
    int * wavefronts;
    
    switch (inspectorChoice) {

        case (byhandfast_inspector):
            find_waves_fast(mat, nnz, row, col,
                            &max_wave, &wavestart, &wavefronts);
            break;
        case (fast_inspector):
            find_waves_fast_gen(mat, nnz, row, col,
                            &max_wave, &wavestart, &wavefronts);
            break;
        case (Rauchwerger95_inspector):
            rauchwerger95(mat, nnz, row, col,
                            &max_wave, &wavestart, &wavefronts);
            break;
        case (Zhuang09_inspector):
            zhuang09(mat, nnz, row, col,
                            &max_wave, &wavestart, &wavefronts);
            break;
        default:
            fprintf(stderr, "ERROR: unknown inspector\n");
     }
    
        
    timer_end(&inspector_timer);    

    // The wavefront executor
    printf("==== performing wavefront executor ====\n");
    timer_start(&executor_timer);
    // for each wavefront
    for (int w=0; w<=max_wave; w++) {  
        // foreach non-zero A_{ij} in sparse matrix in wavefront
        #pragma omp parallel for shared(data)
        for (int k=wavestart[w]; k<wavestart[w+1]; k++) {
            int p = wavefronts[k];
            
            // The rest of the code is all the same as original
            // except writing into data instead of data_org.
            int i = row[p];
            int j = col[p];
            if (debug) {
                printf("executor: i=%d, j=%d\n", i, j);
            }
            // sum = Sum_{k=0}^{w-1} 1 / exp( k * data[i] * data[j] )
            double sum = 0.0;
            for (int k=0; k<workPerIter; k++) {
                sum += 1.0 / exp( (double)k * data[i] * data[j] );
            }
            data[ i ] += 1.0 + sum;
            data[ j ] += 1.0 + sum;
        }
    }
    timer_end(&executor_timer);    

    // Compare the wavefront executor results with original.
    diff_results(N, data_org, data);

    // Compute wavebench.fields results of this run.
    // The other fields are initialized when command
    // line parameters are read.
    // numwave is initialized by the inspector.
    gethostname(computername, MAXLINESIZE);
    my_strftime(datetime, MAXLINESIZE);
    N = mat->nrows;
    // stats about the wavefronts
    numwave = max_wave + 1;
    avgIterPerWave = (double)nnz / (double)numwave;
    double sum = 0.0;
    minIterPerWave = nnz;
    maxIterPerWave = 0;
    for (int w=0; w<numwave; w++) {
        int wave_size = wavestart[w+1] - wavestart[w];
        if (wave_size>maxIterPerWave) { maxIterPerWave = wave_size; }
        if (wave_size<minIterPerWave) { minIterPerWave = wave_size; }
        sum += (wave_size - avgIterPerWave)*(wave_size - avgIterPerWave);
    }
    stddevIterPerWave = sqrt( sum / (double)numwave);  
    // timings
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
            IPairs, num_IPairs, byhandfast_inspector);

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

    strncpy(outfilename, CmdParams_getString(cmdparams,'o'), MAXLINESIZE);

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

void diff_results(int N, double *data_org, double *data)
/*--------------------------------------------------------------*//*!
  Compares the data array generated by the original code
  with the data generated by the executor.  Should be equal.
*//*--------------------------------------------------------------*/
{
    printf("==== Running difference test for wavefront computation ====\n");
    int i;
    double diff,diffsum;

    diffsum=0.0;
    for(i=0;i<N;i++) {
        if (debug) {
            printf("data_org[%d] = %lf\n", i, data_org[i]);
        }
        diff=abs(data_org[i]-data[i]);
        diffsum+=diff;

        // if have more than 0.1% diff, then print an error message
        if((diff/data_org[i])>0.001) {
            printf("diff over 0.1%%, i=%d, diff = %lf, "
                   "data_org= %lf, data=%lf\n",
                  i, diff, data_org[i], data[i]);
        }
    }
    printf("diff: diffsum = %lf\n", diffsum);
        
}
