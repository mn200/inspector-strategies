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
 * Pseudocode
 *      foreach non-zero A_{ij} in sparse matrix:
 *          data[ i ] += data[i]*data[j] 
 *                       + Sum_{k=0}^{w-1} exp( data[i] * data[j] )
 *                       
 *          data[ j ] += data[i]*data[j] 
 *                       + Sum_{k=0}^{w-1} exp( data[i] * data[j] )
 *
 * The loop has reduction dependencies.  Race conditions have to be
 * avoided between two iterations that share a dependence, but they
 * could be reordered.  The wavefront inspectors we investigate in
 * this driver, treat all of the dependences between iterations in this
 * loop as creating a partial ordering between i and j where A_{i,j}
 * is a non-zero in the sparse matrix and i<j.
 * 
 *
 * \date Started: March 5, 2014
 *
 * \authors Michelle Strout
 *
 * Copyright (c) 2014, Colorado State University <br>
 * All rights reserved. <br>
 */
#include "CmdParams.h"
#include <fstream>
#include <string>
#include <sstream>
#include <iostream>

//==============================================
// Global parameters with their default values.
// Generated ...
/*int work_per_iter = 1;

// Inspector types and default inspector type.
typedef enum {
    naive_inspector,
    Rauchwerger95_inspector,
    Zhuang09_inspector
} inspector_type;
inspector_type inspectorChoice = naive_inspector;
char inspectorStr[MAXPOSSVALSTRING];
#define num_IPairs 3
static EnumStringPair IPairs[] = {{naive_inspector,"pipelined_4x4x4"},
                        {Rauchwerger95_inspector,"Rauchwerger95_inspector"},
                        {Zhuang09_inspector,"Zhuang09_inspector"}
                };

*/

//==============================================


void initParams(CmdParams * cmdparams)
/*--------------------------------------------------------------*//*!
  Uses a CmdParams object to describe all of the command line
  parameters.
*//*--------------------------------------------------------------*/
{
/*
    CmdParams_describeEnumParam(cmdparams, "tiling", 't', 1,
            "specify the tiling to use",
            TPairs, num_TPairs, diamonds_3x3x3);

    CmdParams_describeNumParam(cmdparams,"numTimeSteps", 'T', 1,
            "number of time steps",
            1, 30, 4);
*/

}   

//============================================== Inspectors
// Want to move each of these into separate file.


/*--------------------------------------------------------------*//*!
  Naive Inspector
*//*--------------------------------------------------------------*/


//============================================== Driver


int main(int argc, char ** argv) {
    // Do command-line parsing.
    CmdParams *cmdparams = CmdParams_ctor(1);
    initParams(cmdparams);
    CmdParams_parseParams(cmdparams,argc,argv);
/*
    tilingChoice = (tiling_type)CmdParams_getValue(cmdparams,'t');
    strncpy(tilingStr, CmdParams_getString(cmdparams,'t'), MAXPOSSVALSTRING);
    T = CmdParams_getValue(cmdparams,'T');
*/

    // Open the sparse matrix file and read in sparse matrix
    // FIXME: have code that does this somewhere

    return 0;
}
