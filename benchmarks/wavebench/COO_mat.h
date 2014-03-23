/**********************************************************************//*!
 \file COO_mat.h

 \authors Alan LaMielle 9/3/10 (based on code from Barbara Kreaseck)

 Data structure and interface for representing and loading a sparse matrix in
 CSR format into COO format in memory.

 Example usage:
 COO_mat *mat=COO_mat_load_from_CSR("matrix.csr");
 COO_mat_dump(mat);
 COO_mat_dtor(&mat);

<pre>
 Copyright ((c)) 2009, Colorado State University
 All rights reserved.
 See COPYING for copyright details.
</pre>
*//**********************************************************************/

#ifndef __COO_MAT_H__
#define __COO_MAT_H__

#ifdef __cplusplus
extern "C" {
#endif

typedef struct COO_mat {
    int nrows; // Number of rows of matrix
    int ncols; // Number of columns of matrix
    int nnz;   // Number of non-zero entries in matrix

    int *row; // Row values for non-zeros (length nnz)
    int *col; // Column values for non-zeros (length nnz)
    double *val; //non-zero values (length nnz)
} COO_mat;

//! Reads the CSR sparse matrix from the given named file and loads this matrix
//! into memory in COO format.
COO_mat* COO_mat_load_from_MM(const char *filename);
COO_mat* COO_mat_load_from_CSR(const char *filename);
//COO_mat* COO_mat_load_from_CSR_mmap(const char *filename);

//! Allocates an empty COO_mat data structure using the given number of non-zero entries
COO_mat* COO_mat_ctor(int nrows,int ncols,int nnz);

//! Allocates a new COO_mat data structure that is a copy of the given COO_mat
COO_mat* COO_mat_copy(COO_mat *orig_mat);

//! Frees the given COO_mat
void COO_mat_dtor(COO_mat **mat);

//! Prints the given COO_mat
void COO_mat_dump(COO_mat *mat);

//! Validates the given COO_mat
int COO_mat_is_valid(COO_mat *mat);

#ifdef __cplusplus
}
#endif

#endif // __COO_MAT_H__
