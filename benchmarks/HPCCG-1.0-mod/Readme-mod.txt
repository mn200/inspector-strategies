#########################################
HPGGC-1.0-mod/Readme-mod.txt

We have added a number of files to this HPCCG version, as well as a
modified Makefile.  We have preserved the original Makefile as
Makefile.orig.  Currently, seven executables are created with the
command: make all

  test_HPCCG             using no mod files, same name as HPCCG-1.0
  HPCCG-origOMP          using HPC_sparsemv.cpp    no mod files
  HPCCG-csrOMP           using HPC_sparsemv-CSR.cpp
  HPCCG-origSchedOMP     using HPC_sparsemv-schedRuntime.cpp
  HPCCG-csrSchedOMP      using HPC_sparsemv-CSR-schedRuntime.cpp
  HPCCG-origStaticOMP    using HPC_sparsemv-schedStatic.cpp
  HPCCG-csrStaticOMP     using HPC_sparsemv-CSR-schedStatic.cpp


The HPC_Sparse_Matrix_struct contains a number of arrays
of information:  
   nnz_in_row     ... int* with size of total nnz
   list_of_inds     ... int* like the col[] array in CSR
   list_of_vals     ... double* like the val[] array in CSR
as well as a number of pointers into arrays:
   ptr_to_vals_in_row   ... double ** 
   ptr_to_inds_in_row   ... int **
   ptr_to_diags             ... double **
which are intialized based upon start_row and stop_row for for an
MPI_Rank to allow zero-based indexing.
 
   


The following updates pertain to the HPC_sparsemv() routine.

orig version:  HPC_sparsemv.cpp
This file contains the original sparsemv function that works on the
given HPC_Sparse_Matrix_struct, which contains pointers into the
sparse matrix data arrays per non-zero  (or 'row')

CSR  version:  HPC_sparsemv-CSR.cpp

This file contains a new function: HPC_sparsemv_CSR(). It could be
called from within the original HPC_sparsemv() function, but instead,
the sparsemv_CSR code has been in-lined into the original sparsemv
function for efficiency. The sparse matrix structure given above is
almost in CSR format. The list_of_inds is essentially the col[] array,
and the list_of_vals is essentially the val[] array. What we need is
the rowStart[] array, which we can create using the given nnz_in_row[]
array. The first time HPC_sparsemv() is called with the in-lined code,
a traditional rowStart array (a static local pointer) is allocated and
filled with the rowStart indices as calculated using the accumulation
of nnz_in_row values up to the current row. Thus, we are not copying
data values (found in the list_of_vals), just adding a one-time pass
over an integer array which is of the size of the number of non-zeros
in the matrix. This rowStart array will contain starting indices into
the exiting col and val arrays which exist as list_of_inds and
list_of_vals respectively within the sparse matrix structure. All
subsequent calls to HPC_sparsemv() will simply use the static rowStart
array previously filled. The rest of the in-lined code is a
traditional implementation of a CSR sparsemv computation.


Changes for OMP Schedule:

#pragma omp parallel for schedule(runtime)
orig version filename: HPC_sparsemv-schedRuntime.cpp
CSR  version filename: HPC_sparsemv-CSR-schedRuntime.cpp

Two versions (orig and csr) where the omp schedule will be given at
runtime.  See HPCCGExperiments/origSchedOMP and
HPCCGExperiments/csrSchedOMP for run scripts that show how to set the
schedule at runtime: guided, dynamic, (static) as well as chunk size.



#pragma omp parallel for schedule(static)
orig version filename: HPC_sparsemv-schedStatic.cpp
CSR  version filename: HPC_sparsemv-CSR-schedStatic.cpp

Two versions (orig and csr) where the omp schedule is static which
appears to be the number of nonzeros divided by number of OMP threads
(see openmp.org/mp-documents/omp-hands-on-SC08.pdf slides 45, 66,
67).  Since the default OMP schedule is system dependent, we have
provided both a schedule(runtime) executable, as well as a
schedule(static) executable.

