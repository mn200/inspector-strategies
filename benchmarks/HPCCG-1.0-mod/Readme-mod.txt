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


The following updates pertain to the HPC_sparsemv() routine.

orig version:  HPC_sparsemv.cpp
This file contains the original sparsemv function that works on the
given HPC_Sparse_Matrix_struct, which contains pointers into the
sparse matrix data files per non-zero 'row'

CSR  version:  HPC_sparsemv-CSR.cpp
This file contains a new function: HPC_sparsemv_CSR() It could be
called from within the original: HPC_sparsemv() but it has been
in-lined for efficiency.  The first time HPC_sparsemv() is called, a
traditional rowStart array (a static local pointer) is allocated and
filled with the rowStart indices into the exiting col and val arrays
which exist as list_of_inds and list_of_vals respectively within the
sparse matrix structure.  All other calls will simpley use the static
rowStart array previously filled.


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

