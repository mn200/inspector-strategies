#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

#if 0
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#endif

#include "COO_mat.h"
#include "mmio.h"

COO_mat* COO_mat_load_from_MM(const char *filename)
{
    FILE *f;
    int nrows,ncols,nnz,res,curr_pos,curr_row,curr_col;
    double curr_val;
    MM_typecode matcode;

    //Open the CSR matrix file with the given name
    f=NULL;
    f=fopen(filename,"r");

    //Make sure the file was successfully opened
    if(!f)
    {
       fprintf(stderr,"Unable to open file '%s'.\n",filename);
       exit(1);
    }

    //Read the MM info
    if(0!=mm_read_banner(f,&matcode))
    {
        fprintf(stderr,"Could not process Matrix Market banner.\n");
        exit(1);
    }

    //Read the number of rows, columns, and non-zeros
    mm_read_mtx_crd_size(f,&nrows,&ncols,&nnz);

    //Allocate the COO matrix
    COO_mat *mat;
    mat=NULL;
    mat=COO_mat_ctor(nrows,ncols,nnz);

    //Make sure the COO_mat structure was successfully allocated
    if(!mat)
    {
       fprintf(stderr,"Unable to allocate new COO_mat structure using COO_mat_ctor.\n");
       exit(1);
    }

    //Read each row/col/val triple from the MM file
    curr_pos=0;
    while(curr_pos<nnz)
    {
       //Read the current row/col/val triple into the row/col/val arrays
       res=fscanf(f,"%d %d %lf\n",&curr_row,&curr_col,&curr_val);

       //Shift from the 1-based MM format to the 0-based COO in-memory format
       mat->row[curr_pos]=curr_row-1;
       mat->col[curr_pos]=curr_col-1;
       mat->val[curr_pos]=curr_val;

       curr_pos++;

       //Make sure we didn't hit the end of the file
       if(EOF==res && curr_pos<nnz)
       {
          fprintf(stderr,"Unexpected EOF in matrix file\n");
          exit(1);
       }
    }

    //We're finished reading the MM file, close it
    fclose(f);

    return mat;
}

COO_mat* COO_mat_load_from_CSR(const char *filename)
{
    FILE *f;
    int nrows,ncols,nnz;

    //Open the CSR matrix file with the given name
    f=fopen(filename,"r");
    assert(f);

    //Read the number of rows, columns, and non-zeros
    fscanf(f,"%d %d %d",&nrows,&ncols,&nnz);

    //Allocate the COO matrix
    COO_mat *mat;
    mat=COO_mat_ctor(nrows,ncols,nnz);
    assert(mat);

    //Allocate local memory for reading CSR data (will translate to COO later)
    int *row_ptr;
    row_ptr=(int*)malloc((mat->nrows+1)*sizeof(int));
    assert(row_ptr);

    //Read non-zero matrix values from the file
    int i;
    for(i=0; i<mat->nnz; i++)
    {
        if(EOF==fscanf(f,"%lf",&(mat->val[i])))
        {
            fprintf(stderr,"Unexpected EOF in matrix file\n");
            exit(1);
        }
    }

    //Read column values from the file
    for(i=0; i<mat->nnz; i++)
    {
        if(EOF==fscanf(f,"%d",&(mat->col[i])))
        {
            fprintf(stderr,"Unexpected EOF in matrix file\n");
            exit(1);
        }
    }

    //read row pointers
    for(i=0; i<mat->nrows; i++)
    {
        if(EOF==fscanf(f,"%d",&(row_ptr[i])))
        {
            fprintf(stderr,"Unexpected EOF in matrix file\n");
            exit(1);
        }
    }
    row_ptr[mat->nrows]=mat->nnz;

    //We're finished reading the CSR file, close it
    fclose(f);

    //Translate the CSR row_ptr[] into the COO row[]
    int r;
    for(i=0; i<mat->nrows; i++)
    {
        //i is the row number
        //row_ptr[i] is first non-zero in row number i
        //row_ptr[i+1] is first non-zero in row after row i
        for(r=row_ptr[i]; r<row_ptr[i+1]; r++)
        {
            mat->row[r] = i;
        }
    }

    //Free the row_ptr array
    free(row_ptr);

    return mat;
}

#if 0
//This routine is the start of an attempt to use mmap
//to improve the performance of reading in CSR sparse matrix
//files.  It is not complete.
COO_mat* COO_mat_load_from_CSR_mmap(const char *filename)
{
    int nrows,ncols,nnz;

    struct stat sb;
    char *csr_data;
    int fd,res;


    //Open the CSR matrix file with the given name
    fd=open(filename,O_RDONLY);
    assert(fd>=0);

    //Stat the opened file
    res=fstat(fd,&sb);
    assert(res>=0);

    //Assert that it is a regular file
    assert(S_ISREG(sb.st_mode));

    printf("calling mmap\n");
    csr_data=mmap(0,sb.st_size,PROT_READ,MAP_SHARED,fd,0);
    assert(csr_data!=MAP_FAILED);

    res=close(fd);
    assert(res>=0);

    //Read the number of rows, columns, and non-zeros
    sscanf(csr_data,"%d %d %d",&nrows,&ncols,&nnz);

    //Allocate the COO matrix
    COO_mat *mat;
    mat=COO_mat_ctor(nrows,ncols,nnz);
    assert(mat);

    //Allocate local memory for reading CSR data (will translate to COO later)
    int *row_ptr;
    row_ptr=malloc((mat->nrows+1)*sizeof(int));
    assert(row_ptr);

    //Read non-zero matrix values from the file
    printf("scanning non-zeros\n");
    int i;
    for(i=0; i<mat->nnz; i++)
    {
        if(EOF==sscanf(csr_data,"%lf",&(mat->val[i])))
        {
            fprintf(stderr,"Unexpected EOF in matrix file\n");
            exit(1);
        }
    }

    //Read column values from the file
    printf("scanning non-zeros\n");
    for(i=0; i<mat->nnz; i++)
    {
        if(EOF==sscanf(csr_data,"%d",&(mat->col[i])))
        {
            fprintf(stderr,"Unexpected EOF in matrix file\n");
            exit(1);
        }
    }

    //read row pointers
    for(i=0; i<mat->nrows; i++)
    {
        if(EOF==sscanf(csr_data,"%d",&(row_ptr[i])))
        {
            fprintf(stderr,"Unexpected EOF in matrix file\n");
            exit(1);
        }
    }
    row_ptr[mat->nrows]=mat->nnz;

    //We're finished reading the CSR file, munmap it
    res=munmap(csr_data,sb.st_size);
    assert(res>=0);

    //Translate the CSR row_ptr[] into the COO row[]
    int r;
    for(i=0; i<mat->nrows; i++)
    {
        //i is the row number
        //row_ptr[i] is first non-zero in row number i
        //row_ptr[i+1] is first non-zero in row after row i
        for(r=row_ptr[i]; r<row_ptr[i+1]; r++)
        {
            mat->row[r] = i;
        }
    }

    //Free the row_ptr array
    free(row_ptr);

    return mat;
}
#endif

COO_mat* COO_mat_ctor(int nrows,int ncols,int nnz)
{
    COO_mat *mat;

    //Allocate the matrix structure
    mat=NULL;
    mat=(COO_mat*)malloc(sizeof(COO_mat));
    assert(mat);

    //Init given values
    mat->nrows=nrows;
    mat->ncols=ncols;
    mat->nnz=nnz;

    //Allocate the matrix arrays
    mat->row=NULL;
    mat->col=NULL;
    mat->val=NULL;
    mat->row=(int*)malloc(nnz*sizeof(int));
    mat->col=(int*)malloc(nnz*sizeof(int));
    mat->val=(double*)malloc(nnz*sizeof(double));
    assert(mat->row);
    assert(mat->col);
    assert(mat->val);

    return mat;
}

COO_mat* COO_mat_copy(COO_mat *orig_mat)
{
    COO_mat *mat;

    assert(orig_mat);

    //Allocate the matrix structure
    mat=NULL;
    mat=(COO_mat*)malloc(sizeof(COO_mat));
    assert(mat);

    //Init integer fields
    mat->nrows=orig_mat->nrows;
    mat->ncols=orig_mat->ncols;
    mat->nnz=orig_mat->nnz;

    //Allocate the matrix arrays
    mat->row=NULL;
    mat->col=NULL;
    mat->val=NULL;
    mat->row=(int*)malloc(mat->nnz*sizeof(int));
    mat->col=(int*)malloc(mat->nnz*sizeof(int));
    mat->val=(double*)malloc(mat->nnz*sizeof(double));
    assert(mat->row);
    assert(mat->col);
    assert(mat->val);

    //Copy the row, col, and val arrays
    memcpy(mat->row,orig_mat->row,sizeof(int)*mat->nnz);
    memcpy(mat->col,orig_mat->col,sizeof(int)*mat->nnz);
    memcpy(mat->val,orig_mat->val,sizeof(double)*mat->nnz);

    return mat;
}

void COO_mat_dtor(COO_mat **mat)
{
    //Free the matrix arrays
    free((*mat)->row);
    free((*mat)->col);
    free((*mat)->val);

    //Free the matrix structure
    free(*mat);

    //Set the pointer to NULL
    *mat=NULL;
}

// prints row and col in ind order
void COO_mat_dump(COO_mat *mat)
{
   int i;

   printf("nrows: %d ncols: %d nnz: %d\n",mat->nrows,mat->ncols,mat->nnz);

   printf("row: ");
   for(i=0; i<mat->nnz; i++)
   {
      printf("%d ",mat->row[i]);
   }
   printf("\n");

   printf("col: ");
   for(i=0; i<mat->nnz; i++)
   {
      printf("%d ",mat->col[i]);
   }
   printf("\n");

   printf("val: ");
   for(i=0; i<mat->nnz; i++)
   {
      printf("%f ",mat->val[i]);
   }
   printf("\n");
}

int COO_mat_is_valid(COO_mat *mat)
{
   int i;
   int res;

   res=1;

   for(i=0; i<mat->nnz; i++)
   {
      if(mat->row[i]<0 || mat->row[i]>=mat->nrows)
      {
         res=0;
         break;
      }
      if(mat->col[i]<0 || mat->col[i]>=mat->ncols)
      {
         res=0;
         break;
      }
   }

   return res;
}
