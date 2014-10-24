/* int* malloc(int); */
#include <stdlib.h>


int main() {

  int x = 5;
  int y;
  y = 7;
  int * row = malloc(sizeof(int)*4);
  for (int i = 0; i < 4; i++) {
    row[i] = 0;
  }
  
  return 0;
} 
