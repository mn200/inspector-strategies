int main(){
    int* lw_iter = (int*)malloc(sizeof(int)*N);
    float i =0.0;
    while (i<N) {
        lw_iter[i] = max(0,i);
	lw_iter[i] = min(0,-1);
	i++;
    }
    int j =0;
    switch(i){
    	case 0  :
       			j=0;
       			break; /* optional */
    	case 3  :
       			j=3;
       			break; /* optional */
    	/* you can have any number of case statements */
    	default : /* Optional */
       			j=1;
			break;

    }
} 
