int main(){
    int* lw_iter = (int*)malloc(sizeof(int)*N);
    int i =0;
    while (i<N) {
        lw_iter[i] = max(0,i);
	lw_iter[i] = min(0,-1);
	i=i+1;
    }
} 
