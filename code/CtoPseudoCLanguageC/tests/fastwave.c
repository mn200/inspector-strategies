int main(){
    int* lw_iter = (int*)malloc(sizeof(int)*N);
    for (int i=0; i<N; i++) {
        lw_iter[i] = -1;
    }
    int* lr_iter = (int*)malloc(sizeof(int)*N);
    for (int i=0; i<N; i++) {
        lr_iter[i] = -1;
    }
    int* wave = (int*)malloc(sizeof(int)*nnz);
    for (int i=0; i<nnz; i++) {
        wave[i] = 0;
    }
    int max_wave = 0;
    int r = 0;
    int c = 0;
    for (int p=1; p<nnz; p++) {
        lr_iter[row[(p - 1)]] = (p - 1);
        lr_iter[col[(p - 1)]] = (p - 1);
        lw_iter[row[(p - 1)]] = (p - 1);
        lw_iter[col[(p - 1)]] = (p - 1);
        r = row[p];
        c = col[p];
        if ((lw_iter[r])>=(0)) {
            wave[p] = MAX(wave[p], (wave[lw_iter[r]] + 1));
        }
        if ((lr_iter[r])>=(0)) {
            wave[p] = MAX(wave[p], (wave[lr_iter[r]] + 1));
        }
        if ((lw_iter[c])>=(0)) {
            wave[p] = MAX(wave[p], (wave[lw_iter[c]] + 1));
        }
        if ((lr_iter[c])>=(0)) {
            wave[p] = MAX(wave[p], (wave[lr_iter[c]] + 1));
        }
        max_wave = MAX(max_wave, wave[p]);
    }
    int* wavestart = (int*)malloc(sizeof(int)*(max_wave + 2));
    for (int i=0; i<(max_wave + 2); i++) {
        wavestart[i] = 0;
    }
    for (int p=0; p<nnz; p++) {
        wavestart[wave[p]] = (wavestart[wave[p]] + 1);
    }
    for (int w=1; w<(max_wave + 1); w++) {
        wavestart[w] = (wavestart[(w - 1)] + wavestart[w]);
    }
    int* wavefronts = (int*)malloc(sizeof(int)*nnz);
    for (int i=0; i<nnz; i++) {
        wavefronts[i] = 0;
    }
    int p = 0;
    int w = 0;
    for (int prev=1; prev<(nnz + 1); prev++) {
        p = (nnz - prev);
        w = wave[p];
        wavestart[w] = (wavestart[w] - 1);
        wavefronts[wavestart[w]] = p;
    }
    
    // epilogue to capture outputs
    (*max_wave_ptr) = max_wave;
    (*wavestart_ptr) = wavestart;
    (*wavefronts_ptr) = wavefronts;
}
