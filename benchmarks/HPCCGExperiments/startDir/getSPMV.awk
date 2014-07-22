BEGIN{FS=":";ORS="";print "SPMV"}{if (FNR==28) print ","$2;} END{print "\n"}
