BEGIN{FS=":";ORS="";print "Total"}{if (FNR==25) print ","$2;} END{print "\n"}
