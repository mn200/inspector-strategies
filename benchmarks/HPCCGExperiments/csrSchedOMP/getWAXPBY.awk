BEGIN{FS=":";ORS="";print "WAXPBY"}{if (FNR==27) print ","$2;} END{print "\n"}
