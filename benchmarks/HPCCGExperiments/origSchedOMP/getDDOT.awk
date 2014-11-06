BEGIN{FS=":";ORS="";print "DDOT"}{if (FNR==26) print ","$2;} END{print "\n"}
