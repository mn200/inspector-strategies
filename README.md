inspector-strategies
====================

Verification of Inspector-style Compilations, 
joint work by Michelle Strout and Michael Norrish.

-------------------------------------
Running HOL4 (put in README.md as well)


------------------------ 
Installing HOL4
http://hol.sourceforge.net
git clone git://github.com/mn200/HOL.git

Michael indicated I would need a particular option when I installed polyML.
http://hol.sourceforge.net/InstallKananaskis.html
http://sourceforge.net/projects/polyml/?source=dlp
~/package/polyml.5.5.2] mstrout% ./configure  --enable-shared
make
sudo make install

cd ~/GITWorkDirs/HOL
more tools-poly/README
poly < tools/smart-configure.sml
bin/build -expk             // that took awhile

------------------------ 
Interpreting an inspector written in HOL4
   cd inspectors/public/code/
   setenv HOLDIR /Users/mstrout/GITWorkDirs/HOL
   $HOLDIR/bin/Holmake
   $HOLDIR/bin/hol < evalpc.ML

