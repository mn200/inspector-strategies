CtoPseudoCLanguageC/Readme.txt

gettingStarted.hs clearly currently only works on test-noHeader.c
since it is built into the .hs code itself.

requirements:
   cabal install language-c
   cabal install groom

------------------------------------
The following astDump files were created using the Clang front end on
gcc on my Mac (Apple LLVM version 5.1 (clang-503.0.40) (based on LLVM 3.4svn)):

expr.c
expr.pp.c
expr.pp.c.astDump

varAssign.c
varAssign.c.astDump
varAssign.pp.c
varAssign.pp.c.astDump

varDecl.c
varDecl.c.astDump
varDecl.pp.c
varDecl.pp.c.astDump

To invoke the C-PreProcessor in gcc:
    gcc -E expr.c -o expr.pp.c

To dump the ast:
    gcc -cc1 -ast-dump expr.pp.c -o expr.pp.c.astDump

-------------------------------------------------

