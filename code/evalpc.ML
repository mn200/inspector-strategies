load "fastwaveTheory";
load "PseudoCLib";
local
open PseudoCLib
open fastwaveTheory
val initstate =
    ``(FEMPTY |+ ("N", Int 5)
              |+ ("nnz", Int 13)
              |+ ("max_wave", Int 0)
              |+ ("r", Int 0)
              |+ ("c", Int 0)
              |+ ("row", Array [Int 0; Int 0; Int 0; Int 1; Int 1; Int 1;
                                Int 2; Int 2; Int 2; Int 3; Int 3; Int 4;
                                Int 4])
              |+ ("col", Array [Int 0; Int 1; Int 2; Int 1; Int 2; Int 3;
                                Int 2; Int 3; Int 4; Int 3; Int 4; Int 0;
                                Int 4]),
       ^(rhs (concl findWavesFast_def)))``;

in

val results = chaineval 100 initstate;

end
