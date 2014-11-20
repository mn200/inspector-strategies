open HolKernel Parse boolLib bossLib;

open pred_setTheory
open listTheory
open pairTheory
open PseudoCTheory
open PseudoCOpsTheory
open PseudoCPropsTheory
open hidagTheory
open PseudoCHDAGTheory
open monadsyntax boolSimps
open lcsymtacs

val _ = new_theory "forparConvert";

val _ = set_trace "Goalstack.print_goal_at_top" 0

(* for compatibility with old PC syntax *)
val _ = temp_overload_on ("ARead", ``λs e. MAccess (ASub (VRead s) e)``)
val _ = temp_overload_on ("VarExpr", ``λs. MAccess (VRead s)``)

(*
Would like this equivalence between old code and executor:

    for (i ∈ d) { body } ==

    for (w ∈ 0 .. wavedepth g) {
      parfor (p ∈ 0 .. wsizes[w])
        body[ i := wave_doms[wave_offs[w] + p] ]

But will first aim for the simpler (less realistic):

    for (i ∈ d) { body } ==

    for (w ∈ 0 .. wavedepth g) {
      parfor (i ∈ d) {
        if (wave_a[i] == w) { body }
      }
    }

where the wave_a array maps iteration numbers to wave number, which notion is captured by the wave_array_correct relation.

*)
val wave_array_correct_def = Define`
  wave_array_correct anm lo hi graph mem ⇔
    lo ≤ hi ∧
    ∃avalue.
      FLOOKUP mem anm = SOME (Array avalue) ∧
      LENGTH avalue = Num (hi - lo) ∧
      ∀i wnum. lo ≤ i ∧ i < hi ⇒
               (EL (Num (i - lo)) avalue = Int wnum ⇔
                0 ≤ wnum ∧
                ∃sg. HG sg <: wave (Num wnum) graph ∧
                     ∀n. n <: allnodes sg ⇒ [Int i] <<= FST n.data)
`;

val strip_purereads_IDEM = store_thm(
  "strip_purereads_IDEM",
  ``strip_purereads (strip_purereads g) = strip_purereads g``,
  simp[gafilter_gafilter, combinTheory.o_DEF]);

(*
val graphOf_ForLoop_Seq = store_thm(
  "graphOf_ForLoop_Seq",
  ``graphOf lab m (ForLoop i (D lo hi) body) =
      case (evalexpr m lo, evalexpr m hi) of
        (Int lo_i, Int hi_i) => if lo_i <= hi_i then
*)

val domreadAction_write = store_thm(
  "domreadAction_write[simp]",
  ``(domreadAction l m d).write = NONE``,
  Cases_on `d` >> simp[domreadAction_def]);

val simple_executor_equivalence = store_thm(
  "simple_executor_equivalence",
  ``evalexpr m0 lo = Int loi ∧
    evalexpr m0 hi = Int hii ∧
    wave_array_correct wave_a loi hii g m0 ∧
    w ≠ i ∧ wave_a ≠ i ∧ wave_a ≠ w ∧ w # lo ∧ w # hi ∧
    graphOf [] m0 (ForLoop i (D lo hi) body) = SOME(m,g) ⇒
    ∃g'.
      graphOf [] m0
        (ForLoop
           w
           (D (Value (Int 0)) (Value (Int &(wavedepth g))))
           (ParLoop i (D lo hi)
              (IfStmt (ARead wave_a (VarExpr i) == VarExpr w)
                      body
                      Done))) = SOME(m,g') ∧
      strip_purereads g' = g``,
  ONCE_REWRITE_TAC [graphOf_def] >>
  csimp[dvalues_def, evalexpr_def, PULL_EXISTS, EXISTS_PROD,
        FORALL_PROD, ssubst_def, esubst_def] >>
  simp[rich_listTheory.FOLDL_FOLDR_REVERSE, MAP_GENLIST,
       REVERSE_GENLIST, combinTheory.o_ABS_R,
       DECIDE ``PRE n - m = n - (m + 1)``] >>
  qx_gen_tac `g0` >> strip_tac >>
  `loi ≤ hii` by fs[wave_array_correct_def] >> fs[]
 );

val _ = export_theory();
