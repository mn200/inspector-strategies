open HolKernel Parse boolLib bossLib;

open listTheory

val _ = new_theory "listRange";

val listRange_def = Define`
  listRange m n = GENLIST (\i. m + i) (n + 1 - m)
`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Closefix,
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "[", TM, HardSpace 1, TOK "..",
                                  BreakSpace(1,1), TM, BreakSpace(0,0),
                                  TOK "]"],
                   term_name = "listRange" }

val listRange_SING = store_thm(
  "listRange_SING",
  ``[m .. m] = [m]``,
  SIMP_TAC (srw_ss()) [listRange_def]);
val _ = export_rewrites ["listRange_SING"]

val MEM_listRange = store_thm(
  "MEM_listRange",
  ``MEM x [m .. n] <=> m <= x /\ x <= n``,
  SIMP_TAC (srw_ss() ++ ARITH_ss)
           [listRange_def, MEM_GENLIST, EQ_IMP_THM] THEN
  STRIP_TAC THEN Q.EXISTS_TAC `x - m` THEN DECIDE_TAC);
val _ = export_rewrites ["MEM_listRange"]

val listRange_CONS = store_thm(
  "listRange_CONS",
  ``m <= n ==> ([m .. n] = m :: [m+1 .. n])``,
  SIMP_TAC (srw_ss()) [listRange_def] THEN STRIP_TAC THEN
  `(n + 1 - m = SUC (n - m)) /\ (n + 1 - (m + 1) = n - m)` by DECIDE_TAC THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [GENLIST_CONS, GENLIST_FUN_EQ]);

val listRange_EMPTY = store_thm(
  "listRange_EMPTY",
  ``n < m ==> ([m .. n] = [])``,
  SRW_TAC [][listRange_def] THEN
  `n + 1 - m = 0` by DECIDE_TAC THEN SRW_TAC[][]);

val _ = export_theory();
