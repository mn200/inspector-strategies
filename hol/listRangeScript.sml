open HolKernel Parse boolLib bossLib;

open listTheory

val _ = new_theory "listRange";

val listRangeINC_def = Define`
  listRangeINC m n = GENLIST (\i. m + i) (n + 1 - m)
`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Closefix,
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "[", TM, HardSpace 1, TOK "..",
                                  BreakSpace(1,1), TM, BreakSpace(0,0),
                                  TOK "]"],
                   term_name = "listRangeINC" }

val listRangeINC_SING = store_thm(
  "listRangeINC_SING",
  ``[m .. m] = [m]``,
  SIMP_TAC (srw_ss()) [listRangeINC_def]);
val _ = export_rewrites ["listRangeINC_SING"]

val MEM_listRangeINC = store_thm(
  "MEM_listRangeINC",
  ``MEM x [m .. n] <=> m <= x /\ x <= n``,
  SIMP_TAC (srw_ss() ++ ARITH_ss)
           [listRangeINC_def, MEM_GENLIST, EQ_IMP_THM] THEN
  STRIP_TAC THEN Q.EXISTS_TAC `x - m` THEN DECIDE_TAC);
val _ = export_rewrites ["MEM_listRangeINC"]

val listRangeINC_CONS = store_thm(
  "listRangeINC_CONS",
  ``m <= n ==> ([m .. n] = m :: [m+1 .. n])``,
  SIMP_TAC (srw_ss()) [listRangeINC_def] THEN STRIP_TAC THEN
  `(n + 1 - m = SUC (n - m)) /\ (n + 1 - (m + 1) = n - m)` by DECIDE_TAC THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [GENLIST_CONS, GENLIST_FUN_EQ]);

val listRangeINC_EMPTY = store_thm(
  "listRangeINC_EMPTY",
  ``n < m ==> ([m .. n] = [])``,
  SRW_TAC [][listRangeINC_def] THEN
  `n + 1 - m = 0` by DECIDE_TAC THEN SRW_TAC[][]);

val listRangeLHI_def = Define`
  listRangeLHI m n = GENLIST (\i. m + i) (n - m)
`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Closefix,
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "[", TM, HardSpace 1, TOK "..<",
                                  BreakSpace(1,1), TM, BreakSpace(0,0),
                                  TOK "]"],
                   term_name = "listRangeLHI" }

val listRangeLHI_EQ = store_thm(
  "listRangeLHI_EQ",
  ``[m ..< m] = []``,
  SRW_TAC[][listRangeLHI_def]);

val MEM_listRangeLHI = store_thm(
  "MEM_listRangeLHI",
  ``MEM x [m ..< n] <=> m <= x /\ x < n``,
  SRW_TAC[ARITH_ss][listRangeLHI_def, MEM_GENLIST, EQ_IMP_THM] THEN
  Q.EXISTS_TAC `x - m` THEN DECIDE_TAC);
val _ = export_rewrites ["MEM_listRangeLHI"]


val _ = export_theory();
