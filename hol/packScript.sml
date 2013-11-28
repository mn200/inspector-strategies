open HolKernel Parse boolLib bossLib;

open pred_setTheory
open primitivesTheory simpleLoopTheory
open lcsymtacs

val _ = new_theory "pack";

val _ = augment_srw_ss [SatisfySimps.SATISFY_ss]

val primpack_def = Define`
  primpack dinv dp visited y =
     if ¬ visited ' y then
       (update dinv dp y, dp + 1, update visited y T)
     else (dinv, dp, visited)
`

val cpack_def = Define`
  cpack E =
     let visited = empty_v (rsizey E) F in
     let (dinv, dp, visited) =
         RFOR X
              (λ(x,y) (dinv, dp, visited). primpack dinv dp visited y)
              E
              (empty_v (rsizey E) 0, 0, visited) in
     let (dinv, dp, visited) =
         FOR (0, rsizey E)
             (λy (dinv,dp,visited). primpack dinv dp visited y)
             (dinv, dp, visited)
     in
       dinv
`;

val list_contains_allupto_N_1 = prove(
  ``∀l N. (∀i. MEM i l ⇔ i < N) ⇒ N ≤ LENGTH l``,
  rpt gen_tac >> strip_tac >>
  `∀i. i < N ⇒ ∃j. j < LENGTH l ∧ EL j l = i`
    by metis_tac[listTheory.MEM_EL] >>
  `INJ (λi. LEAST j. j < LENGTH l ∧ EL j l = i) (count N) (count (LENGTH l))`
     by (simp[INJ_DEF] >> conj_tac
         >- (rpt strip_tac >> numLib.LEAST_ELIM_TAC >> simp[]) >>
         map_every qx_gen_tac [`i`, `j`] >> strip_tac >>
         numLib.LEAST_ELIM_TAC >> simp[] >>
         numLib.LEAST_ELIM_TAC >> simp[]) >>
  `¬(CARD (count (LENGTH l)) < CARD (count N))`
    by metis_tac[PHP, FINITE_COUNT] >>
  fs[] >> decide_tac);

val list_contains_allupto_N_2 = prove(
  ``∀l N. (∀i. MEM i l ⇔ i < N) ∧ ALL_DISTINCT l ⇒ LENGTH l = N``,
  rpt strip_tac >>
  `N ≤ LENGTH l` by metis_tac[list_contains_allupto_N_1] >>
  `¬(N < LENGTH l)` suffices_by decide_tac >>
  `INJ (λi. EL i l) (count (LENGTH l)) (count N)`
     by (simp[INJ_DEF] >> conj_tac
         >- metis_tac[listTheory.MEM_EL] >>
         metis_tac[listTheory.EL_ALL_DISTINCT_EL_EQ]) >>
  `¬(CARD (count N) < CARD (count (LENGTH l)))`
    by metis_tac[PHP, FINITE_COUNT] >> fs[]);

val listphp_3 = prove(
  ``(∀n. MEM n l ⇒ n < LENGTH l) ∧ ALL_DISTINCT l ⇒
    ∀m. m < LENGTH l ⇒ MEM m l``,
  rpt strip_tac >> spose_not_then assume_tac >>
  `INJ (λi. EL i l) (count (LENGTH l)) (set l)`
     by (simp[INJ_DEF] >> conj_tac >- metis_tac[listTheory.MEM_EL] >>
         metis_tac[listTheory.EL_ALL_DISTINCT_EL_EQ]) >>
  `set l PSUBSET count (LENGTH l)`
     by (simp[PSUBSET_DEF, EXTENSION, SUBSET_DEF] >>
         metis_tac[]) >>
  `CARD (set l) < CARD (count (LENGTH l))`
     by metis_tac[CARD_PSUBSET, FINITE_COUNT] >>
  metis_tac[PHP, listTheory.FINITE_LIST_TO_SET]);

val TAKE_ADD = store_thm(
  "TAKE_ADD",
  ``∀l m n. m + n ≤ LENGTH l ⇒ TAKE (m + n) l = TAKE m l ++ TAKE n (DROP m l)``,
  Induct >> simp[] >> map_every qx_gen_tac [`h`, `m`, `n`] >> strip_tac >>
  Cases_on `m = 0` >> simp[] >>
  `m + n - 1 = m - 1 + n` by decide_tac >>
  pop_assum SUBST_ALL_TAC >> first_x_assum match_mp_tac >> decide_tac);

val SEG1 = store_thm(
  "SEG1",
  ``∀l start. start < LENGTH l ⇒ (SEG 1 start l = [EL start l])``,
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `start` >- simp[rich_listTheory.SEG_compute] >>
  REWRITE_TAC [rich_listTheory.SEG, arithmeticTheory.ONE] >> fs[]);

val SEG_GENLIST = store_thm(
  "SEG_GENLIST",
  ``∀l n m. n + m ≤ LENGTH l ⇒ SEG n m l = GENLIST (λi. EL (i + m) l) n``,
  Induct >> simp[rich_listTheory.SEG] >> rpt gen_tac >>
  Cases_on `n` >> simp[rich_listTheory.SEG] >>
  Cases_on `m` >> simp[rich_listTheory.SEG, listTheory.GENLIST_CONS,
                       combinTheory.o_DEF, arithmeticTheory.ADD_CLAUSES]);

val cpack_correct = store_thm(
  "cpack_correct",
  ``∀E. BIJ (vsub (cpack E)) (count (rsizey E)) (count (rsizey E))``,
  asm_simp_tac (srw_ss()) [cpack_def] >> rw[] >> qunabbrev_tac `visited` >>
  qmatch_assum_rename_tac `RFOR X FF E AA = (dinv0,dp0,visited0)` ["FF", "AA"] >>
  qmatch_assum_rename_tac `FOR YY FF AA = (dinv,dp,visited)` ["FF", "AA", "YY"]>>
  qabbrev_tac `N = rsizey E` >>
  qabbrev_tac `dl0 = TAKE dp0 (mvector_to_list dinv0)` >>
  `vsz visited0 = N ∧ vsz dinv0 = N ∧ dp0 ≤ N ∧ ALL_DISTINCT dl0 ∧
   (∀y. MEM y dl0 ⇒ y < N) ∧ ∀y. y < N ⇒ (visited0 ' y ⇔ MEM y dl0)`
     by cheat >>
  qpat_assum `FOR XX YY ZZ = AA` mp_tac >>
  DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `λi (di,dp,v).
    dp ≤ N ∧ i ≤ N ∧ vsz v = N ∧ vsz di = N ∧
    let dl = TAKE dp (mvector_to_list di)
    in
      ALL_DISTINCT dl ∧ (∀y. MEM y dl ⇒ y < N) ∧
      (∀y. y < i ⇒ v ' y) ∧
      ∀y. y < N ⇒ (v ' y ⇔ MEM y dl)
  ` >> simp[primpack_def] >>
  conj_tac >| [
    (* for body preserves invariant *)
    map_every qx_gen_tac [`i`, `A`] >>
    `∃di dp v. A = (di,dp,v)`
      by (PairCases_on `A` >> simp[]) >> pop_assum SUBST_ALL_TAC >>
    simp[] >> rpt strip_tac >>
    Cases_on `MEM i (TAKE dp (mvector_to_list di))`
    >- (simp[] >> qx_gen_tac `y` >> strip_tac >>
        `y = i ∨ y < i` by decide_tac >> simp[] >>
        `y < N` by decide_tac >> metis_tac[]) >>
    `dp < N`
      by (`dp ≠ vsz di` suffices_by decide_tac >>
          disch_then SUBST_ALL_TAC >>
          fs[listTheory.TAKE_LENGTH_TOO_LONG, LENGTH_mvector_to_list] >>
          metis_tac[listphp_3, LENGTH_mvector_to_list]) >>
    srw_tac[ARITH_ss][]
    >- (asm_simp_tac (srw_ss() ++ ARITH_ss)[TAKE_ADD] >>
        srw_tac[ARITH_ss][GSYM rich_listTheory.SEG_TAKE_BUTFISTN,
                          SEG1, EL_mvector_to_list] >>
        simp[update_sub] >>
        simp[listTheory.ALL_DISTINCT_APPEND] >>
        `TAKE dp (mvector_to_list (update di dp i)) =
         TAKE dp (mvector_to_list di)` suffices_by simp[] >>
        simp[listTheory.LIST_EQ_REWRITE, rich_listTheory.EL_TAKE,
             LENGTH_mvector_to_list, EL_mvector_to_list, update_sub])
    >- (qpat_assum `MEM YY (TAKE NN (mvector_to_list VV))` mp_tac >>
        asm_simp_tac (srw_ss() ++ ARITH_ss ++ boolSimps.CONJ_ss)
          [listTheory.MEM_EL, rich_listTheory.EL_TAKE,
           LENGTH_mvector_to_list, EL_mvector_to_list] >>
        disch_then (qx_choose_then `j` mp_tac) >>
        Cases_on `j < dp + 1` >> simp[] >>
        `j = dp ∨ j < dp` by decide_tac >> simp[update_sub] >>
        rw[] >> first_x_assum match_mp_tac >>
        asm_simp_tac (srw_ss() ++ ARITH_ss ++ boolSimps.CONJ_ss)
          [listTheory.MEM_EL, rich_listTheory.EL_TAKE,
           LENGTH_mvector_to_list, EL_mvector_to_list] >>
        metis_tac[])
    >- (`y = i ∨ y < i` by decide_tac >> metis_tac[update_sub]) >>
    Cases_on `y = i` >> simp[update_sub] >>
    asm_simp_tac (srw_ss() ++ ARITH_ss ++ boolSimps.CONJ_ss)
       [listTheory.MEM_EL, rich_listTheory.EL_TAKE,
        LENGTH_mvector_to_list, EL_mvector_to_list]
    >- (qexists_tac `dp` >> simp[update_sub]) >>
    eq_tac >> strip_tac
    >- (qexists_tac `n` >> srw_tac[ARITH_ss][update_sub]) >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qpat_assum `XX ≠ i` mp_tac >>
    rw[update_sub] >> qexists_tac `n` >> decide_tac,

    (* invariant implies goal *)
    rpt strip_tac >> `j = N` by decide_tac >> pop_assum SUBST_ALL_TAC >>
    qabbrev_tac `dl = TAKE dp (mvector_to_list dinv)` >>
    `∀y. MEM y dl ⇔ y < N` by metis_tac[] >>
    `LENGTH dl = N` by metis_tac [list_contains_allupto_N_2] >>
    `dp = N` by metis_tac[listTheory.LENGTH_TAKE, LENGTH_mvector_to_list] >>
    pop_assum SUBST_ALL_TAC >>
    `dl = mvector_to_list dinv`
      by metis_tac[listTheory.TAKE_LENGTH_ID, LENGTH_mvector_to_list] >>
    `∀i. i < N ⇒ dinv ' i = EL i dl`
      by (pop_assum SUBST1_TAC >>
          simp[EL_mvector_to_list]) >>
    simp[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
    metis_tac[listTheory.MEM_EL, listTheory.EL_ALL_DISTINCT_EL_EQ]
  ]);








val _ = export_theory();
