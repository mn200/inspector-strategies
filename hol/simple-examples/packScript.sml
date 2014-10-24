open HolKernel Parse boolLib bossLib;

open pred_setTheory
open primitivesTheory forLoopTheory simpleLoopTheory
open lcsymtacs boolSimps

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

val primpack_E = store_thm(
  "primpack_E",
  ``∀dv0 pos0 visited0 i dv pos visited.
    primpack dv0 pos0 visited0 i = (dv,pos,visited) ⇒

    ALL_DISTINCT (TAKE pos0 (mvector_to_list dv0)) ∧
    (∀j. MEM j (TAKE pos0 (mvector_to_list dv0)) ⇒ j < vsz visited0) ∧
    (∀j. j < vsz visited0 ⇒ (visited0 ' j ⇔ MEM j (TAKE pos0 (mvector_to_list dv0)))) ∧
    pos0 ≤ vsz visited0 ∧ vsz dv0 = vsz visited0 ∧
    i < vsz visited0

   ⇒

    vsz dv = vsz visited0 ∧ visited = update visited0 i T ∧
    (∀j. MEM j (TAKE pos (mvector_to_list dv)) ⇒ j < vsz visited) ∧
    (∀j. j < vsz visited ⇒
         (visited ' j ⇔ MEM j (TAKE pos (mvector_to_list dv)))) ∧
    ALL_DISTINCT (TAKE pos (mvector_to_list dv)) ∧
    pos ≤ vsz visited``,
  rpt gen_tac >>
  simp[primpack_def] >> Cases_on `visited0 ' i` >> simp[]
  >- (rpt strip_tac >> simp[vector_EQ, update_sub] >> rw[] >>
      metis_tac[]) >>
  DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) >>
  strip_tac >>
  qabbrev_tac `N = vsz visited0` >>
  qabbrev_tac `L = TAKE N (mvector_to_list dv0)` >>
  `pos0 < N`
    by (`pos0 ≠ N` suffices_by decide_tac >> strip_tac >>
        pop_assum SUBST_ALL_TAC >>
        `LENGTH L = N` by simp[Abbr`L`] >> metis_tac[listphp_3]) >>
  asm_simp_tac (srw_ss() ++ ARITH_ss ++ CONJ_ss)[] >>
  `TAKE pos0 (mvector_to_list (update dv0 pos0 i)) =
   TAKE pos0 (mvector_to_list dv0)`
     by simp[listTheory.LIST_EQ_REWRITE, rich_listTheory.EL_TAKE,
             LENGTH_mvector_to_list, EL_mvector_to_list, update_sub] >>
  rpt conj_tac
  >- asm_simp_tac (srw_ss() ++ ARITH_ss ++ DNF_ss)
       [TAKE_ADD, GSYM rich_listTheory.SEG_TAKE_BUTFISTN,
        SEG1, EL_mvector_to_list, update_sub]
  >- (qx_gen_tac `j` >> strip_tac >>
      Cases_on `i = j`
      >- (simp[listTheory.MEM_EL, update_sub] >>
          qexists_tac `pos0` >>
          simp[rich_listTheory.EL_TAKE, EL_mvector_to_list,
               update_sub]) >>
      simp[update_sub] >>
      simp[EQ_IMP_THM, TAKE_ADD, DISJ_IMP_THM] >>
      simp[GSYM rich_listTheory.SEG_TAKE_BUTFISTN, SEG1,
           EL_mvector_to_list, update_sub])
  >- (asm_simp_tac (srw_ss() ++ ARITH_ss)[TAKE_ADD] >>
      `¬MEM i (TAKE pos0 (mvector_to_list dv0))` by metis_tac[] >>
      srw_tac[ARITH_ss][GSYM rich_listTheory.SEG_TAKE_BUTFISTN,
                        SEG1, EL_mvector_to_list, update_sub] >>
      simp[listTheory.ALL_DISTINCT_APPEND]))

val FOLDL_RULE = prove(
  ``∀Q f a0 l Inv.
      Inv a0 ∧ (∀a. Inv a ⇒ Q a) ∧ (∀a v. MEM v l ∧ Inv a ⇒ Inv (f a v)) ⇒
      Q (FOLDL f a0 l)``,
  rpt strip_tac >> first_x_assum match_mp_tac >> Q.UNDISCH_THEN `Inv a0` mp_tac >>
  qid_spec_tac `a0` >>
  Induct_on `l` >> simp[]);

val cpack_correct = store_thm(
  "cpack_correct",
  ``∀E. (∀x y. MEM y (mrel_at_x E x) ⇒ y < rsizey E) ⇒
        BIJ (vsub (cpack E)) (count (rsizey E)) (count (rsizey E))``,
  asm_simp_tac (srw_ss()) [cpack_def] >> rw[] >> qunabbrev_tac `visited` >>
  qmatch_assum_rename_tac `RFOR X FF E AA = (dinv0,dp0,visited0)` ["FF", "AA"] >>
  qmatch_assum_rename_tac `FOR YY FF AA = (dinv,dp,visited)` ["FF", "AA", "YY"]>>
  qabbrev_tac `N = rsizey E` >>
  qabbrev_tac `dl0 = TAKE dp0 (mvector_to_list dinv0)` >>
  qabbrev_tac `
    Inv = λ(di,dp,v).
           dp ≤ N ∧ vsz v = N ∧ vsz di = N ∧
           let dl = TAKE dp (mvector_to_list di)
           in
              ALL_DISTINCT dl ∧ (∀y. MEM y dl ⇒ y < N) ∧
              ∀y. y < N ⇒ (v ' y ⇔ MEM y dl)` >>
  `∀i A. i < N ∧ Inv A ⇒ Inv ((λ(dv,pos,v). primpack dv pos v i) A)`
    by (rpt gen_tac >>
        `∃di pos v. A = (di,pos,v)`
           by (PairCases_on `A` >> simp[]) >> pop_assum SUBST_ALL_TAC >>
        simp[Abbr`Inv`] >> rpt strip_tac >>
        `∃di' pos' v'. primpack di pos v i = (di',pos',v')`
           by metis_tac[TypeBase.nchotomy_of ``:'a#'b``] >>
        simp[] >> pop_assum (mp_tac o MATCH_MP primpack_E) >>
        simp[] >> rw[] >> fs[] >> metis_tac[]) >>
  `Inv (dinv0, dp0, visited0)`
     by (qpat_assum `RFOR XX YY ZZ AA = BB` mp_tac >>
         qpat_assum `FOR XX YY ZZ = AA` kall_tac >>
         simp[RFOR_def] >>
         DEEP_INTRO_TAC FOR_RULE >>
         qexists_tac `λi A. Inv A` >>
         simp[] >>
         conj_tac >- simp[Abbr`Inv`] >>
         map_every qx_gen_tac [`i`, `A`] >> strip_tac >>
         match_mp_tac FOLDL_RULE >> qexists_tac `Inv` >>
         simp[]) >>
  qpat_assum `FOR XX YY ZZ = AA` mp_tac >>
  DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `λi (di,dp,v). Inv (di,dp,v) ∧ i ≤ N ∧ (∀y. y < i ⇒ v ' y)` >>
  simp[] >> conj_tac >| [
    (* for body preserves invariant *)
    map_every qx_gen_tac [`i`, `A`] >>
    `∃di dp v. A = (di,dp,v)`
      by (PairCases_on `A` >> simp[]) >> pop_assum SUBST_ALL_TAC >>
    simp[] >> rpt strip_tac >>
    `∃di2 dp2 v2. primpack di dp v i = (di2,dp2,v2)`
      by metis_tac[TypeBase.nchotomy_of ``:'a # 'b``] >>
    simp[] >> conj_tac
    >- (first_x_assum (qspecl_then [`i`, `(di,dp,v)`] mp_tac) >>
        simp[]) >>
    first_assum (mp_tac o MATCH_MP primpack_E) >> simp[Abbr`Inv`] >>
    fs[LET_THM] >>
    rpt strip_tac >> `y = i ∨ y < i` by decide_tac
    >- (pop_assum SUBST_ALL_TAC >> simp_tac (srw_ss()) [update_sub] >>
        rw[]) >>
    first_assum (fn th => simp_tac(srw_ss() ++ ARITH_ss) [th, update_sub]) >>
    metis_tac[],

    (* invariant implies goal *)
    rpt strip_tac >> `j = N` by decide_tac >> pop_assum SUBST_ALL_TAC >>
    qunabbrev_tac `Inv` >> fs[LET_THM] >>
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

val construct_explicit_relation_def = Define`
  construct_explicit_relation M N f g =
    FOR (0,N)
        (λi E. rupdate (rupdate E (vsub f i, i)) (vsub g i, i))
        (∅, (M, N))
`;

val cer_guarantees_ys = store_thm(
  "cer_guarantees_ys",
  ``(E = construct_explicit_relation M N f g) ⇒
    (∀x y. MEM y (mrel_at_x E x) ⇒ y < rsizey E)``,
  simp[construct_explicit_relation_def] >> DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `λi mr. ∀x y. MEM y (mrel_at_x mr x) ⇒ y < rsizey mr` >>
  simp[xmrels_present] >> conj_tac >- simp[RIN_def] >>
  simp[RIN_rupdate] >> rw[] >> metis_tac[]);

val cer_rsizey = store_thm(
  "cer_rsizey",
  ``E = construct_explicit_relation M N f g ⇒ rsizey E = N``,
  simp[construct_explicit_relation_def] >> DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `λi mr. rsizey mr = N` >> simp[]);

val cpackcer = MATCH_MP cpack_correct (UNDISCH_ALL cer_guarantees_ys)

(*
 |- E = construct_explicit_relation M N f g ⇒
    δ = cpack E ⇒
    N ≤ vsz A ⇒
    FOR (0,N) (λi A. update A (δ ' i) (rhs (δ ' i) (A ' (δ ' i)))) A =
    FOR (0,N) (λi A. update A i (rhs i (A ' i))) A
*)

val final_correctness = save_thm(
  "final_correctness",
  PART_MATCH (lhand o lhand)
             (PERMS_SUFFICE |> Q.INST [`f` |-> `rhs`] |> GEN_ALL)
             (concl cpackcer)
    |> REWRITE_RULE [cpackcer, UNDISCH_ALL cer_rsizey]
    |> REWRITE_RULE [GSYM (ASSUME ``δ = cpack E``)]
    |> DISCH_ALL);

val _ = export_theory();
