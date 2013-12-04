open HolKernel Parse boolLib bossLib;

open lcsymtacs
open pred_setTheory

val _ = new_theory "primitives";

val _ = ParseExtras.tight_equality()

val _ = type_abbrev ("mvector", ``:(num -> 'a) # num``)
val SAT_ss = SatisfySimps.SATISFY_ss
val _ = augment_srw_ss [SAT_ss]

val empty_v_def = Define`empty_v n v = (K v, n)`

val vsz_empty_v = store_thm(
  "vsz_empty_v",
  ``vsz (empty_v n v) = n``,
  simp[empty_v_def]);
val _ = export_rewrites ["vsz_empty_v"]

val empty_v_sub = store_thm(
  "empty_v_sub",
  ``empty_v n v ' i = v``,
  simp[empty_v_def, vsub_def]);
val _ = export_rewrites ["empty_v_sub"]

val FOR_def = TotalDefn.tDefine "FOR" `
  FOR (lo,hi) body A = if lo < hi then FOR (lo+1,hi) body (body lo A)
                       else A
` (WF_REL_TAC `measure (λ(lohi,b,A). SND lohi - FST lohi)`)

val FOR_0 = store_thm(
  "FOR_0",
  ``FOR (x,x) f A = A``,
  rw[Once FOR_def]);
val _ = export_rewrites ["FOR_0"]

val FOR_nonzero = store_thm(
  "FOR_nonzero",
  ``lo < hi ⇒ FOR (lo,hi) f A = FOR (lo + 1, hi) f (f lo A)``,
  rw[Once FOR_def, SimpLHS])

val FOR_ind = save_thm(
  "FOR_ind",
  theorem "FOR_ind"
          |> Q.SPEC `λp f A. Q (FST p) (SND p) f A`
          |> SIMP_RULE (srw_ss()) []
          |> Q.GEN `Q`);

val FOR_SUC_shift = store_thm(
  "FOR_SUC_shift",
  ``∀i j f A.
      FOR (SUC i, SUC j) f A = FOR (i, j) (λi a. f (SUC i) a) A``,
  NTAC 2 GEN_TAC >> Induct_on `j - i` THEN rpt strip_tac >| [
    `j <= i` by decide_tac >> ONCE_REWRITE_TAC [FOR_def] >>
    SRW_TAC[ARITH_ss][],
    `i < j` by decide_tac >> ONCE_REWRITE_TAC [FOR_def] >>
    SRW_TAC[ARITH_ss][GSYM arithmeticTheory.ADD1]
  ]);

val FOR_RULE = store_thm(
  "FOR_RULE",
  ``Inv lo A ∧ (∀i a. lo ≤ i ∧ i < hi ∧ Inv i a ⇒ Inv (i + 1) (f i a)) ∧
    (∀j a. hi ≤ j ∧ Inv j a ⇒ P a)
   ⇒
    P (FOR (lo,hi) f A)``,
  qid_spec_tac `A` >> Induct_on `hi - lo`
  >- srw_tac[ARITH_ss][Once FOR_def] >>
  srw_tac[ARITH_ss][FOR_nonzero]);

val update_def = Define`
  update (mv,sz) d r = if d < sz then ((d =+ r) mv, sz) else (mv, sz)
`;

val vsub_def = Define`vsub (mv,sz) d = mv d`

val _ = set_fixity "'" (Infixl 2000)
val _ = overload_on ("'", ``vsub``)
val _ = overload_on ("vsz", ``SND : (num -> 'a) # num -> num``)

val list_to_mvector_def = Define`
  list_to_mvector l = ((λi. EL i l), LENGTH l)
`;

val mvector_to_list_def = Define`
  mvector_to_list (f,sz) = REVERSE (FOR (0,sz) (λi l. f i :: l) [])
`;

(* e.g. *)
val _ = EVAL ``mvector_to_list (list_to_mvector [1;2;3;4])``

val LENGTH_mvector_to_list = store_thm(
  "LENGTH_mvector_to_list",
  ``LENGTH (mvector_to_list mv) = vsz mv``,
  `∃mvf msz. mv = (mvf, msz)` by (Cases_on `mv` >> simp[]) >>
  rw[mvector_to_list_def] >>
  DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `λi l. i ≤ msz ∧ LENGTH l = i` >> simp[]);
val _ = export_rewrites ["LENGTH_mvector_to_list"]

val EL_mvector_to_list = store_thm(
  "EL_mvector_to_list",
  ``i < vsz v ⇒ (EL i (mvector_to_list v) = v ' i)``,
  `∃vf vz. v = (vf,vz)` by (Cases_on `v` >> simp[]) >>
  rw[mvector_to_list_def] >>
  DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `
    λj a. j ≤ vz ∧ LENGTH a = j ∧ (∀k. k < j ⇒ EL k (REVERSE a) = vf k)` >>
  simp[] >> rpt strip_tac
  >- (`k = LENGTH a ∨ k < LENGTH a` by decide_tac
      >- simp[rich_listTheory.EL_APPEND2] >>
      simp[rich_listTheory.EL_APPEND1]) >>
  simp[vsub_def]);

val mvector_list_ISO = store_thm(
  "mvector_list_ISO",
  ``mvector_to_list (list_to_mvector l) = l``,
  SRW_TAC[][mvector_to_list_def, list_to_mvector_def] THEN
  `∀l A. REVERSE (FOR (0,LENGTH l) (λi l0. EL i l :: l0) A) = REVERSE A ++ l`
    suffices_by rw[] >>
  Induct_on `l` >> rw[Once FOR_def] >>
  simp_tac bool_ss [arithmeticTheory.ONE, FOR_SUC_shift] >>
  simp[]);

val vector_EQ = store_thm(
  "vector_EQ",
  ``v1 : 'a mvector = v2 ⇔ (∀i. v1 ' i = v2 ' i) ∧ vsz v1 = vsz v2``,
  Cases_on `v1` >> Cases_on `v2` >> rw[vsub_def, FUN_EQ_THM]);

val update_sub = store_thm(
  "update_sub",
  ``update A j x ' i = if i = j ∧ j < vsz A then x
                       else A ' i``,
  Cases_on `A` >> rw[update_def, vsub_def, combinTheory.UPDATE_APPLY] >>
  fs[combinTheory.UPDATE_APPLY]);

val vsz_update = store_thm(
  "vsz_update",
  ``vsz (update a i x) = vsz a``,
  Cases_on `a` >> rw[update_def]);
val _ = export_rewrites ["vsz_update"]

val vsz_update_FOR = store_thm(
  "vsz_update_FOR",
  ``∀A. vsz (FOR (lo, hi) (λi a. update a (f i a) (g i a)) A) = vsz A``,
  strip_tac >> DEEP_INTRO_TAC FOR_RULE >> qexists_tac `λi a. vsz a = vsz A` >>
  srw_tac[][]);

val range_CONG = store_thm(
  "range_CONG",
  ``(!i A. lo ≤ i ∧ i < hi ⇒ (f i A = f' i A)) ⇒
    FOR (lo, hi) f B = FOR (lo,hi) f' B``,
  qid_spec_tac `B` >> Induct_on `hi - lo`
  >- (ONCE_REWRITE_TAC [FOR_def] >> srw_tac[ARITH_ss][]) >>
  rpt strip_tac >> srw_tac[ARITH_ss][FOR_nonzero]);

(* relations *)
val _ = type_abbrev ("mrel", ``:(num # num -> bool) # (num # num)``)
val _ = overload_on("rsizex", ``\mr:mrel. FST (SND mr)``)
val _ = overload_on("rsizey", ``\mr:mrel. SND (SND mr)``)

val RIN_def = Define`
  RIN xy mr ⇔ FST xy < rsizex mr ∧ SND xy < rsizey mr ∧ FST mr xy
`;
val _ = overload_on("IN", ``RIN``)

val RIN_bounds = store_thm(
  "RIN_bounds",
  ``(x,y) ∈ mr ⇒ x < rsizex mr ∧ y < rsizey mr``,
  simp[RIN_def]);

val canonical_def = Define`
  canonical mr ⇔
    (case OLEAST mx. ∀x y. FST mr (x,y) ⇒ x < mx of
         NONE => F
       | SOME mx => rsizex mr = mx) ∧
    (case OLEAST my. ∀x y. FST mr (x,y) ⇒ y < my of
         NONE => F
       | SOME my => rsizey mr = my)
`;

val mrEMPTY_def = Define`
  mrEMPTY = (∅, (0,0))
`;

val IN_mrEMPTY = store_thm(
  "IN_mrEMPTY",
  ``p ∈ mrEMPTY ⇔ F``,
  simp[mrEMPTY_def, RIN_def]);
val _ = export_rewrites ["IN_mrEMPTY"]

val rsize_mrEMPTY = store_thm(
  "rsize_mrEMPTY",
  ``rsizex mrEMPTY = 0 ∧ rsizey mrEMPTY = 0``,
  simp[mrEMPTY_def]);
val _ = export_rewrites ["rsize_mrEMPTY"]

val mrEMPTY_canonical = store_thm(
  "mrEMPTY_canonical",
  ``canonical mrEMPTY``,
  simp[canonical_def, mrEMPTY_def]);

val _ = prove(
  ``¬canonical (∅, 1, 0)``,
  simp[canonical_def]);

val complete_mr_def = Define`
  complete_mr n = ((λ(x,y). x < n ∧ y < n), n, n)
`;

val rsize_complete_mr = store_thm(
  "rsize_complete_mr",
  ``rsizex (complete_mr n) = n ∧ rsizey (complete_mr n) = n``,
  simp[complete_mr_def]);
val _ = export_rewrites ["rsize_complete_mr"]

val IN_complete_mr = store_thm(
  "IN_complete_mr",
  ``(x,y) ∈ complete_mr n ⇔ x < n ∧ y < n``,
  simp[complete_mr_def, RIN_def]);
val _ = export_rewrites ["IN_complete_mr"]

val complete_mr_canonical = store_thm(
  "complete_mr_canonical",
  ``canonical (complete_mr n)``,
  simp[canonical_def, complete_mr_def] >> conj_tac >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >> simp[] >>
  (conj_tac >- metis_tac[]) >> rpt strip_tac >>
  `¬(n < n') ∧ ¬(n' < n)` by metis_tac [DECIDE ``¬(x < x)``] >>
  decide_tac)

val mrel_EQ = store_thm(
  "mrel_EQ",
  ``mr1 = mr2 ⇔
      rsizex mr1 = rsizex mr2 ∧
      rsizey mr1 = rsizey mr2 ∧
      FST mr1 = FST mr2``,
  simp[pairTheory.PAIR_FST_SND_EQ, EQ_IMP_THM]);

val canonical_zero_size = store_thm(
  "canonical_zero_size",
  ``canonical mr ⇒ (rsizex mr = 0 ⇔ rsizey mr = 0)``,
  simp[canonical_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >> simp[] >>
  strip_tac >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >> simp[] >>
  strip_tac >> eq_tac >> strip_tac >> fs[] >>
  REV_FULL_SIMP_TAC (srw_ss()) []
  >- (`~(rsizey mr - 1 < rsizey mr)` by simp[] >>
      decide_tac) >>
  `~(rsizex mr - 1 < rsizex mr)` by simp[] >>
  decide_tac)
val _ = export_rewrites ["canonical_zero_size"]

val canonical_zero_size_EMPTY = store_thm(
  "canonical_zero_size_EMPTY",
  ``canonical mr ⇒ (rsizey mr = 0 ⇔ mr = mrEMPTY)``,
  simp[EQ_IMP_THM] >> rpt strip_tac >>
  `rsizex mr = 0` by metis_tac [canonical_zero_size] >>
  Q.UNDISCH_THEN `canonical mr` mp_tac >>
  simp[mrel_EQ] >>
  simp[mrEMPTY_def, FUN_EQ_THM, canonical_def, pairTheory.FORALL_PROD] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >> simp[]);
val _ = export_rewrites ["canonical_zero_size_EMPTY"]

val nonzero_canonical_has_members = store_thm(
  "nonzero_canonical_has_members",
  ``canonical mr ∧ rsizex mr ≠ 0 ⇒ ∃x y. (x,y) ∈ mr``,
  simp[RIN_def] >> spose_not_then strip_assume_tac >>
  `rsizey mr ≠ 0` by metis_tac[canonical_zero_size] >>
  Q.UNDISCH_THEN `canonical mr` mp_tac >>
  simp[canonical_def] >>
  Cases_on `∀x y. ¬FST mr (x,y)` >> simp[] >> fs[] >>
  Cases_on `x < rsizex mr`
  >- (`¬(y < rsizey mr)` by metis_tac[] >>
      DISJ2_TAC >>
      DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >> simp[]) >>
  DISJ1_TAC >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >> simp[])

(* would be nice to prove:
val canonical_mrs_unique = store_thm(
  "canonical_mrs_unique",
  ``canonical mr1 ∧ canonical mr2 ∧ (∀p. p ∈ mr1 ⇔ p ∈ mr2) ⇒ mr1 = mr2``,
  strip_tac >> simp_tac (srw_ss()) [mrel_EQ] >>
  Cases_on `FST mr1 = FST mr2` >> simp[]
  >- (fs[RIN_def] >>
      Cases_on `rsizex mr1 = rsizex mr2` >> fs[] >>
      spose_not_then assume_tac >>
      Cases_on `rsizex mr2 = 0` >> fs[]
      >- metis_tac [canonical_zero_size]
      >- (`rsizey mr2 ≠ 0 ∧ rsizey mr1 ≠ 0` by metis_tac[canonical_zero_size] >>
          `∃x1 y1 x2 y2. (x1,y1) ∈ mr1 ∧ (x2,y2) ∈ mr2`
            by metis_tac[nonzero_canonical_has_members] >>
      first_x_assum (qspec_then `(0,MIN (rsizey mr1) (rsizey mr2))` mp_tac) >>
      srw_tac[ARITH_ss][EQ_IMP_THM]
      >- (
  CONJ
  spose_not_then strip_assume_tac >>
*)

val FINITE_RELN_HAS_MAXCOORDS = store_thm(
  "FINITE_RELN_HAS_MAXCOORDS",
  ``∀r. FINITE r ⇒
        (∃mx. ∀x y. (x,y) ∈ r ⇒ x < mx) ∧
        ∃my. ∀x y. (x,y) ∈ r ⇒ y < my``,
  Induct_on `FINITE r` >> simp[] >> rpt strip_tac >>
  `∃x y. e = (x,y)` by (Cases_on `e` >> simp[])
  >- (qexists_tac `MAX mx (x + 1)` >>
      asm_simp_tac (srw_ss() ++ boolSimps.DNF_ss) []) >>
  qexists_tac `MAX my (y + 1)` >>
  asm_simp_tac (srw_ss() ++ boolSimps.DNF_ss) []);

val canonical_mrs_exists = store_thm(
  "canonical_mrs_exists",
  ``FINITE r ⇒ ∃mr. canonical mr ∧ ∀p. p ∈ mr ⇔ p ∈ r``,
  strip_tac >> imp_res_tac FINITE_RELN_HAS_MAXCOORDS >>
  qexists_tac `(r,
                (LEAST mx. ∀x y. (x,y) ∈ r ⇒ x < mx),
                (LEAST my. ∀x y. (x,y) ∈ r ⇒ y < my))` >>
  conj_tac
  >- (simp[canonical_def] >> conj_tac >>
      DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >> simp[] >>
      fs[SPECIFICATION] >> (conj_tac >- metis_tac[]) >>
      rpt strip_tac >>
      DEEP_INTRO_TAC whileTheory.LEAST_ELIM >> simp[] >>
      (conj_tac >- metis_tac[]) >>
      qx_gen_tac `m` >> strip_tac >>
      metis_tac[arithmeticTheory.LESS_LESS_CASES]) >>
  simp[pairTheory.FORALL_PROD] >> fs[RIN_def, SPECIFICATION] >>
  map_every qx_gen_tac [`x`, `y`] >>
  DEEP_INTRO_TAC whileTheory.LEAST_ELIM >> conj_tac >- metis_tac[] >>
  qx_gen_tac `n` >> rpt strip_tac >> fs[] >>
  DEEP_INTRO_TAC whileTheory.LEAST_ELIM >> conj_tac >- metis_tac[] >>
  qx_gen_tac `m` >> rpt strip_tac >> fs[] >> metis_tac[]);

val mrel_at_x_def = Define`
  mrel_at_x (mr:mrel) x =
    REVERSE (FOR (0,rsizey mr) (λy l. if (x,y) ∈ mr then y::l else l) [])
`;

val mrel_at_y_def = Define`
  mrel_at_y (mr:mrel) y =
    REVERSE (FOR (0,rsizex mr) (λx l. if (x,y) ∈ mr then x::l else l) [])
`;


val mrel_at_x_thm = store_thm(
  "mrel_at_x_thm",
  ``mrel_at_x mr x = FILTER (λy. (x,y) ∈ mr) (GENLIST I (rsizey mr))``,
  simp[mrel_at_x_def] >>
  DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `
    λi a. i ≤ rsizey mr ∧ a = REVERSE (FILTER (λy. (x,y) ∈ mr) (GENLIST I i))`>>
  srw_tac[ARITH_ss][]
  >- simp[GSYM arithmeticTheory.ADD1, listTheory.GENLIST,
          listTheory.FILTER_APPEND_DISTRIB]
  >- simp[GSYM arithmeticTheory.ADD1, listTheory.GENLIST,
          listTheory.FILTER_APPEND_DISTRIB] >>
  `j = rsizey mr` by decide_tac >> simp[]);

val xmrels_present = store_thm(
  "xmrels_present",
  ``MEM y (mrel_at_x mr x) ⇔ (x,y) ∈ mr``,
  simp[mrel_at_x_thm, listTheory.MEM_FILTER,
       listTheory.MEM_GENLIST] >>
  metis_tac[RIN_bounds]);

val mrel_at_y_thm = store_thm(
  "mrel_at_y_thm",
  ``mrel_at_y mr y = FILTER (λx. (x,y) ∈ mr) (GENLIST I (rsizex mr))``,
  simp[mrel_at_y_def] >>
  DEEP_INTRO_TAC FOR_RULE >>
  qexists_tac `
    λi a. i ≤ rsizex mr ∧ a = REVERSE (FILTER (λx. (x,y) ∈ mr) (GENLIST I i))`>>
  srw_tac[ARITH_ss][]
  >- simp[GSYM arithmeticTheory.ADD1, listTheory.GENLIST,
          listTheory.FILTER_APPEND_DISTRIB]
  >- simp[GSYM arithmeticTheory.ADD1, listTheory.GENLIST,
          listTheory.FILTER_APPEND_DISTRIB] >>
  `j = rsizex mr` by decide_tac >> simp[]);

val ymrels_present = store_thm(
  "ymrels_present",
  ``MEM x (mrel_at_y mr y) ⇔ (x,y) ∈ mr``,
  simp[mrel_at_y_thm, listTheory.MEM_FILTER,
       listTheory.MEM_GENLIST] >>
  metis_tac[RIN_bounds]);

val _ = Hol_datatype`direction = X | Y`
val RFOR_def = Define`
  RFOR X f mr A =
    FOR (0, rsizex mr)
        (λx acc. FOLDL (λacc y. f (x,y) acc) acc (mrel_at_x mr x))
        A ∧
  RFOR Y f mr A =
    FOR (0, rsizey mr)
        (λy acc. FOLDL (λacc x. f (x,y) acc) acc (mrel_at_y mr y))
        A
`

val _ = export_theory();
