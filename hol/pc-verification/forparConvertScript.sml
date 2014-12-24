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

open indexedListsTheory

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

val _ = augment_srw_ss [intSimps.OMEGA_ss]

val strip_labels_def = Define`
  strip_labels (g : 'a pcg) : unit pcg = hdmap (K () ## I) g
`

val nstrip_labels_def = Define`
  nstrip_labels (n : 'a pcnode) : unit pcnode = nmap (K () ## I) n
`;

val strip_labels_thm = store_thm(
  "strip_labels_thm[simp]",
  ``strip_labels ε = ε ∧
    strip_labels (n <+ g) = nstrip_labels n <+ strip_labels g ∧
    nstrip_labels (HD a) = HD (polydata_upd (K () ## I) a) ∧
    nstrip_labels (HG g) = HG (strip_labels g)``,
  simp[strip_labels_def, nstrip_labels_def]);

val polydata_upd_o = store_thm(
  "polydata_upd_o[simp]",
  ``polydata_upd f (polydata_upd g a) = polydata_upd (f o g) a``,
  simp[actionTheory.polydata_upd_def]);

val SND_PAIRMAP = store_thm(
  "SND_PAIRMAP[simp]",
  ``SND o (f ## g) = g o SND``,
  simp[FUN_EQ_THM]);

val strip_labels_preserves_meaning = store_thm(
  "strip_labels_preserves_meaning[simp]",
  ``(∀n: α pcnode. pcn_eval (nstrip_labels n) = pcn_eval n) ∧
    (∀g: α pcg. pcg_eval (strip_labels g) = pcg_eval g)``,
  ho_match_mp_tac hidag_ind >> simp[pcg_eval_thm, FUN_EQ_THM]);

val strip_labels_merge = store_thm(
  "strip_labels_merge[simp]",
  ``∀g1 g2. strip_labels (g1 ⊕ g2) = strip_labels g1 ⊕ strip_labels g2``,
  Induct >> simp[]);

fun rename_subterm pat_t avoids t = let
  fun test (bvs, subt) =
      case SOME(match_term pat_t subt) handle HOL_ERR _ => NONE of
          SOME(tmsub, tysub)
      if can (match_term pat_t) subt then


fun case_t (q,sl) = let
  fun has_t (asl, w) = let
    val t = parse_in_context (w::asl) q
  in
    if List.exists (free_in t) (w::asl) then ALL_TAC
    else NO_TAC
  end (asl,w)
in
  qmatch_rename_tac q sl ORELSE qmatch_assum_rename_tac q sl ORELSE
  has_t
end


val hdmerge_cons_snoc = store_thm(
  "hdmerge_cons_snoc",
  ``∀g h a b. g ⊕ (a <+ ε) = b <+ h ⇔
                a = b ∧ g = h ∧ ¬ngtouches a g ∨
                ∃gh0. g = b <+ gh0 ∧ h = gh0 ⊕ (a <+ ε)``,
  Induct >> conj_tac >> simp[] >- metis_tac[] >>
  qx_gen_tac `g` >> strip_tac >> simp[hidagAdd_11_thm] >>
  qx_genl_tac [`a1`, `h`, `b`, `a2`] >> Cases_on `a1 ∼ₜ a2` >> dsimp[]
  >- metis_tac[htouches_SYM] >>
  Cases_on `a1 = a2` >- (dsimp[EQ_IMP_THM] >> rw[] >> metis_tac[htouches_SYM]) >>
  simp[] >> metis_tac[htouches_SYM]);

val ngtouches_merge = store_thm(
  "ngtouches_merge[simp]",
  ``ngtouches n (g1 ⊕ g2) ⇔ ngtouches n g1 ∨ ngtouches n g2``,
  Induct_on `g1` >> simp[]);

val hdmerge_11 = store_thm(
  "hdmerge_11[simp]",
  ``(∀g g1 g2. g ⊕ g1 = g ⊕ g2 ⇔ g1 = g2) ∧
    (∀g g1 g2. g1 ⊕ g = g2 ⊕ g ⇔ g1 = g2)``,
  conj_tac >> Induct >> simp[] >> rpt strip_tac >>
  `∀a g1. g1 ⊕ a <+ g = (g1 ⊕ a <+ ε) ⊕ g`
    by (Induct_on `g1` >> simp[]) >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
  simp[] >> pop_assum kall_tac >> map_every qid_spec_tac [`g2`, `g1`] >>
  Induct >> simp[] >> rpt strip_tac >- (Cases_on `g2` >> simp[]) >>
  qmatch_rename_tac `b <+ (g1 ⊕ a <+ ε) = g2 ⊕ a <+ ε ⇔ b <+ g1 = g2` [] >>
  dsimp[hdmerge_cons_snoc, EQ_IMP_THM] >> rw[] >> fs[]);

(*
val graphOf_label_invariant = store_thm(
  "graphOf_label_invariant",
  ``∀s lab m0 m g.
      graphOf lab m0 s = SOME(m,g) ⇒
      ∀lab'.
        ∃g'. graphOf lab' m0 s = SOME(m,g') ∧
             strip_labels g' = strip_labels g``,
  ho_match_mp_tac graphOf_ind' >> Cases >> strip_tac >>
  TRY (simp_tac (srw_ss()) [Once graphOf_def] >> NO_TAC) >>
  FIRST [

  has_t `Assign` >>
    simp[graphOf_def, PULL_EXISTS, mareadAction_def, actionTheory.polydata_upd_def,
         dvreadAction_def, addLabel_def],

  has_t `IfStmt` >>
    dsimp[graphOf_def, value_case_eq, PULL_EXISTS, bool_case_eq, EXISTS_PROD,
          addLabel_def, readAction_def, actionTheory.polydata_upd_def] >>
    fs[AND_IMP_INTRO, PULL_FORALL] >> rpt strip_tac >> first_x_assum match_mp_tac >>
    simp[pairTheory.LEX_DEF, MAX_PLUS] >> metis_tac[],

  has_t `ForLoop` >>
    simp[graphOf_def, PULL_EXISTS, EXISTS_PROD, FORALL_PROD, addLabel_def,
         actionTheory.polydata_upd_def] >>
    qx_genl_tac [`lab`, `m0`, `m`, `dvs`, `g`] >> strip_tac >>
    Q.UNDISCH_THEN `dvalues m0 d = SOME dvs` kall_tac >>
    fs[rich_listTheory.FOLDL_FOLDR_REVERSE] >>
    qabbrev_tac `ds = REVERSE dvs` >> markerLib.RM_ALL_ABBREVS_TAC >>
    pop_assum mp_tac >> map_every qid_spec_tac [`m`, `g`] >>
    Induct_on `ds` >> simp[PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
    qabbrev_tac `ff = λlab vnm bod v mg0.
       do
          (m0', g0) <- mg0;
          (m, g') <- graphOf (v::lab) m0' (ssubst vnm v bod);
          SOME(m, g0 ⊕ HG g' <+ ε)
       od` >> fs[] >>
    full_simp_tac (srw_ss() ++ ETA_ss) [] >> rpt strip_tac >>
    res_tac >> first_x_assum (qspec_then `lab'` strip_assume_tac) >>
    simp[] >> fs[PULL_FORALL, AND_IMP_INTRO] >>
    first_x_assum match_mp_tac >> simp[pairTheory.LEX_DEF] >> rw[] >>
    metis_tac[],

  has_t `ParLoop` >>
    simp[graphOf_def, PULL_EXISTS, addLabel_def, combinTheory.o_ABS_R]

  ALL_TAC
  ]

*)

val simple_executor_equivalence = store_thm(
  "simple_executor_equivalence",
  ``evalexpr m0 lo = Int loi ∧
    evalexpr m0 hi = Int hii ∧
    wave_array_correct wave_a loi hii g m0 ∧
    w ≠ i ∧ wave_a ≠ i ∧ wave_a ≠ w ∧ w # lo ∧ w # hi ∧ w # body ∧
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
      strip_labels (strip_purereads g') = strip_labels g``,
  ONCE_REWRITE_TAC [graphOf_def] >>
  csimp[dvalues_def, evalexpr_def, PULL_EXISTS, EXISTS_PROD,
        FORALL_PROD, ssubst_def, esubst_def] >>
  simp[rich_listTheory.FOLDL_FOLDR_REVERSE, MAP_GENLIST,
       REVERSE_GENLIST, combinTheory.o_ABS_R,
       DECIDE ``PRE n - m = n - (m + 1)``] >>
  qx_gen_tac `g0` >> strip_tac >>
  `loi ≤ hii` by fs[wave_array_correct_def] >> fs[] >>
  qabbrev_tac `sz = Num (hii - loi)` >>
  `∀m. m < sz ⇒ &(sz - (m + 1)) + loi = hii - &(m + 1)`
    by simp[int_arithTheory.INT_NUM_SUB, Abbr`sz`] >>
  fs[Cong GENLIST_CONG] >>
  simp[graphOf_def, ssubst_def, esubst_def]
 );

val _ = export_theory();
