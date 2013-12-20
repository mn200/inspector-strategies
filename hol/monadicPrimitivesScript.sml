open HolKernel Parse boolLib bossLib;

open lcsymtacs
open pred_setTheory
open monadsyntax

val _ = new_theory "monadicPrimitives";

val _ = overload_on("assert", ``OPTION_GUARD``)
val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)
val _ = ParseExtras.tight_equality()

val _ = type_abbrev ("mvector", ``:'a list``)
val _ = disable_tyabbrev_printing "mvector"
val SAT_ss = SatisfySimps.SATISFY_ss
val _ = augment_srw_ss [SAT_ss]

fun csimp thl = asm_simp_tac (srw_ss() ++ boolSimps.CONJ_ss) thl
fun asimp thl = asm_simp_tac (srw_ss() ++ ARITH_ss) thl
fun acsimp thl = asm_simp_tac (srw_ss() ++ boolSimps.CONJ_ss ++ ARITH_ss) thl
val bsimp = asm_simp_tac bool_ss

val vsub_def = Define`
  vsub l i = if i < LENGTH l then SOME (EL i l) else NONE
`

val _ = set_fixity "'" (Infixl 2000)
val _ = overload_on ("'", ``vsub``)
val _ = overload_on ("vsz", ``LENGTH : 'a list -> num``)
val _ = overload_on ("LENGTH", listSyntax.length_tm)

val empty_v_def = Define`empty_v n v = GENLIST (K v) n`

val vsz_empty_v = store_thm(
  "vsz_empty_v",
  ``vsz (empty_v n v) = n``,
  simp[empty_v_def]);
val _ = export_rewrites ["vsz_empty_v"]

val empty_v_sub = store_thm(
  "empty_v_sub",
  ``empty_v n v ' i = do assert(i < n); SOME v od``,
  simp[empty_v_def, vsub_def] >> Cases_on `i < n` >> simp[]);
val _ = export_rewrites ["empty_v_sub"]

val IGNORE_BIND_ASSOC = store_thm(
  "IGNORE_BIND_ASSOC",
  ``OPTION_BIND (OPTION_IGNORE_BIND m1 m2) f =
    OPTION_IGNORE_BIND m1 (OPTION_BIND m2 f)``,
  Cases_on `m1` >> simp[]);
val _ = export_rewrites ["IGNORE_BIND_ASSOC"]

val update_def = Define`
  update l d r = if d < LENGTH l then SOME (LUPDATE r d l) else NONE
`;

val EL_mvector_to_list = store_thm(
  "EL_mvector_to_list",
  ``i < vsz v ⇒ v ' i = SOME (EL i v)``,
  simp[vsub_def]);

val vector_EQ = store_thm(
  "vector_EQ",
  ``v1 : 'a mvector = v2 ⇔ (∀i. v1 ' i = v2 ' i) ∧ vsz v1 = vsz v2``,
  simp[listTheory.LIST_EQ_REWRITE, vsub_def, EQ_IMP_THM] >>
  metis_tac[TypeBase.one_one_of ``:'a option``]);

val mFOR_def = tDefine "mFOR" `
  mFOR (lo,hi) f A =
    if lo < hi then
      case f lo A of
          NONE => NONE
        | SOME A' => mFOR (lo+1,hi) f A'
    else SOME A
` (WF_REL_TAC `measure (λ((lo,hi),f,A). hi - lo)`)

val mFOR_0 = store_thm(
  "mFOR_0",
  ``mFOR (x,x) f A = SOME A``,
  simp[Once mFOR_def]);
val _ = export_rewrites ["mFOR_0"]

val mFOR_thm = store_thm(
  "mFOR_thm",
  ``(hi ≤ lo ⇒ mFOR (lo,hi) f A = SOME A) ∧
    (lo < hi ⇒ mFOR (lo,hi) f A =
               do
                 A' <- f lo A;
                 mFOR (lo+1,hi) f A'
               od)``,
  strip_tac >> simp[Once mFOR_def, SimpLHS] >>
  Cases_on `f lo A` >> simp[]);

val mFOR_RULE = store_thm(
  "mFOR_RULE",
  ``∀lo hi f A P Inv.
      Inv lo A ∧
      (∀i s0. lo ≤ i ∧ i < hi ∧ Inv i s0 ⇒ ∃s. f i s0 = SOME s ∧ Inv (i + 1) s) ∧
      (∀i s. hi ≤ i ⇒ Inv i s ⇒ P (SOME s)) ⇒
      P (mFOR (lo,hi) f A)``,
  rpt gen_tac >>
  qid_spec_tac `A` >> Induct_on `hi - lo`
  >- srw_tac[ARITH_ss][mFOR_thm] >>
  srw_tac[][] >>
  `lo ≤ lo ∧ lo < hi` by decide_tac >>
  `∃A'. f lo A = SOME A' ∧ Inv (lo + 1) A'` by metis_tac[] >>
  srw_tac[ARITH_ss][mFOR_thm]);

val _ = overload_on ("''", ``λa i. OPTION_BIND a (combin$C vsub i)``)
val _ = set_fixity "''" (Infixl 2000)

val vsub_assert = store_thm(
  "vsub_assert",
  ``A ' i = do assert(i < vsz A); SOME (EL i A) od``,
  rw[vsub_def]);

val update_assert = store_thm(
  "update_assert",
  ``update A i v = do assert(i < vsz A); SOME(LUPDATE v i A) od``,
  rw[update_def]);

val mFOR_CONG = store_thm(
  "mFOR_CONG",
  ``(∀j A. j < hi ⇒ (f j A = f' j A)) ⇒
    mFOR (lo,hi) f A = mFOR (lo,hi) f' A``,
  strip_tac >> qid_spec_tac `A` >>
  Induct_on `hi - lo` >> asm_simp_tac(srw_ss() ++ ARITH_ss) [mFOR_thm]);

val PERMS_suffice0 = prove(
  ``BIJ (THE o vsub Δ) (count N) (count N) ∧ vsz Δ = N ∧ N ≤ vsz A1 ∧
    SOME final = mFOR (0, N) (λi A. update A i (g i)) A1 ⇒
    ∀m n A2:α list.
      vsz A2 = vsz A1 ∧
      (m = N - n) ∧ n ≤ N ∧
      (∀i. i < vsz A2 ⇒
           A2 ' i = if i ∈ IMAGE (THE o vsub Δ) (count n) then final ' i
                    else A1 ' i)
   ⇒
      mFOR (n,N) (λj A. do i <- Δ ' j ; update A i (g i) od) A2 = SOME final``,
  strip_tac >>
  `vsz final = vsz A1 ∧
   ∀i. i < vsz A1 ⇒ EL i final = if i < N then g i else EL i A1`
    by (qpat_assum `SOME final = XX` mp_tac >>
        DEEP_INTRO_TAC mFOR_RULE >>
        qexists_tac
          `λi A. vsz A = vsz A1 ∧
                 ∀j. j < vsz A1 ⇒ EL j A = if j < i ∧ j < N then g j
                                           else EL j A1` >>
        srw_tac[ARITH_ss][update_assert, listTheory.EL_LUPDATE] >>
        srw_tac[][] >> full_simp_tac(srw_ss() ++ ARITH_ss) []) >>
  `∀i. i < N ⇒ EL i Δ < N`
    by (qpat_assum `BIJ ff ss tt` mp_tac >>
        simp[BIJ_IFF_INV, vsub_def]) >>
  Induct >| [
    rpt strip_tac >> `N = n` by decide_tac >> qpat_assum `0 = N - n` kall_tac >>
    srw_tac[ARITH_ss][] >>
    `A2 = final` suffices_by simp[] >>
    srw_tac[ARITH_ss][listTheory.LIST_EQ_REWRITE] >>
    Cases_on `x < LENGTH Δ`
    >- (`x ∈ IMAGE (THE o $' Δ) (count (LENGTH Δ))`
           by (simp[] >> qpat_assum `BIJ ff ss tt` mp_tac >>
               simp[BIJ_IFF_INV, vsub_def] >>
               asm_simp_tac(srw_ss() ++ boolSimps.CONJ_ss) [] >>
               metis_tac[]) >>
        first_x_assum (qspec_then `x` mp_tac) >>
        asm_simp_tac bool_ss [] >>
        simp[vsub_def]) >>
    first_x_assum (qspec_then `x` mp_tac) >>
    asm_simp_tac(srw_ss() ++ ARITH_ss)[vsub_def],

    rpt strip_tac >>
    asm_simp_tac(srw_ss() ++ ARITH_ss) [mFOR_thm, SimpLHS] >>
    `Δ ' n = do assert (n < vsz Δ); SOME(EL n Δ) od` by simp[vsub_assert] >>
    FREEZE_THEN
      (fn th => REWRITE_TAC [th])
      (update_assert |> Q.GEN `i` |> Q.GEN `v` |> Q.INST [`A` |-> `A2`]) >>
    `n < N` by decide_tac >>
    `EL n Δ < LENGTH A1` by metis_tac[DECIDE ``x < y ∧ y ≤ z ⇒ x < z``] >>
    asm_simp_tac (srw_ss() ++ ARITH_ss) [] >>
    qpat_assum `SOME final = XX` (ASSUME_TAC o SYM) >> simp[] >>
    first_x_assum match_mp_tac >> simp[] >> rpt strip_tac >>
    asm_simp_tac(srw_ss() ++ ARITH_ss ++ boolSimps.CONJ_ss)[vsub_assert] >>
    Cases_on `i = EL n Δ` >> simp[]
    >- (reverse (rw[]) >- metis_tac[DECIDE ``n < n + 1``] >>
        simp[listTheory.EL_LUPDATE]) >>
    Cases_on `∃j. i = EL j Δ ∧ j < n + 1`
    >- (simp[] >> pop_assum strip_assume_tac >>
        `j < n` by metis_tac[DECIDE ``x < y + 1 ⇔ x < y ∨ x = y``] >> simp[] >>
        `i ∈ IMAGE (THE o $' Δ) (count n)`
          by (simp[vsub_assert] >> acsimp[] >> metis_tac[]) >>
        first_x_assum (qspec_then `i` mp_tac) >>
        asm_simp_tac bool_ss [] >>
        simp[vsub_def, listTheory.EL_LUPDATE]) >>
    simp[] >>
    `i ∉ IMAGE (THE o $' Δ) (count n)`
      by (simp[vsub_def] >> qx_gen_tac `j` >> Cases_on `j < n` >> simp[] >>
          metis_tac[DECIDE ``j < n ⇒ j < n + 1``]) >>
    first_x_assum (qspec_then `i` mp_tac) >> bsimp[] >>
    simp[vsub_def, listTheory.EL_LUPDATE]
  ]);

val PERMS_SUFFICE_simple = save_thm(
  "PERMS_SUFFICE_simple",
  PERMS_suffice0 |> SIMP_RULE (srw_ss()) []
                 |> UNDISCH
                 |> Q.SPECL [`0`, `A1`]
                 |> SIMP_RULE (srw_ss()) []
                 |> DISCH_ALL
                 |> Q.INST [`A1` |-> `A`]);

val _ = export_theory();
