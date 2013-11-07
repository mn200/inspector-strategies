open HolKernel Parse boolLib bossLib;

open lcsymtacs

val _ = new_theory "primitives";

val FOR_def = TotalDefn.tDefine "FOR" `
  FOR (lo,hi) body A = if lo < hi then FOR (lo+1,hi) body (body lo A)
                       else A
` (WF_REL_TAC `measure (λ(lohi,b,A). SND lohi - FST lohi)`)

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

val update_def = Define`
  update (mv,sz) d r = ((d =+ r) mv, MAX sz (d + 1))
`;

val vsub_def = Define`vsub (mv,sz) d = mv d`

val _ = set_fixity "'" (Infixl 2000)
val _ = overload_on ("'", ``vsub``)

val list_to_mvector_def = Define`
  list_to_mvector l = ((λi. EL i l), LENGTH l)
`;

val mvector_to_list_def = Define`
  mvector_to_list (f,sz) = REVERSE (FOR (0,sz) (λi l. f i :: l) [])
`;

(* e.g. *)
val _ = EVAL ``mvector_to_list (list_to_mvector [1;2;3;4])``

val mvector_list_ISO = store_thm(
  "mvector_list_ISO",
  ``mvector_to_list (list_to_mvector l) = l``,
  SRW_TAC[][mvector_to_list_def, list_to_mvector_def] THEN
  `∀l A. REVERSE (FOR (0,LENGTH l) (λi l0. EL i l :: l0) A) = REVERSE A ++ l`
    suffices_by rw[] >>
  Induct_on `l` >> rw[Once FOR_def] >>
  simp_tac bool_ss [arithmeticTheory.ONE, FOR_SUC_shift] >>
  simp[]);


val _ = export_theory();
