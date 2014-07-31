open HolKernel Parse boolLib bossLib;

open pred_setTheory listTheory pairTheory
open lcsymtacs
open actionTheory
open bagTheory
open quotientLib

val _ = new_theory "hidag";

val _ = type_abbrev("node", ``:(β,α,unit)action``)

val _ = Datatype`hn0 = HD0 ((α,β) node) | HG0 hg0 ;
                 hg0 = emptyHDG0 | hadd0 hn0 hg0`

val greads0_def = Define`
  greads0 emptyHDG0 = ∅ ∧
  greads0 (hadd0 n g) = nreads0 n ∪ greads0 g ∧
  nreads0 (HD0 n) = set n.reads ∧
  nreads0 (HG0 g) = greads0 g
`;

val gwrites0_def = Define`
  gwrites0 emptyHDG0 = ∅ ∧
  gwrites0 (hadd0 n g) = nwrites0 n ∪ gwrites0 g ∧
  nwrites0 (HD0 n) = set n.writes ∧
  nwrites0 (HG0 g) = gwrites0 g
`;

val htouches0_def = Define`
  htouches0 n1 n2 ⇔
    (∃w. w ∈ nwrites0 n1 ∧ w ∈ nwrites0 n2) ∨
    (∃w. w ∈ nwrites0 n1 ∧ w ∈ nreads0 n2) ∨
    (∃w. w ∈ nwrites0 n2 ∧ w ∈ nreads0 n1)
`;


val (heq_rules, heq_ind, heq_cases) = Hol_reln`
  (heq emptyHDG0 emptyHDG0) ∧
  (∀n1 n2 g1 g2.
     neq n1 n2 ∧ heq g1 g2 ⇒
     heq (hadd0 n1 g1) (hadd0 n2 g2)) ∧
  (∀g1 g2. heq g1 g2 ⇒ heq g2 g1) ∧
  (∀g1 g2 g3. heq g1 g2 ∧ heq g2 g3 ⇒ heq g1 g3) ∧
  (∀n1 n2 g. ¬htouches0 n1 n2 ⇒
             heq (hadd0 n1 (hadd0 n2 g)) (hadd0 n2 (hadd0 n1 g))) ∧

  (∀n. neq n n) ∧
  (∀n1 n2. neq n1 n2 ⇒ neq n2 n1) ∧
  (∀n1 n2 n3. neq n1 n2 ∧ neq n2 n3 ⇒ neq n1 n3) ∧
  (∀g1 g2. heq g1 g2 ⇒ neq (HG0 g1) (HG0 g2))
`;

val neq_refl = List.nth(CONJUNCTS heq_rules, 5)
val heq_refl = prove(
  ``(∀g. heq g g)``,
  Induct >> metis_tac[heq_rules]);

val heq_sym = List.nth(CONJUNCTS heq_rules, 2)
val heq_trans = List.nth (CONJUNCTS heq_rules, 3)

val heq_equiv = prove(
  ``∀g1 g2. heq g1 g2 ⇔ (heq g1 = heq g2)``,
  simp[FUN_EQ_THM] >> metis_tac[heq_refl, heq_sym, heq_trans]);
val hadd0_commutes = List.nth(CONJUNCTS heq_rules, 4)

val neq_equiv = prove(
  ``∀n1 n2. neq n1 n2 ⇔ (neq n1 = neq n2)``,
  simp[FUN_EQ_THM] >> metis_tac[heq_rules]);

val ax = TypeBase.axiom_of ``:(α,β)hn0``
            |> INST_TYPE [gamma |-> delta, delta |-> gamma]
            |> Q.SPEC `df`
            |> Q.SPEC `gf`
            |> Q.SPEC `e`
            |> Q.SPEC `af`
            |> BETA_RULE

val gtouches0_def = Define`
  gtouches0 g1 g2 ⇔
    (∃w. w ∈ gwrites0 g1 ∧ w ∈ gwrites0 g2) ∨
    (∃w. w ∈ gwrites0 g1 ∧ w ∈ greads0 g2) ∨
    (∃w. w ∈ gwrites0 g2 ∧ w ∈ greads0 g1)
`;

val gentouches_def = Define`
  gentouches rf wf g1 g2 ⇔
    (∃w. w ∈ wf g1 ∧ w ∈ wf g2) ∨
    (∃w. w ∈ wf g1 ∧ w ∈ rf g2) ∨
    (∃w. w ∈ wf g2 ∧ w ∈ rf g1)
`;

val recursion = prove(
  ``∀   (e : γ)
        (af :: respects (neq ===> heq ===> (=) ===> (=)))
        (gf :: respects (heq ===> (=) ===> (=)))
        (df : (α,β)node -> δ)
        (nrr : δ -> α -> bool)
        (nrw : δ -> α -> bool)
        (grr : γ -> α -> bool)
        (grw : γ -> α -> bool).
      (∀m : (α,β)node. nrr (df m) ⊆ set m.reads) ∧
      (∀m : (α,β)node. nrw (df m) ⊆ set m.writes) ∧
      (∀g : (α,β)hg0 gr : γ. grr gr ⊆ greads0 g ⇒ nrr (gf g gr) ⊆ greads0 g) ∧
      (∀g : (α,β)hg0 gr : γ. grw gr ⊆ gwrites0 g ⇒ nrw (gf g gr) ⊆ gwrites0 g) ∧

      (∀n : (α,β)hn0 g:(α,β)hg0 nr:δ gr:γ.
        grr gr ⊆ greads0 g ∧ nrr nr ⊆ nreads0 n ⇒
        grr (af n g nr gr) ⊆ nreads0 n ∪ greads0 g) ∧
      (∀n : (α,β)hn0 g:(α,β)hg0 nr:δ gr:γ.
        grw gr ⊆ gwrites0 g ∧ nrw nr ⊆ nwrites0 n ⇒
        grw (af n g nr gr) ⊆ nwrites0 n ∪ gwrites0 g) ∧
      grr e = ∅ ∧ grw e = ∅ ∧

      (∀m n mr nr g r.
         ¬htouches0 m n ∧ ¬gentouches nrr nrw mr nr ⇒
           af m (hadd0 n g) mr (af n g nr r) =
           af n (hadd0 m g) nr (af m g mr r)) ⇒
      ∃(hf :: respects (heq ===> (=)))
       (nf :: respects (neq ===> ((=) : δ -> δ -> bool))).
        hf emptyHDG0 = e ∧
        (∀n g. hf (hadd0 n g : (α,β)hg0) = af n g (nf n : δ) (hf g) : γ) ∧
        (∀n. nf (HD0 n : (α,β)hn0) = df n : δ) ∧
        (∀g. nf (HG0 g) = gf g (hf g))``,
  simp[respects_def, combinTheory.W_DEF, RES_EXISTS_THM, FUN_REL,
       RES_FORALL_THM] >>
  rpt strip_tac >>
  qx_choosel_then [`nfn`, `hfn`] strip_assume_tac ax >>
  qexists_tac `hfn` >> simp[] >>
  `(∀n. nrr (nfn n) ⊆ nreads0 n ∧ nrw (nfn n) ⊆ nwrites0 n) ∧
   (∀g. grr (hfn g) ⊆ greads0 g ∧ grw (hfn g) ⊆ gwrites0 g)`
    by (ho_match_mp_tac (TypeBase.induction_of ``:(α,β)hg0``) >>
        simp[greads0_def, gwrites0_def]) >>
  `(∀g1 g2. heq g1 g2 ⇒ hfn g1 = hfn g2) ∧
   (∀n1 n2. neq n1 n2 ⇒ nfn n1 = nfn n2)`
    by (Induct_on `heq` >> simp[] >> rpt strip_tac
        >- fs[FUN_EQ_THM] >>
        first_x_assum match_mp_tac >> simp[] >>
        simp[gentouches_def] >> fs[htouches0_def] >>
        metis_tac[SUBSET_DEF]) >>
  simp[] >> qexists_tac `nfn` >> simp[])

val hadd0_rsp = List.nth(CONJUNCTS heq_rules, 1)
val HG0_rsp = last (CONJUNCTS heq_rules)

fun define_quotient {types,defs,thms,poly_preserves,poly_respects,respects} =
    let
      fun mk(s,t) = {def_name = s ^ "_def", fname = s, fixity = NONE, func = t}
      val (names, old_thms) = ListPair.unzip thms
      val new_thms =
          quotientLib.define_quotient_types_full {
            types = types, defs = map mk defs, old_thms = old_thms,
            poly_respects = poly_respects, poly_preserves = poly_preserves,
            respects = respects, tyop_equivs = [],
            tyop_quotients = [], tyop_simps = []}
      val named_new = ListPair.zip(names, new_thms)
    in
      map save_thm named_new
    end

val neq_pull_hg = prove(
  ``(∀g1:(α,β)hg0 g2. heq g1 g2 ⇒ T) ∧
    (∀n1:(α,β)hn0 n2.
       neq n1 n2 ⇒
       (∀g1. n1 = HG0 g1 ⇒ ∃g2. n2 = HG0 g2 ∧ heq g1 g2) ∧
       (∀g2. n2 = HG0 g2 ⇒ ∃g1. n1 = HG0 g1 ∧ heq g1 g2))``,
  Induct_on `heq` >> simp[] >> rpt strip_tac >> rw[] >>
  metis_tac[heq_rules, heq_refl])
    |> CONJUNCT2
    |> SIMP_RULE (srw_ss()) [IMP_CONJ_THM, FORALL_AND_THM,
                             GSYM RIGHT_FORALL_IMP_THM]

val HG0_11 = prove(
  ``neq (HG0 g1) (HG0 g2) ⇔ heq g1 g2``,
  simp[EQ_IMP_THM, HG0_rsp] >> strip_tac >>
  imp_res_tac (CONJUNCT1 neq_pull_hg) >> fs[]);

val neq_pull_hd = prove(
  ``(∀g1:(α,β)hg0 g2. heq g1 g2 ⇒ T) ∧
    (∀n1:(α,β)hn0 n2.
       neq n1 n2 ⇒
       (∀a1. n1 = HD0 a1 ⇒ n2 = HD0 a1) ∧
       (∀a2. n2 = HD0 a2 ⇒ n1 = HD0 a2))``,
  Induct_on `heq` >> simp[])
   |> CONJUNCT2
   |> SIMP_RULE (srw_ss()) [IMP_CONJ_THM, FORALL_AND_THM,
                            GSYM RIGHT_FORALL_IMP_THM]

val HD0_11 = prove(
  ``neq (HD0 n1) (HD0 n2) ⇔ n1 = n2``,
  simp[EQ_IMP_THM, neq_refl] >> strip_tac >>
  imp_res_tac neq_pull_hd >> fs[]);

val heq_empty = prove(
  ``(∀g1:(α,β)hg0 g2.
      heq g1 g2 ⇒ (g1 = emptyHDG0 ⇔ g2 = emptyHDG0)) ∧
    (∀n1:(α,β)hn0 n2. neq n1 n2 ⇒ T)``,
  Induct_on `heq` >> simp[]) |> CONJUNCT1

val empty_not_hadd0 = prove(
  ``¬heq emptyHDG0 (hadd0 a d)``,
  strip_tac >> imp_res_tac heq_empty >> fs[]);

val HD_not_HG0 = prove(
  ``¬neq (HD0 n) (HG0 g)``,
  strip_tac >> imp_res_tac neq_pull_hd >> fs[]);

val gnrws0_rsp0 = prove(
  ``(∀g1 : (α,β)hg0 g2.
      heq g1 g2 ⇒ greads0 g1 = greads0 g2 ∧ gwrites0 g1 = gwrites0 g2) ∧
    (∀n1 : (α,β)hn0 n2.
      neq n1 n2 ⇒ nreads0 n1 = nreads0 n2 ∧ nwrites0 n1 = nwrites0 n2)``,
  Induct_on `heq` >>
  simp[greads0_def, gwrites0_def, AC UNION_ASSOC UNION_COMM])
    |> SIMP_RULE (srw_ss()) [FORALL_AND_THM, IMP_CONJ_THM,
                             GSYM RIGHT_FORALL_IMP_THM]

val (greads_rsp, gwrites_rsp, nreads_rsp, nwrites_rsp) =
    case CONJUNCTS gnrws0_rsp0 of
        [a,b,c,d] => (a,b,c,d)
      | _ => raise mk_HOL_ERR "hidagScript" "" "rws_rsp theorem failed"

val htouches_rsp = prove(
  ``neq (n1:(α,β)hn0) n1' ∧ neq (n2:(α,β)hn0) n2' ⇒
    (htouches0 n1 n2 ⇔ htouches0 n1' n2')``,
  simp[htouches0_def] >> metis_tac[nreads_rsp, nwrites_rsp]);

val gnchotomy0 = prove(
  ``∀d. heq d emptyHDG0 ∨
        ∃(n::respects neq) (d0::respects heq). heq d (hadd0 n d0)``,
  simp[RES_EXISTS_THM, respects_def, combinTheory.W_DEF] >> Cases >>
  simp[heq_refl, neq_refl] >> metis_tac[heq_refl]);

val [HG_11, HD_11, hidag_ind, empty_not_hidagadd, HD_not_HG,
     hidag_recursion, reads_thm, writes_thm, hidagAdd_commutes,
     htouches_def, hidag_nchotomy] =
define_quotient {
  types = [{name = "hidag", equiv = heq_equiv},
           {name = "hinode", equiv = neq_equiv}],
  defs = [("emptyHDG",``emptyHDG0 : (α,β)hg0``),
          ("hidagAdd", ``hadd0 : (α,β)hn0 -> (α,β) hg0 -> (α,β) hg0``),
          ("HD", ``HD0 : (α,β)node -> (α,β)hn0``),
          ("HG", ``HG0 : (α,β)hg0 -> (α,β)hn0``),
          ("htouches", ``htouches0 : (α,β)hn0 -> (α,β)hn0 -> bool``),
          ("greads", ``greads0 : (α,β)hg0 -> α set``),
          ("gwrites", ``gwrites0 : (α,β)hg0 -> α set``),
          ("nreads", ``nreads0 : (α,β)hn0 -> α set``),
          ("nwrites", ``nwrites0 : (α,β)hn0 -> α set``)],
  thms = [("HG_11[simp]", HG0_11),
          ("HD_11[simp]", HD0_11),
          ("hidag_ind", TypeBase.induction_of ``:(α,β)hg0``),
          ("empty_not_hidagAdd[simp]", empty_not_hadd0),
          ("HD_not_HG[simp]", HD_not_HG0),
          ("hidag_recursion", recursion),
          ("reads_thm[simp]", greads0_def),
          ("writes_thm[simp]", gwrites0_def),
          ("hidagAdd_commutes", hadd0_commutes),
          ("htouches_def", INST_TYPE [gamma |-> beta] htouches0_def),
          ("hidag_nchotomy", gnchotomy0)],
  poly_preserves = [],
  poly_respects = [],
  respects = [hadd0_rsp, HG0_rsp, htouches_rsp,
              greads_rsp, nreads_rsp, nwrites_rsp, gwrites_rsp]}

val _ = overload_on("ε", ``emptyHDG``)
val _ = overload_on ("touches", ``htouches``)
val _ = overload_on ("not_touches", ``λn1 n2. ¬htouches n1 n2``)
val _ = set_mapped_fixity { fixity = Infixr 501, term_name = "hidagAdd",
                            tok = "<+" }

fun firstn_conjs_under_exists n th = let
  val (v, body) = dest_exists (concl th)
  val body_th = ASSUME body
  val wanted_body = LIST_CONJ (List.take(CONJUNCTS body_th, n))
  val wanted = mk_exists(v, concl wanted_body)
  val ex_th0 = EXISTS(wanted, v) wanted_body
in
  CHOOSE(v,th) ex_th0
end

val hnodebag_def = new_specification(
  "hnodebag_def", ["hnodebag"],
  hidag_recursion
    |> INST_TYPE [gamma |-> ``:(α,β)hinode bag``, delta |-> bool]
    |> Q.SPECL[`{||}`, `λn g nr gr. BAG_INSERT n gr`, `ARB`,
               `ARB`, `K ∅`, `K ∅`, `K ∅`, `K ∅`]
    |> SIMP_RULE (srw_ss()) [BAG_INSERT_commutes, RIGHT_EXISTS_AND_THM]
    |> firstn_conjs_under_exists 2);
val _ = export_rewrites ["hnodebag_def"]

val hidag_ind0 = store_thm(
  "hidag_ind0",
  ``∀P. P ε ∧ (∀g. P g ⇒ ∀a. P (a <+ g)) ⇒ ∀g. P g``,
  metis_tac [hidag_ind |> Q.SPECL [`K T`, `P`] |> SIMP_RULE (srw_ss()) []
                       |> Q.GEN `P`]);

val _ = TypeBase.write [
  TypeBasePure.mk_nondatatype_info
          (``:(α,β)hidag``,
           {encode = NONE, induction = SOME hidag_ind0,
            nchotomy = SOME hidag_nchotomy, size = NONE})
]

val _ = adjoin_to_theory
          {sig_ps = NONE,
           struct_ps = SOME (fn pps =>
            (PP.add_string pps
             "val _ = TypeBase.write [\n\
             \  TypeBasePure.mk_nondatatype_info (\n\
             \    Type.mk_thy_type{Args = [alpha,beta], Thy = \"hidag\", Tyop = \"hidag\"},\n\
             \    {encode = NONE, induction = SOME hidag_ind0,\n\
             \     nchotomy = SOME hidag_nchotomy, size = NONE})]";
             PP.add_newline pps))}

val FINITE_hnodebag = store_thm(
  "FINITE_hnodebag[simp]",
  ``∀d. FINITE_BAG (hnodebag d)``,
  Induct >> simp[])

val _ = overload_on("IN", ``λa d. BAG_IN a (hnodebag d)``)

val hnodebag_EQ_empty = store_thm(
  "hnodebag_EQ_empty[simp]",
  ``(hnodebag d = {||} ⇔ d = ε) ∧ ({||} = hnodebag d ⇔ d = ε)``,
  Cases_on `d` >> simp[]);

val gentouches_htouches = store_thm(
  "gentouches_htouches[simp]",
  ``gentouches nreads nwrites = htouches``,
  simp[gentouches_def, htouches_def, FUN_EQ_THM]);

val _ = overload_on("gtouches", ``gentouches greads gwrites``)
val _ = set_mapped_fixity { fixity = Infix(NONASSOC, 450),
                            tok = "∼ᵍ", term_name = "gtouches" }

val hdmap_def = new_specification("hdmap_def",
  ["hdmap", "nmap"],
  hidag_recursion
    |> INST_TYPE [gamma |-> ``:(α,γ)hidag``,
                  delta |-> ``:(α,γ)hinode``]
    |> Q.SPECL [`ε`, `λn g nr gr. nr <+ gr`, `λg gr. HG gr`,
                `λn. HD (polydata_upd f n)`, `nreads`, `nwrites`,
                `greads`, `gwrites`]
    |> SIMP_RULE (srw_ss()) []
    |> SIMP_RULE (srw_ss()) [SUBSET_DEF, Once hidagAdd_commutes]
    |> Q.GEN `f` |> SIMP_RULE (srw_ss()) [SKOLEM_THM])
val _ = export_rewrites ["hdmap_def"]

val hdmerge_def = new_specification("hdmerge_def",
  ["hdmerge"],
  hidag_recursion
    |> INST_TYPE [gamma |-> ``:(α,β)hidag -> (α,β)hidag``]
    |> Q.SPECL [`λg2. g2`, `λn g nr gr g2. n <+ gr g2`, `ARB`, `ARB`,
                `K ∅`, `K ∅`, `K ∅`, `K ∅`]
    |> SIMP_RULE (srw_ss()) []
    |> SIMP_RULE (srw_ss()) [FUN_EQ_THM, Once hidagAdd_commutes]
    |> SIMP_RULE (srw_ss()) [RIGHT_EXISTS_AND_THM]
    |> firstn_conjs_under_exists 2)
val _ = export_rewrites ["hdmerge_def"]

val _ = set_mapped_fixity {fixity = Infixl 500, term_name = "hdmerge",
                           tok = "⊕"}

val hdmerge_EQ_empty = store_thm(
  "hdmerge_EQ_empty[simp]",
  ``g1 ⊕ g2 = ε ⇔ g1 = ε ∧ g2 = ε``,
  Cases_on `g1` >> simp[]);

val hdmerge_ASSOC = store_thm(
  "hdmerge_ASSOC",
  ``∀g1 g2 g3. g1 ⊕ (g2 ⊕ g3) = (g1 ⊕ g2) ⊕ g3``,
  Induct >> simp[]);

val DISJ_CONG = prove(
  ``(¬q ==> p = p') ⇒ (~p' ⇒ q = q') ⇒ (p ∨ q ⇔ p' ∨ q')``,
  decide_tac)

val hddel_def = new_specification("hddel_def",
  ["hddel"],
  hidag_recursion
    |> INST_TYPE [gamma |-> ``:(α,β)hidag``]
    |> Q.SPECL [`ε`, `λn g nr gr. if m = n then g
                                  else n <+ gr`,
                `ARB`, `ARB`, `K ∅`, `K ∅`,
                `greads`, `gwrites`]
    |> CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss() ++ boolSimps.COND_elim_ss) []))
    |> SIMP_RULE (srw_ss()) [Cong DISJ_CONG]
    |> SIMP_RULE (srw_ss()) [Once hidagAdd_commutes]
    |> SIMP_RULE (srw_ss()) [SUBSET_DEF, RIGHT_EXISTS_AND_THM]
    |> Q.GEN `m` |> SIMP_RULE (srw_ss()) [SKOLEM_THM]
    |> SIMP_RULE (srw_ss()) [FORALL_AND_THM]
    |> firstn_conjs_under_exists 2)

val hddel_simp = store_thm(
  "hddel_simp[simp]",
  ``hddel a ε = ε ∧ hddel a (a <+ d) = d``,
  simp[hddel_def]);

val hidagAdd_11 = store_thm(
  "hidagAdd_11[simp]",
  ``(a <+ g1 = a <+ g2 ⇔ g1 = g2) ∧ (a1 <+ g = a2 <+ g ⇔ a1 = a2)``,
  simp[EQ_IMP_THM] >> conj_tac
  >- (disch_then (mp_tac o Q.AP_TERM `hddel a`) >> simp[hddel_def]) >>
  disch_then (mp_tac o Q.AP_TERM `hnodebag`) >> simp[])

val BAG_FILTER_FILTER = prove(
  ``BAG_FILTER P (BAG_FILTER Q b) = BAG_FILTER (λa. P a ∧ Q a) b``,
  simp[BAG_FILTER_DEF] >> simp[FUN_EQ_THM] >> rw[] >> fs[]);

val htouches_SYM = store_thm(
  "htouches_SYM",
  ``htouches n1 n2 ⇔ htouches n2 n1``,
  simp[htouches_def] >> metis_tac[]);

val wave0_def = new_specification("wave0_def",
  ["wave0"],
  hidag_recursion
    |> INST_TYPE [gamma |-> ``:(α,β)hinode bag``]
    |> Q.SPECL [`{||}`,
                `λn g nr gr. BAG_INSERT n (BAG_FILTER (λb. ¬htouches n b) gr)`,
                `ARB`, `ARB`, `K ∅`, `K ∅`, `K ∅`, `K ∅`]
    |> SIMP_RULE (srw_ss()) [BAG_FILTER_FILTER, htouches_SYM,
                             CONJ_COMM, BAG_INSERT_commutes,
                             RIGHT_EXISTS_AND_THM]
    |> firstn_conjs_under_exists 2);

val wave0_empty = store_thm(
  "wave0_empty[simp]",
  ``wave0 ε = {||}``,
  simp[wave0_def]);

val BAG_FILTER_SUB_BAG = store_thm(
  "BAG_FILTER_SUB_BAG[simp]",
  ``∀P b. BAG_FILTER P b ≤ b``,
  dsimp[BAG_FILTER_DEF, SUB_BAG]);

val wave0_SUBBAG = store_thm(
  "wave0_SUBBAG[simp]",
  ``∀d. wave0 d ≤ hnodebag d``,
  Induct >> simp[wave0_def, SUB_BAG_INSERT] >>
  qx_gen_tac `d` >> strip_tac >> gen_tac >>
  match_mp_tac SUB_BAG_TRANS >> qexists_tac `wave0 d` >> simp[]);

val wave0_FINITE = store_thm(
  "wave0_FINITE[simp]",
  ``FINITE_BAG (wave0 d)``,
  metis_tac[FINITE_SUB_BAG, FINITE_hnodebag, wave0_SUBBAG]);

val wave0_ddel = store_thm(
  "wave0_ddel[simp]",
  ``∀d a. BAG_IN a (wave0 d) ⇒ a <+ (hddel a d) = d``,
  Induct >> simp[wave0_def] >> dsimp[] >>
  simp[hddel_def] >> rw[] >> metis_tac[hidagAdd_commutes]);

val wave0_EQ_EMPTY = store_thm(
  "wave0_EQ_EMPTY[simp]",
  ``(wave0 g = {||} ⇔ g = ε) ∧ ({||} = wave0 g ⇔ g = ε)``,
  Cases_on `g` >> simp[wave0_def]);

val allnodes_def = new_specification("allnodes_def",
  ["allnodes", "nnodes"],
  hidag_recursion
    |> INST_TYPE [gamma |-> ``:(α,β)node bag``,
                  delta |-> ``:(α,β)node bag``]
    |> Q.SPECL [`{||}`, `λn g nr gr. nr + gr`,
                `λg gr. gr`, `λn. {|n|}`, `K ∅`, `K ∅`,
                `K ∅`, `K ∅`]
    |> SIMP_RULE (srw_ss()) [AC COMM_BAG_UNION ASSOC_BAG_UNION])

(* val _ = app delete_type ["hg0", "hn0"] *)

val _ = export_theory();
