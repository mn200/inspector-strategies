open HolKernel Parse boolLib bossLib;

open pred_setTheory listTheory pairTheory
open lcsymtacs
open actionTheory
open bagTheory
open quotientLib
open indexedListsTheory

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
  gentouches rf1 wf1 rf2 wf2 g1 g2 ⇔
    (∃w. w ∈ wf1 g1 ∧ w ∈ wf2 g2) ∨
    (∃w. w ∈ wf1 g1 ∧ w ∈ rf2 g2) ∨
    (∃w. w ∈ wf2 g2 ∧ w ∈ rf1 g1)
`;

val _ = overload_on ("sgentouches", ``λrf wf. gentouches rf wf rf wf``)

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
         ¬htouches0 m n ∧ ¬sgentouches nrr nrw mr nr ⇒
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

val hinode_ind = store_thm(
  "hinode_ind",
  ``∀P. (∀a. P (HD a)) ∧ (∀g. P (HG g)) ⇒
        ∀n:(α,β)hinode. P n``,
  ntac 2 strip_tac >>
  `(∀n. P n) ∧ (∀g:(α,β)hidag. T)` suffices_by metis_tac[] >>
  ho_match_mp_tac hidag_ind >> simp[]);

val hinode_ax = store_thm(
  "hinode_ax",
  ``∀(f0 : (α,β)node -> γ) f1.
     ∃fn. (∀a. fn (HD a) = f0 a) ∧
          (∀g. fn (HG g) = f1 g)``,
  rpt strip_tac >>
  qspecl_then [`ARB`, `λn g nr gr. ARB`, `λg gr. f1 g`,
               `λa. f0 a`, `K ∅`, `K ∅`, `K ∅`, `K ∅`]
    (strip_assume_tac o SIMP_RULE (srw_ss()) [])
    (INST_TYPE [delta |-> gamma] hidag_recursion) >>
  metis_tac[]);

val hinode_CASE_def = new_specification(
  "hinode_CASE_def", ["hinode_CASE"],
  hinode_ax
    |> INST_TYPE [gamma |-> ``:((α,β)node -> γ) -> ((α,β)hidag -> γ) -> γ``]
    |> Q.SPECL [`λa f1 f2. f1 a`, `λg f1 f2. f2 g`]
    |> SIMP_RULE bool_ss [FUN_EQ_THM]);

val _ = TypeBase.write (
          TypeBasePure.gen_datatype_info { ax = hinode_ax,
                                           case_defs = [hinode_CASE_def],
                                           ind = hinode_ind }
        )

val _ = adjoin_to_theory
          {sig_ps = NONE,
           struct_ps = SOME (fn pps =>
            (PP.add_string pps
             "val _ = TypeBase.write (\n\
             \  TypeBasePure.mk_nondatatype_info (\n\
             \    Type.mk_thy_type{Args = [alpha,beta], Thy = \"hidag\", Tyop = \"hidag\"},\n\
             \    {encode = NONE, induction = SOME hidag_ind0,\n\
             \     nchotomy = SOME hidag_nchotomy, size = NONE}) ::\n\
             \  TypeBasePure.gen_datatype_info {\n\
             \    ax = hinode_ax, case_defs = [hinode_CASE_def], ind = hinode_ind})";
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
  ``sgentouches nreads nwrites = htouches``,
  simp[gentouches_def, htouches_def, FUN_EQ_THM]);

val _ = overload_on("gtouches", ``sgentouches greads gwrites``)
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

val hidagAdd_EQ_sing = store_thm(
  "hidagAdd_EQ_sing[simp]",
  ``a <+ ε = b <+ g ⇔ a = b ∧ g = ε``,
  simp[EQ_IMP_THM] >> disch_then (mp_tac o Q.AP_TERM `hnodebag`) >>
  simp[]);

val hdmerge_EQ_sing = store_thm(
  "hdmerge_EQ_sing",
  ``a <+ ε = g1 ⊕ g2 ⇔ g1 = a <+ ε ∧ g2 = ε ∨ g1 = ε ∧ g2 = a <+ ε``,
  map_every qid_spec_tac [`a`, `g2`, `g1`] >> Induct >> simp[] >> metis_tac[])

val hdmerge_ASSOC = store_thm(
  "hdmerge_ASSOC",
  ``∀g1 g2 g3. g1 ⊕ (g2 ⊕ g3) = (g1 ⊕ g2) ⊕ g3``,
  Induct >> simp[]);

val greads_merge = store_thm(
  "greads_merge[simp]",
  ``∀g1 g2. greads (g1 ⊕ g2) = greads g1 ∪ greads g2``,
  Induct >> simp[AC UNION_COMM UNION_ASSOC]);
val gwrites_merge = store_thm(
  "gwrites_merge[simp]",
  ``∀g1 g2. gwrites (g1 ⊕ g2) = gwrites g1 ∪ gwrites g2``,
  Induct >> simp[AC UNION_COMM UNION_ASSOC]);

val hdmerge_empty = store_thm(
  "hdmerge_empty[simp]",
  ``∀g. g ⊕ ε = g``,
  Induct >> simp[]);

val _ = overload_on("ngtouches", ``gentouches nreads nwrites greads gwrites``)

val ngtouches_thm = store_thm(
  "ngtouches_thm[simp]",
  ``(ngtouches n ε ⇔ F) ∧
    (ngtouches n1 (n2 <+ g) ⇔ n1 ∼ₜ n2 ∨ ngtouches n1 g)``,
  simp[gentouches_def, htouches_def] >> metis_tac[]);

val hidagAdd_gtouches = store_thm(
  "hidagAdd_gtouches[simp]",
  ``∀g2 a g1.
      (a <+ g1 ∼ᵍ g2 ⇔
       g1 ∼ᵍ g2 ∨ gentouches nreads nwrites greads gwrites a g2) ∧
      (g2 ∼ᵍ a <+ g1 ⇔
       g1 ∼ᵍ g2 ∨ gentouches nreads nwrites greads gwrites a g2)``,
  simp[gentouches_def] >> rw[] >> metis_tac[]);

val add_front_to_back = store_thm(
  "add_front_to_back",
  ``∀g a. ¬ngtouches a g ⇒
          a <+ g = g ⊕ (a <+ ε)``,
  Induct >> simp[] >> metis_tac[hidagAdd_commutes]);

val hdmerge_COMM = store_thm(
  "hdmerge_COMM",
  ``∀g1 g2. ¬(g1 ∼ᵍ g2) ⇒ g1 ⊕ g2 = g2 ⊕ g1``,
  Induct >> simp[] >> metis_tac[hdmerge_def, add_front_to_back, hdmerge_ASSOC])

val flatten_lemma = prove(
  ``¬(mr ∼ᵍ nr) ⇒ mr ⊕ (nr ⊕ g) = nr ⊕ (mr ⊕ g)``,
  metis_tac[hdmerge_COMM, hdmerge_ASSOC]);

val gflatten_def = new_specification(
  "gflatten_def", ["gflatten", "nflatten"],
  hidag_recursion |> INST_TYPE [gamma |-> ``:('a,'b)hidag``,
                                delta |-> ``:('a,'b)hidag``]
                  |> Q.SPECL [`ε`, `λn g nr gr. hdmerge nr gr`,
                              `λg gr. gr`, `λa. HD a <+ ε`,
                              `greads`, `gwrites`, `greads`,`gwrites`]
                  |> SIMP_RULE (srw_ss()) []
                  |> SIMP_RULE (srw_ss()) [SUBSET_DEF]
                  |> SIMP_RULE (srw_ss()) [Once flatten_lemma])
val _ = export_rewrites ["gflatten_def"]

val greads_gflatten = store_thm(
  "greads_gflatten[simp]",
  ``(∀n:(α,β)hinode. greads (nflatten n) = nreads n) ∧
    (∀g:(α,β)hidag. greads (gflatten g) = greads g)``,
  ho_match_mp_tac hidag_ind >> simp[]);

val gwrites_gflatten = store_thm(
  "gwrites_gflatten[simp]",
  ``(∀n:(α,β)hinode. gwrites (nflatten n) = nwrites n) ∧
    (∀g:(α,β)hidag. gwrites (gflatten g) = gwrites g)``,
  ho_match_mp_tac hidag_ind >> simp[]);


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

val _ = overload_on ("hdsize", ``λd. BAG_CARD (hnodebag d)``)

val hdsize_EQ0 = store_thm(
  "hdsize_EQ0[simp]",
  ``(hdsize d = 0 ⇔ d = ε) ∧ (0 = hdsize d ⇔ d = ε)``,
  Cases_on `d` >> simp[BAG_CARD_THM]);

val hdsize_hidagAdd = store_thm(
  "hdsize_hidagAdd[simp]",
  ``hdsize (a <+ d) = hdsize d + 1``,
  simp[BAG_CARD_THM]);

val hidagAdd_touches_eq = store_thm(
  "hidagAdd_touches_eq",
  ``a1 <+ g1 = a2 <+ g2 ⇒ a1 = a2 ∨ a1 ≁ₜ a2``,
  Cases_on `a1 ∼ₜ a2` >> simp[] >>
  Cases_on `a1 = a2` >> simp[] >>
  disch_then (mp_tac o Q.AP_TERM `wave0`) >> simp[wave0_def] >>
  fs[htouches_SYM] >> disch_then (mp_tac o Q.AP_TERM `BAG_IN a1`) >>
  simp[] >> fs[htouches_SYM]);

val hidag_commutes_EQ = store_thm(
  "hidag_commutes_EQ[simp]",
  ``a1 <+ a2 <+ g1 = a2 <+ a1 <+ g2 ⇔ (a1 ∼ₜ a2 ⇒ a1 = a2) ∧ g1 = g2``,
  eq_tac >> simp[Once hidagAdd_commutes]
  >- (strip_tac >> imp_res_tac hidagAdd_touches_eq >>
      fs[Once hidagAdd_commutes]) >>
  rw[] >> Cases_on `a1 = a2` >- simp[] >> fs[Once hidagAdd_commutes]);

val hidagAdd_11_thm = store_thm(
  "hidagAdd_11_thm",
  ``∀g1 g2 a1 a2.
      a1 <+ g1 = a2 <+ g2 ⇔
      a1 = a2 ∧ g1 = g2 ∨
      a1 ≁ₜ a2 ∧ ∃g0. g1 = a2 <+ g0 ∧ g2 = a1 <+ g0``,
  Induct_on `hdsize g1`
  >- (simp[EQ_IMP_THM] >> rpt gen_tac >>
      disch_then (mp_tac o Q.AP_TERM `hnodebag`) >> simp[]) >>
  qx_gen_tac `g1` >> Cases_on `g1` >> simp[] >>
  simp[GSYM arithmeticTheory.ADD1] >> disch_then SUBST_ALL_TAC >>
  qx_genl_tac [`g2`, `a1`, `a2`] >>
  Cases_on `a1 = a2` >> simp[]
  >- (eq_tac >> strip_tac >> simp[Once hidagAdd_commutes]) >>
  reverse eq_tac >- (rw[] >> metis_tac[hidagAdd_commutes, htouches_SYM]) >>
  strip_tac >>
  qmatch_assum_rename_tac `a1 <+ b <+ g0 = a2 <+ g2` [] >>
  Cases_on `b = a2` >> dsimp[]
  >- (rw[] >> dsimp[] >>
      `g2 = a1 <+ g0` suffices_by metis_tac[hidag_commutes_EQ] >>
      pop_assum (mp_tac o Q.AP_TERM `hddel a2`) >> simp[hddel_def]) >>
  Cases_on `a1 = b` >> rw[]
  >- (first_assum (mp_tac o Q.AP_TERM `hddel a1`) >> simp[hddel_def] >>
      disch_then (CONJUNCTS_THEN2 assume_tac
                                  (qx_choose_then `g00` strip_assume_tac)) >>
      rw[] >>
      pop_assum kall_tac >> first_x_assum (mp_tac o Q.AP_TERM `hddel a2`) >>
      simp[hddel_def]) >>
  first_assum (mp_tac o Q.AP_TERM `hddel a2`) >> simp[hddel_def] >>
  disch_then (SUBST_ALL_TAC o SYM) >>
  qexists_tac `hddel a2 g0` >> simp[] >>
  `a1 ≁ₜ a2` by metis_tac[hidagAdd_touches_eq] >>
  `b <+ g0 = a2 <+ b <+ hddel a2 g0`
    by metis_tac[hidagAdd_commutes, hidagAdd_11] >>
  `b ≁ₜ a2` by metis_tac[hidagAdd_touches_eq] >>
  metis_tac[hidagAdd_11, hidagAdd_commutes]);

val _ = overload_on("-", ``λd b. ITBAG hddel b d``)

val hddel_commutes = store_thm(
  "hddel_commutes",
  ``∀a b d. hddel a (hddel b d) = hddel b (hddel a d)``,
  Induct_on `d` >> simp[hddel_def] >> rw[] >> rw[hddel_def]);

val dagsubtract_BAG_INSERT = store_thm(
  "dagsubtract_BAG_INSERT",
  ``FINITE_BAG b ⇒ (d - BAG_INSERT a b = hddel a d - b)``,
  simp[COMMUTING_ITBAG_INSERT, hddel_commutes])

val wave0_elements_dont_touch = store_thm(
  "wave0_elements_dont_touch",
  ``∀d a b w0. wave0 d = BAG_INSERT a (BAG_INSERT b w0) ⇒ a ≁ₜ b``,
  Induct_on `d` >> simp[] >> qx_gen_tac `d` >> strip_tac >>
  simp[wave0_def] >> qx_genl_tac [`c`, `a`, `b`, `w0`] >>
  Cases_on `c = a` >> simp[]
  >- (disch_then (mp_tac o Q.AP_TERM  `BAG_IN b`) >> simp[] >>
      simp[htouches_SYM]) >>
  Cases_on `c = b` >> simp[]
  >- (disch_then (mp_tac o Q.AP_TERM `BAG_IN a`) >> simp[] >>
      metis_tac[htouches_SYM]) >>
  dsimp[BAG_INSERT_EQUAL] >> qx_gen_tac `w00` >> rw[] >>
  first_x_assum match_mp_tac >> qexists_tac `wave0 d - {| a; b |}` >>
  `a ≁ₜ c` by (first_x_assum (mp_tac o Q.AP_TERM `BAG_IN a`) >> simp[]) >>
  `BAG_IN a (wave0 d)`
    by (first_x_assum (mp_tac o Q.AP_TERM `BAG_IN a`) >> simp[]) >>
  `{| a; b |} ≤ wave0 d`
    by (`∃w1. wave0 d = BAG_INSERT a w1` by metis_tac[BAG_DECOMPOSE] >>
        simp[SUB_BAG_INSERT] >> fs[] >>
        qpat_assum `BAG_FILTER P XX = YY`
                   (mp_tac o Q.AP_TERM `BAG_IN b`) >> simp[]) >>
  simp[GSYM BAG_DIFF_INSERT_SUB_BAG] >>
  simp[Once BAG_INSERT_commutes] >>
  `{|a|} ≤ wave0 d` by simp[] >>
  simp[GSYM BAG_DIFF_INSERT_SUB_BAG])

val wave_def = Define`
  (wave 0 d = wave0 d) ∧
  (wave (SUC n) d = wave n (d - wave0 d))
`;
val _ = overload_on ("waveset", ``λn d. SET_OF_BAG (wave n d)``)

val wave_elements_dont_touch = store_thm(
  "wave_elements_dont_touch",
  ``∀n d a b w0.
      wave n d = BAG_INSERT a (BAG_INSERT b w0) ⇒ a ≁ₜ b``,
  Induct >> simp[wave_def] >> metis_tac[wave0_elements_dont_touch]);

val waveset_elements_dont_touch = store_thm(
  "waveset_elements_dont_touch",
  ``∀n a b d.
      a ∈ waveset n d ∧ b ∈ waveset n d ∧ a ≠ b ⇒ a ≁ₜ b``,
  simp[] >> rpt strip_tac >>
  `∃w1. wave n d = BAG_INSERT a w1` by metis_tac[BAG_DECOMPOSE] >>
  `BAG_IN b w1`
    by (pop_assum (mp_tac o Q.AP_TERM `BAG_IN b`) >> simp[]) >>
  `∃w2. w1 = BAG_INSERT b w2` by metis_tac[BAG_DECOMPOSE] >> rw[] >>
  metis_tac[wave_elements_dont_touch]);

val hnodebag_hddel = store_thm(
  "hnodebag_hddel[simp]",
  ``hnodebag (hddel a d) = hnodebag d - {|a|}``,
  Induct_on `d` >> simp[hddel_def] >> rw[] >> rw[] >>
  simp[BAG_DIFF_INSERT]);

val hnodebag_subtraction = store_thm(
  "hnodebag_subtraction",
  ``b ≤ hnodebag d ⇒ hnodebag (d - b) = hnodebag d - b``,
  strip_tac >>
  `FINITE_BAG b` by metis_tac[FINITE_SUB_BAG, FINITE_hnodebag] >>
  Q.UNDISCH_THEN `b ≤ hnodebag d` mp_tac >> qid_spec_tac `d` >>
  pop_assum mp_tac >> qid_spec_tac `b` >>
  Induct_on `FINITE_BAG` >> simp[dagsubtract_BAG_INSERT, hnodebag_hddel] >>
  rpt strip_tac >>
  `b ≤ hnodebag d - {|e|}`
    suffices_by simp[BAG_DIFF_2L, BAG_UNION_INSERT] >>
  imp_res_tac BAG_INSERT_SUB_BAG_E >>
  simp[SUB_BAG_UNION_DIFF, BAG_UNION_INSERT])

val dagsize_subtraction = store_thm(
  "dagsize_subtraction",
  ``b ≤ hnodebag d ⇒ hdsize (d - b) = hdsize d - BAG_CARD b``,
  simp[hnodebag_subtraction, BAG_CARD_DIFF]);

val wave0_subbag = store_thm(
  "wave0_subbag[simp]",
  ``∀d. wave0 d ≤ hnodebag d``,
  Induct >> simp[]);

val wave_subbag = store_thm(
  "wave_subbag[simp]",
  ``∀n d. wave n d ≤ hnodebag d``,
  Induct >> simp[wave_def] >> qx_gen_tac `d` >>
  pop_assum (qspec_then `d - wave0 d` strip_assume_tac) >>
  `hnodebag (d - wave0 d) ≤ hnodebag d`
    suffices_by metis_tac[SUB_BAG_TRANS] >>
  simp[hnodebag_subtraction]);

val wavedepth_def = tDefine "wavedepth" `
  wavedepth d = if d = ε then 0
                else wavedepth (d - wave0 d) + 1
` (WF_REL_TAC `measure hdsize` >> simp[dagsize_subtraction] >>
   Cases >> simp[wave0_def, BAG_CARD_THM])

val wavedepth_empty = store_thm(
  "wavedepth_empty[simp]",
  ``wavedepth ε = 0 ∧ (wavedepth d = 0 ⇔ d = ε) ∧
    (0 = wavedepth d ⇔ d = ε)``,
  rpt conj_tac >> simp[Once wavedepth_def] >>
  Cases_on `d` >> simp[]);

val IN_hddel_I = store_thm(
  "IN_hddel_I",
  ``a ∈ d ∧ a ≠ e ⇒ a ∈ hddel e d``,
  simp[BAG_IN_DIFF_I, hnodebag_hddel]);

val BAG_IN_subtraction_I = store_thm(
  "BAG_IN_subtraction_I",
  ``∀d a b. FINITE_BAG b ∧ a ∈ d ∧ ¬BAG_IN a b ⇒ a ∈ d - b``,
  `∀b. FINITE_BAG b ⇒ ∀a d. a ∈ d ∧ ¬BAG_IN a b ⇒ a ∈ d - b`
    suffices_by metis_tac[] >>
  Induct_on `FINITE_BAG` >> simp[dagsubtract_BAG_INSERT] >>
  rpt strip_tac >>
  simp[hnodebag_subtraction, IN_hddel_I])

val waves_cover_all_nodes = store_thm(
  "waves_cover_all_nodes",
  ``∀d a. a ∈ d ⇒ ∃n. BAG_IN a (wave n d)``,
  gen_tac >> completeInduct_on `hdsize d` >> qx_gen_tac `d` >>
  strip_tac >> Cases_on `d = ε` >> simp[] >> qx_gen_tac `a` >>
  Cases_on `BAG_IN a (wave 0 d)` >- metis_tac[] >> strip_tac >>
  Q.REFINE_EXISTS_TAC `SUC n` >> simp[wave_def] >>
  fs[PULL_FORALL, AND_IMP_INTRO] >> first_x_assum match_mp_tac >>
  fs[dagsize_subtraction, BAG_IN_subtraction_I, wave_def] >>
  Cases_on `d` >> lfs[wave0_def, BAG_CARD_THM]);

val waves_become_empty = store_thm(
  "waves_become_empty",
  ``∀d. ∃n. wave n d = {||} ∧ ∀m. n < m ⇒ wave m d = {||}``,
  gen_tac >> completeInduct_on `hdsize d` >> qx_gen_tac `d` >>
  strip_tac >> Cases_on `d = ε` >> simp[]
  >- (qexists_tac `0` >> simp[wave_def] >> rpt (pop_assum kall_tac) >>
      Induct >> simp[wave_def] >> Cases_on `m` >- simp[wave_def] >>
      simp[]) >>
  Q.REFINE_EXISTS_TAC `SUC n` >> simp[wave_def] >>
  fs[PULL_FORALL, AND_IMP_INTRO] >>
  first_assum (qspec_then `d - wave0 d` mp_tac) >>
  simp_tac (srw_ss()) [dagsize_subtraction] >>
  `0 < BAG_CARD (wave0 d) ∧ 0 < hdsize d`
    by (Cases_on `d` >> lfs[BAG_CARD_THM, wave0_def]) >>
  simp[] >> disch_then (qx_choose_then `n` strip_assume_tac) >>
  fs[FORALL_AND_THM] >> qexists_tac `n` >> simp[] >> Cases >> simp[] >>
  simp[wave_def])

val wavedepth_preds_nonempty = store_thm(
  "wavedepth_preds_nonempty",
  ``∀d n. n < wavedepth d ⇒ wave n d ≠ {||}``,
  gen_tac >> completeInduct_on `hdsize d` >>
  fs[PULL_FORALL, AND_IMP_INTRO] >> rw[] >>
  Cases_on `n` >> simp[wave_def]
  >- (strip_tac >> fs[]) >>
  first_x_assum match_mp_tac >>
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [wavedepth_def]) >>
  Cases_on `d = ε` >> lfs[] >>
  simp[dagsize_subtraction] >> Cases_on `d` >>
  simp[BAG_CARD_THM, wave0_def] >> fs[])

val wavedepth_empty = store_thm(
  "wavedepth_empty[simp]",
  ``∀d. wave (wavedepth d) d = {||}``,
  gen_tac >> completeInduct_on `hdsize d` >>
  fs[PULL_FORALL, AND_IMP_INTRO] >> rw[] >>
  Cases_on `d = ε` >> simp[wave_def] >>
  simp[Once wavedepth_def, wave_def, GSYM arithmeticTheory.ADD1] >>
  first_x_assum match_mp_tac >>
  simp[dagsize_subtraction] >>
  Cases_on `d` >> lfs[BAG_CARD_THM, wave0_def])

val wavedepth_LEAST = store_thm(
  "wavedepth_LEAST",
  ``wavedepth d = LEAST n. wave n d = {||}``,
  numLib.LEAST_ELIM_TAC >> conj_tac
  >- metis_tac[wavedepth_empty] >> rpt strip_tac >>
  `¬(wavedepth d < n) ∧ ¬(n < wavedepth d)` suffices_by simp[] >>
  rpt strip_tac >> metis_tac[wavedepth_empty, wavedepth_preds_nonempty]);

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

val _ = overload_on("hdbuild", ``FOLDR hidagAdd ε``)

val IN_hdbuild = store_thm(
  "IN_hdbuild[simp]",
  ``∀ns a. a ∈ hdbuild ns ⇔ MEM a ns``,
  Induct >> simp[]);

val move_nontouching_hdbuild_front = store_thm(
  "move_nontouching_hdbuid_front",
  ``∀n l. n < LENGTH l ∧ (∀i. i < n ⇒ EL i l ≁ₜ EL n l) ⇒
          hdbuild l = hdbuild (EL n l :: delN n l)``,
  Induct >- (Cases >> simp[delN_def]) >> dsimp[LT_SUC] >>
  qx_gen_tac `l` >> strip_tac >>
  `∃h t. l = h::t` by (Cases_on `l` >> fs[]) >> rw[] >>
  simp[delN_def] >> fs[])

val _ = export_theory();
