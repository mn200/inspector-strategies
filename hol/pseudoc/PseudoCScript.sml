open HolKernel Parse boolLib bossLib;

open listTheory stringTheory
open integerTheory intLib
open realTheory
open finite_mapTheory
open lcsymtacs
open listRangeTheory
open monadsyntax boolSimps

val _ = new_theory "PseudoC";

val _ = ParseExtras.tight_equality()
val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)
val _ = overload_on ("assert", ``OPTION_GUARD``)

val _ = Datatype`
  value = Int int
        | Real real
        | Array (value list)
        | Bool bool
        | Error
`;

val isArray_def = Define`
  (isArray (Array _ : value) ⇔ T) ∧
  (isArray _ ⇔ F)
`;
val _ = export_rewrites ["isArray_def"]

val isArrayError_def = Define`
  (isArrayError Error ⇔ T) ∧
  (isArrayError (Array _) ⇔ T) ∧
  (isArrayError _ ⇔ F)
`;
val _ = export_rewrites ["isArrayError_def"]

val isArrayError_DISJ_EQ = store_thm(
  "isArrayError_DISJ_EQ",
  ``isArrayError v ⇔ v = Error ∨ isArray v``,
  Cases_on `v` >> simp[]);

val destInt_def = Define`
  destInt (Int i) = i
`;
val _ = export_rewrites ["destInt_def"]

val _ = Datatype`
  expr = MAccess maccess
       | Opn (value list -> value) (expr list)
       | Value value ;
  maccess = VRead string
          | ASub maccess expr
`
val expr_size_def = definition "expr_size_def"

val isValue_def = Define`
  isValue (Value _) = T ∧
  isValue _ = F
`
val _ = export_rewrites ["isValue_def"]


val _ = Datatype`domain = D expr expr`  (* lo/hi pair *)
val FORALL_domain = store_thm(
  "FORALL_domain",
  ``(∀d. P d) ⇔ ∀e1 e2. P (D e1 e2)``,
  simp[EQ_IMP_THM] >> strip_tac >> Cases >> simp[]);

val _ = Datatype`dexpr = DMA maccess | DValue value`
val destDValue_def = Define`
  destDValue (DValue (Array _)) = Error ∧
  destDValue (DValue v) = v ∧
  destDValue (DMA _) = Error
`;
val _ = export_rewrites ["destDValue_def"]

val isDValue_def = Define`
  isDValue (DValue v) = ¬isArrayError v ∧
  isDValue (DMA _) = F
`
val _ = export_rewrites ["isDValue_def"]


val _ = type_abbrev ("vname", ``:string``)
val _ = disable_tyabbrev_printing "vname"
val _ = type_abbrev ("memory", ``:vname |-> value``)

val _ = Datatype`
  stmt = Assign maccess (dexpr list) (value list -> value)
       | IfStmt expr stmt stmt
       | Malloc vname expr value
       | ForLoop vname domain stmt
       | ParLoop vname domain stmt
       | Seq (stmt list)
       | Par (stmt list)
       | Local vname expr stmt
       | Label value stmt
       | Abort
       | Done
`
val stmt_size_def = definition "stmt_size_def"

val stmt_induction = store_thm(
  "stmt_induction",
  ``∀P.
     (∀w ds vf. P (Assign w ds vf)) ∧
     (∀g t e. P t ∧ P e ⇒ P (IfStmt g t e)) ∧
     (∀nm e value. P (Malloc nm e value)) ∧
     (∀s d stmt. P stmt ⇒ P (ForLoop s d stmt)) ∧
     (∀s d stmt. P stmt ⇒ P (ParLoop s d stmt)) ∧
     (∀stmts. (∀m s. MEM s stmts ⇒ P s) ⇒ P (Seq stmts)) ∧
     (∀stmts. (∀m s. MEM s stmts ⇒ P s) ⇒ P (Par stmts)) ∧
     (∀v s. P s ⇒ P (Label v s)) ∧
     (∀v e s. P s ⇒ P (Local v e s)) ∧
     P Abort ∧ P Done
    ⇒
     ∀s. P s``,
  ntac 2 strip_tac >>
  `(∀s. P s) ∧ (∀l s. MEM s l ⇒ P s)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:stmt``) >>
  simp[] >> dsimp[pairTheory.FORALL_PROD] >> metis_tac[]);

(* lookup_array : memory -> string -> int -> value *)
val lookup_array_def = Define`
  lookup_array m a i =
    case FLOOKUP m a of
        SOME (Array vlist) => if i < 0i ∨ &(LENGTH vlist) ≤ i then Error
                              else EL (Num i) vlist
      | SOME _ => Error
      | NONE => Error
`;

val upd_array_def = Define`
  upd_array m a i v =
    case FLOOKUP m a of
        SOME (Array vlist) => if i < 0 ∨ &(LENGTH vlist) ≤ i then NONE
                              else SOME (m |+ (a, Array (LUPDATE v (Num i) vlist)))
      | _ => NONE
`;

val upd_var_def = Define`
  upd_var m vnm v =
    if vnm ∈ FDOM m ∧ v ≠ Error ∧ ¬isArray (m ' vnm) ∧ ¬isArray v then
      SOME (m |+ (vnm,v))
    else
      NONE
`;

(* lookup_v : memory -> string -> value *)
val lookup_v_def = Define`
  lookup_v m v =
    case FLOOKUP m v of
        NONE => Error
      | SOME v => v
`;

(* evalexpr : memory -> expr -> value *)
val evalexpr_def = tDefine "evalexpr" `
  (evalmaccess m (ASub ma i_expr) =
     case (evalmaccess m ma, evalexpr m i_expr) of
         (Array vlist, Int i) => if i < 0i ∨ &(LENGTH vlist) ≤ i then Error
                                 else EL (Num i) vlist
       | _ => Error) ∧
  (evalmaccess m (VRead nm) = lookup_v m nm) ∧

  (evalexpr m (MAccess ma) = evalmaccess m ma) ∧
  (evalexpr m (Opn vf elist) =
     let vl = MAP (evalexpr m) elist
     in
       if EXISTS isArray vl then Error
       else if EXISTS ((=) Error) vl then Error
       else vf vl) ∧
  (evalexpr m (Value v) = v)
` (WF_REL_TAC `measure (λs. case s of
                                INL (m,ma) => maccess_size ma
                              | INR (m,e) => expr_size e)` >>
   simp[] >> Induct >> rw[expr_size_def] >>
   res_tac >> simp[])

val devals_scalar_def = Define`
  devals_scalar m (D lo hi) ⇔
    ¬isArrayError (evalexpr m lo) ∧
    ¬isArrayError (evalexpr m hi)
`;

(* dvalues : domain -> value list option *)
val dvalues_def = Define`
  dvalues m (D lo hi) =
    case (evalexpr m lo, evalexpr m hi) of
      | (Int lo, Int hi) =>
          SOME (MAP Int (GENLIST (λn. &n + lo)
                                 (if lo ≤ hi then Num(hi - lo) else 0)))
      | _ => NONE
`;

val dvalues_SOME_devals_scalar = store_thm(
  "dvalues_SOME_devals_scalar",
  ``dvalues m d = SOME l ⇒ devals_scalar m d``,
  `∃lo hi. d = D lo hi` by (Cases_on `d` >> simp[]) >>
  simp[dvalues_def, devals_scalar_def] >>
  Cases_on `evalexpr m lo` >> simp[] >>
  Cases_on `evalexpr m hi` >> simp[]);

(* trickiness here is that we only want to substitute scalars for variables
   in "scalar position".  I.e., if we are substituting 10 for x, we want

      a[x+1] --> a[10+1]
      x * 4  --> 10 * 4

   but for

      x[i]

   to stay unchanged, though it's probably some sort of error in any case. *)

val esubst_def = tDefine "esubst" `
  (esubst vnm value (MAccess (VRead vnm')) =
     if vnm = vnm' then Value value else MAccess (VRead vnm')) ∧
  (esubst vnm value (MAccess (ASub ae ie)) =
     MAccess (ASub (msubst vnm value ae) (esubst vnm value ie))) ∧
  (esubst vnm value (Opn f vs) = Opn f (MAP (esubst vnm value) vs)) ∧
  (esubst vnm value (Value v) = Value v) ∧

  (msubst vnm value (VRead vnm') = VRead vnm') ∧
  (msubst vnm value (ASub ae ie) =
    ASub (msubst vnm value ae) (esubst vnm value ie))
`
  (WF_REL_TAC `measure (λs. case s of
                                INL (_,_,e) => expr_size e
                              | INR (_,_,ma) => maccess_size ma)` >>
   simp[] >>
   Induct >> dsimp[expr_size_def] >> rpt strip_tac >> res_tac >> simp[])

val dsubst_def = Define`
  (dsubst _ _ (DValue v) = DValue v) ∧
  (dsubst vnm value (DMA (VRead vnm')) =
     if vnm = vnm' then (DValue value)
     else DMA (VRead vnm')) ∧
  (dsubst vnm value (DMA (ASub ae ie)) =
     DMA (ASub (msubst vnm value ae) (esubst vnm value ie)))
`;
val _ = export_rewrites ["dsubst_def"]

val ap1_def = Define`ap1 f (x,y) = (f x, y)`;
val ap2_def = Define`ap2 f (x,y) = (x, f y)`;
val ap3_def = Define`
  ap3 f (x,y,z) = (x,y,f z)
`;
val _ = export_rewrites ["ap1_def", "ap2_def", "ap3_def"]

val ssubst_def = tDefine "ssubst" `
  (ssubst vnm value (Assign w ds opf) =
     Assign (msubst vnm value w) (MAP (dsubst vnm value) ds) opf) ∧
  (ssubst vnm value (IfStmt g t e) =
     IfStmt (esubst vnm value g) (ssubst vnm value t) (ssubst vnm value e)) ∧
  (ssubst vnm value (Malloc vnm' e value') =
     Malloc vnm' (esubst vnm value e) value') ∧
  (ssubst vnm value (ForLoop vnm' (D lo hi) s) =
     ForLoop vnm' (D (esubst vnm value lo) (esubst vnm value hi))
             (if vnm = vnm' then s else ssubst vnm value s)) ∧
  (ssubst vnm value (ParLoop vnm' (D lo hi) s) =
     ParLoop vnm' (D (esubst vnm value lo) (esubst vnm value hi))
             (if vnm = vnm' then s else ssubst vnm value s)) ∧
  (ssubst vnm value (Seq slist) = Seq (MAP (ssubst vnm value) slist)) ∧
  (ssubst vnm value (Par slist) = Par (MAP (ssubst vnm value) slist)) ∧
  (ssubst vnm value (Label v s) = Label v (ssubst vnm value s)) ∧
  (ssubst vnm value (Local v e s) =
     if v = vnm then Local v (esubst vnm value e) s
     else Local v (esubst vnm value e) (ssubst vnm value s)) ∧
  (ssubst vnm value Abort = Abort) ∧
  (ssubst vnm value Done = Done)
`
  (WF_REL_TAC `measure (λ(vnm,value,s). stmt_size s)` >> simp[] >>
   Induct >> dsimp[stmt_size_def] >> rpt strip_tac >> res_tac >> simp[])

val varsOf_def = tDefine "varsOf" `
  varsOf (MAccess ma) = mvarsOf ma ∧
  varsOf (Opn _ es) = BIGUNION (IMAGE varsOf (set es)) ∧
  varsOf (Value _) = ∅ ∧
  mvarsOf (VRead v) = {v} ∧
  mvarsOf (ASub ma e) = mvarsOf ma ∪ varsOf e
` (WF_REL_TAC
     `measure (λs. case s of INL e => expr_size e | INR m => maccess_size m)` >>
   simp[] >> Induct >> simp[] >> rpt strip_tac >> simp[expr_size_def] >>
   res_tac >> simp[]);
val _ = export_rewrites ["varsOf_def"]
val varsOf_ind = theorem "varsOf_ind"

val _ = set_fixity "#" (Infix(NONASSOC, 450))
val _ = overload_on ("#", ``λn e. n ∉ varsOf e``)

val fresh_esubst = store_thm(
  "fresh_esubst[simp]",
  ``(∀e. n # e ⇒ esubst n v e = e) ∧
    ∀m. n ∉ mvarsOf m ⇒ msubst n v m = m``,
  ho_match_mp_tac varsOf_ind >> simp[esubst_def] >> conj_tac >| [
    Cases >> simp[esubst_def],
    rpt strip_tac >> simp[LIST_EQ_REWRITE, EL_MAP] >>
    metis_tac[MEM_EL]
  ]);

val dvarsOf_def = Define`
  dvarsOf (DValue _) = ∅ ∧
  dvarsOf (DMA ma) = mvarsOf ma
`;
val _ = export_rewrites ["dvarsOf_def"]
val _ = overload_on ("#", ``λn d. n ∉ dvarsOf d``)

val fresh_dsubst = store_thm(
  "fresh_dsubst[simp]",
  ``∀d. n # d ⇒ dsubst n v d = d``,
  Induct >> simp[dsubst_def] >> Cases >> simp[]);

val listVarsOf_def = Define`
  listVarsOf ef [] = ∅ ∧
  listVarsOf ef (h::t) = ef h ∪ listVarsOf ef t
`;
val _ = export_rewrites ["listVarsOf_def"]
val _ = overload_on ("#", ``λn dl : dexpr list. n ∉ listVarsOf dvarsOf dl``)

val listVarsOf_CONG = store_thm(
  "listVarsOf_CONG[defncong]",
  ``∀l1 l2 f1 f2.
      l1 = l2 ∧ (∀e. MEM e l2 ⇒ f1 e = f2 e) ⇒
      listVarsOf f1 l1 = listVarsOf f2 l2``,
  simp[] >> Induct >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  metis_tac[]);

val listVarsOf_MEM = store_thm(
  "listVarsOf_MEM",
  ``n ∈ listVarsOf f l ⇔ ∃e. MEM e l ∧ n ∈ f e``,
  Induct_on `l` >> simp[] >> metis_tac[]);

val fresh_dsubstl = store_thm(
  "fresh_dsubstl[simp]",
  ``∀dl. n # dl ⇒ MAP (dsubst n v) dl = dl``,
  Induct >> simp[]);

val dmvarsOf_def = Define`
  dmvarsOf (D lo hi) = varsOf lo ∪ varsOf hi
`;
val _ = export_rewrites ["dmvarsOf_def"]

val svarsOf_def = tDefine "svarsOf" `
  svarsOf (Assign w ds _) = mvarsOf w ∪ listVarsOf dvarsOf ds ∧
  svarsOf (IfStmt g t e) = varsOf g ∪ svarsOf t ∪ svarsOf e ∧
  svarsOf (Malloc _ e _) = varsOf e ∧
  svarsOf (ForLoop _ dm b) = dmvarsOf dm ∪ svarsOf b ∧
  svarsOf (ParLoop _ dm b) = dmvarsOf dm ∪ svarsOf b ∧
  svarsOf (Seq slist) = listVarsOf svarsOf slist ∧
  svarsOf (Par slist) = listVarsOf svarsOf slist ∧
  svarsOf (Label _ s) = svarsOf s ∧
  svarsOf (Local v e s) = (svarsOf s DELETE v) ∪ varsOf e ∧
  svarsOf Abort = ∅ ∧
  svarsOf Done = ∅
` (WF_REL_TAC `measure stmt_size` >> simp[] >>
   Induct >> simp[] >> rw[] >> simp[stmt_size_def] >>
   res_tac >> simp[]);
val _ = export_rewrites ["svarsOf_def"]

val _ = overload_on("#", ``λn s. n ∉ svarsOf s``)
val _ = overload_on("#", ``λn sl. n ∉ listVarsOf svarsOf sl``)

val fresh_ssubst = store_thm(
  "fresh_ssubst[simp]",
  ``∀s. n # s ⇒ ssubst n v s = s``,
  ho_match_mp_tac (theorem "svarsOf_ind") >>
  asm_simp_tac (srw_ss() ++ ETA_ss)[ssubst_def, FORALL_domain] >> rw[] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >> fs[listVarsOf_MEM] >> metis_tac[MEM_EL]);

val fresh_ssubstl = store_thm(
  "fresh_ssubstl[simp]",
  ``n # sl ⇒ MAP (ssubst n v) sl = sl``,
  simp[LIST_EQ_REWRITE, EL_MAP, listVarsOf_MEM] >>
  metis_tac[MEM_EL, fresh_ssubst]);

val eval_lvalue_def = Define`
  (eval_lvalue m (VRead nm) = SOME (nm, [])) ∧
  (eval_lvalue m (ASub ae ie) =
     do
       (nm, indices) <- eval_lvalue m ae;
       i <- (some i. evalexpr m ie = Int i);
       assert(0 <= i);
       SOME(nm, indices ++ [Num i])
     od)
`

val upd_nested_array_def = Define`
  (upd_nested_array i [] value vlist =
     if i < LENGTH vlist then
       case (EL i vlist, value) of
           (Array _, _) => NONE
         | (_, Array _) => NONE
         | (_, Error) => NONE
         | _ => SOME (LUPDATE value i vlist)
     else NONE) ∧
  (upd_nested_array i (j::is) value vlist =
     if i < LENGTH vlist then
       case EL i vlist of
           Array nvlist =>
           do
             nvlist' <- upd_nested_array j is value nvlist ;
             SOME (LUPDATE (Array nvlist') i vlist)
           od
         | _ => NONE
     else NONE)
`;
val _ = export_rewrites ["upd_nested_array_def"]

val upd_memory_def = Define`
  (upd_memory (nm, []) value m = upd_var m nm value) ∧
  (upd_memory (nm, i :: is) value m =
     case FLOOKUP m nm of
         SOME(Array vlist) =>
           do
             newarray <- upd_nested_array i is value vlist;
             SOME(m |+ (nm, Array newarray))
           od
        | _ => NONE)`
val _ = export_rewrites ["upd_memory_def"]

val upd_write_def = Define`
  upd_write m0 w vf values =
    do
      lvalue <- eval_lvalue m0 w;
      upd_memory lvalue (vf values) m0
    od
`;

val (eval_rules, eval_ind, eval_cases) = Hol_reln`
  (∀c c0 pfx sfx m0 m.
     eval (m0, c0) (m, c) ∧ EVERY ((=) Done) pfx
    ⇒
     eval (m0, Seq (pfx ++ [c0] ++ sfx))
          (m, Seq (pfx ++ [c] ++ sfx)))

     ∧

  (∀m cs.
     EVERY ((=) Done) cs
    ⇒
     eval (m, Seq cs) (m, Done))

     ∧

  (∀m pfx sfx.
     EVERY ((=) Done) pfx
    ⇒
     eval (m, Seq (pfx ++ [Abort] ++ sfx)) (m, Abort))

     ∧

  (∀m g t e b.
     evalexpr m g = Bool b
   ⇒
     eval (m,IfStmt g t e) (m, Seq [Done; if b then t else e]))

     ∧

  (∀m g t e.
     (∀b. evalexpr m g ≠ Bool b)
    ⇒
     eval (m,IfStmt g t e) (m,Abort))

     ∧

  (* lvalue is evaluated atomically when reads are ready to go;
     assumption is that write/destination calculation is never
     racy with respect to data arrays. *)
  (∀rdes m0 m' vf.
      EVERY isDValue rdes ∧
      upd_write m0 w vf (MAP destDValue rdes) = SOME m'
     ⇒
      eval (m0, Assign w rdes vf) (m', Done))

     ∧

  (∀w rdes m0 vf.
      EVERY isDValue rdes ∧
      upd_write m0 w vf (MAP destDValue rdes) = NONE
     ⇒
      eval (m0, Assign w rdes vf) (m0, Abort))

     ∧

  (∀pfx expr sfx w vf m.
      eval (m, Assign w (pfx ++ [DMA expr] ++ sfx) vf)
           (m,
            Assign w
                  (pfx ++ [DValue (evalmaccess m expr)] ++ sfx)
                  vf))

     ∧

  (∀pfx sfx w vf v m.
      isArrayError v
     ⇒
      eval (m, Assign w (pfx ++ [DValue v] ++ sfx) vf) (m, Abort))

     ∧

  (∀body d m vnm iters.
      dvalues m d = SOME iters
     ⇒
      eval (m, ForLoop vnm d body)
           (m, Seq (MAP (λdv. Label dv (ssubst vnm dv body)) iters)))

     ∧

  (∀body d m vnm.
      dvalues m d = NONE
     ⇒
      eval (m, ForLoop vnm d body) (m, Abort))

     ∧

  (∀body d m vnm iters.
      dvalues m d = SOME iters
     ⇒
      eval (m, ParLoop vnm d body)
           (m, Par (MAP (λdv. Label dv (ssubst vnm dv body)) iters)))

     ∧

  (∀body d m vnm.
      dvalues m d = NONE
     ⇒
      eval (m, ParLoop vnm d body) (m, Abort))

     ∧

  (∀m m' pfx ps s s' sfx.
      ps = pfx ++ [s] ++ sfx ∧ eval (m, s) (m', s')
    ⇒
      eval (m, Par ps) (m', Par (pfx ++ [s'] ++ sfx)))

     ∧

  (∀m cs.
      EVERY ((=) Done) cs
     ⇒
      eval (m, Par cs) (m, Done))

     ∧

  (∀m cs.
      MEM Abort cs
     ⇒
      eval (m, Par cs) (m, Abort))

     ∧

  (∀anm sz_e sz_i iv m0.
      evalexpr m0 sz_e = Int sz_i ∧
      0 ≤ sz_i ∧
      anm ∉ FDOM m0
     ⇒
      eval (m0, Malloc anm sz_e iv)
           (m0 |+ (anm, Array (GENLIST (K iv) (Num sz_i))),
            Done))

     ∧

  (∀m0 c0 m c v.
      eval (m0, c0) (m, c)
     ⇒
      eval (m0, Label v c0) (m, Label v c))

     ∧

  (∀m v.
      eval (m, Label v Done) (m, Done))

     ∧

  (∀m v.
      eval (m, Label v Abort) (m, Abort))

     ∧

  (∀m vnm value e s.
      evalexpr m e = value ∧ ¬isArray value
     ⇒
      eval (m, Local vnm e s) (m, ssubst vnm value s))
`

val _ = set_fixity "--->" (Infix(NONASSOC, 450))
val _ = overload_on("--->", ``eval``)

val _ = set_fixity "--->⁺" (Infix(NONASSOC, 450))
val _ = overload_on ("--->⁺", ``TC eval``)

val _ = set_fixity "--->*" (Infix(NONASSOC, 450))
val _ = overload_on ("--->*", ``RTC eval``)


val _ = export_theory()
