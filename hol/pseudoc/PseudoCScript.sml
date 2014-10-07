open HolKernel Parse boolLib bossLib;

open stringTheory
open integerTheory intLib
open realTheory
open finite_mapTheory
open lcsymtacs
open listRangeTheory
open intrealTheory transcTheory
open monadsyntax

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

val _ = Datatype`
  expr = VRead string
       | ASub expr expr
       | Opn (value list -> value) (expr list)
       | Value value
`

val isValue_def = Define`
  isValue (Value _) = T ∧
  isValue _ = F
`
val _ = export_rewrites ["isValue_def"]

val _ = type_abbrev ("write", ``:expr``)
val _ = type_abbrev ("aname", ``:string``)
val _ = type_abbrev ("vname", ``:string``)
val _ = disable_tyabbrev_printing "aname"
val _ = disable_tyabbrev_printing "vname"
val _ = disable_tyabbrev_printing "write"

val isValue_def = Define`
  isValue (Value _) = T ∧
  isValue _ = F
`
val _ = export_rewrites ["isValue_def"]

val destValue_def = Define`
  destValue (Value v) = v
`;
val _ = export_rewrites ["destValue_def"]

val _ = Datatype`domain = D expr expr`  (* lo/hi pair *)


val _ = type_abbrev ("vname", ``:string``)
val _ = type_abbrev ("memory", ``:vname |-> value``)

val _ = Datatype`
  stmt = Assign write (expr list) (value list -> value)
       | IfStmt expr stmt stmt
       | Malloc aname expr value
       | ForLoop vname domain stmt
       | ParLoop vname domain stmt
       | Seq (stmt list)
       | Par (stmt list)
       | Local vname expr stmt
       | Label value stmt
       | Abort
       | Done
`

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
    if vnm ∈ FDOM m ∧ v ≠ Error ∧ (∀els. m ' vnm ≠ Array els) ∧
       (∀els. v ≠ Array els)
    then
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
  (evalexpr m (ASub a_expr i_expr) =
     case (evalexpr m a_expr, evalexpr m i_expr) of
         (Array vlist, Int i) => if i < 0i ∨ &(LENGTH vlist) ≤ i then Error
                                 else EL (Num i) vlist
       | _ => Error) ∧
  (evalexpr m (VRead nm) = lookup_v m nm) ∧
  (evalexpr m (Opn vf elist) = vf (MAP (evalexpr m) elist)) ∧
  (evalexpr m (Value v) = v)
` (WF_REL_TAC `inv_image (measure expr_size) SND` >>
   simp[] >> Induct >> rw[definition "expr_size_def"] >>
   res_tac >> simp[])

(* dvalues : domain -> value list option *)
val dvalues_def = Define`
  dvalues m (D lo hi) =
    case (evalexpr m lo, evalexpr m hi) of
      | (Int lo, Int hi) =>
          SOME (MAP Int (GENLIST (λn. &n + lo)
                                 (if lo ≤ hi then Num(hi - lo) else 0)))
      | _ => NONE
`;

val esubst_def = tDefine "esubst" `
  (esubst vnm value (VRead vnm') = if vnm = vnm' then Value value
                                   else VRead vnm') ∧
  (esubst vnm value (ASub ae ie) =
     ASub (esubst vnm value ae) (esubst vnm value ie)) ∧
  (esubst vnm value (Opn f vs) = Opn f (MAP (esubst vnm value) vs)) ∧
  (esubst vnm value (Value v) = Value v)
`
  (WF_REL_TAC `measure (λ(vnm,value,e). expr_size e)` >> simp[] >>
   Induct >> dsimp[definition "expr_size_def"] >> rpt strip_tac >>
   res_tac >> simp[])

val ap1_def = Define`ap1 f (x,y) = (f x, y)`;
val ap2_def = Define`ap2 f (x,y) = (x, f y)`;
val ap3_def = Define`
  ap3 f (x,y,z) = (x,y,f z)
`;
val _ = export_rewrites ["ap1_def", "ap2_def", "ap3_def"]

val ssubst_def = tDefine "ssubst" `
  (ssubst vnm value (Assign w ds opf) =
     Assign (esubst vnm value w) (MAP (esubst vnm value) ds) opf) ∧
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
     if v = vnm then Local v e s
     else Local v (esubst vnm value e) (ssubst vnm value s)) ∧
  (ssubst vnm value Abort = Abort) ∧
  (ssubst vnm value Done = Done)
`
  (WF_REL_TAC `measure (λ(vnm,value,s). stmt_size s)` >> simp[] >>
   Induct >> dsimp[definition "stmt_size_def"] >> rpt strip_tac >>
   res_tac >> simp[])

val eval_lvalue_def = Define`
  (eval_lvalue m (VRead nm) = SOME (nm, [])) ∧
  (eval_lvalue m (ASub ae ie) =
     do
       (nm, indices) <- eval_lvalue m ae;
       i <- (some i. evalexpr m ie = Int i);
       assert(0 <= i);
       SOME(nm, indices ++ [Num i])
     od) ∧
  (eval_lvalue m (Opn _ _) = NONE) ∧
  (eval_lvalue m (Value _) = NONE)
`

val upd_nested_array_def = Define`
  (upd_nested_array i [] value vlist =
     if i < LENGTH vlist then
       case EL i vlist of
           Array _ => NONE
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

val upd_write_def = Define`
  upd_write m0 w value =
    case eval_lvalue m0 w of
        NONE => NONE
      | SOME lvalue => upd_memory lvalue value m0
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
      EVERY isValue rdes ∧
      upd_write m0 w (vf (MAP destValue rdes)) = SOME m'
     ⇒
      eval (m0, Assign w rdes vf) (m', Done))

     ∧

  (∀w rdes m0 vf.
      EVERY isValue rdes ∧
      upd_write m0 w (vf (MAP destValue rdes)) = NONE
     ⇒
      eval (m0, Assign w rdes vf) (m0, Abort))

     ∧

  (∀pfx expr sfx w vf m.
      ¬isValue expr
     ⇒
      eval (m, Assign w (pfx ++ [expr] ++ sfx) vf)
           (m,
            Assign w
                  (pfx ++ [Value (evalexpr m expr)] ++ sfx)
                  vf))

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
      evalexpr m e = value ∧
      (∀a. value ≠ Array a)
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
