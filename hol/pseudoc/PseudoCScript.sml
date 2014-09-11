open HolKernel Parse boolLib bossLib;

open stringTheory
open integerTheory intLib
open realTheory
open finite_mapTheory
open lcsymtacs
open listRangeTheory
open intrealTheory transcTheory

val _ = new_theory "PseudoC";

val _ = ParseExtras.tight_equality()

val _ = Datatype`
  value = Int int
        | Real real
        | Array (value list)
        | Bool bool
        | Error
`;

val _ = Datatype`
  expr = VRead string
       | ARead string expr
       | Opn (value list -> value) (expr list)
       | Value value
`

val isValue_def = Define`
  isValue (Value _) = T ∧
  isValue _ = F
`
val _ = export_rewrites ["isValue_def"]

val _ = type_abbrev ("write", ``:string # expr``)
val _ = type_abbrev ("aname", ``:string``)
val _ = type_abbrev ("vname", ``:string``)
val _ = disable_tyabbrev_printing "aname"
val _ = disable_tyabbrev_printing "vname"

val _ = Datatype`
  dexpr = DValue value
        | DARead aname expr
        | DVRead vname
`

val isDValue_def = Define`
  isDValue (DValue _) = T ∧
  isDValue _ = F
`
val _ = export_rewrites ["isDValue_def"]

val destDValue_def = Define`
  destDValue (DValue v) = v
`;
val _ = export_rewrites ["destDValue_def"]

val _ = Datatype`domain = D expr expr`  (* lo/hi pair *)


val _ = type_abbrev ("vname", ``:string``)
val _ = type_abbrev ("memory", ``:vname |-> value``)

val _ = Datatype`
  stmt = Assign write (dexpr list) (value list -> value)
       | AssignVar vname (dexpr list) (value list -> value)
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
     (∀v ds vf. P (AssignVar v ds vf)) ∧
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
      | SOME (Array _) => Error
      | SOME v => v
`;

(* evalexpr : memory -> expr -> value *)
val evalexpr_def = tDefine "evalexpr" `
  (evalexpr m (ARead nm i_expr) =
     case evalexpr m i_expr of
         Int i => lookup_array m nm i
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
  (esubst vnm value (ARead vn e) = ARead vn (esubst vnm value e)) ∧
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

val dsubst_def = Define`
  (dsubst vnm value (DValue v) = DValue v) ∧
  (dsubst vnm value (DARead anm e) = DARead anm (esubst vnm value e)) ∧
  (dsubst vnm value (DVRead vnm') = if vnm = vnm' then DValue value
                                   else DVRead vnm')
`;

val ssubst_def = tDefine "ssubst" `
  (ssubst vnm value (Assign w ds opf) =
     Assign (ap2 (esubst vnm value) w) (MAP (dsubst vnm value) ds) opf) ∧
  (ssubst vnm value (AssignVar vnm' ds opf) =
     AssignVar vnm' (MAP (dsubst vnm value) ds) opf) ∧ (* maybe abort if vnm = vnm' ? *)
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

  (* assignvar completes successfully, having performed all reads *)
  (∀m0 m vnm rdes vf.
     EVERY isDValue rdes ∧
     upd_var m0 vnm (vf (MAP destDValue rdes)) = SOME m
    ⇒
     eval (m0, AssignVar vnm rdes vf) (m, Done))

    ∧

  (* assignvar fails on attempting to write to memory *)
  (∀m0 vnm rdes vf.
     EVERY isDValue rdes ∧
     upd_var m0 vnm (vf (MAP destDValue rdes)) = NONE
    ⇒
     eval (m0, AssignVar vnm rdes vf) (m0, Abort))

     ∧

  (* assignvar calculates index for an array read *)
  (∀m vnm pfx sfx anm e vf.
     ¬isValue e
    ⇒
     eval (m, AssignVar vnm (pfx ++ [DARead anm e] ++ sfx) vf)
          (m, AssignVar vnm (pfx ++
                             [DARead anm (Value (evalexpr m e))] ++
                             sfx) vf))

     ∧

  (* assignvar completes an array read *)
  (∀m vnm pfx sfx anm i vf.
     eval (m, AssignVar vnm (pfx ++ [DARead anm (Value (Int i))] ++ sfx) vf)
          (m, AssignVar vnm (pfx ++ [DValue (lookup_array m anm i)] ++ sfx) vf))

     ∧

  (* assignvar completes a DVRead *)
  (∀m vnm pfx sfx vr vf.
     eval (m, AssignVar vnm (pfx ++ [DVRead vr] ++ sfx) vf)
          (m, AssignVar vnm (pfx ++ [DValue (lookup_v m vr)] ++ sfx) vf))

     ∧

  (∀rdes m0 m' aname i vf.
      EVERY isDValue rdes ∧
      upd_array m0 aname i (vf (MAP destDValue rdes)) = SOME m'
     ⇒
      eval (m0, Assign (aname, Value (Int i)) rdes vf) (m', Done))

     ∧

  (∀rdes m0 aname i vf.
      EVERY isDValue rdes ∧
      upd_array m0 aname i (vf (MAP destDValue rdes)) = NONE
     ⇒
      eval (m0, Assign (aname, Value (Int i)) rdes vf)
           (m0, Abort))

     ∧

  (∀m0 aname expr rds vf.
      ¬isValue expr ⇒
      eval (m0, Assign (aname, expr) rds vf)
           (m0, Assign (aname, Value (evalexpr m0 expr)) rds vf))

     ∧

  (∀rds pfx aname expr sfx w vf m.
      rds = pfx ++ [DARead aname expr] ++ sfx /\ ¬isValue expr ⇒
      eval (m, Assign w rds vf)
           (m,
            Assign w
                  (pfx ++ [DARead aname (Value (evalexpr m expr))] ++ sfx)
                  vf))

     ∧

  (∀rds pfx aname i sfx w vf m.
      rds = pfx ++ [DARead aname (Value (Int i))] ++ sfx
     ⇒
      eval (m, Assign w rds vf)
           (m,
            Assign w (pfx ++ [DValue (lookup_array m aname i)] ++ sfx) vf))

     ∧

  (∀rds pfx vname sfx w vf m.
      rds = pfx ++ [DVRead vname] ++ sfx ⇒
      eval (m, Assign w rds vf)
           (m,
            Assign w (pfx ++ [DValue (lookup_v m vname)] ++ sfx) vf))

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
