open HolKernel Parse boolLib bossLib;

open stringTheory
open integerTheory intLib
open realTheory
open finite_mapTheory
open lcsymtacs
open listRangeTheory

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
  expr = VarExp string
       | ISub string expr
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
val _ = disable_tyabbrev_printing "aname"

val _ = Datatype`
  dexpr = DValue value
        | Read aname expr
        | Convert expr
`

val isDValue_def = Define`
  isDValue (DValue _) = T ∧
  isDValue _ = F
`

val destDValue_def = Define`
  destDValue (DValue v) = v
`;

val _ = Datatype`domain = D expr expr`  (* lo/hi pair *)


val _ = type_abbrev ("vname", ``:string``)
val _ = type_abbrev ("memory", ``:vname |-> value``)

val _ = Datatype`
  stmt = Assign write (dexpr list) (value list -> value)
       | AssignVar vname  expr      (* for assignments to scalars, global or local *)
       | IfStmt expr stmt stmt
       | Malloc aname num value
       | ForLoop string domain stmt
       | ParLoop string domain stmt
       | Seq ((memory # stmt) list)
       | Par ((memory # stmt) list)
       | Abort
       | Done
`

val stmt_induction = store_thm(
  "stmt_induction",
  ``∀P.
     (∀w ds vf. P (Assign w ds vf)) ∧
     (∀v e. P (AssignVar v e)) ∧
     (∀g t e. P t ∧ P e ⇒ P (IfStmt g t e)) ∧
     (∀nm n value. P (Malloc nm n value)) ∧
     (∀s d stmt. P stmt ⇒ P (ForLoop s d stmt)) ∧
     (∀s d stmt. P stmt ⇒ P (ParLoop s d stmt)) ∧
     (∀ms. (∀m s. MEM (m,s) ms ⇒ P s) ⇒ P (Seq ms)) ∧
     (∀ms. (∀m s. MEM (m,s) ms ⇒ P s) ⇒ P (Par ms)) ∧
     P Abort ∧ P Done
    ⇒
     ∀s. P s``,
  ntac 2 strip_tac >>
  `(∀s. P s) ∧ (∀l (m:memory) s. MEM (m,s) l ⇒ P s) ∧ (∀ms:memory#stmt. P (SND ms))`
    suffices_by simp[] >>
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

(* lookup_v : memory -> string -> value *)
val lookup_v_def = Define`
  lookup_v m v =
    case FLOOKUP m v of
        NONE => Error
      | SOME v => v
`;

(* evalexpr : memory -> expr -> value *)
val evalexpr_def = tDefine "evalexpr" `
  (evalexpr m (ISub nm i_expr) =
     case evalexpr m i_expr of
         Int i => lookup_array m nm i
       | _ => Error) ∧
  (evalexpr m (VarExp nm) = lookup_v m nm) ∧
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

val (eval_rules, eval_ind, eval_cases) = Hol_reln`
  (∀m0 lm0 llm s1 m s1' rest.
    eval (m0, llm ⊌ lm0, s1) (m, llm ⊌ lm0, s1')
   ⇒
    eval (m0, lm0, Seq ((llm,s1)::rest)) (m, lm0, Seq ((llm,s1')::rest)))

     ∧

  (∀m lm llm rest.
     eval (m, lm, Seq ((llm, Done) :: rest)) (m, lm, Seq rest))

     ∧

  (∀m lm.
     eval (m, lm, Seq []) (m, lm, Done))

     ∧

  (∀m lm g t e b.
     evalexpr (lm ⊌ m) g = Bool b
   ⇒
     eval (m,lm,IfStmt g t e) (m, lm, if b then t else e))

     ∧

  (∀m lm g t e.
     (∀b. evalexpr (lm ⊌ m) g ≠ Bool b)
    ⇒
     eval (m,lm,IfStmt g t e) (m,lm,Abort))

     ∧

  (∀rdes m0 m' lm0 aname i vf.
      EVERY isDValue rdes ∧
      upd_array m0 aname i (vf (MAP destDValue rdes)) = SOME m'
    ⇒
      eval (m0, lm0, Assign (aname, Value (Int i)) rdes vf) (m', lm0, Done))

     ∧

  (∀rdes m0 lm0 aname i vf.
      EVERY isDValue rdes ∧
      upd_array m0 aname i (vf (MAP destDValue rdes)) = NONE ⇒
      eval (m0, lm0, Assign (aname, Value (Int i)) rdes vf)
           (m0, lm0, Abort))

     ∧

  (∀m0 lm aname expr rds vf.
      ¬isValue expr ⇒
      eval (m0, lm, Assign (aname, expr) rds vf)
           (m0, lm, Assign (aname, Value (evalexpr (lm ⊌ m0) expr)) rds vf))

     ∧

  (∀rds pfx aname expr sfx w vf m lm.
      rds = pfx ++ [Read aname expr] ++ sfx /\ ¬isValue expr ⇒
      eval (m, lm, Assign w rds vf)
           (m, lm,
            Assign w
                  (pfx ++ [Read aname (Value (evalexpr (lm ⊌ m) expr))] ++ sfx)
                  vf))

     ∧

  (∀rds pfx aname i sfx w vf lm m.
      rds = pfx ++ [Read aname (Value (Int i))] ++ sfx ⇒
      eval (m, lm, Assign w rds vf)
           (m, lm, Assign w (pfx ++ [DValue (lookup_array m aname i)] ++ sfx) vf)) ∧

  (∀body d lm m vnm iters.
      dvalues (lm ⊌ m) d = SOME iters
     ⇒
      eval (m, lm, ForLoop vnm d body)
           (m, lm, Seq (MAP (λdv. (lm |+ (vnm, dv), body)) iters))) ∧

  (∀body d lm m vnm.
      dvalues (lm ⊌ m) d = NONE
     ⇒
      eval (m, lm, ForLoop vnm d body) (m, lm, Abort))

     ∧

  (∀body d lm m vnm iters.
      dvalues (lm ⊌ m) d = SOME iters
     ⇒
      eval (m, lm, ParLoop vnm d body)
           (m, lm, Par (MAP (λdv. (lm |+ (vnm, dv), body)) iters)))

     ∧

  (∀body d lm m vnm.
      dvalues (lm ⊌ m) d = NONE
     ⇒
      eval (m, lm, ParLoop vnm d body) (m, lm, Abort))

     ∧

  (∀llm lm m m' pfx ps s s' sfx.
      ps = pfx ++ [(llm, s)] ++ sfx ∧ eval (m, llm ⊌ lm, s) (m', llm ⊌ lm, s')
    ⇒
      eval (m, lm, Par ps) (m', lm, Par (pfx ++ [(llm, s')] ++ sfx))) ∧

  (∀llm lm m pfx ps sfx.
      ps = pfx ++ [(llm, Done)] ++ sfx ⇒
      eval (m, lm, Par ps) (m, lm, Par (pfx ++ sfx))) ∧

  (∀lm m. eval (m, lm, Par []) (m, lm, Done))
`

val _ = set_fixity "--->" (Infix(NONASSOC, 450))
val _ = overload_on("--->", ``eval``)

val incval_def = Define`
  incval [Real j] = Real (j + 1) ∧
  incval [Int j] = Int (j + 1) ∧
  incval _ = Error
`;

val plusval_def = Define`
  plusval [Real r; Real s] = Real (r + s) ∧
  plusval [Int i; Int j] = Int (i + j) ∧
  plusval _ = Error
`
val _ = overload_on("+", ``\v1 v2. plusval[v1;v2]``)

val _ = export_theory()
