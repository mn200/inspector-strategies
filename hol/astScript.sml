open HolKernel Parse boolLib bossLib;

open stringTheory
open integerTheory intLib
open realTheory
open finite_mapTheory
open lcsymtacs
open listRangeTheory
open bagTheory

val _ = new_theory "ast";

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

val expr_weight_def = Define`
  (expr_weight (Value v) = 0:num) ∧
  (expr_weight e = 1)
`;
val _ = export_rewrites ["expr_weight_def"]

val dexpr_weight_def = Define`
  (dexpr_weight (DValue v) = 0:num) ∧
  (dexpr_weight (Read v e) = 1 + expr_weight e) ∧
  (dexpr_weight (Convert e) = expr_weight e)
`;
val _ = export_rewrites ["dexpr_weight_def"]

val stmt_weight_def = tDefine "stmt_weight" `
  (stmt_weight Abort = 0) ∧
  (stmt_weight Done = 0) ∧
  (stmt_weight (Assign w ds v) =
     1 + expr_weight (SND w) + SUM (MAP dexpr_weight ds)) ∧
  (stmt_weight (AssignVar v e) = 1) ∧
  (stmt_weight (Malloc v d value) = 1) ∧
  (stmt_weight (IfStmt g t e) = MAX (stmt_weight t) (stmt_weight e) + 1) ∧
  (stmt_weight (ForLoop v d s) = stmt_weight s + 1) ∧
  (stmt_weight (ParLoop v d s) = stmt_weight s + 1) ∧
  (stmt_weight (Seq stmts) =
    SUM (MAP (λms. stmt_weight (SND ms)) stmts) + 1 + LENGTH stmts) ∧
  (stmt_weight (Par stmts) =
    SUM (MAP (λms. stmt_weight (SND ms)) stmts) + 1 + LENGTH stmts)
` (WF_REL_TAC `measure stmt_size` >> simp[] >>
   Induct >> dsimp[definition "stmt_size_def"] >>
   rpt strip_tac >> res_tac >> simp[])
val _ = export_rewrites ["stmt_weight_def"]

val loopbag_def = tDefine "loopbag" `
  (loopbag Abort = {| 0 |}) ∧
  (loopbag Done = {| 0 |}) ∧
  (loopbag (Assign w ds v) = {| 0 |}) ∧
  (loopbag (AssignVar v e) = {| 0 |}) ∧
  (loopbag (Malloc v d value) = {| 0 |}) ∧
  (loopbag (IfStmt g t e) = BAG_UNION (loopbag t) (loopbag e)) ∧
  (loopbag (ForLoop v d s) = BAG_IMAGE SUC (loopbag s)) ∧
  (loopbag (ParLoop v d s) = BAG_IMAGE SUC (loopbag s)) ∧
  (loopbag (Seq stmts) =
     FOLDR (λms b. BAG_UNION (loopbag (SND ms)) b) {|0|} stmts) ∧
  (loopbag (Par stmts) =
     FOLDR (λms b. BAG_UNION (loopbag (SND ms)) b) {|0|} stmts)
` (WF_REL_TAC `measure stmt_size` >> simp[] >>
   Induct >> dsimp[definition "stmt_size_def"] >>
   rpt strip_tac >> res_tac >> simp[])
val _ = export_rewrites ["loopbag_def"]

val FINITE_loopbag = store_thm(
  "FINITE_loopbag[simp]",
  ``∀s. FINITE_BAG (loopbag s)``,
  ho_match_mp_tac (theorem "loopbag_ind") >>
  simp[] >> Induct >> simp[]);

val loopbag_not_empty = store_thm(
  "loopbag_not_empty[simp]",
  ``∀s. loopbag s ≠ {||}``,
  ho_match_mp_tac (theorem "loopbag_ind") >> simp[] >>
  Induct >> simp[]);

val MAX_PLUS = store_thm(
  "MAX_PLUS",
  ``MAX x y + z = MAX (x + z) (y + z)``,
  rw[arithmeticTheory.MAX_DEF]);

val transitive_LT = store_thm(
  "transitive_LT[simp]",
  ``transitive ((<) : num -> num -> bool)``,
  simp[relationTheory.transitive_def]);


val SUM_IMAGE_CONG = REWRITE_RULE [GSYM AND_IMP_INTRO] pred_setTheory.SUM_IMAGE_CONG
val BAG_CARD_SUM_IMAGE = store_thm(
  "BAG_CARD_SUM_IMAGE",
  ``FINITE_BAG b ==>
    (BAG_CARD b = SUM_IMAGE b { e | BAG_IN e b })``,
  Q.ID_SPEC_TAC `b` THEN Induct_on `FINITE_BAG` THEN
  SRW_TAC [][pred_setTheory.SUM_IMAGE_THM, BAG_CARD_THM] THEN
  SIMP_TAC (srw_ss()) [BAG_INSERT, pred_setTheory.GSPEC_OR] THEN
  `{ e | BAG_IN e b} = SET_OF_BAG b`
    by SRW_TAC [][SET_OF_BAG, pred_setTheory.EXTENSION] THEN
  SRW_TAC[][pred_setTheory.SUM_IMAGE_UNION,
            pred_setTheory.SUM_IMAGE_THM] THEN
  Cases_on `e IN SET_OF_BAG b` THENL [
    SRW_TAC[][pred_setTheory.INSERT_INTER, pred_setTheory.SUM_IMAGE_THM] THEN
    `SET_OF_BAG b = e INSERT (SET_OF_BAG b DELETE e)`
      by (SRW_TAC[][pred_setTheory.EXTENSION] THEN METIS_TAC[IN_SET_OF_BAG])THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    SRW_TAC [][pred_setTheory.SUM_IMAGE_THM] THEN
    SRW_TAC[ARITH_ss][] THEN
    SRW_TAC[][Cong SUM_IMAGE_CONG],
    SRW_TAC [][pred_setTheory.INSERT_INTER, pred_setTheory.SUM_IMAGE_THM] THEN
    `!x. x IN SET_OF_BAG b ==> x <> e` by METIS_TAC[] THEN
    SRW_TAC[][Cong SUM_IMAGE_CONG] THEN
    `b e = 0` suffices_by SRW_TAC[ARITH_ss][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [BAG_IN, BAG_INN]
  ]);

val eval_terminates = store_thm(
  "eval_terminates",
  ``∀a b. eval a b ⇒ inv_image (mlt (<) LEX (<)) (λ(m,lm,s). (loopbag s, stmt_weight s)) b a``,
  Induct_on `eval a b` >> rpt strip_tac >>
  lfs[pairTheory.LEX_DEF, pred_setTheory.MAX_SET_THM]
  >- (Induct_on `rest` >> simp[])
  >- (Induct_on `rest` >> simp[])
  >- (Cases_on `b` >> simp[])
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- (Cases_on `expr` >> fs[isValue_def])
  >- (simp[listTheory.SUM_APPEND] >> Cases_on `expr` >> fs[isValue_def])
  >- simp[listTheory.SUM_APPEND]
  >- (disj1_tac >> pop_assum kall_tac >>
      simp[mlt_dominates_thm1, rich_listTheory.FOLDR_MAP] >>
      conj_tac >- (Induct_on `iters` >> simp[]) >>
      qexists_tac `BAG_IMAGE SUC (loopbag body)` >> simp[] >>
      dsimp[dominates_def] >>
      qho_match_abbrev_tac
        `∀e1. BAG_IN e1 FF ⇒ ∃e2. BAG_IN e2 (loopbag body) /\ e1 < SUC e2` >>
      `∀e. BAG_IN e FF ⇒ BAG_IN e (loopbag body) ∨ e = 0`
        by (simp[Abbr`FF`] >> Induct_on `iters` >> simp[] >> metis_tac[]) >>
      rpt strip_tac >> res_tac >- metis_tac[DECIDE ``x < SUC x``] >> simp[] >>
      metis_tac[loopbag_not_empty, BAG_cases, BAG_IN_BAG_INSERT])
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- (disj1_tac >> pop_assum kall_tac >>
      simp[rich_listTheory.FOLDR_MAP, mlt_dominates_thm1] >>
      conj_tac >- (Induct_on `iters` >> simp[]) >>
      qexists_tac `BAG_IMAGE SUC (loopbag body)` >> simp[] >>
      dsimp[dominates_def] >>
      qho_match_abbrev_tac
        `∀e1. BAG_IN e1 FF ⇒ ∃e2. BAG_IN e2 (loopbag body) ∧ e1 < SUC e2` >>
      `∀e. BAG_IN e FF ⇒ BAG_IN e (loopbag body) ∨ e = 0`
         by (simp[Abbr`FF`] >> Induct_on `iters` >> simp[] >> metis_tac[]) >>
      rpt strip_tac >> res_tac >- metis_tac[DECIDE ``x < SUC x``] >>
      simp[] >>
      metis_tac[loopbag_not_empty, BAG_cases, BAG_IN_BAG_INSERT])
  >- (simp[mltLT_SING0] >> metis_tac[])
  >- (disj1_tac >> rw[] >> Induct_on `pfx` >> simp[] >>
      Induct_on `sfx` >> simp[])
  >- (disj2_tac >> simp[listTheory.SUM_APPEND] >> rw[] >>
      Induct_on `pfx` >> simp[]) >>
  disj1_tac >> rw[] >> Induct_on `pfx` >> simp[] >>
  Induct_on `sfx` >> simp[])

fun newrule t =
    eval_cases |> Q.SPEC `(m,lm,^t)` |> SIMP_RULE (srw_ss()) []

val evalths = [newrule ``Seq []``, newrule ``Done``, newrule ``Seq (h::t)``,
               newrule ``ForLoop v d b``, newrule ``Assign w rds vf``,
               newrule ``ParLoop v d b``, newrule ``Par []``,
               newrule ``Par (h::t)``, newrule ``AssignVar v e``,
               newrule ``IfStmt g t e``, newrule ``Malloc v n value``]

fun subeval t =
    SIMP_CONV (srw_ss()) (dvalues_def:: listRangeLHI_CONS :: isValue_def ::
                          listTheory.APPEND_EQ_CONS :: EXISTS_OR_THM ::
                          LEFT_AND_OVER_OR :: RIGHT_AND_OVER_OR ::
                          evalexpr_def :: lookup_v_def :: upd_array_def ::
                          FLOOKUP_FUNION :: FLOOKUP_UPDATE :: isDValue_def ::
                          lookup_array_def :: destDValue_def :: incval_def ::
                          listTheory.LUPDATE_compute ::
                          evalths) t
fun eval1 t0 = let
  val gv = genvar (type_of t0)
  val th = subeval ``eval ^t0 ^gv``
  val c = rhs (concl th)
  val ts = if aconv c F then []
           else map rhs (strip_disj (rhs (concl th)))
  fun mkth t = th |> INST [gv |-> t] |> PURE_REWRITE_RULE [OR_CLAUSES, REFL_CLAUSE]
                  |> EQT_ELIM
in
  map mkth ts
end;

val _ = overload_on ("VInt", ``\i. Value (Int i)``)

val ser_t =
    ``(FEMPTY |+ ("a", Array (GENLIST (λn. Int &n) 20)), FEMPTY : memory,
       ForLoop "i" (D (VInt 0) (VInt 10)) (Assign ("a", VarExp "i") [Read "a" (VarExp "i")] incval))``

fun chain m eq (f: 'a -> 'b list) (d: 'b -> 'a) s0 = let
  fun history_to_next h =
      case h of
          (bs as (b::_), a) =>
          (case f (d b) of
               [] => [h]
                   | newbs => map (fn b' => (b'::bs, a)) newbs)
        | ([], a) => map (fn b => ([b], a)) (f a)

  fun recurse n hs =
    if n <= 0 then hs
    else let
      val acc' = op_mk_set eq (List.concat (map history_to_next hs))
      val _ = print ("Stage " ^ Int.toString (m - n + 1) ^ ": " ^
                     Int.toString (length acc') ^ " results\n")
    in
      recurse (n - 1) acc'
    end
in
  map (fn (bs, a) => (a, List.rev bs)) (recurse m [([], s0)])
end

fun chaineval n t = let
  val d = rand o concl
in
  map (fn (a, bs) => d (last bs))
      (chain n
             (fn (bs1,a1) => fn (bs2, a2) => aconv (d (hd bs1)) (d (hd bs2)))
             eval1
             d
             t)
end

val par_t =
    ``(FEMPTY |+ ("a", Array (GENLIST (λn. Real &(2 * n)) 10)), FEMPTY : memory,
         ParLoop "i" (D (VInt 0) (VInt 3)) (Assign ("a", VarExp "i") [Read "a" (VarExp "i")] incval))``
(*
val serial_res = chaineval 52 ser_t;
val res = chaineval 4 par_t;
val _ = print ("Length of result is " ^ Int.toString (length res) ^ "\n")
*)

val _ = export_theory();
