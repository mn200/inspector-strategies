open HolKernel Parse boolLib bossLib;

open stringTheory
open integerTheory intLib
open realTheory
open finite_mapTheory
open lcsymtacs
open listRangeTheory

val _ = new_theory "ast";

val _ = ParseExtras.tight_equality()

val _ = Hol_datatype`
  value = Int of int
        | Real of real
        | Array of value list
        | Bool of bool
        | Error
`;

val _ = Hol_datatype`
  expr = VarExp of string
       | ISub of string => expr
       | Opn of (value list -> value) => expr list
       | Value of value
`

val isValue_def = Define`
  isValue (Value _) = T ∧
  isValue _ = F
`
val _ = export_rewrites ["isValue_def"]

val _ = type_abbrev ("write", ``:string # expr``)
val _ = type_abbrev ("aname", ``:string``)
val _ = disable_tyabbrev_printing "aname"

val _ = Hol_datatype`
  dexpr = DValue of value
        | Read of aname => expr
        | Convert of expr
`

val isDValue_def = Define`
  isDValue (DValue _) = T ∧
  isDValue _ = F
`

val destDValue_def = Define`
  destDValue (DValue v) = v
`;

val _ = Hol_datatype`
  domain = D of int => int  (* lo/hi pair *)
`

(* dvalues : domain -> value list *)
val dvalues_def = Define`
  dvalues (D lo hi) = MAP Int [lo ..< hi]
`;

val _ = type_abbrev ("vname", ``:string``)
val _ = type_abbrev ("memory", ``:vname |-> value``)

val _ = Datatype`
  stmt = Assign write (dexpr list) (value list -> value)(* => string *)
       | AssignVar vname  expr
       | IfStmt expr stmt stmt
       | Malloc aname num value
       | Let vname expr
       | ForLoop string domain stmt
       | ParLoop string domain stmt
       | Seq ((memory # stmt) list)
       | Par ((memory # stmt) list)
       | Abort
       | Done
`

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

val (eval_rules, eval_ind, eval_cases) = Hol_reln`
  (∀m0 lm0 llm s1 m s1' rest.
    eval (m0, llm ⊌ lm0, s1) (m, llm ⊌ lm0, s1') ⇒
    eval (m0, lm0, Seq ((llm,s1)::rest)) (m, lm0, Seq ((llm,s1')::rest))) ∧

  (∀m lm llm rest. eval (m, lm, Seq ((llm, Done) :: rest)) (m, lm, Seq rest)) ∧

  (∀m lm. eval (m, lm, Seq []) (m, lm, Done)) ∧

  (∀m m' lm lm' g t e b s.
     eval (m,lm,if b then t else e) (m', lm', s) ∧
     evalexpr (lm ⊌ m) g = Bool b
   ⇒
     eval (m,lm,IfStmt g t e) (m', lm', s))

        ∧

  (∀m lm g t e.
     (∀b. evalexpr (lm ⊌ m) g ≠ Bool b) ⇒
     eval (m,lm,IfStmt g t e) (m,lm,Abort))

        ∧

  (∀rdes m0 m' lm0 aname i vf.
      EVERY isDValue rdes ∧
      upd_array m0 aname i (vf (MAP destDValue rdes)) = SOME m' ⇒
      eval (m0, lm0, Assign (aname, Value (Int i)) rdes vf)
           (m', lm0, Done)) ∧

  (∀rdes m0 lm0 aname i vf.
      EVERY isDValue rdes ∧
      upd_array m0 aname i (vf (MAP destDValue rdes)) = NONE ⇒
      eval (m0, lm0, Assign (aname, Value (Int i)) rdes vf)
           (m0, lm0, Abort))  ∧

  (∀m0 lm aname expr rds vf.
      ¬isValue expr ⇒
      eval (m0, lm, Assign (aname, expr) rds vf)
           (m0, lm, Assign (aname, Value (evalexpr (lm ⊌ m0) expr)) rds vf)) ∧

  (∀rds pfx aname expr sfx w vf m lm.
      rds = pfx ++ [Read aname expr] ++ sfx /\ ¬isValue expr ⇒
      eval (m, lm, Assign w rds vf)
           (m, lm,
            Assign w
                  (pfx ++ [Read aname (Value (evalexpr (lm ⊌ m) expr))] ++ sfx)
                  vf)) ∧

  (∀rds pfx aname i sfx w vf lm m.
      rds = pfx ++ [Read aname (Value (Int i))] ++ sfx ⇒
      eval (m, lm, Assign w rds vf)
           (m, lm, Assign w (pfx ++ [DValue (lookup_array m aname i)] ++ sfx) vf)) ∧

  (∀body d lm m vnm.
      eval (m, lm, ForLoop vnm d body)
           (m, lm, Seq (MAP (λdv. (lm |+ (vnm, dv), body)) (dvalues d)))) ∧

  (∀body d lm m vnm.
      eval (m, lm, ParLoop vnm d body)
           (m, lm, Par (MAP (λdv. (lm |+ (vnm, dv), body)) (dvalues d)))) ∧

  (∀llm lm m m' pfx ps s s' sfx.
      ps = pfx ++ [(llm, s)] ++ sfx ∧ eval (m, llm ⊌ lm, s) (m', llm ⊌ lm, s')
    ⇒
      eval (m, lm, Par ps) (m', lm, Par (pfx ++ [(llm, s')] ++ sfx))) ∧

  (∀llm lm m pfx ps sfx.
      ps = pfx ++ [(llm, Done)] ++ sfx ⇒
      eval (m, lm, Par ps) (m, lm, Par (pfx ++ sfx))) ∧

  (∀lm m. eval (m, lm, Par []) (m, lm, Done))
`

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
  (stmt_weight (Let v e) = 1) ∧
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

val loop_count_def = tDefine "loop_count" `
  (loopbag Abort = {| |}) ∧
  (loopbag Done = {| |}) ∧
  (loopbag (Assign w ds v) = {| 0 |}) ∧
  (loopbag (AssignVar v e) = {| 0 |}) ∧
  (loopbag (Malloc v d value) = {| 0 |}) ∧
  (loopbag (Let v e) = {| 0 |}) ∧
  (loopbag (IfStmt g t e) = BAG_UNION (loopbag t) (loopbag e)) ∧
  (loopbag (ForLoop v d s) = BAG_IMAGE SUC (loopbag s)) ∧
  (loopbag (ParLoop v d s) = BAG_IMAGE SUC (loopbag s)) ∧
  (loopbag (Seq stmts) =
     FOLDR (λms b. BAG_UNION (loopbag (SND ms)) b) {||} stmts) ∧
  (loopbag (Par stmts) =
     FOLDR (λms b. BAG_UNION (loopbag (SND ms)) b) {||} stmts)
` (WF_REL_TAC `measure stmt_size` >> simp[] >>
   Induct >> dsimp[definition "stmt_size_def"] >>
   rpt strip_tac >> res_tac >> simp[])
val _ = export_rewrites ["loop_count_def"]

val MAX_PLUS = store_thm(
  "MAX_PLUS",
  ``MAX x y + z = MAX (x + z) (y + z)``,
  rw[arithmeticTheory.MAX_DEF]);

val mlt_UNION_LCANCEL = store_thm(
  "mlt_UNION_LCANCEL",
  ``mlt R a b /\ FINITE_BAG c ==>
    mlt R (BAG_UNION a c) (BAG_UNION b c)``,

val eval_terminates = store_thm(
  "eval_terminates",
  ``∀a b. eval a b ⇒ inv_image (mlt (<) LEX (<)) (λ(m,lm,s). (loopbag s, stmt_weight s)) b a``,
  Induct_on `eval a b` >> rpt strip_tac >>
  lfs[pairTheory.LEX_DEF, pred_setTheory.MAX_SET_THM]
  >- (disj1_tac
  >- (Cases_on `b` >> fs[] >> simp[])
  >- (Cases_on `b` >> fs[]
      >- (Cases_on `loop_count e = 0` >> simp[MAX_PLUS])
      >- (Cases_on `loop_count t = 0` >> simp[MAX_PLUS]))
  >- (Cases_on `expr` >> lfs[])
  >- (Cases_on `expr` >> lfs[])


>> rpt strip_tac >>
  Cases_on `expr` >> fs[isValue_def]);

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

val t0 = ``(FEMPTY |+ ("a", Array (GENLIST (λn. Int &n) 20)), FEMPTY : memory,
         ForLoop "i" (D 0 10) (Assign ("a", VarExp "i") [Read "a" (VarExp "i")] incval))``

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
         ParLoop "i" (D 0 3) (Assign ("a", VarExp "i") [Read "a" (VarExp "i")] incval))``
(*
val res = chaineval 4 par_t;
val _ = print ("Length of result is " ^ Int.toString (length res) ^ "\n")
*)

val _ = export_theory();
