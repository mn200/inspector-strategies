structure PseudoCLib =
struct

open HolKernel simpLib

open listRangeTheory finite_mapTheory PseudoCTheory PseudoCOpsTheory
open PseudoCHDAGTheory

open lcsymtacs intReduce

fun newrule t =
    eval_cases |> Q.SPEC `(m,^t)` |> SIMP_RULE (srw_ss()) []

val evalths = [newrule ``Seq []``, newrule ``Done``,
               newrule ``ForLoop v d b``, newrule ``Assign w rds vf``,
               newrule ``ParLoop v d b``, newrule ``Par []``,
               newrule ``Par (h::t)``,
               newrule ``IfStmt g t e``, newrule ``Malloc v n value``,
               newrule ``Label l s``, newrule ``Local var e s``]

val option_CASE_Cong = prove(
  ``M1 = M2 ⇒ option_CASE M1 n f = option_CASE M2 n f``,
  simp[]);

val alt_upd_var = prove(
  ``upd_var m vnm v =
      case FLOOKUP m vnm of
          NONE => NONE
        | SOME (Array _) => NONE
        | SOME _ => case v of
                        Error => NONE
                      | Array _ => NONE
                      | _ => SOME(m |+ (vnm,v))``,
  simp[upd_var_def] >> Cases_on `v` >> simp[FLOOKUP_DEF] >>
  Cases_on `vnm ∈ FDOM m` >> simp[] >>
  Cases_on `m ' vnm` >> simp[]);

val evalseq_cons = prove(
  ``∀cs c. eval (m0, Seq (c::cs)) mr ⇔
           if c = Done then
             EVERY ((=) Done) cs ∧ mr = (m0,Done) ∨
             (∃m r'. eval(m0,Seq cs) (m,r') ∧
                     ((∃cs'. r' = Seq cs' ∧ mr = (m,Seq (Done::cs'))) ∨
                      r' = Abort ∧ mr = (m, Abort)))
           else if c = Abort then mr = (m0, Abort)
           else
             ∃c' m. eval (m0,c) (m,c') ∧ mr = (m,Seq(c'::cs))``,
  dsimp[newrule ``Seq(h::t)``, listTheory.APPEND_EQ_CONS] >>
  map_every qx_gen_tac [`cs`, `c`] >> reverse (Cases_on `c = Done`) >>
  simp[newrule ``Done``]
  >- (Cases_on `c = Abort` >> simp[newrule ``Abort``] >> metis_tac[]) >>
  Cases_on `mr = (m0,Done)` >> simp[] >>
  Cases_on `∃m. mr = (m,Abort)` >> fs[]
  >- (simp[newrule ``Seq cs``] >> metis_tac[]) >>
  simp[newrule ``Seq cs``] >> dsimp[] >> metis_tac[])

val bb = prove(``(!b. b) = F``, SIMP_TAC bool_ss [FORALL_BOOL])

val atomic = prove(
  ``∀m0 s mr.
      (m0, Atomic s) ---> mr ⇔
      case graphOf [] m0 s of
          SOME (m, _) => mr = (m, Done)
        | NONE => unint ((m0, Atomic s) ---> mr)``,
  simp[Once eval_cases, SimpLHS, pairTheory.FORALL_PROD] >>
  rpt gen_tac >>
  `graphOf [] m0 s = NONE ∨ ∃m g. graphOf [] m0 s = SOME(m,g)`
    by metis_tac[optionTheory.option_CASES, pairTheory.pair_CASES]
  >- (simp[markerTheory.unint_def] >> simp[SimpRHS, Once eval_cases]) >>
  simp[] >> metis_tac[graphOf_correct


fun subeval t =
    (SIMP_CONV (srw_ss() ++ INT_REDUCE_ss)
              (FLOOKUP_UPDATE :: lookup_v_def :: evalexpr_def ::
               evalseq_cons :: alt_upd_var :: Cong option_CASE_Cong ::
               PULL_EXISTS :: dvalues_def :: ssubst_def :: esubst_def ::
               dsubst_def :: listTheory.APPEND_EQ_CONS :: LET_THM ::
               minusval_def :: plusval_def :: cmpGTEval_def ::
               bb :: maxval_def :: upd_write_def :: eval_lvalue_def ::
               lookup_array_def :: upd_array_def :: listTheory.LUPDATE_compute::
               evalths) THENC
     SIMP_CONV (srw_ss() ++ INT_REDUCE_ss)
               [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, EXISTS_OR_THM,
                evalexpr_def, lookup_v_def, lookup_array_def,
                minusval_def, plusval_def, cmpGTEval_def,
                bb,
                FLOOKUP_UPDATE])
      t

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

datatype ('a,'b) chainResult = OK of 'a | Error of 'b
fun resmap f (OK x) = OK (f x) | resmap f (Error e) = Error e
fun chain m eq (f: 'a -> 'b list) (d: 'b -> 'a) s0 = let
  fun history_to_next h =
      case h of
          (bs as (b::_), a) =>
          (case f (d b) of
               [] => [h]
             | newbs => map (fn b' => (b'::bs, a)) newbs)
        | ([], a) => map (fn b => ([b], a)) (f a)

  fun pluralise n str =
      Int.toString n ^ " " ^ str ^ (if n = 1 then "" else "s")

  fun recurse n hs =
    if n <= 0 then OK hs
    else let
      val acc' = OK (op_mk_set eq (List.concat (map history_to_next hs)))
                 handle Interrupt => raise Interrupt
                      | e => Error(e, hs)
      val _ = case acc' of
                  OK acc' =>
                  print ("Stage " ^ Int.toString (m - n + 1) ^ ": " ^
                         pluralise (length acc')  "result" ^ "\n")
                | Error e => print ("Stage " ^ Int.toString (m - n + 1) ^
                                    " has an error!\n")
    in
      case acc' of
          OK x => recurse (n - 1) x
        | Error e => Error e
    end
in
  resmap (map (fn (bs, a) => (a, List.rev bs))) (recurse m [([], s0)])
end

fun chaineval n t = let
  val d = rand o concl
in
  resmap
    (map (fn (a, bs) => d (last bs)))
    (chain n
           (fn (bs1,a1) => fn (bs2, a2) => aconv (d (hd bs1)) (d (hd bs2)))
           eval1
           d
           t)
end

end (* struct *)
