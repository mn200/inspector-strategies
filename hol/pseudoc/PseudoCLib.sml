structure PseudoCLib =
struct

open HolKernel simpLib

open listRangeTheory finite_mapTheory PseudoCTheory

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

end (* struct *)
