open HolKernel Parse boolLib bossLib;

val _ = new_theory "minilang";

val _ = Datatype`value = Num num | List (value list)`

(* type of listsort will be: value -> value option *)
val listlength_def = Define`
  (listlength (Num n) = NONE) ∧
  (listlength (List l) = SOME (Num (LENGTH l)))
`;

val sample1 = EVAL ``listlength (List [Num 1; Num 2])``

open stringTheory
val _ = Datatype`
  expr = Var string | Plus expr expr | Literal num |
         (* Fork expr expr | *) Assign string expr
`;

val evalexpr_def = Define`
  (evalexpr env (Var s) = (env, env s)) /\
  (evalexpr env (Plus e1 e2) =
   let (env1, n1) = evalexpr env e1 in
   let (env2, n2) = evalexpr env1 e2
   in
     (env2, n1 + n2)) /\
  (evalexpr env (Literal n) = (env, n)) /\
  (evalexpr env (Assign v e) = let (env', result) = evalexpr env e
                               in
                                 ((λv'. if v' = v then result
                                        else env' v'),
                                  result)) (* /\
  (evalexpr env (Fork e1 e2) = ????) *)
`;

val sample2 =
    EVAL ``evalexpr (λv. if v = "x" then 3 else 4)
                    (Plus (Var "x") (Literal 10))``


val _ = export_theory();
