open HolKernel Parse boolLib bossLib;

open stringTheory

val _ = new_theory "ast";

val _ = Hol_datatype`
  value = Int of int | Real of real | Array of value | Bool of bool| Error
`;

val _ = Hol_datatype`
  expr = VarExp of string
       | ISub of string => expr
       | Opn of (value list -> value) => expr list
       | Plus of expr => expr
       | Const of value
       | Value of value
`

val isValue_def = Define`
  isValue (Value _) = T /\
  isValue _ = F
`

val _ = type_abbrev ("write", ``:string # expr``)

val _ = Hol_datatype`
  dexpr = DValue of value
        | Read of aname => expr
        | Convert of expr
`

val isDValue_def = Define`
  isDValue (DValue _) = T ∧
  isDValue _ = F
`

val _ = Hol_datatype`
  domain = D of num => num
`

val _ = Hol_datatype`
  stmt = Assign of write => dexpr list => (value list -> value)(* => string *)
       | ForLoop of string => domain => stmt
       | ParLoop of string => domain => stmt
       | Seq of (local_memory # stmt) list
       | Par of (local_memory # stmt) list
       | Done
`

(* lookup_array : memory -> string -> num -> value *)
(* lookup_v : memory -> string -> value *)

(* evalexpr : memory -> expr -> value *)
val evalexpr_def = Define`
  evalexpr m (ISub(nm, i_expr)) =
    let iv = evalexpr m i_expr
    in
       lookup_array m nm iv /\
  evalexpr m (VarExp nm) = lookup_v m nm /\
  evalexpr m (Const v) = v /\
  evalexpr m (Plus e1 e2) =
       case (evalexpr m e1, evalexpr m e2) of
           (Int i, Int j) => Int (i + j)
         | _ => Error /\
  evalexpr m (Opn vf elist) = vf (MAP (evalexpr m) elist)
`

val (eval_rules, eval_ind, eval_cases) = Hol_reln`

  eval (m0, llm, s1) (m, llm, s1') ==>
  eval (m0, lm0, Seq ((llm,s1)::rest)) (m, lm0, Seq ((llm,s1')::rest))

  eval (m, lm, Seq ((llm, Done) :: rest)) (m, lm, Seq rest)

  eval (m, lm, Seq []) (m, lm, Done)

  EVERY isDValue rdes ==>
  eval (m0, lm0, Assign (aname, Value (Int i))) rdes vf)
       (m0 updated_at aname[i] = vf rdes, lm0, Done)

  eval (m0, lm, Assign (aname, expr0) rds vf)
       (m0, lm, Assign (aname, Value (evalexpr m0 expr0)) rds vf)

  rds = pfx ++ [Read aname expr] ++ sfx /\ ¬isValue expr ⇒
  eval (m, lm, Assign w rds vf)
       (m, lm,
        Assign w
               (pfx ++ [Read aname (Value (evalexpr (m ∪ lm) expr))] ++ sfx)
               vf)

  rds = pfx ++ [Read aname (Value (Int i))] ++ sfx
  eval (m, lm, Assign w rds vf)
       (m, lm, Assign w (pfx ++ [DValue (lookup_array m aname i)] ++ sfx) vf)


  eval (m, lm, ForLoop vnm d body)
       (m, lm, Seq (MAP (λdv. (lm(vnm := dv), body)) (values d)))

  eval (m, lm, ParLoop vnm d body)
       (m, lm, Par (MAP (λdv. (lm(vnm := dv), body) (values d)))

  pfx ++ [(llm, s)] ++ sfx ∧
  eval (m, llm, s) (m', llm', s')
    ⇒
  eval (m, lm, Par ps) (m', lm, Par (pfx ++ [(llm', s')] ++ sfx))


  pfx ++ [(llm, Done)] ++ sfx = ps ⇒
  eval (m, lm, Par ps) (m, lm, Par (pfx ++ sfx))

  eval (m, lm, Par []) (m, lm, Done)
`





val _ = export_theory();
