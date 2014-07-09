open HolKernel Parse boolLib bossLib;

open realTheory transcTheory PseudoCTheory

val _ = new_theory "PseudoCOps";

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

val divval_def = Define`
  divval [Real r; Real s] = Real (r / s) ∧
  divval [Int i; Int j] = Int (i / j) ∧
  divval _ = Error
`
val multval_def = Define`
  multval [Real r; Real s] = Real (r * s) ∧
  multval [Int i; Int j] = Int (i * j) ∧
  multval _ = Error
`

(* FIXME: don't know how to define exponent function. *)
(* also how do we convert to Real? *)
val expval_def = Define`
  expval [Real s] = Real(exp(s)) ∧
  expval [Int j] = Real(exp(real_of_int j)) ∧
  expval _ = Error
`

val _ = export_theory();
