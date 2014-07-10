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
val _ = overload_on("/", ``\v1 v2. divval[v1;v2]``)

val multval_def = Define`
  multval [Real r; Real s] = Real (r * s) ∧
  multval [Int i; Int j] = Int (i * j) ∧
  multval _ = Error
`
val _ = overload_on("*", ``\v1 v2. multval[v1;v2]``)

(* MN assumes it's desirable to have exp work on integer arguments *)
val expval_def = Define`
  expval [Real s] = Real(exp(s)) ∧
  expval [Int j] = Real(exp(real_of_int j)) ∧
  expval _ = Error
`
val _ = overload_on("exp", ``\v. expval[v]``)

val _ = export_theory();
