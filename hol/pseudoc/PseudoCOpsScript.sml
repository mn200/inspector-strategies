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
val _ = overload_on("+", ``\v1 v2. Opn plusval[v1;v2]``)

val minusval_def = Define`
  minusval [Real r; Real s] = Real (r - s) ∧
  minusval [Int i; Int j] = Int (i - j) ∧
  minusval _ = Error
`
val _ = overload_on("-", ``\v1 v2. Opn minusval[v1;v2]``)

val divval_def = Define`
  divval [Real r; Real s] = Real (r / s) ∧
  divval [Int i; Int j] = Int (i / j) ∧
  divval _ = Error
`
val _ = overload_on("/", ``\v1 v2. Opn divval[v1;v2]``)

val multval_def = Define`
  multval [Real r; Real s] = Real (r * s) ∧
  multval [Int i; Int j] = Int (i * j) ∧
  multval _ = Error
`
val _ = overload_on("*", ``\v1 v2. Opn multval[v1;v2]``)

(* it would equally be fine to write

      Real (if r < s then s else r)

   and

      Int (if i < j then i else j)

   The fact that real max is called "max" and integer max is called "int_max" is
   unfortunate (and totally fixable).

*)
val maxval_def = Define`
  maxval [Real r; Real s] = Real (max r s) ∧
  maxval [Int i; Int j] = Int (int_max i j) ∧
  maxval _ = Error
`
val _ = overload_on("max", ``\v1 v2. Opn maxval[v1;v2]``)

val cmpGTval_def = Define`
  cmpGTval [Real r; Real s] = Bool (r > s) ∧
  cmpGTval [Int i; Int j] = Bool (i > j) ∧
  cmpGTval _ = Error
`
val _ = overload_on(">", ``\v1 v2. Opn cmpGTval[v1;v2]``)

val cmpGTEval_def = Define`
  cmpGTEval [Real r; Real s] = Bool (r >= s) ∧
  cmpGTEval [Int i; Int j] = Bool (i >= j) ∧
  cmpGTEval _ = Error
`
val _ = overload_on(">=", ``\v1 v2. Opn cmpGTEval[v1;v2]``)

val cmpLTval_def = Define`
  cmpLTval [Real r; Real s] = Bool (r < s) ∧
  cmpLTval [Int i; Int j] = Bool (i < j) ∧
  cmpLTval _ = Error
`
val _ = overload_on("<", ``\v1 v2. Opn cmpLTval[v1;v2]``)

val cmpLTEval_def = Define`
  cmpLTEval [Real r; Real s] = Bool (r <= s) ∧
  cmpLTEval [Int i; Int j] = Bool (i <=j) ∧
  cmpLTEval _ = Error
`
val _ = overload_on("<=", ``\v1 v2. Opn cmpLTEval[v1;v2]``)

val cmpEQval_def = Define`
  cmpEQval [Real r; Real s] = Bool (r = s) ∧
  cmpEQval [Int i; Int j] = Bool (i = j) ∧
  cmpEQval _ = Error
`
val _ = overload_on("==", ``\e1 e2. Opn cmpEQval[e1;e2]``)
val _ = set_fixity "==" (Infix(NONASSOC, 450))

(* MN assumes it's desirable to have exp work on integer arguments *)
val expval_def = Define`
  expval [Real s] = Real(exp(s)) ∧
  expval [Int j] = Real(exp(real_of_int j)) ∧
  expval _ = Error
`
val _ = overload_on("exp", ``\v. Opn expval[v]``)

val _ = export_theory();
