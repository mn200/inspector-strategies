open HolKernel Parse boolLib bossLib;

open lcsymtacs
open pred_setTheory
open monadsyntax
open forLoopTheory

val _ = new_theory "monadicPrimitives";

val _ = overload_on("assert", ``OPTION_GUARD``)
val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)
val _ = ParseExtras.tight_equality()

val _ = type_abbrev ("mvector", ``:(num -> 'a) # num``)
val SAT_ss = SatisfySimps.SATISFY_ss
val _ = augment_srw_ss [SAT_ss]

val vsub_def = Define`
  vsub (mv, sz) i = if i < sz then SOME (mv i) else NONE
`

val _ = set_fixity "'" (Infixl 2000)
val _ = overload_on ("'", ``vsub``)
val _ = overload_on ("vsz", ``SND : (num -> 'a) # num -> num``)

val empty_v_def = Define`empty_v n v = (K v, n)`

val vsz_empty_v = store_thm(
  "vsz_empty_v",
  ``vsz (empty_v n v) = n``,
  simp[empty_v_def]);
val _ = export_rewrites ["vsz_empty_v"]

val empty_v_sub = store_thm(
  "empty_v_sub",
  ``empty_v n v ' i = do assert(i < n); SOME v od``,
  simp[empty_v_def, vsub_def] >> Cases_on `i < n` >> simp[]);
val _ = export_rewrites ["empty_v_sub"]

val IGNORE_BIND_ASSOC = store_thm(
  "IGNORE_BIND_ASSOC",
  ``OPTION_BIND (OPTION_IGNORE_BIND m1 m2) f =
    OPTION_IGNORE_BIND m1 (OPTION_BIND m2 f)``,
  Cases_on `m1` >> simp[]);
val _ = export_rewrites ["IGNORE_BIND_ASSOC"]

val update_def = Define`
  update (mv,sz) d r = if d < sz then SOME ((d =+ r) mv, sz) else NONE
`;

val mvector_to_list_def = Define`
  mvector_to_list (f,sz) = REVERSE (FOR (0,sz) (λi l. f i :: l) [])
`;


val _ = export_theory();
