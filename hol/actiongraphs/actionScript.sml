open HolKernel Parse boolLib bossLib;

open pred_setTheory listRangeTheory listTheory
open finite_mapTheory
open lcsymtacs
open indexedListsTheory

val _ = new_theory "action";


val _ = IndDefLib.export_rule_induction "relation.TC_STRONG_INDUCT"
val _ = Hol_datatype`
  action = <|
    write : 'rw option;
    reads : 'rw list ;
    data : 'data;
    ident : 's_ident
     (* bogus ty variable name chosen to preserve order of
        type arguments *)
  |>
`;

val action_component_equality = theorem "action_component_equality"
val optset_def = Define`
  optset NONE = ∅ ∧
  optset (SOME x) = {x}
`;
val _ = overload_on ("set", ``optset``)
val _ = export_rewrites ["optset_def"]

val touches_def = Define`
  touches a1 a2 ⇔
     ¬DISJOINT (set a1.reads) (set a2.write) ∨
     ¬DISJOINT (set a2.reads) (set a1.write) ∨
     ¬DISJOINT (set a1.write) (set a2.write)
`;

val _ = set_mapped_fixity {term_name = "touches", fixity = Infix(NONASSOC, 450),
                           tok = "∼ₜ"}
val _ = set_mapped_fixity {term_name = "not_touches",
                           fixity = Infix(NONASSOC, 450),
                           tok = "≁ₜ"}
val _ = overload_on("not_touches", ``λa1 a2. ¬(touches a1 a2)``)

val touches_ignores_ident = store_thm(
  "touches_ignores_ident",
  ``(touches a1 (a2 with ident updated_by f) ⇔ touches a1 a2) ∧
    (touches (a1 with ident updated_by f) a2 ⇔ touches a1 a2)``,
  simp[touches_def]);
val _ = export_rewrites ["touches_ignores_ident"]

val touches_SYM = store_thm(
  "touches_SYM",
  ``touches a1 a2 ⇒ touches a2 a1``,
  simp[touches_def] >> rpt strip_tac >> simp[] >> metis_tac[DISJOINT_SYM]);

(* redundant if HOL's github issue #173 is fixed *)
val polydata_upd_def = Define`
  polydata_upd f a = <|
    reads := a.reads ;
    write := a.write ;
    data := f a.data;
    ident := a.ident
  |>`

val polydata_upd_ident = store_thm(
  "polydata_upd_ident[simp]",
  ``(polydata_upd f a).ident = a.ident``,
  simp[polydata_upd_def]);

val polydata_upd_reads_writes = store_thm(
  "polydata_upd_reads_writes[simp]",
  ``(polydata_upd f a).reads = a.reads ∧ (polydata_upd f a).write = a.write``,
  simp[polydata_upd_def]);

val polydata_upd_data = store_thm(
  "polydata_upd_data[simp]",
  ``(polydata_upd f a).data = f a.data``,
  simp[polydata_upd_def]);

val touches_dataupd = store_thm(
  "touches_dataupd[simp]",
  ``(polydata_upd f a ∼ₜ b ⇔ a ∼ₜ b) ∧
    (b ∼ₜ polydata_upd f a ⇔ b ∼ₜ a)``,
  simp[touches_def]);

val _ = export_theory();
