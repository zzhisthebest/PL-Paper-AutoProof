Set Implicit Arguments.

Require Import LibExtra.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode GeneralTyping Indep Equivalence RecordTypes.

Notation typ_objref T S := (typ_and (typ_bnd T) S) (only parsing).

Notation typ_objref_loc typing_mode T := (
  match (mode_refcaps' typing_mode) with
  | mode_refcaps_none => (typ_objref T typ_top)
  | mode_refcaps_mutability => (typ_objref T (typ_mut_marker typ_bot))
  end)(only parsing).

Inductive refcap_inert_mutability: typ -> varkind -> Prop :=
| refacp_inert_mutability_loc: refcap_inert_mutability (typ_mut_marker typ_bot) v_loc
| refacp_inert_mutability_ref Tbnd: refcap_inert_mutability (typ_mut_marker Tbnd) v_ref
.

Definition refcap_inert_type {typing_mode: Mode} T vk :=
  match (mode_refcaps' typing_mode) with
  | mode_refcaps_none => refcap_typ T \{}
  | mode_refcaps_mutability => refcap_inert_mutability T vk
  end.

Notation obj_typ_is cond T S vk := (
      record_type T ->
      refcap_inert_type S vk ->
      typ_indep_b 0 T ->
      cond (typ_objref T S) vk) (only parsing).

Notation fun_typ_is cond S T := (
      cond (typ_fun S T)) (only parsing).

Notation fun_type U := (exists S T, fun_typ_is (eq U) S T) (only parsing).

Notation obj_type typing_mode U := (exists T S, obj_typ_is typing_mode (eq U) T S) (only parsing).

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive inert_vk: varkind -> Prop :=
  | inert_vk_loc: inert_vk v_loc
  | inert_vk_ref: inert_vk v_ref.

Inductive inert_typ: typ -> varkind -> Prop :=

  | inert_typ_fun S T vk:
    mode_has_fun typing_mode ->
    fun_typ_is inert_typ S T vk

  | inert_typ_obj T S vk:
    obj_typ_is inert_typ T S vk.

Definition inert_type T := exists vk, inert_typ T vk.

Inductive inert: ctx -> Prop :=
  | inert_empty: inert ctx_empty
  | inert_push G x vk T:
      inert G ->
      inert_vk vk ->
      inert_typ T vk ->
      x §# G ->
      x \notin ctx_fv G ->
      x \notin fv T ->
      inert (G § x / vk ~ T).

End WithTypingMode.

Arguments inert [typing_mode].

Arguments inert_typ {typing_mode}.

Arguments inert_type {typing_mode}.

Inductive fresh_telescope : ctx -> Prop :=
  | fresh_telescope_empty : fresh_telescope ctx_empty
  | fresh_telescope_push : forall G x vk T,
      fresh_telescope G ->
      x §# G ->
      x \notin ctx_fv G ->
      x \notin fv T ->
      fresh_telescope (G § x / vk ~ T).

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
