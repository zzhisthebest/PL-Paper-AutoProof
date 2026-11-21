Set Implicit Arguments.

Require Import LibExtra.

Require Import Coq.Program.Equality.

Inductive mode :=
  | basic
  | basic_no_fun
  | basic_incap
  | basic_sef_typing
  | rodot
  | rodot_top_nm
  | rodot_nm_compl
  | rodot_nm_muttop
  | rodot_nm_compl_muttop
  | rodot_sef.

Class Mode := mode_m: mode.

Definition mode_has_fun' m: bool := match m with
| basic | basic_sef_typing => true
| _ => false
end.

Notation mode_has_fun m := ((mode_has_fun' m) = true)(only parsing).

Definition mode_has_mutability' m: bool := match m with
| rodot | rodot_top_nm | rodot_nm_compl | rodot_nm_muttop | rodot_nm_compl_muttop | rodot_sef => true
| _ => false
end.

Notation mode_has_mutability m := ((mode_has_mutability' m) = true)(only parsing).

Inductive mode_visibility := mode_visibility_all | mode_visibility_hide_method.

Definition mode_visibility' m: mode_visibility := match m with
| rodot | rodot_top_nm | rodot_nm_compl | rodot_nm_muttop | rodot_nm_compl_muttop | rodot_sef => mode_visibility_hide_method
| _ => mode_visibility_all
end.

Notation mode_has_visibility m := ((mode_visibility' m) = mode_visibility_hide_method)(only parsing).

Inductive mode_refcaps := mode_refcaps_none | mode_refcaps_mutability.

Definition mode_refcaps' m: mode_refcaps := match m with
| rodot | rodot_top_nm | rodot_nm_compl | rodot_nm_muttop | rodot_nm_compl_muttop | rodot_sef => mode_refcaps_mutability
| _ => mode_refcaps_none
end.

Inductive mode_refcap_corr := mode_refcap_corr_same | mode_refcap_corr_ref_mutability.

Definition mode_refcap_corr' m: mode_refcap_corr := match m with
| rodot | rodot_top_nm | rodot_nm_compl | rodot_nm_muttop | rodot_nm_compl_muttop  | rodot_sef => mode_refcap_corr_ref_mutability
| _ => mode_refcap_corr_same
end.

Inductive mode_viewpoint_adaptation := mode_viewpoint_adaptation_same | mode_viewpoint_adapt_mutability.

Definition mode_viewpoint_adaptation' m: mode_viewpoint_adaptation := match m with
| rodot | rodot_top_nm | rodot_nm_compl | rodot_nm_muttop | rodot_nm_compl_muttop | rodot_sef => mode_viewpoint_adapt_mutability
| _ => mode_viewpoint_adaptation_same
end.

Inductive mode_objlit_refcaps := mode_objlit_refcaps_none | mode_objlit_refcaps_mutable.

Definition mode_objlit_refcaps' m: mode_objlit_refcaps := match m with
| rodot | rodot_top_nm | rodot_nm_compl | rodot_nm_muttop | rodot_nm_compl_muttop | rodot_sef => mode_objlit_refcaps_mutable
| _ => mode_objlit_refcaps_none
end.

Inductive mode_top_nm := mode_top_nm_none | mode_top_nm_subtype | mode_top_nm_complement.

Definition mode_top_nm' m: mode_top_nm := match m with
| rodot_top_nm | rodot_nm_muttop | rodot_sef => mode_top_nm_subtype
| rodot_nm_compl | rodot_nm_compl_muttop  => mode_top_nm_complement
| _ => mode_top_nm_none
end.

Definition mode_has_top_nm_subtype' m: bool := match (mode_top_nm' m) with
| mode_top_nm_subtype | mode_top_nm_complement => true
| _ => false
end.

Notation mode_has_top_nm_subtype m := ((mode_has_top_nm_subtype' m) = true)(only parsing).

Notation mode_has_top_nm_complement m := ((mode_top_nm' m) = mode_top_nm_complement)(only parsing).

Notation mode_has_top_nm_subtype_boundless m := ((mode_top_nm' m) = mode_top_nm_subtype)(only parsing).

Inductive mode_mut_top := mode_mut_top_none | mode_mut_top_subtype.

Definition mode_mut_top' m: mode_mut_top := match m with
| rodot_nm_muttop | rodot_nm_compl_muttop => mode_mut_top_subtype
| _ => mode_mut_top_none
end.

Notation mode_has_mut_top m := ((mode_mut_top' m) = mode_mut_top_subtype)(only parsing).

Inductive mode_incap := mode_incap_none | mode_incap_structural | mode_incap_nocap.

Definition mode_incap' m: mode_incap := match m with
| basic_incap | rodot_top_nm | rodot_nm_muttop | rodot_nm_compl | rodot_nm_compl_muttop | rodot_sef => mode_incap_nocap
| rodot => mode_incap_structural
| _ => mode_incap_none
end.

Definition mode_has_incap' m: bool := match (mode_incap' m) with
| mode_incap_none => false
| _ => true
end.

Notation mode_has_incap m := ((mode_has_incap' m) = true)(only parsing).

Inductive mode_ty_inv := mode_ty_inv_flat | mode_ty_inv_layered.

Definition mode_ty_inv' m: mode_ty_inv := match m with
| basic_incap | rodot_top_nm | rodot_nm_muttop | rodot_nm_compl | rodot_nm_compl_muttop | rodot_sef => mode_ty_inv_layered
| _ => mode_ty_inv_flat
end.

Inductive mode_sef := mode_sef_none | mode_sef_guarantee.

Definition mode_sef' m : mode_sef := match m with
| rodot_sef |  rodot_nm_muttop | rodot_nm_compl | rodot_nm_compl_muttop  | basic_sef_typing => mode_sef_guarantee
| _ => mode_sef_none
end.

Notation mode_has_sef m := ((mode_sef' m) = mode_sef_guarantee)(only parsing).
