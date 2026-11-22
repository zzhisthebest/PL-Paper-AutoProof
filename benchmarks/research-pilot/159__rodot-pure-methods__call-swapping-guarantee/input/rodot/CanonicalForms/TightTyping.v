Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax TypingMode GeneralTyping.

Require Import PreciseTyping Equivalence EWeakening Indep RecordTypes InertContext.

Class TightTyping (A : Set) := tight_typing : ctx -> renv -> A -> typ -> Prop.

Notation "G '⁏' e ⊢# t '∶' T" := (tight_typing G e t T) (at level 40, e at level 39, t at level 59).

Class DecTightTyping (A : Set) := dec_typing : ctx -> renv -> A -> dec -> Prop.

Notation "G '⁏' e ⊢# t '∶d' T" := (dec_typing G e t T) (at level 40, e at level 39, t at level 59).

Reserved Notation "G '⁏' e ⊢# t '<:' T" (at level 40, e at level 39, t at level 59).

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive ty_trm_t : TightTyping var :=




| ty_var_t : forall G e x T,
    ctx_binds x T G ->
    G⁏e ⊢# x ∶ T




| ty_rec_intro_t : forall G e x T,
    typ_indep_b 0 T ->



    (mode_incap' typing_mode = mode_incap_structural -> (G⁏e ⊢ (open x T) ∶icp (open x T))) ->
    (mode_incap' typing_mode = mode_incap_nocap -> (G⁏e ⊢# typ_nocap <: (open x T))) ->
    G⁏e ⊢# x ∶ open x T ->
    G⁏e ⊢# x ∶ typ_bnd T




| ty_rec_elim_t : forall G e x T,
    typ_indep_b 0 T ->
    G⁏e ⊢# x ∶ typ_bnd T ->
    G⁏e ⊢# x ∶ open x T





| ty_and_intro_t : forall G e x T U,
    G⁏e ⊢# x ∶ T ->
    G⁏e ⊢# x ∶ U ->
    G⁏e ⊢# x ∶ typ_and T U





| ty_sub_t : forall G e x T U,
    G⁏e ⊢# x ∶ T ->
    G⁏e ⊢# T <: U ->
    G⁏e ⊢# x ∶ U

| ty_var_mut_top_t : forall G e x T,
    mode_has_mutability typing_mode ->
    G⁏e ⊢# x ∶ T ->
    G⁏e ⊢# x ∶ (typ_mut_marker typ_top)


with subtyp_t : ctx -> renv -> typ -> typ -> Prop :=



| subtyp_top_t: forall G e T,
    G⁏e ⊢# T <: typ_top



| subtyp_bot_t: forall G e T,
    G⁏e ⊢# typ_bot <: T



| subtyp_refl_t: forall G e T,
    G⁏e ⊢# T <: T





| subtyp_trans_t: forall G e S T U,
    G⁏e ⊢# S <: T ->
    G⁏e ⊢# T <: U ->
    G⁏e ⊢# S <: U



| subtyp_and11_t: forall G e T U,
    G⁏e ⊢# typ_and T U <: T



| subtyp_and12_t: forall G e T U,
    G⁏e ⊢# typ_and T U <: U





| subtyp_and2_t: forall G e S T U,
    G⁏e ⊢# S <: T ->
    G⁏e ⊢# S <: U ->
    G⁏e ⊢# S <: typ_and T U



| subtyp_or11_t: forall G e T U,
    G⁏e ⊢# T <: typ_or T U



| subtyp_or12_t: forall G e T U,
    G⁏e ⊢# U <: typ_or T U





| subtyp_or2_t: forall G e S T U,
    G⁏e ⊢# S <: T ->
    G⁏e ⊢# U <: T ->
    G⁏e ⊢# typ_or S U <: T






| subtyp_fld_t: forall G e a T1 T2 U1 U2,
    G⁏e ⊢# T1 <: T2 ->
    G⁏e ⊢# U1 <: U2 ->
    G⁏e ⊢# typ_rcd (dec_fld a T2 U1) <: typ_rcd (dec_fld a T1 U2)






| subtyp_typ_t: forall G e A S1 T1 S2 T2,
    (forall x, G⁏e ⊢# (open x S2) <: (open x S1)) ->
    (forall x, G⁏e ⊢# (open x T1) <: (open x T2)) ->
    G⁏e ⊢# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)




| subtyp_sel2_t: forall G e x A y TL TU U,
    G ⊢! x ∶ U ⪼ typ_rcd (dec_typ A TL TU) ->
    G⁏e ⊢# (open y TL) <: typ_sel (avar_f x) A (avar_f y)




| subtyp_sel1_t: forall G e x A y TL TU U,
    G ⊢! x ∶ U ⪼ typ_rcd (dec_typ A TL TU) ->
    G⁏e ⊢# typ_sel (avar_f x) A (avar_f y) <: (open y TU)







| subtyp_fun_t: forall L G e S1 T1 S2 T2,
    mode_has_fun typing_mode ->
    G⁏e ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G § x / v_par ~ S2 ⁏e ⊢ open x T1 <: open x T2) ->
    G⁏e ⊢# typ_fun S1 T1 <: typ_fun S2 T2







| subtyp_met_t: forall L G e m TC1 TZ1 TR1 TC2 TZ2 TR2,
    G⁏e ⊢# TZ2 <: TZ1 ->
    (forall x, x \notin L ->
    G § x / v_par ~ TZ2 ⁏e ⊢ open x TC2 <: open x TC1) ->

    (mode_has_sef typing_mode -> typ_indep_b 0 TC2 -> typ_indep_b 0 TC1) ->
    (forall x, x \notin L ->
     forall y, y <> x -> y \notin L ->
    G § x / v_par ~ TZ2 § y / v_recv ~ (open x TC2) ⁏e ⊢ open x (open_rec 1 y TR1) <: open x (open_rec 1 y TR2) ) ->
    G⁏e ⊢# typ_rcd (dec_met m TC1 TZ1 TR1) <: typ_rcd (dec_met m TC2 TZ2 TR2)




| subtyp_tyq_t: forall G e T1 T2,
    e ⊢ T1 ≈ T2 ->
    G⁏e ⊢# T1 <: T2



| subtyp_typ_and_t: forall G e A S1 T1 S2 T2,
    G⁏e ⊢#
     typ_and
       (typ_rcd (dec_typ A S1 T1))
       (typ_rcd (dec_typ A S2 T2))
     <: typ_rcd (dec_typ A (typ_or S1 S2) (typ_and T1 T2))



| subtyp_dist_t: forall G e T1 T2 T3,
    G⁏e ⊢#
      typ_and T1 (typ_or T2 T3)
      <: typ_or (typ_and T1 T2) (typ_and T1 T3)



| subtyp_nocap_bnd_t G e T:
    G⁏e ⊢# typ_nocap <: typ_bnd T



| subtyp_nocap_typ_t G e A T1 T2:
    G⁏e ⊢# typ_nocap <: typ_rcd (dec_typ (typ_label_normal A) T1 T2)



| subtyp_nocap_fld_t G e a T1 T2:
    G⁏e ⊢# typ_nocap <: typ_rcd (dec_fld a T1 T2)



| subtyp_nocap_met_t G e a TC TZ TR:
    G⁏e ⊢# typ_nocap <: typ_rcd (dec_met a TC TZ TR)




| subtyp_nocap_fun_t G e TZ TR:
    mode_has_fun typing_mode ->
    G⁏e ⊢# typ_nocap <: typ_fun TZ TR



| subtyp_nocap_mut_top_boundless_t G e T1 T2:
    mode_has_top_nm_subtype_boundless typing_mode ->
    G⁏e ⊢# typ_top <: (typ_or typ_nocap (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability) T1 T2)))



| subtyp_nocap_mut_top_complement_t G e:
    mode_has_top_nm_complement typing_mode ->
    G⁏e ⊢# typ_top <: (typ_or typ_nocap (typ_mut_marker typ_bot) )



| subtyp_nocap_mut_bot_t G e:
    mode_has_top_nm_complement typing_mode ->
    G⁏e ⊢# (typ_and typ_nocap (typ_mut_marker typ_bot) ) <: typ_bot



| subtyp_mut_top_t G e:
    mode_has_mut_top typing_mode ->
    G⁏e ⊢# typ_top <: (typ_mut_marker typ_top)

where "G '⁏' e '⊢#' T '<:' U" := (subtyp_t G e T U).

Scheme ts_ty_trm_t_mut := Induction for ty_trm_t Sort Prop
with   ts_subtyp_t     := Induction for subtyp_t Sort Prop.

Combined Scheme ts_t_mutind from ts_ty_trm_t_mut, ts_subtyp_t.

End WithTypingMode.

Notation "G '⁏' e ⊢# T '<:' U" := (subtyp_t _ G e T U).
