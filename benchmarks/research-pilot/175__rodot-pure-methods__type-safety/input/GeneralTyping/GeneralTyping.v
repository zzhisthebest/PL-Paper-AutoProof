Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import Equivalence Indep.

Require Export TypingMode TypingContext.

Notation EnvProperty A B := (forall (e:renv) (v: A) (T: B), Prop).

Notation TypingProperty A B := (forall (G:ctx) (Go: objctx) (e:renv) (v: A) (T: B), Prop).

Class DecTyping (A : Set) := obj_dec_typing: ctx -> objctx -> renv -> A -> dec -> Prop.

Notation "G '§§' Go '⁏' e ⊢ t '∶d' T" := (obj_dec_typing G Go e t T) (at level 40, Go at level 39, e at level 39, t at level 59).

Class Typing (A : Set) := obj_typing: ctx -> objctx -> renv -> A -> typ -> Prop.

Notation "G '§§' Go '⁏' e ⊢ t '∶' T" := (obj_typing G Go e t T) (at level 40, Go at level 39, e at level 39, t at level 59).

Notation typing G e a t := (obj_typing G objctx_empty e a t).

Notation "G '⁏' e ⊢ t '∶' T" := (typing G e t T) (at level 40, e at level 39, t at level 59).

Notation dec_typing G e a d := (obj_dec_typing G objctx_empty e a d).

Notation "G '⁏' e ⊢ t '∶d' T" := (dec_typing G e t T) (at level 40, e at level 39, t at level 59).

Class Subtyping := subtyping: ctx -> objctx -> renv -> typ -> typ -> Prop.

Notation "G '⁏' e '⊢' T '<:' U" := (subtyping G objctx_empty e T U) (at level 40, e at level 39, T at level 59).

Class ReferenceIncapacitate := obj_ref_incap :
                                 ctx -> objctx -> renv -> typ -> typ -> Prop.

Notation "G '§§' Go '⁏' e  ⊢ T1 '∶icp' T2" := (obj_ref_incap G Go e T1 T2)
  (at level 40, Go at level 39, e at level 39, T1 at level 59, T2 at level 59).

Notation ref_incap G e T1 T2 := (obj_ref_incap G objctx_empty e T1 T2).

Notation "G '⁏' e ⊢ T1 '∶icp' T2" :=
  (ref_incap G e T1 T2)
    (at level 40, e at level 39, T1 at level 59, T2 at level 59).

Class CapabilityBound (C : typ_refcap_label) :=
  obj_cap_bnd :
     ctx -> objctx -> renv -> typ -> typ -> Prop.

Notation "G '§§' Go '⁏' e  ⊢ T1 '∶cpb' ⟦ C ⟧  T2" := (@obj_cap_bnd C _ G Go e T1 T2)
  (at level 40, Go at level 39, e at level 39, T1 at level 59, T2 at level 59).

Notation cap_bnd C G e T1 T2 := (@obj_cap_bnd C _ G objctx_empty e T1 T2).

Notation "G '⁏' e ⊢ T1 '∶cpb' ⟦ C ⟧ T2" := (cap_bnd C G e T1 T2)
    (at level 40, e at level 39, T1 at level 59, T2 at level 59).

Notation typ_cap_adapt C x Tcap := (
  typ_cap_marker C (typ_or Tcap
    (typ_sel (avar_f x) (typ_label_refcap C) (avar_b 0))
  )).

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive ty_var : Typing var :=

| ty_var_var : forall G e x T,
    ctx_binds x T G ->
    G⁏e ⊢ x ∶ T

| ty_rec_intro : forall G e x T,
    G⁏e ⊢ x ∶ open x T ->
    typ_indep_b 0 T ->

    ((mode_has_incap typing_mode) -> (G⁏e ⊢ (open x T) ∶icp (open x T))) ->
    G⁏e ⊢ x ∶ typ_bnd T

| ty_rec_elim : forall G e x T,
    G⁏e ⊢ x ∶ typ_bnd T ->
    typ_indep_b 0 T ->
    G⁏e ⊢ x ∶ open x T

| ty_var_and : forall G e x T U,
    G⁏e ⊢ x ∶ T ->
    G⁏e ⊢ x ∶ U ->
    G⁏e ⊢ x ∶ typ_and T U

| ty_var_sub : forall G e x T U,
    G⁏e ⊢ x ∶ T ->
    G⁏e ⊢ T <: U ->
    G⁏e ⊢ x ∶ U

| ty_var_mut_top : forall G e x T,
    mode_has_mutability typing_mode ->
    G⁏e ⊢ x ∶ T ->
    G⁏e ⊢ x ∶ (typ_mut_marker typ_top)

with subtyp : Subtyping :=

| subtyp_top: forall G e T,
    G⁏e ⊢ T <: typ_top

| subtyp_bot: forall G e T,
    G⁏e ⊢ typ_bot <: T

| subtyp_refl: forall G e T,
    G⁏e ⊢ T <: T

| subtyp_trans: forall G e S T U,
    G⁏e ⊢ S <: T ->
    G⁏e ⊢ T <: U ->
    G⁏e ⊢ S <: U

| subtyp_and11: forall G e T U,
    G⁏e ⊢ typ_and T U <: T

| subtyp_and12: forall G e T U,
    G⁏e ⊢ typ_and T U <: U

| subtyp_and2: forall G e S T U,
    G⁏e ⊢ S <: T ->
    G⁏e ⊢ S <: U ->
    G⁏e ⊢ S <: typ_and T U

| subtyp_or11: forall G e T U,
    G⁏e ⊢ T <: typ_or T U

| subtyp_or12: forall G e T U,
    G⁏e ⊢ U <: typ_or T U

| subtyp_or2: forall G e S T U,
    G⁏e ⊢ S <: T ->
    G⁏e ⊢ U <: T ->
    G⁏e ⊢ typ_or S U <: T

| subtyp_fld: forall G e a T1 T2 U1 U2,
    G⁏e ⊢ T1 <: T2 ->
    G⁏e ⊢ U1 <: U2 ->
    G⁏e ⊢ typ_rcd (dec_fld a T2 U1) <: typ_rcd (dec_fld a T1 U2)

| subtyp_typ: forall G e A S1 T1 S2 T2,
    (forall x, G⁏e ⊢ (open x S2) <: (open x S1)) ->
    (forall x, G⁏e ⊢ (open x T1) <: (open x T2)) ->
    G⁏e ⊢ typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

| subtyp_sel2: forall G e x A y S T,
    G⁏e ⊢ x ∶ typ_rcd (dec_typ A S T) ->
    G⁏e ⊢ (open y S) <: typ_sel (avar_f x) A (avar_f y)

| subtyp_sel1: forall G e x A y S T,
    G⁏e ⊢ x ∶ typ_rcd (dec_typ A S T) ->
    G⁏e ⊢ typ_sel (avar_f x) A (avar_f y) <: (open y T)

| subtyp_fun: forall L G e S1 T1 S2 T2,
    mode_has_fun typing_mode ->
    G⁏e ⊢ S2 <: S1 ->
    (forall x, x \notin L ->
       G § x / v_par ~ S2 ⁏e ⊢ open x T1 <: open x T2) ->
    G⁏e ⊢ typ_fun S1 T1 <: typ_fun S2 T2

| subtyp_met: forall L G e m TC1 TZ1 TR1 TC2 TZ2 TR2,
    G⁏e ⊢ TZ2 <: TZ1 ->
    (forall x, x \notin L ->
    G § x / v_par ~ TZ2 ⁏e ⊢ open x TC2 <: open x TC1) ->

    (mode_has_sef typing_mode -> typ_indep_b 0 TC2 -> typ_indep_b 0 TC1) ->
    (forall x, x \notin L ->
     forall y, y <> x -> y \notin L ->
    (ctx_met G x TZ2 y TC2) ⁏e ⊢ open_met x y TR1 <: open_met x y TR2) ->
    G⁏e ⊢ typ_rcd (dec_met m TC1 TZ1 TR1) <: typ_rcd (dec_met m TC2 TZ2 TR2)

| subtyp_tyq: forall G e T1 T2,
    e ⊢ T1 ≈ T2 ->
    G⁏e ⊢ T1 <: T2

| subtyp_typ_and: forall G e A S1 T1 S2 T2,
    G⁏e ⊢
     typ_and
       (typ_rcd (dec_typ A S1 T1))
       (typ_rcd (dec_typ A S2 T2))
     <: typ_rcd (dec_typ A (typ_or S1 S2) (typ_and T1 T2))

| subtyp_dist: forall G e T1 T2 T3,
    G⁏e ⊢
      typ_and T1 (typ_or T2 T3)
      <: typ_or (typ_and T1 T2) (typ_and T1 T3)

| subtyp_nocap_bnd G e T:
    G⁏e ⊢ typ_nocap <: typ_bnd T

| subtyp_nocap_typ G e A T1 T2:
    G⁏e ⊢ typ_nocap <: typ_rcd (dec_typ (typ_label_normal A) T1 T2)

| subtyp_nocap_fld G e a T1 T2:
    G⁏e ⊢ typ_nocap <: typ_rcd (dec_fld a T1 T2)

| subtyp_nocap_met G e a TC TZ TR:
    G⁏e ⊢ typ_nocap <: typ_rcd (dec_met a TC TZ TR)

| subtyp_nocap_fun G e TZ TR:
    mode_has_fun typing_mode ->
    G⁏e ⊢ typ_nocap <: typ_fun TZ TR

| subtyp_nocap_mut_top_boundless G e T1 T2:
    mode_has_top_nm_subtype_boundless typing_mode ->
    G⁏e ⊢ typ_top <: (typ_or typ_nocap (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability) T1 T2)))

| subtyp_nocap_mut_top_complement G e:
    mode_has_top_nm_complement typing_mode ->
    G⁏e ⊢ typ_top <: (typ_or typ_nocap (typ_mut_marker typ_bot) )

| subtyp_nocap_mut_bot G e:
    mode_has_top_nm_complement typing_mode ->
    G⁏e ⊢ (typ_and typ_nocap (typ_mut_marker typ_bot)) <: typ_bot

| subtyp_mut_top G e:
    mode_has_mut_top typing_mode ->
    G⁏e ⊢ typ_top <: (typ_mut_marker typ_top)

with ty_incap : ReferenceIncapacitate :=

| ty_incap_top G e:
    G⁏e ⊢ typ_top ∶icp typ_top

| ty_incap_bot G e:
    G⁏e ⊢ typ_bot ∶icp typ_nocap

| ty_incap_typ G e A S T:
    G⁏e ⊢ typ_rcd (dec_typ (typ_label_normal A) S T)
     ∶icp typ_rcd (dec_typ (typ_label_normal A) S T)

| ty_incap_cap G e M S T:
    G⁏e ⊢ typ_rcd (dec_typ (typ_label_refcap M) S T)
     ∶icp typ_top

| ty_incap_met G e m TC TZ TR:
    G⁏e ⊢ typ_rcd (dec_met m TC TZ TR) ∶icp typ_rcd (dec_met m TC TZ TR)

| ty_incap_fld G e a T1 T2:
    G⁏e ⊢ typ_rcd (dec_fld a T1 T2) ∶icp typ_rcd (dec_fld a T1 T2)

| ty_incap_sel G e x B y S T T':
    G⁏e ⊢ x ∶ typ_rcd (dec_typ B S T) ->
    G⁏e ⊢ (open y T) ∶icp T' ->
    G⁏e ⊢ typ_sel (avar_f x) B (avar_f y) ∶icp T'

| ty_incap_rec G e T:
    G⁏e ⊢ typ_bnd T ∶icp typ_bnd T

| ty_incap_and G e S1 T1 S2 T2:
    G⁏e ⊢ S1 ∶icp S2 ->
    G⁏e ⊢ T1 ∶icp T2 ->
    G⁏e ⊢ typ_and S1 T1 ∶icp typ_and S2 T2

| ty_incap_or G e S1 T1 S2 T2:
    G⁏e ⊢ S1 ∶icp S2 ->
    G⁏e ⊢ T1 ∶icp T2 ->
    G⁏e ⊢ typ_or S1 T1 ∶icp typ_or S2 T2

| ty_incap_fun G e S T:
    mode_has_fun typing_mode ->
    G⁏e ⊢ typ_fun S T ∶icp typ_fun S T

| ty_incap_nocap G e T:
    mode_incap' typing_mode = mode_incap_nocap ->
    G⁏e ⊢ typ_nocap <: T ->
    G⁏e ⊢ T ∶icp T
.

Global Existing Instance ty_var.

Global Existing Instance subtyp.

Global Existing Instance ty_incap.

Inductive ty_capbnd (C : typ_refcap_label) : CapabilityBound C :=
| ty_capbnd_top G e:
    G⁏e ⊢ typ_top ∶cpb⟦C⟧ typ_top

| ty_capbnd_bot G e:
    G⁏e ⊢ typ_bot ∶cpb⟦C⟧ typ_bot

| ty_capbnd_typ G e A S T:
    G⁏e ⊢ typ_rcd (dec_typ (typ_label_normal A) S T) ∶cpb⟦C⟧ typ_top

| ty_capbnd_cap_sel G e S T:

    G⁏e ⊢ typ_rcd (dec_typ (typ_label_refcap C) S T) ∶cpb⟦C⟧ T

| ty_capbnd_cap_ignore G e C' S T:
    C' <> C ->
    G⁏e ⊢ typ_rcd (dec_typ (typ_label_refcap C') S T) ∶cpb⟦C⟧ typ_top

| ty_capbnd_met G e m TC TZ TR:
    G⁏e ⊢ typ_rcd (dec_met m TC TZ TR) ∶cpb⟦C⟧ typ_top

| ty_capbnd_fld G e a T1 T2:
    G⁏e ⊢ typ_rcd (dec_fld a T1 T2) ∶cpb⟦C⟧ typ_top

| ty_capbnd_sel G e x B y S T T':
    G⁏e ⊢ x ∶ typ_rcd (dec_typ B S T) ->
    G⁏e ⊢ (open y T) ∶cpb⟦C⟧ T' ->
    G⁏e ⊢ typ_sel (avar_f x) B (avar_f y) ∶cpb⟦C⟧ T'

| ty_capbnd_rec G e T:
    G⁏e ⊢ typ_bnd T ∶cpb⟦C⟧ typ_top

| ty_capbnd_and G e S1 T1 S2 T2:
    G⁏e ⊢ S1 ∶cpb⟦C⟧ S2 ->
    G⁏e ⊢ T1 ∶cpb⟦C⟧ T2 ->
    G⁏e ⊢ typ_and S1 T1 ∶cpb⟦C⟧ typ_and S2 T2

| ty_capbnd_or G e S1 T1 S2 T2:
    G⁏e ⊢ S1 ∶cpb⟦C⟧ S2 ->
    G⁏e ⊢ T1 ∶cpb⟦C⟧ T2 ->
    G⁏e ⊢ typ_or S1 T1 ∶cpb⟦C⟧ typ_or S2 T2

| ty_capbnd_all G e S T:
    G⁏e ⊢ typ_fun S T ∶cpb⟦C⟧ typ_top

.

Global Existing Instance ty_capbnd.

Inductive viewpoint_adapt_cap: typ_refcap_label -> var -> (TypingProperty typ typ) :=
| viewpoint_adapt_cap_strip_combine C x G Go e T Tstrip Tcap:
    G§§Go⁏e ⊢ T ∶icp Tstrip ->
    G§§Go⁏e ⊢ T ∶cpb⟦C⟧ Tcap ->
    viewpoint_adapt_cap C x G Go e T (typ_and Tstrip (typ_cap_adapt C x Tcap)).

Definition viewpoint_adapt x G Go e Tf Tr :=
  match (mode_viewpoint_adaptation' typing_mode) with

  | mode_viewpoint_adaptation_same => Tf = Tr

  | mode_viewpoint_adapt_mutability => viewpoint_adapt_cap typ_refcap_mutability x G Go e Tf Tr
  end.

End WithTypingMode.

Notation "G ⁏ e ⊢ x ▷⟦ C ⟧ T1 ⟶ T2" :=
  (viewpoint_adapt_cap _ C x G objctx_empty e T1 T2)
    (at level 40, e at level 39, x at level 59, T1 at level 59, T2 at level 59).

Notation "G ⁏ e ⊢ x ▷ T1 ⟶ T2" :=
  (viewpoint_adapt _ x G objctx_empty e T1 T2)
    (at level 40, e at level 39, x at level 59, T1 at level 59, T2 at level 59).

Notation typ_objlit typing_mode T := (
  match (mode_objlit_refcaps' typing_mode) with

  | mode_objlit_refcaps_none => typ_and (typ_bnd T) typ_top

  | mode_objlit_refcaps_mutable => typ_and (typ_bnd T) (typ_mut_marker typ_bot)
  end) (only parsing).

Notation vis_var typing_mode G x := (
  (mode_has_visibility typing_mode) -> (ctx_vis G x)
  ) (only parsing).

Notation mut_var_writeable typing_mode G e x := (
  (mode_has_mutability typing_mode) -> (G⁏e ⊢ x ∶ (typ_mut_marker typ_bot) )
  ) (only parsing).

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive ty_trm : Typing trm :=

| ty_trm_var : forall G e x T,
    vis_var typing_mode G x ->
    G⁏e ⊢ x ∶ T ->
    G⁏e ⊢ trm_var (avar_f x) ∶ T

| ty_trm_apply : forall G e x z S T,
    mode_has_fun typing_mode ->
    vis_var typing_mode G x ->
    vis_var typing_mode G z ->
    G⁏e ⊢ x ∶ typ_fun S T ->
    G⁏e ⊢ z ∶ S ->
    G⁏e ⊢ trm_apply (avar_f x) (avar_f z) ∶ open z T

| ty_trm_read : forall G e x a S T U,
    vis_var typing_mode G x ->
    G⁏e ⊢ x ∶ typ_rcd (dec_fld a S T) ->
    G⁏e ⊢ x ▷ T ⟶ U ->
    G⁏e ⊢ trm_read (avar_f x) a ∶ U

| ty_trm_write : forall G e x y a S T,
    vis_var typing_mode G x ->
    vis_var typing_mode G y ->
    mut_var_writeable typing_mode G e x ->
    G⁏e ⊢ x ∶ typ_rcd (dec_fld a S T) ->
    G⁏e ⊢ y ∶ S ->
    G⁏e ⊢ trm_write (avar_f x) a (avar_f y) ∶ T

| ty_trm_call : forall G e x y m TC TZ TR,
    vis_var typing_mode G x ->
    vis_var typing_mode G y ->
    G⁏e ⊢ x ∶ typ_rcd (dec_met m TC TZ TR) ->
    G⁏e ⊢ y ∶ TZ ->
    (mode_has_sef typing_mode -> typ_indep_b 0 TC) ->
    G⁏e ⊢ x ∶ (open y TC) ->
    G⁏e ⊢ trm_call (avar_f x) m (avar_f y) ∶ open_met y x TR

| ty_trm_let : forall L G e t u T U,
    G⁏e ⊢ t ∶ T ->
    (forall x, x \notin L ->
      G § x / v_let ~ T ⁏e ⊢ open x u ∶ U) ->
    G⁏e ⊢ trm_let t u ∶ U

| ty_trm_lit : forall L G e l u T U,
    G⁏e ⊢ l ∶ T ->
    (forall x, x \notin L ->
      G § x / v_let ~ T ⁏e ⊢ open x u ∶ U) ->
    G⁏e ⊢ trm_lit l u ∶ U

| ty_trm_sub : forall G e (t : trm) T U,
    G⁏e ⊢ t ∶ T ->
    G⁏e ⊢ T <: U ->
    G⁏e ⊢ t ∶ U

with ty_lit : Typing lit :=

| ty_lit_fun : forall L G e T t U,
    mode_has_fun typing_mode ->
    (forall x, x \notin L ->
      G § x / v_par ~ T ⁏e ⊢ open x t ∶ open x U) ->
    G⁏e ⊢ lit_fun T t ∶ typ_fun T U

| ty_lit_obj : forall L G e T ds,
    (forall x, x \notin L -> G §§ (objctx_lit x T) ⁏e ⊢ (open x ds) ∶ (open x T)) ->
    typ_indep_b 0 T ->
    G⁏e ⊢ lit_obj T ds ∶ typ_objlit typing_mode T

with ty_def : DecTyping def :=

| ty_def_typ : forall L G Go e A T U,
    (forall x, x \notin L -> e ⊢ (open x T) ≈ (open x U)) ->
    G §§ Go⁏e ⊢ def_typ (typ_label_normal A) T ∶d dec_typ (typ_label_normal A) U U

| ty_def_fld : forall G Go e a t T,
    vis_var typing_mode (G §§& Go) t ->
    G §§& Go⁏e ⊢ t ∶ T ->
    G §§ Go⁏e ⊢ def_fld a (avar_f t) ∶d dec_fld a T T

| ty_def_met : forall L G Go e m t TC TZ TR,
    (forall xz, xz \notin L ->
    forall xc, xc <> xz -> xc \notin L ->
    ctx_obj_met typing_mode G Go xz TZ xc TC ⁏e ⊢ open_met xz xc t ∶ open_met xz xc TR) ->
    G §§ Go⁏e ⊢ def_met m t ∶d dec_met m TC TZ TR

with ty_defs: Typing defs :=

| ty_defs_one : forall G Go e d D,
    G §§ Go⁏e ⊢ d ∶d D ->
    G §§ Go⁏e ⊢ defs_cons defs_nil d ∶ typ_rcd D

| ty_defs_cons : forall G Go e ds d T D,
    G §§ Go⁏e ⊢ ds ∶ T ->
    G §§ Go⁏e ⊢ d ∶d D ->
    defs_hasnt ds (label_of d) ->
    G §§ Go⁏e ⊢ defs_cons ds d ∶ typ_and T (typ_rcd D)
.

Global Existing Instance ty_trm | 0.

Global Existing Instance ty_def | 0.

Global Existing Instance ty_lit | 1.

Global Existing Instance ty_defs | 1.

Scheme ts_ty_var_mut := Induction for ty_var Sort Prop
with   ts_subtyp     := Induction for subtyp Sort Prop
with   ts_ty_incap   := Induction for ty_incap Sort Prop.

Combined Scheme ts_mutind from ts_ty_var_mut, ts_subtyp, ts_ty_incap.

Scheme rules_trm_mut    := Induction for ty_trm Sort Prop
with   rules_lit_mut    := Induction for ty_lit Sort Prop
with   rules_def_mut    := Induction for ty_def Sort Prop
with   rules_defs_mut   := Induction for ty_defs Sort Prop.

Combined Scheme rules_mutind from rules_trm_mut, rules_lit_mut,
rules_def_mut, rules_defs_mut.

End WithTypingMode.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.

Notation SubtypingPropery := (ctx -> renv -> typ -> typ -> Prop) (only parsing).

Module GeneralizedSubtyping.

Class AndOrSubtyping (ST: SubtypingPropery) := {
  and11 G e T U: ST G e (typ_and T U) T;
  and12 G e T U: ST G e (typ_and T U) U;
  and2 G e S T U:
    ST G e S T ->
    ST G e S U ->
    ST G e S (typ_and T U);
  or11 G e T U: ST G e T (typ_or T U);
  or12 G e T U: ST G e U (typ_or T U);
  or2 G e S T U:
    ST G e S T ->
    ST G e U T ->
    ST G e (typ_or S U) T;
  trans G e S T U:
    ST G e S T ->
    ST G e T U ->
    ST G e S U;
}.

End GeneralizedSubtyping.

Section GeneralizedSubtypingLemmata.

Context {ST} {AOS: GeneralizedSubtyping.AndOrSubtyping ST}.

End GeneralizedSubtypingLemmata.

Section WithTypingMode.

Context (typing_mode: Mode).

Global Instance and_or_subtyp: GeneralizedSubtyping.AndOrSubtyping (fun G => (subtyping)  G objctx_empty) := {
  and11 := subtyp_and11 typing_mode;
  and12 := subtyp_and12 typing_mode;
  and2 := @subtyp_and2 typing_mode;
  or11 := subtyp_or11 typing_mode;
  or12 := subtyp_or12 typing_mode;
  or2 := @subtyp_or2 typing_mode;
  trans := @subtyp_trans typing_mode;
}.

End WithTypingMode.
