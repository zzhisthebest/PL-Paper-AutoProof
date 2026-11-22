Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax TypingMode GeneralTyping.

Require Import RecordTypes InertContext TFree.

Class MutableReachability := mutable_reachability: ctx -> config -> var -> Prop.

Notation "F ⊢ C 'mreach' y" := (mutable_reachability F C y) (at level 40, C at level 59).

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive mut_reach : MutableReachability :=





| mreach_fld : forall (F : ctx) (t : trm) (fs : stack) (e : renv) (Sigma : heap) Lv
                 (y1 y2 : var) (ds : defs) (a : fld_label),

    inert F ->

    F ⊢ (t; fs; Sigma; e; Lv) mreach y1 ->

    binds y1 (item_obj ds) Sigma -> defs_has ds (def_fld a (avar_f y2)) ->

    F ⁏ e ⊢ trm_var (avar_f y1) ∶ typ_rcd (dec_fld a typ_bot
        (typ_mut_marker typ_bot)) ->

    F ⊢ (t; fs; Sigma; e; Lv) mreach y2






| mreach_trm : forall (F : ctx) (t : trm) (fs : stack) (e : renv) (Sigma : heap) Lv
                 (y w : var),

    inert F ->

    (tfree w t) \/ (tfree w fs) ->

    binds w y e ->

    F ⁏ e ⊢ trm_var (avar_f w) ∶ (typ_mut_marker typ_bot) ->

    F ⊢ (t; fs; Sigma; e; Lv) mreach y
.

End WithTypingMode.

#[export] Existing Instance mut_reach.
