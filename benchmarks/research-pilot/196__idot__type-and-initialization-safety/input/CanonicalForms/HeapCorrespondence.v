Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax Typing PreTyping.

Require Import GeneralTyping RecordTypes InertTypes DefRecordInertTyping PreciseTyping.

Require Import SubstitutionClass Substitution Weakening Narrowing BndIntro.

Inductive ty_heap_def : DecTyping heap_def :=

| ty_heap_def_typ : forall Gamma A T,
    Gamma ⊢ heap_def_typ A T ∶d dec_typ A T T

| ty_heap_def_trm_none : forall Gamma a T,
    Gamma ⊢ heap_def_trm a None ∶d dec_trm a T T

| ty_heap_def_trm_some : forall Gamma a x T,
    Gamma ⊢ (trm_var (avar_f x)) ∶ T ->
    Gamma ⊢ heap_def_trm a (Some x) ∶d dec_trm a T T.

Existing Instance ty_heap_def.

Inductive ty_item_s : ctx -> heap -> var -> Prop :=
| ty_item_lit_s : forall Gamma Sigma x l T,
    binds x T Gamma ->
    binds x (item_lit l) Sigma ->
    Gamma ⊢ l ∶ T ->
    ty_item_s Gamma Sigma x
| ty_item_obj_s : forall Gamma Sigma x U hds,
    binds x (typ_bnd U) Gamma ->
    binds x (item_obj U hds) Sigma ->
    Gamma ⊢ hds ∶ open x U ->
    ty_item_s Gamma Sigma x.

Definition heap_correspond (G : ctx) (Sigma : heap) : Prop :=
  (dom G = dom Sigma) /\
  (forall x,
      x \in dom G ->
      ty_item_s G Sigma x).
