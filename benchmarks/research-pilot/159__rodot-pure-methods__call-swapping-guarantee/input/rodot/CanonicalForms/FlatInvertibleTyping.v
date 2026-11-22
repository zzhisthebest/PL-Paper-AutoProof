Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening Orctx Logctx.

Require Import Incap.

Require Import Coq.Bool.Bool LibBoolExtra.

Section WithTypingMode.

Context {typing_mode: Mode}.

Reserved Notation "G '⁏' e '⊢##f' x '∶' T" (at level 40, e at level 39, x at level 59).

Inductive ty_var_inv : ctx -> renv -> var -> typ -> Prop :=




| ty_precise_inv : forall G e x T U V,
  G ⊢! x ∶ T ⪼ U ->
  typing_equiv e U V ->
  G⁏e ⊢##f x ∶ V






| ty_dec_fld_inv : forall G e x a TL1 TL2 TU1 TU2,
  G⁏e ⊢##f x ∶ typ_rcd (dec_fld a TL1 TU1) ->
  G⁏e ⊢# TL2 <: TL1 ->
  G⁏e ⊢# TU1 <: TU2 ->
  G⁏e ⊢##f x ∶ typ_rcd (dec_fld a TL2 TU2)






| ty_dec_typ_inv : forall G e x A TL1 TL2 TU1 TU2,
  G⁏e ⊢##f x ∶ typ_rcd (dec_typ A TL1 TU1) ->
  (forall y, G⁏e ⊢# open y TL2 <: open y TL1) ->
  (forall y, G⁏e ⊢# open y TU1 <: open y TU2) ->
  G⁏e ⊢##f x ∶ typ_rcd (dec_typ A TL2 TU2)





| ty_bnd_inv : forall G e x T,
  typ_indep_b 0 T ->
  ((mode_has_incap typing_mode) -> (G⁏e ⊢ (open x T) ∶icp (open x T))) ->
  G⁏e ⊢##f x ∶ open x T ->
  G⁏e ⊢##f x ∶ typ_bnd T







| ty_fun_inv : forall L G e x S T S' T',
  mode_has_fun typing_mode ->
  G⁏e ⊢##f x ∶ typ_fun S T ->
  G⁏e ⊢# S' <: S ->
  (forall y, y \notin L ->
   G § y / v_par ~ S' ⁏e ⊢ open y T <: open y T') ->
  G⁏e ⊢##f x ∶ typ_fun S' T'





| ty_and_inv : forall G e x S1 S2,
  G⁏e ⊢##f x ∶ S1 ->
  G⁏e ⊢##f x ∶ S2 ->
  G⁏e ⊢##f x ∶ typ_and S1 S2




| ty_or1_inv : forall G e x S1 S2,
  G⁏e ⊢##f x ∶ S1 ->
  G⁏e ⊢##f x ∶ typ_or S1 S2




| ty_or2_inv : forall G e x S1 S2,
  G⁏e ⊢##f x ∶ S2 ->
  G⁏e ⊢##f x ∶ typ_or S1 S2






| ty_sel_inv : forall G e x y A z S1 S2 U,
  G⁏e ⊢##f x ∶ open z S1 ->
  G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S1 S2) ->
  G⁏e ⊢##f x ∶ typ_sel (avar_f y) A (avar_f z)




| ty_top_inv : forall G e x T,
  G⁏e ⊢##f x ∶ T ->
  G⁏e ⊢##f x ∶ typ_top

| ty_dec_met_inv : forall L G e x m TC1 TZ1 TR1 TC2 TZ2 TR2,
  G⁏e ⊢##f x ∶ typ_rcd (dec_met m TC1 TZ1 TR1)  ->
  G⁏e ⊢# TZ2 <: TZ1 ->
  (forall y, y \notin L ->
   G § y / v_par ~ TZ2 ⁏e ⊢ open y TC2 <: open y TC1) ->

  (mode_has_sef typing_mode -> typ_indep_b 0 TC2 -> typ_indep_b 0 TC1) ->
  (forall y, y \notin L ->
   forall z, z <> y -> z \notin L ->
   G § y / v_par ~ TZ2 § z / v_recv ~ (open y TC2) ⁏e ⊢ open y (open_rec 1 z TR1) <: open y (open_rec 1 z TR2) ) ->
  G⁏e ⊢##f x ∶ typ_rcd (dec_met m TC2 TZ2 TR2)

where "G '⁏' e '⊢##f' x '∶' T" := (ty_var_inv G e x T).

End WithTypingMode.

Notation "G '⁏' e '⊢##f' x '∶' T" := (ty_var_inv G e x T) (at level 40, e at level 39, x at level 59).
