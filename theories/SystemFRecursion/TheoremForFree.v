From Stdlib Require Import Lists.List.
From AutoProof.SystemFRecursion Require Import Syntax Infrastructure RelationalEvaluation.
From AutoProof.SystemFRecursion Require Import BinaryLogicalRelation.
Import ListNotations.

Module SystemFTheoremForFree.
Import SystemF SystemFInfrastructure SystemFRelationalEvaluation.
Import SystemFBinaryLogicalRelation.

Definition empty_binary_env : binary_env := fun _ => None.

Definition singleton_relation (v : tm) : binary_relation :=
  fun v1 v2 => v1 = v /\ v2 = v.

Definition singleton_candidate (v : tm) (Hv : value v) : binary_candidate.
Proof.
  refine {| candidate_relation := singleton_relation v |}.
  intros v1 v2 [-> ->]. split; exact Hv.
Defined.

Lemma closed_parametricity : forall t T,
  has_type [] empty t T ->
  expression_relation [] empty_binary_env T t t.
Proof.
  intros t T Htyped.
  pose proof (binary_fundamental [] empty t T Htyped
    identity_type_substitution identity_type_substitution
    empty_binary_env identity_term_substitution identity_term_substitution
    identity_type_substitution_closed identity_type_substitution_closed
    identity_term_substitution_closed identity_term_substitution_closed) as Hrel.
  assert (Hempty : related_substitutions empty_binary_env empty
      identity_term_substitution identity_term_substitution).
  { intros x U Hlookup. unfold empty in Hlookup. simpl in Hlookup. discriminate. }
  specialize (Hrel Hempty).
  repeat rewrite instantiate_identity in Hrel.
  exact Hrel.
Qed.

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t Htyped U v HU Hv _.
  assert (HUlc : locally_closed_ty U).
  { eapply wf_ty_lc; eauto. }
  pose (a := singleton_candidate v Hv).
  pose proof (closed_parametricity _ _ Htyped) as Hparam.
  pose proof (expression_tapp [] empty_binary_env
    (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)) t t U U a
    Hparam HUlc HUlc) as Htapp.
  assert (Hvrel : value_relation [a] empty_binary_env
      (Ty_BVar 0) v v).
  { cbn [value_relation a singleton_candidate singleton_relation]. split; reflexivity. }
  pose proof (value_is_expression _ _ _ _ _ Hvrel) as Harg.
  pose proof (expression_app [a] empty_binary_env
    (Ty_BVar 0) (Ty_BVar 0)
    (tm_tapp t U) (tm_tapp t U) v v Htapp Harg) as Happ.
  destruct Happ as [_ [_ [v1 [v2 [E1 [E2 HR]]]]]].
  cbn [value_relation singleton_relation] in HR.
  destruct HR as [-> _].
  apply evaluates_smallstep. exact E1.
Qed.

Print Assumptions polymorphic_identity_theorem_for_free.
End SystemFTheoremForFree.

