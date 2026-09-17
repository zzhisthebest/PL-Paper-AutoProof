From Stdlib Require Import List Arith Lia.
From AutoProof.SystemFNonDeterminism Require Import Syntax Infrastructure LogicalRelation Norm.
Import ListNotations.
Module SystemFExamples.
Import SystemF SystemFInfrastructure SystemFLogicalRelation SystemFNorm.

Definition identity_type : ty := Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)).
Definition poly_id : tm := tm_tabs (tm_abs (Ty_BVar 0) (tm_bvar 0)).

Lemma poly_id_typed : forall Delta Gamma,
  has_type Delta Gamma poly_id identity_type.
Proof.
  intros Delta Gamma. unfold poly_id, identity_type.
  apply T_TAbs with (L := []). intros X HX. cbn [open_tm_ty open_tm_ty_rec open_ty open_ty_rec].
  apply T_Abs with (L := []).
  - apply WF_Var. simpl. auto.
  - intros x Hx. cbn [open_tm open_tm_rec].
    apply T_Var.
    + cbn [lookup_context update]. rewrite Nat.eqb_refl. reflexivity.
    + apply WF_Var. simpl. auto.
Qed.

Lemma identity_type_wf : forall Delta, wf_ty Delta identity_type.
Proof.
  intro Delta. unfold identity_type. apply WF_All with (L := []).
  intros X HX. cbn [open_ty open_ty_rec]. apply WF_Arrow; apply WF_Var; simpl; auto.
Qed.

Lemma poly_id_value : value poly_id.
Proof.
  apply v_tabs. unfold locally_closed_tm. repeat constructor; lia.
Qed.

Definition poly_id_twice : tm :=
  tm_tabs (tm_abs (Ty_BVar 0)
    (tm_app (tm_abs (Ty_BVar 0) (tm_bvar 0)) (tm_bvar 0))).
Definition choice_example : tm := tm_choice poly_id poly_id_twice.

Lemma poly_id_twice_typed : has_type [] empty poly_id_twice identity_type.
Proof.
  unfold poly_id_twice, identity_type.
  apply T_TAbs with (L := []). intros X HX. cbn [open_tm_ty open_tm_ty_rec open_ty open_ty_rec].
  apply T_Abs with (L := []); [apply WF_Var; simpl; auto |].
  intros x Hx. cbn [open_tm open_tm_rec].
  eapply T_App with (T1 := Ty_FVar X).
  - apply T_Abs with (L := []); [apply WF_Var; simpl; auto |].
    intros y Hy. cbn [open_tm open_tm_rec].
    apply T_Var.
    + cbn [lookup_context update]. rewrite Nat.eqb_refl. reflexivity.
    + apply WF_Var. simpl. auto.
  - apply T_Var.
    + cbn [lookup_context update]. rewrite Nat.eqb_refl. reflexivity.
    + apply WF_Var. simpl. auto.
Qed.

Example choice_example_typed : has_type [] empty choice_example identity_type.
Proof. apply T_Choice; [apply poly_id_typed | apply poly_id_twice_typed]. Qed.

Example choice_example_normalizes : strongly_normalizing choice_example.
Proof. apply (normalization choice_example identity_type). exact choice_example_typed. Qed.

Example choice_has_distinct_reducts :
  choice_example --> poly_id /\
  choice_example --> poly_id_twice /\ poly_id <> poly_id_twice.
Proof.
  assert (H1 : locally_closed_tm poly_id) by (apply value_regular; apply poly_id_value).
  assert (H2 : locally_closed_tm poly_id_twice).
  { unfold locally_closed_tm, poly_id_twice. repeat constructor; lia. }
  split; [apply ST_ChoiceLeft; assumption |].
  split; [apply ST_ChoiceRight; assumption | discriminate].
Qed.

End SystemFExamples.
