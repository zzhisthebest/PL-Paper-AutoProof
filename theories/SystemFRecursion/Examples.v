From Stdlib Require Import List Arith Lia.
From AutoProof.SystemFRecursion Require Import Syntax Infrastructure LogicalRelation Norm.
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

Lemma numeral_typed : forall Delta Gamma n, has_type Delta Gamma (numeral n) Ty_Nat.
Proof. intros Delta Gamma n. induction n; simpl; [apply T_Zero | apply T_Succ; assumption]. Qed.

Definition keep_result : tm :=
  tm_abs Ty_Nat (tm_abs identity_type (tm_bvar 0)).
Definition recursion_example : tm := tm_natrec (numeral 2) poly_id keep_result.

Lemma keep_result_typed :
  has_type [] empty keep_result (Ty_Arrow Ty_Nat (Ty_Arrow identity_type identity_type)).
Proof.
  unfold keep_result. apply T_Abs with (L := []); [apply WF_Nat |].
  intros n Hn. cbn [open_tm open_tm_rec].
  apply T_Abs with (L := []); [apply identity_type_wf |].
  intros x Hx. cbn [open_tm open_tm_rec].
  apply T_Var.
  - cbn [lookup_context update]. rewrite Nat.eqb_refl. reflexivity.
  - apply identity_type_wf.
Qed.

Example recursion_example_typed : has_type [] empty recursion_example identity_type.
Proof.
  apply T_Rec; [apply numeral_typed | apply poly_id_typed | apply keep_result_typed].
Qed.

Example recursion_example_normalizes : strongly_normalizing recursion_example.
Proof. apply (normalization recursion_example identity_type). exact recursion_example_typed. Qed.

Example recursion_unfolds :
  recursion_example -->
  tm_app (tm_app keep_result (numeral 1))
    (tm_natrec (numeral 1) poly_id keep_result).
Proof.
  apply ST_RecSucc.
  - repeat constructor.
  - apply poly_id_value.
  - apply v_abs. unfold locally_closed_tm, identity_type.
    repeat constructor; lia.
Qed.

End SystemFExamples.
