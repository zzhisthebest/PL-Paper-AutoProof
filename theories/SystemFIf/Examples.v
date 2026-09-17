From Stdlib Require Import List Arith Lia.
From AutoProof.SystemFIf Require Import Syntax Infrastructure LogicalRelation Norm.
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

Definition if_example : tm :=
  tm_app (tm_tapp poly_id Ty_Bool) (tm_if tm_true tm_false tm_true).

Example if_example_typed : has_type [] empty if_example Ty_Bool.
Proof.
  unfold if_example. eapply T_App with (T1 := Ty_Bool).
  - change (has_type [] empty (tm_tapp poly_id Ty_Bool)
      (open_ty (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)) Ty_Bool)).
    apply T_TApp; [apply poly_id_typed | apply WF_Bool].
  - apply T_If; constructor.
Qed.

Example if_example_normalizes : strongly_normalizing if_example.
Proof. apply (normalization if_example Ty_Bool). exact if_example_typed. Qed.

Example if_selects_false : tm_if tm_true tm_false tm_true --> tm_false.
Proof. apply ST_IfTrue; constructor. Qed.

End SystemFExamples.
