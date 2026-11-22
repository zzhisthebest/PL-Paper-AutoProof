Set Implicit Arguments.
From CBPV Require Import ObservationalEquivalence StrongReduction AbstractReductionSystems.

Definition Equiv {n: nat} := equiv (@sstep n).

Set Implicit Arguments.
Require Import CBPV.ObservationalEquivalence CBPV.StrongReduction CBPV.AbstractReductionSystems.
Import CommaNotation.
Typeclasses Transparent Subst_comp Subst_value.

(* ------------------------------------------------------------------ *)
(* Basic helper facts about the lifting operations                     *)
(* ------------------------------------------------------------------ *)

Lemma up_value_value_congr {m n} {sigma tau : fin m -> value n}
  (H : forall (i : fin m), sigma i = tau i) :
  forall (i : fin (S m)), up_value_value sigma i = up_value_value tau i.
Proof.
  intros i. destruct i as [x|].
  - cbn [up_value_value scons funcomp].
    change (ren_value shift (sigma x) = ren_value shift (tau x)).
    apply f_equal, H.
  - reflexivity.
Qed.

Lemma up_value_value_ids {m} :
  forall (i : fin (S m)),
    up_value_value (@ids value VarInstance_value m) i = var_value i.
Proof.
  intros i. destruct i as [x|].
  - cbn [up_value_value scons funcomp]. reflexivity.
  - reflexivity.
Qed.

Lemma up_value_value_ids2 {m} :
  forall (i : fin (S (S m))),
    up_value_value (up_value_value (@ids value VarInstance_value m)) i
    = var_value i.
Proof.
  intros i.
  transitivity (up_value_value (@ids value VarInstance_value (S m)) i).
  - apply up_value_value_congr. intros j. apply up_value_value_ids.
  - apply up_value_value_ids.
Qed.

Lemma up_ren_congr {m n} {xi xi' : fin m -> fin n}
  (H : forall (i : fin m), xi i = xi' i) :
  forall (i : fin (S m)), up_ren xi i = up_ren xi' i.
Proof.
  intros i. destruct i as [x|].
  - cbn [up_ren scons funcomp shift bound].
    change (Some (xi x) = Some (xi' x)).
    apply f_equal, H.
  - reflexivity.
Qed.

Lemma up_ren_comp {m n k} (xi1 : fin m -> fin n) (xi2 : fin n -> fin k) :
  forall (i : fin (S m)),
    up_ren (fun i => xi2 (xi1 i)) i = up_ren xi2 (up_ren xi1 i).
Proof.
  intros i. destruct i as [x|].
  - cbn [up_ren scons funcomp shift bound]. reflexivity.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Congruence for renaming                                            *)
(* ------------------------------------------------------------------ *)

Fixpoint ren_value_congr {m n} (V : value m) {xi xi' : fin m -> fin n}
  (H : forall (i : fin m), xi i = xi' i) {struct V} :
  ren_value xi V = ren_value xi' V
with ren_comp_congr {m n} (c : comp m) {xi xi' : fin m -> fin n}
  (H : forall (i : fin m), xi i = xi' i) {struct c} :
  ren_comp xi c = ren_comp xi' c.
Proof.
  - destruct V; simpl.
    + apply f_equal, H.
    + reflexivity.
    + apply f_equal2; apply ren_value_congr; exact H.
    + apply f_equal2; [ reflexivity | apply ren_value_congr; exact H ].
    + apply f_equal. apply ren_comp_congr. exact H.
  - destruct c; simpl.
    + reflexivity.
    + apply f_equal. apply ren_value_congr. exact H.
    + apply f_equal. apply ren_comp_congr. apply up_ren_congr. exact H.
    + apply f_equal2; [ apply ren_comp_congr; exact H | apply ren_value_congr; exact H ].
    + apply f_equal2; apply ren_comp_congr; exact H.
    + apply f_equal. apply ren_value_congr. exact H.
    + apply f_equal2; [ apply ren_comp_congr; exact H
                       | apply ren_comp_congr; apply up_ren_congr; exact H ].
    + apply f_equal2; [ reflexivity | apply ren_comp_congr; exact H ].
    + apply f_equal. apply ren_value_congr. exact H.
    + apply f_equal3; [ apply ren_value_congr; exact H
                       | apply ren_comp_congr; apply up_ren_congr; exact H
                       | apply ren_comp_congr; apply up_ren_congr; exact H ].
    + apply f_equal2; [ apply ren_value_congr; exact H
                       | apply ren_comp_congr; apply up_ren_congr; apply up_ren_congr; exact H ].
Defined.

(* ------------------------------------------------------------------ *)
(* Composition of renamings                                           *)
(* ------------------------------------------------------------------ *)

Fixpoint ren_value_comp {m n k} (xi1 : fin m -> fin n) (xi2 : fin n -> fin k)
  (V : value m) {struct V} :
  ren_value (fun i => xi2 (xi1 i)) V = ren_value xi2 (ren_value xi1 V)
with ren_comp_comp {m n k} (xi1 : fin m -> fin n) (xi2 : fin n -> fin k)
  (c : comp m) {struct c} :
  ren_comp (fun i => xi2 (xi1 i)) c = ren_comp xi2 (ren_comp xi1 c).
Proof.
  - destruct V; simpl.
    + reflexivity.
    + reflexivity.
    + apply f_equal2; apply ren_value_comp.
    + apply f_equal2; [ reflexivity | apply ren_value_comp ].
    + apply f_equal. apply ren_comp_comp.
  - destruct c; simpl.
    + reflexivity.
    + apply f_equal. apply ren_value_comp.
    + apply f_equal.
      transitivity (ren_comp (fun i => up_ren xi2 (up_ren xi1 i)) c).
      * apply ren_comp_congr. apply up_ren_comp.
      * apply ren_comp_comp.
    + apply f_equal2; [ apply ren_comp_comp | apply ren_value_comp ].
    + apply f_equal2; apply ren_comp_comp.
    + apply f_equal. apply ren_value_comp.
    + apply f_equal2; [ apply ren_comp_comp
                       | transitivity (ren_comp (fun i => up_ren xi2 (up_ren xi1 i)) c2);
                         [ apply ren_comp_congr; apply up_ren_comp
                         | apply ren_comp_comp ] ].
    + apply f_equal2; [ reflexivity | apply ren_comp_comp ].
    + apply f_equal. apply ren_value_comp.
    + apply f_equal3;
        [ apply ren_value_comp
        | transitivity (ren_comp (fun i => up_ren xi2 (up_ren xi1 i)) c1);
          [ apply ren_comp_congr; apply up_ren_comp | apply ren_comp_comp ]
        | transitivity (ren_comp (fun i => up_ren xi2 (up_ren xi1 i)) c2);
          [ apply ren_comp_congr; apply up_ren_comp | apply ren_comp_comp ] ].
    + apply f_equal2;
        [ apply ren_value_comp
        | transitivity (ren_comp (fun i => up_ren (up_ren xi2) (up_ren (up_ren xi1) i)) c);
          [ apply ren_comp_congr; intros i;
            transitivity (up_ren (fun j => up_ren xi2 (up_ren xi1 j)) i);
            [ apply up_ren_congr; apply up_ren_comp | apply up_ren_comp ]
          | apply ren_comp_comp ] ].
Defined.

(* ------------------------------------------------------------------ *)
(* Pointwise congruence for substitution                              *)
(* ------------------------------------------------------------------ *)

Fixpoint subst_value_congr {m n} (V : value m) {sigma tau : fin m -> value n}
  (H : forall (i : fin m), sigma i = tau i) {struct V} :
  subst_value sigma V = subst_value tau V
with subst_comp_congr {m n} (c : comp m) {sigma tau : fin m -> value n}
  (H : forall (i : fin m), sigma i = tau i) {struct c} :
  subst_comp sigma c = subst_comp tau c.
Proof.
  - destruct V; simpl.
    + apply H.
    + reflexivity.
    + apply f_equal2; apply subst_value_congr; exact H.
    + apply f_equal2; [ reflexivity | apply subst_value_congr; exact H ].
    + f_equal. apply subst_comp_congr. exact H.
  - destruct c; simpl.
    + reflexivity.
    + f_equal. apply subst_value_congr. exact H.
    + f_equal. apply subst_comp_congr. apply up_value_value_congr. exact H.
    + apply f_equal2; [ apply subst_comp_congr; exact H | apply subst_value_congr; exact H ].
    + apply f_equal2; apply subst_comp_congr; exact H.
    + f_equal. apply subst_value_congr. exact H.
    + apply f_equal2; [ apply subst_comp_congr; exact H
                  | apply subst_comp_congr; apply up_value_value_congr; exact H ].
    + apply f_equal2; [ reflexivity | apply subst_comp_congr; exact H ].
    + f_equal. apply subst_value_congr. exact H.
    + apply f_equal3; [ apply subst_value_congr; exact H
                  | apply subst_comp_congr; apply up_value_value_congr; exact H
                  | apply subst_comp_congr; apply up_value_value_congr; exact H ].
    + apply f_equal2; [ apply subst_value_congr; exact H
                  | apply subst_comp_congr; apply up_value_value_congr;
                    apply up_value_value_congr; exact H ].
Defined.

(* ------------------------------------------------------------------ *)
(* Identity substitution                                              *)
(* ------------------------------------------------------------------ *)

Fixpoint subst_value_id {m} (V : value m) {struct V} :
  subst_value (@ids value VarInstance_value m) V = V
with subst_comp_id {m} (c : comp m) {struct c} :
  subst_comp (@ids value VarInstance_value m) c = c.
Proof.
  - destruct V; simpl.
    + reflexivity.
    + reflexivity.
    + apply f_equal2; apply subst_value_id.
    + apply f_equal2; [ reflexivity | apply subst_value_id ].
    + apply f_equal. apply subst_comp_id.
  - destruct c; simpl.
    + reflexivity.
    + apply f_equal. apply subst_value_id.
    + apply f_equal.
      transitivity (subst_comp (@ids value VarInstance_value (S m)) c).
      * apply subst_comp_congr. apply up_value_value_ids.
      * apply subst_comp_id.
    + apply f_equal2; [ apply subst_comp_id | apply subst_value_id ].
    + apply f_equal2; apply subst_comp_id.
    + apply f_equal. apply subst_value_id.
    + apply f_equal2;
        [ apply subst_comp_id
        | transitivity (subst_comp (@ids value VarInstance_value (S m)) c2);
          [ apply subst_comp_congr; apply up_value_value_ids
          | apply subst_comp_id ] ].
    + apply f_equal2; [ reflexivity | apply subst_comp_id ].
    + apply f_equal. apply subst_value_id.
    + apply f_equal3;
        [ apply subst_value_id
        | transitivity (subst_comp (@ids value VarInstance_value (S m)) c1);
          [ apply subst_comp_congr; apply up_value_value_ids | apply subst_comp_id ]
        | transitivity (subst_comp (@ids value VarInstance_value (S m)) c2);
          [ apply subst_comp_congr; apply up_value_value_ids | apply subst_comp_id ] ].
    + apply f_equal2;
        [ apply subst_value_id
        | transitivity (subst_comp (@ids value VarInstance_value (S (S m))) c);
          [ apply subst_comp_congr; apply up_value_value_ids2
          | apply subst_comp_id ] ].
Defined.


(* ------------------------------------------------------------------ *)
(* Renaming followed by substitution                                  *)
(* ------------------------------------------------------------------ *)

Lemma up_ren_up_value_value {m n k} (xi : fin m -> fin n) (tau : fin n -> value k) :
  forall (i : fin (S m)),
    up_value_value tau (up_ren xi i) = up_value_value (fun j => tau (xi j)) i.
Proof.
  intros i. destruct i as [x|];
    cbn [up_value_value scons funcomp up_ren shift bound]; reflexivity.
Qed.

Lemma up_ren_up_value_value2 {m n k} (xi : fin m -> fin n) (tau : fin n -> value k) :
  forall (i : fin (S (S m))),
    up_value_value (up_value_value tau) (up_ren (up_ren xi) i)
    = up_value_value (up_value_value (fun j => tau (xi j))) i.
Proof.
  intros i.
  rewrite (up_ren_up_value_value (up_ren xi) (up_value_value tau)).
  apply up_value_value_congr. intros j.
  apply up_ren_up_value_value.
Qed.

Fixpoint ren_value_subst {m n k} (xi : fin m -> fin n) (V : value m)
  (tau : fin n -> value k) {struct V} :
  subst_value tau (ren_value xi V) = subst_value (fun i => tau (xi i)) V
with ren_comp_subst {m n k} (xi : fin m -> fin n) (c : comp m)
  (tau : fin n -> value k) {struct c} :
  subst_comp tau (ren_comp xi c) = subst_comp (fun i => tau (xi i)) c.
Proof.
  - destruct V; simpl.
    + reflexivity.
    + reflexivity.
    + apply f_equal2; apply ren_value_subst.
    + apply f_equal2; [ reflexivity | apply ren_value_subst ].
    + apply f_equal. apply ren_comp_subst.
  - destruct c; simpl.
    + reflexivity.
    + apply f_equal. apply ren_value_subst.
    + apply f_equal.
      rewrite ren_comp_subst.
      apply subst_comp_congr.
      apply up_ren_up_value_value.
    + apply f_equal2; [ apply ren_comp_subst | apply ren_value_subst ].
    + apply f_equal2; apply ren_comp_subst.
    + apply f_equal. apply ren_value_subst.
    + apply f_equal2;
        [ apply ren_comp_subst
        | rewrite ren_comp_subst; apply subst_comp_congr; apply up_ren_up_value_value ].
    + apply f_equal2; [ reflexivity | apply ren_comp_subst ].
    + apply f_equal. apply ren_value_subst.
    + apply f_equal3;
        [ apply ren_value_subst
        | rewrite ren_comp_subst; apply subst_comp_congr; apply up_ren_up_value_value
        | rewrite ren_comp_subst; apply subst_comp_congr; apply up_ren_up_value_value ].
    + apply f_equal2;
        [ apply ren_value_subst
        | rewrite ren_comp_subst; apply subst_comp_congr; apply up_ren_up_value_value2 ].
Defined.

(* ------------------------------------------------------------------ *)
(* Substitution followed by renaming                                  *)
(* ------------------------------------------------------------------ *)

Lemma ren_up_value_value {m n k} (xi : fin n -> fin k) (sigma : fin m -> value n) :
  forall (i : fin (S m)),
    ren_value (up_ren xi) (up_value_value sigma i)
    = up_value_value (fun j => ren_value xi (sigma j)) i.
Proof.
  intros i. destruct i as [j|].
  - cbn [up_value_value scons funcomp].
    transitivity (ren_value (fun l => up_ren xi (shift l)) (sigma j)).
    + symmetry. apply ren_value_comp.
    + transitivity (ren_value (fun l => shift (xi l)) (sigma j)).
      * apply ren_value_congr. intros l.
        cbn [up_ren scons funcomp shift bound]. reflexivity.
      * apply ren_value_comp.
  - cbn [up_value_value scons funcomp up_ren shift bound]. reflexivity.
Qed.

Lemma ren_up_value_value2 {m n k} (xi : fin n -> fin k) (sigma : fin m -> value n) :
  forall (i : fin (S (S m))),
    ren_value (up_ren (up_ren xi)) (up_value_value (up_value_value sigma) i)
    = up_value_value (up_value_value (fun j => ren_value xi (sigma j))) i.
Proof.
  intros i.
  rewrite (ren_up_value_value (up_ren xi) (up_value_value sigma)).
  apply up_value_value_congr. intros j.
  apply ren_up_value_value.
Qed.

Fixpoint subst_value_ren {m n k} (V : value m) (sigma : fin m -> value n)
  (xi : fin n -> fin k) {struct V} :
  ren_value xi (subst_value sigma V) = subst_value (fun i => ren_value xi (sigma i)) V
with subst_comp_ren {m n k} (c : comp m) (sigma : fin m -> value n)
  (xi : fin n -> fin k) {struct c} :
  ren_comp xi (subst_comp sigma c) = subst_comp (fun i => ren_value xi (sigma i)) c.
Proof.
  - destruct V; simpl.
    + reflexivity.
    + reflexivity.
    + apply f_equal2; apply subst_value_ren.
    + apply f_equal2; [ reflexivity | apply subst_value_ren ].
    + apply f_equal. apply subst_comp_ren.
  - destruct c; simpl.
    + reflexivity.
    + apply f_equal. apply subst_value_ren.
    + apply f_equal.
      rewrite subst_comp_ren.
      apply subst_comp_congr.
      apply ren_up_value_value.
    + apply f_equal2; [ apply subst_comp_ren | apply subst_value_ren ].
    + apply f_equal2; apply subst_comp_ren.
    + apply f_equal. apply subst_value_ren.
    + apply f_equal2;
        [ apply subst_comp_ren
        | rewrite subst_comp_ren; apply subst_comp_congr; apply ren_up_value_value ].
    + apply f_equal2; [ reflexivity | apply subst_comp_ren ].
    + apply f_equal. apply subst_value_ren.
    + apply f_equal3;
        [ apply subst_value_ren
        | rewrite subst_comp_ren; apply subst_comp_congr; apply ren_up_value_value
        | rewrite subst_comp_ren; apply subst_comp_congr; apply ren_up_value_value ].
    + apply f_equal2;
        [ apply subst_value_ren
        | rewrite subst_comp_ren; apply subst_comp_congr; apply ren_up_value_value2 ].
Defined.

(* ------------------------------------------------------------------ *)
(* Composition of substitutions                                       *)
(* ------------------------------------------------------------------ *)

Lemma up_value_value_subst {m n k} (sigma : fin m -> value n) (tau : fin n -> value k) :
  forall (i : fin (S m)),
    subst_value (up_value_value tau) (up_value_value sigma i)
    = up_value_value (fun j => subst_value tau (sigma j)) i.
Proof.
  intros i. destruct i as [j|].
  - cbn [up_value_value scons funcomp].
    change (subst_value (up_value_value tau) (ren_value shift (sigma j))
            = ren_value shift (subst_value tau (sigma j))).
    rewrite (ren_value_subst shift (sigma j) (up_value_value tau)).
    transitivity (subst_value (fun l => ren_value shift (tau l)) (sigma j)).
    + apply subst_value_congr. intros l. reflexivity.
    + symmetry. apply subst_value_ren.
  - cbn [up_value_value scons funcomp up_ren shift bound]. reflexivity.
Qed.

Lemma up_value_value_subst2 {m n k} (sigma : fin m -> value n) (tau : fin n -> value k) :
  forall (i : fin (S (S m))),
    subst_value (up_value_value (up_value_value tau)) (up_value_value (up_value_value sigma) i)
    = up_value_value (up_value_value (fun j => subst_value tau (sigma j))) i.
Proof.
  intros i.
  rewrite (up_value_value_subst (up_value_value sigma) (up_value_value tau)).
  apply up_value_value_congr. intros j.
  apply up_value_value_subst.
Qed.

Fixpoint subst_value_subst {m n k} (V : value m) (sigma : fin m -> value n)
  (tau : fin n -> value k) {struct V} :
  subst_value tau (subst_value sigma V) = subst_value (fun i => subst_value tau (sigma i)) V
with subst_comp_subst {m n k} (c : comp m) (sigma : fin m -> value n)
  (tau : fin n -> value k) {struct c} :
  subst_comp tau (subst_comp sigma c) = subst_comp (fun i => subst_value tau (sigma i)) c.
Proof.
  - destruct V; simpl.
    + reflexivity.
    + reflexivity.
    + apply f_equal2; apply subst_value_subst.
    + apply f_equal2; [ reflexivity | apply subst_value_subst ].
    + apply f_equal. apply subst_comp_subst.
  - destruct c; simpl.
    + reflexivity.
    + apply f_equal. apply subst_value_subst.
    + apply f_equal.
      rewrite subst_comp_subst.
      apply subst_comp_congr.
      apply up_value_value_subst.
    + apply f_equal2; [ apply subst_comp_subst | apply subst_value_subst ].
    + apply f_equal2; apply subst_comp_subst.
    + apply f_equal. apply subst_value_subst.
    + apply f_equal2;
        [ apply subst_comp_subst
        | rewrite subst_comp_subst; apply subst_comp_congr; apply up_value_value_subst ].
    + apply f_equal2; [ reflexivity | apply subst_comp_subst ].
    + apply f_equal. apply subst_value_subst.
    + apply f_equal3;
        [ apply subst_value_subst
        | rewrite subst_comp_subst; apply subst_comp_congr; apply up_value_value_subst
        | rewrite subst_comp_subst; apply subst_comp_congr; apply up_value_value_subst ].
    + apply f_equal2;
        [ apply subst_value_subst
        | rewrite subst_comp_subst; apply subst_comp_congr; apply up_value_value_subst2 ].
Defined.

(* ------------------------------------------------------------------ *)
(* Corollaries for applying a substitution under a binder              *)
(* ------------------------------------------------------------------ *)

Lemma up_value_value_app {m n} (sigma : fin m -> value n) (v : value n) :
  forall (i : fin (S m)),
    subst_value (scons v (@ids value VarInstance_value n)) (up_value_value sigma i)
    = scons v sigma i.
Proof.
  intros i. destruct i as [j|].
  - cbn [up_value_value scons funcomp].
    change (subst_value (scons v (@ids value VarInstance_value n))
              (ren_value shift (sigma j)) = sigma j).
    rewrite (ren_value_subst shift (sigma j)
               (scons v (@ids value VarInstance_value n))).
    transitivity (subst_value (@ids value VarInstance_value n) (sigma j)).
    + apply subst_value_congr. intros l. reflexivity.
    + apply subst_value_id.
  - cbn [up_value_value scons funcomp]. reflexivity.
Qed.

Lemma up_up_value_value_caseP {m n} (sigma : fin m -> value n) (v1 v2 : value n) :
  forall (i : fin (S (S m))),
    subst_value (scons v2 (scons v1 (@ids value VarInstance_value n)))
      (up_value_value (up_value_value sigma) i)
    = scons v2 (scons v1 sigma) i.
Proof.
  intros i. destruct i as [j|].
  - cbn [up_value_value scons funcomp].
    change (subst_value (scons v2 (scons v1 (@ids value VarInstance_value n)))
              (ren_value shift (up_value_value sigma j)) = scons v1 sigma j).
    rewrite (ren_value_subst shift (up_value_value sigma j)
               (scons v2 (scons v1 (@ids value VarInstance_value n)))).
    transitivity (subst_value (scons v1 (@ids value VarInstance_value n))
                    (up_value_value sigma j)).
    + apply subst_value_congr. intros l. reflexivity.
    + apply up_value_value_app.
  - cbn [up_value_value scons funcomp]. reflexivity.
Qed.

Lemma subst_comp_up_app {m n} (c : comp (S m)) (sigma : fin m -> value n)
  (v : value n) :
  subst_comp (scons v (@ids value VarInstance_value n))
    (subst_comp (up_value_value sigma) c)
  = subst_comp (scons v sigma) c.
Proof.
  rewrite subst_comp_subst.
  apply subst_comp_congr.
  apply up_value_value_app.
Qed.

Lemma subst_comp_up_up_caseP {m n} (c : comp (S (S m))) (sigma : fin m -> value n)
  (v1 v2 : value n) :
  subst_comp (scons v2 (scons v1 (@ids value VarInstance_value n)))
    (subst_comp (up_value_value (up_value_value sigma)) c)
  = subst_comp (scons v2 (scons v1 sigma)) c.
Proof.
  rewrite subst_comp_subst.
  apply subst_comp_congr.
  apply up_up_value_value_caseP.
Qed.

Lemma subst_value_up_app {m n} (V : value (S m)) (sigma : fin m -> value n)
  (v : value n) :
  subst_value (scons v (@ids value VarInstance_value n))
    (subst_value (up_value_value sigma) V)
  = subst_value (scons v sigma) V.
Proof.
  rewrite subst_value_subst.
  apply subst_value_congr.
  apply up_value_value_app.
Qed.

Print Assumptions subst_comp_up_app.
Set Implicit Arguments.
Require Import CBPV.ObservationalEquivalence CBPV.StrongReduction CBPV.AbstractReductionSystems.
Import CommaNotation.

(* Strong (structural) value relation; VRel0 adds syntactic equality so arrow
   transitivity has a reflexive argument relation. *)
Fixpoint SVRel (A: valtype) (V W: value 0) {struct A} : Prop :=
  match A with
  | zero => V = W
  | one => V = W
  | U B => exists c c', V = thunk c /\ W = thunk c' /\ CRel0 B c c'
  | Sigma A1 A2 => exists b v v', V = inj b v /\ W = inj b v' /\
       (if b then SVRel A1 v v' else SVRel A2 v v')
  | cross A1 A2 => exists v1 v2 w1 w2, V = pair v1 v2 /\ W = pair w1 w2 /\
       SVRel A1 v1 w1 /\ SVRel A2 v2 w2
  end
with CRel0 (B: comptype) (c c': comp 0) {struct B} : Prop :=
  match B with
  | cone => True
  | F A => (forall v, c ▷ ret v -> exists v', c' ▷ ret v' /\ SVRel A v v')
        /\ (forall v', c' ▷ ret v' -> exists v, c ▷ ret v /\ SVRel A v v')
  | Pi B1 B2 => CRel0 B2 (proj false c) (proj false c') /\
                CRel0 B1 (proj true c) (proj true c')
  | arrow A B => forall v v', SVRel A v v' -> CRel0 B (c v)(c' v')
  end.

Definition VRel0 (A: valtype) (V W: value 0) : Prop := SVRel A V W.

Lemma SVRel_to_VRel0 A V W : SVRel A V W -> VRel0 A V W.
Proof. intros H. exact H. Qed.

(* Symmetry of SVRel and CRel0; VRel0 later. *)
Fixpoint SVRel_sym (A: valtype) (V W: value 0) {struct A} : SVRel A V W -> SVRel A W V
with CRel0_sym (B: comptype) (c c': comp 0) {struct B} : CRel0 B c c' -> CRel0 B c' c.
Proof.
  - destruct A; simpl.
    + intros H. symmetry. exact H.
    + intros H. symmetry. exact H.
    + intros (cc & cc' & E & E' & H).
      exists cc', cc. split.
      * exact E'.
      * split.
        -- exact E.
        -- apply CRel0_sym. exact H.
    + intros (b & u & u' & E & E' & H).
      exists b, u', u. split.
      * exact E'.
      * split.
        -- exact E.
        -- destruct b; [apply SVRel_sym|apply SVRel_sym]; exact H.
    + intros (v1 & v2 & w1 & w2 & E & E' & H1 & H2).
      exists w1, w2, v1, v2. split.
      * exact E'.
      * split.
        -- exact E.
        -- split.
           ++ apply SVRel_sym. exact H1.
           ++ apply SVRel_sym. exact H2.
  - destruct B; simpl.
    + intros _. exact I.
    + intros (H1 & H2). split.
      * intros vv HH. destruct (H2 vv HH) as (u & Hu & HV).
        exists u. split; [exact Hu|apply SVRel_sym; exact HV].
      * intros vv HH. destruct (H1 vv HH) as (u & Hu & HV).
        exists u. split; [exact Hu|apply SVRel_sym; exact HV].
    + intros (H1 & H2). split.
      * apply CRel0_sym. exact H1.
      * apply CRel0_sym. exact H2.
    + intros H a b HV.
      apply CRel0_sym.
      apply H.
      apply SVRel_sym. exact HV.
Qed.

Lemma VRel0_sym A V W : VRel0 A V W -> VRel0 A W V.
Proof. intros H. apply SVRel_sym. exact H. Qed.

(* Bigstep equivalence and transfer *)
Definition BSim (c c': comp 0) : Prop := forall r, c ▷ r <-> c' ▷ r.

Lemma BSim_refl c : BSim c c.
Proof. intros r. reflexivity. Qed.

Lemma BSim_sym c c' : BSim c c' -> BSim c' c.
Proof. intros H r. symmetry. apply H. Qed.

Lemma BSim_trans c c' c'' : BSim c c' -> BSim c' c'' -> BSim c c''.
Proof. intros H1 H2 r. transitivity (c' ▷ r); [apply H1|apply H2]. Qed.

Lemma BSim_app c c' v : BSim c c' -> BSim (c v) (c' v).
Proof.
  intros H r. split; intro Hr.
  - inversion Hr; subst. eapply bigstepApp.
    + apply H. eassumption.
    + eassumption.
  - inversion Hr; subst. eapply bigstepApp.
    + apply H. eassumption.
    + eassumption.
Qed.

Lemma BSim_proj c c' b : BSim c c' -> BSim (proj b c) (proj b c').
Proof.
  intros H r. split; intro Hr.
  - inversion Hr; subst. eapply bigstepProj.
    + apply H. eassumption.
    + eassumption.
  - inversion Hr; subst. eapply bigstepProj.
    + apply H. eassumption.
    + eassumption.
Qed.

Lemma BSim_force_thunk (d: comp 0) : BSim (force (thunk d)) d.
Proof.
  intros r. split; intro Hr.
  - inversion Hr. assumption.
  - eapply bigstepForce. exact Hr.
Qed.

Lemma BSim_proj_tuple b (c1 c2: comp 0) :
  BSim (proj b (tuple c1 c2)) (if b then c1 else c2).
Proof.
  intros r. split; intro Hr.
  - inversion Hr; subst. match goal with Hf : tuple _ _ ▷ _ |- _ => inversion Hf; subst end. eassumption.
  - eapply bigstepProj.
    + apply bigstepTuple.
    + exact Hr.
Qed.

Lemma BSim_app_lambda (c0: comp 1) (v: value 0) :
  BSim (app (lambda c0) v) (c0[v..]).
Proof.
  intros r. split; intro Hr.
  - inversion Hr; subst. match goal with Hf : lambda _ ▷ _ |- _ => inversion Hf; subst end. eassumption.
  - eapply bigstepApp.
    + apply bigstepLambda.
    + exact Hr.
Qed.

Fixpoint CRel0_BSim_left (B: comptype) (X Y Z: comp 0) {struct B} :
  BSim X Y -> CRel0 B Y Z -> CRel0 B X Z
with CRel0_BSim_right (B: comptype) (X Y Z: comp 0) {struct B} :
  CRel0 B X Y -> BSim Y Z -> CRel0 B X Z.
Proof.
  - destruct B; simpl.
    + intros _ _. exact I.
    + intros HB HR. split.
      * intros vv HH. apply HB in HH. apply HR in HH. exact HH.
      * intros vv HH. apply HR in HH. destruct HH as (w & Hw & HV). exists w. split; [|exact HV].
        apply HB. exact Hw.
    + intros HB (H1 & H2). split.
      * eapply CRel0_BSim_left.
        -- apply BSim_proj. exact HB.
        -- exact H1.
      * eapply CRel0_BSim_left.
        -- apply BSim_proj. exact HB.
        -- exact H2.
    + intros HB HR a b HV.
      eapply CRel0_BSim_left.
      * apply BSim_app. exact HB.
      * apply HR. exact HV.
  - destruct B; simpl.
    + intros _ _. exact I.
    + intros HR HB. split.
      * intros vv HH. apply HR in HH. destruct HH as (w & Hw & HV). exists w. split; [|exact HV].
        apply HB. exact Hw.
      * intros vv HH. apply HB in HH. apply HR in HH. exact HH.
    + intros (H1 & H2) HB. split.
      * eapply CRel0_BSim_right.
        -- exact H1.
        -- apply BSim_proj. exact HB.
      * eapply CRel0_BSim_right.
        -- exact H2.
        -- apply BSim_proj. exact HB.
    + intros HR HB a b HV.
      eapply CRel0_BSim_right.
      * apply HR. exact HV.
      * apply BSim_app. exact HB.
Qed.

(* Bigstep inversion lemmas *)
Lemma bigstep_letin_inv (X: comp 0) (Y: comp 1) r : letin X Y ▷ r ->
  exists (u: value 0), X ▷ ret u /\ Y[u..] ▷ r.
Proof. intros H. inversion H. eauto. Qed.

Lemma bigstep_app_inv (c: comp 0) v r : c v ▷ r ->
  exists (c0: comp 1), c ▷ lambda c0 /\ c0[v..] ▷ r.
Proof. intros H. inversion H. eauto. Qed.

Lemma bigstep_proj_inv b (c: comp 0) r : proj b c ▷ r ->
  exists (c1 c2: comp 0), c ▷ tuple c1 c2 /\ (if b then c1 else c2) ▷ r.
Proof. intros H. inversion H. eauto. Qed.

Lemma bigstep_caseS_inv (V: value 0) (c1 c2: comp 1) r :
  caseS V c1 c2 ▷ r ->
  exists b (u: value 0), V = inj b u /\ (if b then c1 else c2)[u..] ▷ r.
Proof. intros H. inversion H. eauto. Qed.

Lemma bigstep_caseP_inv (V: value 0) (c: comp 2) r :
  caseP V c ▷ r ->
  exists (v1 v2: value 0), V = pair v1 v2 /\ c[scons v2 (scons v1 ids)] ▷ r.
Proof. intros H. inversion H. eauto. Qed.

(* Evaluation stacks of applications/projections *)
Inductive ctxstack : comptype -> comptype -> Type :=
| cs_hole : forall B, ctxstack B B
| cs_projL : forall B B1 B2, ctxstack B (Pi B1 B2) -> ctxstack B B2
| cs_projR : forall B B1 B2, ctxstack B (Pi B1 B2) -> ctxstack B B1
| cs_app : forall B A C, ctxstack B (arrow A C) -> value 0 -> ctxstack B C.

Fixpoint apply_stack {B C} (K: ctxstack B C) (c: comp 0) : comp 0 :=
  match K in ctxstack _ C return comp 0 with
  | cs_hole _ => c
  | cs_projL K0 => proj false (apply_stack K0 c)
  | cs_projR K0 => proj true (apply_stack K0 c)
  | cs_app K0 v => apply_stack K0 c v
  end.

Inductive stack_pair : forall B C, ctxstack B C -> ctxstack B C -> Prop :=
| sp_hole B : stack_pair (cs_hole B) (cs_hole B)
| sp_projL : forall B B1 B2 (K K' : ctxstack B (Pi B1 B2)),
      stack_pair K K' -> stack_pair (cs_projL K) (cs_projL K')
| sp_projR : forall B B1 B2 (K K' : ctxstack B (Pi B1 B2)),
      stack_pair K K' -> stack_pair (cs_projR K) (cs_projR K')
| sp_app : forall B A C (K K' : ctxstack B (arrow A C)) v v',
      stack_pair K K' -> VRel0 A v v' -> stack_pair (cs_app K v) (cs_app K' v').

Lemma stack_compat : forall B C (K K': ctxstack B C),
  stack_pair K K' -> forall Z Z', CRel0 B Z Z' ->
  CRel0 C (apply_stack K Z) (apply_stack K' Z').
Proof.
  intros B C K K' SP. induction SP as
    [B|B B1 B2 K K' SP IH|B B1 B2 K K' SP IH|B A C K K' v v' SP IH HV];
    intros Z Z' HZ.
  - simpl. exact HZ.
  - simpl. exact (proj1 (IH Z Z' HZ)).
  - simpl. exact (proj2 (IH Z Z' HZ)).
  - simpl. exact (IH Z Z' HZ v v' HV).
Qed.

Lemma let_decomp : forall (B C: comptype) (K: ctxstack B C) X Y r,
  apply_stack K (letin X Y) ▷ r ->
  exists u, X ▷ ret u /\ apply_stack K (Y[u..]) ▷ r.
Proof.
  intros B C K. induction K as
    [B|B B1 B2 K0 IHK|B B1 B2 K0 IHK|B A C K0 IHK v];
    intros X Y r H.
  - simpl in H. apply bigstep_letin_inv in H. exact H.
  - simpl in H. apply bigstep_proj_inv in H as (a & b & Hp & Hr).
    destruct (IHK X Y (tuple a b) Hp) as (u & Hx & Hy).
    exists u. split; [exact Hx|]. simpl. eapply bigstepProj; eassumption.
  - simpl in H. apply bigstep_proj_inv in H as (a & b & Hp & Hr).
    destruct (IHK X Y (tuple a b) Hp) as (u & Hx & Hy).
    exists u. split; [exact Hx|]. simpl. eapply bigstepProj; eassumption.
  - simpl in H. apply bigstep_app_inv in H as (c0 & Hp & Hr).
    destruct (IHK X Y (lambda c0) Hp) as (u & Hx & Hy).
    exists u. split; [exact Hx|]. simpl. eapply bigstepApp; eassumption.
Qed.
Arguments let_decomp {B C} K X Y r _.

Lemma let_decomp_rev : forall (B C: comptype) (K: ctxstack B C) X Y u r,
  X ▷ ret u -> apply_stack K (Y[u..]) ▷ r -> apply_stack K (letin X Y) ▷ r.
Proof.
  intros B C K. induction K as
    [B|B B1 B2 K0 IHK|B B1 B2 K0 IHK|B A C K0 IHK v];
    intros X Y u r Hx H.
  - simpl in *. eapply bigstepLetin; eassumption.
  - simpl in H. apply bigstep_proj_inv in H as (a & b & Hp & Hr).
    simpl. eapply bigstepProj.
    + apply IHK with (u:=u).
      * exact Hx.
      * exact Hp.
    + exact Hr.
  - simpl in H. apply bigstep_proj_inv in H as (a & b & Hp & Hr).
    simpl. eapply bigstepProj.
    + apply IHK with (u:=u).
      * exact Hx.
      * exact Hp.
    + exact Hr.
  - simpl in H. apply bigstep_app_inv in H as (c0 & Hp & Hr).
    simpl. eapply bigstepApp.
    + apply IHK with (u:=u).
      * exact Hx.
      * exact Hp.
    + exact Hr.
Qed.
Arguments let_decomp_rev {B C} K X Y u r _ _.

(* Bind (letin) is compatible with the logical relation, for any stack and
   any result type. *)
Lemma bind_letin_stack : forall (C B: comptype) (K K': ctxstack B C),
  stack_pair K K' -> forall (A: valtype) X X' Y Y',
  CRel0 (F A) X X' ->
  (forall u u', SVRel A u u' -> CRel0 B (Y[u..]) (Y'[u'..])) ->
  CRel0 C (apply_stack K (letin X Y)) (apply_stack K' (letin X' Y')).
Proof.
  induction C as [|A0|C1 IHC1 C2 IHC2|A0 C1 IHC1]; intros B K K' SP A X X' Y Y' HX HY.
  - simpl. exact I.
  - (* C = F A0 *)
    destruct HX as (HX1 & HX2).
    split.
    + intros v Hv.
      destruct (let_decomp K X Y (ret v) Hv) as (u & Hu & Hku).
      destruct (HX1 u Hu) as (u' & Hu' & Hsu).
      pose proof (HY u u' Hsu) as Hc.
      pose proof (stack_compat SP (Y[u..]) (Y'[u'..]) Hc) as Hcom.
      cbn [CRel0] in Hcom. destruct Hcom as (Hcom1 & _).
      destruct (Hcom1 v Hku) as (v' & Hv' & Hsv).
      exists v'. split; [|exact Hsv].
      eapply let_decomp_rev; [exact Hu'|exact Hv'].
    + intros v' Hv'.
      destruct (let_decomp K' X' Y' (ret v') Hv') as (u' & Hu' & Hku').
      destruct (HX2 u' Hu') as (u & Hu & Hsu).
      pose proof (HY u u' Hsu) as Hc.
      pose proof (stack_compat SP (Y[u..]) (Y'[u'..]) Hc) as Hcom.
      cbn [CRel0] in Hcom. destruct Hcom as (_ & Hcom2).
      destruct (Hcom2 v' Hku') as (v & Hv & Hsv).
      exists v. split; [|exact Hsv].
      eapply let_decomp_rev; [exact Hu|exact Hv].
  - (* C = Pi C1 C2 *)
    split.
    + eapply (IHC2 B (cs_projL K) (cs_projL K')).
      * apply sp_projL. exact SP.
      * exact HX.
      * exact HY.
    + eapply (IHC1 B (cs_projR K) (cs_projR K')).
      * apply sp_projR. exact SP.
      * exact HX.
      * exact HY.
  - (* C = arrow A0 C1 *)
    intros v v' HV.
    eapply (IHC1 B (cs_app K v) (cs_app K' v')).
    + apply sp_app with (v:=v)(v':=v').
      * exact SP.
      * exact HV.
    + exact HX.
    + exact HY.
Qed.

(* caseS through a stack *)
Lemma caseS_decomp : forall (B C: comptype) (K: ctxstack B C)
  (V: value 0) (c1 c2: comp 1) r,
  apply_stack K (caseS V c1 c2) ▷ r ->
  exists b u, V = inj b u /\
    apply_stack K ((if b then c1 else c2)[u..]) ▷ r.
Proof.
  intros B C K. induction K as
    [B|B B1 B2 K0 IHK|B B1 B2 K0 IHK|B A C K0 IHK v];
    intros V c1 c2 r H.
  - simpl in H. apply bigstep_caseS_inv in H. exact H.
  - simpl in H. apply bigstep_proj_inv in H as (a & b & Hp & Hr).
    destruct (IHK V c1 c2 (tuple a b) Hp) as (bb & u & HV & Hy).
    exists bb, u. split; [exact HV|]. simpl. eapply bigstepProj; eassumption.
  - simpl in H. apply bigstep_proj_inv in H as (a & b & Hp & Hr).
    destruct (IHK V c1 c2 (tuple a b) Hp) as (bb & u & HV & Hy).
    exists bb, u. split; [exact HV|]. simpl. eapply bigstepProj; eassumption.
  - simpl in H. apply bigstep_app_inv in H as (c0 & Hp & Hr).
    destruct (IHK V c1 c2 (lambda c0) Hp) as (bb & u & HV & Hy).
    exists bb, u. split; [exact HV|]. simpl. eapply bigstepApp; eassumption.
Qed.
Arguments caseS_decomp {B C} K V c1 c2 r _.

Lemma caseS_decomp_rev : forall (B C: comptype) (K: ctxstack B C)
  (V: value 0) (c1 c2: comp 1) b u r,
  V = inj b u ->
  apply_stack K ((if b then c1 else c2)[u..]) ▷ r ->
  apply_stack K (caseS V c1 c2) ▷ r.
Proof.
  intros B C K. induction K as
    [B|B B1 B2 K0 IHK|B B1 B2 K0 IHK|B A C K0 IHK v];
    intros V c1 c2 bb u r HV H.
  - simpl in *. subst. eapply bigstepCaseS. exact H.
  - simpl in H. apply bigstep_proj_inv in H as (a & b & Hp & Hr).
    simpl. eapply bigstepProj.
    + eapply IHK; [exact HV|exact Hp].
    + exact Hr.
  - simpl in H. apply bigstep_proj_inv in H as (a & b & Hp & Hr).
    simpl. eapply bigstepProj.
    + eapply IHK; [exact HV|exact Hp].
    + exact Hr.
  - simpl in H. apply bigstep_app_inv in H as (c0 & Hp & Hr).
    simpl. eapply bigstepApp.
    + eapply IHK; [exact HV|exact Hp].
    + exact Hr.
Qed.
Arguments caseS_decomp_rev {B C} K V c1 c2 b u r _ _.

Lemma bind_caseS_stack : forall (C Bres: comptype) (K K': ctxstack Bres C),
  stack_pair K K' ->
  forall A1 A2 (V V': value 0) (c1 c1' c2 c2': comp 1),
  SVRel (Sigma A1 A2) V V' ->
  (forall u u', SVRel A1 u u' -> CRel0 Bres (c1[u..]) (c1'[u'..])) ->
  (forall u u', SVRel A2 u u' -> CRel0 Bres (c2[u..]) (c2'[u'..])) ->
  CRel0 C (apply_stack K (caseS V c1 c2))
           (apply_stack K' (caseS V' c1' c2')).
Proof.
  induction C as [|A0|C1 IHC1 C2 IHC2|A0 C1 IHC1];
    intros Bres K K' SP A1 A2 V V' c1 c1' c2 c2' HV H1 H2.
  - simpl. exact I.
  - (* C = F A0 *)
    destruct HV as (b & u & u' & Ev & Ev' & Hvu).
    split.
    + intros v Hv.
      destruct (caseS_decomp K V c1 c2 (ret v) Hv) as (b0 & w & HV0 & Hkv).
      rewrite Ev in HV0. injection HV0 as Hb Hw. subst b0. subst u.
      assert (Hc : CRel0 Bres ((if b then c1 else c2)[w..])
                        ((if b then c1' else c2')[u'..])).
      { destruct b; simpl in *; [apply H1|apply H2]; exact Hvu. }
      pose proof (stack_compat SP _ _ Hc) as Hcom.
      cbn [CRel0] in Hcom. destruct Hcom as (Hcom1 & _).
        destruct (Hcom1 v Hkv) as (v' & Hv' & Hsv).
        exists v'. split; [|exact Hsv].
        eapply caseS_decomp_rev; [exact Ev'|exact Hv'].
    + intros v' Hv'.
      destruct (caseS_decomp K' V' c1' c2' (ret v') Hv') as (b0 & w' & HV0 & Hkv').
      rewrite Ev' in HV0. injection HV0 as Hb Hw. subst b0. subst u'.
      assert (Hc : CRel0 Bres ((if b then c1 else c2)[u..])
                        ((if b then c1' else c2')[w'..])).
      { destruct b; simpl in *; [apply H1|apply H2]; exact Hvu. }
      pose proof (stack_compat SP _ _ Hc) as Hcom.
      cbn [CRel0] in Hcom. destruct Hcom as (_ & Hcom2).
        destruct (Hcom2 v' Hkv') as (v & Hv & Hsv).
        exists v. split; [|exact Hsv].
        eapply caseS_decomp_rev; [exact Ev|exact Hv].
  - (* C = Pi C1 C2 *)
    split.
    + eapply (IHC2 Bres (cs_projL K) (cs_projL K')).
      * apply sp_projL. exact SP.
      * exact HV.
      * exact H1.
      * exact H2.
    + eapply (IHC1 Bres (cs_projR K) (cs_projR K')).
      * apply sp_projR. exact SP.
      * exact HV.
      * exact H1.
      * exact H2.
  - (* C = arrow A0 C1 *)
    intros v v' HVv.
    eapply (IHC1 Bres (cs_app K v) (cs_app K' v')).
    + apply sp_app with (v:=v)(v':=v').
      * exact SP.
      * exact HVv.
    + exact HV.
    + exact H1.
    + exact H2.
Qed.

(* caseP through a stack *)
Lemma caseP_decomp : forall (B C: comptype) (K: ctxstack B C)
  (V: value 0) (c: comp 2) r,
  apply_stack K (caseP V c) ▷ r ->
  exists v1 v2, V = pair v1 v2 /\ apply_stack K (c[scons v2 (scons v1 ids)]) ▷ r.
Proof.
  intros B C K. induction K as
    [B|B B1 B2 K0 IHK|B B1 B2 K0 IHK|B A C K0 IHK v];
    intros V c r H.
  - simpl in H. apply bigstep_caseP_inv in H. exact H.
  - simpl in H. apply bigstep_proj_inv in H as (a & b & Hp & Hr).
    destruct (IHK V c (tuple a b) Hp) as (v1 & v2 & HV & Hy).
    exists v1, v2. split; [exact HV|]. simpl. eapply bigstepProj; eassumption.
  - simpl in H. apply bigstep_proj_inv in H as (a & b & Hp & Hr).
    destruct (IHK V c (tuple a b) Hp) as (v1 & v2 & HV & Hy).
    exists v1, v2. split; [exact HV|]. simpl. eapply bigstepProj; eassumption.
  - simpl in H. apply bigstep_app_inv in H as (c0 & Hp & Hr).
    destruct (IHK V c (lambda c0) Hp) as (v1 & v2 & HV & Hy).
    exists v1, v2. split; [exact HV|]. simpl. eapply bigstepApp; eassumption.
Qed.
Arguments caseP_decomp {B C} K V c r _.

Lemma caseP_decomp_rev : forall (B C: comptype) (K: ctxstack B C)
  (V: value 0) (c: comp 2) v1 v2 r,
  V = pair v1 v2 -> apply_stack K (c[scons v2 (scons v1 ids)]) ▷ r ->
  apply_stack K (caseP V c) ▷ r.
Proof.
  intros B C K. induction K as
    [B|B B1 B2 K0 IHK|B B1 B2 K0 IHK|B A C K0 IHK v];
    intros V c a b r HV H.
  - simpl in *. subst. eapply bigstepCaseP. exact H.
  - simpl in H. apply bigstep_proj_inv in H as (x & y & Hp & Hr).
    simpl. eapply bigstepProj.
    + eapply IHK; [exact HV|exact Hp].
    + exact Hr.
  - simpl in H. apply bigstep_proj_inv in H as (x & y & Hp & Hr).
    simpl. eapply bigstepProj.
    + eapply IHK; [exact HV|exact Hp].
    + exact Hr.
  - simpl in H. apply bigstep_app_inv in H as (c0 & Hp & Hr).
    simpl. eapply bigstepApp.
    + eapply IHK; [exact HV|exact Hp].
    + exact Hr.
Qed.
Arguments caseP_decomp_rev {B C} K V c v1 v2 r _ _.

Lemma bind_caseP_stack : forall (C Bres: comptype) (K K': ctxstack Bres C),
  stack_pair K K' ->
  forall A1 A2 (V V': value 0) (c c': comp 2),
  SVRel (cross A1 A2) V V' ->
  (forall v1 v2 v1' v2', SVRel A1 v1 v1' -> SVRel A2 v2 v2' ->
      CRel0 Bres (c[scons v2 (scons v1 ids)]) (c'[scons v2' (scons v1' ids)])) ->
  CRel0 C (apply_stack K (caseP V c))
           (apply_stack K' (caseP V' c')).
Proof.
  induction C as [|A0|C1 IHC1 C2 IHC2|A0 C1 IHC1];
    intros Bres K K' SP A1 A2 V V' c c' HV H.
  - simpl. exact I.
  - destruct HV as (v1 & v2 & v1' & v2' & Ev & Ev' & Hv1 & Hv2).
    split.
    + intros w Hw.
      destruct (caseP_decomp K V c (ret w) Hw) as (w1 & w2 & HV0 & Hkw).
      rewrite Ev in HV0. injection HV0 as H1 H2. subst w1. subst w2.
      assert (Hc : CRel0 Bres (c[scons v2 (scons v1 ids)]) (c'[scons v2' (scons v1' ids)])).
      { apply H; assumption. }
      pose proof (stack_compat SP _ _ Hc) as Hcom.
      cbn [CRel0] in Hcom. destruct Hcom as (Hcom1 & _).
      destruct (Hcom1 w Hkw) as (w' & Hw' & Hsv).
      exists w'. split; [|exact Hsv].
      eapply caseP_decomp_rev; [exact Ev'|exact Hw'].
    + intros w' Hw'.
      destruct (caseP_decomp K' V' c' (ret w') Hw') as (w1 & w2 & HV0 & Hkw').
      rewrite Ev' in HV0. injection HV0 as H1 H2. subst v1'. subst v2'.
      assert (Hc : CRel0 Bres (c[scons v2 (scons v1 ids)]) (c'[scons w2 (scons w1 ids)])).
      { apply H; assumption. }
      pose proof (stack_compat SP _ _ Hc) as Hcom.
      cbn [CRel0] in Hcom. destruct Hcom as (_ & Hcom2).
      destruct (Hcom2 w' Hkw') as (w & Hw & Hsv).
      exists w. split; [|exact Hsv].
      eapply caseP_decomp_rev; [exact Ev|exact Hw].
  - split.
    + eapply (IHC2 Bres (cs_projL K) (cs_projL K')).
      * apply sp_projL. exact SP.
      * exact HV.
      * exact H.
    + eapply (IHC1 Bres (cs_projR K) (cs_projR K')).
      * apply sp_projR. exact SP.
      * exact HV.
      * exact H.
  - intros w w' HW.
    eapply (IHC1 Bres (cs_app K w) (cs_app K' w')).
    + apply sp_app with (v:=w)(v':=w').
      * exact SP.
      * exact HW.
    + exact HV.
    + exact H.
Qed.

(* Terms with no bigstep result are related at every type. *)
Lemma no_bigstep_proj b (c: comp 0) : (forall (r: comp 0), ~ (c ▷ r)) ->
  forall (r: comp 0), ~ (proj b c ▷ r).
Proof.
  intros H r Hr. inversion Hr; subst.
  match goal with Hp : c ▷ tuple ?a ?b |- _ => exact (H (tuple a b) Hp) end.
Qed.

Lemma no_bigstep_app (c: comp 0) v : (forall (r: comp 0), ~ (c ▷ r)) ->
  forall (r: comp 0), ~ (c v ▷ r).
Proof.
  intros H r Hr. inversion Hr; subst.
  match goal with Hp : c ▷ lambda ?c0 |- _ => exact (H (lambda c0) Hp) end.
Qed.

Lemma no_bigstep_caseZ (V: value 0) : forall (r: comp 0), ~ (caseZ V ▷ r).
Proof. intros r Hr. inversion Hr. Qed.

Fixpoint CRel0_no_bigstep (B: comptype) (c c': comp 0) {struct B} :
  (forall r, ~ (c ▷ r)) -> (forall r, ~ (c' ▷ r)) -> CRel0 B c c'.
Proof.
  destruct B; simpl.
  - intros _ _. exact I.
  - intros Hc Hc'. split.
    + intros vv Hv. exfalso. exact (Hc (ret vv) Hv).
    + intros vv Hv. exfalso. exact (Hc' (ret vv) Hv).
  - intros Hc Hc'. split.
    + apply CRel0_no_bigstep.
      * apply no_bigstep_proj. exact Hc.
      * apply no_bigstep_proj. exact Hc'.
    + apply CRel0_no_bigstep.
      * apply no_bigstep_proj. exact Hc.
      * apply no_bigstep_proj. exact Hc'.
  - intros Hc Hc' a b HV.
    apply CRel0_no_bigstep.
    + apply no_bigstep_app. exact Hc.
    + apply no_bigstep_app. exact Hc'.
Qed.

(* Two-sided BSim transfer through a CRel0 relation *)
Fixpoint CRel0_BSim_both (B: comptype) (X Y Z W: comp 0) {struct B} :
  BSim X Y -> CRel0 B Y Z -> BSim Z W -> CRel0 B X W.
Proof.
  destruct B; simpl.
  - intros _ _ _. exact I.
  - intros HB1 HR HB2. destruct HR as (HR1 & HR2). split.
    + intros vv HH. apply (proj1 (HB1 (ret vv))) in HH.
      destruct (HR1 vv HH) as (v' & Hv' & HV).
      exists v'. split; [|exact HV]. apply (proj1 (HB2 (ret v'))). exact Hv'.
    + intros vv HH. apply (proj2 (HB2 (ret vv))) in HH.
      destruct (HR2 vv HH) as (u & Hu & HV).
      exists u. split; [|exact HV]. apply (proj2 (HB1 (ret u))). exact Hu.
  - intros HB1 (H1 & H2) HB2. split.
    + eapply CRel0_BSim_both; [apply BSim_proj; exact HB1|exact H1|apply BSim_proj; exact HB2].
    + eapply CRel0_BSim_both; [apply BSim_proj; exact HB1|exact H2|apply BSim_proj; exact HB2].
  - intros HB1 HR HB2 a b HV.
    eapply CRel0_BSim_both; [apply BSim_app; exact HB1|apply HR; exact HV|apply BSim_app; exact HB2].
Qed.

Lemma subst_comp_up_app0 {m} (c: comp (S m)) (σ: fin m -> value 0) (v: value 0) :
  (subst_comp (up_value_value σ) c)[v..] = subst_comp (scons v σ) c.
Proof. apply subst_comp_up_app. Qed.

Lemma subst_comp_up_up_caseP0 {m} (c: comp (S (S m))) (σ: fin m -> value 0)
  (v1 v2: value 0) :
  (subst_comp (up_value_value (up_value_value σ)) c)
    [scons v2 (scons v1 (@ids value VarInstance_value 0))]
  = subst_comp (scons v2 (scons v1 σ)) c.
Proof. apply subst_comp_up_up_caseP. Qed.

Definition EnvRel {n} (Γ: ctx n) (σ σ': fin n -> value 0) : Prop :=
  forall i, SVRel (Γ i) (σ i) (σ' i).

Definition Pval (m:nat) (Γ: ctx m) (V: value m) (A: valtype)
  (H: Γ ⊩ V : A) : Prop :=
  forall (σ σ': fin m -> value 0), EnvRel Γ σ σ' ->
    SVRel A (subst_value σ V) (subst_value σ' V).

Definition Pcomp (m:nat) (Γ: ctx m) (c: comp m) (B: comptype)
  (H: Γ ⊢ c : B) : Prop :=
  forall (σ σ': fin m -> value 0), EnvRel Γ σ σ' ->
    CRel0 B (subst_comp σ c) (subst_comp σ' c).
Arguments Pval m Γ V A H : clear implicits.
Arguments Pcomp m Γ c B H : clear implicits.

Lemma fundamental_value_comp :
  forall (m:nat) (Γ:ctx m),
   (forall (V:value m) (A:valtype) (H:Γ ⊩ V : A), Pval m Γ V A H)
   /\ (forall (c:comp m) (B:comptype) (H:Γ ⊢ c : B), Pcomp m Γ c B H).
Proof.
  apply (mutindt_value_computation_typing Pval Pcomp).
  - (* typeVar *) intros m Γ i σ σ' HE. simpl. apply HE.
  - (* typeUnit *) intros m Γ σ σ' HE. simpl. reflexivity.
  - (* typePair *) intros m Γ v1 v2 A1 A2 H1 IH1 H2 IH2 σ σ' HE. simpl.
    eexists (subst_value σ v1), (subst_value σ v2), (subst_value σ' v1), (subst_value σ' v2).
    split.
    * reflexivity.
    * split.
      -- reflexivity.
      -- split.
         ++ apply IH1. exact HE.
         ++ apply IH2. exact HE.
  - (* typeSum *) intros m Γ A1 A2 b v H IH σ σ' HE. simpl.
    eexists b, (subst_value σ v), (subst_value σ' v).
    split.
    * reflexivity.
    * split.
      -- reflexivity.
      -- destruct b; simpl in *; apply IH; exact HE.
  - (* typeThunk *) intros m Γ c A H IH σ σ' HE. simpl.
    eexists (subst_comp σ c), (subst_comp σ' c).
    split.
    * reflexivity.
    * split.
      -- reflexivity.
      -- apply IH. exact HE.
  - (* typeCone *) intros m Γ σ σ' HE. simpl. exact I.
  - (* typeLambda *) intros m Γ c A B H IH σ σ' HE. simpl.
    intros v v' HV.
    pose proof (BSim_app_lambda (subst_comp (up_value_value σ) c) v) as HB1.
    pose proof (BSim_app_lambda (subst_comp (up_value_value σ') c) v') as HB2.
    refine (@CRel0_BSim_both B
      (app (lambda (subst_comp (up_value_value σ) c)) v)
      (subst_comp (scons v (@ids value VarInstance_value 0))
         (subst_comp (up_value_value σ) c))
      (subst_comp (scons v' (@ids value VarInstance_value 0))
         (subst_comp (up_value_value σ') c))
      (app (lambda (subst_comp (up_value_value σ') c)) v')
      _ _ _).
    + exact HB1.
    + rewrite (subst_comp_up_app c σ v). rewrite (subst_comp_up_app c σ' v').
      apply (IH (scons v σ) (scons v' σ')).
      intros i0; destruct i0 as [|i]; simpl; [apply HE|exact HV].
    + apply BSim_sym. exact HB2.
  - (* typeLetin *) intros m Γ c1 c2 A B H1 IH1 H2 IH2 σ σ' HE. simpl.
    eapply bind_letin_stack with (C:=B) (B:=B)
      (K:=cs_hole B) (K':=cs_hole B) (A:=A)
      (X:=subst_comp σ c1) (X':=subst_comp σ' c1)
      (Y:=subst_comp (up_value_value σ) c2)
      (Y':=subst_comp (up_value_value σ') c2).
    + apply sp_hole.
    + apply IH1. exact HE.
    + intros u u' HSu.
      rewrite (subst_comp_up_app0 c2 σ u). rewrite (subst_comp_up_app0 c2 σ' u').
      apply (IH2 (scons u σ) (scons u' σ')).
      intros i0; destruct i0 as [|i]; simpl; [apply HE|exact HSu].
  - (* typeRet *) intros m Γ v A H IH σ σ' HE. simpl.
    split.
    + intros w Hw. inversion Hw; subst.
      exists (subst_value σ' v). split; [apply bigstepReturn|apply IH; exact HE].
    + intros w Hw. inversion Hw; subst.
      exists (subst_value σ v). split; [apply bigstepReturn|apply IH; exact HE].
  - (* typeApp *) intros m Γ c v A B H1 IH1 H2 IH2 σ σ' HE. simpl.
    apply (IH1 σ σ' HE). apply IH2. exact HE.
  - (* typeTuple *) intros m Γ c1 c2 B1 B2 H1 IH1 H2 IH2 σ σ' HE. simpl.
    split.
    + eapply CRel0_BSim_both.
      * apply BSim_proj_tuple.
      * apply IH2. exact HE.
      * apply BSim_sym. apply BSim_proj_tuple.
    + eapply CRel0_BSim_both.
      * apply BSim_proj_tuple.
      * apply IH1. exact HE.
      * apply BSim_sym. apply BSim_proj_tuple.
  - (* typeProj *) intros m Γ b c B1 B2 H IH σ σ' HE. simpl.
    destruct b; simpl in *; [apply (proj2 (IH σ σ' HE))|apply (proj1 (IH σ σ' HE))].
  - (* typeForce *) intros m Γ v A H IH σ σ' HE. simpl.
    destruct (IH σ σ' HE) as (d & d' & E & E' & HR).
    rewrite E. rewrite E'.
    eapply CRel0_BSim_both.
    + apply BSim_force_thunk.
    + exact HR.
    + apply BSim_sym. apply BSim_force_thunk.
  - (* typeCaseZ *) intros m Γ v A H IH σ σ' HE. simpl.
    apply CRel0_no_bigstep; apply no_bigstep_caseZ.
  - (* typeCaseS *) intros m Γ v c1 c2 A1 A2 C Hv IHv H1 IH1 H2 IH2 σ σ' HE. simpl.
    eapply bind_caseS_stack with (C:=C) (Bres:=C)
      (K:=cs_hole C) (K':=cs_hole C)
      (A1:=A1) (A2:=A2)
      (V:=subst_value σ v) (V':=subst_value σ' v)
      (c1:=subst_comp (up_value_value σ) c1)
      (c1':=subst_comp (up_value_value σ') c1)
      (c2:=subst_comp (up_value_value σ) c2)
      (c2':=subst_comp (up_value_value σ') c2).
    + apply sp_hole.
    + exact (IHv σ σ' HE).
    + intros u u' HSu.
      rewrite (subst_comp_up_app0 c1 σ u). rewrite (subst_comp_up_app0 c1 σ' u').
      apply (IH1 (scons u σ) (scons u' σ')).
      intros i0; destruct i0 as [|i]; simpl; [apply HE|exact HSu].
    + intros u u' HSu.
      rewrite (subst_comp_up_app0 c2 σ u). rewrite (subst_comp_up_app0 c2 σ' u').
      apply (IH2 (scons u σ) (scons u' σ')).
      intros i0; destruct i0 as [|i]; simpl; [apply HE|exact HSu].
  - (* typeCaseP *) intros m Γ v c A B C Hv IHv H1 IH1 σ σ' HE. simpl.
    eapply bind_caseP_stack with (C:=C) (Bres:=C)
      (K:=cs_hole C) (K':=cs_hole C)
      (A1:=A) (A2:=B)
      (V:=subst_value σ v) (V':=subst_value σ' v)
      (c:=subst_comp (up_value_value (up_value_value σ)) c)
      (c':=subst_comp (up_value_value (up_value_value σ')) c).
    + apply sp_hole.
    + exact (IHv σ σ' HE).
    + intros v1 v2 v1' v2' HS1 HS2.
      rewrite (subst_comp_up_up_caseP0 c σ v1 v2).
      rewrite (subst_comp_up_up_caseP0 c σ' v1' v2').
      apply (IH1 (scons v2 (scons v1 σ)) (scons v2' (scons v1' σ'))).
      intros i0. destruct i0 as [i0'|].
      * destruct i0' as [i|].
        -- simpl. apply HE.
        -- simpl. exact HS1.
      * simpl. exact HS2.
Qed.

(* Administrative bigstep laws for primitive steps *)
Lemma BSim_letin_ret (v: value 0) (c2: comp 1) :
  BSim (letin (ret v) c2) (c2[v..]).
Proof.
  intros r. split; intro H.
  - apply bigstep_letin_inv in H as (u & Hu & Hc).
    inversion Hu; subst. exact Hc.
  - eapply bigstepLetin; [apply bigstepReturn|exact H].
Qed.

Lemma BSim_caseS_inj b (v: value 0) (c1 c2: comp 1) :
  BSim (caseS (inj b v) c1 c2) ((if b then c1 else c2)[v..]).
Proof.
  intros r. split; intro H.
  - apply bigstep_caseS_inv in H as (b0 & u & HV & Hc).
    injection HV as -> ->. exact Hc.
  - eapply bigstepCaseS. exact H.
Qed.

Lemma BSim_caseP_pair (v1 v2: value 0) (c: comp 2) :
  BSim (caseP (pair v1 v2) c) (c[scons v2 (scons v1 (@ids value VarInstance_value 0))]).
Proof.
  intros r. split; intro H.
  - apply bigstep_caseP_inv in H as (w1 & w2 & HV & Hc).
    injection HV as -> ->. exact Hc.
  - eapply bigstepCaseP. exact H.
Qed.

(* Substitution helpers for primitive-step commuting *)
Lemma subst_up_app_comp {m n} (c: comp (S m)) (σ: fin m -> value n) (v: value m) :
  (subst_comp (up_value_value σ) c)[(subst_value σ v)..]
  = (c[v..])[σ].
Proof.
  rewrite subst_comp_subst.
  rewrite subst_comp_subst.
  apply subst_comp_congr.
  intros i. destruct i as [i|].
  - rewrite (up_value_value_app σ (subst_value σ v) (Some i)). simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma subst_up_app_comp2 {m n} (c: comp (S (S m))) (σ: fin m -> value n)
  (v1 v2: value m) :
  (subst_comp (up_value_value (up_value_value σ)) c)
    [scons (subst_value σ v2) (scons (subst_value σ v1) (@ids value VarInstance_value n))]
  = (c[scons v2 (scons v1 (@ids value VarInstance_value m))])[σ].
Proof.
  rewrite subst_comp_subst.
  rewrite subst_comp_subst.
  apply subst_comp_congr.
  intros i. destruct i as [i|].
  - destruct i as [i|].
    + change (subst_value
                (scons (subst_value σ v2) (scons (subst_value σ v1)
                   (@ids value VarInstance_value n)))
                (up_value_value (up_value_value σ) (Some (Some i)))
              = subst_value σ (scons v2 (scons v1
                   (@ids value VarInstance_value m)) (Some (Some i)))).
      rewrite (up_up_value_value_caseP σ (subst_value σ v1) (subst_value σ v2) (Some (Some i))).
      simpl. reflexivity.
    + change (subst_value
                (scons (subst_value σ v2) (scons (subst_value σ v1)
                   (@ids value VarInstance_value n)))
                (up_value_value (up_value_value σ) (Some None))
              = subst_value σ (scons v2 (scons v1
                   (@ids value VarInstance_value m)) (Some None))).
      rewrite (up_up_value_value_caseP σ (subst_value σ v1) (subst_value σ v2) (Some None)).
      simpl. reflexivity.
  - change (subst_value
              (scons (subst_value σ v2) (scons (subst_value σ v1)
                 (@ids value VarInstance_value n)))
              (up_value_value (up_value_value σ) None)
            = subst_value σ (scons v2 (scons v1
                 (@ids value VarInstance_value m)) None)).
    simpl. reflexivity.
Qed.

(* Typing eliminators (Type-valued judgments, Prop-valued conclusions) *)
Lemma cty_ret_elim {m} {Γ: ctx m} {B: comptype} {v: value m}
  (H: Γ ⊢ ret v : B) (P: Prop)
  (k: forall (A: valtype), B = F A -> (Γ ⊩ v : A) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma cty_lambda_elim {m} {Γ: ctx m} {B: comptype} {c: comp (S m)}
  (H: Γ ⊢ lambda c : B) (P: Prop)
  (k: forall (A: valtype) (B0: comptype), B = arrow A B0 ->
      (A .: Γ ⊢ c : B0) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma cty_app_elim {m} {Γ: ctx m} {B: comptype} {c: comp m} {v: value m}
  (H: Γ ⊢ c v : B) (P: Prop)
  (k: forall (A: valtype), (Γ ⊢ c : arrow A B) -> (Γ ⊩ v : A) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma cty_tuple_elim {m} {Γ: ctx m} {B: comptype} {c1 c2: comp m}
  (H: Γ ⊢ tuple c1 c2 : B) (P: Prop)
  (k: forall (B1 B2: comptype), B = Pi B1 B2 ->
      (Γ ⊢ c1 : B1) -> (Γ ⊢ c2 : B2) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma cty_proj_elim {m} {Γ: ctx m} {B: comptype} {b: bool} {c: comp m}
  (H: Γ ⊢ proj b c : B) (P: Prop)
  (k: forall (B1 B2: comptype), (Γ ⊢ c : Pi B1 B2) ->
      B = (if b then B1 else B2) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma cty_letin_elim {m} {Γ: ctx m} {B: comptype} {c1: comp m} {c2: comp (S m)}
  (H: Γ ⊢ letin c1 c2 : B) (P: Prop)
  (k: forall (A: valtype), (Γ ⊢ c1 : F A) -> (A .: Γ ⊢ c2 : B) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma cty_force_elim {m} {Γ: ctx m} {B: comptype} {v: value m}
  (H: Γ ⊢ force v : B) (P: Prop)
  (k: (Γ ⊩ v : U B) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma cty_caseZ_elim {m} {Γ: ctx m} {B: comptype} {v: value m}
  (H: Γ ⊢ caseZ v : B) (P: Prop)
  (k: (Γ ⊩ v : zero) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma cty_caseS_elim {m} {Γ: ctx m} {B: comptype} {v: value m}
  {c1 c2: comp (S m)} (H: Γ ⊢ caseS v c1 c2 : B) (P: Prop)
  (k: forall (A1 A2: valtype), (Γ ⊩ v : Sigma A1 A2) ->
      (A1 .: Γ ⊢ c1 : B) -> (A2 .: Γ ⊢ c2 : B) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma cty_caseP_elim {m} {Γ: ctx m} {B: comptype} {v: value m}
  {c: comp (S (S m))} (H: Γ ⊢ caseP v c : B) (P: Prop)
  (k: forall (A1 A2: valtype), (Γ ⊩ v : A1 * A2) ->
      (A2 .: (A1 .: Γ) ⊢ c : B) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma vty_thunk_elim {m} {Γ: ctx m} {A: valtype} {c: comp m}
  (H: Γ ⊩ thunk c : A) (P: Prop)
  (k: forall (B: comptype), A = U B -> (Γ ⊢ c : B) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma vty_pair_elim {m} {Γ: ctx m} {A: valtype} {v1 v2: value m}
  (H: Γ ⊩ pair v1 v2 : A) (P: Prop)
  (k: forall (A1 A2: valtype), A = A1 * A2 ->
      (Γ ⊩ v1 : A1) -> (Γ ⊩ v2 : A2) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma vty_inj_elim {m} {Γ: ctx m} {A: valtype} {b: bool} {v: value m}
  (H: Γ ⊩ inj b v : A) (P: Prop)
  (k: forall (A1 A2: valtype), A = Sigma A1 A2 ->
      (Γ ⊩ v : (if b then A1 else A2)) -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Lemma vty_unit_elim {m} {Γ: ctx m} {A: valtype}
  (H: Γ ⊩ u : A) (P: Prop) (k: A = one -> P) : P.
Proof. inversion H; subst; eauto. Qed.

Definition fund_val (m:nat) (Γ:ctx m) (V:value m) (A:valtype)
  (H:Γ ⊩ V : A) : Pval m Γ V A H :=
  proj1 (@fundamental_value_comp m Γ) V A H.

Definition fund_comp (m:nat) (Γ:ctx m) (c:comp m) (B:comptype)
  (H:Γ ⊢ c : B) : Pcomp m Γ c B H :=
  proj2 (@fundamental_value_comp m Γ) c B H.
Arguments fund_val m Γ V A H : clear implicits.
Arguments fund_comp m Γ c B H : clear implicits.

Lemma subst_value_null (V: value 0) (σ: fin 0 -> value 0) :
  subst_value σ V = V.
Proof.
  transitivity (subst_value (@ids value VarInstance_value 0) V).
  - apply subst_value_congr. intros i. destruct i.
  - apply subst_value_id.
Qed.

Lemma subst_comp_null (c: comp 0) (σ: fin 0 -> value 0) :
  subst_comp σ c = c.
Proof.
  transitivity (subst_comp (@ids value VarInstance_value 0) c).
  - apply subst_comp_congr. intros i. destruct i.
  - apply subst_comp_id.
Qed.

Definition SVRel_typed (A:valtype) (V:value 0) (H: null ⊩ V : A) : SVRel A V V.
Proof.
  pose (c0 := (fun i : fin 0 => match i with end) : ctx 0).
  pose (e := (fun i : fin 0 => match i with end) : fin 0 -> value 0).
  pose proof (@fund_val 0 c0 V A H
    e e (fun i : fin 0 => match i with end)) as Hf.
  refine (eq_ind (subst_value e V)
            (fun x => SVRel A V x) _ V (subst_value_null V e)).
  refine (eq_ind (subst_value e V)
            (fun x => SVRel A x (subst_value e V)) _ V (subst_value_null V e)).
  exact Hf.
Qed.

(* Unfolding helpers for the closed value relation at U *)
Lemma SVRel_U_inv A (V W: value 0) :
  SVRel (U A) V W -> exists c c', V = thunk c /\ W = thunk c' /\ CRel0 A c c'.
Proof. simpl. intros H. exact H. Qed.

Lemma subst_comp_vcons {m n} (c: comp (S m)) (v: value m) (σ: fin m -> value n) :
  (c[v..])[σ] = c[scons (subst_value σ v) σ].
Proof.
  rewrite subst_comp_subst.
  apply subst_comp_congr. intros i. destruct i as [i|]; simpl; reflexivity.
Qed.

Lemma subst_comp_vcons2 {m n} (c: comp (S (S m))) (v1 v2: value m)
  (σ: fin m -> value n) :
  (c[scons v2 (scons v1 (@ids value VarInstance_value m))])[σ]
  = c[scons (subst_value σ v2) (scons (subst_value σ v1) σ)].
Proof.
  rewrite subst_comp_subst.
  apply subst_comp_congr. intros i.
  destruct i as [i|]; [destruct i as [i|]|]; simpl; reflexivity.
Qed.

Lemma subst_comp_vcons_raw {m n} (c: comp (S m)) (v: value m) (σ: fin m -> value n) :
  subst_comp σ (c[v..]) = subst_comp (scons (subst_value σ v) σ) c.
Proof.
  change (subst_comp σ (subst_comp (scons v (@ids value VarInstance_value m)) c)
          = subst_comp (scons (subst_value σ v) σ) c).
  rewrite subst_comp_subst.
  apply subst_comp_congr. intros i; destruct i as [i|]; simpl; reflexivity.
Qed.

Lemma subst_comp_vcons2_raw {m n} (c: comp (S (S m))) (v1 v2: value m)
  (σ: fin m -> value n) :
  subst_comp σ (c[scons v2 (scons v1 (@ids value VarInstance_value m))])
  = subst_comp (scons (subst_value σ v2) (scons (subst_value σ v1) σ)) c.
Proof.
  change (subst_comp σ (subst_comp (scons v2 (scons v1 (@ids value VarInstance_value m))) c)
          = subst_comp (scons (subst_value σ v2) (scons (subst_value σ v1) σ)) c).
  rewrite subst_comp_subst.
  apply subst_comp_congr. intros i.
  destruct i as [i|]; [destruct i as [i|]|]; simpl; reflexivity.
Qed.

(* pstep soundness against the closed logical relation, for all substitutions *)
Lemma pstep_env : forall n (c c': comp n), pstep c c' ->
  forall (Γ: ctx n) B (Hc: Γ ⊢ c : B)
         (σ σ': fin n -> value 0), EnvRel Γ σ σ' ->
  CRel0 B (subst_comp σ c) (subst_comp σ' c').
Proof.
  intros n c c' Hp. induction Hp as
    [c0 | c0 c' v E | b c c1 c2 E | c0 c' v E | v b c c1 c2 E | v1 v2 c c' E];
    intros Γ B Hc σ σ' HE.
  - (* pstepForce *)
    simpl.
    eapply cty_force_elim; [exact Hc|]. intros Hv.
    eapply vty_thunk_elim; [exact Hv|]. intros B' HB Hc0.
    injection HB as HB. subst B'.
    eapply CRel0_BSim_left.
    + apply BSim_force_thunk.
    + apply (fund_comp n Γ c0 B Hc0 σ σ' HE).
  - (* pstepApp *)
    rewrite <- E.
    simpl.
    eapply cty_app_elim; [exact Hc|]. intros A Hlam Hv.
    eapply cty_lambda_elim; [exact Hlam|]. intros A0 B0 HB Hc0.
    injection HB as HA HB. subst A0. subst B0.
    pose proof (BSim_app_lambda (subst_comp (up_value_value σ) c0) (subst_value σ v)) as HB1.
    rewrite subst_up_app_comp in HB1. rewrite subst_comp_vcons in HB1.
    (* Right side: (c0[v..])[σ'] = c0[scons (v[σ']) σ'] *)
    rewrite (subst_comp_vcons_raw c0 v σ').
    eapply CRel0_BSim_left.
    + exact HB1.
    + apply (fund_comp (S n) (_ .: Γ) c0 B Hc0
             (scons (subst_value σ v) σ) (scons (subst_value σ' v) σ')).
      intros i0. destruct i0 as [|i].
      * simpl. apply HE.
      * simpl. apply (fund_val n Γ v _ Hv σ σ' HE).
  - (* pstepProj *)
    subst c. simpl.
    eapply cty_proj_elim; [exact Hc|]. intros B1 B2 Hcp HB.
    eapply cty_tuple_elim; [exact Hcp|]. intros C1 C2 Ht Hc1 Hc2.
    injection Ht as HC1 HC2. subst C1. subst C2. subst B.
    destruct b; simpl in *.
    + eapply CRel0_BSim_left.
      * apply BSim_proj_tuple.
      * apply (fund_comp n Γ c1 B1 Hc1 σ σ' HE).
    + eapply CRel0_BSim_left.
      * apply BSim_proj_tuple.
      * apply (fund_comp n Γ c2 B2 Hc2 σ σ' HE).
  - (* pstepLetin *)
    rewrite <- E.
    simpl.
    eapply cty_letin_elim; [exact Hc|]. intros A Hc1 Hc2.
    eapply cty_ret_elim; [exact Hc1|]. intros A0 HB Hv.
    injection HB as HA. subst.
    pose proof (BSim_letin_ret (subst_value σ v) (subst_comp (up_value_value σ) c0)) as HB1.
    rewrite subst_up_app_comp in HB1. rewrite subst_comp_vcons in HB1.
    rewrite (subst_comp_vcons_raw c0 v σ').
    eapply CRel0_BSim_left.
    + exact HB1.
    + apply (fund_comp (S n) (_ .: Γ) c0 B Hc2
             (scons (subst_value σ v) σ) (scons (subst_value σ' v) σ')).
      intros i0. destruct i0 as [|i].
      * simpl. apply HE.
      * simpl. apply (fund_val n Γ v _ Hv σ σ' HE).
  - (* pstepCaseS *)
    rewrite <- E.
    simpl.
    eapply cty_caseS_elim; [exact Hc|]. intros A1 A2 Hv Hc1 Hc2.
    eapply vty_inj_elim; [exact Hv|]. intros D1 D2 HA Hv0.
    injection HA as HA1 HA2. subst D1. subst D2.
    destruct b; simpl in *.
    + pose proof (BSim_caseS_inj true (subst_value σ v) (subst_comp (up_value_value σ) c1) (subst_comp (up_value_value σ) c2)) as HB1.
      simpl in HB1. rewrite subst_up_app_comp in HB1. rewrite subst_comp_vcons in HB1.
      rewrite (subst_comp_vcons_raw c1 v σ').
      eapply CRel0_BSim_left.
      * exact HB1.
      * apply (fund_comp (S n) (_ .: Γ) c1 B Hc1
               (scons (subst_value σ v) σ) (scons (subst_value σ' v) σ')).
        intros i0. destruct i0 as [|i].
        -- simpl. apply HE.
        -- simpl. apply (fund_val n Γ v _ Hv0 σ σ' HE).
    + pose proof (BSim_caseS_inj false (subst_value σ v) (subst_comp (up_value_value σ) c1) (subst_comp (up_value_value σ) c2)) as HB1.
      simpl in HB1. rewrite subst_up_app_comp in HB1. rewrite subst_comp_vcons in HB1.
      rewrite (subst_comp_vcons_raw c2 v σ').
      eapply CRel0_BSim_left.
      * exact HB1.
      * apply (fund_comp (S n) (_ .: Γ) c2 B Hc2
               (scons (subst_value σ v) σ) (scons (subst_value σ' v) σ')).
        intros i0. destruct i0 as [|i].
        -- simpl. apply HE.
        -- simpl. apply (fund_val n Γ v _ Hv0 σ σ' HE).
  - (* pstepCaseP *)
    rewrite <- E.
    simpl.
    eapply cty_caseP_elim; [exact Hc|]. intros A1 A2 Hv Hc0.
    eapply vty_pair_elim; [exact Hv|]. intros D1 D2 HA Hv1 Hv2.
    injection HA as HA1 HA2. subst D1. subst D2.
    pose proof (BSim_caseP_pair (subst_value σ v1) (subst_value σ v2)
                  (subst_comp (up_value_value (up_value_value σ)) c)) as HB1.
    rewrite subst_up_app_comp2 in HB1. rewrite subst_comp_vcons2 in HB1.
    rewrite (subst_comp_vcons2_raw c v1 v2 σ').
    eapply CRel0_BSim_left.
    + exact HB1.
    + apply (fund_comp (S (S n)) (_ .: (_ .: Γ)) c B Hc0
             (scons (subst_value σ v2) (scons (subst_value σ v1) σ))
             (scons (subst_value σ' v2) (scons (subst_value σ' v1) σ'))).
      intros i0. destruct i0 as [i0'|].
      * destruct i0' as [i|].
        -- simpl. apply HE.
        -- simpl. apply (fund_val n Γ v1 _ Hv1 σ σ' HE).
      * simpl. apply (fund_val n Γ v2 _ Hv2 σ σ' HE).
Qed.




Lemma subst_comp_up_app_nt {m n} (c: comp (S m)) (σ: fin m -> value n)
  (v: value n) :
  (subst_comp (up_value_value σ) c)[v..] = subst_comp (scons v σ) c.
Proof.
  change (subst_comp (scons v (@ids value VarInstance_value n))
            (subst_comp (up_value_value σ) c) = subst_comp (scons v σ) c).
  apply subst_comp_up_app.
Qed.

Definition Scomp (n:nat) (c c': comp n) (s: c ↪ c') : Prop :=
  forall (Γ: ctx n) B (Hc: Γ ⊢ c : B) (σ σ': fin n -> value 0),
    EnvRel Γ σ σ' -> CRel0 B (subst_comp σ c) (subst_comp σ' c').

Definition Sval (n:nat) (v v': value n) (s: v ↪ᵥ v') : Prop :=
  forall (Γ: ctx n) A (Hv: Γ ⊩ v : A) (σ σ': fin n -> value 0),
    EnvRel Γ σ σ' -> SVRel A (subst_value σ v) (subst_value σ' v').
Arguments Scomp n c c' s : clear implicits.
Arguments Sval n v v' s : clear implicits.

Lemma sstep_env_all : forall n,
  (forall (c c': comp n) (s: c ↪ c'), Scomp n c c' s) /\
  (forall (v v': value n) (s: v ↪ᵥ v'), Sval n v v' s).
Proof.
  apply (mutind_sstep Sval Scomp).
  - (* sstepValuePairL *) intros n v1 v1' v2 s IH.
    intros Γ A Hv σ σ' HE.
    eapply vty_pair_elim; [exact Hv|]. intros A1 A2 HA H1 H2. subst A.
    simpl. eexists (subst_value σ v1), (subst_value σ v2),
                  (subst_value σ' v1'), (subst_value σ' v2).
    split. reflexivity. split. reflexivity. split.
    + apply (IH Γ A1 H1 σ σ' HE).
    + apply (fund_val n Γ v2 A2 H2 σ σ' HE).
  - (* sstepValuePairR *) intros n v1 v2 v2' s IH.
    intros Γ A Hv σ σ' HE.
    eapply vty_pair_elim; [exact Hv|]. intros A1 A2 HA H1 H2. subst A.
    simpl. eexists (subst_value σ v1), (subst_value σ v2),
                  (subst_value σ' v1), (subst_value σ' v2').
    split. reflexivity. split. reflexivity. split.
    + apply (fund_val n Γ v1 A1 H1 σ σ' HE).
    + apply (IH Γ A2 H2 σ σ' HE).
  - (* sstepValueInj *) intros n b v v' s IH.
    intros Γ A Hv σ σ' HE.
    eapply vty_inj_elim; [exact Hv|]. intros A1 A2 HA H1. subst A.
    simpl. eexists b, (subst_value σ v), (subst_value σ' v').
    split. reflexivity. split. reflexivity.
    destruct b; simpl in *; apply (IH Γ _ H1 σ σ' HE).
  - (* sstepValueThunk *) intros n c c' s IH.
    intros Γ A Hv σ σ' HE.
    eapply vty_thunk_elim; [exact Hv|]. intros B HB Hc. subst A.
    simpl. eexists (subst_comp σ c), (subst_comp σ' c').
    split. reflexivity. split. reflexivity.
    apply (IH Γ B Hc σ σ' HE).
  - (* sstepForce *) intros n v v' s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_force_elim; [exact Hc|]. intros Hv.
    simpl.
    destruct (IH Γ (U B) Hv σ σ' HE) as (d & d' & E & E' & HR).
    rewrite E. rewrite E'.
    eapply CRel0_BSim_both.
    + apply BSim_force_thunk.
    + exact HR.
    + apply BSim_sym. apply BSim_force_thunk.
  - (* sstepLambda *) intros n c c' s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_lambda_elim; [exact Hc|]. intros A B0 HB Hc0. subst B.
    simpl. intros v v' HV.
    pose proof (BSim_app_lambda (subst_comp (up_value_value σ) c) v) as HB1.
    rewrite (subst_comp_up_app_nt c σ v) in HB1.
    pose proof (BSim_app_lambda (subst_comp (up_value_value σ') c') v') as HB2.
    rewrite (subst_comp_up_app_nt c' σ' v') in HB2.
    eapply CRel0_BSim_both.
    + exact HB1.
    + apply (IH (A .: Γ) B0 Hc0 (scons v σ) (scons v' σ')).
      intros i0. destruct i0 as [|i].
      * simpl. apply HE.
      * simpl. exact HV.
    + apply BSim_sym. exact HB2.
  - (* sstepAppL *) intros n c c' v s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_app_elim; [exact Hc|]. intros A Hlam Hv.
    simpl.
    apply (IH Γ (arrow A B) Hlam σ σ' HE).
    apply (fund_val n Γ v A Hv σ σ' HE).
  - (* sstepAppR *) intros n c v v' s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_app_elim; [exact Hc|]. intros A Hlam Hv.
    simpl.
    apply (fund_comp n Γ c (arrow A B) Hlam σ σ' HE).
    apply (IH Γ A Hv σ σ' HE).
  - (* sstepTupleL *) intros n c1 c1' c2 s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_tuple_elim; [exact Hc|]. intros B1 B2 HB H1 H2. subst B.
    simpl. split.
    + eapply CRel0_BSim_both.
      * apply BSim_proj_tuple.
      * apply (fund_comp n Γ c2 B2 H2 σ σ' HE).
      * apply BSim_sym. apply BSim_proj_tuple.
    + eapply CRel0_BSim_both.
      * apply BSim_proj_tuple.
      * apply (IH Γ B1 H1 σ σ' HE).
      * apply BSim_sym. apply BSim_proj_tuple.
  - (* sstepTupleR *) intros n c1 c2 c2' s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_tuple_elim; [exact Hc|]. intros B1 B2 HB H1 H2. subst B.
    simpl. split.
    + eapply CRel0_BSim_both.
      * apply BSim_proj_tuple.
      * apply (IH Γ B2 H2 σ σ' HE).
      * apply BSim_sym. apply BSim_proj_tuple.
    + eapply CRel0_BSim_both.
      * apply BSim_proj_tuple.
      * apply (fund_comp n Γ c1 B1 H1 σ σ' HE).
      * apply BSim_sym. apply BSim_proj_tuple.
  - (* sstepRet *) intros n v v' s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_ret_elim; [exact Hc|]. intros A HB Hv. subst B.
    simpl. split.
    + intros w Hw. inversion Hw; subst.
      exists (subst_value σ' v'). split; [apply bigstepReturn|].
      apply (IH Γ A Hv σ σ' HE).
    + intros w Hw. inversion Hw; subst.
      exists (subst_value σ v). split; [apply bigstepReturn|].
      apply (IH Γ A Hv σ σ' HE).
  - (* sstepLetinL *) intros n c1 c1' c2 s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_letin_elim; [exact Hc|]. intros A H1 H2.
    simpl.
    eapply bind_letin_stack with (C:=B) (B:=B) (K:=cs_hole B) (K':=cs_hole B)
      (A:=A) (X:=subst_comp σ c1) (X':=subst_comp σ' c1')
      (Y:=subst_comp (up_value_value σ) c2) (Y':=subst_comp (up_value_value σ') c2).
    + apply sp_hole.
    + apply (IH Γ (F A) H1 σ σ' HE).
    + intros u u' HSu.
      rewrite (subst_comp_up_app0 c2 σ u). rewrite (subst_comp_up_app0 c2 σ' u').
      apply (fund_comp (S n) (A .: Γ) c2 B H2 (scons u σ) (scons u' σ')).
      intros i0. destruct i0 as [|i].
      * simpl. apply HE.
      * simpl. exact HSu.
  - (* sstepLetinR *) intros n c1 c2 c2' s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_letin_elim; [exact Hc|]. intros A H1 H2.
    simpl.
    eapply bind_letin_stack with (C:=B) (B:=B) (K:=cs_hole B) (K':=cs_hole B)
      (A:=A) (X:=subst_comp σ c1) (X':=subst_comp σ' c1)
      (Y:=subst_comp (up_value_value σ) c2) (Y':=subst_comp (up_value_value σ') c2').
    + apply sp_hole.
    + apply (fund_comp n Γ c1 (F A) H1 σ σ' HE).
    + intros u u' HSu.
      rewrite (subst_comp_up_app0 c2 σ u). rewrite (subst_comp_up_app0 c2' σ' u').
      apply (IH (A .: Γ) B H2 (scons u σ) (scons u' σ')).
      intros i0. destruct i0 as [|i].
      * simpl. apply HE.
      * simpl. exact HSu.
  - (* sstepProj *) intros n c c' b s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_proj_elim; [exact Hc|]. intros B1 B2 Hcp HB.
    simpl. destruct b; simpl in *; rewrite HB.
    + apply (proj2 ((IH Γ (Pi B1 B2) Hcp σ σ' HE))).
    + apply (proj1 ((IH Γ (Pi B1 B2) Hcp σ σ' HE))).
  - (* sstepCaseZ *) intros n v v' s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_caseZ_elim; [exact Hc|]. intros Hv.
    simpl. apply CRel0_no_bigstep; apply no_bigstep_caseZ.
  - (* sstepCaseSV *) intros n v v' c1 c2 s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_caseS_elim; [exact Hc|]. intros A1 A2 Hv H1 H2.
    simpl.
    eapply bind_caseS_stack with (C:=B) (Bres:=B) (K:=cs_hole B) (K':=cs_hole B)
      (A1:=A1) (A2:=A2) (V:=subst_value σ v) (V':=subst_value σ' v')
      (c1:=subst_comp (up_value_value σ) c1) (c1':=subst_comp (up_value_value σ') c1)
      (c2:=subst_comp (up_value_value σ) c2) (c2':=subst_comp (up_value_value σ') c2).
    + apply sp_hole.
    + apply (IH Γ (Sigma A1 A2) Hv σ σ' HE).
    + intros u u' HSu.
      rewrite (subst_comp_up_app0 c1 σ u). rewrite (subst_comp_up_app0 c1 σ' u').
      apply (fund_comp (S n) (A1 .: Γ) c1 B H1 (scons u σ) (scons u' σ')).
      intros i0. destruct i0 as [|i]; simpl; [apply HE|exact HSu].
    + intros u u' HSu.
      rewrite (subst_comp_up_app0 c2 σ u). rewrite (subst_comp_up_app0 c2 σ' u').
      apply (fund_comp (S n) (A2 .: Γ) c2 B H2 (scons u σ) (scons u' σ')).
      intros i0. destruct i0 as [|i]; simpl; [apply HE|exact HSu].
  - (* sstepCaseSL *) intros n v c1 c1' c2 s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_caseS_elim; [exact Hc|]. intros A1 A2 Hv H1 H2.
    simpl.
    eapply bind_caseS_stack with (C:=B) (Bres:=B) (K:=cs_hole B) (K':=cs_hole B)
      (A1:=A1) (A2:=A2) (V:=subst_value σ v) (V':=subst_value σ' v)
      (c1:=subst_comp (up_value_value σ) c1) (c1':=subst_comp (up_value_value σ') c1')
      (c2:=subst_comp (up_value_value σ) c2) (c2':=subst_comp (up_value_value σ') c2).
    + apply sp_hole.
    + apply (fund_val n Γ v (Sigma A1 A2) Hv σ σ' HE).
    + intros u u' HSu.
      rewrite (subst_comp_up_app0 c1 σ u). rewrite (subst_comp_up_app0 c1' σ' u').
      apply (IH (A1 .: Γ) B H1 (scons u σ) (scons u' σ')).
      intros i0. destruct i0 as [|i]; simpl; [apply HE|exact HSu].
    + intros u u' HSu.
      rewrite (subst_comp_up_app0 c2 σ u). rewrite (subst_comp_up_app0 c2 σ' u').
      apply (fund_comp (S n) (A2 .: Γ) c2 B H2 (scons u σ) (scons u' σ')).
      intros i0. destruct i0 as [|i]; simpl; [apply HE|exact HSu].
  - (* sstepCaseSR *) intros n v c1 c2 c2' s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_caseS_elim; [exact Hc|]. intros A1 A2 Hv H1 H2.
    simpl.
    eapply bind_caseS_stack with (C:=B) (Bres:=B) (K:=cs_hole B) (K':=cs_hole B)
      (A1:=A1) (A2:=A2) (V:=subst_value σ v) (V':=subst_value σ' v)
      (c1:=subst_comp (up_value_value σ) c1) (c1':=subst_comp (up_value_value σ') c1)
      (c2:=subst_comp (up_value_value σ) c2) (c2':=subst_comp (up_value_value σ') c2').
    + apply sp_hole.
    + apply (fund_val n Γ v (Sigma A1 A2) Hv σ σ' HE).
    + intros u u' HSu.
      rewrite (subst_comp_up_app0 c1 σ u). rewrite (subst_comp_up_app0 c1 σ' u').
      apply (fund_comp (S n) (A1 .: Γ) c1 B H1 (scons u σ) (scons u' σ')).
      intros i0. destruct i0 as [|i]; simpl; [apply HE|exact HSu].
    + intros u u' HSu.
      rewrite (subst_comp_up_app0 c2 σ u). rewrite (subst_comp_up_app0 c2' σ' u').
      apply (IH (A2 .: Γ) B H2 (scons u σ) (scons u' σ')).
      intros i0. destruct i0 as [|i]; simpl; [apply HE|exact HSu].
  - (* sstepCasePV *) intros n v v' c s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_caseP_elim; [exact Hc|]. intros A1 A2 Hv H1.
    simpl.
    eapply bind_caseP_stack with (C:=B) (Bres:=B) (K:=cs_hole B) (K':=cs_hole B)
      (A1:=A1) (A2:=A2) (V:=subst_value σ v) (V':=subst_value σ' v')
      (c:=subst_comp (up_value_value (up_value_value σ)) c)
      (c':=subst_comp (up_value_value (up_value_value σ')) c).
    + apply sp_hole.
    + apply (IH Γ (A1 * A2) Hv σ σ' HE).
    + intros v1 v2 v1' v2' HS1 HS2.
      rewrite (subst_comp_up_up_caseP0 c σ v1 v2).
      rewrite (subst_comp_up_up_caseP0 c σ' v1' v2').
      apply (fund_comp (S (S n)) (A2 .: (A1 .: Γ)) c B H1
        (scons v2 (scons v1 σ)) (scons v2' (scons v1' σ'))).
      intros i0. destruct i0 as [i0'|].
      * destruct i0' as [i|].
        -- simpl. apply HE.
        -- simpl. exact HS1.
      * simpl. exact HS2.
  - (* sstepCasePC *) intros n v c c' s IH.
    intros Γ B Hc σ σ' HE.
    eapply cty_caseP_elim; [exact Hc|]. intros A1 A2 Hv H1.
    simpl.
    eapply bind_caseP_stack with (C:=B) (Bres:=B) (K:=cs_hole B) (K':=cs_hole B)
      (A1:=A1) (A2:=A2) (V:=subst_value σ v) (V':=subst_value σ' v)
      (c:=subst_comp (up_value_value (up_value_value σ)) c)
      (c':=subst_comp (up_value_value (up_value_value σ')) c').
    + apply sp_hole.
    + apply (fund_val n Γ v (A1 * A2) Hv σ σ' HE).
    + intros v1 v2 v1' v2' HS1 HS2.
      rewrite (subst_comp_up_up_caseP0 c σ v1 v2).
      rewrite (subst_comp_up_up_caseP0 c' σ' v1' v2').
      apply (IH (A2 .: (A1 .: Γ)) B H1
        (scons v2 (scons v1 σ)) (scons v2' (scons v1' σ'))).
      intros i0. destruct i0 as [i0'|].
      * destruct i0' as [i|].
        -- simpl. apply HE.
        -- simpl. exact HS1.
      * simpl. exact HS2.
  - (* sstepPrimitive *) intros n c c' p.
    intros Γ B Hc σ σ' HE.
    exact (@pstep_env n c c' p Γ B Hc σ σ' HE).
Qed.

Lemma BSim_letin (c1 c1': comp 0) (c2: comp 1) :
  (forall r, c1 ▷ r <-> c1' ▷ r) -> BSim (letin c1 c2) (letin c1' c2).
Proof.
  intros HB r. split; intro H.
  - apply bigstep_letin_inv in H as (u & Hu & Hc).
    eapply bigstepLetin.
    + apply HB. exact Hu.
    + exact Hc.
  - apply bigstep_letin_inv in H as (u & Hu & Hc).
    eapply bigstepLetin.
    + apply (proj2 (HB (ret u))). exact Hu.
    + exact Hc.
Qed.

Lemma pstep_BSim : forall (c c': comp 0), pstep c c' -> BSim c c'.
Proof.
  intros c c' Hp. induction Hp as
    [c0 | c0 c' v E | b c c1 c2 E | c0 c' v E | v b c c1 c2 E | v1 v2 c c' E].
  - apply BSim_force_thunk.
  - rewrite <- E. apply BSim_app_lambda.
  - rewrite E. apply BSim_proj_tuple.
  - rewrite <- E. apply BSim_letin_ret.
  - rewrite <- E. destruct b; simpl; apply BSim_caseS_inj.
  - rewrite <- E. apply BSim_caseP_pair.
Qed.

Lemma step_BSim : forall (c c': comp 0), step c c' -> BSim c c'.
Proof.
  intros c c' H. induction H.
  - eapply pstep_BSim. eassumption.
  - apply BSim_app. exact IHstep.
  - apply BSim_proj. exact IHstep.
  - apply BSim_letin. exact IHstep.
Qed.

Lemma star_trans_g {X: Type} {R: X -> X -> Prop} :
  forall x y z, star R x y -> star R y z -> star R x z.
Proof.
  intros x y z H. induction H as [x|x x' y' Hs Hst IH]; intros H2.
  - exact H2.
  - eapply starStep; [exact Hs|apply IH; exact H2].
Qed.

Lemma star_step_app {n} : forall (c c': comp n) v,
  star step c c' -> star step (c v) (c' v).
Proof.
  intros c c' v H. induction H as [c|c c' c'' Hs Hst IH].
  - apply starRefl.
  - eapply starStep with (x' := c' v).
    + apply stepApp. exact Hs.
    + exact IH.
Qed.

Lemma star_step_proj {n} b : forall (c c': comp n),
  star step c c' -> star step (proj b c) (proj b c').
Proof.
  intros c c' H. induction H as [c|c c' c'' Hs Hst IH].
  - apply starRefl.
  - eapply starStep with (x' := proj b c').
    + apply stepProj. exact Hs.
    + exact IH.
Qed.

Lemma star_step_letin {n} : forall (c c': comp n) c2,
  star step c c' -> star step (letin c c2) (letin c' c2).
Proof.
  intros c c' c2 H. induction H as [c|c c' c'' Hs Hst IH].
  - apply starRefl.
  - eapply starStep with (x' := letin c' c2).
    + apply stepLetin. exact Hs.
    + exact IH.
Qed.

Lemma bigstep_to_star : forall (c c': comp 0), c ▷ c' -> star step c c'.
Proof.
  intros c c' H. induction H.
  - apply starRefl.
  - apply starRefl.
  - apply starRefl.
  - apply starRefl.
  - eapply starStep.
    + apply stepPrimitive. apply pstepForce.
    + exact IHbigstep.
  - eapply star_trans_g.
    + eapply star_step_app. exact IHbigstep1.
    + eapply starStep.
      * apply stepPrimitive. apply pstepApp. reflexivity.
      * exact IHbigstep2.
  - eapply star_trans_g.
    + eapply star_step_proj. exact IHbigstep1.
    + eapply starStep.
      * apply stepPrimitive. apply pstepProj. reflexivity.
      * exact IHbigstep2.
  - eapply star_trans_g.
    + eapply star_step_letin. exact IHbigstep1.
    + eapply starStep.
      * apply stepPrimitive. apply pstepLetin. reflexivity.
      * exact IHbigstep2.
  - eapply starStep.
    + apply stepPrimitive. apply pstepCaseS. reflexivity.
    + exact IHbigstep.
  - eapply starStep.
    + apply stepPrimitive. apply pstepCaseP. reflexivity.
    + exact IHbigstep.
Qed.

Lemma star_to_bigstep_ret : forall (c d: comp 0), star step c d ->
  forall v, d = ret v -> c ▷ ret v.
Proof.
  intros c d H. induction H as [c|c c' d Hs Hst IH]; intros v Ed.
  - rewrite Ed. apply bigstepReturn.
  - apply (proj2 (step_BSim Hs (ret v))). apply IH. exact Ed.
Qed.

Lemma star_ret_bigstep : forall (c: comp 0) v, c >* ret v <-> c ▷ ret v.
Proof.
  intros c v. split; intro H.
  - exact (@star_to_bigstep_ret c (ret v) H v eq_refl).
  - apply bigstep_to_star. exact H.
Qed.

(* Ground-value relation is syntactic equality, hence observations agree. *)
Fixpoint SVRel_ground_eq (G: groundtype) : forall (V W: value 0),
  SVRel (to_valtype G) V W -> V = W.
Proof.
  destruct G as [|G1 G2|G1 G2]; simpl.
  - intros V W H. exact H.
  - intros V W (b & v & w & EV & EW & H).
    subst V. subst W. f_equal.
    destruct b; [apply (SVRel_ground_eq G1)|apply (SVRel_ground_eq G2)]; exact H.
  - intros V W (v1 & v2 & w1 & w2 & EV & EW & H1 & H2).
    subst V. subst W. f_equal.
    + apply (SVRel_ground_eq G1). exact H1.
    + apply (SVRel_ground_eq G2). exact H2.
Qed.

Definition Raw_star (c c': comp 0) : Prop :=
  forall v, c >* ret v <-> c' >* ret v.

Lemma Raw_star_refl c : Raw_star c c.
Proof. intros v. reflexivity. Qed.

Lemma Raw_star_sym c c' : Raw_star c c' -> Raw_star c' c.
Proof. intros H v. symmetry. apply H. Qed.

Lemma Raw_star_trans c c' c'' : Raw_star c c' -> Raw_star c' c'' -> Raw_star c c''.
Proof. intros H1 H2 v. transitivity (c' >* ret v); [apply H1|apply H2]. Qed.

Lemma CRel0_F_ground_raw_star (G: groundtype) (c c': comp 0) :
  CRel0 (F (to_valtype G)) c c' -> Raw_star c c'.
Proof.
  intros (H1 & H2) v. split; intro Hv.
  - apply star_ret_bigstep in Hv.
    destruct (H1 v Hv) as (v' & Hv' & HV).
    apply star_ret_bigstep.
    rewrite (SVRel_ground_eq G v v' HV). exact Hv'.
  - apply star_ret_bigstep in Hv.
    destruct (H2 v Hv) as (v' & Hv' & HV).
    apply star_ret_bigstep.
    rewrite (symmetry (SVRel_ground_eq G v' v HV)). exact Hv'.
Qed.

(* CRel0 at ground-return type gives star-step observation equivalence *)
Lemma CRel0_F_ground_obs (G: groundtype) (c c': comp 0) :
  CRel0 (F (to_valtype G)) c c' -> forall v, c >* ret v <-> c' >* ret v.
Proof.
  intros H. apply CRel0_F_ground_raw_star in H. exact H.
Qed.

Set Implicit Arguments.
Require Import CBPV.ObservationalEquivalence CBPV.StrongReduction CBPV.AbstractReductionSystems.
Import CommaNotation.
Typeclasses Transparent Subst_comp Subst_value.

(* ------------------------------------------------------------------ *)
(* Lifting a typed renaming to a context cons                          *)
(* ------------------------------------------------------------------ *)

Lemma up_lift_eq {m n} (Γ: ctx n) (Δ: ctx m) (ξ: fin m -> fin n)
  (Hξ: forall i, Δ i = Γ (ξ i)) (A: valtype) :
  forall (i : fin (S m)), (A .: Δ) i = (A .: Γ) (up_ren ξ i).
Proof.
  intros i. destruct i as [i|]; simpl.
  - change (Δ i = Γ (ξ i)). apply Hξ.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Typed renaming                                                     *)
(* ------------------------------------------------------------------ *)

Fixpoint ren_value_typing (m n : nat) (Γ: ctx n) (Δ: ctx m) (ξ: fin m -> fin n)
  (Hξ: forall i, Δ i = Γ (ξ i)) (v: value m) (A: valtype)
  (H: Δ ⊩ v : A) {struct H} : Γ ⊩ ren_value ξ v : A
with ren_comp_typing (m n : nat) (Γ: ctx n) (Δ: ctx m) (ξ: fin m -> fin n)
  (Hξ: forall i, Δ i = Γ (ξ i)) (c: comp m) (B: comptype)
  (H: Δ ⊢ c : B) {struct H} : Γ ⊢ ren_comp ξ c : B.
Proof.
  - (* value *) simpl.
    destruct H; simpl.
    + (* typeVar *)
      exact (match eq_sym (Hξ i) in (_ = T') return (Γ ⊩ var_value (ξ i) : T') with
             | eq_refl => @typeVar _ Γ (ξ i)
             end).
    + apply typeUnit.
    + apply typePair.
      * eapply (@ren_value_typing m n Γ Δ ξ Hξ). eassumption.
      * eapply (@ren_value_typing m n Γ Δ ξ Hξ). eassumption.
    + apply typeSum.
      eapply (@ren_value_typing m n Γ Δ ξ Hξ). eassumption.
    + apply typeThunk.
      eapply (@ren_comp_typing m n Γ Δ ξ Hξ). eassumption.
  - (* comp *) simpl.
    destruct H; simpl.
    + (* typeCone *) apply typeCone.
    + (* typeLambda *) apply typeLambda.
      eapply (@ren_comp_typing (S m) (S n) (A .: Γ) (A .: Δ) (up_ren ξ)
                                 (up_lift_eq Γ Δ ξ Hξ A)).
      eassumption.
    + (* typeLetin *) eapply typeLetin.
      * eapply (@ren_comp_typing m n Γ Δ ξ Hξ). eassumption.
      * eapply (@ren_comp_typing (S m) (S n) (A .: Γ) (A .: Δ) (up_ren ξ)
                                   (up_lift_eq Γ Δ ξ Hξ A)).
        eassumption.
    + (* typeRet *) apply typeRet.
      eapply (@ren_value_typing m n Γ Δ ξ Hξ). eassumption.
    + (* typeApp *) eapply typeApp.
      * eapply (@ren_comp_typing m n Γ Δ ξ Hξ). eassumption.
      * eapply (@ren_value_typing m n Γ Δ ξ Hξ). eassumption.
    + (* typeTuple *) eapply typeTuple.
      * eapply (@ren_comp_typing m n Γ Δ ξ Hξ). eassumption.
      * eapply (@ren_comp_typing m n Γ Δ ξ Hξ). eassumption.
    + (* typeProj *) eapply typeProj.
      eapply (@ren_comp_typing m n Γ Δ ξ Hξ). eassumption.
    + (* typeForce *) apply typeForce.
      eapply (@ren_value_typing m n Γ Δ ξ Hξ). eassumption.
    + (* typeCaseZ *) apply typeCaseZ.
      eapply (@ren_value_typing m n Γ Δ ξ Hξ). eassumption.
    + (* typeCaseS *) eapply typeCaseS.
      * eapply (@ren_value_typing m n Γ Δ ξ Hξ). eassumption.
      * eapply (@ren_comp_typing (S m) (S n) (A1 .: Γ) (A1 .: Δ) (up_ren ξ)
                                   (up_lift_eq Γ Δ ξ Hξ A1)).
        eassumption.
      * eapply (@ren_comp_typing (S m) (S n) (A2 .: Γ) (A2 .: Δ) (up_ren ξ)
                                   (up_lift_eq Γ Δ ξ Hξ A2)).
        eassumption.
    + (* typeCaseP *) eapply typeCaseP.
      * eapply (@ren_value_typing m n Γ Δ ξ Hξ). eassumption.
      * eapply (@ren_comp_typing (S (S m)) (S (S n)) (B .: (A .: Γ)) (B .: (A .: Δ))
                                   (up_ren (up_ren ξ))
                                   (up_lift_eq (A .: Γ) (A .: Δ) (up_ren ξ)
                                               (up_lift_eq Γ Δ ξ Hξ A) B)).
        eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Typed lifting of a substitution under a cons                       *)
(* ------------------------------------------------------------------ *)

Lemma up_value_value_typing {m n} (Γ: ctx n) (Δ: ctx m) (σ: fin m -> value n)
  (A: valtype) (Hσ: forall i, Γ ⊩ σ i : Δ i) :
  forall (i : fin (S m)), (A .: Γ) ⊩ up_value_value σ i : (A .: Δ) i.
Proof.
  intros [i|]; simpl.
  - eapply (@ren_value_typing n (S n) (A .: Γ) Γ shift).
    + intros j. reflexivity.
    + eapply Hσ.
  - apply typeVar.
Qed.

(* ------------------------------------------------------------------ *)
(* Substitution typing (mutual, arbitrary context substitution)       *)
(* ------------------------------------------------------------------ *)

Fixpoint subst_value_typing (m n : nat) (Γ: ctx n) (Δ: ctx m) (σ: fin m -> value n)
  (Hσ: forall i, Γ ⊩ σ i : Δ i) (v: value m) (A: valtype)
  (H: Δ ⊩ v : A) {struct H} : Γ ⊩ subst_value σ v : A
with subst_comp_typing (m n : nat) (Γ: ctx n) (Δ: ctx m) (σ: fin m -> value n)
  (Hσ: forall i, Γ ⊩ σ i : Δ i) (c: comp m) (B: comptype)
  (H: Δ ⊢ c : B) {struct H} : Γ ⊢ subst_comp σ c : B.
Proof.
  - (* value *) simpl. destruct H; simpl.
    + (* typeVar *) exact (Hσ i).
    + apply typeUnit.
    + apply typePair.
      * eapply (@subst_value_typing m n Γ Δ σ Hσ). eassumption.
      * eapply (@subst_value_typing m n Γ Δ σ Hσ). eassumption.
    + apply typeSum.
      eapply (@subst_value_typing m n Γ Δ σ Hσ). eassumption.
    + apply typeThunk.
      eapply (@subst_comp_typing m n Γ Δ σ Hσ). eassumption.
  - (* comp *) simpl. destruct H; simpl.
    + (* typeCone *) apply typeCone.
    + (* typeLambda *) apply typeLambda.
      eapply (@subst_comp_typing (S m) (S n) (A .: Γ) (A .: Δ)
                                   (up_value_value σ) (@up_value_value_typing m n Γ Δ σ A Hσ)).
      eassumption.
    + (* typeLetin *) eapply typeLetin.
      * eapply (@subst_comp_typing m n Γ Δ σ Hσ). eassumption.
      * eapply (@subst_comp_typing (S m) (S n) (A .: Γ) (A .: Δ)
                                     (up_value_value σ) (@up_value_value_typing m n Γ Δ σ A Hσ)).
        eassumption.
    + (* typeRet *) apply typeRet.
      eapply (@subst_value_typing m n Γ Δ σ Hσ). eassumption.
    + (* typeApp *) eapply typeApp.
      * eapply (@subst_comp_typing m n Γ Δ σ Hσ). eassumption.
      * eapply (@subst_value_typing m n Γ Δ σ Hσ). eassumption.
    + (* typeTuple *) eapply typeTuple.
      * eapply (@subst_comp_typing m n Γ Δ σ Hσ). eassumption.
      * eapply (@subst_comp_typing m n Γ Δ σ Hσ). eassumption.
    + (* typeProj *) eapply typeProj.
      eapply (@subst_comp_typing m n Γ Δ σ Hσ). eassumption.
    + (* typeForce *) apply typeForce.
      eapply (@subst_value_typing m n Γ Δ σ Hσ). eassumption.
    + (* typeCaseZ *) apply typeCaseZ.
      eapply (@subst_value_typing m n Γ Δ σ Hσ). eassumption.
    + (* typeCaseS *) eapply typeCaseS.
      * eapply (@subst_value_typing m n Γ Δ σ Hσ). eassumption.
      * eapply (@subst_comp_typing (S m) (S n) (A1 .: Γ) (A1 .: Δ)
                                     (up_value_value σ) (@up_value_value_typing m n Γ Δ σ A1 Hσ)).
        eassumption.
      * eapply (@subst_comp_typing (S m) (S n) (A2 .: Γ) (A2 .: Δ)
                                     (up_value_value σ) (@up_value_value_typing m n Γ Δ σ A2 Hσ)).
        eassumption.
    + (* typeCaseP *) eapply typeCaseP.
      * eapply (@subst_value_typing m n Γ Δ σ Hσ). eassumption.
      * eapply (@subst_comp_typing (S (S m)) (S (S n))
                                     (B .: (A .: Γ)) (B .: (A .: Δ))
                                     (up_value_value (up_value_value σ))
                                     (@up_value_value_typing (S m) (S n) (A .: Γ) (A .: Δ)
                                        (up_value_value σ) B
                                        (@up_value_value_typing m n Γ Δ σ A Hσ))).
        eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* pstep forward typing preservation                                  *)
(* ------------------------------------------------------------------ *)

Lemma pstep_typing_fwd : forall n (c c': comp n), pstep c c' ->
  forall (Gamma: ctx n) B, inhab (Gamma ⊢ c : B) -> inhab (Gamma ⊢ c' : B).
Proof.
  intros n c c' Hp. induction Hp as
    [c0 | c0 c' v E | b c c1 c2 E | c0 c' v E | v b c c1 c2 E | v1 v2 c c' E];
    intros Γ B Hc; destruct Hc as [Hc].
  - (* pstepForce *)
    eapply cty_force_elim; [ exact Hc | ]. intros Hv.
    eapply vty_thunk_elim; [ exact Hv | ]. intros B0 HB Hc0.
    injection HB as HB. subst B0. apply inhabited. exact Hc0.
  - (* pstepApp *)
    eapply cty_app_elim; [ exact Hc | ]. intros A Hlam Hv.
    eapply cty_lambda_elim; [ exact Hlam | ]. intros A0 B0 HB Hc0.
    injection HB as HA HB. subst A0. subst B0.
    rewrite <- E. apply inhabited.
    eapply (@subst_comp_typing (S n) n Γ (A .: Γ)
                                 (scons v (@ids value VarInstance_value n))).
    + intros [i|]; simpl.
      * apply typeVar.
      * exact Hv.
    + exact Hc0.
  - (* pstepProj *)
    eapply cty_proj_elim; [ exact Hc | ]. intros B1 B2 Ht HB.
    eapply cty_tuple_elim; [ exact Ht | ]. intros C1 C2 Htup HC1 HC2.
    injection Htup as HC1' HC2'. subst C1. subst C2.
    rewrite E. destruct b; simpl in *; subst B; apply inhabited; assumption.
  - (* pstepLetin *)
    eapply cty_letin_elim; [ exact Hc | ]. intros A Hret Hc0.
    eapply cty_ret_elim; [ exact Hret | ]. intros A0 HB Hv.
    injection HB as HB. subst A0.
    rewrite <- E. apply inhabited.
    eapply (@subst_comp_typing (S n) n Γ (A .: Γ)
                                 (scons v (@ids value VarInstance_value n))).
    + intros [i|]; simpl.
      * apply typeVar.
      * exact Hv.
    + exact Hc0.
  - (* pstepCaseS *)
    eapply cty_caseS_elim; [ exact Hc | ]. intros A1 A2 Hv H1 H2.
    eapply vty_inj_elim; [ exact Hv | ]. intros D1 D2 HA Hv0.
    injection HA as HA1 HA2. subst D1. subst D2.
    rewrite <- E. destruct b; simpl in *.
    + apply inhabited.
      eapply (@subst_comp_typing (S n) n Γ (A1 .: Γ)
                                   (scons v (@ids value VarInstance_value n))).
      * intros [i|]; simpl.
        -- apply typeVar.
        -- exact Hv0.
      * exact H1.
    + apply inhabited.
      eapply (@subst_comp_typing (S n) n Γ (A2 .: Γ)
                                   (scons v (@ids value VarInstance_value n))).
      * intros [i|]; simpl.
        -- apply typeVar.
        -- exact Hv0.
      * exact H2.
  - (* pstepCaseP *)
    eapply cty_caseP_elim; [ exact Hc | ]. intros A B0 Hv Hc0.
    eapply vty_pair_elim; [ exact Hv | ]. intros D1 D2 HA Hv1 Hv2.
    injection HA as HA1 HA2. subst D1. subst D2.
    rewrite <- E. apply inhabited.
    eapply (@subst_comp_typing (S (S n)) n Γ (B0 .: (A .: Γ))
                                 (scons v2 (scons v1 (@ids value VarInstance_value n)))).
    + intros [j|]; simpl.
      * destruct j as [j|]; simpl.
        -- apply typeVar.
        -- exact Hv1.
      * exact Hv2.
    + exact Hc0.
Qed.

(* ------------------------------------------------------------------ *)
(* sstep forward typing preservation (mutual)                         *)
(* ------------------------------------------------------------------ *)

Lemma sstep_typing_fwd_all : forall n,
  (forall (c c': comp n) (s: c ↪ c'),
      forall (Gamma: ctx n) B, inhab (Gamma ⊢ c : B) -> inhab (Gamma ⊢ c' : B)) /\
  (forall (v v': value n) (s: v ↪ᵥ v'),
      forall (Gamma: ctx n) A, inhab (Gamma ⊩ v : A) -> inhab (Gamma ⊩ v' : A)).
Proof.
  apply mutind_sstep.
  - (* sstepValuePairL *)
    intros n v1 v1' v2 s IH Γ A Hp. destruct Hp as [Hp].
    eapply vty_pair_elim; [ exact Hp | ]. intros A1 A2 HA H1 H2.
    subst A. destruct (IH Γ A1 (inhabited H1)) as [H1'].
    apply inhabited. apply typePair.
    + exact H1'.
    + exact H2.
  - (* sstepValuePairR *)
    intros n v1 v2 v2' s IH Γ A Hp. destruct Hp as [Hp].
    eapply vty_pair_elim; [ exact Hp | ]. intros A1 A2 HA H1 H2.
    subst A. destruct (IH Γ A2 (inhabited H2)) as [H2'].
    apply inhabited. apply typePair.
    + exact H1.
    + exact H2'.
  - (* sstepValueInj *)
    intros n b v v' s IH Γ A Hp. destruct Hp as [Hp].
    eapply vty_inj_elim; [ exact Hp | ]. intros A1 A2 HA Hv.
    subst A. destruct b; simpl in *.
    + destruct (IH Γ A1 (inhabited Hv)) as [Hv'].
      apply inhabited. apply typeSum. exact Hv'.
    + destruct (IH Γ A2 (inhabited Hv)) as [Hv'].
      apply inhabited. apply typeSum. exact Hv'.
  - (* sstepValueThunk *)
    intros n c c' s IH Γ A Hp. destruct Hp as [Hp].
    eapply vty_thunk_elim; [ exact Hp | ]. intros B HB Hc.
    subst A. destruct (IH Γ B (inhabited Hc)) as [Hc'].
    apply inhabited. apply typeThunk. exact Hc'.
  - (* sstepForce *)
    intros n v v' s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_force_elim; [ exact Hp | ]. intros Hv.
    destruct (IH Γ (U B) (inhabited Hv)) as [Hv'].
    apply inhabited. apply typeForce. exact Hv'.
  - (* sstepLambda *)
    intros n c c' s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_lambda_elim; [ exact Hp | ]. intros A B0 HB Hc.
    subst B. destruct (IH (A .: Γ) B0 (inhabited Hc)) as [Hc'].
    apply inhabited. apply typeLambda. exact Hc'.
  - (* sstepAppL *)
    intros n c c' v s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_app_elim; [ exact Hp | ]. intros A Hlam Hv.
    destruct (IH Γ (arrow A B) (inhabited Hlam)) as [Hlam'].
    apply inhabited. eapply typeApp.
    + exact Hlam'.
    + exact Hv.
  - (* sstepAppR *)
    intros n c v v' s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_app_elim; [ exact Hp | ]. intros A Hlam Hv.
    destruct (IH Γ A (inhabited Hv)) as [Hv'].
    apply inhabited. eapply typeApp.
    + exact Hlam.
    + exact Hv'.
  - (* sstepTupleL *)
    intros n c1 c1' c2 s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_tuple_elim; [ exact Hp | ]. intros B1 B2 HB H1 H2.
    subst B. destruct (IH Γ B1 (inhabited H1)) as [H1'].
    apply inhabited. apply typeTuple.
    + exact H1'.
    + exact H2.
  - (* sstepTupleR *)
    intros n c1 c2 c2' s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_tuple_elim; [ exact Hp | ]. intros B1 B2 HB H1 H2.
    subst B. destruct (IH Γ B2 (inhabited H2)) as [H2'].
    apply inhabited. apply typeTuple.
    + exact H1.
    + exact H2'.
  - (* sstepRet *)
    intros n v v' s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_ret_elim; [ exact Hp | ]. intros A HB Hv.
    subst B. destruct (IH Γ A (inhabited Hv)) as [Hv'].
    apply inhabited. apply typeRet. exact Hv'.
  - (* sstepLetinL *)
    intros n c1 c1' c2 s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_letin_elim; [ exact Hp | ]. intros A H1 H2.
    destruct (IH Γ (F A) (inhabited H1)) as [H1'].
    apply inhabited. eapply typeLetin.
    + exact H1'.
    + exact H2.
  - (* sstepLetinR *)
    intros n c1 c2 c2' s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_letin_elim; [ exact Hp | ]. intros A H1 H2.
    destruct (IH (A .: Γ) B (inhabited H2)) as [H2'].
    apply inhabited. eapply typeLetin.
    + exact H1.
    + exact H2'.
  - (* sstepProj *)
    intros n c c' b s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_proj_elim; [ exact Hp | ]. intros B1 B2 Hc HB.
    subst B. destruct (IH Γ (Pi B1 B2) (inhabited Hc)) as [Hc'].
    apply inhabited. apply typeProj. exact Hc'.
  - (* sstepCaseZ *)
    intros n v v' s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_caseZ_elim; [ exact Hp | ]. intros Hv.
    destruct (IH Γ zero (inhabited Hv)) as [Hv'].
    apply inhabited. apply typeCaseZ. exact Hv'.
  - (* sstepCaseSV *)
    intros n v v' c1 c2 s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_caseS_elim; [ exact Hp | ]. intros A1 A2 Hv H1 H2.
    destruct (IH Γ (Sigma A1 A2) (inhabited Hv)) as [Hv'].
    apply inhabited. eapply typeCaseS.
    + exact Hv'.
    + exact H1.
    + exact H2.
  - (* sstepCaseSL *)
    intros n v c1 c1' c2 s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_caseS_elim; [ exact Hp | ]. intros A1 A2 Hv H1 H2.
    destruct (IH (A1 .: Γ) B (inhabited H1)) as [H1'].
    apply inhabited. eapply typeCaseS.
    + exact Hv.
    + exact H1'.
    + exact H2.
  - (* sstepCaseSR *)
    intros n v c1 c2 c2' s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_caseS_elim; [ exact Hp | ]. intros A1 A2 Hv H1 H2.
    destruct (IH (A2 .: Γ) B (inhabited H2)) as [H2'].
    apply inhabited. eapply typeCaseS.
    + exact Hv.
    + exact H1.
    + exact H2'.
  - (* sstepCasePV *)
    intros n v v' c s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_caseP_elim; [ exact Hp | ]. intros A B0 Hv Hc.
    destruct (IH Γ (A * B0) (inhabited Hv)) as [Hv'].
    apply inhabited. eapply typeCaseP.
    + exact Hv'.
    + exact Hc.
  - (* sstepCasePC *)
    intros n v c c' s IH Γ B Hp. destruct Hp as [Hp].
    eapply cty_caseP_elim; [ exact Hp | ]. intros A B0 Hv Hc.
    destruct (IH (B0 .: (A .: Γ)) B (inhabited Hc)) as [Hc'].
    apply inhabited. eapply typeCaseP.
    + exact Hv.
    + exact Hc'.
  - (* sstepPrimitive *)
    intros n c c' p Γ B Hp.
    exact (@pstep_typing_fwd n c c' p Γ B Hp).
Qed.

Lemma sstep_typing_fwd : forall n (c c': comp n), sstep c c' ->
  forall (Gamma: ctx n) B, inhab (Gamma ⊢ c : B) -> inhab (Gamma ⊢ c' : B).
Proof.
  intros n c c' Hs Γ B Hc.
  exact (proj1 (sstep_typing_fwd_all n) c c' Hs Γ B Hc).
Qed.

Lemma sstep_value_typing_fwd : forall n (v v': value n), sstep_value v v' ->
  forall (Gamma: ctx n) A, inhab (Gamma ⊩ v : A) -> inhab (Gamma ⊩ v' : A).
Proof.
  intros n v v' Hs Γ A Hv.
  exact (proj2 (sstep_typing_fwd_all n) v v' Hs Γ A Hv).
Qed.

(* ------------------------------------------------------------------ *)
(* The unconditional backward (reflection) statements are false.      *)
(* The counterexample is the pstepApp redex                          *)
(*   (lambda cu) (thunk (caseZ u))  ≽  cu                             *)
(* in the empty context: the reduct cu : cone is typable, while the   *)
(* redex is untypable because (thunk (caseZ u)) : U A would require    *)
(* caseZ u : A, hence u : zero, but u : one is the only typing of u.   *)
(* Consequently there is no proof of the backward statements without   *)
(* extra hypotheses.  We record the formal refutation below.          *)
(* ------------------------------------------------------------------ *)

Definition bad_value : value 0 := thunk (caseZ u).

Lemma u_not_zero : forall (Gamma: ctx 0), Gamma ⊩ u : zero -> False.
Proof.
  intros Gamma H. inversion H.
Qed.

Lemma bad_value_untypable :
  forall (Gamma: ctx 0) (A: valtype), Gamma ⊩ bad_value : A -> False.
Proof.
  intros Gamma A H. unfold bad_value in H.
  eapply vty_thunk_elim; [ exact H | ]. intros B HB Hc.
  eapply cty_caseZ_elim; [ exact Hc | ]. intros Hu.
  exact (@u_not_zero Gamma Hu).
Qed.

Lemma bad_source_untypable :
  forall B, ~ inhab (null ⊢ app (lambda cu) bad_value : B).
Proof.
  intros B [H].
  eapply cty_app_elim; [ exact H | ]. intros A Hlam Hv.
  eapply cty_lambda_elim; [ exact Hlam | ]. intros A0 B0 HB Hc.
  injection HB as HA HB. subst A0. subst B0.
  exact (@bad_value_untypable null A Hv).
Qed.

Lemma pstep_typing_bwd_refuted :
  ~ (forall n (c c': comp n), pstep c c' ->
       forall (Gamma: ctx n) B, inhab (Gamma ⊢ c' : B) -> inhab (Gamma ⊢ c : B)).
Proof.
  intro H.
  pose (Step := @pstepApp 0 cu cu bad_value eq_refl).
  pose proof (H 0 (app (lambda cu) bad_value) cu Step null cone
                (inhabited (@typeCone 0 null))) as Hsrc.
  exact (@bad_source_untypable cone Hsrc).
Qed.

Lemma sstep_typing_bwd_refuted :
  ~ (forall n (c c': comp n), sstep c c' ->
       forall (Gamma: ctx n) B, inhab (Gamma ⊢ c' : B) -> inhab (Gamma ⊢ c : B)).
Proof.
  intro H.
  pose (Step := @pstepApp 0 cu cu bad_value eq_refl).
  pose (Sc := @sstepPrimitive 0 (app (lambda cu) bad_value) cu Step).
  exact (@bad_source_untypable cone
           (H 0 (app (lambda cu) bad_value) cu Sc null cone
              (inhabited (@typeCone 0 null)))).
Qed.

Lemma sstep_value_typing_bwd_refuted :
  ~ (forall n (v v': value n), sstep_value v v' ->
       forall (Gamma: ctx n) A,
       inhab (Gamma ⊩ v' : A) -> inhab (Gamma ⊩ v : A)).
Proof.
  intro H.
  pose (Step := @pstepApp 0 cu cu bad_value eq_refl).
  pose (Sc := @sstepPrimitive 0 (app (lambda cu) bad_value) cu Step).
  pose (Sv := @sstepValueThunk 0 (app (lambda cu) bad_value) cu Sc).
  pose proof (H 0 (thunk (app (lambda cu) bad_value)) (thunk cu) Sv
                null (U cone)
                (inhabited (@typeThunk 0 null cu cone (@typeCone 0 null)))) as Hv.
  destruct Hv as [Hbad].
  eapply vty_thunk_elim; [ exact Hbad | ]. intros B HB Hc.
  exact (@bad_source_untypable B (inhabited Hc)).
Qed.

(* The substitution-inversion helper needed by the backward plan is also
   false as stated: the term c may ignore its variable.  Taking c = cu
   and v = bad_value gives a typable substituted term cu : cone although
   bad_value is untypable, so no A with (null ⊩ v : A) can exist.        *)
Definition subst_inv_refuted :
  (forall (c: comp 1) (v: value 0) (B: comptype),
       null ⊢ c[v..] : B ->
       { A : valtype & (null ⊩ v : A) * (A .: null ⊢ c : B) }) -> False.
Proof.
  intro H.
  destruct (H cu bad_value cone (@typeCone 0 null)) as [A Hp].
  destruct Hp as [Hv Hc].
  exact (@bad_value_untypable null A Hv).
Qed.

Set Implicit Arguments.
(* [Require Import Tmp.All] does not re-export the CBPV library, so we
   re-require [CBPV.StrongReduction] to bring [CommaNotation] and the
   [↪] / [↪ᵥ] / [star] notations into scope. *)
Require Import CBPV.StrongReduction.
Import CommaNotation.

(* Closure of strong reduction under one-hole program contexts.

   We prove the two [true]-indexed and the two [false]-indexed statements
   by two mutual fixpoints (the [true] and [false] families cannot be
   merged, since the impossible hole constructor has a different type
   in each).  Every recursive call is on a direct constructor argument,
   so the structural guard condition is satisfied. *)

Fixpoint sstep_fillc_true_aux {m n: nat} (C: cctx true m n) {struct C} :
  forall (v v': value n), v ↪ᵥ v' -> fillc C v ↪ fillc C v'
with sstep_fillv_true_aux {m n: nat} (C: vctx true m n) {struct C} :
  forall (v v': value n), v ↪ᵥ v' -> fillv C v ↪ᵥ fillv C v'.
Proof.
  - (* cctx true *)
    destruct C as [H | n C | n C | n C v0 | n c0 C | n C c0 | n c0 C
                  | n C | n C c0 | n c0 C | n b C | n C | n C c1 c2
                  | n v0 C c2 | n v0 c1 C | n C c0 | n v0 C];
    intros v v' Hv.
    + destruct H.
    + apply sstepForce. apply sstep_fillv_true_aux. exact Hv.
    + apply sstepLambda. apply sstep_fillc_true_aux. exact Hv.
    + apply sstepAppL. apply sstep_fillc_true_aux. exact Hv.
    + apply sstepAppR. apply sstep_fillv_true_aux. exact Hv.
    + apply sstepTupleL. apply sstep_fillc_true_aux. exact Hv.
    + apply sstepTupleR. apply sstep_fillc_true_aux. exact Hv.
    + apply sstepRet. apply sstep_fillv_true_aux. exact Hv.
    + apply sstepLetinL. apply sstep_fillc_true_aux. exact Hv.
    + apply sstepLetinR. apply sstep_fillc_true_aux. exact Hv.
    + apply sstepProj. apply sstep_fillc_true_aux. exact Hv.
    + apply sstepCaseZ. apply sstep_fillv_true_aux. exact Hv.
    + apply sstepCaseSV. apply sstep_fillv_true_aux. exact Hv.
    + apply sstepCaseSL. apply sstep_fillc_true_aux. exact Hv.
    + apply sstepCaseSR. apply sstep_fillc_true_aux. exact Hv.
    + apply sstepCasePV. apply sstep_fillv_true_aux. exact Hv.
    + apply sstepCasePC. apply sstep_fillc_true_aux. exact Hv.
  - (* vctx true *)
    destruct C as [H | n C v0 | n v0 C | n b C | n C]; intros v v' Hv.
    + exact Hv.
    + apply sstepValuePairL. apply sstep_fillv_true_aux. exact Hv.
    + apply sstepValuePairR. apply sstep_fillv_true_aux. exact Hv.
    + apply sstepValueInj. apply sstep_fillv_true_aux. exact Hv.
    + apply sstepValueThunk. apply sstep_fillc_true_aux. exact Hv.
Qed.

Fixpoint sstep_fillc_false_aux {m n: nat} (C: cctx false m n) {struct C} :
  forall (c c': comp n), c ↪ c' -> fillc C c ↪ fillc C c'
with sstep_fillv_false_aux {m n: nat} (C: vctx false m n) {struct C} :
  forall (c c': comp n), c ↪ c' -> fillv C c ↪ᵥ fillv C c'.
Proof.
  - (* cctx false *)
    destruct C as [H | n C | n C | n C v0 | n c0 C | n C c0 | n c0 C
                  | n C | n C c0 | n c0 C | n b C | n C | n C c1 c2
                  | n v0 C c2 | n v0 c1 C | n C c0 | n v0 C];
    intros c c' Hc.
    + exact Hc.
    + apply sstepForce. apply sstep_fillv_false_aux. exact Hc.
    + apply sstepLambda. apply sstep_fillc_false_aux. exact Hc.
    + apply sstepAppL. apply sstep_fillc_false_aux. exact Hc.
    + apply sstepAppR. apply sstep_fillv_false_aux. exact Hc.
    + apply sstepTupleL. apply sstep_fillc_false_aux. exact Hc.
    + apply sstepTupleR. apply sstep_fillc_false_aux. exact Hc.
    + apply sstepRet. apply sstep_fillv_false_aux. exact Hc.
    + apply sstepLetinL. apply sstep_fillc_false_aux. exact Hc.
    + apply sstepLetinR. apply sstep_fillc_false_aux. exact Hc.
    + apply sstepProj. apply sstep_fillc_false_aux. exact Hc.
    + apply sstepCaseZ. apply sstep_fillv_false_aux. exact Hc.
    + apply sstepCaseSV. apply sstep_fillv_false_aux. exact Hc.
    + apply sstepCaseSL. apply sstep_fillc_false_aux. exact Hc.
    + apply sstepCaseSR. apply sstep_fillc_false_aux. exact Hc.
    + apply sstepCasePV. apply sstep_fillv_false_aux. exact Hc.
    + apply sstepCasePC. apply sstep_fillc_false_aux. exact Hc.
  - (* vctx false *)
    destruct C as [H | n C v0 | n v0 C | n b C | n C]; intros c c' Hc.
    + destruct H.
    + apply sstepValuePairL. apply sstep_fillv_false_aux. exact Hc.
    + apply sstepValuePairR. apply sstep_fillv_false_aux. exact Hc.
    + apply sstepValueInj. apply sstep_fillv_false_aux. exact Hc.
    + apply sstepValueThunk. apply sstep_fillc_false_aux. exact Hc.
Qed.

Lemma sstep_fillc_true : forall m n (C: cctx true m n) (v v': value n),
  v ↪ᵥ v' -> fillc C v ↪ fillc C v'.
Proof.
  intros m n C v v' H. apply sstep_fillc_true_aux. exact H.
Qed.

Lemma sstep_fillc_false : forall m n (C: cctx false m n) (c c': comp n),
  c ↪ c' -> fillc C c ↪ fillc C c'.
Proof.
  intros m n C c c' H. apply sstep_fillc_false_aux. exact H.
Qed.

Lemma sstep_fillv_true : forall m n (C: vctx true m n) (v v': value n),
  v ↪ᵥ v' -> fillv C v ↪ᵥ fillv C v'.
Proof.
  intros m n C v v' H. apply sstep_fillv_true_aux. exact H.
Qed.

Lemma sstep_fillv_false : forall m n (C: vctx false m n) (c c': comp n),
  c ↪ c' -> fillv C c ↪ᵥ fillv C c'.
Proof.
  intros m n C c c' H. apply sstep_fillv_false_aux. exact H.
Qed.

Lemma sstep_star_fillc_false : forall m n (C: cctx false m n) (c c': comp n),
  star sstep c c' -> star sstep (fillc C c) (fillc C c').
Proof.
  intros m n C c c' H. induction H.
  - apply starRefl.
  - eapply starStep.
    + apply sstep_fillc_false. exact H.
    + exact IHstar.
Qed.

Lemma sstep_star_fillc_true : forall m n (C: cctx true m n) (v v': value n),
  star sstep_value v v' -> star sstep (fillc C v) (fillc C v').
Proof.
  intros m n C v v' H. induction H.
  - apply starRefl.
  - eapply starStep.
    + apply sstep_fillc_true. exact H.
    + exact IHstar.
Qed.

Lemma sstep_star_fillv_false : forall m n (C: vctx false m n) (c c': comp n),
  star sstep c c' -> star sstep_value (fillv C c) (fillv C c').
Proof.
  intros m n C c c' H. induction H.
  - apply starRefl.
  - eapply starStep.
    + apply sstep_fillv_false. exact H.
    + exact IHstar.
Qed.

Lemma sstep_star_fillv_true : forall m n (C: vctx true m n) (v v': value n),
  star sstep_value v v' -> star sstep_value (fillv C v) (fillv C v').
Proof.
  intros m n C v v' H. induction H.
  - apply starRefl.
  - eapply starStep.
    + apply sstep_fillv_true. exact H.
    + exact IHstar.
Qed.

Set Implicit Arguments.
Require Import CBPV.ProgramContexts.
Import CommaNotation.

(* We need a type-valued simultaneous induction principle, since the
   typing judgments themselves live in [Type]. *)
Scheme vctx_typing_ind_T := Induction for vctxTyping Sort Type
  with cctx_typing_ind_T := Induction for cctxTyping Sort Type.
Combined Scheme mutindT_vctx_cctx_typing from
  vctx_typing_ind_T, cctx_typing_ind_T.

(* The type of the object that can be plugged in a hole of kind [t]:
   a value when [t = true], a computation when [t = false].  The typing
   judgment for that object is packaged in [input_typing]. *)

Definition input_typing {n: nat} (t: bool) (Delta: ctx n)
  (T: if t then valtype else comptype)
  (x: if t then value n else comp n) : Type :=
  match t as b return
    (if b then valtype else comptype) ->
    (if b then value n else comp n) -> Type
  with
  | true  => fun T v => Delta ⊩ v : T
  | false => fun T c => Delta ⊢ c : T
  end T x.

(* The two simultaneous statements, parameterised over the bool index [t]. *)

Definition Pv : forall (m: nat) (t: bool) (Gamma: ctx m) (n: nat)
    (Delta: ctx n) (C: vctx t m n) (A: valtype)
    (T: if t then valtype else comptype),
    (Gamma [[ Delta ]] ⊩ C : A ; T) -> Type :=
  fun m t Gamma n Delta C A T H =>
    forall x, @input_typing n t Delta T x -> Gamma ⊩ fillv C x : A.

Definition Pc : forall (m: nat) (t: bool) (Gamma: ctx m) (n: nat)
    (Delta: ctx n) (C: cctx t m n) (B: comptype)
    (T: if t then valtype else comptype),
    (Gamma [[ Delta ]] ⊢ C : B ; T) -> Type :=
  fun m t Gamma n Delta C B T H =>
    forall x, @input_typing n t Delta T x -> Gamma ⊢ fillc C x : B.

Definition fill_typing_all : forall (m: nat) (t: bool) (Gamma: ctx m),
  prod
  (forall (n: nat) (Delta: ctx n) (C: vctx t m n) (A: valtype)
     (T: if t then valtype else comptype)
     (H: Gamma [[ Delta ]] ⊩ C : A ; T),
      @Pv m t Gamma n Delta C A T H)
  (forall (n: nat) (Delta: ctx n) (C: cctx t m n) (B: comptype)
     (T: if t then valtype else comptype)
     (H: Gamma [[ Delta ]] ⊢ C : B ; T),
      @Pc m t Gamma n Delta C B T H).
Proof.
  intros m t Gamma.
  apply (mutindT_vctx_cctx_typing Pv Pc).
  - (* vctxTypingHole *)
    intros m0 t0 Gamma0 A H.
    destruct t0; simpl.
    + intros x Hx. exact Hx.
    + destruct H.
  - (* vctxTypingPairL *)
    intros m0 t0 Gamma0 n Delta C A A1 A2 v vrec IH v1 x Hx.
    simpl. apply typePair.
    + exact (IH x Hx).
    + exact v1.
  - (* vctxTypingPairR *)
    intros m0 t0 Gamma0 n Delta C A A1 A2 v v0 vrec IH x Hx.
    simpl. apply typePair.
    + exact v0.
    + exact (IH x Hx).
  - (* vctxTypingInj *)
    intros m0 t0 Gamma0 n Delta C A A1 A2 b vrec IH x Hx.
    simpl. apply typeSum. exact (IH x Hx).
  - (* vctxTypingThunk *)
    intros m0 t0 Gamma0 n Delta C B A c IH x Hx.
    simpl. apply typeThunk. exact (IH x Hx).
  - (* cctxTypingHole *)
    intros m0 t0 Gamma0 A H.
    destruct t0; simpl.
    + destruct H.
    + intros x Hx. exact Hx.
  - (* cctxTypingLambda *)
    intros m0 t0 Gamma0 n Delta C A A' B c IH x Hx.
    simpl. apply typeLambda. exact (IH x Hx).
  - (* cctxTypingForce *)
    intros m0 t0 Gamma0 n Delta C B A' v IH x Hx.
    simpl. apply typeForce. exact (IH x Hx).
  - (* cctxTypingAppL *)
    intros m0 t0 Gamma0 n Delta C A A' B v c IH v0 x Hx.
    simpl. apply typeApp with (A := A).
    + exact (IH x Hx).
    + exact v0.
  - (* cctxTypingAppR *)
    intros m0 t0 Gamma0 n Delta c C A A' B c0 v IH x Hx.
    simpl. apply typeApp with (A := A).
    + exact c0.
    + exact (IH x Hx).
  - (* cctxTypingTupleL *)
    intros m0 t0 Gamma0 n Delta C B1 B2 A c c0 IH c1 x Hx.
    simpl. apply typeTuple.
    + exact (IH x Hx).
    + exact c1.
  - (* cctxTypingTupleR *)
    intros m0 t0 Gamma0 n Delta C B1 B2 A c c0 c1 IH x Hx.
    simpl. apply typeTuple.
    + exact c0.
    + exact (IH x Hx).
  - (* cctxTypingRet *)
    intros m0 t0 Gamma0 n Delta C A A' v IH x Hx.
    simpl. apply typeRet. exact (IH x Hx).
  - (* cctxTypingLetinL *)
    intros m0 t0 Gamma0 n Delta C A A' B c c0 IH c1 x Hx.
    simpl. apply typeLetin with (A := A).
    + exact (IH x Hx).
    + exact c1.
  - (* cctxTypingLetinR *)
    intros m0 t0 Gamma0 n Delta C A A' B c c0 c1 IH x Hx.
    simpl. apply typeLetin with (A := A).
    + exact c0.
    + exact (IH x Hx).
  - (* cctxTypingProj *)
    intros m0 t0 Gamma0 n Delta C A B1 B2 b c IH x Hx.
    simpl. apply typeProj. exact (IH x Hx).
  - (* cctxTypingCaseZ *)
    intros m0 t0 Gamma0 n Delta C A A' v IH x Hx.
    simpl. apply typeCaseZ. exact (IH x Hx).
  - (* cctxTypingCaseSV *)
    intros m0 t0 Gamma0 n Delta C A1 A2 A' B c1 c2 v IH h1 h2 x Hx.
    simpl. apply typeCaseS with (A1 := A1) (A2 := A2).
    + exact (IH x Hx).
    + exact h1.
    + exact h2.
  - (* cctxTypingCaseSL *)
    intros m0 t0 Gamma0 n Delta C A1 A2 A' B v c2 hv c IH h2 x Hx.
    simpl. apply typeCaseS with (A1 := A1) (A2 := A2).
    + exact hv.
    + exact (IH x Hx).
    + exact h2.
  - (* cctxTypingCaseSR *)
    intros m0 t0 Gamma0 n Delta C A1 A2 A' B v c1 hv h1 c IH x Hx.
    simpl. apply typeCaseS with (A1 := A1) (A2 := A2).
    + exact hv.
    + exact h1.
    + exact (IH x Hx).
  - (* cctxTypingCasePV *)
    intros m0 t0 Gamma0 n Delta C A1 A2 A' B c v IH hc x Hx.
    simpl. apply typeCaseP with (A := A1) (B := A2).
    + exact (IH x Hx).
    + exact hc.
  - (* cctxTypingCasePC *)
    intros m0 t0 Gamma0 n Delta C A1 A2 A' B v hv c IH x Hx.
    simpl. apply typeCaseP with (A := A1) (B := A2).
    + exact hv.
    + exact (IH x Hx).
Defined.

Lemma fillc_typing_false : forall m n (Gamma: ctx m) (Delta: ctx n)
  (C: cctx false m n) (B: comptype) (A: comptype),
  Gamma [[ Delta ]] ⊢ C : B ; A ->
  forall (c: comp n), Delta ⊢ c : A -> Gamma ⊢ fillc C c : B.
Proof.
  intros m n Gamma Delta C B A H c Hc.
  exact (snd (@fill_typing_all m false Gamma) n Delta C B A H c Hc).
Qed.

Lemma fillc_typing_true : forall m n (Gamma: ctx m) (Delta: ctx n)
  (C: cctx true m n) (B: comptype) (A: valtype),
  Gamma [[ Delta ]] ⊢ C : B ; A ->
  forall (v: value n), Delta ⊩ v : A -> Gamma ⊢ fillc C v : B.
Proof.
  intros m n Gamma Delta C B A H v Hv.
  exact (snd (@fill_typing_all m true Gamma) n Delta C B A H v Hv).
Qed.

Lemma fillv_typing_true : forall m n (Gamma: ctx m) (Delta: ctx n)
  (C: vctx true m n) (A: valtype) (T: valtype),
  Gamma [[ Delta ]] ⊩ C : A ; T ->
  forall (v: value n), Delta ⊩ v : T -> Gamma ⊩ fillv C v : A.
Proof.
  intros m n Gamma Delta C A T H v Hv.
  exact (fst (@fill_typing_all m true Gamma) n Delta C A T H v Hv).
Qed.

Lemma fillv_typing_false : forall m n (Gamma: ctx m) (Delta: ctx n)
  (C: vctx false m n) (A: valtype) (T: comptype),
  Gamma [[ Delta ]] ⊩ C : A ; T ->
  forall (c: comp n), Delta ⊢ c : T -> Gamma ⊩ fillv C c : A.
Proof.
  intros m n Gamma Delta C A T H c Hc.
  exact (fst (@fill_typing_all m false Gamma) n Delta C A T H c Hc).
Qed.

Lemma fillc_typing_closing : forall n (Gamma: ctx n) (C: cctx false 0 n)
  (G: groundtype) (A: comptype),
  null [[ Gamma ]] ⊢ C : F G ; A ->
  forall (c: comp n), Gamma ⊢ c : A -> (null ⊢ fillc C c : F G).
Proof.
  intros n Gamma C G A H c Hc.
  apply fillc_typing_false with (A := A) (Delta := Gamma).
  exact H.
  exact Hc.
Qed.

Set Implicit Arguments.
Require Import CBPV.ObservationalEquivalence CBPV.StrongReduction CBPV.AbstractReductionSystems.
Import CommaNotation.

(* ------------------------------------------------------------------ *)
(* Renaming / substitution lemmas for the primitive step [pstep]       *)
(* ------------------------------------------------------------------ *)

Lemma ren_comp_subst_scons {n m} (xi: fin n -> fin m) (c: comp (S n)) (v: value n) :
  ren_comp xi (subst_comp (scons v (@ids value VarInstance_value n)) c)
  = subst_comp (scons (ren_value xi v) (@ids value VarInstance_value m))
      (ren_comp (up_ren xi) c).
Proof.
  rewrite subst_comp_ren.
  rewrite ren_comp_subst.
  apply subst_comp_congr. intros i. destruct i as [j|]; cbn; reflexivity.
Qed.

Lemma ren_comp_subst_caseP {n m} (xi: fin n -> fin m)
  (c: comp (S (S n))) (v1 v2: value n) :
  ren_comp xi (subst_comp (scons v2 (scons v1 (@ids value VarInstance_value n))) c)
  = subst_comp (scons (ren_value xi v2) (scons (ren_value xi v1)
                   (@ids value VarInstance_value m)))
      (ren_comp (up_ren (up_ren xi)) c).
Proof.
  rewrite subst_comp_ren.
  rewrite ren_comp_subst.
  apply subst_comp_congr. intros i.
  destruct i as [j|]; [destruct j as [k|] | ]; cbn; reflexivity.
Qed.

Lemma pstep_ren : forall n m (c c': comp n), pstep c c' ->
  forall (xi: fin n -> fin m), pstep (ren_comp xi c) (ren_comp xi c').
Proof.
  intros n m c c' H. induction H; intros xi; simpl.
  - (* pstepForce *) apply pstepForce.
  - (* pstepApp *) eapply pstepApp.
    rewrite <- H. symmetry. apply ren_comp_subst_scons.
  - (* pstepProj *) eapply pstepProj.
    rewrite H. destruct b; reflexivity.
  - (* pstepLetin *) eapply pstepLetin.
    rewrite <- H. symmetry. apply ren_comp_subst_scons.
  - (* pstepCaseS *) destruct b; eapply pstepCaseS.
    + simpl in H. rewrite <- H. symmetry. apply ren_comp_subst_scons.
    + simpl in H. rewrite <- H. symmetry. apply ren_comp_subst_scons.
  - (* pstepCaseP *) eapply pstepCaseP.
    rewrite <- H. symmetry. apply ren_comp_subst_caseP.
Qed.

Lemma subst_comp_subst_up_app {n m} (c: comp (S n)) (v: value n)
  (sigma: fin n -> value m) :
  subst_comp (scons (subst_value sigma v) (@ids value VarInstance_value m))
    (subst_comp (up_value_value sigma) c)
  = subst_comp sigma (subst_comp (scons v (@ids value VarInstance_value n)) c).
Proof.
  rewrite (@subst_comp_up_app n m c sigma (subst_value sigma v)).
  rewrite subst_comp_subst.
  apply subst_comp_congr. intros i. destruct i as [j|]; cbn; reflexivity.
Qed.

Lemma subst_comp_subst_up_caseP {n m} (c: comp (S (S n)))
  (v1 v2: value n) (sigma: fin n -> value m) :
  subst_comp (scons (subst_value sigma v2) (scons (subst_value sigma v1)
    (@ids value VarInstance_value m)))
    (subst_comp (up_value_value (up_value_value sigma)) c)
  = subst_comp sigma
      (subst_comp (scons v2 (scons v1 (@ids value VarInstance_value n))) c).
Proof.
  rewrite (@subst_comp_up_up_caseP n m c sigma (subst_value sigma v1) (subst_value sigma v2)).
  rewrite subst_comp_subst.
  apply subst_comp_congr. intros i.
  destruct i as [j|]; [destruct j as [k|] | ]; cbn; reflexivity.
Qed.

Lemma pstep_subst_same : forall n m (c c': comp n), pstep c c' ->
  forall (sigma: fin n -> value m), pstep (subst_comp sigma c) (subst_comp sigma c').
Proof.
  intros n m c c' H. induction H; intros sigma; simpl.
  - (* pstepForce *) apply pstepForce.
  - (* pstepApp *) eapply pstepApp.
    rewrite <- H. apply subst_comp_subst_up_app.
  - (* pstepProj *) eapply pstepProj.
    rewrite H. destruct b; reflexivity.
  - (* pstepLetin *) eapply pstepLetin.
    rewrite <- H. apply subst_comp_subst_up_app.
  - (* pstepCaseS *) destruct b; eapply pstepCaseS.
    + simpl in H. rewrite <- H. apply subst_comp_subst_up_app.
    + simpl in H. rewrite <- H. apply subst_comp_subst_up_app.
  - (* pstepCaseP *) eapply pstepCaseP.
    rewrite <- H. apply subst_comp_subst_up_caseP.
Qed.

(* ------------------------------------------------------------------ *)
(* Closure of [sstep] under renaming                                   *)
(* ------------------------------------------------------------------ *)

Lemma sstep_ren_all : forall n,
  (forall (c c': comp n), c ↪ c' ->
     forall m (xi: fin n -> fin m), ren_comp xi c ↪ ren_comp xi c') /\
  (forall (v v': value n), v ↪ᵥ v' ->
     forall m (xi: fin n -> fin m), ren_value xi v ↪ᵥ ren_value xi v').
Proof.
  intro n.
  apply (mutind_sstep
    (fun n v v' (s: v ↪ᵥ v') =>
       forall m (xi: fin n -> fin m), ren_value xi v ↪ᵥ ren_value xi v')
    (fun n c c' (s: c ↪ c') =>
       forall m (xi: fin n -> fin m), ren_comp xi c ↪ ren_comp xi c')).
  - (* sstepValuePairL *) intros n0 v1 v1' v2 s IH m xi. simpl.
    apply sstepValuePairL. apply (IH m xi).
  - (* sstepValuePairR *) intros n0 v1 v2 v2' s IH m xi. simpl.
    apply sstepValuePairR. apply (IH m xi).
  - (* sstepValueInj *) intros n0 b v v' s IH m xi. simpl.
    apply sstepValueInj. apply (IH m xi).
  - (* sstepValueThunk *) intros n0 c c' s IH m xi. simpl.
    apply sstepValueThunk. apply (IH m xi).
  - (* sstepForce *) intros n0 v v' s IH m xi. simpl.
    apply sstepForce. apply (IH m xi).
  - (* sstepLambda *) intros n0 c c' s IH m xi. simpl.
    apply sstepLambda. apply (IH (S m) (up_ren xi)).
  - (* sstepAppL *) intros n0 c c' v s IH m xi. simpl.
    apply sstepAppL. apply (IH m xi).
  - (* sstepAppR *) intros n0 c v v' s IH m xi. simpl.
    apply sstepAppR. apply (IH m xi).
  - (* sstepTupleL *) intros n0 c1 c1' c2 s IH m xi. simpl.
    apply sstepTupleL. apply (IH m xi).
  - (* sstepTupleR *) intros n0 c1 c2 c2' s IH m xi. simpl.
    apply sstepTupleR. apply (IH m xi).
  - (* sstepRet *) intros n0 v v' s IH m xi. simpl.
    apply sstepRet. apply (IH m xi).
  - (* sstepLetinL *) intros n0 c1 c1' c2 s IH m xi. simpl.
    apply sstepLetinL. apply (IH m xi).
  - (* sstepLetinR *) intros n0 c1 c2 c2' s IH m xi. simpl.
    apply sstepLetinR. apply (IH (S m) (up_ren xi)).
  - (* sstepProj *) intros n0 c c' b s IH m xi. simpl.
    apply sstepProj. apply (IH m xi).
  - (* sstepCaseZ *) intros n0 v v' s IH m xi. simpl.
    apply sstepCaseZ. apply (IH m xi).
  - (* sstepCaseSV *) intros n0 v v' c1 c2 s IH m xi. simpl.
    apply sstepCaseSV. apply (IH m xi).
  - (* sstepCaseSL *) intros n0 v c1 c1' c2 s IH m xi. simpl.
    apply sstepCaseSL. apply (IH (S m) (up_ren xi)).
  - (* sstepCaseSR *) intros n0 v c1 c2 c2' s IH m xi. simpl.
    apply sstepCaseSR. apply (IH (S m) (up_ren xi)).
  - (* sstepCasePV *) intros n0 v v' c s IH m xi. simpl.
    apply sstepCasePV. apply (IH m xi).
  - (* sstepCasePC *) intros n0 v c c' s IH m xi. simpl.
    apply sstepCasePC. apply (IH (S (S m)) (up_ren (up_ren xi))).
  - (* sstepPrimitive *) intros n0 c c' p m xi. simpl.
    apply sstepPrimitive. apply pstep_ren. exact p.
Qed.

Lemma sstep_ren : forall n m (c c': comp n), c ↪ c' ->
  forall (xi: fin n -> fin m), ren_comp xi c ↪ ren_comp xi c'.
Proof.
  intros n m c c' H xi. exact ((proj1 (sstep_ren_all n)) c c' H m xi).
Qed.

Lemma sstep_value_ren : forall n m (v v': value n), v ↪ᵥ v' ->
  forall (xi: fin n -> fin m), ren_value xi v ↪ᵥ ren_value xi v'.
Proof.
  intros n m v v' H xi. exact ((proj2 (sstep_ren_all n)) v v' H m xi).
Qed.

(* ------------------------------------------------------------------ *)
(* Closure of [sstep] under a fixed substitution                        *)
(* ------------------------------------------------------------------ *)

Lemma sstep_subst_same_all : forall n,
  (forall (c c': comp n), c ↪ c' ->
     forall m (sigma: fin n -> value m),
       subst_comp sigma c ↪ subst_comp sigma c') /\
  (forall (v v': value n), v ↪ᵥ v' ->
     forall m (sigma: fin n -> value m),
       subst_value sigma v ↪ᵥ subst_value sigma v').
Proof.
  intro n.
  apply (mutind_sstep
    (fun n v v' (s: v ↪ᵥ v') =>
       forall m (sigma: fin n -> value m),
         subst_value sigma v ↪ᵥ subst_value sigma v')
    (fun n c c' (s: c ↪ c') =>
       forall m (sigma: fin n -> value m),
         subst_comp sigma c ↪ subst_comp sigma c')).
  - (* sstepValuePairL *) intros n0 v1 v1' v2 s IH m sigma. simpl.
    apply sstepValuePairL. apply (IH m sigma).
  - (* sstepValuePairR *) intros n0 v1 v2 v2' s IH m sigma. simpl.
    apply sstepValuePairR. apply (IH m sigma).
  - (* sstepValueInj *) intros n0 b v v' s IH m sigma. simpl.
    apply sstepValueInj. apply (IH m sigma).
  - (* sstepValueThunk *) intros n0 c c' s IH m sigma. simpl.
    apply sstepValueThunk. apply (IH m sigma).
  - (* sstepForce *) intros n0 v v' s IH m sigma. simpl.
    apply sstepForce. apply (IH m sigma).
  - (* sstepLambda *) intros n0 c c' s IH m sigma. simpl.
    apply sstepLambda. apply (IH (S m) (up_value_value sigma)).
  - (* sstepAppL *) intros n0 c c' v s IH m sigma. simpl.
    apply sstepAppL. apply (IH m sigma).
  - (* sstepAppR *) intros n0 c v v' s IH m sigma. simpl.
    apply sstepAppR. apply (IH m sigma).
  - (* sstepTupleL *) intros n0 c1 c1' c2 s IH m sigma. simpl.
    apply sstepTupleL. apply (IH m sigma).
  - (* sstepTupleR *) intros n0 c1 c2 c2' s IH m sigma. simpl.
    apply sstepTupleR. apply (IH m sigma).
  - (* sstepRet *) intros n0 v v' s IH m sigma. simpl.
    apply sstepRet. apply (IH m sigma).
  - (* sstepLetinL *) intros n0 c1 c1' c2 s IH m sigma. simpl.
    apply sstepLetinL. apply (IH m sigma).
  - (* sstepLetinR *) intros n0 c1 c2 c2' s IH m sigma. simpl.
    apply sstepLetinR. apply (IH (S m) (up_value_value sigma)).
  - (* sstepProj *) intros n0 c c' b s IH m sigma. simpl.
    apply sstepProj. apply (IH m sigma).
  - (* sstepCaseZ *) intros n0 v v' s IH m sigma. simpl.
    apply sstepCaseZ. apply (IH m sigma).
  - (* sstepCaseSV *) intros n0 v v' c1 c2 s IH m sigma. simpl.
    apply sstepCaseSV. apply (IH m sigma).
  - (* sstepCaseSL *) intros n0 v c1 c1' c2 s IH m sigma. simpl.
    apply sstepCaseSL. apply (IH (S m) (up_value_value sigma)).
  - (* sstepCaseSR *) intros n0 v c1 c2 c2' s IH m sigma. simpl.
    apply sstepCaseSR. apply (IH (S m) (up_value_value sigma)).
  - (* sstepCasePV *) intros n0 v v' c s IH m sigma. simpl.
    apply sstepCasePV. apply (IH m sigma).
  - (* sstepCasePC *) intros n0 v c c' s IH m sigma. simpl.
    apply sstepCasePC. apply (IH (S (S m)) (up_value_value (up_value_value sigma))).
  - (* sstepPrimitive *) intros n0 c c' p m sigma. simpl.
    apply sstepPrimitive. apply pstep_subst_same. exact p.
Qed.

Lemma sstep_subst_same : forall n m (c c': comp n), c ↪ c' ->
  forall (sigma: fin n -> value m),
    subst_comp sigma c ↪ subst_comp sigma c'.
Proof.
  intros n m c c' H sigma. exact ((proj1 (sstep_subst_same_all n)) c c' H m sigma).
Qed.

Lemma sstep_value_subst_same : forall n m (v v': value n), v ↪ᵥ v' ->
  forall (sigma: fin n -> value m),
    subst_value sigma v ↪ᵥ subst_value sigma v'.
Proof.
  intros n m v v' H sigma. exact ((proj2 (sstep_subst_same_all n)) v v' H m sigma).
Qed.

(* ------------------------------------------------------------------ *)
(* Star closure under renaming                                         *)
(* ------------------------------------------------------------------ *)

Lemma star_sstep_value_ren : forall n m (v v': value n), star sstep_value v v' ->
  forall (xi: fin n -> fin m), star sstep_value (ren_value xi v) (ren_value xi v').
Proof.
  intros n m v v' H xi. induction H as [v|v v1 v2 Hs Hst IH].
  - apply starRefl.
  - eapply starStep with (x' := ren_value xi v1).
    + apply sstep_value_ren. exact Hs.
    + exact IH.
Qed.

(* ------------------------------------------------------------------ *)
(* Lifting a pointwise star through [up_value_value]                   *)
(* ------------------------------------------------------------------ *)

Lemma up_star_value : forall n m (sigma sigma': fin n -> value m),
  (forall i, star sstep_value (sigma i) (sigma' i)) ->
  forall i, star sstep_value (up_value_value sigma i) (up_value_value sigma' i).
Proof.
  intros n m sigma sigma' H i. destruct i as [j|].
  - cbn [up_value_value scons funcomp].
    apply star_sstep_value_ren. apply H.
  - cbn [up_value_value scons funcomp]. apply starRefl.
Qed.

(* ------------------------------------------------------------------ *)
(* Same-term substitution congruence at the star level                 *)
(* ------------------------------------------------------------------ *)


Fixpoint star_sstep_value_subst_same_term (n m: nat) (v: value n) {struct v} :
  (forall (sigma sigma': fin n -> value m),
    (forall i, star sstep_value (sigma i) (sigma' i)) ->
    star sstep_value (subst_value sigma v) (subst_value sigma' v))
with star_sstep_subst_same_term (n m: nat) (c: comp n) {struct c} :
  (forall (sigma sigma': fin n -> value m),
    (forall i, star sstep_value (sigma i) (sigma' i)) ->
    star sstep (subst_comp sigma c) (subst_comp sigma' c)).
Proof.
  - (* value *)
    intros sigma sigma' H. destruct v as [i| | v1 v2 | b v1 | c].
    + (* var_value *) simpl. apply H.
    + (* u *) simpl. apply starRefl.
    + (* pair *) simpl.
      eapply star_trans_g.
      * exact (sstep_star_fillv_true
                 (vctxPairL •__v (subst_value sigma v2))
                 (star_sstep_value_subst_same_term n m v1 sigma sigma' H)).
      * exact (sstep_star_fillv_true
                 (vctxPairR (subst_value sigma' v1) •__v)
                 (star_sstep_value_subst_same_term n m v2 sigma sigma' H)).
    + (* inj *) simpl.
      exact (sstep_star_fillv_true (vctxInj b •__v)
               (star_sstep_value_subst_same_term n m v1 sigma sigma' H)).
    + (* thunk *) simpl.
      exact (sstep_star_fillv_false (vctxThunk •__c)
               (star_sstep_subst_same_term n m c sigma sigma' H)).
  - (* comp *)
    intros sigma sigma' H.
    destruct c as [ | v | c0 | c0 v | c1 c2 | v | c1 c2 | b c0 | v
                   | v c1 c2 | v c0].
    + (* cu *) simpl. apply starRefl.
    + (* force *) simpl.
      exact (sstep_star_fillc_true (cctxForce •__v)
               (star_sstep_value_subst_same_term n m v sigma sigma' H)).
    + (* lambda *) simpl.
      exact (sstep_star_fillc_false (cctxLambda •__c)
               (star_sstep_subst_same_term (S n) (S m) c0
                  (up_value_value sigma) (up_value_value sigma')
                  (up_star_value sigma sigma' H))).
    + (* app *) simpl.
      eapply star_trans_g.
      * exact (sstep_star_fillc_false (cctxAppL •__c (subst_value sigma v))
                 (star_sstep_subst_same_term n m c0 sigma sigma' H)).
      * exact (sstep_star_fillc_true
                 (cctxAppR (subst_comp sigma' c0) •__v)
                 (star_sstep_value_subst_same_term n m v sigma sigma' H)).
    + (* tuple *) simpl.
      eapply star_trans_g.
      * exact (sstep_star_fillc_false
                 (cctxTupleL •__c (subst_comp sigma c2))
                 (star_sstep_subst_same_term n m c1 sigma sigma' H)).
      * exact (sstep_star_fillc_false
                 (cctxTupleR (subst_comp sigma' c1) •__c)
                 (star_sstep_subst_same_term n m c2 sigma sigma' H)).
    + (* ret *) simpl.
      exact (sstep_star_fillc_true (cctxRet •__v)
               (star_sstep_value_subst_same_term n m v sigma sigma' H)).
    + (* letin *) simpl.
      eapply star_trans_g.
      * exact (sstep_star_fillc_false
                 (cctxLetinL •__c (subst_comp (up_value_value sigma) c2))
                 (star_sstep_subst_same_term n m c1 sigma sigma' H)).
      * exact (sstep_star_fillc_false
                 (cctxLetinR (subst_comp sigma' c1) •__c)
                 (star_sstep_subst_same_term (S n) (S m) c2
                    (up_value_value sigma) (up_value_value sigma')
                    (up_star_value sigma sigma' H))).
    + (* proj *) simpl.
      exact (sstep_star_fillc_false (cctxProj b •__c)
               (star_sstep_subst_same_term n m c0 sigma sigma' H)).
    + (* caseZ *) simpl.
      exact (sstep_star_fillc_true (cctxCaseZ •__v)
               (star_sstep_value_subst_same_term n m v sigma sigma' H)).
    + (* caseS *) simpl.
      eapply star_trans_g.
      * exact (sstep_star_fillc_true
                 (cctxCaseSV •__v (subst_comp (up_value_value sigma) c1)
                    (subst_comp (up_value_value sigma) c2))
                 (star_sstep_value_subst_same_term n m v sigma sigma' H)).
      * eapply star_trans_g.
        -- exact (sstep_star_fillc_false
                    (cctxCaseSL (subst_value sigma' v) •__c
                       (subst_comp (up_value_value sigma) c2))
                    (star_sstep_subst_same_term (S n) (S m) c1
                       (up_value_value sigma) (up_value_value sigma')
                       (up_star_value sigma sigma' H))).
        -- exact (sstep_star_fillc_false
                    (cctxCaseSR (subst_value sigma' v)
                       (subst_comp (up_value_value sigma') c1) •__c)
                    (star_sstep_subst_same_term (S n) (S m) c2
                       (up_value_value sigma) (up_value_value sigma')
                       (up_star_value sigma sigma' H))).
    + (* caseP *) simpl.
      eapply star_trans_g.
      * exact (sstep_star_fillc_true
                 (cctxCasePV •__v
                    (subst_comp (up_value_value (up_value_value sigma)) c0))
                 (star_sstep_value_subst_same_term n m v sigma sigma' H)).
      * exact (sstep_star_fillc_false
                 (cctxCasePC (subst_value sigma' v) •__c)
                 (star_sstep_subst_same_term (S (S n)) (S (S m)) c0
                    (up_value_value (up_value_value sigma))
                    (up_value_value (up_value_value sigma'))
                    (up_star_value (up_value_value sigma) (up_value_value sigma')
                       (up_star_value sigma sigma' H)))).
Qed.

(* ------------------------------------------------------------------ *)
(* Related-substitution star invariance                                *)
(* ------------------------------------------------------------------ *)

Lemma star_sstep_subst : forall n m (c c': comp n), star sstep c c' ->
  forall (sigma sigma': fin n -> value m),
    (forall i, star sstep_value (sigma i) (sigma' i)) ->
    star sstep (subst_comp sigma c) (subst_comp sigma' c').
Proof.
  intros n m c c' H sigma sigma' HS. induction H as [c| c c1 c2 Hs Hst IH].
  - apply (star_sstep_subst_same_term c sigma sigma' HS).
  - refine (@star_trans_g (comp m) sstep
      (subst_comp sigma c) (subst_comp sigma c1) (subst_comp sigma' c2) _ _).
    + refine (@starStep (comp m) sstep
        (subst_comp sigma c) (subst_comp sigma c1) (subst_comp sigma c1)
        _ (@starRefl (comp m) sstep (subst_comp sigma c1))).
      apply sstep_subst_same. exact Hs.
    + exact IH.
Qed.

Lemma star_sstep_value_subst : forall n m (v v': value n), star sstep_value v v' ->
  forall (sigma sigma': fin n -> value m),
    (forall i, star sstep_value (sigma i) (sigma' i)) ->
    star sstep_value (subst_value sigma v) (subst_value sigma' v').
Proof.
  intros n m v v' H sigma sigma' HS. induction H as [v| v v1 v2 Hs Hst IH].
  - apply (star_sstep_value_subst_same_term v sigma sigma' HS).
  - refine (@star_trans_g (value m) sstep_value
      (subst_value sigma v) (subst_value sigma v1) (subst_value sigma' v2) _ _).
    + refine (@starStep (value m) sstep_value
        (subst_value sigma v) (subst_value sigma v1) (subst_value sigma v1)
        _ (@starRefl (value m) sstep_value (subst_value sigma v1))).
      apply sstep_value_subst_same. exact Hs.
    + exact IH.
Qed.

Set Implicit Arguments.
Require Import CBPV.ObservationalEquivalence CBPV.StrongReduction CBPV.AbstractReductionSystems.
Import CommaNotation.

(* Parallel strong reduction: one parallel step allows the unique primitive
   contraction at the head together with parallel reductions of all of its
   components, or a structural reduction of any constructor. *)

Inductive par {n: nat} : comp n -> comp n -> Prop :=
| par_cu : par cu cu
| par_force v v' : pval v v' -> par (force v) (force v')
| par_lambda c c' : par c c' -> par (lambda c) (lambda c')
| par_app c c' v v' : par c c' -> pval v v' -> par (c v) (c' v')
| par_tuple c1 c1' c2 c2' :
    par c1 c1' -> par c2 c2' -> par (tuple c1 c2) (tuple c1' c2')
| par_ret v v' : pval v v' -> par (ret v) (ret v')
| par_letin c1 c1' c2 c2' :
    par c1 c1' -> par c2 c2' -> par (letin c1 c2) (letin c1' c2')
| par_proj b c c' : par c c' -> par (proj b c) (proj b c')
| par_caseZ v v' : pval v v' -> par (caseZ v) (caseZ v')
| par_caseS v v' c1 c1' c2 c2' :
    pval v v' -> par c1 c1' -> par c2 c2' ->
    par (caseS v c1 c2) (caseS v' c1' c2')
| par_caseP v v' c c' :
    pval v v' -> par c c' -> par (caseP v c) (caseP v' c')
(* head primitive contractions with parallel-reduced components *)
| par_force_red c c' : par c c' -> par (force (thunk c)) c'
| par_app_red c c' v v' :
    par c c' -> pval v v' -> par (app (lambda c) v) (c'[v'..])
| par_proj_red b c1 c1' c2 c2' :
    par c1 c1' -> par c2 c2' ->
    par (proj b (tuple c1 c2)) (if b then c1' else c2')
| par_letin_red c c' v v' :
    par c c' -> pval v v' -> par (letin (ret v) c) (c'[v'..])
| par_caseS_red v v' b c1 c1' c2 c2' :
    pval v v' -> par c1 c1' -> par c2 c2' ->
    par (caseS (inj b v) c1 c2) ((if b then c1' else c2')[v'..])
| par_caseP_red v1 v1' v2 v2' c c' :
    pval v1 v1' -> pval v2 v2' -> par c c' ->
    par (caseP (pair v1 v2) c) (c'[v2',v1'..])
with pval {n: nat} : value n -> value n -> Prop :=
| pval_var i : pval (var_value i) (var_value i)
| pval_unit : pval u u
| pval_pair v1 v1' v2 v2' :
    pval v1 v1' -> pval v2 v2' -> pval (pair v1 v2) (pair v1' v2')
| pval_inj b v v' : pval v v' -> pval (inj b v) (inj b v')
| pval_thunk c c' : par c c' -> pval (thunk c) (thunk c').

(* Reflexivity *)
Fixpoint par_refl {n: nat} (c: comp n) {struct c} : par c c
with pval_refl {n: nat} (v: value n) {struct v} : pval v v.
Proof.
  - destruct c; simpl.
    + apply par_cu.
    + apply par_force. apply pval_refl.
    + apply par_lambda. apply par_refl.
    + apply par_app.
      * apply par_refl.
      * apply pval_refl.
    + apply par_tuple; apply par_refl.
    + apply par_ret. apply pval_refl.
    + apply par_letin; apply par_refl.
    + apply par_proj. apply par_refl.
    + apply par_caseZ. apply pval_refl.
    + apply par_caseS.
      * apply pval_refl.
      * apply par_refl.
      * apply par_refl.
    + apply par_caseP.
      * apply pval_refl.
      * apply par_refl.
  - destruct v; simpl.
    + apply pval_var.
    + apply pval_unit.
    + apply pval_pair; apply pval_refl.
    + apply pval_inj. apply pval_refl.
    + apply pval_thunk. apply par_refl.
Qed.

(* Every strong step is a parallel step. *)
Lemma sstep_to_par_all : forall n,
  (forall (c c': comp n), sstep c c' -> par c c') /\
  (forall (v v': value n), sstep_value v v' -> pval v v').
Proof.
  apply (mutind_sstep
    (fun n v v' _ => pval v v')
    (fun n c c' _ => par c c')).
  - (* sstepValuePairL *) intros n v1 v1' v2 s IH.
    apply pval_pair; [exact IH|apply pval_refl].
  - (* sstepValuePairR *) intros n v1 v2 v2' s IH.
    apply pval_pair; [apply pval_refl|exact IH].
  - (* sstepValueInj *) intros n b v v' s IH.
    apply pval_inj. exact IH.
  - (* sstepValueThunk *) intros n c c' s IH.
    apply pval_thunk. exact IH.
  - (* sstepForce *) intros n v v' s IH.
    apply par_force. exact IH.
  - (* sstepLambda *) intros n c c' s IH.
    apply par_lambda. exact IH.
  - (* sstepAppL *) intros n c c' v s IH.
    apply par_app; [exact IH|apply pval_refl].
  - (* sstepAppR *) intros n c v v' s IH.
    apply par_app; [apply par_refl|exact IH].
  - (* sstepTupleL *) intros n c1 c1' c2 s IH.
    apply par_tuple; [exact IH|apply par_refl].
  - (* sstepTupleR *) intros n c1 c2 c2' s IH.
    apply par_tuple; [apply par_refl|exact IH].
  - (* sstepRet *) intros n v v' s IH.
    apply par_ret. exact IH.
  - (* sstepLetinL *) intros n c1 c1' c2 s IH.
    apply par_letin; [exact IH|apply par_refl].
  - (* sstepLetinR *) intros n c1 c2 c2' s IH.
    apply par_letin; [apply par_refl|exact IH].
  - (* sstepProj *) intros n c c' b s IH.
    apply par_proj. exact IH.
  - (* sstepCaseZ *) intros n v v' s IH.
    apply par_caseZ. exact IH.
  - (* sstepCaseSV *) intros n v v' c1 c2 s IH.
    apply par_caseS; [exact IH|apply par_refl|apply par_refl].
  - (* sstepCaseSL *) intros n v c1 c1' c2 s IH.
    apply par_caseS; [apply pval_refl|exact IH|apply par_refl].
  - (* sstepCaseSR *) intros n v c1 c2 c2' s IH.
    apply par_caseS; [apply pval_refl|apply par_refl|exact IH].
  - (* sstepCasePV *) intros n v v' c s IH.
    apply par_caseP; [exact IH|apply par_refl].
  - (* sstepCasePC *) intros n v c c' s IH.
    apply par_caseP; [apply pval_refl|exact IH].
  - (* sstepPrimitive *) intros n c c' p.
    destruct p as [c0|c0 c' v E|b c0 c1 c2 E|c0 c' v E
                  |v b c0 c1 c2 E|v1 v2 c0 c' E].
    + apply par_force_red. apply par_refl.
    + rewrite <- E. apply par_app_red with (c':=c0) (v':=v).
      * apply par_refl.
      * apply pval_refl.
    + rewrite E. apply par_proj_red; apply par_refl.
    + rewrite <- E. apply par_letin_red with (c':=c0) (v':=v).
      * apply par_refl.
      * apply pval_refl.
    + rewrite <- E. apply par_caseS_red with (v':=v) (c1':=c1) (c2':=c2).
      * apply pval_refl.
      * apply par_refl.
      * apply par_refl.
    + rewrite <- E. apply par_caseP_red with (v1':=v1) (v2':=v2) (c':=c0).
      * apply pval_refl.
      * apply pval_refl.
      * apply par_refl.
Qed.

Lemma sstep_to_par {n} {c c': comp n} : sstep c c' -> par c c'.
Proof. intros H. exact (proj1 (sstep_to_par_all n) c c' H). Qed.

Lemma sstep_value_to_pval {n} {v v': value n} : sstep_value v v' -> pval v v'.
Proof. intros H. exact (proj2 (sstep_to_par_all n) v v' H). Qed.

Set Implicit Arguments.
Require Import CBPV.ObservationalEquivalence CBPV.StrongReduction CBPV.AbstractReductionSystems.
Import CommaNotation.

Scheme par_ind_2 := Induction for par Sort Prop
  with pval_ind_2 := Induction for pval Sort Prop.
Combined Scheme mutind_par from par_ind_2, pval_ind_2.

Lemma ren_comp_vcons {m k} (c: comp (S m)) (v: value m)
  (xi: fin m -> fin k) :
  ren_comp xi (subst_comp (scons v (@ids value VarInstance_value m)) c)
  = subst_comp (scons (ren_value xi v) (@ids value VarInstance_value k))
      (ren_comp (up_ren xi) c).
Proof.
  change (ren_comp xi (subst_comp (scons v (@ids value VarInstance_value m)) c)
    = subst_comp (scons (ren_value xi v) (@ids value VarInstance_value k))
        (ren_comp (up_ren xi) c)).
  rewrite subst_comp_ren.
  rewrite ren_comp_subst.
  apply subst_comp_congr.
  intros i. destruct i as [i|]; simpl.
  - cbv [scons up_ren funcomp bound shift]. reflexivity.
  - reflexivity.
Qed.

Lemma ren_value_vcons {m k} (c: comp m) (xi: fin m -> fin k) :
  ren_value xi (thunk c) = thunk (ren_comp xi c).
Proof. reflexivity. Qed.

Lemma ren_comp_vcons2 {m k} (c: comp (S (S m))) (v1 v2: value m)
  (xi: fin m -> fin k) :
  ren_comp xi (subst_comp (scons v2 (scons v1 (@ids value VarInstance_value m))) c)
  = subst_comp (scons (ren_value xi v2) (scons (ren_value xi v1) (@ids value VarInstance_value k)))
      (ren_comp (up_ren (up_ren xi)) c).
Proof.
  change (ren_comp xi
      (subst_comp (scons v2 (scons v1 (@ids value VarInstance_value m))) c)
    = subst_comp (scons (ren_value xi v2)
        (scons (ren_value xi v1) (@ids value VarInstance_value k)))
        (ren_comp (up_ren (up_ren xi)) c)).
  rewrite subst_comp_ren.
  rewrite ren_comp_subst.
  apply subst_comp_congr.
  intros i. destruct i as [i|]; [destruct i as [i|]|]; simpl; cbv [scons up_ren funcomp bound shift]; reflexivity.
Qed.

(* Renaming commutes with parallel reduction. *)
Lemma par_ren_all : forall n,
  (forall (c c': comp n), par c c' ->
    forall m (xi: fin n -> fin m), par (ren_comp xi c) (ren_comp xi c')) /\
  (forall (v v': value n), pval v v' ->
    forall m (xi: fin n -> fin m), pval (ren_value xi v) (ren_value xi v')).
Proof.
  apply mutind_par.
  - (* par_cu *) intros n m xi. simpl. apply par_cu.
  - (* par_force *) intros n v v' s IH m xi. simpl. apply par_force. apply IH.
  - (* par_lambda *) intros n c c' s IH m xi. simpl. apply par_lambda.
    apply IH.
  - (* par_app *) intros n c c' v v' s IHc sv IHv m xi. simpl.
    apply par_app; [apply IHc|apply IHv].
  - (* par_tuple *) intros n c1 c1' c2 c2' s1 IH1 s2 IH2 m xi. simpl.
    apply par_tuple; [apply IH1|apply IH2].
  - (* par_ret *) intros n v v' s IH m xi. simpl. apply par_ret. apply IH.
  - (* par_letin *) intros n c1 c1' c2 c2' s1 IH1 s2 IH2 m xi. simpl.
    apply par_letin; [apply IH1|apply IH2].
  - (* par_proj *) intros n b c c' s IH m xi. simpl. apply par_proj. apply IH.
  - (* par_caseZ *) intros n v v' s IH m xi. simpl. apply par_caseZ. apply IH.
  - (* par_caseS *) intros n v v' c1 c1' c2 c2' sv IHv s1 IH1 s2 IH2 m xi. simpl.
    apply par_caseS; [apply IHv|apply IH1|apply IH2].
  - (* par_caseP *) intros n v v' c c' sv IHv sc IHc m xi. simpl.
    apply par_caseP; [apply IHv|apply IHc].
  - (* par_force_red *) intros n c c' s IH m xi. simpl.
    apply par_force_red. apply IH.
  - (* par_app_red *) intros n c c' v v' sc IHc sv IHv m xi. simpl.
    rewrite ren_comp_vcons.
    apply par_app_red.
    + apply IHc.
    + apply IHv.
  - (* par_proj_red *) intros n b c1 c1' c2 c2' s1 IH1 s2 IH2 m xi. simpl.
    assert (Hif : ren_comp xi (if b then c1' else c2')
                  = (if b then ren_comp xi c1' else ren_comp xi c2'))
      by (destruct b; reflexivity).
    rewrite Hif. apply par_proj_red; [apply IH1|apply IH2].
  - (* par_letin_red *) intros n c c' v v' sc IHc sv IHv m xi. simpl.
    rewrite ren_comp_vcons.
    apply par_letin_red.
    + apply IHc.
    + apply IHv.
  - (* par_caseS_red *) intros n v v' b c1 c1' c2 c2' sv IHv s1 IH1 s2 IH2 m xi. simpl.
    rewrite ren_comp_vcons.
    assert (Hif : ren_comp (up_ren xi) (if b then c1' else c2')
                  = (if b then ren_comp (up_ren xi) c1' else ren_comp (up_ren xi) c2'))
      by (destruct b; reflexivity).
    rewrite Hif. apply par_caseS_red; [apply IHv|apply IH1|apply IH2].
  - (* par_caseP_red *) intros n v1 v1' v2 v2' c c' s1 IH1 s2 IH2 sc IHc m xi. simpl.
    rewrite ren_comp_vcons2.
    apply par_caseP_red; [apply IH1|apply IH2|apply IHc].
  - (* pval_var *) intros n i m xi. simpl. apply pval_var.
  - (* pval_unit *) intros n m xi. simpl. apply pval_unit.
  - (* pval_pair *) intros n v1 v1' v2 v2' s1 IH1 s2 IH2 m xi. simpl.
    apply pval_pair; [apply IH1|apply IH2].
  - (* pval_inj *) intros n b v v' s IH m xi. simpl. apply pval_inj. apply IH.
  - (* pval_thunk *) intros n c c' s IH m xi. simpl. apply pval_thunk. apply IH.
Qed.

Lemma par_ren {n m} {c c': comp n} (H: par c c') (xi: fin n -> fin m) :
  par (ren_comp xi c) (ren_comp xi c').
Proof. exact (proj1 (par_ren_all n) c c' H m xi). Qed.

Lemma pval_ren {n m} {v v': value n} (H: pval v v') (xi: fin n -> fin m) :
  pval (ren_value xi v) (ren_value xi v').
Proof. exact (proj2 (par_ren_all n) v v' H m xi). Qed.

(* Parallel reduction is stable under pointwise-parallel value substitution. *)
Lemma par_subst_all : forall n,
  (forall (c c': comp n), par c c' ->
     forall m (sigma sigma': fin n -> value m),
       (forall i, pval (sigma i) (sigma' i)) ->
       par (subst_comp sigma c) (subst_comp sigma' c')) /\
  (forall (v v': value n), pval v v' ->
     forall m (sigma sigma': fin n -> value m),
       (forall i, pval (sigma i) (sigma' i)) ->
       pval (subst_value sigma v) (subst_value sigma' v')).
Proof.
  apply (mutind_par
    (fun n c c' _ => forall m (sigma sigma': fin n -> value m),
       (forall i, pval (sigma i) (sigma' i)) ->
       par (subst_comp sigma c) (subst_comp sigma' c'))
    (fun n v v' _ => forall m (sigma sigma': fin n -> value m),
       (forall i, pval (sigma i) (sigma' i)) ->
       pval (subst_value sigma v) (subst_value sigma' v'))).
  - (* par_cu *) intros n m sigma sigma' H. simpl. apply par_cu.
  - (* par_force *) intros n v v' p IH m sigma sigma' H. simpl.
    apply par_force. apply (IH m sigma sigma' H).
  - (* par_lambda *) intros n c c' p IH m sigma sigma' H. simpl.
    apply par_lambda.
    apply (IH (S m) (up_value_value sigma) (up_value_value sigma')).
    intros i. destruct i as [i|]; simpl; [apply pval_ren; apply H|apply pval_var].
  - (* par_app *) intros n c c' v v' p IHp p0 IHv m sigma sigma' H. simpl.
    apply par_app; [apply (IHp m sigma sigma' H)|apply (IHv m sigma sigma' H)].
  - (* par_tuple *) intros n c1 c1' c2 c2' p1 IH1 p2 IH2 m sigma sigma' H. simpl.
    apply par_tuple; [apply (IH1 m sigma sigma' H)|apply (IH2 m sigma sigma' H)].
  - (* par_ret *) intros n v v' p IH m sigma sigma' H. simpl.
    apply par_ret. apply (IH m sigma sigma' H).
  - (* par_letin *) intros n c1 c1' c2 c2' p1 IH1 p2 IH2 m sigma sigma' H. simpl.
    apply par_letin.
    + apply (IH1 m sigma sigma' H).
    + apply (IH2 (S m) (up_value_value sigma) (up_value_value sigma')).
      intros i. destruct i as [i|]; simpl; [apply pval_ren; apply H|apply pval_var].
  - (* par_proj *) intros n b c c' p IH m sigma sigma' H. simpl.
    apply par_proj. apply (IH m sigma sigma' H).
  - (* par_caseZ *) intros n v v' p IH m sigma sigma' H. simpl.
    apply par_caseZ. apply (IH m sigma sigma' H).
  - (* par_caseS *) intros n v v' c1 c1' c2 c2' pv IHv p1 IH1 p2 IH2 m sigma sigma' H. simpl.
    apply par_caseS.
    + apply (IHv m sigma sigma' H).
    + apply (IH1 (S m) (up_value_value sigma) (up_value_value sigma')).
      intros i. destruct i as [i|]; simpl; [apply pval_ren; apply H|apply pval_var].
    + apply (IH2 (S m) (up_value_value sigma) (up_value_value sigma')).
      intros i. destruct i as [i|]; simpl; [apply pval_ren; apply H|apply pval_var].
  - (* par_caseP *) intros n v v' c c' pv IHv pc IHc m sigma sigma' H. simpl.
    apply par_caseP.
    + apply (IHv m sigma sigma' H).
    + apply (IHc (S (S m)) (up_value_value (up_value_value sigma))
                   (up_value_value (up_value_value sigma'))).
      intros i. destruct i as [i|]; [destruct i as [j|]|]; simpl;
        [ apply pval_ren; apply pval_ren; apply H
        | apply pval_var | apply pval_var ].
  - (* par_force_red *) intros n c c' p IH m sigma sigma' H. simpl.
    apply par_force_red. apply (IH m sigma sigma' H).
  - (* par_app_red *) intros n c c' v v' p IHp p0 IHv m sigma sigma' H. simpl.
    rewrite (subst_comp_vcons_raw c' v' sigma').
    rewrite <- (subst_comp_up_app c' sigma' (subst_value sigma' v')).
    apply par_app_red.
    + apply (IHp (S m) (up_value_value sigma) (up_value_value sigma')).
      intros i. destruct i as [i|]; simpl; [apply pval_ren; apply H|apply pval_var].
    + apply (IHv m sigma sigma' H).
  - (* par_proj_red *) intros n b c1 c1' c2 c2' p1 IH1 p2 IH2 m sigma sigma' H. simpl.
    assert (Hif : subst_comp sigma' (if b then c1' else c2')
                  = (if b then subst_comp sigma' c1' else subst_comp sigma' c2'))
      by (destruct b; reflexivity).
    rewrite Hif.
    apply par_proj_red; [apply (IH1 m sigma sigma' H)|apply (IH2 m sigma sigma' H)].
  - (* par_letin_red *) intros n c c' v v' p IHp p0 IHv m sigma sigma' H. simpl.
    rewrite (subst_comp_vcons_raw c' v' sigma').
    rewrite <- (subst_comp_up_app c' sigma' (subst_value sigma' v')).
    apply par_letin_red.
    + apply (IHp (S m) (up_value_value sigma) (up_value_value sigma')).
      intros i. destruct i as [i|]; simpl; [apply pval_ren; apply H|apply pval_var].
    + apply (IHv m sigma sigma' H).
  - (* par_caseS_red *) intros n v v' b c1 c1' c2 c2' pv IHv p1 IH1 p2 IH2 m sigma sigma' H. simpl.
    rewrite (subst_comp_vcons_raw (if b then c1' else c2') v' sigma').
    rewrite <- (subst_comp_up_app (if b then c1' else c2') sigma' (subst_value sigma' v')).
    assert (Hif : subst_comp (up_value_value sigma') (if b then c1' else c2')
                  = (if b then subst_comp (up_value_value sigma') c1'
                     else subst_comp (up_value_value sigma') c2'))
      by (destruct b; reflexivity).
    rewrite Hif.
    apply par_caseS_red.
    + apply (IHv m sigma sigma' H).
    + apply (IH1 (S m) (up_value_value sigma) (up_value_value sigma')).
      intros i. destruct i as [i|]; simpl; [apply pval_ren; apply H|apply pval_var].
    + apply (IH2 (S m) (up_value_value sigma) (up_value_value sigma')).
      intros i. destruct i as [i|]; simpl; [apply pval_ren; apply H|apply pval_var].
  - (* par_caseP_red *) intros n v1 v1' v2 v2' c c' p1 IH1 p2 IH2 pc IHc m sigma sigma' H. simpl.
    rewrite (subst_comp_vcons2_raw c' v1' v2' sigma').
    rewrite <- (subst_comp_up_up_caseP c' sigma' (subst_value sigma' v1') (subst_value sigma' v2')).
    apply par_caseP_red.
    + apply (IH1 m sigma sigma' H).
    + apply (IH2 m sigma sigma' H).
    + apply (IHc (S (S m)) (up_value_value (up_value_value sigma))
                   (up_value_value (up_value_value sigma'))).
      intros i. destruct i as [i|]; [destruct i as [j|]|]; simpl;
        [ apply pval_ren; apply pval_ren; apply H
        | apply pval_var | apply pval_var ].
  - (* pval_var *) intros n i m sigma sigma' H. simpl. apply H.
  - (* pval_unit *) intros n m sigma sigma' H. simpl. apply pval_unit.
  - (* pval_pair *) intros n v1 v1' v2 v2' p1 IH1 p2 IH2 m sigma sigma' H. simpl.
    apply pval_pair; [apply (IH1 m sigma sigma' H)|apply (IH2 m sigma sigma' H)].
  - (* pval_inj *) intros n b v v' p IH m sigma sigma' H. simpl.
    apply pval_inj. apply (IH m sigma sigma' H).
  - (* pval_thunk *) intros n c c' p IH m sigma sigma' H. simpl.
    apply pval_thunk. apply (IH m sigma sigma' H).
Qed.

Lemma par_subst {n m} {c c': comp n} (p: par c c')
  (sigma sigma': fin n -> value m) :
  (forall i, pval (sigma i) (sigma' i)) ->
  par (subst_comp sigma c) (subst_comp sigma' c').
Proof. intros H. exact (proj1 (par_subst_all n) c c' p m sigma sigma' H). Qed.

Lemma pval_subst {n m} {v v': value n} (p: pval v v')
  (sigma sigma': fin n -> value m) :
  (forall i, pval (sigma i) (sigma' i)) ->
  pval (subst_value sigma v) (subst_value sigma' v').
Proof. intros H. exact (proj2 (par_subst_all n) v v' p m sigma sigma' H). Qed.

Set Implicit Arguments.
Require Import CBPV.ObservationalEquivalence CBPV.StrongReduction CBPV.AbstractReductionSystems.
Import CommaNotation.

Lemma star_trans_par {X} (R:X->X->Prop) x y z :
  star R x y -> star R y z -> star R x z.
Proof. apply star_trans_g. Qed.

Lemma par_to_star_all : forall n,
  (forall (c c': comp n), par c c' -> star sstep c c') /\
  (forall (v v': value n), pval v v' -> star sstep_value v v').
Proof.
  apply (mutind_par
    (fun n c c' _ => star sstep c c')
    (fun n v v' _ => star sstep_value v v')).
  - (* par_cu *) intros n. apply starRefl.
  - (* par_force *) intros n v v' p IH.
    apply (@sstep_star_fillc_true n n (cctxForce (vctxHole true n I)) v v' IH).
  - (* par_lambda *) intros n c c' p IH.
    apply (@sstep_star_fillc_false n (S n) (cctxLambda (cctxHole false (S n) I)) c c' IH).
  - (* par_app *) intros n c c' v v' p IHp p0 IHv.
    eapply star_trans_par.
    + apply (@sstep_star_fillc_false n n (cctxAppL (cctxHole false n I) v) c c' IHp).
    + apply (@sstep_star_fillc_true n n (cctxAppR c' (vctxHole true n I)) v v' IHv).
  - (* par_tuple *) intros n c1 c1' c2 c2' p1 IH1 p2 IH2.
    eapply star_trans_par.
    + apply (@sstep_star_fillc_false n n (cctxTupleL (cctxHole false n I) c2) c1 c1' IH1).
    + apply (@sstep_star_fillc_false n n (cctxTupleR c1' (cctxHole false n I)) c2 c2' IH2).
  - (* par_ret *) intros n v v' p IH.
    apply (@sstep_star_fillc_true n n (cctxRet (vctxHole true n I)) v v' IH).
  - (* par_letin *) intros n c1 c1' c2 c2' p1 IH1 p2 IH2.
    eapply star_trans_par.
    + apply (@sstep_star_fillc_false n n (cctxLetinL (cctxHole false n I) c2) c1 c1' IH1).
    + apply (@sstep_star_fillc_false n (S n) (cctxLetinR c1' (cctxHole false (S n) I)) c2 c2' IH2).
  - (* par_proj *) intros n b c c' p IH.
    apply (@sstep_star_fillc_false n n (cctxProj b (cctxHole false n I)) c c' IH).
  - (* par_caseZ *) intros n v v' p IH.
    apply (@sstep_star_fillc_true n n (cctxCaseZ (vctxHole true n I)) v v' IH).
  - (* par_caseS *) intros n v v' c1 c1' c2 c2' pv IHv p1 IH1 p2 IH2.
    eapply star_trans_par; [|
    eapply star_trans_par].
    + apply (@sstep_star_fillc_true n n (cctxCaseSV (vctxHole true n I) c1 c2) v v' IHv).
    + apply (@sstep_star_fillc_false n (S n) (cctxCaseSL v' (cctxHole false (S n) I) c2) c1 c1' IH1).
    + apply (@sstep_star_fillc_false n (S n) (cctxCaseSR v' c1' (cctxHole false (S n) I)) c2 c2' IH2).
  - (* par_caseP *) intros n v v' c c' pv IHv pc IHc.
    eapply star_trans_par.
    + apply (@sstep_star_fillc_true n n (cctxCasePV (vctxHole true n I) c) v v' IHv).
    + apply (@sstep_star_fillc_false n (S (S n)) (cctxCasePC v' (cctxHole false (S (S n)) I)) c c' IHc).
  - (* par_force_red *) intros n c c' p IH.
    eapply starStep.
    + apply sstepPrimitive. apply pstepForce.
    + exact IH.
  - (* par_app_red *) intros n c c' v v' p IHp p0 IHv.
    eapply starStep.
    + apply sstepPrimitive. apply (@pstepApp n c (c[v..]) v eq_refl).
    + apply (@star_sstep_subst (S n) n c c' IHp
        (scons v (@ids value VarInstance_value n))
        (scons v' (@ids value VarInstance_value n))).
      intros i. destruct i as [i|]; simpl.
      * apply starRefl.
      * exact IHv.
  - (* par_proj_red *) intros n b c1 c1' c2 c2' p1 IH1 p2 IH2.
    eapply starStep.
    + apply sstepPrimitive.
      apply (@pstepProj n b (if b then c1 else c2) c1 c2 eq_refl).
    + destruct b; simpl; [exact IH1|exact IH2].
  - (* par_letin_red *) intros n c c' v v' p IHp p0 IHv.
    eapply starStep.
    + apply sstepPrimitive. apply (@pstepLetin n c (c[v..]) v eq_refl).
    + apply (@star_sstep_subst (S n) n c c' IHp
        (scons v (@ids value VarInstance_value n))
        (scons v' (@ids value VarInstance_value n))).
      intros i. destruct i as [i|]; simpl.
      * apply starRefl.
      * exact IHv.
  - (* par_caseS_red *) intros n v v' b c1 c1' c2 c2' pv IHv p1 IH1 p2 IH2.
    eapply starStep.
    + apply sstepPrimitive.
      apply (@pstepCaseS n v b ((if b then c1 else c2)[v..]) c1 c2 eq_refl).
    + apply (@star_sstep_subst (S n) n (if b then c1 else c2)
        (if b then c1' else c2')).
      * destruct b; simpl; [exact IH1|exact IH2].
      * intros i. destruct i as [i|]; simpl.
        -- apply starRefl.
        -- exact IHv.
  - (* par_caseP_red *) intros n v1 v1' v2 v2' c c' p1 IH1 p2 IH2 pc IHc.
    eapply starStep.
    + apply sstepPrimitive.
      apply (@pstepCaseP n v1 v2 c (c[v2,v1..]) eq_refl).
    + apply (@star_sstep_subst (S (S n)) n c c' IHc
        (scons v2 (scons v1 (@ids value VarInstance_value n)))
        (scons v2' (scons v1' (@ids value VarInstance_value n)))).
      intros i. destruct i as [i|]; [destruct i as [j|]|]; simpl.
      * apply starRefl.
      * exact IH1.
      * exact IH2.
  - (* pval_var *) intros n i. apply starRefl.
  - (* pval_unit *) intros n. apply starRefl.
  - (* pval_pair *) intros n v1 v1' v2 v2' p1 IH1 p2 IH2.
    eapply star_trans_par.
    + apply (@sstep_star_fillv_true n n (vctxPairL (vctxHole true n I) v2) v1 v1' IH1).
    + apply (@sstep_star_fillv_true n n (vctxPairR v1' (vctxHole true n I)) v2 v2' IH2).
  - (* pval_inj *) intros n b v v' p IH.
    apply (@sstep_star_fillv_true n n (vctxInj b (vctxHole true n I)) v v' IH).
  - (* pval_thunk *) intros n c c' p IH.
    apply (@sstep_star_fillv_false n n (vctxThunk (cctxHole false n I)) c c' IH).
Qed.

Lemma par_to_star {n} {c c': comp n} : par c c' -> star sstep c c'.
Proof. intros H. exact (proj1 (par_to_star_all n) c c' H). Qed.

Lemma pval_to_star {n} {v v': value n} : pval v v' -> star sstep_value v v'.
Proof. intros H. exact (proj2 (par_to_star_all n) v v' H). Qed.

Set Implicit Arguments.
Require Import CBPV.AbstractReductionSystems.

(* [equiv] was declared with an automatically implicit type argument.  Make
   the type explicit so that it can be written [equiv X R x y] as required. *)
Arguments equiv : clear implicits.

(* Transitivity of the reflexive-transitive closure. *)
Lemma ars_star_trans_g : forall {X} (R:X->X->Prop) x y z,
  star R x y -> star R y z -> star R x z.
Proof.
  intros X R x y z Hxy.
  revert z.
  induction Hxy as [x | x x' y Hr Hs IH].
  - intros z Hz. exact Hz.
  - intros z Hz. eapply starStep; [exact Hr | apply IH; exact Hz].
Qed.

(* Every element is joinable with itself. *)
Lemma joinable_refl : forall {X} (R:X->X->Prop) x,
  joinable (star R) x x.
Proof.
  intros X R x.
  exists x.
  - apply starRefl.
  - apply starRefl.
Qed.

(* Joinability is symmetric. *)
Lemma joinable_sym : forall {X} (R:X->X->Prop) x y,
  joinable (star R) x y -> joinable (star R) y x.
Proof.
  intros X R x y [z Hx Hy].
  exists z.
  - exact Hy.
  - exact Hx.
Qed.

(* If R is diamond, then R is semi-confluent (one step versus many steps). *)
Lemma diamond_semi : forall {X} (R:X->X->Prop),
  diamond R -> semi_confluent R.
Proof.
  intros X R Hd x y z Hxy Hxz.
  revert y Hxy.
  induction Hxz as [x | x q z Hxq Hqz IH].
  - intros y Hxy.
    exists y.
    + apply starRefl.
    + eapply starStep; [exact Hxy | apply starRefl].
  - intros y Hxy.
    destruct (Hd x y q Hxy Hxq) as [w Hyw Hqw].
    destruct (IH w Hqw) as [v Hwv Hzv].
    exists v.
    + eapply ars_star_trans_g.
      * eapply starStep; [exact Hyw | apply starRefl].
      * exact Hwv.
    + exact Hzv.
Qed.

(* Semi-confluence implies confluence. *)
Lemma semi_confluent_confluent : forall {X} (R:X->X->Prop),
  semi_confluent R -> confluent R.
Proof.
  intros X R Hs x y z Hxy.
  revert z.
  induction Hxy as [x | x x' y Hr Hxy' IH].
  - intros z Hxz.
    exists z.
    + exact Hxz.
    + apply starRefl.
  - intros z Hxz.
    destruct (Hs x x' z Hr Hxz) as [w Hx'w Hzw].
    destruct (IH w Hx'w) as [v Hyv Hwv].
    exists v.
    + exact Hyv.
    + eapply ars_star_trans_g; [exact Hzw | exact Hwv].
Qed.

(* Main corollary: the diamond property implies confluence. *)
Lemma diamond_confluent : forall {X} (R:X->X->Prop),
  diamond R -> confluent R.
Proof.
  intros X R Hd.
  apply semi_confluent_confluent.
  apply diamond_semi.
  exact Hd.
Qed.

(* Joinability is transitive under confluence. *)
Lemma joinable_trans : forall {X} (R:X->X->Prop),
  confluent R -> forall x y z,
  joinable (star R) x y -> joinable (star R) y z -> joinable (star R) x z.
Proof.
  intros X R Hc x y z [u Hxu Hyu] [v Hyv Hzv].
  destruct (Hc y u v Hyu Hyv) as [w Huw Hvw].
  exists w.
  - eapply ars_star_trans_g; [exact Hxu | exact Huw].
  - eapply ars_star_trans_g; [exact Hzv | exact Hvw].
Qed.

(* sym R is symmetric. *)
Lemma sym_sym : forall {X} (R:X->X->Prop) x y,
  sym R x y -> sym R y x.
Proof.
  intros X R x y H.
  destruct H as [x y H | x y H].
  - apply symInv. exact H.
  - apply symId. exact H.
Qed.

(* Star of a symmetric relation is symmetric. *)
Lemma star_equiv_sym : forall {X} (R:X->X->Prop) x y,
  star (sym R) x y -> star (sym R) y x.
Proof.
  intros X R x y H.
  induction H as [x | x x' y Hs Hrest IH].
  - apply starRefl.
  - eapply ars_star_trans_g; [exact IH |].
    eapply starStep; [apply sym_sym; exact Hs | apply starRefl].
Qed.

(* Every R-step is an equivalence step. *)
Lemma star_to_equiv : forall {X} (R:X->X->Prop) x y,
  star R x y -> equiv X R x y.
Proof.
  intros X R x y H.
  unfold equiv.
  induction H as [x | x x' y Hr Hrest IH].
  - apply starRefl.
  - eapply ars_star_trans_g.
    + eapply starStep; [apply symId; exact Hr | apply starRefl].
    + exact IH.
Qed.

(* A symmetric step yields joinability. *)
Lemma sym_joinable : forall {X} (R:X->X->Prop) x y,
  sym R x y -> joinable (star R) x y.
Proof.
  intros X R x y H.
  destruct H as [x y H | x y H].
  - exists y.
    + eapply starStep; [exact H | apply starRefl].
    + apply starRefl.
  - exists x.
    + apply starRefl.
    + eapply starStep; [exact H | apply starRefl].
Qed.

(* Under confluence, equivalence implies joinability. *)
Lemma equiv_joinable : forall {X} (R:X->X->Prop),
  confluent R -> forall x y, equiv X R x y -> joinable (star R) x y.
Proof.
  intros X R Hc x y H.
  unfold equiv in H.
  induction H as [x | x x' y Hs Hrest IH].
  - apply joinable_refl.
  - eapply joinable_trans;
      [exact Hc | apply sym_joinable; exact Hs | exact IH].
Qed.

(* Conversely, joinability implies equivalence (no confluence needed). *)
Lemma confluent_equiv_joinable_rev : forall {X} (R:X->X->Prop) x y,
  joinable (star R) x y -> equiv X R x y.
Proof.
  intros X R x y [z Hxz Hyz].
  unfold equiv.
  eapply ars_star_trans_g.
  - apply star_to_equiv. exact Hxz.
  - apply star_equiv_sym. apply star_to_equiv. exact Hyz.
Qed.

Print Assumptions ars_star_trans_g.
Print Assumptions diamond_confluent.
Print Assumptions joinable_refl.
Print Assumptions joinable_sym.
Print Assumptions joinable_trans.
Print Assumptions equiv_joinable.
Print Assumptions confluent_equiv_joinable_rev.

Set Implicit Arguments.
Require Import CBPV.ObservationalEquivalence CBPV.StrongReduction CBPV.AbstractReductionSystems.
Arguments equiv : clear implicits.

Lemma star_sstep_to_par {n} {c d: comp n} :
  star sstep c d -> star par c d.
Proof.
  intros H. induction H as [c|c c1 d Hs Hst IH].
  - apply starRefl.
  - eapply starStep with (x' := c1).
    + apply sstep_to_par. exact Hs.
    + exact IH.
Qed.

Lemma star_par_to_sstep {n} {c d: comp n} :
  star par c d -> star sstep c d.
Proof.
  intros H. induction H as [c|c c1 d Hs Hst IH].
  - apply starRefl.
  - eapply star_trans_g with (y := c1).
    + apply par_to_star. exact Hs.
    + exact IH.
Qed.

Lemma confluent_sstep_from_par : forall n, diamond (@par n) -> confluent (@sstep n).
Proof.
  intros n PDn x y z Hxy Hxz.
  pose proof (diamond_confluent (R := @par n) PDn) as HC.
  destruct (HC x y z (star_sstep_to_par Hxy) (star_sstep_to_par Hxz))
    as [w Hyw Hzw].
  exists w; apply star_par_to_sstep; assumption.
Qed.

(* Flatten a two-level star. *)
Lemma star_star_flat {X: Type} (R: X -> X -> Prop) :
  forall x y, star (star R) x y -> star R x y.
Proof.
  intros x y H. induction H as [x|x x' y Hx Hst IH].
  - apply starRefl.
  - eapply star_trans_g; [exact Hx|exact IH].
Qed.

Lemma equiv_joinable_sstep : forall n (PDn: diamond (@par n)) (x y: comp n),
  equiv (comp n) (@sstep n) x y ->
  exists z, star sstep x z /\ star sstep y z.
Proof.
  intros n PDn x y HE.
  destruct (@equiv_joinable (comp n) (@sstep n)
              (confluent_sstep_from_par (n:=n) PDn) x y HE) as [z Hx Hy].
  exists z. split; assumption.
Qed.

Set Implicit Arguments.
Require Import CBPV.ObservationalEquivalence CBPV.StrongReduction CBPV.AbstractReductionSystems.
Import CommaNotation.

(* ------------------------------------------------------------------ *)
(* Inversion lemmas for the second parallel-reduction derivation.      *)
(* ------------------------------------------------------------------ *)

Lemma par_cu_inv {n} {c2: comp n} (H: par cu c2) : c2 = cu.
Proof. inversion H; subst; reflexivity. Qed.

Lemma par_force_inv {n} {v: value n} {c2: comp n} (H: par (force v) c2) :
  (exists v', c2 = force v' /\ pval v v') \/
  (exists c c', c2 = c' /\ v = thunk c /\ par c c').
Proof. inversion H; subst; eauto 10. Qed.

Lemma par_lambda_inv {n} {c: comp (S n)} {c2: comp n} (H: par (lambda c) c2) :
  exists c', c2 = lambda c' /\ par c c'.
Proof. inversion H; subst; eauto 10. Qed.

Lemma par_app_inv {n} {c: comp n} {v: value n} {c2: comp n}
  (H: par (app c v) c2) :
  (exists c' v', c2 = app c' v' /\ par c c' /\ pval v v') \/
  (exists c0 c0' v0', c = lambda c0 /\ c2 = c0'[v0'..] /\ par c0 c0' /\ pval v v0').
Proof. inversion H; subst; eauto 10. Qed.

Lemma par_tuple_inv {n} {c1 c2: comp n} {c3: comp n}
  (H: par (tuple c1 c2) c3) :
  exists c1' c2', c3 = tuple c1' c2' /\ par c1 c1' /\ par c2 c2'.
Proof. inversion H; subst; eauto 10. Qed.

Lemma par_ret_inv {n} {v: value n} {c2: comp n} (H: par (ret v) c2) :
  exists v', c2 = ret v' /\ pval v v'.
Proof. inversion H; subst; eauto 10. Qed.

Lemma par_letin_inv {n} {c1: comp n} {c2: comp (S n)} {c3: comp n}
  (H: par (letin c1 c2) c3) :
  (exists c1' c2', c3 = letin c1' c2' /\ par c1 c1' /\ par c2 c2') \/
  (exists v c0' v', c1 = ret v /\ c3 = c0'[v'..] /\ par c2 c0' /\ pval v v').
Proof. inversion H; subst; eauto 10. Qed.

Lemma par_proj_inv {n} {b: bool} {c: comp n} {c2: comp n}
  (H: par (proj b c) c2) :
  (exists c', c2 = proj b c' /\ par c c') \/
  (exists c1 c2c c1' c2', c = tuple c1 c2c /\ c2 = (if b then c1' else c2')
     /\ par c1 c1' /\ par c2c c2').
Proof. inversion H; subst; eauto 10. Qed.

Lemma par_caseZ_inv {n} {v: value n} {c2: comp n} (H: par (caseZ v) c2) :
  exists v', c2 = caseZ v' /\ pval v v'.
Proof. inversion H; subst; eauto 10. Qed.

Lemma par_caseS_inv {n} {v: value n} {c1 c2: comp (S n)} {c3: comp n}
  (H: par (caseS v c1 c2) c3) :
  (exists v' c1' c2', c3 = caseS v' c1' c2' /\ pval v v' /\ par c1 c1' /\ par c2 c2') \/
  (exists v0 v0' b c1' c2', v = inj b v0 /\ c3 = (if b then c1' else c2')[v0'..]
     /\ pval v0 v0' /\ par c1 c1' /\ par c2 c2').
Proof.
  inversion H; subst.
  - left. eauto 10.
  - right. eauto 10.
Qed.

Lemma par_caseP_inv {n} {v: value n} {c: comp (S (S n))} {c3: comp n}
  (H: par (caseP v c) c3) :
  (exists v' c', c3 = caseP v' c' /\ pval v v' /\ par c c') \/
  (exists v1 v2 v1' v2' c', v = pair v1 v2 /\ c3 = c'[v2',v1'..]
     /\ pval v1 v1' /\ pval v2 v2' /\ par c c').
Proof.
  inversion H; subst.
  - left. eauto 10.
  - right. eauto 10.
Qed.

(* Specialised inversion lemmas for the six head-redex source shapes. *)

Lemma par_force_thunk_inv {n} {c: comp n} {c2: comp n}
  (H: par (force (thunk c)) c2) :
  (exists v', c2 = force v' /\ pval (thunk c) v') \/
  (exists c', c2 = c' /\ par c c').
Proof.
  inversion H; subst.
  - left. eauto 10.
  - right. eauto 10.
Qed.

Lemma par_app_lambda_inv {n} {c: comp (S n)} {v: value n} {c2: comp n}
  (H: par (app (lambda c) v) c2) :
  (exists cT vT, c2 = app cT vT /\ par (lambda c) cT /\ pval v vT) \/
  (exists c' v', c2 = c'[v'..] /\ par c c' /\ pval v v').
Proof.
  inversion H; subst.
  - left. eauto 10.
  - right. eauto 10.
Qed.

Lemma par_proj_tuple_inv {n} {b: bool} {c1 c2: comp n} {c3: comp n}
  (H: par (proj b (tuple c1 c2)) c3) :
  (exists c', c3 = proj b c' /\ par (tuple c1 c2) c') \/
  (exists c1' c2', c3 = (if b then c1' else c2') /\ par c1 c1' /\ par c2 c2').
Proof.
  inversion H; subst.
  - left. eauto 10.
  - right. eauto 10.
Qed.

Lemma par_letin_ret_inv {n} {c: comp (S n)} {v: value n} {c3: comp n}
  (H: par (letin (ret v) c) c3) :
  (exists c1' c2', c3 = letin c1' c2' /\ par (ret v) c1' /\ par c c2') \/
  (exists c' v', c3 = c'[v'..] /\ par c c' /\ pval v v').
Proof.
  inversion H; subst.
  - left. eauto 10.
  - right. eauto 10.
Qed.

Lemma par_caseS_inj_inv {n} {v: value n} {b: bool} {c1 c2: comp (S n)} {c3: comp n}
  (H: par (caseS (inj b v) c1 c2) c3) :
  (exists vT c1' c2', c3 = caseS vT c1' c2' /\ pval (inj b v) vT
     /\ par c1 c1' /\ par c2 c2') \/
  (exists v' c1' c2', c3 = (if b then c1' else c2')[v'..] /\ pval v v'
     /\ par c1 c1' /\ par c2 c2').
Proof.
  inversion H; subst.
  - left. eauto 10.
  - right. eauto 10.
Qed.

Lemma par_caseP_pair_inv {n} {v1 v2: value n} {c: comp (S (S n))} {c3: comp n}
  (H: par (caseP (pair v1 v2) c) c3) :
  (exists vT c', c3 = caseP vT c' /\ pval (pair v1 v2) vT /\ par c c') \/
  (exists v1' v2' c', c3 = c'[v2',v1'..] /\ pval v1 v1' /\ pval v2 v2' /\ par c c').
Proof.
  inversion H; subst.
  - left. eauto 10.
  - right. eauto 10.
Qed.

(* Inversion lemmas for pval. *)

Lemma pval_var_inv {n} {i: fin n} {v2: value n} (H: pval (var_value i) v2) :
  v2 = var_value i.
Proof. inversion H; subst; reflexivity. Qed.

Lemma pval_unit_inv {n} {v2: value n} (H: pval u v2) : v2 = u.
Proof. inversion H; subst; reflexivity. Qed.

Lemma pval_pair_inv {n} {v1 v2: value n} {v3: value n}
  (H: pval (pair v1 v2) v3) :
  exists v1' v2', v3 = pair v1' v2' /\ pval v1 v1' /\ pval v2 v2'.
Proof. inversion H; subst; eauto 10. Qed.

Lemma pval_inj_inv {n} {b: bool} {v: value n} {v2: value n}
  (H: pval (inj b v) v2) :
  exists v', v2 = inj b v' /\ pval v v'.
Proof. inversion H; subst; eauto 10. Qed.

Lemma pval_thunk_inv {n} {c: comp n} {v2: value n} (H: pval (thunk c) v2) :
  exists c', v2 = thunk c' /\ par c c'.
Proof. inversion H; subst; eauto 10. Qed.

Lemma pval_to_thunk {n} {v: value n} {c': comp n} (H: pval v (thunk c')) :
  exists c, v = thunk c /\ par c c'.
Proof. inversion H; subst; eauto 10. Qed.

(* ------------------------------------------------------------------ *)
(* Small helpers.                                                      *)
(* ------------------------------------------------------------------ *)

Lemma par_if {n} (b: bool) {c1 c1' c2 c2': comp n} :
  par c1 c1' -> par c2 c2' -> par (if b then c1 else c2) (if b then c1' else c2').
Proof. intros H1 H2. destruct b; simpl; assumption. Qed.

Lemma pval_scons_ids {n} (v v': value n) :
  pval v v' ->
  forall i, pval (scons v (@ids value VarInstance_value n) i)
              (scons v' (@ids value VarInstance_value n) i).
Proof.
  intros H [j|]; simpl; [apply pval_var | exact H].
Qed.

Lemma pval_scons2_ids {n} (a a' b b': value n) :
  pval a a' -> pval b b' ->
  forall i, pval (scons a (scons b (@ids value VarInstance_value n)) i)
              (scons a' (scons b' (@ids value VarInstance_value n)) i).
Proof.
  intros Ha Hb [j|]; [destruct j as [k|]|]; simpl; auto using pval_var.
Qed.

(* ------------------------------------------------------------------ *)
(* The diamond property.                                               *)
(* ------------------------------------------------------------------ *)

Lemma par_diamond_all : forall n,
  (forall (c c1: comp n), par c c1 -> forall (c2: comp n), par c c2 ->
     exists c3, par c1 c3 /\ par c2 c3) /\
  (forall (v v1: value n), pval v v1 -> forall (v2: value n), pval v v2 ->
     exists v3, pval v1 v3 /\ pval v2 v3).
Proof.
  apply (mutind_par
    (fun n c c1 _ => forall c2, par c c2 -> exists c3, par c1 c3 /\ par c2 c3)
    (fun n v v1 _ => forall v2, pval v v2 -> exists v3, pval v1 v3 /\ pval v2 v3)).
  - (* par_cu *)
    intros n cT Hdq. apply par_cu_inv in Hdq. subst.
    exists cu. split; apply par_cu.
  - (* par_force *)
    intros n v v' pv IHpv cT Hdq.
    destruct (par_force_inv Hdq) as [(v2 & (E & pv2)) | (c0 & (c0' & (E & (Ev & p))))]; subst.
    + destruct (IHpv v2 pv2) as (v3 & (H1 & H2)).
      exists (force v3). split; apply par_force; assumption.
    + destruct (IHpv (thunk c0') (pval_thunk p)) as (v3 & (H1 & H2)).
      destruct (pval_thunk_inv H2) as (c3 & (E3 & p3)); subst.
      destruct (pval_to_thunk H1) as (c4 & (E4 & p4)); subst.
      exists c3. split.
      * apply par_force_red. exact p4.
      * exact p3.
  - (* par_lambda *)
    intros n c c' p IHp cT Hdq.
    destruct (par_lambda_inv Hdq) as (d & (E & q)); subst.
    destruct (IHp d q) as (c3 & (H1 & H2)).
    exists (lambda c3). split; apply par_lambda; assumption.
  - (* par_app *)
    intros n c c' v v' pc IHpc pv IHpv cT Hdq.
    destruct (par_app_inv Hdq) as [(cW & (vW & (E & (pW & qW)))) | (c0 & (c0' & (v0' & (Ec & (E2 & (pc0 & pv0'))))))]; subst.
    + destruct (IHpc cW pW) as (c3 & (H1 & H2)).
      destruct (IHpv vW qW) as (v3 & (H3 & H4)).
      exists (app c3 v3). split; apply par_app; assumption.
    + inversion pc; subst.
      destruct (IHpc (lambda c0') (par_lambda pc0)) as (c3 & (H1 & H2)).
      destruct (par_lambda_inv H2) as (cB & (E2 & pB)); subst c3.
      destruct (par_lambda_inv H1) as (cB' & (E1 & pAB)). injection E1 as E1. subst cB'.
      destruct (IHpv v0' pv0') as (v3 & (H3 & H4)).
      exists (cB[v3..]). split.
      * apply par_app_red; assumption.
      * apply (par_subst pB (scons v0' (@ids value VarInstance_value n))
                   (scons v3 (@ids value VarInstance_value n))).
        apply pval_scons_ids. exact H4.
  - (* par_tuple *)
    intros n c1 c1' c2 c2' p1 IH1 p2 IH2 cT Hdq.
    destruct (par_tuple_inv Hdq) as (d1 & (d2 & (E & (q1 & q2)))); subst.
    destruct (IH1 d1 q1) as (e1 & (H1 & H2)).
    destruct (IH2 d2 q2) as (e2 & (H3 & H4)).
    exists (tuple e1 e2). split; apply par_tuple; assumption.
  - (* par_ret *)
    intros n v v' pv IHpv cT Hdq.
    destruct (par_ret_inv Hdq) as (v2 & (E & pv2)); subst.
    destruct (IHpv v2 pv2) as (v3 & (H1 & H2)).
    exists (ret v3). split; apply par_ret; assumption.
  - (* par_letin *)
    intros n c1 c1' c2 c2' p1 IH1 p2 IH2 cT Hdq.
    destruct (par_letin_inv Hdq) as [(d1 & (d2 & (E & (q1 & q2)))) | (v & (c0' & (v' & (E1 & (E3 & (q & pv))))))]; subst.
    + destruct (IH1 d1 q1) as (e1 & (H1 & H2)).
      destruct (IH2 d2 q2) as (e2 & (H3 & H4)).
      exists (letin e1 e2). split; apply par_letin; assumption.
    + destruct (par_ret_inv p1) as (vT & (E1' & pvT)); subst c1'.
      destruct (IH1 (ret v') (par_ret pv)) as (c3 & (H1 & H2)).
      destruct (par_ret_inv H2) as (v3 & (E3' & pvv3)); subst c3.
      destruct (par_ret_inv H1) as (v3' & (E4 & pvT3)). injection E4 as E4. subst v3'.
      destruct (IH2 c0' q) as (c4 & (H3 & H4)).
      exists (c4[v3..]). split.
      * apply par_letin_red; assumption.
      * apply (par_subst H4 (scons v' (@ids value VarInstance_value n))
                   (scons v3 (@ids value VarInstance_value n))).
        apply pval_scons_ids. exact pvv3.
  - (* par_proj *)
    intros n b c c' p IHp cT Hdq.
    destruct (par_proj_inv Hdq) as [(d & (E & q)) | (a1 & (a2 & (d1 & (d2 & (Ec & (E2 & (q1 & q2)))))))]; subst.
    + destruct (IHp d q) as (c3 & (H1 & H2)).
      exists (proj b c3). split; apply par_proj; assumption.
    + destruct (IHp (tuple d1 d2) (par_tuple q1 q2)) as (c3 & (H1 & H2)).
      destruct (par_tuple_inv H2) as (e1 & (e2 & (E2' & (r1 & r2)))); subst c3.
      destruct (par_tuple_inv p) as (f1 & (f2 & (Ep & (s1 & s2)))); subst c'.
      destruct (par_tuple_inv H1) as (g1 & (g2 & (Eg & (t1 & t2)))). injection Eg as Eg. subst g1 g2.
      exists (if b then e1 else e2). split.
      * apply par_proj_red; assumption.
      * apply par_if; assumption.
  - (* par_caseZ *)
    intros n v v' pv IHpv cT Hdq.
    destruct (par_caseZ_inv Hdq) as (v2 & (E & pv2)); subst.
    destruct (IHpv v2 pv2) as (v3 & (H1 & H2)).
    exists (caseZ v3). split; apply par_caseZ; assumption.
  - (* par_caseS *)
    intros n v v' c1 c1' c2 c2' pv IHpv p1 IH1 p2 IH2 cT Hdq.
    destruct (par_caseS_inv Hdq) as [(w & (d1 & (d2 & (E & (pw & (q1 & q2)))))) | (v0 & (v0' & (b0 & (d1 & (d2 & (Ev & (E3 & (pvv & (q1 & q2)))))))))]; subst.
    + destruct (IHpv w pw) as (v3 & (H1 & H2)).
      destruct (IH1 d1 q1) as (e1 & (H3 & H4)).
      destruct (IH2 d2 q2) as (e2 & (H5 & H6)).
      exists (caseS v3 e1 e2). split; apply par_caseS; assumption.
    + destruct (pval_inj_inv pv) as (vA & (E4 & pvA)); subst v'.
      destruct (IHpv (inj b0 v0') (@pval_inj n b0 v0 v0' pvv)) as (v3 & (H1 & H2)).
      destruct (pval_inj_inv H1) as (vB & (E5 & pvAB)); subst v3.
      destruct (pval_inj_inv H2) as (vC & (E6 & pvC)). injection E6 as E6. subst vC.
      destruct (IH1 d1 q1) as (e1 & (H3 & H4)).
      destruct (IH2 d2 q2) as (e2 & (H5 & H6)).
      exists ((if b0 then e1 else e2)[vB..]). split.
      * apply par_caseS_red; assumption.
      * apply (par_subst (par_if b0 H4 H6) (scons v0' (@ids value VarInstance_value n))
                   (scons vB (@ids value VarInstance_value n))).
        apply pval_scons_ids. exact pvC.
  - (* par_caseP *)
    intros n v v' c c' pv IHpv pc IHc cT Hdq.
    destruct (par_caseP_inv Hdq) as [(w & (d & (E & (pw & q)))) | (a1 & (a2 & (d1 & (d2 & (d & (Ev & (E3 & (q1 & (q2 & q)))))))))]; subst.
    + destruct (IHpv w pw) as (v3 & (H1 & H2)).
      destruct (IHc d q) as (c3 & (H3 & H4)).
      exists (caseP v3 c3). split; apply par_caseP; assumption.
    + destruct (pval_pair_inv pv) as (v1A & (v2A & (E4 & (pv1A & pv2A)))); subst v'.
      destruct (IHpv (pair d1 d2) (pval_pair q1 q2)) as (v3 & (H1 & H2)).
      destruct (pval_pair_inv H1) as (v1B & (v2B & (E5 & (pv1B & pv2B)))); subst v3.
      destruct (pval_pair_inv H2) as (x1 & (x2 & (E6 & (pd1 & pd2)))). injection E6 as E6a E6b. subst x1 x2.
      destruct (IHc d q) as (c3 & (H3 & H4)).
      exists (c3[v2B,v1B..]). split.
      * apply par_caseP_red; assumption.
      * apply (par_subst H4 (scons d2 (scons d1 (@ids value VarInstance_value n)))
                   (scons v2B (scons v1B (@ids value VarInstance_value n)))).
        apply pval_scons2_ids; assumption.
  - (* par_force_red *)
    intros n c c' p IHp cT Hdq.
    destruct (par_force_thunk_inv Hdq) as [(v2 & (E & pv2)) | (c2 & (E & p2))]; subst.
    + destruct (pval_thunk_inv pv2) as (cT2 & (E2 & p2)); subst.
      destruct (IHp cT2 p2) as (c3 & (H1 & H2)).
      exists c3. split.
      * exact H1.
      * apply par_force_red. exact H2.
    + destruct (IHp c2 p2) as (c3 & (H1 & H2)).
      exists c3. split; assumption.
  - (* par_app_red *)
    intros n c c' v v' pc IHpc pv IHpv cT Hdq.
    destruct (par_app_lambda_inv Hdq) as [(cW & (vW & (E & (pW & qW)))) | (c2 & (v2 & (E & (p2 & q2))))]; subst.
    + destruct (par_lambda_inv pW) as (cT2 & (E2 & pT2)); subst.
      destruct (IHpc cT2 pT2) as (c3 & (H1 & H2)).
      destruct (IHpv vW qW) as (v3 & (H3 & H4)).
      exists (c3[v3..]). split.
      * apply (par_subst H1 (scons v' (@ids value VarInstance_value n))
                   (scons v3 (@ids value VarInstance_value n))).
        apply pval_scons_ids. exact H3.
      * apply par_app_red; assumption.
    + destruct (IHpc c2 p2) as (c3 & (H1 & H2)).
      destruct (IHpv v2 q2) as (v3 & (H3 & H4)).
      exists (c3[v3..]). split.
      * apply (par_subst H1 (scons v' (@ids value VarInstance_value n))
                   (scons v3 (@ids value VarInstance_value n))).
        apply pval_scons_ids. exact H3.
      * apply (par_subst H2 (scons v2 (@ids value VarInstance_value n))
                   (scons v3 (@ids value VarInstance_value n))).
        apply pval_scons_ids. exact H4.
  - (* par_proj_red *)
    intros n b c1 c1' c2 c2' p1 IH1 p2 IH2 cT Hdq.
    destruct (par_proj_tuple_inv Hdq) as [(d & (E & q)) | (d1 & (d2 & (E & (q1 & q2))))]; subst.
    + destruct (par_tuple_inv q) as (e1 & (e2 & (E2 & (r1 & r2)))); subst.
      destruct (IH1 e1 r1) as (u1 & (H1 & H2)).
      destruct (IH2 e2 r2) as (u2 & (H3 & H4)).
      exists (if b then u1 else u2). split.
      * apply par_if; assumption.
      * apply par_proj_red; assumption.
    + destruct (IH1 d1 q1) as (u1 & (H1 & H2)).
      destruct (IH2 d2 q2) as (u2 & (H3 & H4)).
      exists (if b then u1 else u2). split.
      * apply par_if; assumption.
      * apply par_if; assumption.
  - (* par_letin_red *)
    intros n c c' v v' pc IHpc pv IHpv cT Hdq.
    destruct (par_letin_ret_inv Hdq) as [(d1 & (d2 & (E & (q1 & q2)))) | (c2 & (v2 & (E & (p2 & q2))))]; subst.
    + destruct (par_ret_inv q1) as (vT & (E1 & pvT)); subst.
      destruct (IHpc d2 q2) as (c3 & (H1 & H2)).
      destruct (IHpv vT pvT) as (v3 & (H3 & H4)).
      exists (c3[v3..]). split.
      * apply (par_subst H1 (scons v' (@ids value VarInstance_value n))
                   (scons v3 (@ids value VarInstance_value n))).
        apply pval_scons_ids. exact H3.
      * apply par_letin_red; assumption.
    + destruct (IHpc c2 p2) as (c3 & (H1 & H2)).
      destruct (IHpv v2 q2) as (v3 & (H3 & H4)).
      exists (c3[v3..]). split.
      * apply (par_subst H1 (scons v' (@ids value VarInstance_value n))
                   (scons v3 (@ids value VarInstance_value n))).
        apply pval_scons_ids. exact H3.
      * apply (par_subst H2 (scons v2 (@ids value VarInstance_value n))
                   (scons v3 (@ids value VarInstance_value n))).
        apply pval_scons_ids. exact H4.
  - (* par_caseS_red *)
    intros n v v' b c1 c1' c2 c2' pv IHpv p1 IH1 p2 IH2 cT Hdq.
    destruct (par_caseS_inj_inv Hdq) as [(vT & (d1 & (d2 & (E & (qT & (q1 & q2)))))) | (v2 & (d1 & (d2 & (E & (q2 & (q1 & q3))))))]; subst.
    + destruct (pval_inj_inv qT) as (vW & (E2 & pvW)); subst.
      destruct (IHpv vW pvW) as (v3 & (H1 & H2)).
      destruct (IH1 d1 q1) as (e1 & (H3 & H4)).
      destruct (IH2 d2 q2) as (e2 & (H5 & H6)).
      exists ((if b then e1 else e2)[v3..]). split.
      * apply (par_subst (par_if b H3 H5) (scons v' (@ids value VarInstance_value n))
                   (scons v3 (@ids value VarInstance_value n))).
        apply pval_scons_ids. exact H1.
      * apply par_caseS_red; assumption.
    + destruct (IHpv v2 q2) as (v3 & (H1 & H2)).
      destruct (IH1 d1 q1) as (e1 & (H3 & H4)).
      destruct (IH2 d2 q3) as (e2 & (H5 & H6)).
      exists ((if b then e1 else e2)[v3..]). split.
      * apply (par_subst (par_if b H3 H5) (scons v' (@ids value VarInstance_value n))
                   (scons v3 (@ids value VarInstance_value n))).
        apply pval_scons_ids. exact H1.
      * apply (par_subst (par_if b H4 H6) (scons v2 (@ids value VarInstance_value n))
                   (scons v3 (@ids value VarInstance_value n))).
        apply pval_scons_ids. exact H2.
  - (* par_caseP_red *)
    intros n v1 v1' v2 v2' c c' p1 IH1 p2 IH2 pc IHpc cT Hdq.
    destruct (par_caseP_pair_inv Hdq) as [(w & (d & (E & (pW & q)))) | (d1 & (d2 & (d & (E & (q1 & (q2 & q))))))]; subst.
    + destruct (pval_pair_inv pW) as (a1 & (a2 & (E2 & (pa1 & pa2)))); subst.
      destruct (IH1 a1 pa1) as (u1 & (H1 & H2)).
      destruct (IH2 a2 pa2) as (u2 & (H3 & H4)).
      destruct (IHpc d q) as (c3 & (H5 & H6)).
      exists (c3[u2,u1..]). split.
      * apply (par_subst H5 (scons v2' (scons v1' (@ids value VarInstance_value n)))
                   (scons u2 (scons u1 (@ids value VarInstance_value n)))).
        apply pval_scons2_ids; assumption.
      * apply par_caseP_red; assumption.
    + destruct (IH1 d1 q1) as (u1 & (H1 & H2)).
      destruct (IH2 d2 q2) as (u2 & (H3 & H4)).
      destruct (IHpc d q) as (c3 & (H5 & H6)).
      exists (c3[u2,u1..]). split.
      * apply (par_subst H5 (scons v2' (scons v1' (@ids value VarInstance_value n)))
                   (scons u2 (scons u1 (@ids value VarInstance_value n)))).
        apply pval_scons2_ids; assumption.
      * apply (par_subst H6 (scons d2 (scons d1 (@ids value VarInstance_value n)))
                   (scons u2 (scons u1 (@ids value VarInstance_value n)))).
        apply pval_scons2_ids; assumption.
  - (* pval_var *)
    intros n i vT Hdq. apply pval_var_inv in Hdq. subst.
    exists (var_value i). split; apply pval_var.
  - (* pval_unit *)
    intros n vT Hdq. apply pval_unit_inv in Hdq. subst.
    exists u. split; apply pval_unit.
  - (* pval_pair *)
    intros n v1 v1' v2 v2' p1 IH1 p2 IH2 vT Hdq.
    destruct (pval_pair_inv Hdq) as (w1 & (w2 & (E & (q1 & q2)))); subst.
    destruct (IH1 w1 q1) as (u1 & (H1 & H2)).
    destruct (IH2 w2 q2) as (u2 & (H3 & H4)).
    exists (pair u1 u2). split; apply pval_pair; assumption.
  - (* pval_inj *)
    intros n b v v' p IHp vT Hdq.
    destruct (pval_inj_inv Hdq) as (w & (E & q)); subst.
    destruct (IHp w q) as (u & (H1 & H2)).
    exists (inj b u). split; apply pval_inj; assumption.
  - (* pval_thunk *)
    intros n c c' p IHp vT Hdq.
    destruct (pval_thunk_inv Hdq) as (d & (E & q)); subst.
    destruct (IHp d q) as (e & (H1 & H2)).
    exists (thunk e). split; apply pval_thunk; assumption.
Qed.

Lemma par_diamond {n} {c c1 c2: comp n} :
  par c c1 -> par c c2 -> exists c3, par c1 c3 /\ par c2 c3.
Proof. intros H1 H2. exact (proj1 (par_diamond_all n) c c1 H1 c2 H2). Qed.

Lemma pval_diamond {n} {v v1 v2: value n} :
  pval v v1 -> pval v v2 -> exists v3, pval v1 v3 /\ pval v2 v3.
Proof. intros H1 H2. exact (proj2 (par_diamond_all n) v v1 H1 v2 H2). Qed.

Print Assumptions par_diamond_all.
Print Assumptions par_diamond.
Print Assumptions pval_diamond.

Set Implicit Arguments.
Require Import CBPV.ObservationalEquivalence CBPV.StrongReduction CBPV.AbstractReductionSystems.
Import CommaNotation.

Lemma par_diamond_prop n : diamond (@par n).
Proof.
  intros x y z H1 H2.
  destruct (@par_diamond n x y z H1 H2) as (c3 & Hp1 & Hp2).
  exists c3; [exact Hp1|exact Hp2].
Qed.

Lemma sstep_confluent_all n : confluent (@sstep n).
Proof.
  apply confluent_sstep_from_par. apply par_diamond_prop.
Qed.

Lemma equiv_joinable_sstep_prop n x y :
  equiv (comp n) (@sstep n) x y ->
  exists z, star sstep x z /\ star sstep y z.
Proof.
  apply equiv_joinable_sstep. apply par_diamond_prop.
Qed.

Set Implicit Arguments.
Require Import CBPV.ObservationalEquivalence CBPV.StrongReduction CBPV.AbstractReductionSystems.
Import CommaNotation.

Definition empty_sub : fin 0 -> value 0 := fun i => match i with end.
Definition empty_ctx : ctx 0 := fun i => match i with end.
Lemma empty_env : EnvRel empty_ctx empty_sub empty_sub.
Proof. intros i. destruct i. Qed.
Lemma step_typed_raw_star (c c': comp 0) (G: groundtype) :
  sstep c c' -> (null ⊢ c : F (to_valtype G)) -> Raw_star c c'.
Proof.
  intros Hs Hc.
  pose proof (proj1 (sstep_env_all 0) c c' Hs null (F (to_valtype G)) Hc
                empty_sub empty_sub empty_env) as Hrel.
  rewrite (subst_comp_null c empty_sub) in Hrel.
  rewrite (subst_comp_null c' empty_sub) in Hrel.
  apply (CRel0_F_ground_raw_star G). exact Hrel.
Qed.
Lemma forward_ctx_raw : forall n (Gamma: ctx n) (A: comptype) (c d: comp n),
  inhab (Gamma ⊢ c : A) -> star sstep c d ->
  forall (G: groundtype) (C: cctx false 0 n),
  null [[ Gamma ]] ⊢ C : F (to_valtype G) ; A -> Raw_star (fillc C c) (fillc C d).
Proof.
  intros n Gamma A c d Hc0 Hpath. revert Hc0.
  induction Hpath as [x | x x' y Hs Hst IH].
  - intros Hc0 G C HC. apply Raw_star_refl.
  - intros Hc0 G C HC.
    assert (Hc1 : inhab (Gamma ⊢ x' : A)) by (apply (sstep_typing_fwd Hs); exact Hc0).
    assert (Hhead : Raw_star (fillc C x) (fillc C x')).
    { destruct Hc0 as [HcT].
      pose proof (fillc_typing_closing G HC HcT) as Hfc.
      apply (step_typed_raw_star G (sstep_fillc_false C Hs) Hfc). }
    apply (Raw_star_trans Hhead (IH Hc1 G C HC)).
Qed.
Theorem equiv_soundness_CBPV n (Gamma: ctx n) A (M N: CBPVc Gamma A):
  Equiv M N -> M ≃ N.
Proof.
  intros HE. unfold comp_obseq.
  intros G C HC v.
  destruct (@equiv_joinable_sstep_prop n M N HE) as (z & HM & HN).
  pose proof (@forward_ctx_raw n Gamma A M z (inhabited (CBPVc_H M)) HM G C HC) as HfM.
  pose proof (@forward_ctx_raw n Gamma A N z (inhabited (CBPVc_H N)) HN G C HC) as HfN.
  split.
  - intro Hv. apply (proj2 (HfN v)). apply (proj1 (HfM v)). exact Hv.
  - intro Hv. apply (proj2 (HfM v)). apply (proj1 (HfN v)). exact Hv.
Qed.
