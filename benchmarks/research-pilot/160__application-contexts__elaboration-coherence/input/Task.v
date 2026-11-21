Set Implicit Arguments.

From TLC Require Import LibList.

From TLC Require Import LibLN.

Require Import FDef.

Require Import FInfra.

Require Import TransGen.

Require Import TransSubtyping.

Require Import TransTyping.

Implicit Types x : var.

Inductive erased_ftrm : Set :=
  | erased_ftrm_bvar   : nat -> erased_ftrm
  | erased_ftrm_fvar   : var -> erased_ftrm
  | erased_ftrm_nat    : nat -> erased_ftrm
  | erased_ftrm_abs    : erased_ftrm -> erased_ftrm
  | erased_ftrm_app    : erased_ftrm -> erased_ftrm -> erased_ftrm
  | erased_ftrm_pair   : erased_ftrm -> erased_ftrm -> erased_ftrm
  | erased_ftrm_fst    : erased_ftrm -> erased_ftrm
  | erased_ftrm_snd    : erased_ftrm -> erased_ftrm
.

Fixpoint erased_fopen_ee_rec (k : nat) (f : erased_ftrm) (e : erased_ftrm) {struct e} : erased_ftrm :=
  match e with
  | erased_ftrm_bvar i       => If k = i then f else (erased_ftrm_bvar i)
  | erased_ftrm_fvar x       => erased_ftrm_fvar x
  | erased_ftrm_nat i        => erased_ftrm_nat i
  | erased_ftrm_abs e1       => erased_ftrm_abs (erased_fopen_ee_rec (S k) f e1)
  | erased_ftrm_app e1 e2    => erased_ftrm_app (erased_fopen_ee_rec k f e1) (erased_fopen_ee_rec k f e2)
  | erased_ftrm_pair e1 e2   => erased_ftrm_pair (erased_fopen_ee_rec k f e1) (erased_fopen_ee_rec k f e2)
  | erased_ftrm_fst e1       => erased_ftrm_fst (erased_fopen_ee_rec k f e1)
  | erased_ftrm_snd e1       => erased_ftrm_snd (erased_fopen_ee_rec k f e1)
  end.

Definition erased_fopen_ee t u := erased_fopen_ee_rec 0 u t.

Notation "t 'erased_fopen_ee_var' x" := (erased_fopen_ee t (erased_ftrm_fvar x)) (at level 67).

Inductive erased_fterm : erased_ftrm -> Prop :=
  | erased_fterm_var : forall x,
      erased_fterm (erased_ftrm_fvar x)
  | erased_fterm_nat : forall i,
      erased_fterm (erased_ftrm_nat i)
  | erased_fterm_abs : forall L e1,
      (forall x, x \notin L -> erased_fterm (e1 erased_fopen_ee_var x)) ->
      erased_fterm (erased_ftrm_abs e1)
  | erased_fterm_app : forall e1 e2,
      erased_fterm e1 ->
      erased_fterm e2 ->
      erased_fterm (erased_ftrm_app e1 e2)
  | erased_fterm_pair : forall e1 e2,
      erased_fterm e1 ->
      erased_fterm e2 ->
      erased_fterm (erased_ftrm_pair e1 e2)
  | erased_fterm_fst : forall e,
      erased_fterm e ->
      erased_fterm (erased_ftrm_fst e)
  | erased_fterm_snd : forall e,
      erased_fterm e ->
      erased_fterm (erased_ftrm_snd e)
.

Fixpoint erased_ffv_ee (e : erased_ftrm) {struct e} : vars :=
  match e with
  | erased_ftrm_bvar i       => \{}
  | erased_ftrm_fvar x       => \{x}
  | erased_ftrm_nat i        => \{}
  | erased_ftrm_abs e1       => (erased_ffv_ee e1)
  | erased_ftrm_app e1 e2    => (erased_ffv_ee e1) \u (erased_ffv_ee e2)
  | erased_ftrm_pair e1 e2   => (erased_ffv_ee e1) \u (erased_ffv_ee e2)
  | erased_ftrm_fst e1       => (erased_ffv_ee e1)
  | erased_ftrm_snd e1       => (erased_ffv_ee e1)
  end.

Fixpoint erase (e:ftrm) {struct e} : erased_ftrm :=
  match e with
  | ftrm_bvar i       => erased_ftrm_bvar i
  | ftrm_fvar x       => erased_ftrm_fvar x
  | ftrm_nat i        => erased_ftrm_nat i
  | ftrm_absann V e1  => erased_ftrm_abs (erase e1)
  | ftrm_app e1 e2    => erased_ftrm_app (erase e1) (erase e2)
  | ftrm_tabs e1      => erase e1
  | ftrm_tapp e1 e2   => erase e1
  | ftrm_pair e1 e2   => erased_ftrm_pair (erase e1) (erase e2)
  | ftrm_fst e1       => erased_ftrm_fst (erase e1)
  | ftrm_snd e1       => erased_ftrm_snd (erase e1)
  end.

Definition id := erased_ftrm_abs (erased_ftrm_bvar 0).

Inductive id_eta_eq : erased_ftrm -> erased_ftrm -> Prop :=
  | id_eta_eta_reduce : forall L e,
      (forall x, x \notin L -> x \notin erased_ffv_ee (e erased_fopen_ee_var x)) ->
      id_eta_eq (erased_ftrm_abs (erased_ftrm_app e
                                               (erased_ftrm_bvar 0)))
             e
  | id_eta_id_reduce : forall e,
      id_eta_eq (erased_ftrm_app id e) e
  | id_eta_pair_reduce : forall e,
      id_eta_eq e (erased_ftrm_pair (erased_ftrm_fst e) (erased_ftrm_snd e))

  | id_eta_app : forall e1 e1' e2 e2',
      id_eta_eq e1 e1' ->
      id_eta_eq e2 e2' ->
      id_eta_eq (erased_ftrm_app e1 e2) (erased_ftrm_app e1' e2')
  | id_eta_pair : forall e1 e1' e2 e2',
      id_eta_eq e1 e1' ->
      id_eta_eq e2 e2' ->
      id_eta_eq (erased_ftrm_pair e1 e2) (erased_ftrm_pair e1' e2')
  | id_eta_fst : forall e1 e1',
      id_eta_eq e1 e1' ->
      id_eta_eq (erased_ftrm_fst e1) (erased_ftrm_fst e1')
  | id_eta_snd : forall e1 e1',
      id_eta_eq e1 e1' ->
      id_eta_eq (erased_ftrm_snd e1) (erased_ftrm_snd e1')

  | id_eta_abs : forall L e1 e1',
      (forall x, x \notin L -> id_eta_eq (e1 erased_fopen_ee_var x)
                                   (e1' erased_fopen_ee_var x)) ->
      id_eta_eq (erased_ftrm_abs e1) (erased_ftrm_abs e1')
  | id_eta_refl : forall e,
      id_eta_eq e e
  | id_eta_symm : forall e1 e2,
      id_eta_eq e1 e2 ->
      id_eta_eq e2 e1
  | id_eta_trans : forall e1 e2 e3,
      id_eta_eq e1 e2 ->
      id_eta_eq e2 e3 ->
      id_eta_eq e1 e3.

Theorem d2ftyping_confluence : forall E1 E2 Q1 Q2 S T1 T2 f1 f2,
    d2ftyping E1 Q1 S T1 f1 ->
    d2ftyping E2 Q2 S T2 f2 ->
    id_eta_eq (erase f1) (erase f2).
