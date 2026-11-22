Require Import syntax_ott.

Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Export LibTactics.

Require Import Lia.

Require Export equiRec.

Require Import List.
Require Import Sorting.Permutation.

(* ============================================================ *)
(* Section 1: basic atom equality and type substitution lemmas  *)
(* ============================================================ *)

Lemma eq_dec_same : forall (X:atom) (A:Type) (a b:A),
  (if (eq_dec X X) then a else b) = a.
Proof. intros. rewrite eq_dec_refl. reflexivity. Qed.

Lemma eq_dec_diff : forall (X Y:atom) (A:Type) (a b:A),
  X <> Y -> (if (eq_dec X Y) then a else b) = b.
Proof. intros X Y A a b Hne. destruct (eq_dec X Y) as [e|n]. exfalso; auto. reflexivity. Qed.

Lemma typsubst_typ_same : forall (P:typ) (X:typevar),
  typsubst_typ P X (t_var_f X) = P.
Proof. intros. simpl. apply eq_dec_same. Qed.

Lemma typsubst_typ_diff : forall (P:typ) (X Y:typevar),
  X <> Y -> typsubst_typ P X (t_var_f Y) = t_var_f Y.
Proof. intros. simpl. apply eq_dec_diff. auto. Qed.

Lemma typsubst_typ_open_rec : forall (A:typ) (k:nat) (B:typ) (P:typ) (X:typevar),
  X \notin typefv_typ A ->
  typsubst_typ P X (open_typ_wrt_typ_rec k B A) =
  open_typ_wrt_typ_rec k (typsubst_typ P X B) (typsubst_typ P X A).
Proof.
  induction A as [n|Y| | |A1 IH1 A2 IH2|A0 IH0]; intros k B P X Hf.
  - (* t_var_b *) simpl. destruct (lt_eq_lt_dec n k) as [[l|e]|r]; reflexivity.
  - (* t_var_f *) destruct (eq_dec Y X) as [e|n].
    + exfalso. apply Hf. simpl. rewrite e. simpl. fsetdec.
    + simpl. destruct (eq_dec Y X) as [e2|_].
      * exfalso; auto.
      * reflexivity.
  - reflexivity.
  - reflexivity.
  - (* arrow *) simpl.
    assert (H1 : X \notin typefv_typ A1) by (simpl in Hf; fsetdec).
    assert (H2 : X \notin typefv_typ A2) by (simpl in Hf; fsetdec).
    rewrite (IH1 k B P X H1), (IH2 k B P X H2). reflexivity.
  - (* mu *) simpl.
    assert (H1 : X \notin typefv_typ A0) by (simpl in Hf; auto).
    rewrite (IH0 (S k) B P X H1). reflexivity.
Qed.

Lemma typsubst_typ_open : forall (A B:typ) (P:typ) (X:typevar),
  X \notin typefv_typ A ->
  typsubst_typ P X (open_typ_wrt_typ A B) =
  open_typ_wrt_typ (typsubst_typ P X A) (typsubst_typ P X B).
Proof. intros. unfold open_typ_wrt_typ. apply typsubst_typ_open_rec. auto. Qed.

Lemma typsubst_typ_id : forall (A:typ) (P:typ) (X:typevar),
  X \notin typefv_typ A -> typsubst_typ P X A = A.
Proof.
  induction A as [n|Y| | |A1 IH1 A2 IH2|A0 IH0]; intros P X Hf.
  - reflexivity.
  - (* fvar *) simpl. destruct (eq_dec Y X) as [e|n].
    + exfalso. apply Hf. simpl. rewrite e. simpl. fsetdec.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - (* arrow *) simpl.
    assert (H1 : X \notin typefv_typ A1) by (simpl in Hf; fsetdec).
    assert (H2 : X \notin typefv_typ A2) by (simpl in Hf; fsetdec).
    rewrite (IH1 P X H1), (IH2 P X H2). reflexivity.
  - (* mu *) simpl.
    assert (H1 : X \notin typefv_typ A0) by (simpl in Hf; auto).
    rewrite (IH0 P X H1). reflexivity.
Qed.

Lemma typsubst_typ_open_self : forall (A:typ) (P:typ) (X:typevar),
  X \notin typefv_typ A ->
  typsubst_typ P X (open_typ_wrt_typ A (t_var_f X)) = open_typ_wrt_typ A P.
Proof.
  intros A P X Hf.
  rewrite (typsubst_typ_open A (t_var_f X) P X Hf).
  rewrite typsubst_typ_id by auto.
  rewrite typsubst_typ_same.
  reflexivity.
Qed.

Lemma typsubst_typ_comm : forall (A:typ) (P Q:typ) (X Y:typevar),
  X <> Y -> X \notin typefv_typ Q -> Y \notin typefv_typ P ->
  typsubst_typ P X (typsubst_typ Q Y A) = typsubst_typ Q Y (typsubst_typ P X A).
Proof.
  induction A as [n|Z| | |A1 IH1 A2 IH2|A0 IH0]; intros P Q X Y HXY HQ HP.
  - reflexivity.
  - (* fvar *) cbn [typsubst_typ].
    destruct (eq_dec Z Y) as [eY|nY]; destruct (eq_dec Z X) as [eX|nX].
    + subst. exfalso; auto.
    + subst. rewrite (typsubst_typ_id Q P X HQ). rewrite typsubst_typ_same. reflexivity.
    + subst. rewrite typsubst_typ_same. rewrite (typsubst_typ_id P Q Y HP). reflexivity.
    + assert (HXZ : X <> Z) by (intro H; apply nX; symmetry; auto).
      assert (HYZ : Y <> Z) by (intro H; apply nY; symmetry; auto).
      rewrite (typsubst_typ_diff P X Z HXZ).
      rewrite (typsubst_typ_diff Q Y Z HYZ). reflexivity.
  - reflexivity.
  - reflexivity.
  - (* arrow *) simpl. rewrite IH1; auto. rewrite IH2; auto.
  - (* mu *) simpl. rewrite IH0; auto.
Qed.
(* ============================================================ *)
(* Section 2: degrees, size, and lc for types                  *)
(* ============================================================ *)

Lemma size_typ_open_rec : forall (A:typ) (X:typevar) (k:nat),
  size_typ (open_typ_wrt_typ_rec k (t_var_f X) A) = size_typ A.
Proof.
  intros A. induction A as [n|Y| | |A1 IH1 A2 IH2|A0 IH0].
  - intros X k; simpl. destruct (lt_eq_lt_dec n k) as [[l|e]|r]; simpl; auto.
  - intros X k; simpl; auto.
  - intros X k; simpl; auto.
  - intros X k; simpl; auto.
  - intros X k; simpl. rewrite (IH1 X k), (IH2 X k). reflexivity.
  - intros X k; simpl. rewrite (IH0 X (S k)). reflexivity.
Qed.

Lemma size_typ_open : forall (A:typ) (X:typevar),
  size_typ (open_typ_wrt_typ A (t_var_f X)) = size_typ A.
Proof. intros. unfold open_typ_wrt_typ. apply size_typ_open_rec. Qed.

Lemma degree_typ_mu_iff : forall (k:nat) (A:typ),
  degree_typ_wrt_typ k (t_mu A) <-> degree_typ_wrt_typ (S k) A.
Proof.
  intros k A. split; intro H.
  - inversion H. auto.
  - constructor. auto.
Qed.

Lemma degree_typ_open : forall (A:typ) (k:nat) (X:typevar),
  degree_typ_wrt_typ (S k) A <-> degree_typ_wrt_typ k (open_typ_wrt_typ_rec k (t_var_f X) A).
Proof.
  intros A. induction A as [m|Y| | |A1 IH1 A2 IH2|A0 IH0].
  - (* t_var_b *) intros k X; simpl. destruct (lt_eq_lt_dec m k) as [[l|e]|r]; split; intro H.
    + apply degree_wrt_typ_t_var_b. lia.
    + inversion H. apply degree_wrt_typ_t_var_b. lia.
    + subst. apply degree_wrt_typ_t_var_f.
    + subst. inversion H. apply degree_wrt_typ_t_var_b. lia.
    + inversion H; subst. exfalso; lia.
    + inversion H; subst. apply degree_wrt_typ_t_var_b. lia.
  - (* t_var_f *) intros k X; simpl. split; intro H; constructor.
  - (* int *) intros k X; simpl. split; intro H; constructor.
  - (* top *) intros k X; simpl. split; intro H; constructor.
  - (* arrow *) intros k X; simpl. split; intro H.
    + inversion H; subst. constructor.
      * apply (proj1 (IH1 k X)). auto.
      * apply (proj1 (IH2 k X)). auto.
    + inversion H; subst. constructor.
      * apply (proj2 (IH1 k X)). auto.
      * apply (proj2 (IH2 k X)). auto.
  - (* mu *) intros k X; simpl. split; intro H.
    + rewrite degree_typ_mu_iff. apply (proj1 (IH0 (S k) X)).
      rewrite degree_typ_mu_iff in H. auto.
    + apply (proj2 (degree_typ_mu_iff (S k) A0)). apply (proj2 (IH0 (S k) X)).
      rewrite degree_typ_mu_iff in H. auto.
Qed.

Lemma lc_typ_degree : forall (A:typ), lc_typ A -> degree_typ_wrt_typ 0 A.
Proof.
  intros A Hlc. remember (size_typ A) as n eqn:E. generalize dependent A.
  induction n as [n IH] using lt_wf_ind. intros A0 Hlc Hs.
  destruct A0 as [m|X| | |A1 A2|A0]; simpl in *.
    - (* bvar *) inversion Hlc.
    - constructor.
    - constructor.
    - constructor.
    - (* arrow *) inversion Hlc; subst. constructor.
      + apply (IH (size_typ A1)); [lia | auto | reflexivity].
      + apply (IH (size_typ A2)); [lia | auto | reflexivity].
    - (* mu *) inversion Hlc; subst.
      pick fresh Y.
      apply (proj2 (degree_typ_mu_iff 0 A0)).
      apply (proj2 (degree_typ_open A0 0 Y)).
      apply (IH (size_typ (open_typ_wrt_typ_rec 0 (t_var_f Y) A0))).
      * rewrite size_typ_open_rec. lia.
      * match goal with Hf : forall X, lc_typ _ |- _ => apply Hf end.
      * reflexivity.
Qed.

Lemma degree_lc_typ : forall (A:typ), degree_typ_wrt_typ 0 A -> lc_typ A.
Proof.
  intros A Hd. remember (size_typ A) as n eqn:E. generalize dependent A.
  induction n as [n IH] using lt_wf_ind. intros A0 Hd Hs.
  destruct A0 as [m|X| | |A1 A2|A0]; simpl in *.
  - (* bvar *) inversion Hd; subst. lia.
  - constructor.
  - constructor.
  - constructor.
  - (* arrow *) inversion Hd; subst. constructor.
    + apply (IH (size_typ A1)); [lia | auto | reflexivity].
    + apply (IH (size_typ A2)); [lia | auto | reflexivity].
  - (* mu *) constructor. intro Y.
    inversion Hd; subst.
    apply (IH (size_typ (open_typ_wrt_typ_rec 0 (t_var_f Y) A0))).
    + rewrite size_typ_open_rec. lia.
    + apply (proj1 (degree_typ_open A0 0 Y)). auto.
    + reflexivity.
Qed.
(* ============================================================ *)
(* Section 3: degrees and lc for cast operators                *)
(* ============================================================ *)

Lemma size_castop_open_castop_rec : forall (c:castop) (cx:castvar) (k:nat),
  size_castop (open_castop_wrt_castop_rec k (c_var_f cx) c) = size_castop c.
Proof.
  intros c. induction c as [n|x| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IH].
  - intros cx k; simpl. destruct (lt_eq_lt_dec n k) as [[l|e]|r]; simpl; auto.
  - intros; simpl; auto.
  - intros; simpl; auto.
  - intros; simpl; auto.
  - intros; simpl; auto.
  - intros; simpl. rewrite (IH1 cx k), (IH2 cx k). reflexivity.
  - intros; simpl. rewrite (IH1 cx k), (IH2 cx k). reflexivity.
  - intros; simpl. rewrite (IH cx (S k)). reflexivity.
Qed.

Lemma size_castop_open_castop : forall (c:castop) (cx:castvar),
  size_castop (open_castop_wrt_castop c (c_var_f cx)) = size_castop c.
Proof. intros. unfold open_castop_wrt_castop. apply size_castop_open_castop_rec. Qed.

Lemma size_castop_open_typ_rec : forall (c:castop) (X:typevar) (k:nat),
  size_castop (open_castop_wrt_typ_rec k (t_var_f X) c) = size_castop c.
Proof.
  intros c. induction c as [n|x| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IH].
  - intros; simpl; auto.
  - intros; simpl; auto.
  - intros; simpl; auto.
  - intros X k; simpl. rewrite size_typ_open_rec. reflexivity.
  - intros X k; simpl. rewrite size_typ_open_rec. reflexivity.
  - intros; simpl. rewrite (IH1 X k), (IH2 X k). reflexivity.
  - intros; simpl. rewrite (IH1 X k), (IH2 X k). reflexivity.
  - intros; simpl. rewrite (IH X k). reflexivity.
Qed.

Lemma degree_castop_fix_iff : forall (k:nat) (c:castop),
  degree_castop_wrt_castop k (c_fixc c) <-> degree_castop_wrt_castop (S k) c.
Proof.
  intros k c. split; intro H.
  - inversion H. auto.
  - constructor. auto.
Qed.

Lemma degree_castop_typ_fix_iff : forall (k:nat) (c:castop),
  degree_castop_wrt_typ k (c_fixc c) <-> degree_castop_wrt_typ k c.
Proof.
  intros k c. split; intro H.
  - inversion H. auto.
  - constructor. auto.
Qed.

Lemma degree_castop_wrt_castop_open : forall (c:castop) (k:nat) (cx:castvar),
  degree_castop_wrt_castop (S k) c <->
  degree_castop_wrt_castop k (open_castop_wrt_castop_rec k (c_var_f cx) c).
Proof.
  intros c. induction c as [n|x| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IH].
  - (* var_b *) intros k cx; simpl. destruct (lt_eq_lt_dec n k) as [[l|e]|r]; split; intro H.
    + apply degree_wrt_castop_c_var_b. lia.
    + inversion H. apply degree_wrt_castop_c_var_b. lia.
    + subst. apply degree_wrt_castop_c_var_f.
    + subst. inversion H. apply degree_wrt_castop_c_var_b. lia.
    + inversion H; subst. exfalso; lia.
    + inversion H; subst. apply degree_wrt_castop_c_var_b. lia.
  - (* var_f *) intros k cx; simpl. split; intro H; constructor.
  - (* id *) intros k cx; simpl. split; intro H; constructor.
  - (* unfold *) intros k cx; simpl. split; intro H; constructor.
  - (* fold *) intros k cx; simpl. split; intro H; constructor.
  - (* arrow *) intros k cx; simpl. split; intro H.
    + inversion H; subst. constructor.
      * apply (proj1 (IH1 k cx)). auto.
      * apply (proj1 (IH2 k cx)). auto.
    + inversion H; subst. constructor.
      * apply (proj2 (IH1 k cx)). auto.
      * apply (proj2 (IH2 k cx)). auto.
  - (* seq *) intros k cx; simpl. split; intro H.
    + inversion H; subst. constructor.
      * apply (proj1 (IH1 k cx)). auto.
      * apply (proj1 (IH2 k cx)). auto.
    + inversion H; subst. constructor.
      * apply (proj2 (IH1 k cx)). auto.
      * apply (proj2 (IH2 k cx)). auto.
  - (* fixc *) intros k cx; simpl. split; intro H.
    + rewrite degree_castop_fix_iff. apply (proj1 (IH (S k) cx)).
      rewrite degree_castop_fix_iff in H. auto.
    + rewrite degree_castop_fix_iff in H. rewrite degree_castop_fix_iff.
      apply (proj2 (IH (S k) cx)). auto.
Qed.

Lemma degree_castop_wrt_typ_open : forall (c:castop) (k k':nat) (cx:castvar),
  degree_castop_wrt_typ k (open_castop_wrt_castop_rec k' (c_var_f cx) c) <->
  degree_castop_wrt_typ k c.
Proof.
  intros c. induction c as [n|x| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IH].
  - (* var_b *) intros k k' cx; simpl.
    destruct (lt_eq_lt_dec n k') as [[l|e]|r]; simpl; split; intro H; constructor.
  - intros; simpl. split; intro H; constructor.
  - intros; simpl. split; intro H; constructor.
  - intros; simpl. split; auto.
  - intros; simpl. split; auto.
  - intros k k' cx; simpl. split; intro H.
    + inversion H; subst. constructor.
      * apply (proj1 (IH1 k k' cx)). auto.
      * apply (proj1 (IH2 k k' cx)). auto.
    + inversion H; subst. constructor.
      * apply (proj2 (IH1 k k' cx)). auto.
      * apply (proj2 (IH2 k k' cx)). auto.
  - intros k k' cx; simpl. split; intro H.
    + inversion H; subst. constructor.
      * apply (proj1 (IH1 k k' cx)). auto.
      * apply (proj1 (IH2 k k' cx)). auto.
    + inversion H; subst. constructor.
      * apply (proj2 (IH1 k k' cx)). auto.
      * apply (proj2 (IH2 k k' cx)). auto.
  - intros k k' cx; simpl. split; intro H.
    + apply (proj2 (degree_castop_typ_fix_iff k c)).
      apply (proj1 (IH k (S k') cx)).
      apply (proj1 (degree_castop_typ_fix_iff k (open_castop_wrt_castop_rec (S k') (c_var_f cx) c))).
      auto.
    + apply (proj2 (degree_castop_typ_fix_iff k (open_castop_wrt_castop_rec (S k') (c_var_f cx) c))).
      apply (proj2 (IH k (S k') cx)).
      apply (proj1 (degree_castop_typ_fix_iff k c)). auto.
Qed.

Lemma lc_castop_degree : forall (c:castop), lc_castop c ->
  degree_castop_wrt_castop 0 c /\ degree_castop_wrt_typ 0 c.
Proof.
  intros c H. induction H as [cx| |A HA|A HA|c1 c2 H1 IH1 H2 IH2|c1 c2 H1 IH1 H2 IH2|c Hc IHc].
  - (* var_f *) split; constructor.
  - (* id *) split; constructor.
  - (* unfold *) split; constructor; apply lc_typ_degree; auto.
  - (* fold *) split; constructor; apply lc_typ_degree; auto.
  - (* arrow *) split.
    + constructor; [apply (proj1 IH1) | apply (proj1 IH2)].
    + constructor; [apply (proj2 IH1) | apply (proj2 IH2)].
  - (* seq *) split.
    + constructor; [apply (proj1 IH1) | apply (proj1 IH2)].
    + constructor; [apply (proj2 IH1) | apply (proj2 IH2)].
  - (* fixc *) split.
    + apply (proj2 (degree_castop_fix_iff 0 c)).
      pick fresh cx.
      apply (proj2 (degree_castop_wrt_castop_open c 0 cx)).
      apply (proj1 (IHc cx)).
    + pick fresh cy.
      apply (proj2 (degree_castop_typ_fix_iff 0 c)).
      apply (proj1 (degree_castop_wrt_typ_open c 0 0 cy)).
      apply (proj2 (IHc cy)).
Qed.

Lemma degree_lc_castop : forall (c:castop),
  degree_castop_wrt_castop 0 c /\ degree_castop_wrt_typ 0 c -> lc_castop c.
Proof.
  intros c H. remember (size_castop c) as n eqn:E. generalize dependent c.
  induction n as [n IH] using lt_wf_ind. intros c0 H Hs.
  destruct c0 as [m|x| |A|A|c1 c2|c1 c2|c]; simpl in *.
  - (* var_b *) destruct H as [H1 H2]. inversion H1; subst. lia.
  - (* var_f *) constructor.
  - (* id *) constructor.
  - (* unfold *) destruct H as [H1 H2]. inversion H2; subst. constructor.
    apply degree_lc_typ. auto.
  - (* fold *) destruct H as [H1 H2]. inversion H2; subst. constructor.
    apply degree_lc_typ. auto.
  - (* arrow *) destruct H as [H1 H2]. inversion H1; subst. inversion H2; subst.
    constructor.
    + apply (IH (size_castop c1)); [lia | split; auto | reflexivity].
    + apply (IH (size_castop c2)); [lia | split; auto | reflexivity].
  - (* seq *) destruct H as [H1 H2]. inversion H1; subst. inversion H2; subst.
    constructor.
    + apply (IH (size_castop c1)); [lia | split; auto | reflexivity].
    + apply (IH (size_castop c2)); [lia | split; auto | reflexivity].
  - (* fixc *) destruct H as [H1 H2]. inversion H1; subst. 
    apply (proj1 (degree_castop_typ_fix_iff 0 c)) in H2.
    constructor. intro cx.
    apply (IH (size_castop (open_castop_wrt_castop c (c_var_f cx)))).
    + rewrite size_castop_open_castop. lia.
    + split.
      * apply (proj1 (degree_castop_wrt_castop_open c 0 cx)). auto.
      * apply (proj2 (degree_castop_wrt_typ_open c 0 0 cx)). auto.
    + rewrite size_castop_open_castop. reflexivity.
Qed.
(* ============================================================ *)
(* Section 4: degrees and lc for expressions                   *)
(* ============================================================ *)

Lemma size_exp_open_exp_rec : forall (e:exp) (x:termvar) (k:nat),
  size_exp (open_exp_wrt_exp_rec k (e_var_f x) e) = size_exp e.
Proof.
  intros e. induction e as [n|x|i|A e IH|e1 IH1 e2 IH2|c e IH].
  - intros x k; simpl. destruct (lt_eq_lt_dec n k) as [[l|e]|r]; simpl; auto.
  - intros; simpl; auto.
  - intros; simpl; auto.
  - intros x k; simpl. rewrite (IH x (S k)). reflexivity.
  - intros; simpl. rewrite (IH1 x k), (IH2 x k). reflexivity.
  - intros; simpl. rewrite (IH x k). reflexivity.
Qed.

Lemma size_exp_open_castop_rec : forall (e:exp) (cx:castvar) (k:nat),
  size_exp (open_exp_wrt_castop_rec k (c_var_f cx) e) = size_exp e.
Proof.
  intros e. induction e as [n|x|i|A e IH|e1 IH1 e2 IH2|c e IH].
  - intros; simpl; auto.
  - intros; simpl; auto.
  - intros; simpl; auto.
  - intros cx k; simpl. rewrite (IH cx k). reflexivity.
  - intros; simpl. rewrite (IH1 cx k), (IH2 cx k). reflexivity.
  - intros cx k; simpl. rewrite size_castop_open_castop_rec. rewrite (IH cx k). reflexivity.
Qed.

Lemma size_exp_open_typ_rec : forall (e:exp) (X:typevar) (k:nat),
  size_exp (open_exp_wrt_typ_rec k (t_var_f X) e) = size_exp e.
Proof.
  intros e. induction e as [n|x|i|A e IH|e1 IH1 e2 IH2|c e IH].
  - intros; simpl; auto.
  - intros; simpl; auto.
  - intros; simpl; auto.
  - intros X k; simpl. rewrite size_typ_open_rec. rewrite (IH X k). reflexivity.
  - intros; simpl. rewrite (IH1 X k), (IH2 X k). reflexivity.
  - intros X k; simpl. rewrite size_castop_open_typ_rec. rewrite (IH X k). reflexivity.
Qed.

Lemma size_exp_open_exp : forall (e:exp) (x:termvar),
  size_exp (open_exp_wrt_exp e (e_var_f x)) = size_exp e.
Proof. intros. unfold open_exp_wrt_exp. apply size_exp_open_exp_rec. Qed.

Lemma degree_exp_wrt_exp_open : forall (e:exp) (k:nat) (x:termvar),
  degree_exp_wrt_exp (S k) e <->
  degree_exp_wrt_exp k (open_exp_wrt_exp_rec k (e_var_f x) e).
Proof.
  intros e. induction e as [n|y|i|A e IH|e1 IH1 e2 IH2|c e IH].
  - (* var_b *) intros k x; simpl. destruct (lt_eq_lt_dec n k) as [[l|eq]|r]; split; intro H.
    + apply degree_wrt_exp_e_var_b. lia.
    + inversion H. apply degree_wrt_exp_e_var_b. lia.
    + subst. apply degree_wrt_exp_e_var_f.
    + subst. inversion H. apply degree_wrt_exp_e_var_b. lia.
    + inversion H; subst. exfalso; lia.
    + inversion H; subst. apply degree_wrt_exp_e_var_b. lia.
  - intros; simpl. split; intro H; constructor.
  - intros; simpl. split; intro H; constructor.
  - (* abs *) intros k x; split; intro H.
    + inversion H; subst. constructor. apply (proj1 (IH (S k) x)). auto.
    + inversion H; subst. constructor. apply (proj2 (IH (S k) x)). auto.
  - (* app *) intros k x; split; intro H.
    + inversion H; subst. constructor.
      * apply (proj1 (IH1 k x)). auto.
      * apply (proj1 (IH2 k x)). auto.
    + inversion H; subst. constructor.
      * apply (proj2 (IH1 k x)). auto.
      * apply (proj2 (IH2 k x)). auto.
  - (* cast *) intros k x; split; intro H.
    + inversion H; subst. constructor. apply (proj1 (IH k x)). auto.
    + inversion H; subst. constructor. apply (proj2 (IH k x)). auto.
Qed.

Lemma degree_exp_wrt_castop_inv_open_exp : forall (e:exp) (k k':nat) (x:termvar),
  degree_exp_wrt_castop k (open_exp_wrt_exp_rec k' (e_var_f x) e) <->
  degree_exp_wrt_castop k e.
Proof.
  intros e. induction e as [n|y|i|A e IH|e1 IH1 e2 IH2|c e IH].
  - (* var_b *) intros k k' x; simpl. destruct (lt_eq_lt_dec n k') as [[l|eq]|r]; split; intro H; constructor.
  - intros; simpl. split; intro H; constructor.
  - intros; simpl. split; intro H; constructor.
  - (* abs *) intros k k' x; split; intro H.
    + inversion H; subst. constructor. apply (proj1 (IH k (S k') x)). auto.
    + inversion H; subst. constructor. apply (proj2 (IH k (S k') x)). auto.
  - (* app *) intros k k' x; split; intro H.
    + inversion H; subst. constructor; [apply (proj1 (IH1 k k' x))|apply (proj1 (IH2 k k' x))]; auto.
    + inversion H; subst. constructor; [apply (proj2 (IH1 k k' x))|apply (proj2 (IH2 k k' x))]; auto.
  - (* cast *) intros k k' x; split; intro H.
    + inversion H; subst. constructor.
      * auto.
      * apply (proj1 (IH k k' x)). auto.
    + inversion H; subst. constructor.
      * auto.
      * apply (proj2 (IH k k' x)). auto.
Qed.

Lemma degree_exp_wrt_typ_inv_open_exp : forall (e:exp) (k k':nat) (x:termvar),
  degree_exp_wrt_typ k (open_exp_wrt_exp_rec k' (e_var_f x) e) <->
  degree_exp_wrt_typ k e.
Proof.
  intros e. induction e as [n|y|i|A e IH|e1 IH1 e2 IH2|c e IH].
  - (* var_b *) intros k k' x; simpl. destruct (lt_eq_lt_dec n k') as [[l|eq]|r]; split; intro H; constructor.
  - intros; simpl. split; intro H; constructor.
  - intros; simpl. split; intro H; constructor.
  - (* abs *) intros k k' x; split; intro H.
    + inversion H; subst. constructor.
      * auto.
      * apply (proj1 (IH k (S k') x)). auto.
    + inversion H; subst. constructor.
      * auto.
      * apply (proj2 (IH k (S k') x)). auto.
  - (* app *) intros k k' x; split; intro H.
    + inversion H; subst. constructor; [apply (proj1 (IH1 k k' x))|apply (proj1 (IH2 k k' x))]; auto.
    + inversion H; subst. constructor; [apply (proj2 (IH1 k k' x))|apply (proj2 (IH2 k k' x))]; auto.
  - (* cast *) intros k k' x; split; intro H.
    + inversion H; subst. constructor; [auto|apply (proj1 (IH k k' x))]; auto.
    + inversion H; subst. constructor; [auto|apply (proj2 (IH k k' x))]; auto.
Qed.
(* ============================================================ *)
(* Section 5: lc_exp versus degrees                            *)
(* ============================================================ *)

Lemma degree_exp_abs_inv : forall (k:nat) (A:typ) (e:exp),
  degree_exp_wrt_exp k (e_abs A e) -> degree_exp_wrt_exp (S k) e.
Proof. intros. inversion H. auto. Qed.

Lemma degree_castop_abs_inv : forall (k:nat) (A:typ) (e:exp),
  degree_exp_wrt_castop k (e_abs A e) -> degree_exp_wrt_castop k e.
Proof. intros. inversion H. auto. Qed.

Lemma degree_typ_abs_inv : forall (k:nat) (A:typ) (e:exp),
  degree_exp_wrt_typ k (e_abs A e) ->
  degree_typ_wrt_typ k A /\ degree_exp_wrt_typ k e.
Proof. intros. inversion H. auto. Qed.

Lemma degree_exp_app_inv : forall (k:nat) (e1 e2:exp),
  degree_exp_wrt_exp k (e_app e1 e2) ->
  degree_exp_wrt_exp k e1 /\ degree_exp_wrt_exp k e2.
Proof. intros. inversion H. auto. Qed.

Lemma degree_castop_app_inv : forall (k:nat) (e1 e2:exp),
  degree_exp_wrt_castop k (e_app e1 e2) ->
  degree_exp_wrt_castop k e1 /\ degree_exp_wrt_castop k e2.
Proof. intros. inversion H. auto. Qed.

Lemma degree_typ_app_inv : forall (k:nat) (e1 e2:exp),
  degree_exp_wrt_typ k (e_app e1 e2) ->
  degree_exp_wrt_typ k e1 /\ degree_exp_wrt_typ k e2.
Proof. intros. inversion H. auto. Qed.

Lemma degree_exp_cast_inv : forall (k:nat) (c:castop) (e:exp),
  degree_exp_wrt_exp k (e_cast c e) -> degree_exp_wrt_exp k e.
Proof. intros. inversion H. auto. Qed.

Lemma degree_castop_cast_inv : forall (k:nat) (c:castop) (e:exp),
  degree_exp_wrt_castop k (e_cast c e) ->
  degree_castop_wrt_castop k c /\ degree_exp_wrt_castop k e.
Proof. intros. inversion H. auto. Qed.

Lemma degree_typ_cast_inv : forall (k:nat) (c:castop) (e:exp),
  degree_exp_wrt_typ k (e_cast c e) ->
  degree_castop_wrt_typ k c /\ degree_exp_wrt_typ k e.
Proof. intros. inversion H. auto. Qed.

Lemma lc_exp_degree : forall (e:exp), lc_exp e ->
  degree_exp_wrt_exp 0 e /\ degree_exp_wrt_castop 0 e /\ degree_exp_wrt_typ 0 e.
Proof.
  intros e H. induction H as [x|i|A e HA Hb IHb|e1 e2 H1 IH1 H2 IH2|c e Hc He IHe].
  - (* var_f *) split; [constructor|split; constructor].
  - (* lit *) split; [constructor|split; constructor].
  - (* abs *)
    split.
    + constructor. pick fresh x.
      apply (proj2 (degree_exp_wrt_exp_open e 0 x)).
      apply (proj1 (IHb x)).
    + split.
      * constructor. pick fresh x.
        apply (proj1 (degree_exp_wrt_castop_inv_open_exp e 0 0 x)).
        apply (proj1 (proj2 (IHb x))).
      * constructor.
        -- apply lc_typ_degree. auto.
        -- pick fresh x.
           apply (proj1 (degree_exp_wrt_typ_inv_open_exp e 0 0 x)).
           apply (proj2 (proj2 (IHb x))).
  - (* app *) destruct IH1 as [H1a [H1b H1c]]. destruct IH2 as [H2a [H2b H2c]].
    split.
    + constructor; auto.
    + split; constructor; auto.
  - (* cast *) destruct IHe as [H1a [H1b H1c]].
    destruct (lc_castop_degree c Hc) as [Hca Hcb].
    split.
    + constructor; auto.
    + split; constructor; auto.
Qed.

Lemma degree_lc_exp : forall (e:exp),
  degree_exp_wrt_exp 0 e /\ degree_exp_wrt_castop 0 e /\ degree_exp_wrt_typ 0 e ->
  lc_exp e.
Proof.
  intros e H. remember (size_exp e) as n eqn:E. generalize dependent e.
  induction n as [n IH] using lt_wf_ind. intros e0 H Hs.
  destruct e0 as [m|x|i|A e|e1 e2|c e]; simpl in *.
  - (* var_b *) destruct H as [H1 _]. inversion H1; subst. lia.
  - (* var_f *) constructor.
  - (* lit *) constructor.
  - (* abs *) destruct H as [H1 [Hc Ht]].
    pose proof (degree_typ_abs_inv 0 A e Ht) as [HA He].
    pose proof (degree_castop_abs_inv 0 A e Hc) as Hce.
    pose proof (degree_exp_abs_inv 0 A e H1) as Hb.
    constructor.
    + apply degree_lc_typ. auto.
    + intro x.
      apply (IH (size_exp (open_exp_wrt_exp e (e_var_f x)))).
      * rewrite size_exp_open_exp. lia.
      * split.
        -- apply (proj1 (degree_exp_wrt_exp_open e 0 x)). auto.
        -- split.
           ++ apply (proj2 (degree_exp_wrt_castop_inv_open_exp e 0 0 x)). auto.
           ++ apply (proj2 (degree_exp_wrt_typ_inv_open_exp e 0 0 x)). auto.
      * rewrite size_exp_open_exp. reflexivity.
  - (* app *) destruct H as [H1 [Hc Ht]].
    destruct (degree_exp_app_inv 0 e1 e2 H1) as [H1a H1b].
    destruct (degree_castop_app_inv 0 e1 e2 Hc) as [Hca Hcb].
    destruct (degree_typ_app_inv 0 e1 e2 Ht) as [Hta Htb].
    constructor.
    + apply (IH (size_exp e1)); [lia | split; [auto|split;auto] | reflexivity].
    + apply (IH (size_exp e2)); [lia | split; [auto|split;auto] | reflexivity].
  - (* cast *) destruct H as [H1 [Hc Ht]].
    pose proof (degree_exp_cast_inv 0 c e H1) as He.
    destruct (degree_castop_cast_inv 0 c e Hc) as [Hca Hcb].
    destruct (degree_typ_cast_inv 0 c e Ht) as [Hta Htb].
    constructor.
    + apply degree_lc_castop. split; auto.
    + apply (IH (size_exp e)); [lia | split; [auto|split;auto] | reflexivity].
Qed.
(* ============================================================ *)
(* Section 6: WFT / AmberWFT degrees, TypCast degrees, Typing  *)
(* ============================================================ *)

Lemma WFT_degree : forall (D:tctx) (A:typ), WFT D A -> degree_typ_wrt_typ 0 A.
Proof.
  intros D A H. induction H.
  - constructor.
  - constructor.
  - constructor.
  - constructor; auto.
  - (* rec *) constructor. pick fresh X.
    apply (proj2 (degree_typ_open A 0 X)). apply H0. auto.
Qed.

Lemma WFT_lc_typ : forall (D:tctx) (A:typ), WFT D A -> lc_typ A.
Proof. intros D A H. apply degree_lc_typ. apply (WFT_degree D A H). Qed.

Lemma AmberWFT_degree : forall (AE:acctx) (A:typ), AmberWFT AE A -> degree_typ_wrt_typ 0 A.
Proof.
  intros AE A H.
  induction H as [AE Hwf|AE Hwf|AE X Y Hwf Hin|AE Y X Hwf Hin|AE A1 A2 H1 IH1 H2 IH2|L AE A Y Hprem IHprem].
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor; auto.
  - (* rec *) constructor. pick fresh Z. pick fresh W.
    apply (proj2 (degree_typ_open A 0 Z)).
    assert (Hz : Z \notin L) by auto.
    assert (Hw : W \notin L \u {{Z}}) by auto.
    exact (IHprem Z Hz W Hw).
Qed.

Lemma AmberWFT_lc_typ : forall (AE:acctx) (A:typ), AmberWFT AE A -> lc_typ A.
Proof. intros AE A H. apply degree_lc_typ. apply (AmberWFT_degree AE A H). Qed.

Lemma WFTmE_cons_inv : forall (G:ctx) (x:termvar) (A:typ),
  WFTmE (cons (x,A) G) -> WFTmE G /\ WFT nil A.
Proof. intros. inversion H. auto. Qed.

Lemma typcast_degree : forall (D:tctx) (E:cctx) (A B:typ) (c:castop),
  TypCast D E A B c ->
  degree_castop_wrt_castop 0 c /\ degree_castop_wrt_typ 0 c.
Proof.
  intros D E A B c H. induction H.
  - (* id *) split; constructor.
  - (* arrow *) split.
    + constructor; [apply (proj1 IHTypCast1) | apply (proj1 IHTypCast2)].
    + constructor; [apply (proj2 IHTypCast1) | apply (proj2 IHTypCast2)].
  - (* unfold *) split.
    + constructor.
    + constructor. apply (WFT_degree D (t_mu A) H).
  - (* fold *) split.
    + constructor.
    + constructor. apply (WFT_degree D (t_mu A) H).
  - (* seq *) split.
    + constructor; [apply (proj1 IHTypCast1) | apply (proj1 IHTypCast2)].
    + constructor; [apply (proj2 IHTypCast1) | apply (proj2 IHTypCast2)].
  - (* var *) split; constructor.
  - (* fix *) split.
    + apply (proj2 (degree_castop_fix_iff 0 (c_arrow c1 c2))).
      constructor.
      * pick fresh cx.
        apply (proj2 (degree_castop_wrt_castop_open c1 0 cx)).
        apply (proj1 (H0 cx Fr)).
      * pick fresh cx.
        apply (proj2 (degree_castop_wrt_castop_open c2 0 cx)).
        apply (proj1 (H2 cx Fr)).
    + apply (proj2 (degree_castop_typ_fix_iff 0 (c_arrow c1 c2))).
      constructor.
      * pick fresh cx.
        apply (proj1 (degree_castop_wrt_typ_open c1 0 0 cx)).
        apply (proj2 (H0 cx Fr)).
      * pick fresh cx.
        apply (proj1 (degree_castop_wrt_typ_open c2 0 0 cx)).
        apply (proj2 (H2 cx Fr)).
Qed.

Lemma typcast_lc_castop : forall (D:tctx) (E:cctx) (A B:typ) (c:castop),
  TypCast D E A B c -> lc_castop c.
Proof.
  intros D E A B c H. apply degree_lc_castop. apply (typcast_degree D E A B c H).
Qed.

Lemma typing_wftmE : forall (G:ctx) (e:exp) (T:typ), Typing G e T -> WFTmE G.
Proof.
  intros G e T H. induction H as [G i Hwf|G x A Hwf Hb|L G A1 e A2 Hprem IH|G e1 e2 A2 A1 H1 IH1 H2 IH2|G c e B A H IH TC|G e B A H IH AS].
  - auto.
  - auto.
  - (* abs *) pick fresh x. apply (proj1 (WFTmE_cons_inv G x A1 (IH x Fr))).
  - auto.
  - auto.
  - auto.
Qed.

Lemma typing_degree : forall (G:ctx) (e:exp) (T:typ), Typing G e T ->
  degree_exp_wrt_exp 0 e /\ degree_exp_wrt_castop 0 e /\ degree_exp_wrt_typ 0 e.
Proof.
  intros G e T H. induction H as [G i Hwf|G x A Hwf Hb|L G A1 e A2 Hprem IH|G e1 e2 A2 A1 H1 IH1 H2 IH2|G c e B A H IH TC|G e B A H IH AS].
  - (* int *) split; [constructor|split; constructor].
  - (* var *) split; [constructor|split; constructor].
  - (* abs *) split.
    + constructor. pick fresh x.
      apply (proj2 (degree_exp_wrt_exp_open e 0 x)).
      apply (proj1 (IH x Fr)).
    + split.
      * constructor. pick fresh x.
        apply (proj1 (degree_exp_wrt_castop_inv_open_exp e 0 0 x)).
        apply (proj1 (proj2 (IH x Fr))).
      * constructor.
        -- (* degree of annotation *) pick fresh x.
           apply (WFT_degree nil A1).
           apply (proj2 (WFTmE_cons_inv G x A1
                 (typing_wftmE (cons (x,A1) G) (open_exp_wrt_exp e (e_var_f x)) A2 (Hprem x Fr)))).
        -- pick fresh x.
           apply (proj1 (degree_exp_wrt_typ_inv_open_exp e 0 0 x)).
           apply (proj2 (proj2 (IH x Fr))).
  - (* app *) destruct IH1 as [H1a [H1b H1c]]. destruct IH2 as [H2a [H2b H2c]].
    split.
    + constructor; auto.
    + split; constructor; auto.
  - (* cast *) destruct IH as [He [Hec Het]].
    destruct (typcast_degree nil nil A B c TC) as [Hc Hct].
    split.
    + constructor. auto.
    + split; constructor; auto.
  - (* sub *) auto.
Qed.

Lemma typing_lc_exp : forall (G:ctx) (e:exp) (T:typ), Typing G e T -> lc_exp e.
Proof.
  intros G e T H. apply degree_lc_exp. apply (typing_degree G e T H).
Qed.
(* ============================================================ *)
(* Section 7: opening/substitution, weakening, term substitution *)
(* ============================================================ *)

Lemma degree_exp_open_id : forall (e:exp) (k:nat) (y:termvar) (d:nat),
  degree_exp_wrt_exp d e -> d <= k ->
  open_exp_wrt_exp_rec k (e_var_f y) e = e.
Proof.
  intros e. induction e as [n|x|i|A e IH|e1 IH1 e2 IH2|c e IH]; intros k y d Hd Hle; simpl.
  - (* var_b *) inversion Hd; subst.
    destruct (lt_eq_lt_dec n k) as [[l|eq]|r]; auto.
    + subst. exfalso; lia.
    + exfalso; lia.
  - reflexivity.
  - reflexivity.
  - (* abs *) inversion Hd; subst. simpl. f_equal.
    apply (IH (S k) y (S d)); auto. lia.
  - (* app *) inversion Hd; subst. simpl.
    rewrite (IH1 k y d); auto. rewrite (IH2 k y d); auto.
  - (* cast *) inversion Hd; subst. simpl. rewrite (IH k y d); auto.
Qed.

Lemma subst_exp_same : forall (u:exp) (x:termvar), subst_exp u x (e_var_f x) = u.
Proof. intros. simpl. apply eq_dec_same. Qed.

Lemma subst_exp_diff : forall (u:exp) (x y:termvar), x <> y ->
  subst_exp u x (e_var_f y) = e_var_f y.
Proof. intros. simpl. apply eq_dec_diff. auto. Qed.

Lemma subst_exp_open_exp_rec : forall (e:exp) (u:exp) (x y:termvar) (k:nat),
  y <> x -> lc_exp u ->
  subst_exp u x (open_exp_wrt_exp_rec k (e_var_f y) e) =
  open_exp_wrt_exp_rec k (e_var_f y) (subst_exp u x e).
Proof.
  intros e. induction e as [n|x0|i|A e IH|e1 IH1 e2 IH2|c e IH]; intros u x y k Hyx Hu; simpl.
  - (* var_b *) destruct (lt_eq_lt_dec n k) as [[l|eq]|r]; simpl.
    + reflexivity.
    + destruct (eq_dec y x) as [e|ne]; [exfalso; auto|reflexivity].
    + reflexivity.
  - (* var_f *) destruct (eq_dec x0 x) as [eq|ne].
    + subst x0. symmetry.
      apply (degree_exp_open_id u k y 0).
      * apply (proj1 (lc_exp_degree u Hu)).
      * lia.
    + simpl. reflexivity.
  - reflexivity.
  - (* abs *) rewrite (IH u x y (S k) Hyx Hu). reflexivity.
  - (* app *) rewrite (IH1 u x y k Hyx Hu), (IH2 u x y k Hyx Hu). reflexivity.
  - (* cast *) rewrite (IH u x y k Hyx Hu). reflexivity.
Qed.

Lemma in_swap_prefix : forall (T:Type) (a b:T) (P G:list T) (z:T),
  In z (P ++ a :: b :: G) -> In z (P ++ b :: a :: G).
Proof.
  intros. repeat rewrite in_app_iff in *. simpl in *. tauto.
Qed.

Lemma in_add_iff : forall (z x:atom) (s:atoms), z \in add x s <-> z = x \/ z \in s.
Proof. intros. split; intro H; fsetdec. Qed.

Lemma dom_swap_prefix_in : forall (P:ctx) (x y:atom) (A B:typ) (G:ctx) (z:atom),
  z \in dom (P ++ cons (x,A) (cons (y,B) G)) <->
  z \in dom (P ++ cons (y,B) (cons (x,A) G)).
Proof.
  intros P. induction P as [|p P IH].
  - intros. simpl. rewrite !in_add_iff. tauto.
  - intros x y A B G z. destruct p as [a t]. simpl.
    rewrite !in_add_iff. rewrite (IH x y A B G z). tauto.
Qed.

Lemma dom_ctx_mid_in : forall (P0 E:ctx) (X:atom) (Y:typ) (z:atom),
  z \in dom (P0 ++ E) -> z \in dom (P0 ++ cons (X,Y) E).
Proof.
  intros P0. induction P0 as [|p P0 IH].
  - intros. simpl. fsetdec.
  - intros E X Y z. destruct p as [a t]. simpl. intro H.
    rewrite in_add_iff in H. rewrite in_add_iff.
    destruct H as [Heq|Hin]; [left; auto | right; apply (IH E X Y z); auto].
Qed.

Lemma WFTmE_swap_prefix : forall (P:ctx) (x:atom) (A:typ) (y:atom) (B:typ) (G:ctx),
  x <> y ->
  WFTmE (P ++ cons (x,A) (cons (y,B) G)) ->
  WFTmE (P ++ cons (y,B) (cons (x,A) G)).
Proof.
  intros P. induction P as [|p P IH].
  - intros x A y B G Hxy H.
    simpl in *. inversion H; subst. inversion H3; subst.
    constructor.
    + constructor.
      * auto.
      * auto.
      * auto.
    + auto.
    + simpl. apply notin_add_3.
      * intro e; apply Hxy; symmetry; auto.
      * auto.
  - intros x A y B G Hxy H. destruct p as [z C].
    simpl in *. inversion H; subst.
    constructor.
    + apply (IH x A y B G); auto.
    + auto.
    + intro Hz. exfalso. apply H5.
      apply (proj2 (dom_swap_prefix_in P x y A B G z)). auto.
Qed.

Lemma typing_swap_prefix : forall (G:ctx) (e:exp) (T:typ), Typing G e T ->
  forall (P:ctx) (x:termvar) (A:typ) (y:termvar) (B:typ) (G':ctx),
    x <> y -> G = P ++ cons (x,A) (cons (y,B) G') ->
    Typing (P ++ cons (y,B) (cons (x,A) G')) e T.
Proof.
  intros G e T H. induction H as [G i Hwf|G z C Hwf Hb|L G A1 e A2 Hprem IH|G e1 e2 A2 A1 H1 IH1 H2 IH2|G c e B A H IH TC|G e B A H IH AS].
  - (* int *) intros P x0 A0 y0 B0 G' Hxy Heq. subst G.
    apply Typing_int. apply (WFTmE_swap_prefix P x0 A0 y0 B0 G'); auto.
  - (* var *) intros P x0 A0 y0 B0 G' Hxy Heq. subst G.
    apply Typing_var.
    + apply (WFTmE_swap_prefix P x0 A0 y0 B0 G'); auto.
    + apply in_swap_prefix with (b := (y0,B0)); auto.
  - (* abs *) intros P x0 A0 y0 B0 G' Hxy Heq. subst G.
    apply Typing_abs with (L := L).
    intros z Hz.
    apply (IH z Hz (cons (z,A1) P) x0 A0 y0 B0 G'); auto.
  - (* app *) intros P x0 A0 y0 B0 G' Hxy Heq. subst G.
    apply Typing_app with (A1 := A1).
    + apply (IH1 P x0 A0 y0 B0 G'); auto.
    + apply (IH2 P x0 A0 y0 B0 G'); auto.
  - (* cast *) intros P x0 A0 y0 B0 G' Hxy Heq. subst G.
    apply Typing_cast with (A := A).
    + apply (IH P x0 A0 y0 B0 G'); auto.
    + auto.
  - (* sub *) intros P x0 A0 y0 B0 G' Hxy Heq. subst G.
    apply Typing_sub with (A := A).
    + apply (IH P x0 A0 y0 B0 G'); auto.
    + auto.
Qed.

Lemma WFTmE_cons_notin : forall (G:ctx) (x:termvar) (A:typ),
  WFTmE (cons (x,A) G) -> x \notin dom G.
Proof. intros. inversion H. auto. Qed.

Lemma WFTmE_uniq : forall (G:ctx), WFTmE G -> uniq G.
Proof.
  intros G H. induction H.
  - constructor.
  - constructor; auto.
Qed.

Lemma WFTmE_cons : forall (G:ctx) (x:termvar) (A:typ),
  WFTmE G -> WFT nil A -> x \notin dom G -> WFTmE (cons (x,A) G).
Proof. intros. constructor; auto. Qed.

Lemma typing_weaken : forall (G:ctx) (e:exp) (T:typ), Typing G e T ->
  forall (x:termvar) (A:typ), WFTmE (cons (x,A) G) -> Typing (cons (x,A) G) e T.
Proof.
  intros G e T H. induction H as [G i Hwf|G z C Hwf Hb|L G A1 e A2 Hprem IH|G e1 e2 A2 A1 H1 IH1 H2 IH2|G c e B A H IH TC|G e B A H IH AS].
  - (* int *) intros x0 A0 Hwf'. apply Typing_int. auto.
  - (* var *) intros x0 A0 Hwf'. apply Typing_var; auto.
  - (* abs *) intros x0 A0 Hwf'.
    apply Typing_abs with (L := L \u {{x0}} \u dom G).
    intros y Hy.
    assert (HyL : y \notin L) by (simpl in Hy; fsetdec).
    assert (Hyx : y <> x0) by (intro; subst; simpl in Hy; fsetdec).
    assert (HyG : y \notin dom G) by (simpl in Hy; fsetdec).
    assert (Hwf_y : WFTmE (cons (x0,A0) (cons (y,A1) G))).
    { apply WFTmE_cons.
      - apply (typing_wftmE (cons (y,A1) G) (open_exp_wrt_exp e (e_var_f y)) A2).
        apply (Hprem y HyL).
      - apply (proj2 (WFTmE_cons_inv G x0 A0 Hwf')).
      - simpl. apply notin_add_3.
        + auto.
        + apply (WFTmE_cons_notin G x0 A0 Hwf'). }
    apply (typing_swap_prefix (cons (x0,A0) (cons (y,A1) G)) (open_exp_wrt_exp e (e_var_f y)) A2
           (IH y HyL x0 A0 Hwf_y) nil x0 A0 y A1 G).
    + auto.
    + reflexivity.
  - (* app *) intros x0 A0 Hwf'. apply Typing_app with (A1 := A1); auto.
  - (* cast *) intros x0 A0 Hwf'. apply Typing_cast with (A := A); auto.
  - (* sub *) intros x0 A0 Hwf'. apply Typing_sub with (A := A); auto.
Qed.
(* ============================================================ *)
(* Section 8: term substitution for Typing                     *)
(* ============================================================ *)

Lemma binds_cons_neq : forall (G:ctx) (x y:termvar) (A C:typ),
  x <> y -> binds y C (cons (x,A) G) -> binds y C G.
Proof.
  intros. simpl in H0. destruct H0 as [Heq|Hin].
  - inversion Heq. subst. exfalso; auto.
  - auto.
Qed.

Lemma in_mid_remove : forall (P Q:ctx) (x y:termvar) (A C:typ),
  x <> y -> In (y,C) (P ++ cons (x,A) Q) -> In (y,C) (P ++ Q).
Proof.
  intros P. induction P as [|p P IH].
  - intros. simpl in *. destruct H0 as [Heq|Hin].
    + inversion Heq. subst. exfalso; auto.
    + auto.
  - intros Q x y A C Hxy Hin. destruct p as [a t]. simpl in *.
    destruct Hin as [Heq|Hin].
    + left; auto.
    + right. apply (IH Q x y A C); auto.
Qed.

Lemma dom_mid_in : forall (P Q:ctx) (x:atom) (A:typ) (z:atom),
  z \in dom (P ++ Q) -> z \in dom (P ++ cons (x,A) Q).
Proof.
  intros P. induction P as [|p P IH].
  - intros. simpl. fsetdec.
  - intros Q x A z. destruct p as [a t]. simpl. intro H.
    rewrite in_add_iff in H. rewrite in_add_iff.
    destruct H as [Heq|Hin]; [left; auto | right; apply (IH Q x A z); auto].
Qed.

Lemma WFTmE_mid_remove : forall (P Q:ctx) (x:termvar) (A:typ),
  WFTmE (P ++ cons (x,A) Q) -> WFTmE (P ++ Q).
Proof.
  intros P. induction P as [|p P IH].
  - intros. simpl in *. apply (proj1 (WFTmE_cons_inv Q x A H)).
  - intros Q x A H. destruct p as [a t]. simpl in *.
    inversion H; subst.
    apply WFTmE_cons.
    + apply (IH Q x A). auto.
    + auto.
    + intro Hz. apply H5. apply (dom_mid_in P Q x A a). auto.
Qed.

Lemma dom_in : forall (G:ctx) (z:termvar) (D:typ), In (z,D) G -> z \in dom G.
Proof.
  intros G. induction G as [|p G IH].
  - intros. simpl in *. destruct H.
  - intros z D H. destruct p as [a b]. simpl in *. rewrite in_add_iff.
    destruct H as [Heq|Hin].
    + left. inversion Heq. auto.
    + right. apply (IH z D); auto.
Qed.

Lemma uniq_binds_eq : forall (G:ctx) (z:termvar) (C D:typ),
  uniq G -> binds z C G -> binds z D G -> C = D.
Proof.
  intros G. induction G as [|p G IH].
  - intros. simpl in *. destruct H0.
  - intros z C D Huq H1 H2. destruct p as [a b]. simpl in *.
    apply uniq_cons_iff in Huq. destruct Huq as [Huq Hnot].
    destruct H1 as [Heq|H1]; destruct H2 as [Heq2|H2].
    + inversion Heq; subst; inversion Heq2; subst; reflexivity.
    + inversion Heq; subst. exfalso. apply Hnot. apply dom_in in H2. auto.
    + inversion Heq2; subst. exfalso. apply Hnot. apply dom_in in H1. auto.
    + apply (IH z C D Huq); auto.
Qed.

Lemma subst_exp_open_exp : forall (e u:exp) (x y:termvar),
  y <> x -> lc_exp u ->
  subst_exp u x (open_exp_wrt_exp e (e_var_f y)) =
  open_exp_wrt_exp (subst_exp u x e) (e_var_f y).
Proof. intros. unfold open_exp_wrt_exp. apply subst_exp_open_exp_rec; auto. Qed.

Lemma typing_subst : forall (G:ctx) (e:exp) (T:typ), Typing G e T ->
  forall (P Q:ctx) (x:termvar) (A:typ), G = P ++ cons (x,A) Q ->
  forall (u:exp), Typing (P ++ Q) u A -> lc_exp u -> x \notin dom (P ++ Q) ->
  Typing (P ++ Q) (subst_exp u x e) T.
Proof.
  intros G e T H.
  induction H as [G' i Hwf|G' y C Hwf Hb|L G' A1 e0 A2 Hprem IH|G' e1 e2 A2 A1 H1 IH1 H2 IH2|G' c e0 B A' H IH TC|G' e0 B A' H IH AS];
  intros P Q x A Heq u Hu Hlu Hx; subst G'.
  - (* int *) apply Typing_int. apply WFTmE_mid_remove with (x:=x) (A:=A). auto.
  - (* var *) destruct (eq_dec y x) as [e|ne].
    + subst y. rewrite subst_exp_same.
      assert (Huq : uniq (P ++ cons (x,A) Q)) by (apply WFTmE_uniq; auto).
      assert (Hin : In (x,A) (P ++ cons (x,A) Q)).
      { apply in_or_app. right. simpl. left. auto. }
      assert (HCA : C = A) by (apply (uniq_binds_eq (P ++ cons (x,A) Q) x C A Huq Hb Hin)).
      subst C. auto.
    + assert (Hxy : x <> y) by (intro h; apply ne; symmetry; exact h).
      rewrite (subst_exp_diff u x y Hxy).
      apply Typing_var.
      * apply WFTmE_mid_remove with (x:=x) (A:=A). auto.
      * apply (in_mid_remove P Q x y A C Hxy Hb).
  - (* abs *) apply Typing_abs with (L := L \u {{x}} \u termfv_exp u \u dom (P ++ Q)).
    intros z Hz.
    assert (HzL : z \notin L) by (simpl in Hz; fsetdec).
    assert (Hzx : z <> x) by (intro; subst; simpl in Hz; fsetdec).
    assert (Hzu : z \notin termfv_exp u) by (simpl in Hz; fsetdec).
    assert (HzG : z \notin dom (P ++ Q)) by (simpl in Hz; fsetdec).
    assert (Htyping : Typing (cons (z,A1) (P ++ cons (x,A) Q)) (open_exp_wrt_exp e0 (e_var_f z)) A2).
    { apply (Hprem z HzL). }
    assert (Hwf_z : WFTmE (cons (z,A1) (P ++ cons (x,A) Q))).
    { apply (typing_wftmE _ _ _ Htyping). }
    assert (HWA1 : WFT nil A1).
    { apply (proj2 (WFTmE_cons_inv (P ++ cons (x,A) Q) z A1 Hwf_z)). }
    assert (HwfPQ : WFTmE (P ++ Q)).
    { apply (WFTmE_mid_remove P Q x A).
      apply (proj1 (WFTmE_cons_inv (P ++ cons (x,A) Q) z A1 Hwf_z)). }
    assert (Hty : Typing (cons (z,A1) (P ++ Q)) u A).
    { apply (typing_weaken (P ++ Q) u A Hu z A1).
      apply WFTmE_cons; auto. }
    assert (Hx' : x \notin dom (cons (z,A1) (P ++ Q))).
    { simpl. apply notin_add_3; auto. }
    assert (Hres := IH z HzL (cons (z,A1) P) Q x A eq_refl u Hty Hlu Hx').
    rewrite (subst_exp_open_exp e0 u x z Hzx Hlu) in Hres.
    exact Hres.
  - (* app *) apply Typing_app with (A1 := A1).
    + apply (IH1 P Q x A eq_refl u Hu Hlu Hx).
    + apply (IH2 P Q x A eq_refl u Hu Hlu Hx).
  - (* cast *) apply Typing_cast with (A := A').
    + apply (IH P Q x A eq_refl u Hu Hlu Hx).
    + auto.
  - (* sub *) apply Typing_sub with (A := A').
    + apply (IH P Q x A eq_refl u Hu Hlu Hx).
    + auto.
Qed.

Lemma typing_subst_head : forall (G:ctx) (x:termvar) (A:typ) (e:exp) (T:typ),
  Typing (cons (x,A) G) e T ->
  forall (u:exp), Typing G u A -> lc_exp u -> x \notin dom G ->
  Typing G (subst_exp u x e) T.
Proof.
  intros. apply (typing_subst (cons (x,A) G) e T H nil G x A eq_refl u H0 H1 H2).
Qed.
(* ============================================================ *)
(* Section 9: Amber well-formedness: freshness and weakening   *)
(* ============================================================ *)

Fixpoint freshA (Z:atom) (E:acctx) : Prop :=
  match E with
  | nil => True
  | (a,b) :: E' => Z <> a /\ Z <> b /\ freshA Z E'
  end.

Definition allA (E:acctx) := flat_map (fun p => fst p :: snd p :: nil) E.

Definition awfP (E:acctx) :=
  NoDup (allA E) /\ (forall a b, In (a,b) E -> a <> b).

Lemma in_singleton_iff : forall (x y:atom), x \in singleton y <-> x = y.
Proof. intros. split; intro H; fsetdec. Qed.

Lemma notin_union_iff : forall (x:atom) (s s':atoms),
  x \notin union s s' <-> x \notin s /\ x \notin s'.
Proof.
  intros. split.
  - intro H. split; intro Hin; apply H; [apply AtomSetImpl.union_2 | apply AtomSetImpl.union_3]; auto.
  - intros [H1 H2] Hin. apply AtomSetImpl.union_1 in Hin.
    destruct Hin as [Hin|Hin]; [apply H1|apply H2]; auto.
Qed.

Lemma notin_domA_freshA : forall (E:acctx) (Z:atom), Z \notin domA E <-> freshA Z E.
Proof.
  intros E. induction E as [|p E IH].
  - intro Z. simpl. split.
    + auto.
    + intro; fsetdec.
  - intro Z. destruct p as [a b]. simpl.
    rewrite notin_union_iff. rewrite notin_union_iff. rewrite in_singleton_iff. rewrite in_singleton_iff.
    rewrite (IH Z). tauto.
Qed.

Lemma freshA_app : forall (P Q:acctx) (Z:atom),
  freshA Z (P ++ Q) <-> freshA Z P /\ freshA Z Q.
Proof.
  intros P. induction P as [|p P IH].
  - intros. simpl. tauto.
  - intros Q Z. destruct p as [a b]. simpl. rewrite IH. tauto.
Qed.

Lemma freshA_cons : forall (a b Z:atom) (E:acctx),
  freshA Z ((a,b)::E) <-> Z <> a /\ Z <> b /\ freshA Z E.
Proof. intros. simpl. tauto. Qed.

Lemma allA_nil : allA nil = nil.
Proof. reflexivity. Qed.

Lemma allA_cons : forall (a b:atom) (E:acctx), allA ((a,b)::E) = a :: b :: allA E.
Proof. intros. reflexivity. Qed.

Lemma allA_app : forall (P Q:acctx), allA (P++Q) = allA P ++ allA Q.
Proof.
  intros P. induction P as [|p P IH]; intros Q.
  - reflexivity.
  - destruct p as [a b]. simpl. rewrite IH. reflexivity.
Qed.

Lemma domA_in_l : forall (E:acctx) (a b:atom), In (a,b) E -> a \in domA E.
Proof.
  intros E. induction E as [|p E IH].
  - intros. destruct H.
  - intros a b H. destruct p as [c d]. simpl in *.
    rewrite union_iff. rewrite union_iff.
    destruct H as [Heq|Hin].
    + inversion Heq. subst. left. rewrite in_singleton_iff. auto.
    + right. right. apply (IH a b); auto.
Qed.

Lemma domA_in_r : forall (E:acctx) (a b:atom), In (a,b) E -> b \in domA E.
Proof.
  intros E. induction E as [|p E IH].
  - intros. destruct H.
  - intros a b H. destruct p as [c d]. simpl in *.
    rewrite union_iff. rewrite union_iff.
    destruct H as [Heq|Hin].
    + inversion Heq. subst. right. left. rewrite in_singleton_iff. auto.
    + right. right. apply (IH a b); auto.
Qed.

Lemma domA_app_in_l : forall (P Q:acctx) (z:atom),
  z \in domA P -> z \in domA (P ++ Q).
Proof.
  intros P. induction P as [|p P IH].
  - intros. simpl in *. fsetdec.
  - intros Q z H. destruct p as [a b]. simpl in *.
    repeat rewrite union_iff in H. repeat rewrite union_iff.
    destruct H as [H|[H|H]]; auto.
Qed.

Lemma domA_app_in_r : forall (P Q:acctx) (z:atom),
  z \in domA Q -> z \in domA (P ++ Q).
Proof.
  intros P. induction P as [|p P IH].
  - intros. simpl. auto.
  - intros Q z H. destruct p as [a b]. simpl.
    repeat rewrite union_iff. right. right. apply (IH Q z); auto.
Qed.

Lemma domA_mid_in : forall (P0 E:acctx) (X Y z:atom),
  z \in domA (P0 ++ E) -> z \in domA (P0 ++ cons (X,Y) E).
Proof.
  intros P0. induction P0 as [|p P0 IH].
  - intros E X Y z H. simpl in *. repeat rewrite union_iff. right. right. auto.
  - intros E X Y z H. destruct p as [a b]. simpl in *.
    repeat rewrite union_iff in H. repeat rewrite union_iff.
    destruct H as [H|[H|H]]; auto.
Qed.

Lemma allA_in : forall (E:acctx) (z:atom), In z (allA E) <-> z \in domA E.
Proof.
  intros E. induction E as [|p E IH]; intro z.
  - simpl. split; [destruct 1 | fsetdec].
  - destruct p as [a b]. simpl.
    rewrite union_iff. rewrite union_iff. rewrite in_singleton_iff. rewrite in_singleton_iff.
    rewrite <- IH. split; intro H; destruct H as [H|[H|H]]; auto.
Qed.

Lemma amber_wf_iff : forall (E:acctx), AmberWF E <-> awfP E.
Proof.
  intro E. split.
  - intro H. induction H as [|E X Y Hwf IH HX HY HXY].
    + simpl. split; [constructor | intros a b Hin; simpl in Hin; destruct Hin].
    + destruct IH as [Hnd Hpair].
      change (NoDup (X :: Y :: allA E) /\
              (forall a b, In (a,b) ((X,Y)::E) -> a <> b)).
      split.
      * apply NoDup_cons.
        -- simpl. intros [Heq|Hin].
           ++ subst. auto.
           ++ apply HX. apply allA_in. auto.
        -- apply NoDup_cons.
           ++ intro Hin. apply HY. apply allA_in. auto.
           ++ auto.
      * intros a b Hin. simpl in Hin. destruct Hin as [Heq|Hin].
        -- inversion Heq. subst. auto.
        -- apply Hpair. auto.
  - intro H. induction E as [|p E IH].
    + constructor.
    + destruct p as [a b]. destruct H as [Hnd Hpair].
      apply AWF_cons.
      * apply IH. split.
        -- change (NoDup (a :: b :: allA E)) in Hnd.
           apply NoDup_cons_iff in Hnd. destruct Hnd as [_ Hnd].
           apply NoDup_cons_iff in Hnd. tauto.
        -- intros a' b' Hin. apply Hpair. right; auto.
      * (* a notin domA E *) intro Hin. apply allA_in in Hin.
        change (NoDup (a :: b :: allA E)) in Hnd.
        apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnot _].
        apply Hnot. right. auto.
      * (* b notin domA E *) intro Hin. apply allA_in in Hin.
        change (NoDup (a :: b :: allA E)) in Hnd.
        apply NoDup_cons_iff in Hnd. destruct Hnd as [_ Hnd].
        apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnot _].
        apply Hnot. auto.
      * apply Hpair. left. auto.
Qed.

Lemma perm_in : forall (A:Type) (l l':list A) (x:A),
  Permutation l l' -> In x l -> In x l'.
Proof.
  intros A l l' x H. induction H; simpl in *; auto.
  - intros [e|e]; auto.
  - intros [e|[e|e]]; auto.
Qed.

Lemma amber_wf_perm : forall (E1 E2:acctx),
  Permutation E1 E2 -> AmberWF E1 -> AmberWF E2.
Proof.
  intros E1 E2 Hp Hwf.
  apply amber_wf_iff in Hwf. apply amber_wf_iff.
  destruct Hwf as [Hnd Hpair]. split.
  - assert (HpermA : Permutation (allA E1) (allA E2)).
    { unfold allA. apply Permutation_flat_map. auto. }
    apply (Permutation_NoDup HpermA). auto.
  - intros a b Hin. apply Hpair. apply (perm_in (atom*atom) E2 E1 (a,b) (Permutation_sym Hp)). auto.
Qed.

Lemma amber_wft_perm : forall (E1:acctx) (A:typ),
  AmberWFT E1 A -> forall (E2:acctx), Permutation E1 E2 -> AmberWFT E2 A.
Proof.
  intros E1 A Hwt. induction Hwt as [E Hwf|E Hwf|E X Y Hwf Hin|E Y X Hwf Hin|E A1 A2 H1 IH1 H2 IH2|L E A0 Y0 Hprem IHprem];
  intros E2 Hp.
  - apply AWFT_nat. apply (amber_wf_perm E E2 Hp Hwf).
  - apply AWFT_top. apply (amber_wf_perm E E2 Hp Hwf).
  - apply AWFT_varl with (Y:=Y).
    + apply (amber_wf_perm E E2 Hp Hwf).
    + apply (perm_in (atom*atom) E E2 (X,Y) Hp). auto.
  - apply AWFT_varr with (X:=X).
    + apply (amber_wf_perm E E2 Hp Hwf).
    + apply (perm_in (atom*atom) E E2 (X,Y) Hp). auto.
  - apply AWFT_arrow.
    + apply (IH1 E2 Hp).
    + apply (IH2 E2 Hp).
  - apply (AWFT_rec L E2 A0 Y0).
    intros X HX Y HY.
    apply (IHprem X HX Y HY (cons (X,Y) E2)).
    apply perm_skip. auto.
Qed.

Lemma amber_wf_drop : forall (X Y:atom) (AE:acctx), AmberWF (cons (X,Y) AE) -> AmberWF AE.
Proof. intros. inversion H. auto. Qed.

Lemma amber_wf_weaken_front : forall (AE:acctx) (Z W:atom),
  AmberWF AE -> freshA Z AE -> freshA W AE -> Z <> W -> AmberWF (cons (Z,W) AE).
Proof.
  intros AE Z W Hwf HZ HW HZW.
  apply AWF_cons.
  - auto.
  - apply (proj2 (notin_domA_freshA AE Z)). auto.
  - apply (proj2 (notin_domA_freshA AE W)). auto.
  - auto.
Qed.

Lemma amber_wft_weaken_front : forall (AE:acctx) (A:typ),
  AmberWFT AE A -> forall (Z W:atom),
  freshA Z AE -> freshA W AE -> Z <> W -> AmberWFT (cons (Z,W) AE) A.
Proof.
  intros AE A Hwt. induction Hwt as [E Hwf|E Hwf|E X Y Hwf Hin|E Y X Hwf Hin|E A1 A2 H1 IH1 H2 IH2|L E A0 Y0 Hprem IHprem];
  intros Z W HZ HW HZW.
  - apply AWFT_nat. apply amber_wf_weaken_front; auto.
  - apply AWFT_top. apply amber_wf_weaken_front; auto.
  - apply AWFT_varl with (Y:=Y).
    + apply amber_wf_weaken_front; auto.
    + simpl. auto.
  - apply AWFT_varr with (X:=X).
    + apply amber_wf_weaken_front; auto.
    + simpl. auto.
  - apply AWFT_arrow; auto.
  - (* rec *) apply (AWFT_rec (L \u {{Z}} \u {{W}} \u domA E) (cons (Z,W) E) A0 Y0).
    intros X HX Y HY.
    assert (HXY : X <> Y) by (intro; subst; simpl in HY; fsetdec).
    assert (HZE : freshA Z E) by auto.
    assert (HWE : freshA W E) by auto.
    assert (HZX : Z <> X) by (intro e; apply HX; rewrite <- e; fsetdec).
    assert (HZY : Z <> Y) by (intro e; apply HY; rewrite <- e; fsetdec).
    assert (HWX : W <> X) by (intro e; apply HX; rewrite <- e; fsetdec).
    assert (HWY : W <> Y) by (intro e; apply HY; rewrite <- e; fsetdec).
    assert (HZX' : freshA Z (cons (X,Y) E)).
    { rewrite freshA_cons. split; [|split]; auto. }
    assert (HWX' : freshA W (cons (X,Y) E)).
    { rewrite freshA_cons. split; [|split]; auto. }
    assert (HXL : X \notin L) by (intro Hin; apply HX; fsetdec).
    assert (HYL : Y \notin L \u {{X}}) by (intro Hin; apply HY; fsetdec).
    specialize (IHprem X HXL Y HYL Z W HZX' HWX' HZW).
    (* swap the two bindings *)
    apply (amber_wft_perm (cons (Z,W) (cons (X,Y) E))
                          (open_typ_wrt_typ A0 (t_var_f X)) IHprem).
    apply perm_swap.
Qed.

(* ============================================================ *)
(* Section 10: type substitution preserves degrees and lc      *)
(* ============================================================ *)

Lemma degree_typ_mono : forall (A:typ) (k m:nat),
  degree_typ_wrt_typ k A -> k <= m -> degree_typ_wrt_typ m A.
Proof.
  intros A. induction A as [n|Y| | |A1 IH1 A2 IH2|A0 IH0]; intros k m Hd Hle.
  - inversion Hd; subst. constructor. lia.
  - constructor.
  - constructor.
  - constructor.
  - (* arrow *) inversion Hd; subst. constructor.
    + apply (IH1 k m); auto.
    + apply (IH2 k m); auto.
  - (* mu *) inversion Hd; subst. constructor.
    apply (IH0 (S k) (S m)); auto. lia.
Qed.

Lemma degree_typ_subst : forall (A:typ) (k:nat) (P:typ) (X:typevar),
  degree_typ_wrt_typ k A -> degree_typ_wrt_typ k P ->
  degree_typ_wrt_typ k (typsubst_typ P X A).
Proof.
  intros A. induction A as [n|Y| | |A1 IH1 A2 IH2|A0 IH0]; intros k P X HA HP; simpl.
  - (* bvar *) inversion HA; subst. constructor. auto.
  - (* fvar *) destruct (eq_dec Y X) as [e|n].
    + subst. auto.
    + constructor.
  - constructor.
  - constructor.
  - (* arrow *) inversion HA; subst. constructor; auto.
  - (* mu *) inversion HA; subst. constructor.
    apply (IH0 (S k) P X); auto.
    apply (degree_typ_mono P k (S k)); auto.
Qed.

Lemma lc_typ_subst : forall (A:typ) (P:typ) (X:typevar),
  lc_typ A -> lc_typ P -> lc_typ (typsubst_typ P X A).
Proof.
  intros A P X HA HP.
  apply degree_lc_typ.
  apply (degree_typ_subst A 0 P X).
  - apply lc_typ_degree. auto.
  - apply lc_typ_degree. auto.
Qed.

Lemma degree_typ_open_id : forall (A:typ) (d k:nat) (B:typ),
  degree_typ_wrt_typ d A -> d <= k -> open_typ_wrt_typ_rec k B A = A.
Proof.
  intros A. induction A as [n|Y| | |A1 IH1 A2 IH2|A0 IH0]; intros d k B HA Hle; simpl.
  - (* bvar *) inversion HA; subst.
    destruct (lt_eq_lt_dec n k) as [[l|e]|r]; auto.
    + subst. exfalso; lia.
    + exfalso; lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* arrow *) inversion HA; subst. simpl. rewrite (IH1 d k B); auto. rewrite (IH2 d k B); auto.
  - (* mu *) inversion HA; subst. simpl. rewrite (IH0 (S d) (S k) B); auto. lia.
Qed.

Lemma typsubst_open_gen : forall (A:typ) (k:nat) (P Q:typ) (X Y X':typevar),
  lc_typ P -> lc_typ Q -> X <> Y -> X' <> X -> X' <> Y ->
  typsubst_typ P X (typsubst_typ Q Y (open_typ_wrt_typ_rec k (t_var_f X') A)) =
  open_typ_wrt_typ_rec k (t_var_f X') (typsubst_typ P X (typsubst_typ Q Y A)).
Proof.
  intros A. induction A as [n|W| | |A1 IH1 A2 IH2|A0 IH0];
  intros k P Q X Y X' HP HQ HXY HX'X HX'Y; simpl.
  - (* bvar *) destruct (lt_eq_lt_dec n k) as [[l|e]|r]; simpl.
    + reflexivity.
    + subst.
      change (typsubst_typ P X (typsubst_typ Q Y (t_var_f X')) = t_var_f X').
      assert (H1 : typsubst_typ Q Y (t_var_f X') = t_var_f X').
      { apply typsubst_typ_diff. intro ee; apply HX'Y; symmetry; auto. }
      assert (H2 : typsubst_typ P X (t_var_f X') = t_var_f X').
      { apply typsubst_typ_diff. intro ee; apply HX'X; symmetry; auto. }
      rewrite H1, H2. reflexivity.
    + reflexivity.
  - (* fvar *)
    change (typsubst_typ P X (typsubst_typ Q Y (t_var_f W)) =
            open_typ_wrt_typ_rec k (t_var_f X') (typsubst_typ P X (typsubst_typ Q Y (t_var_f W)))).
    assert (HlcS : lc_typ (typsubst_typ P X (typsubst_typ Q Y (t_var_f W)))).
    { destruct (eq_dec W Y) as [eY|nY].
      - subst W.
        assert (E1 : typsubst_typ Q Y (t_var_f Y) = Q) by apply typsubst_typ_same.
        rewrite E1. apply lc_typ_subst; auto.
      - destruct (eq_dec W X) as [eX|nX].
        + subst W.
          assert (E1 : typsubst_typ Q Y (t_var_f X) = t_var_f X).
          { apply typsubst_typ_diff. intro ee; apply HXY; symmetry; auto. }
          assert (E2 : typsubst_typ P X (t_var_f X) = P) by apply typsubst_typ_same.
          rewrite E1, E2. auto.
        + assert (E1 : typsubst_typ Q Y (t_var_f W) = t_var_f W).
          { apply typsubst_typ_diff. intro ee; apply nY; symmetry; auto. }
          assert (E2 : typsubst_typ P X (t_var_f W) = t_var_f W).
          { apply typsubst_typ_diff. intro ee; apply nX; symmetry; auto. }
          rewrite E1, E2. constructor. }
    symmetry. apply degree_typ_open_id with (d:=0).
    + apply lc_typ_degree. auto.
    + lia.
  - (* int *) reflexivity.
  - (* top *) reflexivity.
  - (* arrow *) rewrite IH1; auto. rewrite IH2; auto.
  - (* mu *) rewrite IH0; auto.
Qed.

Lemma typefv_open_rec : forall (A:typ) (X Y:typevar) (k:nat),
  Y <> X -> Y \notin typefv_typ A ->
  Y \notin typefv_typ (open_typ_wrt_typ_rec k (t_var_f X) A).
Proof.
  intros A. induction A as [n|Z| | |A1 IH1 A2 IH2|A0 IH0]; intros X Y k HYX HY; simpl in *.
  - (* bvar *) destruct (lt_eq_lt_dec n k) as [[l|e]|r]; simpl.
    + fsetdec.
    + subst. fsetdec.
    + fsetdec.
  - (* fvar *) auto.
  - fsetdec.
  - fsetdec.
  - (* arrow *) rewrite notin_union_iff. rewrite notin_union_iff in HY. destruct HY as [H1 H2].
    split.
    + apply (IH1 X Y k); auto.
    + apply (IH2 X Y k); auto.
  - (* mu *) simpl. apply (IH0 X Y (S k)); auto.
Qed.


Lemma amber_wft_subst1 : forall (AE:acctx) (A:typ),
  AmberWFT AE A -> forall (X:atom) (P:typ),
  freshA X AE -> AmberWFT AE P -> AmberWFT AE (typsubst_typ P X A).
Proof.
  intros AE A Hwt. induction Hwt as [E Hwf|E Hwf|E Z W Hwf Hin|E W Z Hwf Hin|E A1 A2 H1 IH1 H2 IH2|L E A0 Y0 Hprem IHprem];
  intros X P HX HP.
  - apply AWFT_nat. auto.
  - apply AWFT_top. auto.
  - (* varl *)
    assert (HnX : Z <> X).
    { intro e. subst Z. apply (proj2 (notin_domA_freshA E X)) in HX.
      apply HX. apply (domA_in_l E X W). auto. }
    assert (E1 : typsubst_typ P X (t_var_f Z) = t_var_f Z).
    { apply typsubst_typ_diff. auto. }
    rewrite E1.
    apply AWFT_varl with (Y:=W).
    + auto.
    + auto.
  - (* varr *)
    assert (HnX : W <> X).
    { intro e. subst W. apply (proj2 (notin_domA_freshA E X)) in HX.
      apply HX. apply (domA_in_r E Z X). auto. }
    assert (E1 : typsubst_typ P X (t_var_f W) = t_var_f W).
    { apply typsubst_typ_diff. auto. }
    rewrite E1.
    apply AWFT_varr with (X:=Z).
    + auto.
    + auto.
  - (* arrow *) apply AWFT_arrow.
    + apply (IH1 X P HX HP).
    + apply (IH2 X P HX HP).
  - (* rec *) apply (AWFT_rec (L \u singleton X \u domA E) E (typsubst_typ P X A0) Y0).
    intros X' HX' Y' HY'.
    assert (HX'L : X' \notin L) by (simpl in HX'; fsetdec).
    assert (HX'X : X' <> X) by (simpl in HX'; fsetdec).
    assert (HX'E : freshA X' E) by (apply (proj1 (notin_domA_freshA E X')); simpl in HX'; fsetdec).
    assert (HY'L : Y' \notin L \u singleton X') by (simpl in HY'; fsetdec).
    assert (HY'X : Y' <> X) by (simpl in HY'; fsetdec).
    assert (HY'E : freshA Y' E) by (apply (proj1 (notin_domA_freshA E Y')); simpl in HY'; fsetdec).
    assert (HX'Y' : X' <> Y') by (intro; subst; simpl in HY'; fsetdec).
    assert (HlcP : lc_typ P) by (apply (AmberWFT_lc_typ E P); auto).
    pick fresh Yd for (typefv_typ A0 \u {{X}} \u {{X'}}).
    assert (HYdfv : Yd \notin typefv_typ A0) by fsetdec.
    assert (HYdX : Yd <> X) by fsetdec.
    assert (HYdX' : Yd <> X') by fsetdec.
    assert (HXd : X' <> Yd) by auto.
    pose proof (typsubst_open_gen A0 0 P t_int X Yd X' HlcP lc_t_int 
                  (fun e => HYdX (eq_sym e)) HX'X HXd) as Hcomm.
    assert (E2 : typsubst_typ t_int Yd (open_typ_wrt_typ_rec 0 (t_var_f X') A0) =
                 open_typ_wrt_typ_rec 0 (t_var_f X') A0).
    { apply typsubst_typ_id. apply typefv_open_rec; auto. }
    rewrite E2 in Hcomm.
    assert (E3 : typsubst_typ t_int Yd A0 = A0) by (apply typsubst_typ_id; auto).
    rewrite E3 in Hcomm.
    (* build the premise *)
    assert (IHres := IHprem X' HX'L Y' HY'L X P).
    assert (Hfres : freshA X ((X',Y')::E)).
    { rewrite freshA_cons. split; [|split]; auto. }
    assert (HwfP : AmberWFT ((X',Y')::E) P).
    { apply amber_wft_weaken_front; auto. }
    assert (Hres := IHres Hfres HwfP).
    change (typsubst_typ P X (open_typ_wrt_typ A0 (t_var_f X')) =
            open_typ_wrt_typ (typsubst_typ P X A0) (t_var_f X')) in Hcomm.
    rewrite Hcomm in Hres.
    exact Hres.
Qed.

Lemma amber_wf_mid_remove : forall (P0 E:acctx) (X Y:atom),
  AmberWF (P0 ++ cons (X,Y) E) -> AmberWF (P0 ++ E).
Proof.
  intros P0. induction P0 as [|p P0 IH].
  - intros. simpl in *. apply amber_wf_drop in H. auto.
  - intros E X Y H. destruct p as [a b]. simpl in *.
    inversion H; subst.
    apply AWF_cons.
    + apply (IH E X Y). auto.
    + intro Hin. apply H4. apply (domA_mid_in P0 E X Y a); auto.
    + intro Hin. apply H5. apply (domA_mid_in P0 E X Y b); auto.
    + auto.
Qed.


Lemma amber_wft_subst : forall (P0 E:acctx) (X Y:atom) (P Q:typ) (A:typ),
  X <> Y -> freshA X (P0++E) -> freshA Y (P0++E) ->
  AmberWFT (P0++E) P -> AmberWFT (P0++E) Q ->
  AmberWFT (P0 ++ cons (X,Y) E) A ->
  AmberWFT (P0++E) (typsubst_typ P X (typsubst_typ Q Y A)).
Proof.
  intros P0 E X Y P Q A HXY HX HY HP HQ Hwt.
  remember (P0 ++ cons (X,Y) E) as C eqn:EC.
  revert P0 E X Y P Q HXY HX HY HP HQ EC.
  induction Hwt as [C0 Hwf|C0 Hwf|C0 Z W Hwf Hin|C0 W Z Hwf Hin|C0 A1 A2 H1 IH1 H2 IH2|L C0 A0 Y0 Hprem IHprem];
  intros P0 E X Y P Q HXY HX HY HP HQ EC; subst C0.
  - (* nat *) apply AWFT_nat. apply amber_wf_mid_remove with (X:=X) (Y:=Y). auto.
  - (* top *) apply AWFT_top. apply amber_wf_mid_remove with (X:=X) (Y:=Y). auto.
  - (* varl *)
    apply in_app_iff in Hin. destruct Hin as [HinP0|Hin].
    + assert (HZX : Z <> X).
      { intro e; subst Z.
        apply (proj2 (notin_domA_freshA (P0++E) X)) in HX.
        apply HX. apply (domA_app_in_l P0 E X). apply (domA_in_l P0 X W). auto. }
      assert (HZY : Z <> Y).
      { intro e; subst Z.
        apply (proj2 (notin_domA_freshA (P0++E) Y)) in HY.
        apply HY. apply (domA_app_in_l P0 E Y). apply (domA_in_l P0 Y W). auto. }
      assert (E1 : typsubst_typ Q Y (t_var_f Z) = t_var_f Z).
      { apply typsubst_typ_diff. intro e; apply HZY; symmetry; auto. }
      assert (E2 : typsubst_typ P X (t_var_f Z) = t_var_f Z).
      { apply typsubst_typ_diff. intro e; apply HZX; symmetry; auto. }
      rewrite E1, E2. apply AWFT_varl with (Y:=W).
      * apply amber_wf_mid_remove with (X:=X) (Y:=Y). auto.
      * apply in_or_app. left. auto.
    + simpl in Hin. destruct Hin as [Heq|HinE].
      * inversion Heq. subst Z W.
        assert (E1 : typsubst_typ Q Y (t_var_f X) = t_var_f X).
        { apply typsubst_typ_diff. intro e; apply HXY; symmetry; auto. }
        rewrite E1. rewrite typsubst_typ_same. auto.
      * assert (HZX : Z <> X).
        { intro e; subst Z.
          apply (proj2 (notin_domA_freshA (P0++E) X)) in HX.
          apply HX. apply (domA_app_in_r P0 E X). apply (domA_in_l E X W). auto. }
        assert (HZY : Z <> Y).
        { intro e; subst Z.
          apply (proj2 (notin_domA_freshA (P0++E) Y)) in HY.
          apply HY. apply (domA_app_in_r P0 E Y). apply (domA_in_l E Y W). auto. }
        assert (E1 : typsubst_typ Q Y (t_var_f Z) = t_var_f Z).
        { apply typsubst_typ_diff. intro e; apply HZY; symmetry; auto. }
        assert (E2 : typsubst_typ P X (t_var_f Z) = t_var_f Z).
        { apply typsubst_typ_diff. intro e; apply HZX; symmetry; auto. }
        rewrite E1, E2. apply AWFT_varl with (Y:=W).
        -- apply amber_wf_mid_remove with (X:=X) (Y:=Y). auto.
        -- apply in_or_app. right. auto.
  - (* varr *)
    apply in_app_iff in Hin. destruct Hin as [HinP0|Hin].
    + assert (HWX : W <> X).
      { intro e; subst W.
        apply (proj2 (notin_domA_freshA (P0++E) X)) in HX.
        apply HX. apply (domA_app_in_l P0 E X). apply (domA_in_r P0 Z X). auto. }
      assert (HWY : W <> Y).
      { intro e; subst W.
        apply (proj2 (notin_domA_freshA (P0++E) Y)) in HY.
        apply HY. apply (domA_app_in_l P0 E Y). apply (domA_in_r P0 Z Y). auto. }
      assert (E1 : typsubst_typ Q Y (t_var_f W) = t_var_f W).
      { apply typsubst_typ_diff. intro e; apply HWY; symmetry; auto. }
      assert (E2 : typsubst_typ P X (t_var_f W) = t_var_f W).
      { apply typsubst_typ_diff. intro e; apply HWX; symmetry; auto. }
      rewrite E1, E2. apply AWFT_varr with (X:=Z).
      * apply amber_wf_mid_remove with (X:=X) (Y:=Y). auto.
      * apply in_or_app. left. auto.
    + simpl in Hin. destruct Hin as [Heq|HinE].
      * inversion Heq. subst Z W.
        assert (E1 : typsubst_typ Q Y (t_var_f Y) = Q) by apply typsubst_typ_same.
        rewrite E1. apply amber_wft_subst1 with (X:=X) (P:=P); auto.
      * assert (HWX : W <> X).
        { intro e; subst W.
          apply (proj2 (notin_domA_freshA (P0++E) X)) in HX.
          apply HX. apply (domA_app_in_r P0 E X). apply (domA_in_r E Z X). auto. }
        assert (HWY : W <> Y).
        { intro e; subst W.
          apply (proj2 (notin_domA_freshA (P0++E) Y)) in HY.
          apply HY. apply (domA_app_in_r P0 E Y). apply (domA_in_r E Z Y). auto. }
        assert (E1 : typsubst_typ Q Y (t_var_f W) = t_var_f W).
        { apply typsubst_typ_diff. intro e; apply HWY; symmetry; auto. }
        assert (E2 : typsubst_typ P X (t_var_f W) = t_var_f W).
        { apply typsubst_typ_diff. intro e; apply HWX; symmetry; auto. }
        rewrite E1, E2. apply AWFT_varr with (X:=Z).
        -- apply amber_wf_mid_remove with (X:=X) (Y:=Y). auto.
        -- apply in_or_app. right. auto.
  - (* arrow *) apply AWFT_arrow.
    + apply (IH1 P0 E X Y P Q HXY HX HY HP HQ eq_refl).
    + apply (IH2 P0 E X Y P Q HXY HX HY HP HQ eq_refl).
  - (* rec *) apply (AWFT_rec (L \u singleton X \u singleton Y \u domA (P0++E)) (P0++E) (typsubst_typ P X (typsubst_typ Q Y A0)) Y0).
    intros X' HX' Y' HY'.
    assert (HX'L : X' \notin L) by (simpl in HX'; fsetdec).
    assert (HX'X : X' <> X) by (simpl in HX'; fsetdec).
    assert (HX'Y : X' <> Y) by (simpl in HX'; fsetdec).
    assert (HX'E : freshA X' (P0++E)) by (apply (proj1 (notin_domA_freshA (P0++E) X')); simpl in HX'; fsetdec).
    assert (HY'L : Y' \notin L \u singleton X') by (simpl in HY'; fsetdec).
    assert (HY'X : Y' <> X) by (simpl in HY'; fsetdec).
    assert (HY'Y : Y' <> Y) by (simpl in HY'; fsetdec).
    assert (HY'E : freshA Y' (P0++E)) by (apply (proj1 (notin_domA_freshA (P0++E) Y')); simpl in HY'; fsetdec).
    assert (HX'Y' : X' <> Y') by (intro; subst; simpl in HY'; fsetdec).
    assert (HfX : freshA X ((cons (X',Y') P0)++E)).
    { rewrite freshA_app. rewrite freshA_cons.
      assert (HXP0 : freshA X P0) by (apply (proj1 (proj1 (freshA_app P0 E X) HX))).
      assert (HXE : freshA X E) by (apply (proj2 (proj1 (freshA_app P0 E X) HX))).
      split.
      + split; [|split]; auto.
      + auto. }
    assert (HfY : freshA Y ((cons (X',Y') P0)++E)).
    { rewrite freshA_app. rewrite freshA_cons.
      assert (HYP0 : freshA Y P0) by (apply (proj1 (proj1 (freshA_app P0 E Y) HY))).
      assert (HYE : freshA Y E) by (apply (proj2 (proj1 (freshA_app P0 E Y) HY))).
      split.
      + split; [|split]; auto.
      + auto. }
    assert (HwfP : AmberWFT ((cons (X',Y') P0)++E) P).
    { change (AmberWFT ((X',Y') :: (P0++E)) P).
      apply amber_wft_weaken_front with (Z:=X') (W:=Y'); auto. }
    assert (HwfQ : AmberWFT ((cons (X',Y') P0)++E) Q).
    { change (AmberWFT ((X',Y') :: (P0++E)) Q).
      apply amber_wft_weaken_front with (Z:=X') (W:=Y'); auto. }
    assert (Hres := IHprem X' HX'L Y' HY'L (cons (X',Y') P0) E X Y P Q HXY HfX HfY HwfP HwfQ eq_refl).
    assert (HlcP : lc_typ P) by (apply (AmberWFT_lc_typ (P0++E) P); auto).
    assert (HlcQ : lc_typ Q) by (apply (AmberWFT_lc_typ (P0++E) Q); auto).
    assert (HneX'Y : X' <> Y) by auto.
    assert (HneX'X : X' <> X) by auto.
    pose proof (typsubst_open_gen A0 0 P Q X Y X' HlcP HlcQ HXY HneX'X HneX'Y) as Hcomm.
    change (AmberWFT ((cons (X',Y') P0)++E)
              (open_typ_wrt_typ_rec 0 (t_var_f X') (typsubst_typ P X (typsubst_typ Q Y A0)))).
    rewrite <- Hcomm. exact Hres.
Qed.

Lemma allA_swap_mid : forall (P0 E:acctx) (a b:atom),
  Permutation (allA (P0 ++ (a,b) :: E)) (allA (P0 ++ (b,a) :: E)).
Proof.
  intros P0 E a b.
  repeat rewrite allA_app. repeat rewrite allA_cons.
  apply Permutation_app.
  - reflexivity.
  - apply perm_swap.
Qed.

Lemma amber_wf_swap_mid : forall (P0 E:acctx) (a b:atom),
  AmberWF (P0 ++ (a,b) :: E) -> AmberWF (P0 ++ (b,a) :: E).
Proof.
  intros P0 E a b H.
  apply amber_wf_iff in H. apply amber_wf_iff.
  destruct H as [Hnd Hpair]. split.
  - apply (Permutation_NoDup (allA_swap_mid P0 E a b) Hnd).
  - intros c d Hin.
    apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply Hpair. apply in_or_app. left. auto.
    + simpl in Hin. destruct Hin as [Heq|HinE].
      * inversion Heq. subst c d.
        assert (Hab : a <> b).
        { apply Hpair. apply in_or_app. right. left. auto. }
        intro e. apply Hab. symmetry. auto.
      * apply Hpair. apply in_or_app. right. right. auto.
Qed.

Lemma amber_wft_swap_mid : forall (C:acctx) (A:typ),
  AmberWFT C A ->
  forall (P0 E:acctx) (a b:atom), C = P0 ++ (a,b) :: E ->
  AmberWFT (P0 ++ (b,a) :: E) A.
Proof.
  intros C A Hwt.
  induction Hwt as [C0 Hwf|C0 Hwf|C0 X Y Hwf Hin|C0 Y X Hwf Hin|C0 A1 A2 H1 IH1 H2 IH2|L C0 A0 Y0 Hprem IHprem];
  intros P0 E a b HC; subst C0.
  - (* nat *) apply AWFT_nat.
    apply (amber_wf_swap_mid P0 E a b). auto.
  - (* top *) apply AWFT_top.
    apply (amber_wf_swap_mid P0 E a b). auto.
  - (* varl *)
    apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply AWFT_varl with (Y:=Y).
      * apply (amber_wf_swap_mid P0 E a b). auto.
      * apply in_or_app. left. auto.
    + simpl in Hin. destruct Hin as [Heq|HinE].
      * inversion Heq. subst X Y.
        apply AWFT_varr with (X:=b).
        -- apply (amber_wf_swap_mid P0 E a b). auto.
        -- apply in_or_app. right. left. auto.
      * apply AWFT_varl with (Y:=Y).
        -- apply (amber_wf_swap_mid P0 E a b). auto.
        -- apply in_or_app. right. right. auto.
  - (* varr *)
    apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply AWFT_varr with (X:=X).
      * apply (amber_wf_swap_mid P0 E a b). auto.
      * apply in_or_app. left. auto.
    + simpl in Hin. destruct Hin as [Heq|HinE].
      * inversion Heq. subst X Y.
        apply AWFT_varl with (Y:=a).
        -- apply (amber_wf_swap_mid P0 E a b). auto.
        -- apply in_or_app. right. left. auto.
      * apply AWFT_varr with (X:=X).
        -- apply (amber_wf_swap_mid P0 E a b). auto.
        -- apply in_or_app. right. right. auto.
  - (* arrow *) apply AWFT_arrow.
    + apply (IH1 P0 E a b eq_refl).
    + apply (IH2 P0 E a b eq_refl).
  - (* rec *) apply (AWFT_rec (L \u domA (P0++(b,a)::E)) (P0++(b,a)::E) A0 Y0).
    intros X HX Y HY.
    assert (HXL : X \notin L) by (simpl in HX; fsetdec).
    assert (HYL : Y \notin L \u singleton X) by (simpl in HY; fsetdec).
    exact (IHprem X HXL Y HYL ((X,Y)::P0) E a b eq_refl).
Qed.

Lemma amber_sub_wft : forall (AE:acctx) (A B:typ),
  AmberSubtyping AE A B -> AmberWFT AE A /\ AmberWFT AE B.
Proof.
  intros AE A B H. induction H as [AE Hwf|AE A Hwf Hwft|AE A1 A2 B1 B2 H1 IH1 H2 IH2|AE X Y Hwf Hin|L AE A B Hprem IHprem|AE A Hwf Hwft].
  - split; apply AWFT_nat; auto.
  - split; auto. apply AWFT_top. auto.
  - destruct IH1 as [HB1 HA1]. destruct IH2 as [HA2 HB2].
    split; apply AWFT_arrow; auto.
  - split.
    + apply AWFT_varl with (Y:=Y); auto.
    + apply AWFT_varr with (X:=X); auto.
  - split.
    + pick fresh Y0 for L.
      apply (AWFT_rec L AE A Y0).
      intros X HX Y' HY'.
      assert (HY'L : Y' \notin L) by (simpl in HY'; fsetdec).
      assert (HXY' : X <> Y') by (intro e; subst; simpl in HY'; fsetdec).
      assert (HXL : X \notin L \u singleton Y') by (simpl in HX; fsetdec).
      exact (proj1 (IHprem Y' HY'L X HXL)).
    + pick fresh Y0 for L.
      apply (AWFT_rec L AE B Y0).
      intros X HX Y' HY'.
      assert (HXL : X \notin L) by (simpl in HX; fsetdec).
      assert (HY'L : Y' \notin L \u singleton X) by (simpl in HY'; fsetdec).
      pose proof (proj2 (IHprem X HXL Y' HY'L)) as Hres.
      exact (amber_wft_swap_mid ((Y',X)::AE) (open_typ_wrt_typ B (t_var_f X))
               Hres nil AE Y' X eq_refl).
  - split; auto.
Qed.

Lemma amber_sub_wft_l : forall (AE:acctx) (A B:typ),
  AmberSubtyping AE A B -> AmberWFT AE A.
Proof. intros. apply amber_sub_wft in H. tauto. Qed.

Lemma amber_sub_wft_r : forall (AE:acctx) (A B:typ),
  AmberSubtyping AE A B -> AmberWFT AE B.
Proof. intros. apply amber_sub_wft in H. tauto. Qed.

Lemma amber_sub_perm : forall (AE1 AE2:acctx), Permutation AE1 AE2 ->
  forall (A B:typ), AmberSubtyping AE1 A B -> AmberSubtyping AE2 A B.
Proof.
  intros AE1 AE2 Hp A B H. revert AE2 Hp.
  induction H as [AE Hwf|AE A0 Hwf Hwft|AE A1 A2 B1 B2 H1 IH1 H2 IH2|AE X Y Hwf Hin|L AE A B Hprem IHprem|AE A0 Hwf Hwft];
  intros AE2 Hp.
  - apply ASub_nat. apply (amber_wf_perm AE AE2 Hp Hwf).
  - apply ASub_top.
    + apply (amber_wf_perm AE AE2 Hp Hwf).
    + apply (amber_wft_perm AE A0 Hwft AE2 Hp).
  - apply ASub_arrow.
    + apply (IH1 AE2 Hp).
    + apply (IH2 AE2 Hp).
  - apply ASub_var.
    + apply (amber_wf_perm AE AE2 Hp Hwf).
    + apply (perm_in (atom*atom) AE AE2 (X,Y) Hp). auto.
  - apply (ASub_rec L AE2 A B).
    intros Y HY X HX.
    apply (IHprem Y HY X HX (cons (X,Y) AE2)).
    apply perm_skip. auto.
  - apply ASub_self.
    + apply (amber_wf_perm AE AE2 Hp Hwf).
    + apply (amber_wft_perm AE (t_mu A0) Hwft AE2 Hp).
Qed.

Lemma amber_sub_weaken : forall (AE:acctx) (A B:typ),
  AmberSubtyping AE A B -> forall (Z W:atom),
  freshA Z AE -> freshA W AE -> Z <> W -> AmberSubtyping (cons (Z,W) AE) A B.
Proof.
  intros AE A B H. induction H as [AE Hwf|AE A0 Hwf Hwft|AE A1 A2 B1 B2 H1 IH1 H2 IH2|AE X Y Hwf Hin|L AE A B Hprem IHprem|AE A0 Hwf Hwft];
  intros Z W HZ HW HZW.
  - apply ASub_nat. apply amber_wf_weaken_front; auto.
  - apply ASub_top.
    + apply amber_wf_weaken_front; auto.
    + apply amber_wft_weaken_front; auto.
  - apply ASub_arrow.
    + apply (IH1 Z W); auto.
    + apply (IH2 Z W); auto.
  - apply ASub_var.
    + apply amber_wf_weaken_front; auto.
    + simpl. auto.
  - apply (ASub_rec (L \u {{Z}} \u {{W}} \u domA AE) (cons (Z,W) AE) A B).
    intros Y HY X HX.
    assert (HYL : Y \notin L) by (simpl in HY; fsetdec).
    assert (HYX : Y \notin L \u {{X}}) by (simpl in HY; fsetdec).
    assert (HYZ : Y <> Z) by (simpl in HY; fsetdec).
    assert (HYW : Y <> W) by (simpl in HY; fsetdec).
    assert (HXL : X \notin L) by (simpl in HX; fsetdec).
    assert (HXZ : X <> Z) by (simpl in HX; fsetdec).
    assert (HXW : X <> W) by (simpl in HX; fsetdec).
    assert (HfZ : freshA Z ((X,Y)::AE)).
    { rewrite freshA_cons. split; [|split]; auto. }
    assert (HfW : freshA W ((X,Y)::AE)).
    { rewrite freshA_cons. split; [|split]; auto. }
    assert (HXY : X <> Y) by (intro e; subst; simpl in HYX; fsetdec).
    assert (HXLY : X \notin L \u singleton Y) by (simpl in HXL; fsetdec).
    pose proof (IHprem Y HYL X HXLY Z W HfZ HfW HZW) as Hres.
    apply (amber_sub_perm (cons (Z,W) (cons (X,Y) AE)) (cons (X,Y) (cons (Z,W) AE))).
    + apply perm_swap.
    + exact Hres.
  - apply ASub_self.
    + apply amber_wf_weaken_front; auto.
    + apply amber_wft_weaken_front; auto.
Qed.

Lemma typefv_open_rec_subset : forall (A:typ) (k:nat) (X:typevar) (Z:atom),
  Z \in typefv_typ A -> Z \in typefv_typ (open_typ_wrt_typ_rec k (t_var_f X) A).
Proof.
  induction A as [n|Y| | |A1 IH1 A2 IH2|A0 IH0]; intros k X Z HZ; simpl in *.
  - destruct (lt_eq_lt_dec n k) as [[l|e]|r]; simpl in *; fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - apply union_iff in HZ. destruct HZ as [HZ|HZ].
    + apply AtomSetImpl.union_2. apply (IH1 k X Z HZ).
    + apply AtomSetImpl.union_3. apply (IH2 k X Z HZ).
  - apply (IH0 (S k) X Z HZ).
Qed.

Lemma amber_wft_typefv_domA : forall (AE:acctx) (A:typ),
  AmberWFT AE A -> forall Z, Z \in typefv_typ A -> Z \in domA AE.
Proof.
  intros AE A Hwt.
  induction Hwt as [E Hwf|E Hwf|E X Y Hwf Hin|E Y X Hwf Hin|E A1 A2 H1 IH1 H2 IH2|L E A0 Y0 Hprem IHprem];
  intros Z HZ.
  - simpl in HZ. fsetdec.
  - simpl in HZ. fsetdec.
  - simpl in HZ. rewrite in_singleton_iff in HZ. subst Z.
    apply (domA_in_l E X Y). auto.
  - simpl in HZ. rewrite in_singleton_iff in HZ. subst Z.
    apply (domA_in_r E X Y). auto.
  - simpl in HZ. apply union_iff in HZ. destruct HZ as [HZ|HZ].
    + apply (IH1 Z HZ).
    + apply (IH2 Z HZ).
  - simpl in HZ.
    pick fresh X0 for (L \u singleton Z).
    assert (HX0L : X0 \notin L) by fsetdec.
    pick fresh Y1 for (L \u singleton X0 \u singleton Z).
    assert (HY1 : Y1 \notin L \u singleton X0) by fsetdec.
    assert (HZopen : Z \in typefv_typ (open_typ_wrt_typ A0 (t_var_f X0))).
    { apply (typefv_open_rec_subset A0 0 X0 Z). auto. }
    assert (Hres := IHprem X0 HX0L Y1 HY1 Z HZopen).
    simpl in Hres. fsetdec.
Qed.

Lemma amber_subst : forall (P0 E:acctx) (X Y:atom) (P Q:typ) (A B:typ),
  X <> Y -> freshA X (P0++E) -> freshA Y (P0++E) ->
  AmberWFT (P0++E) P -> AmberWFT (P0++E) Q -> AmberSubtyping (P0++E) P Q ->
  AmberSubtyping (P0 ++ cons (X,Y) E) A B ->
  AmberSubtyping (P0++E) (typsubst_typ P X (typsubst_typ Q Y A))
                   (typsubst_typ P X (typsubst_typ Q Y B)).
Proof.
  intros P0 E X Y P Q A B HXY HX HY HP HQ HPQ Hsub.
  remember (P0 ++ cons (X,Y) E) as C eqn:EC.
  revert P0 E X Y P Q HXY HX HY HP HQ HPQ EC.
  induction Hsub as [C0 Hwf|C0 A0 Hwf Hwft|C0 A1 A2 B1 B2 H1 IH1 H2 IH2|C0 Z W Hwf Hin|L C0 A0 B0 Hprem IHprem|C0 A0 Hwf Hwft];
  intros P0 E X Y P Q HXY HX HY HP HQ HPQ EC; subst C0.
  - (* nat *) apply ASub_nat. apply amber_wf_mid_remove with (X:=X) (Y:=Y). auto.
  - (* top *) apply ASub_top.
    + apply amber_wf_mid_remove with (X:=X) (Y:=Y). auto.
    + apply (amber_wft_subst P0 E X Y P Q A0); auto.
  - (* arrow *) apply ASub_arrow.
    + apply (IH1 P0 E X Y P Q HXY HX HY HP HQ HPQ eq_refl).
    + apply (IH2 P0 E X Y P Q HXY HX HY HP HQ HPQ eq_refl).
  - (* var *)
    apply in_app_iff in Hin. destruct Hin as [HinP0|Hin].
    + assert (HZX : Z <> X).
      { intro e; subst Z.
        apply (proj2 (notin_domA_freshA (P0++E) X)) in HX.
        apply HX. apply (domA_app_in_l P0 E X). apply (domA_in_l P0 X W). auto. }
      assert (HZY : Z <> Y).
      { intro e; subst Z.
        apply (proj2 (notin_domA_freshA (P0++E) Y)) in HY.
        apply HY. apply (domA_app_in_l P0 E Y). apply (domA_in_l P0 Y W). auto. }
      assert (HWX : W <> X).
      { intro e; subst W.
        apply (proj2 (notin_domA_freshA (P0++E) X)) in HX.
        apply HX. apply (domA_app_in_l P0 E X). apply (domA_in_r P0 Z X). auto. }
      assert (HWY : W <> Y).
      { intro e; subst W.
        apply (proj2 (notin_domA_freshA (P0++E) Y)) in HY.
        apply HY. apply (domA_app_in_l P0 E Y). apply (domA_in_r P0 Z Y). auto. }
      assert (E1 : typsubst_typ Q Y (t_var_f Z) = t_var_f Z).
      { apply typsubst_typ_diff. intro e; apply HZY; symmetry; auto. }
      assert (E2 : typsubst_typ P X (t_var_f Z) = t_var_f Z).
      { apply typsubst_typ_diff. intro e; apply HZX; symmetry; auto. }
      assert (E3 : typsubst_typ Q Y (t_var_f W) = t_var_f W).
      { apply typsubst_typ_diff. intro e; apply HWY; symmetry; auto. }
      assert (E4 : typsubst_typ P X (t_var_f W) = t_var_f W).
      { apply typsubst_typ_diff. intro e; apply HWX; symmetry; auto. }
      rewrite E1, E2, E3, E4. apply ASub_var.
      * apply amber_wf_mid_remove with (X:=X) (Y:=Y). auto.
      * apply in_or_app. left. auto.
    + simpl in Hin. destruct Hin as [Heq|HinE].
      * inversion Heq. subst Z W.
        assert (E1 : typsubst_typ Q Y (t_var_f X) = t_var_f X).
        { apply typsubst_typ_diff. intro e; apply HXY; symmetry; auto. }
        assert (E2 : typsubst_typ P X (t_var_f X) = P) by apply typsubst_typ_same.
        rewrite E1, E2.
        assert (HXQ : X \notin typefv_typ Q).
        { intro Hf. apply (proj2 (notin_domA_freshA (P0++E) X)) in HX.
          apply HX. apply (amber_wft_typefv_domA (P0++E) Q HQ X Hf). }
        assert (E3 : typsubst_typ P X (typsubst_typ Q Y (t_var_f Y)) = Q).
        { rewrite typsubst_typ_same. apply typsubst_typ_id. auto. }
        rewrite E3. auto.
      * assert (HZX : Z <> X).
        { intro e; subst Z.
          apply (proj2 (notin_domA_freshA (P0++E) X)) in HX.
          apply HX. apply (domA_app_in_r P0 E X). apply (domA_in_l E X W). auto. }
        assert (HZY : Z <> Y).
        { intro e; subst Z.
          apply (proj2 (notin_domA_freshA (P0++E) Y)) in HY.
          apply HY. apply (domA_app_in_r P0 E Y). apply (domA_in_l E Y W). auto. }
        assert (HWX : W <> X).
        { intro e; subst W.
          apply (proj2 (notin_domA_freshA (P0++E) X)) in HX.
          apply HX. apply (domA_app_in_r P0 E X). apply (domA_in_r E Z X). auto. }
        assert (HWY : W <> Y).
        { intro e; subst W.
          apply (proj2 (notin_domA_freshA (P0++E) Y)) in HY.
          apply HY. apply (domA_app_in_r P0 E Y). apply (domA_in_r E Z Y). auto. }
        assert (E1 : typsubst_typ Q Y (t_var_f Z) = t_var_f Z).
        { apply typsubst_typ_diff. intro e; apply HZY; symmetry; auto. }
        assert (E2 : typsubst_typ P X (t_var_f Z) = t_var_f Z).
        { apply typsubst_typ_diff. intro e; apply HZX; symmetry; auto. }
        assert (E3 : typsubst_typ Q Y (t_var_f W) = t_var_f W).
        { apply typsubst_typ_diff. intro e; apply HWY; symmetry; auto. }
        assert (E4 : typsubst_typ P X (t_var_f W) = t_var_f W).
        { apply typsubst_typ_diff. intro e; apply HWX; symmetry; auto. }
        rewrite E1, E2, E3, E4. apply ASub_var.
        -- apply amber_wf_mid_remove with (X:=X) (Y:=Y). auto.
        -- apply in_or_app. right. auto.
  - (* rec *) apply (ASub_rec (L \u singleton X \u singleton Y \u domA (P0++E)) (P0++E) (typsubst_typ P X (typsubst_typ Q Y A0)) (typsubst_typ P X (typsubst_typ Q Y B0))).
    intros Yb HYb Xa HXa.
    assert (HYbL : Yb \notin L) by (simpl in HYb; fsetdec).
    assert (HYbX : Yb <> X) by (simpl in HYb; fsetdec).
    assert (HYbY : Yb <> Y) by (simpl in HYb; fsetdec).
    assert (HYbE : freshA Yb (P0++E)) by (apply (proj1 (notin_domA_freshA (P0++E) Yb)); simpl in HYb; fsetdec).
    assert (HXaL : Xa \notin L \u singleton Yb) by (simpl in HXa; fsetdec).
    assert (HXaX : Xa <> X) by (simpl in HXa; fsetdec).
    assert (HXaY : Xa <> Y) by (simpl in HXa; fsetdec).
    assert (HXaE : freshA Xa (P0++E)) by (apply (proj1 (notin_domA_freshA (P0++E) Xa)); simpl in HXa; fsetdec).
    assert (HXaYb : Xa <> Yb) by (intro e; subst; simpl in HXa; fsetdec).
    assert (HfX : freshA X ((cons (Xa,Yb) P0)++E)).
    { rewrite freshA_app. rewrite freshA_cons.
      assert (HXP0 : freshA X P0) by (apply (proj1 (proj1 (freshA_app P0 E X) HX))).
      assert (HXE : freshA X E) by (apply (proj2 (proj1 (freshA_app P0 E X) HX))).
      split.
      + split; [|split]; auto.
      + auto. }
    assert (HfY : freshA Y ((cons (Xa,Yb) P0)++E)).
    { rewrite freshA_app. rewrite freshA_cons.
      assert (HYP0 : freshA Y P0) by (apply (proj1 (proj1 (freshA_app P0 E Y) HY))).
      assert (HYE : freshA Y E) by (apply (proj2 (proj1 (freshA_app P0 E Y) HY))).
      split.
      + split; [|split]; auto.
      + auto. }
    assert (HwfP : AmberWFT ((cons (Xa,Yb) P0)++E) P).
    { change (AmberWFT ((Xa,Yb) :: (P0++E)) P).
      apply amber_wft_weaken_front with (Z:=Xa) (W:=Yb); auto. }
    assert (HwfQ : AmberWFT ((cons (Xa,Yb) P0)++E) Q).
    { change (AmberWFT ((Xa,Yb) :: (P0++E)) Q).
      apply amber_wft_weaken_front with (Z:=Xa) (W:=Yb); auto. }
    assert (HsubPQ : AmberSubtyping ((cons (Xa,Yb) P0)++E) P Q).
    { change (AmberSubtyping ((Xa,Yb) :: (P0++E)) P Q).
      apply amber_sub_weaken with (Z:=Xa) (W:=Yb); auto. }
    assert (Hres := IHprem Yb HYbL Xa HXaL (cons (Xa,Yb) P0) E X Y P Q HXY HfX HfY HwfP HwfQ HsubPQ eq_refl).
    assert (HlcP : lc_typ P) by (apply (AmberWFT_lc_typ (P0++E) P); auto).
    assert (HlcQ : lc_typ Q) by (apply (AmberWFT_lc_typ (P0++E) Q); auto).
    assert (HneXaX : Xa <> X) by auto.
    assert (HneXaY : Xa <> Y) by auto.
    assert (HneYbX : Yb <> X) by auto.
    assert (HneYbY : Yb <> Y) by auto.
    assert (HcommA : typsubst_typ P X (typsubst_typ Q Y (open_typ_wrt_typ A0 (t_var_f Xa)))
                     = open_typ_wrt_typ (typsubst_typ P X (typsubst_typ Q Y A0)) (t_var_f Xa)).
    { pose proof (typsubst_open_gen A0 0 P Q X Y Xa HlcP HlcQ HXY HneXaX HneXaY) as Hc.
      exact Hc. }
    assert (HcommB : typsubst_typ P X (typsubst_typ Q Y (open_typ_wrt_typ B0 (t_var_f Yb)))
                     = open_typ_wrt_typ (typsubst_typ P X (typsubst_typ Q Y B0)) (t_var_f Yb)).
    { pose proof (typsubst_open_gen B0 0 P Q X Y Yb HlcP HlcQ HXY HneYbX HneYbY) as Hc.
      exact Hc. }
    rewrite HcommA in Hres. rewrite HcommB in Hres.
    exact Hres.
  - (* self *) apply ASub_self.
    + apply amber_wf_mid_remove with (X:=X) (Y:=Y). auto.
    + apply (amber_wft_subst P0 E X Y P Q (t_mu A0)); auto.
Qed.
(* ============================================================ *)
(* Section 12: reflexive-transitive closure of subtyping       *)
(* ============================================================ *)

Inductive sub_star (AE:acctx) : typ -> typ -> Prop :=
  | ss_refl : forall A, sub_star AE A A
  | ss_step : forall A B, AmberSubtyping AE A B -> sub_star AE A B
  | ss_trans : forall A B C, sub_star AE A B -> sub_star AE B C -> sub_star AE A C.

Lemma ss_one : forall (AE:acctx) (A B:typ),
  AmberSubtyping AE A B -> sub_star AE A B.
Proof. intros. apply ss_step. auto. Qed.

Lemma ss_from_top_gen : forall (AE:acctx) (X Y:typ),
  sub_star AE X Y -> X = t_top -> Y = t_top.
Proof.
  intros AE X Y H.
  induction H as [T|A B Hsub|A B C H1 IH1 H2 IH2].
  - auto.
  - intros Heq. subst A. inversion Hsub; subst; auto.
  - intros Heq. apply IH2. apply IH1. auto.
Qed.

Lemma ss_from_top : forall (AE:acctx) (Y:typ),
  sub_star AE t_top Y -> Y = t_top.
Proof.
  intros AE Y H. exact (ss_from_top_gen AE t_top Y H eq_refl).
Qed.

Lemma ss_mu_head : forall (AE:acctx) (A:typ) (Y:typ),
  sub_star AE (t_mu A) Y -> Y = t_top \/ (exists C, Y = t_mu C).
Proof.
  intros AE A Y H. remember (t_mu A) as X eqn:EX. revert A EX.
  induction H as [T|X Y Hsub|X Y Z H1 IH1 H2 IH2]; intros A EX.
  - inversion EX. subst. right. exists A. auto.
  - subst X. inversion Hsub; subst.
    + left. auto.
    + (* rec *) right. exists B. auto.
    + (* self *) right. exists A. auto.
  - subst X. pose proof (IH1 A eq_refl) as HY.
    destruct HY as [HYtop|HYmu].
    + left. subst Y. apply ss_from_top in H2. auto.
    + destruct HYmu as [C HC]. subst Y.
      exact (IH2 C eq_refl).
Qed.

Lemma ss_arrow_head : forall (AE:acctx) (A1 A2:typ) (Y:typ),
  sub_star AE (t_arrow A1 A2) Y -> Y = t_top \/ (exists C1 C2, Y = t_arrow C1 C2).
Proof.
  intros AE A1 A2 Y H. remember (t_arrow A1 A2) as X eqn:EX. revert A1 A2 EX.
  induction H as [T|X Y Hsub|X Y Z H1 IH1 H2 IH2]; intros A1 A2 EX.
  - inversion EX. subst. right. exists A1, A2. auto.
  - subst X. inversion Hsub; subst.
    + left. auto.
    + (* arrow *) right. exists B1, B2. auto.
  - subst X. pose proof (IH1 A1 A2 eq_refl) as HY.
    destruct HY as [HYtop|HYa].
    + left. subst Y. apply ss_from_top in H2. auto.
    + destruct HYa as [C1 [C2 HC]]. subst Y.
      exact (IH2 C1 C2 eq_refl).
Qed.

Lemma ss_arrow_inv : forall (AE:acctx) (A1 A2 B1 B2:typ),
  sub_star AE (t_arrow A1 A2) (t_arrow B1 B2) ->
  sub_star AE B1 A1 /\ sub_star AE A2 B2.
Proof.
  intros AE A1 A2 B1 B2 H. remember (t_arrow A1 A2) as X eqn:EX.
  remember (t_arrow B1 B2) as Y eqn:EY. revert A1 A2 B1 B2 EX EY.
  induction H as [T|X Y Hsub|X Y Z H1 IH1 H2 IH2]; intros A1 A2 B1 B2 EX EY.
  - inversion EX; subst. injection EY as HB1 HB2. subst. split; apply ss_refl.
  - subst X. subst Y. inversion Hsub; subst.
    split; apply ss_step; auto.
  - subst X.
    assert (Hhead := ss_arrow_head AE A1 A2 Y H1).
    destruct Hhead as [Htop|Harr].
    + subst Y.
      assert (HZ : Z = t_top) by (apply ss_from_top in H2; auto).
      rewrite HZ in EY. inversion EY.
    + destruct Harr as [C1 [C2 HC]]. subst Y.
      destruct (IH1 A1 A2 C1 C2 eq_refl eq_refl) as [Hg1 Hg2].
      destruct (IH2 C1 C2 B1 B2 eq_refl EY) as [Hg3 Hg4].
      split.
      * apply ss_trans with (B:=C1); auto.
      * apply ss_trans with (B:=C2); auto.
Qed.
(* ============================================================ *)
(* Section 13: unfolding lemma for iso-recursive subtyping     *)
(* ============================================================ *)

Lemma amber_mu_rec_unfold : forall (A B:typ) (L:vars),
  AmberSubtyping nil (t_mu A) (t_mu B) ->
  (forall Y, Y \notin L -> forall X, X \notin L \u {{Y}} ->
     AmberSubtyping (cons (X,Y) nil) (open_typ_wrt_typ A (t_var_f X)) (open_typ_wrt_typ B (t_var_f Y))) ->
  AmberSubtyping nil (open_typ_wrt_typ A (t_mu A)) (open_typ_wrt_typ B (t_mu B)).
Proof.
  intros A B L Hmu Hprem.
  pick fresh X for (L \u typefv_typ A \u typefv_typ B).
  pick fresh Y for (L \u typefv_typ A \u typefv_typ B \u {{X}}).
  assert (HXL : X \notin L) by fsetdec.
  assert (HYL : Y \notin L \u {{X}}) by fsetdec.
  assert (HXY : X <> Y) by (intro; subst; fsetdec).
  assert (HXA : X \notin typefv_typ A) by fsetdec.
  assert (HYB : Y \notin typefv_typ B) by fsetdec.
  assert (HYA : Y \notin typefv_typ A) by fsetdec.
  assert (HXB : X \notin typefv_typ B) by fsetdec.
  assert (HYL0 : Y \notin L) by (simpl in HYL; fsetdec).
  assert (HXL' : X \notin L \u {{Y}}) by (simpl in HXL; fsetdec).
  assert (Hsub := Hprem Y HYL0 X HXL').
  assert (HwfA : AmberWFT nil (t_mu A)) by (apply amber_sub_wft_l in Hmu; auto).
  assert (HwfB : AmberWFT nil (t_mu B)) by (apply amber_sub_wft_r in Hmu; auto).
  pose proof (amber_subst nil nil X Y (t_mu A) (t_mu B)
                (open_typ_wrt_typ A (t_var_f X)) (open_typ_wrt_typ B (t_var_f Y))
                HXY I I HwfA HwfB Hmu Hsub) as Hres.
  (* simplify the substitutions *)
  assert (HsA1 : typsubst_typ (t_mu B) Y (open_typ_wrt_typ A (t_var_f X)) =
                 open_typ_wrt_typ A (t_var_f X)).
  { apply typsubst_typ_id.
    apply typefv_open_rec; auto. }
  assert (HsA2 : typsubst_typ (t_mu A) X (open_typ_wrt_typ A (t_var_f X)) =
                 open_typ_wrt_typ A (t_mu A)).
  { apply typsubst_typ_open_self. auto. }
  assert (HsB : typsubst_typ (t_mu A) X (typsubst_typ (t_mu B) Y (open_typ_wrt_typ B (t_var_f Y)))
              = open_typ_wrt_typ B (t_mu B)).
  { rewrite (typsubst_typ_comm (open_typ_wrt_typ B (t_var_f Y)) (t_mu A) (t_mu B) X Y HXY HXB HYA).
    rewrite (typsubst_typ_id (open_typ_wrt_typ B (t_var_f Y)) (t_mu A) X).
    - apply typsubst_typ_open_self. auto.
    - apply (typefv_open_rec B Y X 0); auto. }
  rewrite HsA1 in Hres. rewrite HsA2 in Hres. rewrite HsB in Hres.
  exact Hres.
Qed.

Lemma ss_mu_unfold_gen : forall (X Y:typ),
  sub_star nil X Y ->
  forall (A:typ), X = t_mu A -> forall (B:typ), Y = t_mu B ->
  sub_star nil (open_typ_wrt_typ A (t_mu A)) (open_typ_wrt_typ B (t_mu B)).
Proof.
  intros X Y H. induction H as [T|X Y Hsub|X Y Z H1 IH1 H2 IH2];
  intros A EX B EY.
  - inversion EX; subst. injection EY as HAB. subst. apply ss_refl.
  - subst X. subst Y. inversion Hsub; subst.
    + apply ss_step. apply (amber_mu_rec_unfold A B L Hsub H2). 
    + apply ss_refl.
  - subst X.
    pose proof (ss_mu_head nil A Y H1) as HZ.
    destruct HZ as [HZtop|HZmu].
    + subst Y.
      assert (HZtop' : Z = t_top) by (apply ss_from_top in H2; auto).
      rewrite HZtop' in EY. inversion EY.
    + destruct HZmu as [C HC]. subst Y.
      apply ss_trans with (B := open_typ_wrt_typ C (t_mu C)).
      * apply (IH1 A eq_refl C eq_refl).
      * apply (IH2 C eq_refl B EY).
Qed.

(* ============================================================ *)
(* Section 14: typing closure and inversion lemmas             *)
(* ============================================================ *)

Lemma typing_ss : forall (G:ctx) (e:exp) (A B:typ),
  Typing G e A -> sub_star nil A B -> Typing G e B.
Proof.
  intros G e A B Hty Hss. revert Hty.
  induction Hss as [T|T1 T2 Hsub|T1 T2 T3 Hs1 IH1 Hs2 IH2]; intros Hty.
  - exact Hty.
  - apply Typing_sub with (A := T1); auto.
  - apply IH2. apply IH1. auto.
Qed.

Lemma typcast_id_inv : forall (D:tctx) (E:cctx) (A B:typ),
  TypCast D E A B c_id -> A = B.
Proof. intros. inversion H. auto. Qed.

Lemma typcast_arrow_inv : forall (D:tctx) (E:cctx) (A B:typ) (c1 c2:castop),
  TypCast D E A B (c_arrow c1 c2) ->
  exists A1 A2 B1 B2, A = t_arrow A1 A2 /\ B = t_arrow B1 B2 /\
    TypCast D E A1 B1 c1 /\ TypCast D E A2 B2 c2.
Proof.
  intros. inversion H; subst.
  exists A1, B1, A2, B2. auto.
Qed.

Lemma typcast_seq_inv : forall (D:tctx) (E:cctx) (A B:typ) (c1 c2:castop),
  TypCast D E A B (c_seq c1 c2) ->
  exists C, TypCast D E A C c1 /\ TypCast D E C B c2.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma typcast_unfold_inv : forall (D:tctx) (E:cctx) (A B:typ) (T:typ),
  TypCast D E A B (c_unfold T) ->
  exists A0, T = t_mu A0 /\ A = t_mu A0 /\ B = open_typ_wrt_typ A0 (t_mu A0).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma typcast_fold_inv : forall (D:tctx) (E:cctx) (A B:typ) (T:typ),
  TypCast D E A B (c_fold T) ->
  exists A0, T = t_mu A0 /\ A = open_typ_wrt_typ A0 (t_mu A0) /\ B = t_mu A0.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma typing_app_inv : forall (G:ctx) (e1 e2:exp) (T:typ),
  Typing G (e_app e1 e2) T ->
  exists A1 A2, Typing G e1 (t_arrow A1 A2) /\ Typing G e2 A1 /\ sub_star nil A2 T.
Proof.
  intros G e1 e2 T H. remember (e_app e1 e2) as e eqn:E. revert e1 e2 E.
  induction H as [G i Hwf|G x A Hwf Hb|L G A1 e0 A2 Hprem IH|G e1 e2 A2 A1 H1 IH1 H2 IH2|G c e0 B A H IH TC|G e B0 A H IH AS];
  intros e1' e2' E.
  - inversion E.
  - inversion E.
  - inversion E.
  - inversion E. subst. exists A1, A2. split; [|split]; auto. apply ss_refl.
  - inversion E.
  - inversion E. subst.
    destruct (IH e1' e2' eq_refl) as [A1 [A2 [H1 [H2 HS]]]].
    exists A1, A2. split; [|split]; auto.
    apply ss_trans with (B := A); auto. apply ss_step. auto.
Qed.

Lemma typing_abs_inv_arrow : forall (G:ctx) (A:typ) (e0:exp) (B1 B2:typ),
  Typing G (e_abs A e0) (t_arrow B1 B2) ->
  exists (A2:typ) (L:vars),
     (forall x, x \notin L -> Typing (cons (x,A) G) (open_exp_wrt_exp e0 (e_var_f x)) A2)
     /\ sub_star nil B1 A /\ sub_star nil A2 B2.
Proof.
  intros G A e0 B1 B2 H. remember (e_abs A e0) as e eqn:E1.
  remember (t_arrow B1 B2) as T eqn:E2. revert A e0 B1 B2 E1 E2.
  induction H as [G i Hwf|G x A0 Hwf Hb|L G A1 e A2 Hprem IH|G e1 e2 A2 A1 H1 IH1 H2 IH2|G c e B A0 H IH TC|G e0 B0 A0 H IH AS];
  intros A' e0' B1' B2' E1 E2.
  - inversion E1.
  - inversion E1.
  - inversion E1. subst. inversion E2. subst.
    exists B2', L. split; [|split]; auto; apply ss_refl.
  - inversion E1.
  - inversion E1.
  - inversion E1; subst.
    inversion AS; subst.
    destruct (IH A' e0' A1 A2 eq_refl eq_refl) as [A2' [L' [Hbody [HS1 HS2]]]].
    exists A2', L'. split; [|split]; auto.
    + apply ss_trans with (B := A1); [apply ss_step; auto | exact HS1].
    + apply ss_trans with (B := A2); [exact HS2 | apply ss_step; auto].
Qed.

Lemma typing_cast_inv : forall (G:ctx) (c:castop) (e0:exp) (T:typ),
  Typing G (e_cast c e0) T ->
  exists A B, Typing G e0 A /\ TypCast nil nil A B c /\ sub_star nil B T.
Proof.
  intros G c e0 T H. remember (e_cast c e0) as e eqn:E. revert c e0 E.
  induction H as [G i Hwf|G x A Hwf Hb|L G A1 e A2 Hprem IH|G e1 e2 A2 A1 H1 IH1 H2 IH2|G c e0 B A H IH TC|G e0 B0 A H IH AS];
  intros c' e0' E.
  - inversion E.
  - inversion E.
  - inversion E.
  - inversion E.
  - inversion E. subst. exists A, B. split; [|split]; auto. apply ss_refl.
  - inversion E; subst.
    destruct (IH c' e0' eq_refl) as [A1 [B1 [H1 [H2 HS]]]].
    exists A1, B1. split; [|split]; auto.
    apply ss_trans with (B := A); [exact HS | apply ss_step; auto].
Qed.
(* ============================================================ *)
(* Section 15: cast reversal                                   *)
(* ============================================================ *)

Fixpoint swap_cctx (E:cctx) : cctx :=
  match E with
  | nil => nil
  | (a,(A,B)) :: E' => (a,(B,A)) :: swap_cctx E'
  end.

Lemma dom_swap_cctx_in : forall (E:cctx) (z:atom),
  z \in dom (swap_cctx E) <-> z \in dom E.
Proof.
  intros E. induction E as [|p E IH]; intro z.
  - simpl. tauto.
  - destruct p as [a [A B]]. simpl. rewrite !in_add_iff. rewrite IH. tauto.
Qed.

Lemma uniq_swap_cctx : forall (E:cctx), uniq E -> uniq (swap_cctx E).
Proof.
  intros E H. induction H as [|x a E HE Hx IH].
  - constructor.
  - destruct a as [A B]. simpl. apply uniq_cons.
    + exact Hx.
    + rewrite <- dom_swap_cctx_in in IH. exact IH.
Qed.

Lemma in_swap_cctx : forall (E:cctx) (cx:castvar) (A B:typ),
  In (cx, (A,B)) E -> In (cx, (B,A)) (swap_cctx E).
Proof.
  intros E. induction E as [|p E IH]; intros cx A B Hin.
  - destruct Hin.
  - destruct p as [a [A0 B0]]. simpl in *. destruct Hin as [Heq|Hin].
    + inversion Heq. subst. left. auto.
    + right. apply IH. auto.
Qed.

Lemma rev_open_castop : forall (c:castop) (cx:castvar) (k:nat),
  rev_cast (open_castop_wrt_castop_rec k (c_var_f cx) c) =
  open_castop_wrt_castop_rec k (c_var_f cx) (rev_cast c).
Proof.
  intros c. induction c as [n|x| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IH];
  intros cx k; simpl.
  - destruct (lt_eq_lt_dec n k) as [[l|e]|r]; simpl; auto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma typcast_rev : forall (D:tctx) (E:cctx) (A B:typ) (c:castop),
  TypCast D E A B c -> TypCast D (swap_cctx E) B A (rev_cast c).
Proof.
  intros D E A B c H. induction H.
  - (* id *) simpl. apply TCast_id; auto. apply uniq_swap_cctx. auto.
  - (* arrow *) simpl. apply TCast_arrow; auto.
  - (* unfold *) simpl. apply TCast_fold; auto. apply uniq_swap_cctx. auto.
  - (* fold *) simpl. apply TCast_unfold; auto. apply uniq_swap_cctx. auto.
  - (* seq *) simpl. eapply TCast_seq; eauto.
  - (* var *) simpl. apply TCast_var.
    + auto.
    + auto.
    + apply uniq_swap_cctx. auto.
    + apply in_swap_cctx. auto.
  - (* fix *) simpl. apply (TCast_fix L D (swap_cctx E) A2 B2 A1 B1).
    + intros cx Hx.
      change (TypCast D ((cx, (t_arrow A2 B2, t_arrow A1 B1)) :: swap_cctx E) A2 A1
                (open_castop_wrt_castop_rec 0 (c_var_f cx) (rev_cast c1))).
      rewrite <- (rev_open_castop c1 cx 0).
      apply (H0 cx Hx).
    + intros cx Hx.
      change (TypCast D ((cx, (t_arrow A2 B2, t_arrow A1 B1)) :: swap_cctx E) B2 B1
                (open_castop_wrt_castop_rec 0 (c_var_f cx) (rev_cast c2))).
      rewrite <- (rev_open_castop c2 cx 0).
      apply (H2 cx Hx).
Qed.
(* ============================================================ *)
(* Section 16: TypCast context permutation and weakening        *)
(* ============================================================ *)

Definition allD (E:cctx) := List.map fst E.

Lemma in_allD : forall (E:cctx) (z:atom), In z (allD E) <-> z \in dom E.
Proof.
  intros E. induction E as [|p E IH]; intro z.
  - simpl. split; [destruct 1 | fsetdec].
  - destruct p as [a [A B]]. simpl. rewrite in_add_iff. rewrite <- IH. simpl.
    split; intros [Heq|Hin].
    + left. symmetry. auto.
    + right. auto.
    + left. symmetry. auto.
    + right. auto.
Qed.

Lemma uniq_iff_allD : forall (E:cctx), uniq E <-> NoDup (allD E).
Proof.
  intro E. induction E as [|p E IH].
  - simpl. split; [constructor | constructor].
  - destruct p as [a [A B]]. simpl.
    rewrite uniq_cons_iff. rewrite NoDup_cons_iff. rewrite <- IH. rewrite in_allD. tauto.
Qed.

Lemma uniq_perm : forall (E1 E2:cctx), Permutation E1 E2 -> uniq E1 -> uniq E2.
Proof.
  intros E1 E2 Hp Huq.
  apply uniq_iff_allD in Huq. apply uniq_iff_allD.
  assert (Hperm : Permutation (allD E1) (allD E2)).
  { unfold allD. apply Permutation_map. auto. }
  apply (Permutation_NoDup Hperm). auto.
Qed.

Lemma dom_app_l : forall (A:Type) (l1 l2:list (atom*A)) (z:atom),
  z \in dom l1 -> z \in dom (l1++l2).
Proof.
  intros A l1. induction l1 as [|p l1 IH]; intros l2 z Hin.
  - simpl in *. fsetdec.
  - destruct p as [a b]. simpl in *.
    rewrite in_add_iff in *. destruct Hin as [Heq|Hin].
    + left. auto.
    + right. apply (IH l2 z Hin).
Qed.

Lemma dom_mid_in_cctx : forall (A:Type) (P0 E:list (atom*A)) (cx:atom) (v:A) (z:atom),
  z \in dom (P0++E) -> z \in dom (P0 ++ (cx,v)::E).
Proof.
  intros A P0. induction P0 as [|p P0 IH]; intros E cx v z Hin.
  - simpl in *. rewrite in_add_iff. right. auto.
  - destruct p as [a b]. simpl in *. rewrite in_add_iff in *.
    destruct Hin as [Heq|Hin].
    + left. auto.
    + right. apply (IH E cx v z Hin).
Qed.

Lemma uniq_mid_remove : forall (P0 E:cctx) (cx:castvar) (S T:typ),
  uniq (P0 ++ cons (cx,(S,T)) E) -> uniq (P0 ++ E).
Proof.
  intros P0. induction P0 as [|p P0 IH].
  - intros. simpl in *. apply uniq_cons_iff in H. tauto.
  - intros E cx S T H. destruct p as [a [A B]]. simpl in *.
    apply uniq_cons_iff in H. destruct H as [Htail Hnot].
    rewrite uniq_cons_iff. split.
    + apply (IH E cx S T); auto.
    + intro Hin. apply Hnot.
      apply (dom_mid_in_cctx (typ*typ) P0 E cx (S,T) a). auto.
Qed.

Lemma typcast_perm : forall (D:tctx) (E1:cctx) (A B:typ) (c:castop),
  TypCast D E1 A B c -> forall (E2:cctx), Permutation E1 E2 -> TypCast D E2 A B c.
Proof.
  intros D E1 A B c H. induction H as [D E0 A Hwf Huq|D E0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2|D E0 A Hwf Huq|D E0 A Hwf Huq|D E0 A C c1 c2 B H1 IH1 H2 IH2|D E0 A B0 cx HwfA HwfB Huq Hin|L D E0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2];
  intros E2 Hp.
  - apply TCast_id; auto. apply (uniq_perm E0 E2); auto.
  - apply TCast_arrow.
    + apply (IH1 E2 Hp).
    + apply (IH2 E2 Hp).
  - apply TCast_unfold; auto. apply (uniq_perm E0 E2); auto.
  - apply TCast_fold; auto. apply (uniq_perm E0 E2); auto.
  - apply TCast_seq with (B := B); auto.
  - apply TCast_var.
    + auto.
    + auto.
    + apply (uniq_perm E0 E2); auto.
    + apply (perm_in (atom * (typ*typ)) E0 E2 (cx,(A,B0)) Hp). auto.
  - apply (TCast_fix L D E2 A1 B1 A2 B2 c1 c2).
    + intros cx Hx. apply (IH1 cx Hx). apply perm_skip. auto.
    + intros cx Hx. apply (IH2 cx Hx). apply perm_skip. auto.
Qed.

Lemma typcast_weaken : forall (D:tctx) (E:cctx) (A B:typ) (c:castop),
  TypCast D E A B c -> forall (z:castvar) (U V:typ),
  z \notin dom E -> TypCast D (cons (z,(U,V)) E) A B c.
Proof.
  intros D E A B c H. induction H as [D E0 A Hwf Huq|D E0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2|D E0 A Hwf Huq|D E0 A Hwf Huq|D E0 A C c1 c2 B H1 IH1 H2 IH2|D E0 A B0 cx HwfA HwfB Huq Hin|L D E0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2];
  intros z U V Hz.
  - apply TCast_id; auto.
  - apply TCast_arrow; auto.
  - apply TCast_unfold; auto.
  - apply TCast_fold; auto.
  - apply TCast_seq with (B := B); auto.
  - apply TCast_var.
    + auto.
    + auto.
    + apply uniq_cons_iff. split; auto.
    + simpl. auto.
  - apply (TCast_fix (L \u singleton z) D (cons (z,(U,V)) E0) A1 B1 A2 B2 c1 c2).
    + intros cx Hx.
      assert (HcxL : cx \notin L) by (simpl in Hx; fsetdec).
      assert (Hcxz : cx <> z) by (simpl in Hx; fsetdec).
      assert (Hzc : z \notin dom (cons (cx,(t_arrow A1 B1, t_arrow A2 B2)) E0)).
      { simpl. rewrite in_add_iff. intros [Heq|Hin].
        - subst. auto.
        - auto. }
      pose proof (IH1 cx HcxL z U V Hzc) as Hw.
      apply (typcast_perm D (cons (z,(U,V)) (cons (cx,(t_arrow A1 B1, t_arrow A2 B2)) E0))
                         A1 A2 (open_castop_wrt_castop c1 (c_var_f cx)) Hw).
      apply perm_swap.
    + intros cx Hx.
      assert (HcxL : cx \notin L) by (simpl in Hx; fsetdec).
      assert (Hcxz : cx <> z) by (simpl in Hx; fsetdec).
      assert (Hzc : z \notin dom (cons (cx,(t_arrow A1 B1, t_arrow A2 B2)) E0)).
      { simpl. rewrite in_add_iff. intros [Heq|Hin].
        - subst. auto.
        - auto. }
      pose proof (IH2 cx HcxL z U V Hzc) as Hw.
      apply (typcast_perm D (cons (z,(U,V)) (cons (cx,(t_arrow A1 B1, t_arrow A2 B2)) E0))
                         B1 B2 (open_castop_wrt_castop c2 (c_var_f cx)) Hw).
      apply perm_swap.
Qed.
(* ============================================================ *)
(* Section 17: cast-variable substitution in TypCast           *)
(* ============================================================ *)

Lemma in_dom_gen : forall (X:Type) (l:list (atom*X)) (z:atom) (a:X),
  In (z,a) l -> z \in dom l.
Proof.
  intros X l. induction l as [|p l IH]; intros z a Hin.
  - destruct Hin.
  - destruct p as [y c]. simpl in *. rewrite in_add_iff in *.
    destruct Hin as [Heq|Hin].
    + inversion Heq; subst. left. auto.
    + right. apply (IH z a Hin).
Qed.

Lemma uniq_pair_eq : forall (X:Type) (l:list (atom*X)) (x:atom) (a b:X),
  uniq l -> In (x,a) l -> In (x,b) l -> a = b.
Proof.
  intros X l. induction l as [|p l IH].
  - intros. destruct H0.
  - intros x a b Huq H1 H2. destruct p as [y c]. simpl in *.
    apply uniq_cons_iff in Huq. destruct Huq as [Huq Hnot].
    destruct H1 as [Heq|H1]; destruct H2 as [Heq2|H2].
    + inversion Heq; inversion Heq2; subst; auto.
    + inversion Heq; subst. exfalso. apply Hnot. apply (in_dom_gen X l x b); auto.
    + inversion Heq2; subst. exfalso. apply Hnot. apply (in_dom_gen X l x a); auto.
    + apply (IH x a b Huq); auto.
Qed.

Lemma in_cctx_mid_remove : forall (P0 E:cctx) (cx:castvar) (S T:typ) (x:atom) (b1 b2:typ),
  x <> cx -> In (x,(b1,b2)) (P0 ++ cons (cx,(S,T)) E) -> In (x,(b1,b2)) (P0 ++ E).
Proof.
  intros P0. induction P0 as [|p P0 IH].
  - intros. simpl in *. destruct H0 as [Heq|Hin].
    + inversion Heq; subst. exfalso; auto.
    + auto.
  - intros E cx S T x b1 b2 Hne Hin. destruct p as [a [A B]]. simpl in *.
    destruct Hin as [Heq|Hin].
    + left; auto.
    + right. apply (IH E cx S T x b1 b2); auto.
Qed.

Lemma castsubst_castop_diff : forall (d:castop) (cx x:castvar),
  x <> cx -> castsubst_castop d cx (c_var_f x) = c_var_f x.
Proof. intros. simpl. apply eq_dec_diff. auto. Qed.

Lemma castsubst_castop_same : forall (d:castop) (cx:castvar),
  castsubst_castop d cx (c_var_f cx) = d.
Proof. intros. simpl. apply eq_dec_same. Qed.

Lemma degree_castop_open_id : forall (c:castop) (d k:nat) (R:castop),
  degree_castop_wrt_castop d c -> d <= k -> open_castop_wrt_castop_rec k R c = c.
Proof.
  intros c. induction c as [n|x| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IH];
  intros d k R Hdeg Hle; simpl.
  - (* var_b *) inversion Hdeg; subst.
    destruct (lt_eq_lt_dec n k) as [[l|e]|r]; auto.
    + subst. exfalso; lia.
    + exfalso; lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - inversion Hdeg; subst. simpl. rewrite (IH1 d k R); auto. rewrite (IH2 d k R); auto.
  - inversion Hdeg; subst. simpl. rewrite (IH1 d k R); auto. rewrite (IH2 d k R); auto.
  - inversion Hdeg; subst. simpl. rewrite (IH (S d) (S k) R); auto. lia.
Qed.

Lemma lc_castop_open_id : forall (c:castop), lc_castop c ->
  forall (k:nat) (R:castop), open_castop_wrt_castop_rec k R c = c.
Proof.
  intros c H k R.
  apply degree_castop_open_id with (d:=0).
  - apply lc_castop_degree. auto.
  - lia.
Qed.

Lemma castsubst_castop_id : forall (d:castop) (cx:castvar) (c:castop),
  cx \notin castfv_castop c -> castsubst_castop d cx c = c.
Proof.
  intros d cx c. induction c as [n|x| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IH];
  intro Hf; simpl in *.
  - reflexivity.
  - destruct (eq_dec x cx) as [e|n].
    + subst. exfalso. apply Hf. fsetdec.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; auto; fsetdec.
  - rewrite IH1, IH2; auto; fsetdec.
  - rewrite IH; auto.
Qed.

Lemma castsubst_castop_open : forall (c:castop) (d:castop) (cx:castvar) (k:nat),
  lc_castop d -> cx \notin castfv_castop c ->
  castsubst_castop d cx (open_castop_wrt_castop_rec k (c_var_f cx) c) =
  open_castop_wrt_castop_rec k d c.
Proof.
  intros c. induction c as [n|x| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IH];
  intros d cx k Hlc Hf; simpl in *.
  - (* var_b *) destruct (lt_eq_lt_dec n k) as [[l|e]|r]; simpl.
    + reflexivity.
    + subst. apply castsubst_castop_same.
    + reflexivity.
  - (* var_f *) destruct (eq_dec x cx) as [e|ne].
    + subst. exfalso. apply Hf. fsetdec.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1; auto; try fsetdec. rewrite IH2; auto; fsetdec.
  - rewrite IH1; auto; try fsetdec. rewrite IH2; auto; fsetdec.
  - rewrite IH; auto.
Qed.

Lemma castsubst_castop_open_gen : forall (c:castop) (d:castop) (cx cx':castvar) (k:nat),
  lc_castop d -> cx' <> cx ->
  castsubst_castop d cx (open_castop_wrt_castop_rec k (c_var_f cx') c) =
  open_castop_wrt_castop_rec k (c_var_f cx') (castsubst_castop d cx c).
Proof.
  intros c. induction c as [n|x| |A|A|c1 IH1 c2 IH2|c1 IH1 c2 IH2|c IH];
  intros d cx cx' k Hlc Hne.
  - (* var_b *) simpl. destruct (lt_eq_lt_dec n k) as [[l|e]|r]; simpl.
    + reflexivity.
    + subst n. destruct (eq_dec cx' cx) as [e2|ne2].
      * exfalso. apply Hne. auto.
      * reflexivity.
    + reflexivity.
  - (* var_f *) simpl. destruct (eq_dec x cx) as [e|ne]; simpl.
    + subst x. symmetry. apply lc_castop_open_id. auto.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH1; auto. rewrite IH2; auto.
  - simpl. rewrite IH1; auto. rewrite IH2; auto.
  - simpl. rewrite IH; auto.
Qed.

Lemma typcast_subst_mid : forall (D:tctx) (P0 E:cctx) (cx:castvar) (S T:typ)
  (A B:typ) (c:castop),
  TypCast D (P0 ++ cons (cx,(S,T)) E) A B c ->
  forall (d:castop), lc_castop d -> TypCast D (P0 ++ E) S T d ->
  TypCast D (P0 ++ E) A B (castsubst_castop d cx c).
Proof.
  intros D P0 E cx S T A B c H.
  remember (P0 ++ cons (cx,(S,T)) E) as C eqn:EC.
  revert P0 E cx S T EC.
  induction H as [D C A0 Hwf Huq|D C A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2|D C A0 Hwf Huq|D C A0 Hwf Huq|D C A0 C0 c1 c2 B0 H1 IH1 H2 IH2|D C A0 B0 cy HwfA HwfB Huq Hin|L D C A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2];
  intros P0 E cx S T EC d Hlc Hd; subst C.
  - (* id *) apply TCast_id.
    + auto.
    + apply (uniq_mid_remove P0 E cx S T). auto.
  - (* arrow *) simpl. apply TCast_arrow.
    + apply (IH1 P0 E cx S T eq_refl d Hlc Hd).
    + apply (IH2 P0 E cx S T eq_refl d Hlc Hd).
  - (* unfold *) simpl. apply TCast_unfold.
    + auto.
    + apply (uniq_mid_remove P0 E cx S T). auto.
  - (* fold *) simpl. apply TCast_fold.
    + auto.
    + apply (uniq_mid_remove P0 E cx S T). auto.
  - (* seq *) simpl. apply TCast_seq with (B := B0).
    + apply (IH1 P0 E cx S T eq_refl d Hlc Hd).
    + apply (IH2 P0 E cx S T eq_refl d Hlc Hd).
  - (* var *) destruct (eq_dec cy cx) as [e|ne].
    + (* hole *) subst cy.
      assert (Hpair : (A0,B0) = (S,T)).
      { apply (uniq_pair_eq (typ*typ) (P0 ++ cons (cx,(S,T)) E) cx (A0,B0) (S,T)); auto.
        apply in_or_app. right. simpl. left. auto. }
      inversion Hpair; subst A0 B0.
      rewrite castsubst_castop_same. exact Hd.
    + (* not hole *)
      rewrite castsubst_castop_diff by auto.
      apply TCast_var.
      * auto.
      * auto.
      * apply (uniq_mid_remove P0 E cx S T). auto.
      * apply (in_cctx_mid_remove P0 E cx S T cy A0 B0); auto.
  - (* fix *) simpl.
    apply (TCast_fix (L \u singleton cx \u dom (P0++E)) D (P0++E) A1 B1 A2 B2 (castsubst_castop d cx c1) (castsubst_castop d cx c2)).
    + intros cx' Hx'.
      assert (Hx'L : cx' \notin L) by (simpl in Hx'; fsetdec).
      assert (Hx'cx : cx' <> cx) by (simpl in Hx'; fsetdec).
      assert (Hx'dE : cx' \notin dom (P0++E)) by (simpl in Hx'; fsetdec).
      assert (Hdw : TypCast D (cons (cx',(t_arrow A1 B1, t_arrow A2 B2)) (P0++E)) S T d).
      { apply typcast_weaken; auto. }
      assert (HIH := IH1 cx' Hx'L (cons (cx',(t_arrow A1 B1, t_arrow A2 B2)) P0) E cx S T eq_refl d Hlc Hdw).
      change (TypCast D ((cx', (t_arrow A1 B1, t_arrow A2 B2)) :: P0 ++ E) A1 A2
                (castsubst_castop d cx (open_castop_wrt_castop_rec 0 (c_var_f cx') c1))) in HIH.
      rewrite (castsubst_castop_open_gen c1 d cx cx' 0 Hlc Hx'cx) in HIH.
      exact HIH.
    + intros cx' Hx'.
      assert (Hx'L : cx' \notin L) by (simpl in Hx'; fsetdec).
      assert (Hx'cx : cx' <> cx) by (simpl in Hx'; fsetdec).
      assert (Hx'dE : cx' \notin dom (P0++E)) by (simpl in Hx'; fsetdec).
      assert (Hdw : TypCast D (cons (cx',(t_arrow A1 B1, t_arrow A2 B2)) (P0++E)) S T d).
      { apply typcast_weaken; auto. }
      assert (HIH := IH2 cx' Hx'L (cons (cx',(t_arrow A1 B1, t_arrow A2 B2)) P0) E cx S T eq_refl d Hlc Hdw).
      change (TypCast D ((cx', (t_arrow A1 B1, t_arrow A2 B2)) :: P0 ++ E) B1 B2
                (castsubst_castop d cx (open_castop_wrt_castop_rec 0 (c_var_f cx') c2))) in HIH.
      rewrite (castsubst_castop_open_gen c2 d cx cx' 0 Hlc Hx'cx) in HIH.
      exact HIH.
Qed.
(* ============================================================ *)
(* Section 18: canonical forms and auxiliary lemmas            *)
(* ============================================================ *)

Lemma typcast_fix_inv : forall (D:tctx) (E:cctx) (A B:typ) (c:castop),
  TypCast D E A B (c_fixc c) ->
  exists (c1 c2:castop) (A1 B1 A2 B2:typ) (L:vars),
    c = c_arrow c1 c2 /\
    A = t_arrow A1 B1 /\ B = t_arrow A2 B2 /\
    (forall cx, cx \notin L ->
       TypCast D (cons (cx,(t_arrow A1 B1, t_arrow A2 B2)) E) A1 A2
         (open_castop_wrt_castop c1 (c_var_f cx))) /\
    (forall cx, cx \notin L ->
       TypCast D (cons (cx,(t_arrow A1 B1, t_arrow A2 B2)) E) B1 B2
         (open_castop_wrt_castop c2 (c_var_f cx))).
Proof.
  intros. inversion H; subst.
  exists c1, c2, A1, B1, A2, B2, L. auto.
Qed.

Lemma typcast_unfold_wft : forall (D:tctx) (E:cctx) (A B:typ) (T:typ),
  TypCast D E A B (c_unfold T) -> exists A0, T = t_mu A0 /\ WFT D (t_mu A0).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma typcast_fold_wft : forall (D:tctx) (E:cctx) (A B:typ) (T:typ),
  TypCast D E A B (c_fold T) -> exists A0, T = t_mu A0 /\ WFT D (t_mu A0).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma value_lc_exp : forall (e:exp), value e -> lc_exp e.
Proof.
  intros e H. induction H.
  - constructor.
  - auto.
  - apply lc_e_cast.
    + apply lc_c_fold. auto.
    + auto.
  - apply lc_e_cast.
    + apply lc_c_arrow; auto.
    + auto.
Qed.

Lemma typing_abs_lc : forall (G:ctx) (A:typ) (e0:exp) (T:typ),
  Typing G (e_abs A e0) T -> lc_typ A.
Proof.
  intros G A e0 T H. remember (e_abs A e0) as e eqn:E. revert A e0 E.
  induction H as [G i Hwf|G x A0 Hwf Hb|L G A1 e A2 Hprem IH|G e1 e2 A2 A1 H1 IH1 H2 IH2|G c e B A0 H IH TC|G e0 B0 A0 H IH AS];
  intros A' e0' E.
  - inversion E.
  - inversion E.
  - inversion E; subst. pick fresh x.
    assert (Hw : WFTmE ((x,A') :: G)).
    { exact (typing_wftmE ((x,A')::G) (open_exp_wrt_exp e0' (e_var_f x)) A2 (Hprem x Fr)). }
    apply (WFT_lc_typ nil).
    apply (proj2 (WFTmE_cons_inv G x A' Hw)).
  - inversion E.
  - inversion E.
  - inversion E; subst. apply (IH A' e0' eq_refl).
Qed.

Lemma canon_arrow : forall (A1 A2:typ) (e:exp),
  value e -> Typing nil e (t_arrow A1 A2) ->
  (exists A e0, e = e_abs A e0) \/ (exists c1 c2 e0, e = e_cast (c_arrow c1 c2) e0).
Proof.
  intros A1 A2 e Hv H.
  remember (t_arrow A1 A2) as T eqn:ET.
  revert Hv. revert A1 A2 ET.
  induction H as [G i Hwf|G x A Hwf Hb|L G A1' e0 A2' Hprem IH|G e1 e2 A2' A1' H1 IH1 H2 IH2|G c e0 B A H IH TC|G e0 B0 A H IH AS];
  intros A1 A2 ET Hv.
  - inversion Hv. discriminate ET.
  - inversion Hv.
  - inversion Hv; subst. left. exists A1', e0. auto.
  - inversion Hv.
  - inversion Hv; subst.
    + inversion TC; subst.
    + right. eauto.
  - rewrite ET in AS. inversion AS; subst.
    apply (IH _ _ eq_refl Hv).
Qed.

Lemma canon_mu : forall (A:typ) (e:exp),
  value e -> Typing nil e (t_mu A) ->
  exists B v, e = e_cast (c_fold B) v /\ value v.
Proof.
  intros A e Hv H.
  remember (t_mu A) as T eqn:ET.
  revert Hv. revert A ET.
  induction H as [G i Hwf|G x A0 Hwf Hb|L G A1 e0 A2 Hprem IH|G e1 e2 A2 A1 H1 IH1 H2 IH2|G c e0 B A0 H IH TC|G e0 B0 A0 H IH AS];
  intros A ET Hv.
  - inversion Hv. discriminate ET.
  - inversion Hv.
  - inversion Hv. discriminate ET.
  - inversion Hv.
  - inversion Hv; subst.
    + eexists _, _. split; auto.
    + inversion TC; subst.
  - rewrite ET in AS. inversion AS; subst.
    + apply (IH _ eq_refl Hv).
    + apply (IH _ eq_refl Hv).
Qed.
(* ============================================================ *)
(* Section 19: preservation                                    *)
(* ============================================================ *)

Lemma subst_exp_open_self : forall (e:exp) (u:exp) (x:termvar) (k:nat),
  x \notin termfv_exp e ->
  subst_exp u x (open_exp_wrt_exp_rec k (e_var_f x) e) =
  open_exp_wrt_exp_rec k u e.
Proof.
  intros e. induction e as [n|y|i|A e0 IH|e1 IH1 e2 IH2|c e IH];
  intros u x k Hx; simpl in *.
  - (* var_b *) destruct (lt_eq_lt_dec n k) as [[l|eq]|r]; simpl.
    + reflexivity.
    + subst. apply eq_dec_same.
    + reflexivity.
  - (* var_f *) destruct (eq_dec y x) as [e|ne].
    + subst. exfalso; auto.
    + reflexivity.
  - reflexivity.
  - (* abs *) simpl. rewrite (IH u x (S k)); auto.
  - (* app *) simpl. rewrite (IH1 u x k); auto. rewrite (IH2 u x k); auto.
  - (* cast *) simpl. rewrite (IH u x k); auto.
Qed.

Theorem preservation: forall e T,
  Typing nil e T -> forall e',
  Reduction e e' -> Typing nil e' T.
Proof.
  intros e T Hty e' Hred. revert T Hty.
  induction Hred as [A e0 e1 HlcA HlcAbs Hv
                   |e1 e2 e1' Hlc2 Hred1 IH1
                   |v1 e2 e2' Hv1 Hred2 IH2
                   |c1 c2 e1 e2 Hlc2 Hlc1 Hv1 Hv2
                   |c1 c2 e0 Hlc2 Hlc1 Hv
                   |c e0 e0' Hlc Hred0 IH0
                   |A B v HlcA HlcB Hv
                   |v Hv
                   |c e0 Hlc Hv];
  intros T Hty.
  - (* beta *) subst.
    destruct (typing_app_inv nil (e_abs A e0) e1 T Hty) as [A1 [A2 [H1 [H2 HS]]]].
    destruct (typing_abs_inv_arrow nil A e0 A1 A2 H1) as [A2' [L [Hbody [HS1 HS2]]]].
    assert (He1A : Typing nil e1 A).
    { apply (typing_ss nil e1 A1 A H2 HS1). }
    pick fresh x for (L \u termfv_exp e0).
    assert (HxL : x \notin L) by fsetdec.
    assert (HxE : x \notin termfv_exp e0) by fsetdec.
    assert (Hbx := Hbody x HxL).
    assert (Hsub := typing_subst (cons (x,A) nil) (open_exp_wrt_exp e0 (e_var_f x)) A2' Hbx
                     nil nil x A eq_refl e1 He1A (value_lc_exp e1 Hv) ltac:(fsetdec)).
    unfold open_exp_wrt_exp in Hsub.
    rewrite (subst_exp_open_self e0 e1 x 0 HxE) in Hsub.
    apply (typing_ss nil (open_exp_wrt_exp e0 e1) A2' T Hsub).
    apply ss_trans with (B := A2); auto.
  - (* appl *) destruct (typing_app_inv nil e1 e2 T Hty) as [A1 [A2 [H1 [H2 HS]]]].
    assert (H1' : Typing nil e1' (t_arrow A1 A2)) by (apply (IH1 (t_arrow A1 A2)); auto).
    apply (typing_ss nil (e_app e1' e2) A2 T).
    + apply Typing_app with (A1 := A1); auto.
    + auto.
  - (* appr *) destruct (typing_app_inv nil v1 e2 T Hty) as [A1 [A2 [H1 [H2 HS]]]].
    assert (H2' : Typing nil e2' A1) by (apply (IH2 A1); auto).
    apply (typing_ss nil (e_app v1 e2') A2 T).
    + apply Typing_app with (A1 := A1); auto.
    + auto.
  - (* cast_arr *) destruct (typing_app_inv nil (e_cast (c_arrow c1 c2) e1) e2 T Hty)
      as [A1 [A2 [H1 [H2 HS]]]].
    destruct (typing_cast_inv nil (c_arrow c1 c2) e1 (t_arrow A1 A2) H1)
      as [A0 [B0 [He1 [TC HS']]]].
    destruct (typcast_arrow_inv nil nil A0 B0 c1 c2 TC)
      as [A1' [A2' [B1' [B2' [HA [HB [TC1 TC2]]]]]]].
    subst A0. subst B0.
    destruct (ss_arrow_inv nil B1' B2' A1 A2 HS') as [HS1 HS2].
    assert (He2 : Typing nil e2 B1') by (apply (typing_ss nil e2 A1 B1'); auto).
    assert (HTC1 : TypCast nil nil B1' A1' (rev_cast c1)) by (exact (typcast_rev nil nil A1' B1' c1 TC1)).
    assert (Hc1 : Typing nil (e_cast (rev_cast c1) e2) A1').
    { apply Typing_cast with (A := B1'); auto. }
    assert (Hc2 : Typing nil (e_cast c2 (e_app e1 (e_cast (rev_cast c1) e2))) B2').
    { apply Typing_cast with (A := A2').
      - apply Typing_app with (A1 := A1'); auto.
      - auto. }
    apply (typing_ss nil (e_cast c2 (e_app e1 (e_cast (rev_cast c1) e2))) B2' T Hc2).
    apply ss_trans with (B := A2); auto.
  - (* cast_seq *) destruct (typing_cast_inv nil (c_seq c1 c2) e0 T Hty) as [A0 [B0 [He [TC HS]]]].
    destruct (typcast_seq_inv nil nil A0 B0 c1 c2 TC) as [C [TC1 TC2]].
    assert (H1 : Typing nil (e_cast c1 e0) C) by (apply Typing_cast with (A := A0); auto).
    assert (H2 : Typing nil (e_cast c2 (e_cast c1 e0)) B0) by (apply Typing_cast with (A := C); auto).
    apply (typing_ss nil (e_cast c2 (e_cast c1 e0)) B0 T H2); auto.
  - (* cast congruence *) destruct (typing_cast_inv nil c e0 T Hty) as [A0 [B0 [He [TC HS]]]].
    assert (He' : Typing nil e0' A0) by (apply (IH0 A0); auto).
    assert (H2 : Typing nil (e_cast c e0') B0) by (apply Typing_cast with (A := A0); auto).
    apply (typing_ss nil (e_cast c e0') B0 T H2); auto.
  - (* castelim *) 
    destruct (typing_cast_inv nil (c_unfold A) (e_cast (c_fold B) v) T Hty)
      as [A1 [B1 [Hinner [TCout HSout]]]].
    destruct (typcast_unfold_inv nil nil A1 B1 A TCout) as [A0 [HT [HA1 HB1]]].
    subst A. subst A1. subst B1.
    destruct (typing_cast_inv nil (c_fold B) v (t_mu A0) Hinner)
      as [A2 [B2 [Hvty [TCin HSin]]]].
    destruct (typcast_fold_inv nil nil A2 B2 B TCin) as [B0 [HB [HA2 HB2]]].
    subst B. subst A2. subst B2.
    assert (HSunf : sub_star nil (open_typ_wrt_typ B0 (t_mu B0)) (open_typ_wrt_typ A0 (t_mu A0))).
    { apply (ss_mu_unfold_gen (t_mu B0) (t_mu A0) HSin B0 eq_refl A0 eq_refl). }
    apply (typing_ss nil v (open_typ_wrt_typ B0 (t_mu B0)) T Hvty).
    apply ss_trans with (B := open_typ_wrt_typ A0 (t_mu A0)); auto.
  - (* castid *) destruct (typing_cast_inv nil c_id v T Hty) as [A0 [B0 [Hvty [TC HS]]]].
    assert (Heq : A0 = B0) by (apply typcast_id_inv in TC; auto).
    subst B0.
    apply (typing_ss nil v A0 T Hvty); auto.
  - (* castfix *) destruct (typing_cast_inv nil (c_fixc c) e0 T Hty) as [A1 [B1 [He [TC HS]]]].
    destruct (typcast_fix_inv nil nil A1 B1 c TC)
      as [c1 [c2 [A1' [B1' [A2' [B2' [L [Hc [HA [HB [Hp1 Hp2]]]]]]]]]]].
    subst c. subst A1. subst B1.
    pick fresh cx for (L \u castfv_castop c1 \u castfv_castop c2).
    assert (HxL : cx \notin L) by fsetdec.
    assert (Hx1 : cx \notin castfv_castop c1) by fsetdec.
    assert (Hx2 : cx \notin castfv_castop c2) by fsetdec.
    assert (Hd1 : TypCast nil nil A1' A2' (open_castop_wrt_castop c1 (c_fixc (c_arrow c1 c2)))).
    { assert (Ht := typcast_subst_mid nil nil nil cx (t_arrow A1' B1') (t_arrow A2' B2')
                     A1' A2' (open_castop_wrt_castop c1 (c_var_f cx))
                     (Hp1 cx HxL) (c_fixc (c_arrow c1 c2)) Hlc TC).
      change (TypCast nil nil A1' A2'
                (castsubst_castop (c_fixc (c_arrow c1 c2)) cx
                   (open_castop_wrt_castop_rec 0 (c_var_f cx) c1))) in Ht.
      rewrite (castsubst_castop_open c1 (c_fixc (c_arrow c1 c2)) cx 0 Hlc Hx1) in Ht.
      exact Ht. }
    assert (Hd2 : TypCast nil nil B1' B2' (open_castop_wrt_castop c2 (c_fixc (c_arrow c1 c2)))).
    { assert (Ht := typcast_subst_mid nil nil nil cx (t_arrow A1' B1') (t_arrow A2' B2')
                     B1' B2' (open_castop_wrt_castop c2 (c_var_f cx))
                     (Hp2 cx HxL) (c_fixc (c_arrow c1 c2)) Hlc TC).
      change (TypCast nil nil B1' B2'
                (castsubst_castop (c_fixc (c_arrow c1 c2)) cx
                   (open_castop_wrt_castop_rec 0 (c_var_f cx) c2))) in Ht.
      rewrite (castsubst_castop_open c2 (c_fixc (c_arrow c1 c2)) cx 0 Hlc Hx2) in Ht.
      exact Ht. }
    assert (HTC : TypCast nil nil (t_arrow A1' B1') (t_arrow A2' B2')
                    (open_castop_wrt_castop (c_arrow c1 c2) (c_fixc (c_arrow c1 c2)))).
    { simpl. apply TCast_arrow; auto. }
    assert (He' : Typing nil (e_cast (open_castop_wrt_castop (c_arrow c1 c2) (c_fixc (c_arrow c1 c2))) e0)
                        (t_arrow A2' B2')).
    { apply Typing_cast with (A := t_arrow A1' B1'); auto. }
    apply (typing_ss nil (e_cast (open_castop_wrt_castop (c_arrow c1 c2) (c_fixc (c_arrow c1 c2))) e0)
                      (t_arrow A2' B2') T He').
    auto.
Qed.
(* ============================================================ *)
(* Section 20: progress                                        *)
(* ============================================================ *)

Lemma progress_gen : forall (G:ctx) (e:exp) (T:typ),
  Typing G e T -> G = nil -> value e \/ exists e', Reduction e e'.
Proof.
  intros G e T H.
  induction H as [G i Hwf|G x A Hwf Hb|L G A1 e A2 Hprem IH|G e1 e2 A2 A1 H1 IH1 H2 IH2|G c e0 B A H IH TC|G e B0 A H IH AS];
  intros HG.
  - (* int *) left. apply V_lit.
  - (* var *) subst G. unfold binds in Hb. destruct Hb.
  - (* abs *)
    assert (Htyabs : Typing G (e_abs A1 e) (t_arrow A1 A2)) by (apply Typing_abs with (L := L); auto).
    assert (Hlc : lc_exp (e_abs A1 e)) by (apply (typing_lc_exp G (e_abs A1 e) (t_arrow A1 A2)); auto).
    left. apply V_abs.
    + apply (typing_abs_lc G A1 e (t_arrow A1 A2)); auto.
    + auto.
  - (* app *)
    rewrite HG in H1, H2.
    destruct (IH1 HG) as [Hv1|Hred1].
    + destruct (canon_arrow A1 A2 e1 Hv1 H1) as [Habs|Hcast].
      * destruct Habs as [A0 [e0 Heq]]. subst e1.
        destruct (IH2 HG) as [Hv2|Hred2].
        -- right. exists (open_exp_wrt_exp e0 e2). apply Red_beta.
           ++ apply (typing_abs_lc nil A0 e0 (t_arrow A1 A2)); auto.
           ++ apply (typing_lc_exp nil (e_abs A0 e0) (t_arrow A1 A2)); auto.
           ++ auto.
        -- destruct Hred2 as [e2' Hred2'].
           right. exists (e_app (e_abs A0 e0) e2'). apply Red_appr; auto.
      * destruct Hcast as [c1 [c2 [e0 Heq]]]. subst e1.
        destruct (IH2 HG) as [Hv2|Hred2].
        -- right. exists (e_cast c2 (e_app e0 (e_cast (rev_cast c1) e2))).
           inversion Hv1; subst. apply Red_cast_arr; auto.
        -- destruct Hred2 as [e2' Hred2'].
           right. exists (e_app (e_cast (c_arrow c1 c2) e0) e2'). apply Red_appr; auto.
    + destruct Hred1 as [e1' Hred1'].
      right. exists (e_app e1' e2). apply Red_appl.
      * apply (typing_lc_exp nil e2 A1); auto.
      * auto.
  - (* cast *)
    rewrite HG in H.
    destruct (IH HG) as [Hv0|Hred0].
    + destruct c as [n0|x0| |T0|T0|c1 c2|c1 c2|c].
      * (* c_var_b *) inversion TC.
      * (* c_var_f *) inversion TC; subst.
        match goal with H : In _ nil |- _ => destruct H end.
      * (* c_id *) right. exists e0. apply Red_castid; auto.
      * (* c_unfold T *)
        destruct (typcast_unfold_wft nil nil A B T0 TC) as [C [HC HWF]].
        destruct (typcast_unfold_inv nil nil A B T0 TC) as [A0 [HT [HA HB]]].
        subst T0. injection HT as HC0. subst C. subst A. subst B.
        destruct (canon_mu A0 e0 Hv0 H) as [B0 [v [Heq Hval]]].
        rewrite Heq in H.
        destruct (typing_cast_inv nil (c_fold B0) v (t_mu A0) H) as [A2 [B2 [Hvty [TCin HSin]]]].
        destruct (typcast_fold_wft nil nil A2 B2 B0 TCin) as [D [HD HWFold]].
        right. exists v. rewrite Heq. apply Red_castelim.
        -- apply (WFT_lc_typ nil (t_mu A0)); auto.
        -- rewrite HD. apply (WFT_lc_typ nil (t_mu D)); auto.
        -- exact Hval.
      * (* c_fold T *)
        destruct (typcast_fold_wft nil nil A B T0 TC) as [A0 [HT HWF]].
        subst T0. left. apply V_fold.
        -- apply (WFT_lc_typ nil (t_mu A0)); auto.
        -- auto.
      * (* c_arrow c1 c2 *)
        destruct (typcast_arrow_inv nil nil A B c1 c2 TC) as [A1' [A2' [B1' [B2' [HA [HB [TC1 TC2]]]]]]].
        left. apply V_arrow.
        -- apply (typcast_lc_castop nil nil A1' B1' c1 TC1).
        -- apply (typcast_lc_castop nil nil A2' B2' c2 TC2).
        -- auto.
      * (* c_seq c1 c2 *)
        destruct (typcast_seq_inv nil nil A B c1 c2 TC) as [C [TC1 TC2]].
        right. exists (e_cast c2 (e_cast c1 e0)). apply Red_cast_seq.
        -- apply (typcast_lc_castop nil nil C B c2 TC2).
        -- apply (typcast_lc_castop nil nil A C c1 TC1).
        -- auto.
      * (* c_fixc c *)
        right. exists (e_cast (open_castop_wrt_castop c (c_fixc c)) e0). apply Red_castfix.
        -- apply (typcast_lc_castop nil nil A B (c_fixc c) TC).
        -- auto.
    + destruct Hred0 as [e0' Hred0'].
      right. exists (e_cast c e0'). apply Red_cast.
      * apply (typcast_lc_castop nil nil A B c TC).
      * auto.
  - (* sub *) destruct (IH HG) as [Hv|Hred]; [left; auto|right; auto].
Qed.

Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Export LibTactics.

Require Export subtyping.

Theorem progress: forall e t, Typing nil e t -> (value e) \/ exists e', Reduction e e'.
Proof.
  intros e t H. exact (progress_gen nil e t H eq_refl).
Qed.
