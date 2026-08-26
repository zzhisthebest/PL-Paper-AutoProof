Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From AutoProof.STLC Require Import Syntax.

Import ListNotations.

Module STLCProp.
Import STLC.

(* 如果 t 在 k 层 lambda 下合法，那么在更多层 lambda 下也合法。
显然。 *)
Lemma lc_at_weaken : forall k j t,
  lc_at k t ->
  k <= j ->
  lc_at j t.
Proof.
  intros k j t H.
  generalize dependent j.
  induction H; intros j Hle; eauto using lc_at.
  - apply lc_bvar. lia.
  - apply lc_abs. apply IHlc_at. lia.
Qed.

(* 完整程序在任意 lambda 深度下都仍然局部闭合。
显然 *)
Lemma term_lc_at : forall k t,
  locally_closed t ->
  lc_at k t.
Proof.
  unfold locally_closed. intros. eapply lc_at_weaken; eauto. lia.
Qed.

Print value.

(* value 一定是合法完整程序。 *)
Lemma value_regular : forall v,
  value v -> locally_closed v.
Proof.
  intros v Hv. inversion Hv; subst.
  - assumption.
  - unfold locally_closed. apply lc_true.
  - unfold locally_closed. apply lc_false.
Qed.

Print lc_at.

(* 打开一个函数体时，如果参数本身是完整程序，结果仍然局部闭合。 *)
Lemma open_rec_preserves_lc_at : forall t k u,
  lc_at (S k) t ->
  locally_closed u ->
  (* bvar k已经被替换了，所以结论从S k 加强为了k *)
  lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Hlc Hu; simpl in *; inversion Hlc; subst; eauto using lc_at.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply term_lc_at. exact Hu.
    + apply Nat.eqb_neq in Heq. apply lc_bvar. lia.
Qed.

(* 上一个定理的简单推论 *)
Lemma open_preserves_term : forall t u,
  lc_at 1 t ->
  locally_closed u ->
  locally_closed (open t u).
Proof.
  unfold open, locally_closed. intros.
  apply open_rec_preserves_lc_at; assumption.
Qed.

(* 反过来：如果打开后合法，那么原函数体在 lambda 内部合法。 
倒也显然。*)
Lemma lc_at_open_inv : forall t k u,
  lc_at k (open_rec k u t) ->
  lc_at (S k) t.
Proof.
  induction t; intros k u Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. apply lc_bvar. lia.
    + inversion Hlc; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - inversion Hlc; subst. eauto using lc_at.
  - inversion Hlc; subst. apply lc_abs. apply (IHt (S k) u). assumption.
  - apply lc_true.
  - apply lc_false.
  - inversion Hlc; subst. eauto using lc_at.
Qed.

(* 类型正确的程序一定是合法完整程序。 *)
Lemma typing_regular : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  locally_closed t.
Proof.
  intros Gamma t T Ht.
  induction Ht.
  - unfold locally_closed. apply lc_fvar.
  - unfold locally_closed. apply lc_abs.
    pose (x := fresh L).
    assert (Hfresh : ~ In x L) by (unfold x; apply fresh_notin).
    specialize (H0 x Hfresh).
    apply lc_at_open_inv with (u := tm_fvar x).
    exact H0.
  - unfold locally_closed. apply lc_app; assumption.
  - unfold locally_closed. apply lc_true.
  - unfold locally_closed. apply lc_false.
  - unfold locally_closed. apply lc_if; assumption.
Qed.

(* \/ 是 Rocq 中的“或”。 *)
Lemma canonical_forms_bool : forall t,
  <{ empty |-- t \in Bool }> ->
  value t ->
  t = <{ true }> \/ t = <{ false }>.
Proof.
  intros t HT HVal.
  inversion HVal; subst.
  - inversion HT.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* 函数类型的 value 只能是 lambda。 *)
Lemma canonical_forms_fun : forall t T1 T2,
  <{ empty |-- t \in T1 -> T2 }> ->
  value t ->
  exists body, t = <{ lambda : T1, $(body) }>.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; subst; inversion HT; subst; eauto.
Qed.

Theorem progress : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.

(**
  progress 的意思：
  如果一个闭合程序 t 类型正确，那么 t 要么已经是 value，
  要么还能往前归约一步。

  证明按 typing derivation 归纳，不是按 tm 结构归纳。
*)
Proof.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma.
  (* T_Var：空环境里不可能查到自由变量类型。 *)
  - discriminate H.
  (* T_Abs：lambda 本身就是 value。 *)
  - left. apply v_abs. unfold locally_closed. apply lc_abs.
    pose (x := fresh L).
    assert (Hfresh : ~ In x L) by (unfold x; apply fresh_notin).
    specialize (H x Hfresh).
    apply lc_at_open_inv with (u := tm_fvar x). apply typing_regular in H. exact H.
  (* T_App：先看函数部分能不能动，再看参数部分能不能动。 *)
  - right.
    destruct (IHHt1 eq_refl) as [Hv1 | [t1' Hs1]].
    + destruct (IHHt2 eq_refl) as [Hv2 | [t2' Hs2]].
      * destruct (canonical_forms_fun t1 T1 T2 Ht1 Hv1) as [body Heq].
        subst t1.
        exists (open body t2).
        apply ST_AppAbs.
        -- apply value_regular. exact Hv1.
        -- exact Hv2.
      * exists (tm_app t1 t2').
        apply ST_App2; assumption.
    + exists (tm_app t1' t2).
      apply ST_App1.
      * exact Hs1.
      * apply typing_regular in Ht2. exact Ht2.
  - left. apply v_true.
  - left. apply v_false.
  (* T_If：先看条件能不能动；条件算成 true/false 后选择分支。 *)
  - right.
    destruct (IHHt1 eq_refl) as [Hv1 | [t1' Hs1]].
    + destruct (canonical_forms_bool t1 Ht1 Hv1) as [Heq | Heq]; subst t1.
      * exists t2. apply ST_IfTrue; apply typing_regular in Ht2 + apply typing_regular in Ht3; assumption.
      * exists t3. apply ST_IfFalse; apply typing_regular in Ht2 + apply typing_regular in Ht3; assumption.
    + exists (tm_if t1' t2 t3).
      apply ST_If.
      * exact Hs1.
      * apply typing_regular in Ht2. exact Ht2.
      * apply typing_regular in Ht3. exact Ht3.
Qed.

End STLCProp.
