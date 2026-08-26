Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From AutoProof Require Import Maps.
From AutoProof Require Import Smallstep.
From AutoProof.STLC Require Import Syntax.

Set Default Goal Selector "!".

Module STLCProp.
Import STLC.

(*\/ 是 Rocq 中的“或”*)
Lemma canonical_forms_bool : forall t,
  <{ empty |-- t \in Bool }> ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; auto.
  inversion HT.
  

Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  <{ empty |-- t \in T1 -> T2 }> ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal.
  - inversion HT.
    exists x0, t1.
    auto.
  - inversion HT.
  - inversion HT.

Qed.



Theorem progress : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.

(** _Proof_: By induction on the derivation of [|-- t \in T].

    - The last rule of the derivation cannot be [T_Var], since a
      variable is never well typed in an empty context.

    - The [T_True], [T_False], and [T_Abs] cases are trivial, since in
      each of these cases we can see by inspecting the rule that [t]
      is a value.

    - If the last rule of the derivation is [T_App], then [t] has the
      form [t1 t2] for some [t1] and [t2], where [|-- t1 \in T2 -> T]
      and [|-- t2 \in T2] for some type [T2].  The induction hypothesis
      for the first subderivation says that either [t1] is a value or
      else it can take a reduction step.

        - If [t1] is a value, then consider [t2], which by the
          induction hypothesis for the second subderivation must also
          either be a value or take a step.

            - Suppose [t2] is a value.  Since [t1] is a value with an
              arrow type, it must be a lambda abstraction; hence [t1
              t2] can take a step by [ST_AppAbs].

            - Otherwise, [t2] can take a step, and hence so can [t1
              t2] by [ST_App2].

        - If [t1] can take a step, then so can [t1 t2] by [ST_App1].

    - If the last rule of the derivation is [T_If], then [t = if
      t1 then t2 else t3], where [t1] has type [Bool].  The first IH
      says that [t1] either is a value or takes a step.

        - If [t1] is a value, then since it has type [Bool] it must be
          either [true] or [false].  If it is [true], then [t] steps to
          [t2]; otherwise it steps to [t3].

        - Otherwise, [t1] takes a step, and therefore so does [t] (by
          [ST_If]). *)
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma. 
  - discriminate H.
  - left.
    apply v_abs.
  - right.
    destruct (IHHt1 eq_refl) as [HVal1 | [t1' HStep1]].
    + destruct (IHHt2 eq_refl) as [HVal2 | [t2' HStep2]].
      * destruct (canonical_forms_fun t1 T2 T1 Ht1 HVal1)
          as [x [u Heq]].
        subst t1.
        exists <{ [x:=t2] u }>.
        apply ST_AppAbs.
        exact HVal2.
      * exists <{ t1 t2' }>.
        apply ST_App2.
        -- exact HVal1.
        -- exact HStep2.
    + exists <{ t1' t2 }>.
      apply ST_App1.
      exact HStep1.
  - left.
    apply v_true.
  - left.
    apply v_false.
  - right.
    destruct (IHHt1 eq_refl) as [HVal1 | [t1' HStep1]].
    + destruct (canonical_forms_bool t1 Ht1 HVal1) as [Heq | Heq].
      * subst t1.
        exists t2.
        apply ST_IfTrue.
      * subst t1.
        exists t3.
        apply ST_IfFalse.
    + exists <{ if t1' then t2 else t3 }>.
      apply ST_If.
      exact HStep1.
  (* remember empty as Gamma. *)
  (* induction Ht; subst Gamma; auto. *)
  (* auto solves all three cases in which t is a value *)
  (* - T_Var
    (* contradictory: variables cannot be typed in an
       empty context *)
    discriminate H.

  - (* T_App *)
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        eapply canonical_forms_fun in Ht1; [|assumption].
        destruct Ht1 as [x [t0 H1]]. subst.
        exists (<{ [x:=t2]t0 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists (<{t1 t2'}>)...

    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists (<{t1' t2}>)...

  - (* T_If *)
    right. destruct IHHt1...

    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.

    + (* t1 also steps *)
      destruct H as [t1' Hstp]. exists <{if t1' then t2 else t3}>... *)
Qed.

(** ** The Weakening Lemma *)

(** First, we show that typing is preserved under "extensions" to the
    context [Gamma].  (Recall the definition of "includedin" from
    Maps.v.) *)

Lemma weakening : forall Gamma Gamma' t T,
    includedin Gamma Gamma' ->
    <{ Gamma  |-- t \in T }>  ->
    <{ Gamma' |-- t \in T }>.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht.
  (* 自然数归纳法是1个基础1个递归情况，而这里是3个基础情况，3个递归情况！ *)
  - intros Gamma' Hinc.
    assert (H1 : Gamma' x0 = Some T1).
    {
      unfold includedin in Hinc.
      auto.
    }
    apply T_Var.
    exact H1.
  - intros Gamma' Hinc.
    (* 全程证明不需要Ht *)
    clear Ht. 
    apply T_Abs.
    apply IHHt.
    (* 接下来只需要Hinc *)
    apply includedin_update.
    exact Hinc.
  - intros Gamma' Hinc.
    apply T_App with (T2 := T2).
    + apply IHHt1.
      exact Hinc.
    + apply IHHt2.
      exact Hinc.

  - intros Gamma' Hinc.
    (* 显然成立 *)
    apply T_True.
  - intros Gamma' Hinc.
    (* 显然成立 *)
    apply T_False.
  - intros Gamma' Hinc.
    apply T_If.
    + apply IHHt1.
      exact Hinc.
    + apply IHHt2.
      exact Hinc.
    + apply IHHt3.
      exact Hinc.
Qed.

(** The following simple corollary is what we actually need below. *)

Lemma weakening_empty : forall Gamma t T,
    <{ empty |-- t \in T }> ->
    <{ Gamma |-- t \in T }>.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ empty |-- v \in U }>  ->
  <{ Gamma |-- [x:=v]t \in T }>.
Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t.
  - intros T Gamma H.
    simpl.
    destruct (eqb_spec x s) as [Heq | Hneq].
    + subst s.
      inversion H; subst.
      rewrite update_eq in H2.
      injection H2 as HUT.
      subst T.
      apply weakening_empty.
      exact Hv.
    + inversion H; subst.
      rewrite update_neq in H2 by exact Hneq.
      apply T_Var.
      exact H2.
    
  - intros T Gamma H.
    simpl.
    inversion H; subst.
    apply T_App with (T2 := T2).
    + apply IHt1.
      exact H3.
    + apply IHt2.
      exact H5.
  - intros T Gamma H.
    inversion H;subst.
    simpl.
    destruct (eqb_spec x s) as [Heq | Hneq].
    + apply T_Abs.
      subst.
      rewrite update_shadow in H5.
      exact H5.
    + apply T_Abs.
      apply IHt.
      rewrite update_permute in H5 by exact Hneq.
      exact H5.
  - intros T Gamma H.
    inversion H; subst.
    simpl.
    apply T_True.
  - intros T Gamma H.
    inversion H; subst.
    simpl.
    apply T_False.  
  - intros T Gamma H.
    inversion H; subst.
    simpl.
    apply T_If.
    + apply IHt1.
      exact H4.
    + apply IHt2.
      exact H6.
    + apply IHt3.
      exact H7.
    


  (* induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto. *)
Qed.

(* 当前定义下，preservation 不能直接推广到任意 Gamma：subst 没有通过
   alpha-renaming 避免变量捕获，因此被代入项中的自由变量可能被捕获。

   反例：令 Gamma 中 y : Bool，并令
     v = lambda z : Bool, y
   所以 v 的类型是 Bool -> Bool。考虑
     (lambda x : (Bool -> Bool),
        (lambda y : (Bool -> Bool), x)) v
   归约前，整个程序的类型是
     (Bool -> Bool) -> (Bool -> Bool)。
   当前 subst 归约后得到
     lambda y : (Bool -> Bool),
       (lambda z : Bool, y)
   其类型是
     (Bool -> Bool) -> (Bool -> (Bool -> Bool))。
   前后类型不同；这里原本自由的 y 被同名的 lambda 参数捕获了。
   empty 版本要求被代入项是闭项，因此不会发生这种变量捕获。 *)
Theorem preservation : forall t t' T,
  <{ empty |-- t \in T }> ->
  t --> t'  ->
  <{ empty |-- t' \in T }>.
Proof with eauto.
  intros t t' T HT.
  generalize dependent t'.
  remember empty as Gamma.
  induction HT.
  - intros t H1.
    subst.
    discriminate H.
  - intros t H1.
    subst.
    inversion H1.
  - intros t H1.
    subst.
    inversion H1;subst.
    + apply substitution_preserves_typing with (U := T2).
      * inversion HT1.
        subst.
        exact H2.
      * exact HT2.
    + apply T_App with (T2:=T2).
      * apply IHHT1.
        -- reflexivity.
        -- assumption.
      * exact HT2.
    + apply T_App with (T2:=T2).
      * exact HT1.
      * apply IHHT2.
        -- reflexivity.
        -- assumption.

  - intros t H1.
    subst.
    (* H1不成立，因为<{true}>无法再归约 *)
    inversion H1.
  - intros t H1.
    subst.
    (* H1不成立，因为<{false}>无法再归约 *)
    inversion H1.
  - intros t H1.
    subst.
    (* inversion H1属于增加条件，把H1对应构造器的条件显示出来了。
    之前所有inversion都是这个目的 *)
    inversion H1.
    + subst.
      exact HT2.
    + subst.
      exact HT3.
    + subst.
      apply T_If.
      * apply IHHT1.
        -- reflexivity.
        -- exact H4.
      * apply HT2.
      * apply HT3.
Qed.

End STLCProp.
