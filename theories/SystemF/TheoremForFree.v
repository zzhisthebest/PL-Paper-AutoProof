(** A theorem for free derived from System F parametricity. *)

From Stdlib Require Import Lists.List.
From AutoProof Require Import Smallstep.
From AutoProof.SystemF Require Import Syntax.
From AutoProof.SystemF Require Import Infrastructure.
From AutoProof.SystemF Require Import Typing.
From AutoProof.SystemF Require Import LogicalRelation.
From AutoProof.SystemF Require Import Parametricity.

Module SystemFTheoremForFree.
Import ListNotations.
Import SystemF.
Import SystemFInfrastructure.
Import SystemFTyping.
Import SystemFLogicalRelation.
Import SystemFParametricity.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Definition singleton_relation (v : tm) : relation :=
  fun v1 v2 => v1 = v /\ v2 = v.

(*
对于任意在空环境下类型为 forall X, X -> X 的程序 t，
对任意没有自由类型变量、也没有悬空绑定类型变量的类型 U，
以及任意在空环境下类型为 U 的值 v，程序 t[U] v 经过若干步求值后，
结果必然是原来的 v。
*)
(* 
自然语言证明：
定义关系 R：
  R(v1, v2) 当且仅当 v1 = v 且 v2 = v
  也就是说，R 只认为 v 和 v 相关。因为 v 是类型为 U 的值，
  所以 R 是类型 U 与 U 之间合法的候选关系。

  根据参数性定理，把 t 左右两边的类型变量 X 都实例化为 U，并用 R 解释 X，可知：
  t[U] 和 t[U] 在 U -> U 下相关
  函数相关的含义是：输入一对相关的参数，求值结果也必须相关。由于 R(v,v) 成立，因此分别把 v 传给两个 t[U] 后，求值结果 v1、v2 必须满足：
  R(v1, v2)

  而根据 R 的定义，这只能意味着：
  v1 = v
  v2 = v
  已知t[U] v -->* v1和t[U] v -->* v2
  因此：
  t[U] v -->* v
*)
Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros.
  (* 引入关系R *)
  pose (R:= singleton_relation v).
  assert (relation_candidate U U R).
  {
    unfold relation_candidate.
    split. assumption.
    split. assumption.
    intros.
    unfold R in H3.
    unfold singleton_relation in H3.
    destruct H3.
    subst.
    split.
    assumption.
    split.
    assumption.
    split.
    assumption.
    assumption.
  }
  (* 引入relation_assignment *)
  pose (a := ({|
    assignment_left := U;
    assignment_right := U;
    assignment_relation := R;
    assignment_is_candidate := H3
  |})).
  assert (
    expression_relation [a] empty_relation_env
    (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))
    (tm_tapp t U)
    (tm_tapp t U)
  ).
  {
    (* 使用参数定理 *)
    apply parametricity_tapp.
    assumption.
  }
  assert (Happ_related :
  expression_relation [a] empty_relation_env (Ty_BVar 0)
    (tm_app (tm_tapp t U) v)
    (tm_app (tm_tapp t U) v)).
  {
    apply (expression_relation_app
    [a] empty_relation_env
    (Ty_BVar 0) (Ty_BVar 0)).
    - exact H4.
    - apply expression_relation_of_values.
      unfold value_relation.
      split. assumption.
      split. assumption.
      split.
      + 
        (*  left_type [a] empty_relation_env (Ty_BVar 0)=U *)
        change (has_type [] empty v U).
        assumption.
      + split.
        * change (has_type [] empty v U).
          assumption.
        * simpl.
          (* 显然成立 *)
          split.
          reflexivity.
          reflexivity.
  }
  clear H4.
  unfold expression_relation in Happ_related.
  unfold expression_lifting in Happ_related.
  destruct Happ_related as
    [Htype1 [Htype2 [v1 [v2 [Hsteps1 [Hsteps2 Hrel]]]]]].
  assert (R v1 v2).
  {
    unfold value_relation in Hrel.
    destruct Hrel as
    [Hvalue1 [Hvalue2 [Htyped1 [Htyped2 HR]]]].
    simpl in HR.
    exact HR.
  }
  unfold R, singleton_relation in H4.
  destruct H4. subst.
  assumption.

Qed.

Print relation_candidate.
End SystemFTheoremForFree.
