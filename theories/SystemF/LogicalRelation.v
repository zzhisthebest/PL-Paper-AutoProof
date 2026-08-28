(** Binary logical relations and relational parametricity for System F. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From AutoProof Require Import Smallstep.
From AutoProof.SystemF Require Import Syntax.
From AutoProof.SystemF Require Import Infrastructure.
From AutoProof.SystemF Require Import Typing.

Module SystemFLogicalRelation.
Import ListNotations.
Import SystemF.
Import SystemFInfrastructure.
Import SystemFTyping.

Definition relation := tm -> tm -> Prop.

(* 关系 R 是否可以作为类型 T1 和类型 T2 之间的一个“合格候选关系”。
   这里还要求 R 关联的两个值分别具有类型 T1 和 T2。 *)
Definition relation_candidate (T1 T2 : ty) (R : relation) : Prop :=
  wf_ty [] T1 /\
  wf_ty [] T2 /\
  forall v1 v2,
    R v1 v2 ->
    value v1 /\ value v2 /\
    has_type [] empty v1 T1 /\ has_type [] empty v2 T2.

(* Record 用来定义一种“包含多个字段的数据类型”，类似 Lean 的 structure。 *)
Record relation_assignment := {
  assignment_left : ty;
  assignment_right : ty;
  assignment_relation : relation;
  assignment_is_candidate :
    relation_candidate assignment_left assignment_right assignment_relation
}.

(* 一个 assignment 同时保存 T1、T2、关系 R，以及 R 是合格候选关系的证明。 *)
Definition relation_env := atom -> option relation_assignment.

(* 在 rho 中把 X 映射为 assignment a。 *)
Definition relation_update
    (rho : relation_env) (X : atom) (a : relation_assignment) : relation_env :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

(* 按照 eta 和 rho 给出的解释，把类型 T 翻译成“左边的具体类型。
k 记录当前类型内部的 binder 深度，防止把当前 forall 自己绑定的变量误当成 eta 中的外层变量。 *)
(* 例子：
设 eta = [a] 且 a.(assignment_left) = U。类型
Ty_All (Ty_Arrow (Ty_BVar 1) (Ty_BVar 0)) 表示 forall X, A -> X，
其中 Ty_BVar 0 是当前 forall 绑定的 X，Ty_BVar 1 是来自外层 eta 的 A。
计算 left_type_rec 0 [a] rho T 时，遇到 Ty_All 后 k 从 0 变为 1；
对 Ty_BVar 1，因为 1 < 1 不成立，所以查询 eta[1-1] = eta[0]，得到 U；
对 Ty_BVar 0，因为 0 < 1 成立，所以它属于当前 forall，保持不变。
最终得到 Ty_All (Ty_Arrow U (Ty_BVar 0))，即 forall X, U -> X。
*)
Fixpoint left_type_rec
    (k : nat) (eta : list relation_assignment) (rho : relation_env)
    (T : ty) : ty :=
  match T with
  | Ty_BVar i =>
      if i <? k then Ty_BVar i
      else
        match nth_error eta (i - k) with
        | Some a => a.(assignment_left)
        | None => Ty_BVar i
        end
  | Ty_FVar X =>
      match rho X with
      | Some a => a.(assignment_left)
      | None => Ty_FVar X
      end
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (left_type_rec k eta rho T1)
        (left_type_rec k eta rho T2)
  | Ty_All body => Ty_All (left_type_rec (S k) eta rho body)
  end.

(* 和上一个对称 *)
Fixpoint right_type_rec
    (k : nat) (eta : list relation_assignment) (rho : relation_env)
    (T : ty) : ty :=
  match T with
  | Ty_BVar i =>
      if i <? k then Ty_BVar i
      else
        match nth_error eta (i - k) with
        | Some a => a.(assignment_right)
        | None => Ty_BVar i
        end
  | Ty_FVar X =>
      match rho X with
      | Some a => a.(assignment_right)
      | None => Ty_FVar X
      end
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (right_type_rec k eta rho T1)
        (right_type_rec k eta rho T2)
  | Ty_All body => Ty_All (right_type_rec (S k) eta rho body)
  end.

Definition left_type eta rho T := left_type_rec 0 eta rho T.
Definition right_type eta rho T := right_type_rec 0 eta rho T.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Definition expression_lifting
    (T1 T2 : ty) (R : relation) (t1 t2 : tm) : Prop :=
  has_type [] empty t1 T1 /\
  has_type [] empty t2 T2 /\
  exists v1 v2,
    t1 -->* v1 /\
    t2 -->* v2 /\
    R v1 v2.

(* value_relation eta rho T v1 v2 意思是：
   在用 eta 解释 T 中的绑定类型变量、用 rho 解释 T 中的自由类型变量时，
   v1 和 v2 是类型 T 的左右两种解释下的一对相关的值。valuation本质就是在定义两个值的相关性。
   例子：
   eta : list relation_assignment := []；rho0 : relation_env := fun _ => None；
   T : ty := Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))，即 forall X, X -> X；
   id : tm := tm_tabs (tm_abs (Ty_BVar 0) (tm_bvar 0))，即 Lambda X, lambda x : X, x。
   要证明的完整命题是 value_relation eta rho0 T id id。
   Ty_All：对所有 relation_assignment a，令 U1 = a 的左类型、U2 = a 的右类型、
   R = a 的关系；分别用 U1、U2 实例化两个 id，得到 lambda x : U1, x 和
   lambda x : U2, x，接下来必须证明它们在 X -> X 下相关。
   Ty_Arrow：对所有在 X 下相关的 arg1、arg2，应用两个函数后分别得到 arg1、arg2；
   因此只需证明结果 arg1、arg2 在 X 下仍然相关。
   Ty_BVar：X 是 forall 绑定的变量，从 eta = [a] 找到 R；“arg1、arg2 在 X 下相关”
   就是 R arg1 arg2，而这正是 Ty_Arrow 已有的前提，所以结论成立。
   例如 a 的左右类型为 Bool、Nat，且 R true 1、R false 0，那么两个实例分别是
   id[Bool]、id[Nat]；相关输入 true、1 被原样返回，结果仍满足 R true 1。
   Ty_FVar：本例没有自由类型变量；若类型是自由变量 Y，则从 rho Y 找到关系。 *)
Fixpoint value_relation
    (eta : list relation_assignment) (rho : relation_env) (T : ty) : relation :=
  fun v1 v2 =>
    value v1 /\ value v2 /\
    has_type [] empty v1 (left_type eta rho T) /\
    has_type [] empty v2 (right_type eta rho T) /\
    match T with
    | Ty_BVar i =>
        (* nth_error eta i 意思是：尝试取得 eta 中下标为 i 的 assignment。 *)
        match nth_error eta i with
        | Some a => a.(assignment_relation) v1 v2
        | None => False
        end
    | Ty_FVar X =>
        match rho X with
        | Some a => a.(assignment_relation) v1 v2
        | None => False
        end
    | Ty_Arrow T1 T2 =>
        (* 相关函数必须把每一对相关参数变成一对相关结果。 *)
        exists body1 body2,
          v1 = tm_abs (left_type eta rho T1) body1 /\
          v2 = tm_abs (right_type eta rho T1) body2 /\
          forall arg1 arg2,
            value_relation eta rho T1 arg1 arg2 ->
            (* 就是 expression_relation eta rho T2
               (open_tm body1 arg1) (open_tm body2 arg2)。 *)
            expression_lifting
              (left_type eta rho T2) (right_type eta rho T2)
              (value_relation eta rho T2)
              (open_tm body1 arg1) (open_tm body2 arg2)
    | Ty_All body =>
        (* 对所有由候选关系关联的左右类型，相关多态值实例化后都得到相关程序。 *)
        exists body1 body2,
          v1 = tm_tabs body1 /\
          v2 = tm_tabs body2 /\
          forall a : relation_assignment,
            (* 就是 expression_relation (a :: eta) rho body
               (open_tm_ty body1 a.(assignment_left))
               (open_tm_ty body2 a.(assignment_right))。 *)
            expression_lifting
              (left_type (a :: eta) rho body)
              (right_type (a :: eta) rho body)
              (value_relation (a :: eta) rho body)
              (open_tm_ty body1 a.(assignment_left))
              (open_tm_ty body2 a.(assignment_right))
    end.

(* System F 的语义不变量。我们这里定义二元逻辑关系，是因为要证明自由定理。
   如果只是为了证明 normalization，也可以像 STLC 那样定义比较简单的一元逻辑关系。 *)
(* 在用 eta 解释 T 中的绑定类型变量、用 rho 解释 T 中的自由类型变量时，
   t1 和 t2 是类型 T 下的一对相关的程序。 *)
Definition expression_relation eta rho T t1 t2 : Prop :=
  expression_lifting
    (left_type eta rho T) (right_type eta rho T)
    (value_relation eta rho T) t1 t2.


(* 因为wf_ty_lc *)
Lemma assignment_left_lc : forall a,
  locally_closed_ty a.(assignment_left).
Proof.
  intros a. destruct a.(assignment_is_candidate) as [Hwf _].
  eapply wf_ty_lc; eauto.
Qed.

Lemma assignment_right_lc : forall a,
  locally_closed_ty a.(assignment_right).
Proof.
  intros a. destruct a.(assignment_is_candidate) as [_ [Hwf _]].
  eapply wf_ty_lc; eauto.
Qed.
(* 似懂非懂 *)
Lemma left_type_rec_cons_open : forall T k eta rho a,
  left_type_rec k (a :: eta) rho T =
  open_ty_rec k a.(assignment_left)
    (left_type_rec (S k) eta rho T).
Proof.
  induction T; intros k eta rho a0; simpl.
  - destruct (n <? k) eqn:Hnk.
    + apply Nat.ltb_lt in Hnk.
      assert (HnSk : n <? S k = true) by (apply Nat.ltb_lt; lia).
      rewrite HnSk. simpl.
      rewrite (proj2 (Nat.eqb_neq k n)) by lia. reflexivity.
    + apply Nat.ltb_ge in Hnk.
      destruct (Nat.eq_dec n k) as [E | Hneq].
      * subst n. rewrite (proj2 (Nat.ltb_lt k (S k))) by lia.
        simpl. rewrite Nat.eqb_refl.
        replace (k - k) with 0 by lia. reflexivity.
      * assert (Hkn : k < n) by lia.
        assert (HnSk : n <? S k = false) by (apply Nat.ltb_ge; lia).
        rewrite HnSk.
        replace (n - k) with (S (n - S k)) by lia. simpl.
        destruct (nth_error eta (n - S k)) as [b |] eqn:Hnth; simpl.
        -- symmetry. apply open_ty_rec_lc_at.
           eapply lc_ty_at_monotone.
           ++ apply assignment_left_lc.
           ++ lia.
        -- rewrite (proj2 (Nat.eqb_neq k n)) by lia. reflexivity.
  - destruct (rho a) as [b |] eqn:Hlookup; simpl.
    + symmetry. apply open_ty_rec_lc_at.
      eapply lc_ty_at_monotone.
      * apply assignment_left_lc.
      * lia.
    + reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
  - rewrite IHT. reflexivity.
Qed.

Lemma right_type_rec_cons_open : forall T k eta rho a,
  right_type_rec k (a :: eta) rho T =
  open_ty_rec k a.(assignment_right)
    (right_type_rec (S k) eta rho T).
Proof.
  induction T; intros k eta rho a0; simpl.
  - destruct (n <? k) eqn:Hnk.
    + apply Nat.ltb_lt in Hnk.
      assert (HnSk : n <? S k = true) by (apply Nat.ltb_lt; lia).
      rewrite HnSk. simpl.
      rewrite (proj2 (Nat.eqb_neq k n)) by lia. reflexivity.
    + apply Nat.ltb_ge in Hnk.
      destruct (Nat.eq_dec n k) as [E | Hneq].
      * subst n. rewrite (proj2 (Nat.ltb_lt k (S k))) by lia.
        simpl. rewrite Nat.eqb_refl.
        replace (k - k) with 0 by lia. reflexivity.
      * assert (Hkn : k < n) by lia.
        assert (HnSk : n <? S k = false) by (apply Nat.ltb_ge; lia).
        rewrite HnSk.
        replace (n - k) with (S (n - S k)) by lia. simpl.
        destruct (nth_error eta (n - S k)) as [b |] eqn:Hnth; simpl.
        -- symmetry. apply open_ty_rec_lc_at.
           eapply lc_ty_at_monotone.
           ++ apply assignment_right_lc.
           ++ lia.
        -- rewrite (proj2 (Nat.eqb_neq k n)) by lia. reflexivity.
  - destruct (rho a) as [b |] eqn:Hlookup; simpl.
    + symmetry. apply open_ty_rec_lc_at.
      eapply lc_ty_at_monotone.
      * apply assignment_right_lc.
      * lia.
    + reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
  - rewrite IHT. reflexivity.
Qed.

Lemma left_type_cons_open : forall eta rho a T,
  left_type (a :: eta) rho T =
  open_ty (left_type_rec 1 eta rho T) a.(assignment_left).
Proof.
  intros. unfold left_type, open_ty. simpl.
  apply left_type_rec_cons_open.
Qed.

Lemma right_type_cons_open : forall eta rho a T,
  right_type (a :: eta) rho T =
  open_ty (right_type_rec 1 eta rho T) a.(assignment_right).
Proof.
  intros. unfold right_type, open_ty. simpl.
  apply right_type_rec_cons_open.
Qed.

(* 显然。 *)
Lemma value_relation_values : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  intros eta rho T v1 v2 H. destruct T; simpl in H; tauto.
Qed.

Lemma value_relation_typing : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 ->
  has_type [] empty v1 (left_type eta rho T) /\
  has_type [] empty v2 (right_type eta rho T).
Proof.
  intros eta rho T v1 v2 H. destruct T; simpl in H; tauto.
Qed.

(* 因为两个相关的值本身就是两个相关的程序。 *)
Lemma expression_relation_of_values : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 ->
  expression_relation eta rho T v1 v2.
Proof.
  intros eta rho T v1 v2 HR.
  destruct (value_relation_values _ _ _ _ _ HR) as [Hv1 Hv2].
  destruct (value_relation_typing _ _ _ _ _ HR) as [Ht1 Ht2].
  unfold expression_relation, expression_lifting.
  repeat split; try assumption.
  exists v1, v2. repeat split; try constructor; assumption.
Qed.

(* 显然，因为 value 本身就是 locally_closed 的
   <{ lambda : $(T), t }> 或 <{ Lambda, t }>。 *)
Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv. inversion Hv; assumption.
Qed.

(* 显然。 *)
Lemma expression_lifting_equiv : forall T1 T2 R S,
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  forall t1 t2,
    expression_lifting T1 T2 R t1 t2 <->
    expression_lifting T1 T2 S t1 t2.
Proof.
  intros T1 T2 R S HRS t1 t2. unfold expression_lifting.
  split; intros [Ht1 [Ht2 [v1 [v2 [Hs1 [Hs2 HR]]]]]];
    repeat split; try assumption.
  - exists v1, v2. repeat split; try assumption. apply HRS. assumption.
  - exists v1, v2. repeat split; try assumption. apply HRS. assumption.
Qed.

(* 显然。 *)
Lemma multi_trans : forall t1 t2 t3,
  t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H12 H23. induction H12; eauto using multi.
Qed.

Lemma multi_app1 : forall t1 t1' t2,
  t1 -->* t1' -> locally_closed_tm t2 ->
  tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 Hsteps Hlc. induction Hsteps.
  - constructor.
  - econstructor; [eapply ST_App1; eauto | exact IHHsteps].
Qed.

Lemma multi_app2 : forall v1 t2 t2',
  value v1 -> t2 -->* t2' ->
  tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv Hsteps. induction Hsteps.
  - constructor.
  - econstructor; [eapply ST_App2; eauto | exact IHHsteps].
Qed.

Lemma multi_tapp : forall t t' T,
  t -->* t' -> locally_closed_ty T ->
  tm_tapp t T -->* tm_tapp t' T.
Proof.
  intros t t' T Hsteps Hlc. induction Hsteps.
  - constructor.
  - econstructor; [eapply ST_TApp; eauto | exact IHHsteps].
Qed.

(* 在 eta 和 rho 对类型变量的解释下：
   如果函数程序 t1 和 t1' 在函数类型 T1 -> T2 下相关，
   并且参数程序 t2 和 t2' 在类型 T1 下相关，
   那么应用程序 t1 t2 和 t1' t2' 在类型 T2 下相关。 *)
Lemma expression_relation_app : forall eta rho T1 T2 t1 t1' t2 t2',
  expression_relation eta rho (Ty_Arrow T1 T2) t1 t1' ->
  expression_relation eta rho T1 t2 t2' ->
  expression_relation eta rho T2
    (tm_app t1 t2) (tm_app t1' t2').
Proof.
  unfold expression_relation, expression_lifting.
  intros eta rho T1 T2 t1 t1' t2 t2' Hfun Harg.
  destruct Hfun as [Ht1 [Ht1' [v1 [v1' [Hs1 [Hs1' HRfun]]]]]].
  destruct Harg as [Ht2 [Ht2' [v2 [v2' [Hs2 [Hs2' HRarg]]]]]].
  simpl in HRfun.
  destruct HRfun as
    [Hv1 [Hv1' [HTv1 [HTv1' [body1 [body1' [E1 [E2 Hbody]]]]]]]].
  subst v1. subst v1'.
  pose proof (value_relation_values _ _ _ _ _ HRarg) as [Hv2 Hv2'].
  pose proof (Hbody v2 v2' HRarg) as Hresult.
  destruct Hresult as
    [Hopen1 [Hopen2 [w1 [w2 [Hw1 [Hw2 HRw]]]]]].
  repeat split.
  - eapply T_App; eauto.
  - eapply T_App; eauto.
  - exists w1, w2. repeat split; try assumption.
    + eapply multi_trans.
      * apply multi_app1; [exact Hs1 | eapply typing_lc; eauto].
      * eapply multi_trans.
        -- apply multi_app2; [exact Hv1 | exact Hs2].
        -- econstructor.
           ++ apply ST_AppAbs; [apply value_lc; exact Hv1 | exact Hv2].
           ++ exact Hw1.
    + eapply multi_trans.
      * apply multi_app1; [exact Hs1' | eapply typing_lc; eauto].
      * eapply multi_trans.
        -- apply multi_app2; [exact Hv1' | exact Hs2'].
        -- econstructor.
           ++ apply ST_AppAbs; [apply value_lc; exact Hv1' | exact Hv2'].
           ++ exact Hw2.
Qed.

(* 相关的多态程序，使用由 R 关联的两个类型分别实例化后，仍然相关。 *)
(*
例子：
  为了直观，先假设语言有 Bool 和 Nat；在我们的极简 System F 中，它们也可以被编码出来。
  取两个相同的多态恒等程序：

  t1 = Lambda X, lambda x : X, x
  t2 = Lambda X, lambda x : X, x

  它们的类型都是：

  forall X, X -> X

  这里：

  T = X -> X
  eta = []
  rho = empty_relation_env

  因此第一个主要前提是：

  expression_relation [] empty_relation_env
    (forall X, X -> X) t1 t2

  现在选择两个不同的具体类型：

  U1 = Bool
  U2 = Nat

  定义一个关系 R：

  R true  1
  R false 0

  除此之外的值都不相关。也可以写成：

  R b n 当且仅当
    (b = true 且 n = 1)
    或
    (b = false 且 n = 0)

  Bool、Nat 都是封闭且良构的类型；R 只关联封闭值，并且相关值分别具有 Bool 和 Nat 类型，
  所以 relation_candidate Bool Nat R。

  把 U1、U2、R 和这个候选关系证明包装成 assignment a，再应用：

  expression_relation_tapp

  得到：

  expression_relation [a] empty_relation_env (X -> X)
    (t1[Bool])
    (t2[Nat])

  分别进行类型应用：

  t1[Bool] = lambda x : Bool, x
  t2[Nat]  = lambda x : Nat, x

  因此结论是在 eta = [a] 的解释下：

  lambda x : Bool, x

  和：

  lambda x : Nat, x

  在 X -> X 下相关。这里 X = Ty_BVar 0，所以通过：

  nth_error [a] 0 = Some a

  知道 X 应该使用 a 中保存的关系 R 解释。
  按照函数关系的定义，我们还要检查：对任意满足 R arg1 arg2 的参数，
  两个函数的结果仍被 R 关联。

  第一组相关参数：

  arg1 = true
  arg2 = 1
  R true 1

  分别应用：

  (lambda x : Bool, x) true --> true
  (lambda x : Nat,  x) 1    --> 1

  输出仍然满足 R true 1。

  第二组相关参数：

  arg1 = false
  arg2 = 0
  R false 0

  分别应用：

  (lambda x : Bool, x) false --> false
  (lambda x : Nat,  x) 0     --> 0

  输出仍然满足 R false 0。

  所以整个例子说明：
  多态恒等函数分别在 Bool 和 Nat 上运行时，会保持我们任意指定的合格对应关系 R。
*)
(* 似懂非懂 *)
Lemma expression_relation_tapp : forall eta rho T t1 t2 a,
  expression_relation eta rho (Ty_All T) t1 t2 ->
  expression_relation (a :: eta) rho T
    (tm_tapp t1 a.(assignment_left))
    (tm_tapp t2 a.(assignment_right)).
Proof.
  unfold expression_relation, expression_lifting.
  intros eta rho T t1 t2 a Hall.
  destruct Hall as [Ht1 [Ht2 [v1 [v2 [Hs1 [Hs2 HRall]]]]]].
  simpl in HRall.
  destruct HRall as
    [Hv1 [Hv2 [HTv1 [HTv2 [body1 [body2 [E1 [E2 Hbody]]]]]]]].
  subst v1. subst v2.
  pose proof (Hbody a) as Hresult.
  destruct Hresult as
    [Hopen1 [Hopen2 [w1 [w2 [Hw1 [Hw2 HRw]]]]]].
  pose proof a.(assignment_is_candidate) as Ha_valid.
  destruct Ha_valid as [Hwf1 [Hwf2 HRa]].
  repeat split.
  - rewrite left_type_cons_open.
    eapply T_TApp; eauto.
  - rewrite right_type_cons_open.
    eapply T_TApp; eauto.
  - exists w1, w2. repeat split; try assumption.
    + eapply multi_trans.
      * apply multi_tapp; [exact Hs1 | eapply wf_ty_lc; eauto].
      * econstructor.
        -- apply ST_TAppTabs; [apply value_lc; exact Hv1 | eapply wf_ty_lc; eauto].
        -- exact Hw1.
    + eapply multi_trans.
      * apply multi_tapp; [exact Hs2 | eapply wf_ty_lc; eauto].
      * econstructor.
        -- apply ST_TAppTabs; [apply value_lc; exact Hv2 | eapply wf_ty_lc; eauto].
        -- exact Hw2.
Qed.

End SystemFLogicalRelation.
