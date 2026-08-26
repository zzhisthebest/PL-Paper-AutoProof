Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From AutoProof Require Import Smallstep.
From AutoProof.STLC Require Import Syntax.
From AutoProof.STLC Require Import StlcProp.

Import ListNotations.

Module STLCNorm.
Import STLC.
Import STLCProp.

(* -->* 表示零步或多步归约。 *)
(* 程序终止的定义：t 最终能归约到某个 value。 *)
Definition halts (t : tm) : Prop :=
  exists v, t -->* v /\ value v.

(* 多步归约可以传递：t -->* u 且 u -->* v，则 t -->* v。 *)
Lemma multi_trans : forall t u v,
  t -->* u ->
  u -->* v ->
  t -->* v.
Proof.
  intros t u v Htu Huv.
  induction Htu.
  - exact Huv.
  - eapply multi_step; eauto.
Qed.

(* 如果函数部分多步归约，那么整个 application 的函数部分也可以同步多步归约。 *)
Lemma multi_app1 : forall t1 t1' t2,
  t1 -->* t1' ->
  locally_closed t2 ->
  tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 Hs Ht2.
  induction Hs.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App1; eauto.
    + exact IHHs.
Qed.



(* 如果函数已经是 value，那么参数部分的多步归约可以搬到整个 application 里。 *)
Lemma multi_app2 : forall v1 t2 t2',
  value v1 ->
  t2 -->* t2' ->
  tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv Hs.
  induction Hs.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; eauto.
    + exact IHHs.
Qed.

(* if 条件部分的多步归约可以搬到整个 if 里。 *)
Lemma multi_if : forall t1 t1' t2 t3,
  t1 -->* t1' ->
  locally_closed t2 ->
  locally_closed t3 ->
  tm_if t1 t2 t3 -->* tm_if t1' t2 t3.
Proof.
  intros t1 t1' t2 t3 Hs Ht2 Ht3.
  induction Hs.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_If; eauto.
    + exact IHHs.
Qed.



Print value.
(**
对好值的定义。
  value_relation T v：
  已经算完的值 v 在类型 T 下是“好值”。

  Bool 分支：好值只能是 true 或 false。
  Arrow 分支：v 必须是一个 lambda；对任意 T1 下的好值 arg，
     将 arg 放入函数体后得到的 open body arg 必须是 T2 下的好程序。这就是好函数的定义。
*)
Fixpoint value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Bool =>
      v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        forall arg,
          value_relation T1 arg ->
          (* 其实就是expression_relation T2 (open body arg) *)
          locally_closed (open body arg) /\
          exists v',
            open body arg -->* v' /\
            value_relation T2 v'
  end.

(**
对好程序的定义。
  expression_relation T t：
  一般程序 t 在类型 T 下是“好程序”。
*)
Definition expression_relation (T : ty) (t : tm) : Prop :=
  (* locally_closed t已经被value_relation T v包含，但这里加上它是为了方便 *)
  locally_closed t /\
  exists v,
    t -->* v /\
    value_relation T v.

(* 替换环境：给每个自由变量指定一个要替换成的程序。 *)
Definition term_substitution := atom -> tm.

(* 恒等替换：每个自由变量仍然替换成它自己。 *)
Definition id_substitution : term_substitution :=
  fun x => tm_fvar x.

(* rho 是希腊字母 ρ 的英文写法，PL 文献里常用它表示“环境”或“映射” *)
(* 在替换环境 rho 里，把 x 改成映射到 v。 *)
Definition subst_update
    (rho : term_substitution) (x : atom) (v : tm) : term_substitution :=
  fun y => if Nat.eqb x y then v else rho y.

(* msubst rho t：按照 rho 同时替换 t 里的所有自由变量。 *)
Fixpoint msubst (rho : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (msubst rho t1) (msubst rho t2)
  | tm_abs T t1 => tm_abs T (msubst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (msubst rho t1) (msubst rho t2) (msubst rho t3)
  end.

(* proper_substitution：替换进去的每个程序本身都必须是合法完整程序。 *)
Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

(**
  related_substitution Gamma rho：
  如果 Gamma 说 x : T，那么 rho x 必须是 T 下的好值。
  一是为了保证rho与Gamma类型一致。二是提供了value_relation这个性质保证。
*)
Definition related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T, Gamma x = Some T -> value_relation T (rho x).


Print value_relation.
(* 从 value_relation 里取出 value 条件。 *)
Lemma value_relation_value : forall T v,
  value_relation T v -> value v.
Proof.
  intros T v H. destruct T; simpl in H; tauto.
Qed.

(* 从 value_relation 里取出 locally_closed 条件。 *)
Lemma value_relation_term : forall T v,
  value_relation T v -> locally_closed v.
Proof.
  intros T v H.
  apply value_regular.
  apply value_relation_value with (T := T).
  exact H.
Qed.

(* expression_relation 比 halts 更强，所以可以推出 halts。 *)
Lemma expression_relation_halts : forall T t,
  expression_relation T t ->
  halts t.
Proof.
  intros T t [_ [v [Hs HV]]].
  exists v. split.
  - exact Hs.
  - apply value_relation_value with (T := T). exact HV.
Qed.

Print lc_at.

(* 如果 t 在层数 k 下已经闭合，那么打开更外层的 index 不改变 t。 
显然，因为 t 里没有 open_rec j 要替换的那个绑定变量。。*)
Lemma open_rec_lc_at : forall k t j u,
  lc_at k t ->
  k <= j ->
  open_rec j u t = t.
Proof.
  intros k t j u Hlc.
  generalize dependent j.
  induction Hlc; intros j Hle; simpl.
  - destruct (Nat.eqb j i) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + reflexivity.
  - reflexivity.
  - rewrite IHHlc1 by assumption.
    rewrite IHHlc2 by assumption.
    reflexivity.
  - rewrite IHHlc by lia. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHHlc1 by assumption.
    rewrite IHHlc2 by assumption.
    rewrite IHHlc3 by assumption.
    reflexivity.
Qed.

(* 完整程序不含任何裸 bvar，所以 open_rec 不改变它。 *)
Lemma open_rec_term : forall t j u,
  locally_closed t ->
  open_rec j u t = t.
Proof.
  unfold locally_closed. intros.
  eapply open_rec_lc_at; eauto. lia.
Qed.

(* 合法替换保持 lc_at。 *)
Lemma msubst_preserves_lc_at : forall rho k t,
  proper_substitution rho ->
  lc_at k t ->
  lc_at k (msubst rho t).
Proof.
  intros rho k t Hproper Hlc.
  (* 对lc_at的各个分支进行数学归纳法，其实挺长 *)
  induction Hlc; simpl; eauto using lc_at.
  - apply term_lc_at. apply Hproper.
Qed.

(* 合法替换保持完整程序。上一个定理的推论。 *)
Lemma msubst_preserves_term : forall rho t,
  proper_substitution rho ->
  locally_closed t ->
  locally_closed (msubst rho t).
Proof.
  unfold locally_closed. intros.
  eapply msubst_preserves_lc_at; eauto.
Qed.

(* 如果 rho 合法，且 v 是完整程序，那么更新 rho 后仍然合法。 *)
(* 显然 *)
Lemma proper_update : forall rho x v,
  proper_substitution rho ->
  locally_closed v ->
  proper_substitution (subst_update rho x v).
Proof.
  unfold proper_substitution, subst_update.
  intros rho x v Hproper Hv y.
  destruct (Nat.eqb x y); auto.
Qed.

(* 如果 rho 和 Gamma 对应，那么同时扩展 x:T 和 x->v 后仍然对应。
显然 *)
Lemma related_update : forall Gamma rho x T v,
  related_substitution Gamma rho ->
  value_relation T v ->
  related_substitution (update Gamma x T) (subst_update rho x v).
Proof.
  unfold related_substitution, subst_update, update.
  intros Gamma rho x T v Hrel HV y U Hy.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst y.
    injection Hy as ->. exact HV.
  - apply Hrel. exact Hy.
Qed.

(* 辅助引理：不在 L1 ++ L2 里，等价于既不在 L1 里也不在 L2 里。
显然 *)
Lemma notin_app_split : forall (x : atom) L1 L2,
  ~ In x (L1 ++ L2) ->
  ~ In x L1 /\ ~ In x L2.
Proof.
  intros x L1 L2 H.
  split; intro Hin; apply H; apply in_app_iff; auto.
Qed.

(**
  LN 的关键替换/open 交换性质：
  先用新自由变量 x 打开函数体，再把 x 替换成 v，
  等价于直接用 v 打开函数体。
*)
Lemma msubst_open_update_rec : forall t rho x v k,
  ~ In x (free_vars t) ->
  proper_substitution rho ->
  locally_closed v ->
  (* musust rho (open_rec k v t)就不等于，因为v可能含有rho里的自由变量。
  如果v不含rho里的自由变量，那就等于*)
  msubst (subst_update rho x v) (open_rec k (tm_fvar x) t) =
  open_rec k v (msubst rho t).
Proof.
  induction t; intros rho x v k Hfresh Hproper Hv; simpl in *.
  - destruct (Nat.eqb k n) eqn:Heq.
    + unfold subst_update. simpl.
      destruct (Nat.eqb x x) eqn:Hxx.
      * reflexivity.
      * apply Nat.eqb_neq in Hxx. contradiction.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst a. contradiction Hfresh. simpl. auto.
    + unfold subst_update. rewrite Heq.
      symmetry. apply open_rec_term. apply Hproper.
  - apply notin_app_split in Hfresh as [Hfresh1 Hfresh2].
    rewrite IHt1 by assumption.
    rewrite IHt2 by assumption.
    reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply notin_app_split in Hfresh as [Hfresh1 Hfresh23].
    apply notin_app_split in Hfresh23 as [Hfresh2 Hfresh3].
    rewrite IHt1 by assumption.
    rewrite IHt2 by assumption.
    rewrite IHt3 by assumption.
    reflexivity.
Qed.

(* 上面引理在最外层 lambda 的版本。 *)
Lemma msubst_open_update : forall t rho x v,
  ~ In x (free_vars t) ->
  proper_substitution rho ->
  locally_closed v ->
  msubst (subst_update rho x v) (open t (tm_fvar x)) =
  open (msubst rho t) v.
Proof.
  unfold open. intros.
  apply msubst_open_update_rec; assumption.
Qed.

(* 恒等替换不改变程序。显然 *)
Lemma msubst_id : forall t,
  msubst id_substitution t = t.
Proof.
  induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
    try rewrite IHt3; reflexivity.
Qed.

(* 恒等替换是合法替换。 *)
Lemma id_substitution_proper :
  proper_substitution id_substitution.
Proof.
  unfold proper_substitution, id_substitution, locally_closed.
  intros. apply lc_fvar.
Qed.

Print related_substitution.
(* 空环境下没有变量需要检查，所以恒等替换自动满足 related_substitution。 *)
Lemma empty_related :
  related_substitution empty id_substitution.
Proof.
  unfold related_substitution, empty.
  intros. discriminate H.
Qed.

(**
  Fundamental theorem:
  如果 t 在 Gamma 下类型正确，并且 rho 给 Gamma 中变量都配了好值，
  那么替换后的程序 msubst rho t 是 T 下的好程序。
*)
Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho,
    proper_substitution rho ->
    related_substitution Gamma rho ->
    expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Htyping.
  induction Htyping; intros rho Hproper Hrel.
  - split.
    + apply Hproper.
    + exists (rho x). split.
      * apply multi_refl.
      * apply Hrel with (x := x). exact H.
  - split.
    + change (locally_closed (msubst rho (tm_abs T1 t1))).
      apply msubst_preserves_term.
      * exact Hproper.
      * apply typing_regular with (Gamma := Gamma) (T := Ty_Arrow T1 T2).
        apply T_Abs with (L := L). exact H.
    + exists (tm_abs T1 (msubst rho t1)).
      split.
      * apply multi_refl.
      * simpl. repeat split.
        -- apply v_abs.
           change (locally_closed (msubst rho (tm_abs T1 t1))).
           apply msubst_preserves_term.
           ++ exact Hproper.
           ++ apply typing_regular with (Gamma := Gamma) (T := Ty_Arrow T1 T2).
              apply T_Abs with (L := L). exact H.
        -- exists (msubst rho t1). split.
           ++ reflexivity.
           ++ intros arg HVarg.
              pose (x := fresh (L ++ free_vars t1)).
              assert (HxL : ~ In x L).
              {
                intro Hin. unfold x in Hin.
                apply (fresh_notin (L ++ free_vars t1)).
                apply in_or_app. left. exact Hin.
              }
              assert (Hxfv : ~ In x (free_vars t1)).
              {
                intro Hin. unfold x in Hin.
                apply (fresh_notin (L ++ free_vars t1)).
                apply in_or_app. right. exact Hin.
              }
              specialize (H0 x HxL (subst_update rho x arg)).
              assert (Harg_term : locally_closed arg).
              {
                apply value_relation_term with (T := T1). exact HVarg.
              }
              specialize (H0 (proper_update rho x arg Hproper Harg_term)).
              specialize (H0 (related_update Gamma rho x T1 arg Hrel HVarg)).
              rewrite (msubst_open_update t1 rho x arg Hxfv Hproper Harg_term) in H0.
              exact H0.
  - destruct (IHHtyping1 rho Hproper Hrel) as [Ht1 [vf [Hs1 HVf]]].
    destruct (IHHtyping2 rho Hproper Hrel) as [Ht2 [va [Hs2 HVa]]].
    destruct HVf as [HVf_value [body [Heq Hbody]]].
    subst vf.
    assert (HVf_term : locally_closed (tm_abs T1 body)).
    {
      apply value_regular. exact HVf_value.
    }
    specialize (Hbody va HVa).
    destruct Hbody as [Hbody_term [vr [Hsbody HVr]]].
    split.
    + simpl. apply lc_app; assumption.
    + exists vr. split.
      * eapply multi_trans.
        -- apply multi_app1; eauto.
        -- eapply multi_trans.
           ++ apply multi_app2.
              ** apply v_abs. exact HVf_term.
              ** exact Hs2.
           ++ eapply multi_step.
              ** apply ST_AppAbs.
                 --- exact HVf_term.
                 --- apply value_relation_value with (T := T1). exact HVa.
              ** exact Hsbody.
      * exact HVr.
  - split.
    + unfold locally_closed. apply lc_true.
    + exists tm_true. split.
      * apply multi_refl.
      * simpl. split.
        -- apply v_true.
        -- left. reflexivity.
  - split.
    + unfold locally_closed. apply lc_false.
    + exists tm_false. split.
      * apply multi_refl.
      * simpl. split.
        -- apply v_false.
        -- right. reflexivity.
  - destruct (IHHtyping1 rho Hproper Hrel) as [Ht1 [vb [Hsb HVb]]].
    destruct (IHHtyping2 rho Hproper Hrel) as [Ht2 [v2 [Hs2 HV2]]].
    destruct (IHHtyping3 rho Hproper Hrel) as [Ht3 [v3 [Hs3 HV3]]].
    destruct HVb as [_ [Hb | Hb]]; subst vb.
    + split.
      * simpl. apply lc_if; assumption.
      * exists v2. split.
        -- eapply multi_trans.
           ++ apply multi_if; eauto.
           ++ eapply multi_step.
              ** apply ST_IfTrue; assumption.
              ** exact Hs2.
        -- exact HV2.
    + split.
      * simpl. apply lc_if; assumption.
      * exists v3. split.
        -- eapply multi_trans.
           ++ apply multi_if; eauto.
           ++ eapply multi_step.
              ** apply ST_IfFalse; assumption.
              ** exact Hs3.
        -- exact HV3.
Qed.

(* Normalization：闭合且类型正确的 STLC 程序一定终止。 *)
Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  halts t.
Proof.
  intros t T Htyping.
  pose proof (fundamental empty t T Htyping id_substitution
    id_substitution_proper empty_related) as Hrel.
  rewrite msubst_id in Hrel.
  apply expression_relation_halts with (T := T). exact Hrel.
Qed.

End STLCNorm.
