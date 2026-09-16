From Stdlib Require Import Arith.PeanoNat Lists.List Lia ZArith.BinInt.
From AutoProof.SystemFRefinementNonDeterminism Require Import Syntax RefinementLogic.

Module SystemFRefinementNonDeterminismTyping.
Import ListNotations.
Import SystemFRefinementNonDeterminism.
Export SystemFRefinementNonDeterminismLogic.

(** Refinement types follow the SystemRF shape.  [R_Func R1 R2] and
    [R_Exists R1 R2] bind one term variable in [R2]. *)
(* 定义一种叫 rty 的数据类型，用来表示我们这门语言中的所有 refinement types *)
Inductive rty : Type :=
  | R_Refine : ty -> qualifier -> rty
  | R_Func : rty -> rty -> rty
  | R_Exists : rty -> rty -> rty
  | R_Poly : rty -> rty.

(* 删除 refinement type 中的额外 predicate，只保留普通 System F 类型 *)
Fixpoint erase (R : rty) : ty :=
  match R with
  | R_Refine T _ => T
  | R_Func R1 R2 => Ty_Arrow (erase R1) (erase R2)
  | R_Exists _ R2 => erase R2
  | R_Poly R => Ty_All (erase R)
  end.

(* 在 refinement type R 中，把编号为 k的绑定程序变量替换成程序u。 *)
Fixpoint open_rty_tm_rec (k : nat) (u : tm) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine T (open_qualifier_tm_rec (S k) u ps)
  | R_Func R1 R2 =>
      R_Func (open_rty_tm_rec k u R1) (open_rty_tm_rec (S k) u R2)
  | R_Exists R1 R2 =>
      R_Exists (open_rty_tm_rec k u R1) (open_rty_tm_rec (S k) u R2)
  | R_Poly R1 => R_Poly (open_rty_tm_rec k u R1)
  end.

(* 在 refinement type R 中，把它当前最外层绑定的程序变量替换成程序 u。
 例如：
R = {v : U | v = x}
如果这里的 x 是等待打开的函数参数（x在v外层），那么：
open_rty_tm R true
得到：
{v : U | v = true}
*)
Definition open_rty_tm (R : rty) (u : tm) : rty :=
  open_rty_tm_rec 0 u R.

Fixpoint open_rty_ty_rec (k : nat) (U : ty) (R : rty) : rty :=
  match R with
  | R_Refine T ps =>
      R_Refine (open_ty_rec k U T) (open_qualifier_ty_rec k U ps)
  | R_Func R1 R2 =>
      R_Func (open_rty_ty_rec k U R1) (open_rty_ty_rec k U R2)
  | R_Exists R1 R2 =>
      R_Exists (open_rty_ty_rec k U R1) (open_rty_ty_rec k U R2)
  | R_Poly R1 => R_Poly (open_rty_ty_rec (S k) U R1)
  end.

Definition open_rty_ty (R : rty) (U : ty) : rty :=
  open_rty_ty_rec 0 U R.

Fixpoint rty_subst (x : atom) (s : tm) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine T (qualifier_subst x s ps)
  | R_Func R1 R2 => R_Func (rty_subst x s R1) (rty_subst x s R2)
  | R_Exists R1 R2 => R_Exists (rty_subst x s R1) (rty_subst x s R2)
  | R_Poly R1 => R_Poly (rty_subst x s R1)
  end.

Fixpoint rty_ty_subst (X : atom) (U : ty) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine (ty_subst X U T) (qualifier_ty_subst X U ps)
  | R_Func R1 R2 =>
      R_Func (rty_ty_subst X U R1) (rty_ty_subst X U R2)
  | R_Exists R1 R2 =>
      R_Exists (rty_ty_subst X U R1) (rty_ty_subst X U R2)
  | R_Poly R1 => R_Poly (rty_ty_subst X U R1)
  end.

Inductive lc_rty_at : nat -> nat -> rty -> Prop :=
  | LCR_Refine : forall K k T ps,
      lc_ty_at K T ->
      lc_qualifier_at K (S k) ps ->
      lc_rty_at K k (R_Refine T ps)
  | LCR_Func : forall K k R1 R2,
      lc_rty_at K k R1 ->
      lc_rty_at K (S k) R2 ->
      lc_rty_at K k (R_Func R1 R2)
  | LCR_Exists : forall K k R1 R2,
      lc_rty_at K k R1 ->
      lc_rty_at K (S k) R2 ->
      lc_rty_at K k (R_Exists R1 R2)
  | LCR_Poly : forall K k R,
      lc_rty_at (S K) k R ->
      lc_rty_at K k (R_Poly R).

Definition locally_closed_rty (R : rty) : Prop := lc_rty_at 0 0 R.

Definition rcontext := list (atom * rty).

Fixpoint lookup_rcontext (x : atom) (RGamma : rcontext) : option rty :=
  match RGamma with
  | [] => None
  | (y, R) :: RGamma' =>
      if Nat.eqb x y then Some R else lookup_rcontext x RGamma'
  end.

Definition empty_rcontext : rcontext := [].
Definition update_rcontext (RGamma : rcontext) (x : atom) (R : rty) : rcontext :=
  (x, R) :: RGamma.

(* 把记录 refinement type 的环境 RGamma，转换成只记录普通类型的环境 context。 *)
Fixpoint erase_context (RGamma : rcontext) : context :=
  match RGamma with
  | [] => empty
  | (x, R) :: RGamma' => update (erase_context RGamma') x (erase R)
  end.

(* 定义什么refinement type 是合法的 *)
(*
wf_rty Delta RGamma R 的意思是：
refinement type R 在类型变量环境 Delta 和 refinement 程序变量环境 RGamma 中是合法的。 *)
Inductive wf_rty : ty_context -> rcontext -> rty -> Prop :=
  (*
  R_Refine T ps 合法
  当且仅当：
  1. 普通类型 T 合法。
  2. 假设被描述的值 x 具有类型 T，公式 ps 也写得合法。
  例如：
  {v : U | v = u}
  只需检查 U 合法，并且在假设 v : U 后，v = u 是合法的等式。 *)
  | RWF_Refine : forall (L : list atom) Delta RGamma T ps,
      wf_ty Delta T ->
      (forall x, ~ In x L ->
        qualifier_wf Delta
          (update (erase_context RGamma) x T)
          (open_qualifier_tm ps (tm_fvar x))) ->
      wf_rty Delta RGamma (R_Refine T ps)
  (* R_Func R1 R2 合法，当且仅当：
  1. 参数的 refinement type R1 合法。
  2. 假设参数 x 的类型是 R1，返回值的 refinement type R2 也合法。
  例：(x : {u : U | True}) -> {v : U | v = x} 是一个 refinement type，
  表示接收 U 类型的 x，返回 U 类型的 v，并要求 v = x。（它可以作为 lambda x, x 的类型。）
  注意：{u : U | True}可以理解为U，只不过前者:rty，后者:ty。
  *)
  | RWF_Func : forall (L : list atom) Delta RGamma R1 R2,
      wf_rty Delta RGamma R1 ->
      (forall x, ~ In x L ->
        wf_rty Delta (update_rcontext RGamma x R1)
          (open_rty_tm R2 (tm_fvar x))) ->
      wf_rty Delta RGamma (R_Func R1 R2)

  | RWF_Exists : forall (L : list atom) Delta RGamma R1 R2,
      wf_rty Delta RGamma R1 ->
      (forall x, ~ In x L ->
        wf_rty Delta (update_rcontext RGamma x R1)
          (open_rty_tm R2 (tm_fvar x))) ->
      wf_rty Delta RGamma (R_Exists R1 R2)
  | RWF_Poly : forall (L : list atom) Delta RGamma R,
      (forall X, ~ In X L ->
        wf_rty (X :: Delta) RGamma (open_rty_ty R (Ty_FVar X))) ->
      wf_rty Delta RGamma (R_Poly R).
(*entails Delta RGamma ps qs
  表示：利用环境 RGamma 中的假设，公式 ps 能推出公式 qs。
  下面给出逻辑推导规则，不是完整的 SMT 求解器。*)
Inductive entails : ty_context -> rcontext -> qualifier -> qualifier -> Prop :=
  | Entails_Refl : forall Delta RGamma ps,
      entails Delta RGamma ps ps
  | Entails_True : forall Delta RGamma ps,
      entails Delta RGamma ps Pred_True
  | Entails_Trans : forall Delta RGamma ps qs rs,
      entails Delta RGamma ps qs ->
      entails Delta RGamma qs rs ->
      entails Delta RGamma ps rs
  | Entails_AndLeft : forall Delta RGamma p q,
      entails Delta RGamma (Pred_And p q) p
  | Entails_AndRight : forall Delta RGamma p q,
      entails Delta RGamma (Pred_And p q) q
  | Entails_AndIntro : forall Delta RGamma ps p qs,
      entails Delta RGamma ps p ->
      entails Delta RGamma ps qs ->
      entails Delta RGamma ps (Pred_And p qs)
  | Entails_OrLeft : forall Delta RGamma p q,
      entails Delta RGamma p (Pred_Or p q)
  | Entails_OrRight : forall Delta RGamma p q,
      entails Delta RGamma q (Pred_Or p q)
  | Entails_OrElim : forall Delta RGamma p q r,
      entails Delta RGamma p r ->
      entails Delta RGamma q r ->
      entails Delta RGamma (Pred_Or p q) r
  | Entails_NotIntro : forall Delta RGamma p q,
      entails Delta RGamma (Pred_And p q) Pred_False ->
      entails Delta RGamma p (Pred_Not q)
  | Entails_NotElim : forall Delta RGamma p,
      entails Delta RGamma (Pred_And p (Pred_Not p)) Pred_False
  | Entails_Context : forall Delta RGamma x T p q,
      lookup_rcontext x RGamma = Some (R_Refine T p) ->
      entails Delta RGamma q (open_qualifier_tm p (tm_fvar x))
  (* False 可以推出任何条件 *)
  | Entails_False : forall Delta RGamma q,
      entails Delta RGamma Pred_False q.

(*
has_rtype Delta RGamma t R 意思是：
在类型变量环境 Delta 和程序变量环境 RGamma 下，程序 t 具有 refinement type R。
*)
Inductive has_rtype : ty_context -> rcontext -> tm -> rty -> Prop :=
  | RT_Var : forall Delta RGamma x R,
      lookup_rcontext x RGamma = Some R ->
      wf_rty Delta RGamma R ->
      has_rtype Delta RGamma (tm_fvar x) R
  (* lambda x, body 具有函数 refinement type (x : R1) -> R2 的条件：
     1. R1 必须合法；
     2. 用新变量 x 同时打开函数体 body 和返回类型模板 R2 后，
     在加入 x : R1 的环境中，打开后的 body 必须具有打开后的 R2。 *)
  | RT_Abs : forall (L : list atom) Delta RGamma R1 body R2,
      wf_rty Delta RGamma R1 ->
      (forall x, ~ In x L ->
        has_rtype Delta (update_rcontext RGamma x R1)
          (open_tm body (tm_fvar x))
          (open_rty_tm R2 (tm_fvar x))) ->
      has_rtype Delta RGamma (tm_abs (erase R1) body) (R_Func R1 R2)
  | RT_App : forall Delta RGamma t1 t2 R1 R2,
      has_rtype Delta RGamma t1 (R_Func R1 R2) ->
      has_rtype Delta RGamma t2 R1 ->
      has_rtype Delta RGamma (tm_app t1 t2) (R_Exists R1 R2)
  | RT_TAbs : forall (L : list atom) Delta RGamma body R,
      (forall X, ~ In X L ->
        has_rtype (X :: Delta) RGamma
          (open_tm_ty body (Ty_FVar X))
          (open_rty_ty R (Ty_FVar X))) ->
      has_rtype Delta RGamma (tm_tabs body) (R_Poly R)
  | RT_TApp : forall Delta RGamma t R U,
      has_rtype Delta RGamma t (R_Poly R) ->
      wf_ty Delta U ->
      has_rtype Delta RGamma (tm_tapp t U) (open_rty_ty R U)
  | RT_Int : forall Delta RGamma (n : Z),
      has_rtype Delta RGamma (tm_int n)
        (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_int n)))
  | RT_Div : forall Delta RGamma t1 t2,
      has_rtype Delta RGamma t1 (R_Refine Ty_Int Pred_True) ->
      has_rtype Delta RGamma t2
        (R_Refine Ty_Int (Pred_Ne (tm_bvar 0) (tm_int 0%Z))) ->
      has_rtype Delta RGamma (tm_div t1 t2) (R_Refine Ty_Int Pred_True)
  | RT_Arith : forall Delta RGamma op t1 t2,
      has_rtype Delta RGamma t1 (R_Refine Ty_Int Pred_True) ->
      has_rtype Delta RGamma t2 (R_Refine Ty_Int Pred_True) ->
      has_rtype Delta RGamma (tm_arith op t1 t2)
        (R_Refine Ty_Int (Pred_Eq (tm_bvar 0) (tm_arith op t1 t2)))
  (* 值 v 属于 refinement type {u : T | ps}，只要 v : T，类型合法，
     并且把条件中的 u 替换成 v 后，得到封闭且成立的公式。 *)
  | RT_Choice : forall Delta RGamma t1 t2 R,
      has_rtype Delta RGamma t1 R ->
      has_rtype Delta RGamma t2 R ->
      has_rtype Delta RGamma (tm_choice t1 t2) R
  | RT_RefineValue : forall Delta RGamma v T ps,
      has_type Delta (erase_context RGamma) v T ->
      value v ->
      wf_rty Delta RGamma (R_Refine T ps) ->
      predicate_closed (open_qualifier_tm ps v) ->
      qualifier_holds (open_qualifier_tm ps v) ->
      has_rtype Delta RGamma v (R_Refine T ps)
  (* 显然 *)
  | RT_Sub : forall Delta RGamma t R S,
      has_rtype Delta RGamma t R ->
      wf_rty Delta RGamma S ->
      subtype Delta RGamma R S ->
      has_rtype Delta RGamma t S


(* subtype Delta RGamma R1 R2
  表示：
  refinement type R1 是 R2 的子类型。
  本质是：满足 R1 的程序一定也满足 R2。（也就是R1更严格）
  例如：
  {v : Int | v = 1}
  是下面类型的子类型：
  {v : Int | v > 0} *)
with subtype : ty_context -> rcontext -> rty -> rty -> Prop :=
  | S_Refl : forall Delta RGamma R,
      subtype Delta RGamma R R
  | S_Refine : forall (L : list atom) Delta RGamma T ps qs,
      (forall x, ~ In x L ->
        entails Delta
          (update_rcontext RGamma x (R_Refine T Pred_True))
          (open_qualifier_tm ps (tm_fvar x))
          (open_qualifier_tm qs (tm_fvar x))) ->
      subtype Delta RGamma (R_Refine T ps) (R_Refine T qs)
  | S_Func : forall (L : list atom) Delta RGamma R1 R2 S1 S2,
      subtype Delta RGamma S1 R1 ->
      (forall x, ~ In x L ->
        subtype Delta (update_rcontext RGamma x S1)
          (open_rty_tm R2 (tm_fvar x))
          (open_rty_tm S2 (tm_fvar x))) ->
      subtype Delta RGamma (R_Func R1 R2) (R_Func S1 S2)
  | S_Witness : forall Delta RGamma v R1 R2 S,
      value v ->
      has_rtype Delta RGamma v R1 ->
      subtype Delta RGamma S (open_rty_tm R2 v) ->
      subtype Delta RGamma S (R_Exists R1 R2)
  | S_Bind : forall (L : list atom) Delta RGamma R1 R2 S,
      (* R1 is added to the context in the premise, so it must be well formed. *)
      wf_rty Delta RGamma R1 ->
      locally_closed_rty S ->
      (forall x, ~ In x L ->
        subtype Delta (update_rcontext RGamma x R1)
          (open_rty_tm R2 (tm_fvar x)) S) ->
      subtype Delta RGamma (R_Exists R1 R2) S
  | S_Poly : forall (L : list atom) Delta RGamma R S,
      (forall X, ~ In X L ->
        subtype (X :: Delta) RGamma
          (open_rty_ty R (Ty_FVar X))
          (open_rty_ty S (Ty_FVar X))) ->
      subtype Delta RGamma (R_Poly R) (R_Poly S)
  | S_Trans : forall Delta RGamma R S U,
      subtype Delta RGamma R S ->
      subtype Delta RGamma S U ->
      subtype Delta RGamma R U.

Lemma erase_open_rty_tm_rec : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros; simpl; try rewrite IHR1; try rewrite IHR2;
    try rewrite IHR; reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof.
  intros. apply erase_open_rty_tm_rec.
Qed.

Lemma erase_open_rty_ty_rec : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof.
  intros. unfold open_rty_ty, open_ty. apply erase_open_rty_ty_rec.
Qed.

Lemma lookup_erase_context : forall RGamma x R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  induction RGamma as [|[y S] RGamma IH]; intros x R Hlookup; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. reflexivity.
    + apply IH. exact Hlookup.
Qed.

Fixpoint close_ty_rec (k : nat) (X : atom) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then Ty_BVar k else Ty_FVar Y
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (close_ty_rec k X T1) (close_ty_rec k X T2)
  | Ty_All T1 => Ty_All (close_ty_rec (S k) X T1)
  | Ty_Int => Ty_Int
  end.

Lemma close_open_ty_rec : forall T k X,
  ~ In X (fv_ty T) ->
  close_ty_rec k X (open_ty_rec k (Ty_FVar X) T) = T.
Proof.
  induction T; intros k X Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      change ((if Nat.eqb X X then Ty_BVar k else Ty_FVar X) = Ty_BVar k).
      rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by intuition.
    rewrite (proj2 (Nat.eqb_neq X a)) by assumption. reflexivity.
  - rewrite in_app_iff in Hfresh. rewrite IHT1, IHT2; intuition.
  - rewrite IHT by assumption. reflexivity.
  - reflexivity.
Qed.

Lemma open_ty_fresh_injective : forall T1 T2 X,
  ~ In X (fv_ty T1) ->
  ~ In X (fv_ty T2) ->
  open_ty T1 (Ty_FVar X) = open_ty T2 (Ty_FVar X) ->
  T1 = T2.
Proof.
  intros T1 T2 X H1 H2 E.
  apply (f_equal (close_ty_rec 0 X)) in E.
  unfold open_ty in E.
  rewrite (close_open_ty_rec T1 0 X H1) in E.
  rewrite (close_open_ty_rec T2 0 X H2) in E.
  exact E.
Qed.

Lemma subtype_erases : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  fix IH 5.
  intros Delta RGamma R S Hsub.
  destruct Hsub as
    [Delta RGamma R
    |L Delta RGamma T ps qs Hentails
    |L Delta RGamma R1 R2 S1 S2 Hdom Hcod
    |Delta RGamma v R1 R2 S Hv Htyped Hbody
    |L Delta RGamma R1 R2 S HR1 HS Hbody
    |L Delta RGamma R S Hbody
    |Delta RGamma R S U HRS HSU].
  - reflexivity.
  - reflexivity.
  - simpl. f_equal.
    + symmetry. exact (IH _ _ _ _ Hdom).
    + set (x := fresh L).
      assert (Hfresh : ~ In x L) by (subst x; apply fresh_notin).
      pose proof (IH _ _ _ _ (Hcod x Hfresh)) as E.
      rewrite !erase_open_rty_tm in E. exact E.
  - simpl. pose proof (IH _ _ _ _ Hbody) as E.
    rewrite erase_open_rty_tm in E. exact E.
  - simpl. set (x := fresh L).
    assert (Hfresh : ~ In x L) by (subst x; apply fresh_notin).
    pose proof (IH _ _ _ _ (Hbody x Hfresh)) as E.
    rewrite erase_open_rty_tm in E. exact E.
  - simpl. f_equal.
    set (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HX : ~ In X (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    { subst X. apply fresh_notin. }
    repeat rewrite in_app_iff in HX.
    assert (HXL : ~ In X L) by intuition.
    assert (HXR : ~ In X (fv_ty (erase R))) by intuition.
    assert (HXS : ~ In X (fv_ty (erase S))) by intuition.
    pose proof (IH _ _ _ _ (Hbody X HXL)) as E.
    rewrite !erase_open_rty_ty in E.
    eapply open_ty_fresh_injective; eauto.
  - etransitivity.
    + exact (IH _ _ _ _ HRS).
    + exact (IH _ _ _ _ HSU).
Qed.

Lemma wf_rty_erases : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  fix IH 4.
  intros Delta RGamma R Hwf.
  destruct Hwf as
    [L Delta RGamma T ps HT Hps
    |L Delta RGamma R1 R2 HR1 HR2
    |L Delta RGamma R1 R2 HR1 HR2
    |L Delta RGamma R HR].
  - exact HT.
  - simpl. apply WF_Arrow.
    + exact (IH _ _ _ HR1).
    + set (x := fresh L).
      rewrite <- (erase_open_rty_tm R2 (tm_fvar x)).
      apply IH with (RGamma := update_rcontext RGamma x R1).
      apply HR2. subst x. apply fresh_notin.
  - simpl. set (x := fresh L).
    rewrite <- (erase_open_rty_tm R2 (tm_fvar x)).
    apply IH with (RGamma := update_rcontext RGamma x R1).
    apply HR2. subst x. apply fresh_notin.
  - simpl. apply WF_All with L. intros X Hfresh.
    rewrite <- erase_open_rty_ty.
    apply IH with (RGamma := RGamma).
    apply HR. exact Hfresh.
Qed.

(* 显然 *)
Theorem refinement_typing_erases : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R Hty. induction Hty.
  - apply T_Var.
    + eapply lookup_erase_context. exact H.
    + exact (wf_rty_erases Delta RGamma R H0).
  - simpl. apply T_Abs with L.
    + exact (wf_rty_erases Delta RGamma R1 H).
    + intros x Hfresh. simpl.
      rewrite <- (erase_open_rty_tm R2 (tm_fvar x)).
      apply H1. exact Hfresh.
  - simpl. eapply T_App; eauto.
  - simpl. apply T_TAbs with L. intros X Hfresh.
    rewrite <- (erase_open_rty_ty R (Ty_FVar X)). apply H0. exact Hfresh.
  - rewrite (erase_open_rty_ty R U). eapply T_TApp; eauto.
  - apply T_Int.
  - simpl in *. apply T_Div; assumption.
  - simpl in *. apply T_Arith; assumption.
  - apply T_Choice; auto.
  - exact H.
  - match goal with
    | Hsub : subtype _ _ _ _ |- _ =>
        pose proof (subtype_erases _ _ _ _ Hsub) as E
    end.
    rewrite <- E. exact IHHty.
Qed.

End SystemFRefinementNonDeterminismTyping.
