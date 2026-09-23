From Stdlib Require Export Arith.PeanoNat Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.

(* 定义了一个新类型 label，它只有两个取值：Low 和 High。 *)
(* “高低”是保密级别 *)
Inductive label : Type := Low | High.

(* 高保密级别的信息不能流向低保密级别的变量或输出。 *)
Definition flows_to (l1 l2 : label) : Prop :=
  match l1, l2 with
  | High, Low => False
  | _, _ => True
  end.

(* 取两个保密级别中较高的那个，防止泄露秘密 *)
Definition join (l1 l2 : label) : label :=
  match l1, l2 with
  | Low, Low => Low
  | _, _ => High
  end.

Lemma flows_to_refl : forall l, flows_to l l.
Proof. destruct l; exact I. Qed.

Lemma flows_to_trans : forall l1 l2 l3,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof. destruct l1, l2, l3; simpl; tauto. Qed.

(* reader：谁能直接查看原始内容；indirect_reader：谁能通过计算结果间接得知信息。
   例如 reader = High、indirect_reader = Low：Low 不能看姓名列表，
   但可以通过查询结果知道某个名字是否在列表中。 *)
Record security : Type := {
  reader : label;
  indirect_reader : label
}.

(* wf_security kappa 表示安全标注 kappa 是合法的：能直接读取内容的人，
   也必须允许间接获知其信息。因此 indirect_reader 不能比 reader 更严格。 *)
Definition wf_security (kappa : security) : Prop :=
  flows_to kappa.(indirect_reader) kappa.(reader).

(* security_le kappa1 kappa2 表示：kappa1 的两个保密级别都不高于 kappa2。
    它分别检查 reader 和 indirect_reader。 *)
Definition security_le (kappa1 kappa2 : security) : Prop :=
  flows_to kappa1.(reader) kappa2.(reader) /\
  flows_to kappa1.(indirect_reader) kappa2.(indirect_reader).

Definition public : security :=
  {| reader := Low; indirect_reader := Low |}.

Definition secret : security :=
  {| reader := High; indirect_reader := High |}.
(* protect_security kappa l 表示：把安全标注 kappa 的两个级别都至少提高到 l，
    返回一个新的 security。 *)
Definition protect_security (kappa : security) (l : label) : security :=
  {| reader := join kappa.(reader) l;
     indirect_reader := join kappa.(indirect_reader) l |}.

Inductive ty : Type :=
  | Ty_Unit : security -> ty
  | Ty_Sum : ty -> ty -> security -> ty
  | Ty_Prod : ty -> ty -> security -> ty
  | Ty_Arrow : ty -> ty -> security -> ty
  | Ty_Nat : security -> ty.

(* security_of T：取出类型 T 最外层的安全标注。 *)
Definition security_of (T : ty) : security :=
  match T with
  | Ty_Unit kappa | Ty_Nat kappa => kappa
  | Ty_Sum _ _ kappa | Ty_Prod _ _ kappa | Ty_Arrow _ _ kappa => kappa
  end.

(* ty_protect l T 表示：把类型 T 最外层的安全标注提高到至少 l，得到一个新类型。 *)
Definition ty_protect (l : label) (T : ty) : ty :=
  match T with
  | Ty_Unit kappa => Ty_Unit (protect_security kappa l)
  | Ty_Nat kappa => Ty_Nat (protect_security kappa l)
  | Ty_Sum T1 T2 kappa => Ty_Sum T1 T2 (protect_security kappa l)
  | Ty_Prod T1 T2 kappa => Ty_Prod T1 T2 (protect_security kappa l)
  | Ty_Arrow T1 T2 kappa => Ty_Arrow T1 T2 (protect_security kappa l)
  end.

(* wf_ty T 表示：类型 T 里所有的安全标注都合法。这是在定义合法的ty *)
Fixpoint wf_ty (T : ty) : Prop :=
  match T with
  | Ty_Unit kappa | Ty_Nat kappa => wf_security kappa
  | Ty_Sum T1 T2 kappa | Ty_Prod T1 T2 kappa | Ty_Arrow T1 T2 kappa =>
      wf_ty T1 /\ wf_ty T2 /\ wf_security kappa
  end.

Definition atom := nat.

(* 看到这里了 *)
Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_unit : security -> tm
  (* tm_abs T body kappa 表示一个函数。kappa.(reader) 决定什么级别的代码
     可以调用它；调用后的结果至少受 kappa.(indirect_reader) 级别保护。
     例如 reader = High、indirect_reader = Low：Low 不能调用这个函数，
     但 High 调用后，原本为 Low 的结果仍可公开；原本为 High 的结果不会降级。 *)
  | tm_abs : ty -> tm -> security -> tm
  (*  tm_app f v r 里的 r : label 表示这次函数调用操作的安全级别。*)
  | tm_app : tm -> tm -> label -> tm
  | tm_pair : tm -> tm -> security -> tm
  (* tm_fst t r 表示：取二元组 t 的第一项，相当于 Lean 里的 t.1 *)
  | tm_fst : tm -> label -> tm
  | tm_snd : tm -> label -> tm
  | tm_inl : tm -> security -> tm
  | tm_inr : tm -> security -> tm
  (*  *)
  | tm_case : tm -> tm -> tm -> label -> tm
  (* tm_protect l t 表示：先运行 t，然后把得到的值至少标为 l 级别。 *)
  | tm_protect : label -> tm -> tm
  | tm_nat : nat -> security -> tm
  | tm_succ : tm -> label -> tm
  | tm_natrec : tm -> tm -> tm -> label -> tm
  | tm_if : tm -> tm -> tm -> label -> tm.

(* open_rec k u t 表示：在程序 t 中，找到编号为 k 的绑定变量，把它换成程序 u。 *)
Fixpoint open_rec (k : nat) (u t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_unit kappa => tm_unit kappa
  | tm_abs T body kappa => tm_abs T (open_rec (S k) u body) kappa
  | tm_app t1 t2 r => tm_app (open_rec k u t1) (open_rec k u t2) r
  | tm_pair t1 t2 kappa => tm_pair (open_rec k u t1) (open_rec k u t2) kappa
  | tm_fst t1 r => tm_fst (open_rec k u t1) r
  | tm_snd t1 r => tm_snd (open_rec k u t1) r
  | tm_inl t1 kappa => tm_inl (open_rec k u t1) kappa
  | tm_inr t1 kappa => tm_inr (open_rec k u t1) kappa
  | tm_case t0 body1 body2 r =>
      tm_case (open_rec k u t0)
        (open_rec (S k) u body1) (open_rec (S k) u body2) r
  | tm_protect l t1 => tm_protect l (open_rec k u t1)
  | tm_if c yes no r => tm_if (open_rec k u c) (open_rec k u yes) (open_rec k u no) r
  | tm_nat n s => tm_nat n s
  | tm_succ t r => tm_succ (open_rec k u t) r
  | tm_natrec n b s r => tm_natrec (open_rec k u n) (open_rec k u b) (open_rec k u s) r
  end.

Definition open (body u : tm) : tm := open_rec 0 u body.

(* subst x u t 表示：在程序 t 里，把自由变量 x 换成程序 u。 *)
Fixpoint subst (x : atom) (u t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then u else tm_fvar y
  | tm_unit kappa => tm_unit kappa
  | tm_abs T body kappa => tm_abs T (subst x u body) kappa
  | tm_app t1 t2 r => tm_app (subst x u t1) (subst x u t2) r
  | tm_pair t1 t2 kappa => tm_pair (subst x u t1) (subst x u t2) kappa
  | tm_fst t1 r => tm_fst (subst x u t1) r
  | tm_snd t1 r => tm_snd (subst x u t1) r
  | tm_inl t1 kappa => tm_inl (subst x u t1) kappa
  | tm_inr t1 kappa => tm_inr (subst x u t1) kappa
  | tm_case t0 body1 body2 r =>
      tm_case (subst x u t0) (subst x u body1) (subst x u body2) r
  | tm_protect l t1 => tm_protect l (subst x u t1)
  | tm_if c yes no r => tm_if (subst x u c) (subst x u yes) (subst x u no) r
  | tm_nat n s => tm_nat n s
  | tm_succ t r => tm_succ (subst x u t) r
  | tm_natrec n b s r => tm_natrec (subst x u n) (subst x u b) (subst x u s) r
  end.
(* fv t 会列出程序 t 中出现的自由变量名。 *)
Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_unit _ | tm_nat _ _ => []
  | tm_fvar x => [x]
  | tm_abs _ body _ => fv body
  | tm_app t1 t2 _ | tm_pair t1 t2 _ => fv t1 ++ fv t2
  | tm_fst t1 _ | tm_snd t1 _ | tm_inl t1 _ | tm_inr t1 _
  | tm_protect _ t1 | tm_succ t1 _ => fv t1
  | tm_natrec n b s _ => fv n ++ fv b ++ fv s
  | tm_case t0 body1 body2 _ | tm_if t0 body1 body2 _ => fv t0 ++ fv body1 ++ fv body2
  end.
(* lc_at k t 表示：把程序 t 放在 k 层变量绑定之内时，它的绑定变量编号都找得到对应的绑定位置。 *)
Fixpoint lc_at (k : nat) (t : tm) : Prop :=
  match t with
  | tm_bvar i => i < k
  | tm_fvar _ | tm_unit _ | tm_nat _ _ => True
  | tm_abs _ body _ => lc_at (S k) body
  | tm_app t1 t2 _ | tm_pair t1 t2 _ => lc_at k t1 /\ lc_at k t2
  | tm_fst t1 _ | tm_snd t1 _ | tm_inl t1 _ | tm_inr t1 _
  | tm_protect _ t1 | tm_succ t1 _ => lc_at k t1
  | tm_natrec n b s _ => lc_at k n /\ lc_at k b /\ lc_at k s
  | tm_case t0 body1 body2 _ =>
      lc_at k t0 /\ lc_at (S k) body1 /\ lc_at (S k) body2
  | tm_if c yes no _ => lc_at k c /\ lc_at k yes /\ lc_at k no
  end.

Definition locally_closed (t : tm) : Prop := lc_at 0 t.
(* closed t 表示 没有自由变量，也没有悬空的绑定变量。 *)
Definition closed (t : tm) : Prop := locally_closed t /\ fv t = [].

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  assert (forall (L : list atom) x,
    In x L -> x <= fold_right Nat.max 0 L) as Hbound.
  { intros L. induction L; simpl; intros x H.
    - contradiction.
    - destruct H as [-> | H].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [apply IHL; exact H | apply Nat.le_max_r]. }
  intros L. exists (S (fold_right Nat.max 0 L)).
  intros H. apply Hbound in H. lia.
Qed.

Lemma lc_at_open_inv : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; intros k u H; simpl in *; try tauto.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + simpl in H. lia.
  - eapply IHt; exact H.
  - destruct H. split; [eapply IHt1 | eapply IHt2]; eassumption.
  - destruct H. split; [eapply IHt1 | eapply IHt2]; eassumption.
  - eapply IHt; exact H.
  - eapply IHt; exact H.
  - eapply IHt; exact H.
  - eapply IHt; exact H.
  - destruct H as [H0 [H1 H2]]. repeat split;
      [eapply IHt1 | eapply IHt2 | eapply IHt3]; eassumption.
  - eapply IHt; exact H.
  - eapply IHt; exact H.
  - destruct H as [H0 [H1 H2]]. repeat split;
      [eapply IHt1 | eapply IHt2 | eapply IHt3]; eassumption.
  - destruct H as [H0 [H1 H2]]. repeat split;
      [eapply IHt1 | eapply IHt2 | eapply IHt3]; eassumption.
Qed.

Lemma open_rec_lc_at : forall t d k u,
  lc_at d t -> d <= k -> open_rec k u t = t.
Proof.
  induction t; intros d k u Hlc Hdk; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n) eqn:Heq; [apply Nat.eqb_eq in Heq; lia | reflexivity].
  - f_equal. eapply IHt; [exact Hlc | lia].
  - destruct Hlc. f_equal; [eapply IHt1 | eapply IHt2]; eassumption.
  - destruct Hlc. f_equal; [eapply IHt1 | eapply IHt2]; eassumption.
  - f_equal. eapply IHt; eassumption.
  - f_equal. eapply IHt; eassumption.
  - f_equal. eapply IHt; eassumption.
  - f_equal. eapply IHt; eassumption.
  - destruct Hlc as [H0 [H1 H2]]. f_equal.
    + eapply IHt1; eassumption.
    + eapply IHt2; [exact H1 | lia].
    + eapply IHt3; [exact H2 | lia].
  - f_equal. eapply IHt; eassumption.
  - f_equal. eapply IHt; eassumption.
  - destruct Hlc as [H0 [H1 H2]]. f_equal;
      [eapply IHt1 | eapply IHt2 | eapply IHt3]; eassumption.
  - destruct Hlc as [H0 [H1 H2]]. f_equal;
      [eapply IHt1 | eapply IHt2 | eapply IHt3]; eassumption.
Qed.

Lemma subst_open_rec : forall t x u k v,
  locally_closed u ->
  subst x u (open_rec k v t) = open_rec k (subst x u v) (subst x u t).
Proof.
  induction t; intros x u k v Hlc; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Nat.eqb x a); simpl; [symmetry; eapply open_rec_lc_at; [exact Hlc | lia] | reflexivity].
  - f_equal. apply IHt; exact Hlc.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hlc.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hlc.
  - f_equal. apply IHt; exact Hlc.
  - f_equal. apply IHt; exact Hlc.
  - f_equal. apply IHt; exact Hlc.
  - f_equal. apply IHt; exact Hlc.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; exact Hlc.
  - f_equal. apply IHt; exact Hlc.
  - f_equal. apply IHt; exact Hlc.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; exact Hlc.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; exact Hlc.
Qed.

Lemma subst_fresh : forall t x u,
  ~ In x (fv t) -> subst x u t = t.
Proof.
  induction t; intros x u Hfresh; simpl in *; try reflexivity.
  - destruct (Nat.eqb x a) eqn:Heq; [apply Nat.eqb_eq in Heq; subst; tauto | reflexivity].
  - f_equal. apply IHt; exact Hfresh.
  - rewrite in_app_iff in Hfresh. f_equal; [apply IHt1 | apply IHt2]; tauto.
  - rewrite in_app_iff in Hfresh. f_equal; [apply IHt1 | apply IHt2]; tauto.
  - f_equal. apply IHt; exact Hfresh.
  - f_equal. apply IHt; exact Hfresh.
  - f_equal. apply IHt; exact Hfresh.
  - f_equal. apply IHt; exact Hfresh.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; tauto.
  - f_equal. apply IHt; exact Hfresh.
  - f_equal. apply IHt; exact Hfresh.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; tauto.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; tauto.
Qed.

Lemma open_subst_intro : forall body x u,
  ~ In x (fv body) -> locally_closed u ->
  open body u = subst x u (open body (tm_fvar x)).
Proof.
  intros body x u Hfresh Hlc. unfold open.
  rewrite subst_open_rec by exact Hlc.
  rewrite (subst_fresh body x u Hfresh). simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Inductive value : tm -> Prop :=
  | v_unit : forall kappa, value (tm_unit kappa)
  | v_abs : forall T body kappa,
      locally_closed (tm_abs T body kappa) -> value (tm_abs T body kappa)
  | v_pair : forall v1 v2 kappa,
      value v1 -> value v2 -> value (tm_pair v1 v2 kappa)
  | v_inl : forall v kappa, value v -> value (tm_inl v kappa)
  | v_inr : forall v kappa, value v -> value (tm_inr v kappa)
  | v_nat : forall n kappa, value (tm_nat n kappa).

(* protect_value v l 表示：把值 v 最外层的安全级别提高到至少 l *)
Definition protect_value (v : tm) (l : label) : tm :=
  match v with
  | tm_unit kappa => tm_unit (protect_security kappa l)
  | tm_abs T body kappa => tm_abs T body (protect_security kappa l)
  | tm_pair v1 v2 kappa => tm_pair v1 v2 (protect_security kappa l)
  | tm_inl v1 kappa => tm_inl v1 (protect_security kappa l)
  | tm_inr v1 kappa => tm_inr v1 (protect_security kappa l)
  | tm_nat n kappa => tm_nat n (protect_security kappa l)
  | _ => v
  end.

(* context 是记录自由变量名及其类型的列表。 *)
Definition context := list (atom * ty).
Definition empty : context := [].

(* lookup_context x Gamma 表示：在环境 Gamma 中查找变量名 x 的类型。 *)
Fixpoint lookup_context (x : atom) (Gamma : context) : option ty :=
  match Gamma with
  | [] => None
  | (y, T) :: Gamma' =>
      if Nat.eqb x y then Some T else lookup_context x Gamma'
  end.

Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  (x, T) :: Gamma.

Definition context_wf (Gamma : context) : Prop :=
  forall (x : atom) (T : ty), lookup_context x Gamma = Some T -> wf_ty T.

(* erase_type T 表示：把类型 T 中所有层的安全标注统一换成 public *)
Fixpoint erase_type (T : ty) : ty :=
  match T with
  | Ty_Unit _ => Ty_Unit public
  | Ty_Nat _ => Ty_Nat public
  | Ty_Sum T1 T2 _ => Ty_Sum (erase_type T1) (erase_type T2) public
  | Ty_Prod T1 T2 _ => Ty_Prod (erase_type T1) (erase_type T2) public
  | Ty_Arrow T1 T2 _ => Ty_Arrow (erase_type T1) (erase_type T2) public
  end.

(* erase_security t 表示：去掉程序 t 中的安全限制信息。
具体是把 security 标注换成 public，把操作上的 label 换成 Low，并去掉 tm_protect。 *)
Fixpoint erase_security (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_unit _ => tm_unit public
  | tm_abs T body _ => tm_abs (erase_type T) (erase_security body) public
  | tm_app t1 t2 _ => tm_app (erase_security t1) (erase_security t2) Low
  | tm_pair t1 t2 _ => tm_pair (erase_security t1) (erase_security t2) public
  | tm_fst t1 _ => tm_fst (erase_security t1) Low
  | tm_snd t1 _ => tm_snd (erase_security t1) Low
  | tm_inl t1 _ => tm_inl (erase_security t1) public
  | tm_inr t1 _ => tm_inr (erase_security t1) public
  | tm_case t0 body1 body2 _ =>
      tm_case (erase_security t0) (erase_security body1) (erase_security body2) Low
  | tm_protect _ t1 => erase_security t1
  | tm_if c yes no _ => tm_if (erase_security c) (erase_security yes) (erase_security no) Low
  | tm_nat n _ => tm_nat n public
  | tm_succ t _ => tm_succ (erase_security t) Low
  | tm_natrec n b s _ => tm_natrec (erase_security n) (erase_security b) (erase_security s) Low
  end.


Fixpoint natrec_unroll (n : nat) (base step_function : tm) (r : label) : tm :=
  match n with
  | O => base
  | S k => tm_app (tm_app step_function (tm_nat k public) r)
                  (natrec_unroll k base step_function r) r
  end.
