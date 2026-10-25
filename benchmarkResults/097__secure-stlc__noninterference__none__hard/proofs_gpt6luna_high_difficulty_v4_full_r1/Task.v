From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Equality.
Import ListNotations.
Reserved Notation "t '-->' t'" (at level 40).

Inductive label : Type := Low | High.

Definition flows_to (l1 l2 : label) : Prop :=
  match l1, l2 with
  | High, Low => False
  | _, _ => True
  end.

Lemma no_flow_iff : forall l1 l2, ~ flows_to l1 l2 <-> l1 = High /\ l2 = Low.
Proof. destruct l1, l2; simpl; intuition congruence. Qed.

Lemma no_flow_labels : forall l1 l2, ~ flows_to l1 l2 -> l1 = High /\ l2 = Low.
Proof. intros; apply no_flow_iff; assumption. Qed.



Definition join (l1 l2 : label) : label :=
  match l1, l2 with
  | Low, Low => Low
  | _, _ => High
  end.

Record security : Type := {
  reader : label;
  indirect_reader : label
}.

Definition wf_security (kappa : security) : Prop :=
  flows_to kappa.(indirect_reader) kappa.(reader).

Definition security_le (kappa1 kappa2 : security) : Prop :=
  flows_to kappa1.(reader) kappa2.(reader) /\
  flows_to kappa1.(indirect_reader) kappa2.(indirect_reader).

Definition public : security :=
  {| reader := Low; indirect_reader := Low |}.

Definition secret : security :=
  {| reader := High; indirect_reader := High |}.

Definition protect_security (kappa : security) (l : label) : security :=
  {| reader := join kappa.(reader) l;
     indirect_reader := join kappa.(indirect_reader) l |}.

Inductive ty : Type :=
  | Ty_Unit : security -> ty
  | Ty_Sum : ty -> ty -> security -> ty
  | Ty_Prod : ty -> ty -> security -> ty
  | Ty_Arrow : ty -> ty -> security -> ty.

Definition security_of (T : ty) : security :=
  match T with
  | Ty_Unit kappa => kappa
  | Ty_Sum _ _ kappa | Ty_Prod _ _ kappa | Ty_Arrow _ _ kappa => kappa
  end.

Lemma secret_result_labels : forall T_secret T_result,
  ~ flows_to (security_of T_secret).(indirect_reader)
      (security_of T_result).(indirect_reader) ->
  (security_of T_secret).(indirect_reader) = High /\
  (security_of T_result).(indirect_reader) = Low.
Proof. intros; apply no_flow_labels; assumption. Qed.

Definition ty_protect (l : label) (T : ty) : ty :=
  match T with
  | Ty_Unit kappa => Ty_Unit (protect_security kappa l)
  | Ty_Sum T1 T2 kappa => Ty_Sum T1 T2 (protect_security kappa l)
  | Ty_Prod T1 T2 kappa => Ty_Prod T1 T2 (protect_security kappa l)
  | Ty_Arrow T1 T2 kappa => Ty_Arrow T1 T2 (protect_security kappa l)
  end.

Lemma protect_security_low : forall kappa,
  protect_security kappa Low = kappa.
Proof. destruct kappa as [r i]; destruct r, i; reflexivity. Qed.

Lemma ty_protect_high_indirect : forall T,
  (security_of (ty_protect High T)).(indirect_reader) = High.
Proof.
  destruct T; simpl; destruct s as [r i]; destruct r, i; reflexivity.
Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof. destruct T; simpl; rewrite protect_security_low; reflexivity. Qed.

Fixpoint wf_ty (T : ty) : Prop :=
  match T with
  | Ty_Unit kappa => wf_security kappa
  | Ty_Sum T1 T2 kappa | Ty_Prod T1 T2 kappa | Ty_Arrow T1 T2 kappa =>
      wf_ty T1 /\ wf_ty T2 /\ wf_security kappa
  end.

Definition atom := nat.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_unit : security -> tm
  | tm_abs : ty -> tm -> security -> tm
  | tm_app : tm -> tm -> label -> tm
  | tm_pair : tm -> tm -> security -> tm
  | tm_fst : tm -> label -> tm
  | tm_snd : tm -> label -> tm
  | tm_inl : tm -> security -> tm
  | tm_inr : tm -> security -> tm
  | tm_case : tm -> tm -> tm -> label -> tm
  | tm_protect : label -> tm -> tm.

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
  end.

Definition open (body u : tm) : tm := open_rec 0 u body.

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
  end.

Fixpoint subst_env (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit kappa => tm_unit kappa
  | tm_abs T body kappa => tm_abs T (subst_env rho body) kappa
  | tm_app t1 t2 r => tm_app (subst_env rho t1) (subst_env rho t2) r
  | tm_pair t1 t2 kappa => tm_pair (subst_env rho t1) (subst_env rho t2) kappa
  | tm_fst t1 r => tm_fst (subst_env rho t1) r
  | tm_snd t1 r => tm_snd (subst_env rho t1) r
  | tm_inl t1 kappa => tm_inl (subst_env rho t1) kappa
  | tm_inr t1 kappa => tm_inr (subst_env rho t1) kappa
  | tm_case t0 body1 body2 r =>
      tm_case (subst_env rho t0) (subst_env rho body1) (subst_env rho body2) r
  | tm_protect l t1 => tm_protect l (subst_env rho t1)
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_unit _ => []
  | tm_fvar x => [x]
  | tm_abs _ body _ => fv body
  | tm_app t1 t2 _ | tm_pair t1 t2 _ => fv t1 ++ fv t2
  | tm_fst t1 _ | tm_snd t1 _ | tm_inl t1 _ | tm_inr t1 _
  | tm_protect _ t1 => fv t1
  | tm_case t0 body1 body2 _ => fv t0 ++ fv body1 ++ fv body2
  end.

Fixpoint lc_at (k : nat) (t : tm) : Prop :=
  match t with
  | tm_bvar i => i < k
  | tm_fvar _ | tm_unit _ => True
  | tm_abs _ body _ => lc_at (S k) body
  | tm_app t1 t2 _ | tm_pair t1 t2 _ => lc_at k t1 /\ lc_at k t2
  | tm_fst t1 _ | tm_snd t1 _ | tm_inl t1 _ | tm_inr t1 _
  | tm_protect _ t1 => lc_at k t1
  | tm_case t0 body1 body2 _ =>
      lc_at k t0 /\ lc_at (S k) body1 /\ lc_at (S k) body2
  end.

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

Lemma lc_at_mono : forall t k m, k <= m -> lc_at k t -> lc_at m t.
Proof.
  fix IH 1. intros t k m Hkm Hlc. destruct t; simpl in *.
  - lia.
  - exact I.
  - exact I.
  - eapply (IH t0 (S k) (S m)); [lia|exact Hlc].
  - destruct Hlc as [H1 H2]. split.
    + eapply (IH t1 k m); eauto.
    + eapply (IH t2 k m); eauto.
  - destruct Hlc as [H1 H2]. split.
    + eapply (IH t1 k m); eauto.
    + eapply (IH t2 k m); eauto.
  - eapply (IH t k m); eauto.
  - eapply (IH t k m); eauto.
  - eapply (IH t k m); eauto.
  - eapply (IH t k m); eauto.
  - destruct Hlc as [H0 [H1 H2]]. repeat split.
    + eapply (IH t1 k m); eauto.
    + eapply (IH t2 (S k) (S m)); [lia|exact H1].
    + eapply (IH t3 (S k) (S m)); [lia|exact H2].
  - eapply (IH t k m); eauto.
Qed.

Lemma open_rec_lc : forall t k u, lc_at k t -> open_rec k u t = t.
Proof.
  fix IH 1. intros t k u Hlc. destruct t; simpl in *.
  - destruct (k =? n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. eapply (IH t0 (S k) u); exact Hlc.
  - destruct Hlc as [H1 H2]. f_equal.
    + eapply (IH t1 k u); exact H1.
    + eapply (IH t2 k u); exact H2.
  - destruct Hlc as [H1 H2]. f_equal.
    + eapply (IH t1 k u); exact H1.
    + eapply (IH t2 k u); exact H2.
  - f_equal. eapply (IH t k u); exact Hlc.
  - f_equal. eapply (IH t k u); exact Hlc.
  - f_equal. eapply (IH t k u); exact Hlc.
  - f_equal. eapply (IH t k u); exact Hlc.
  - destruct Hlc as [H0 [H1 H2]]. f_equal.
    + eapply (IH t1 k u); exact H0.
    + eapply (IH t2 (S k) u); exact H1.
    + eapply (IH t3 (S k) u); exact H2.
  - f_equal. eapply (IH t k u); exact Hlc.
Qed.

Lemma subst_env_open_rec : forall rho t k u,
  (forall x, locally_closed (rho x)) ->
  subst_env rho (open_rec k u t) =
  open_rec k (subst_env rho u) (subst_env rho t).
Proof.
  intros rho t k u Hrho. revert k u Hrho.
  induction t; intros k u Hrho; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_lc.
    exact (lc_at_mono (rho a) 0 k (Nat.le_0_l k) (Hrho a)).
  - reflexivity.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
  - rewrite IHt; auto.
Qed.

Lemma subst_env_open : forall rho body u,
  (forall x, locally_closed (rho x)) ->
  subst_env rho (open body u) = open (subst_env rho body) (subst_env rho u).
Proof. intros; unfold open; apply subst_env_open_rec; assumption. Qed.

Lemma lc_open_rec_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  fix IH 1. intros t k x Hlc. destruct t; simpl in *.
  - destruct (k =? n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + apply Nat.eqb_neq in Heq. change (n < k) in Hlc. lia.
  - exact I.
  - exact I.
  - eapply (IH t0 (S k) x); exact Hlc.
  - destruct Hlc as [H1 H2]. split.
    + eapply (IH t1 k x); exact H1.
    + eapply (IH t2 k x); exact H2.
  - destruct Hlc as [H1 H2]. split.
    + eapply (IH t1 k x); exact H1.
    + eapply (IH t2 k x); exact H2.
  - eapply (IH t k x); exact Hlc.
  - eapply (IH t k x); exact Hlc.
  - eapply (IH t k x); exact Hlc.
  - eapply (IH t k x); exact Hlc.
  - destruct Hlc as [H0 [H1 H2]]. repeat split.
    + eapply (IH t1 k x); exact H0.
    + eapply (IH t2 (S k) x); exact H1.
    + eapply (IH t3 (S k) x); exact H2.
  - eapply (IH t k x); exact Hlc.
Qed.

Lemma lc_subst_env : forall t k rho,
  lc_at k t -> (forall x, locally_closed (rho x)) ->
  lc_at k (subst_env rho t).
Proof.
  fix IH 1. intros t k rho Hlc Hrho. destruct t; simpl in *.
  - exact Hlc.
  - eapply (lc_at_mono (rho a) 0 k); [lia|apply Hrho].
  - exact I.
  - eapply (IH t0 (S k) rho); eauto.
  - destruct Hlc as [H1 H2]. split; eauto.
  - destruct Hlc as [H1 H2]. split; eauto.
  - eapply (IH t k rho); eauto.
  - eapply (IH t k rho); eauto.
  - eapply (IH t k rho); eauto.
  - eapply (IH t k rho); eauto.
  - destruct Hlc as [H0 [H1 H2]]. repeat split; eauto.
  - eapply (IH t k rho); eauto.
Qed.

Definition closed (t : tm) : Prop := locally_closed t /\ fv t = [].

Inductive value : tm -> Prop :=
  | v_unit : forall kappa, value (tm_unit kappa)
  | v_abs : forall T body kappa,
      locally_closed (tm_abs T body kappa) -> value (tm_abs T body kappa)
  | v_pair : forall v1 v2 kappa,
      value v1 -> value v2 -> value (tm_pair v1 v2 kappa)
  | v_inl : forall v kappa, value v -> value (tm_inl v kappa)
  | v_inr : forall v kappa, value v -> value (tm_inr v kappa).

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv; simpl; try exact I.
  - exact H.
  - split; assumption.
  - exact IHHv.
  - exact IHHv.
Qed.

Definition protect_value (v : tm) (l : label) : tm :=
  match v with
  | tm_unit kappa => tm_unit (protect_security kappa l)
  | tm_abs T body kappa => tm_abs T body (protect_security kappa l)
  | tm_pair v1 v2 kappa => tm_pair v1 v2 (protect_security kappa l)
  | tm_inl v1 kappa => tm_inl v1 (protect_security kappa l)
  | tm_inr v1 kappa => tm_inr v1 (protect_security kappa l)
  | _ => v
  end.

Definition context := list (atom * ty).

Definition empty : context := [].

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

Fixpoint erase_type (T : ty) : ty :=
  match T with
  | Ty_Unit _ => Ty_Unit public
  | Ty_Sum T1 T2 _ => Ty_Sum (erase_type T1) (erase_type T2) public
  | Ty_Prod T1 T2 _ => Ty_Prod (erase_type T1) (erase_type T2) public
  | Ty_Arrow T1 T2 _ => Ty_Arrow (erase_type T1) (erase_type T2) public
  end.

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
  end.

Lemma erase_open_rec : forall t k u,
  erase_security (open_rec k u t) = open_rec k (erase_security u) (erase_security t).
Proof.
  induction t; intros k u; simpl; try reflexivity.
  - destruct (k =? n); reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt. reflexivity.
Qed.

Lemma erase_open : forall body u,
  erase_security (open body u) = open (erase_security body) (erase_security u).
Proof. intros; unfold open; apply erase_open_rec. Qed.

Lemma erase_subst : forall x u t,
  erase_security (subst x u t) = subst x (erase_security u) (erase_security t).
Proof.
  intros x u t. induction t; simpl; try reflexivity.
  - destruct (x =? a); reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt. reflexivity.
Qed.

Lemma erase_protect_value : forall v l,
  erase_security (protect_value v l) = erase_security v.
Proof.
  intros v l. destruct v; reflexivity.
Qed.

Lemma erase_protect : forall l t, erase_security (tm_protect l t) = erase_security t.
Proof. reflexivity. Qed.

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T body kappa v r,
      value (tm_abs T body kappa) -> value v ->
      flows_to kappa.(reader) r ->
      tm_app (tm_abs T body kappa) v r -->
        tm_protect kappa.(indirect_reader) (open body v)
  | ST_App1 : forall t1 t1' t2 r,
      t1 --> t1' -> tm_app t1 t2 r --> tm_app t1' t2 r
  | ST_App2 : forall v1 t2 t2' r,
      value v1 -> t2 --> t2' -> tm_app v1 t2 r --> tm_app v1 t2' r
  | ST_Pair1 : forall t1 t1' t2 kappa,
      t1 --> t1' -> tm_pair t1 t2 kappa --> tm_pair t1' t2 kappa
  | ST_Pair2 : forall v1 t2 t2' kappa,
      value v1 -> t2 --> t2' -> tm_pair v1 t2 kappa --> tm_pair v1 t2' kappa
  | ST_FstPair : forall v1 v2 kappa r,
      value v1 -> value v2 -> flows_to kappa.(reader) r ->
      tm_fst (tm_pair v1 v2 kappa) r --> tm_protect kappa.(indirect_reader) v1
  | ST_Fst : forall t t' r,
      t --> t' -> tm_fst t r --> tm_fst t' r
  | ST_SndPair : forall v1 v2 kappa r,
      value v1 -> value v2 -> flows_to kappa.(reader) r ->
      tm_snd (tm_pair v1 v2 kappa) r --> tm_protect kappa.(indirect_reader) v2
  | ST_Snd : forall t t' r,
      t --> t' -> tm_snd t r --> tm_snd t' r
  | ST_Inl : forall t t' kappa,
      t --> t' -> tm_inl t kappa --> tm_inl t' kappa
  | ST_Inr : forall t t' kappa,
      t --> t' -> tm_inr t kappa --> tm_inr t' kappa
  | ST_CaseLeft : forall v kappa body1 body2 r,
      value v -> flows_to kappa.(reader) r ->
      tm_case (tm_inl v kappa) body1 body2 r -->
        tm_protect kappa.(indirect_reader) (open body1 v)
  | ST_CaseRight : forall v kappa body1 body2 r,
      value v -> flows_to kappa.(reader) r ->
      tm_case (tm_inr v kappa) body1 body2 r -->
        tm_protect kappa.(indirect_reader) (open body2 v)
  | ST_Case : forall t t' body1 body2 r,
      t --> t' -> tm_case t body1 body2 r --> tm_case t' body1 body2 r
  | ST_ProtectValue : forall l v,
      value v -> tm_protect l v --> protect_value v l
  | ST_Protect : forall l t t',
      t --> t' -> tm_protect l t --> tm_protect l t'
where "t '-->' t'" := (step t t').

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      step t1 t2 -> multi t2 t3 -> multi t1 t3.

Notation "t '-->*' t'" := (multi t t') (at level 40).

Definition evaluates (t v : tm) : Prop := t -->* v /\ value v.

Lemma value_no_step : forall v t, value v -> ~ step v t.
Proof.
  intros v t Hv. revert t. induction Hv; intros t Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    + exact (IHHv1 t1' H3).
    + exact (IHHv2 t2' H4).
  - inversion Hstep; subst. eapply IHHv; eassumption.
  - inversion Hstep; subst. eapply IHHv; eassumption.
Qed.

Lemma multi_value_id : forall v w, value v -> multi v w -> v = w.
Proof.
  intros v w Hv Hmulti. induction Hmulti; [reflexivity|].
  exfalso. eapply value_no_step; eassumption.
Qed.

Lemma evaluates_value_id : forall v w, value v -> evaluates v w -> v = w.
Proof. intros v w Hv [Hm _]. eapply multi_value_id; eassumption. Qed.

Lemma protect_value_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv. inversion Hv; subst; destruct l; simpl; try constructor; eauto.
Qed.

Lemma protect_value_low_id : forall v, value v -> protect_value v Low = v.
Proof.
  intros v Hv. inversion Hv; subst; simpl; rewrite protect_security_low; reflexivity.
Qed.

Lemma multi_trans : forall t1 t2 t3,
  multi t1 t2 -> multi t2 t3 -> multi t1 t3.
Proof.
  intros t1 t2 t3 H12 H23. induction H12; eauto using multi.
Qed.

Lemma multi_protect : forall l t v,
  multi t v -> multi (tm_protect l t) (tm_protect l v).
Proof.
  intros l t v H. induction H; eauto using multi, step.
Qed.

Lemma evaluates_protect_intro : forall l t v,
  evaluates t v -> evaluates (tm_protect l t) (protect_value v l).
Proof.
  intros l t v [Hm Hv]. split.
  eapply multi_trans.
  - apply multi_protect. exact Hm.
  - econstructor; [apply ST_ProtectValue; exact Hv|constructor].
  - apply protect_value_value. exact Hv.
Qed.

Lemma evaluates_protect_inv : forall l t w,
  evaluates (tm_protect l t) w ->
  exists v, evaluates t v /\ w = protect_value v l.
Proof.
  intros l t w [Hm Hw].
  remember (tm_protect l t) as src eqn:Esrc in Hm.
  revert t Esrc.
  dependent induction Hm.
  - intros u Esource. inversion Esource; subst. inversion Hw.
  - intros u Esource. inversion Esource; subst. inversion H; subst.
    + exists u. split.
      * split; [constructor|exact H4].
      * pose proof (multi_value_id (protect_value u l) t3
          (protect_value_value u l H4) Hm) as E. symmetry. exact E.
    + destruct (IHHm Hw t' eq_refl) as [v [Hv E]].
      exists v. split.
      * destruct Hv as [Hvt Hvv]. split; [econstructor; eassumption|exact Hvv].
      * exact E.
Qed.

Lemma eval_abs_app_inv : forall T body k a r w,
  value (tm_abs T body k) -> evaluates (tm_app (tm_abs T body k) a r) w ->
  exists av, evaluates a av /\ value av /\
    evaluates (tm_protect (indirect_reader k) (open body av)) w.
Proof.
  intros T body k a r w Hfun [Hm Hw].
  remember (tm_app (tm_abs T body k) a r) as src eqn:Esrc in Hm.
  revert a Esrc. dependent induction Hm.
  - intros a Esrc. inversion Esrc; subst. inversion Hw.
  - intros a Esrc. inversion Esrc; subst. inversion H; subst.
    + exists a. split.
      * split; [constructor|assumption].
      * split; [exact H8|]. split; [exact Hm|exact Hw].
    + exfalso. exact (value_no_step _ _ Hfun H5).
    + destruct (IHHm Hw t2' eq_refl) as [av [Hav [Hva Hbody]]].
      exists av. split.
      * destruct Hav as [Hmav Hvav]. split; [econstructor; eassumption|exact Hvav].
      * split; assumption.
Qed.

Lemma eval_pair_inv : forall t1 t2 k v,
  evaluates (tm_pair t1 t2 k) v ->
  exists a b, evaluates t1 a /\ evaluates t2 b /\
    value a /\ value b /\ v = tm_pair a b k.
Proof.
  intros t1 t2 k v [Hm Hv].
  remember (tm_pair t1 t2 k) as src eqn:Esrc in Hm.
  revert t1 t2 k Esrc.
  dependent induction Hm.
  - intros u1 u2 kk Esrc. inversion Esrc; subst. inversion Hv; subst.
    eexists; eexists. repeat split; eauto using multi_refl.
  - intros u1 u2 kk Esrc. inversion Esrc; subst. inversion H; subst.
    + destruct (IHHm Hv t1' u2 kk eq_refl)
        as [a [b [Ha [Hb [Hva [Hvb E]]]]]].
      exists a, b. split.
      * destruct Ha as [Hma Hva']. split; [econstructor; eassumption|exact Hva'].
      * split; [exact Hb|]. split; [exact Hva|]. split; assumption.
    + destruct (IHHm Hv u1 t2' kk eq_refl)
        as [a [b [Ha [Hb [Hva [Hvb E]]]]]].
      exists a, b. split; [exact Ha|]. split.
      * destruct Hb as [Hmb Hvb']. split; [econstructor; eassumption|exact Hvb'].
      * split; [exact Hva|]. split; assumption.
Qed.

Lemma eval_inl_inv : forall t k w,
  evaluates (tm_inl t k) w ->
  exists a, evaluates t a /\ value a /\ w = tm_inl a k.
Proof.
  intros t k w [Hm Hw]. remember (tm_inl t k) as src eqn:Esrc in Hm.
  revert t Esrc. dependent induction Hm.
  - intros u Esrc. inversion Esrc; subst. inversion Hw; subst.
    exists u. split; [split; [constructor|exact H1]|].
    split; [exact H1|reflexivity].
  - intros u Esrc. inversion Esrc; subst. inversion H; subst.
    destruct (IHHm Hw t' eq_refl) as [a [Ha [Hva E]]].
    exists a. split.
    + destruct Ha as [Hma Hval]. split; [econstructor; eassumption|exact Hval].
    + split; assumption.
Qed.

Lemma eval_inr_inv : forall t k w,
  evaluates (tm_inr t k) w ->
  exists a, evaluates t a /\ value a /\ w = tm_inr a k.
Proof.
  intros t k w [Hm Hw]. remember (tm_inr t k) as src eqn:Esrc in Hm.
  revert t Esrc. dependent induction Hm.
  - intros u Esrc. inversion Esrc; subst. inversion Hw; subst.
    exists u. split; [split; [constructor|exact H1]|].
    split; [exact H1|reflexivity].
  - intros u Esrc. inversion Esrc; subst. inversion H; subst.
    destruct (IHHm Hw t' eq_refl) as [a [Ha [Hva E]]].
    exists a. split.
    + destruct Ha as [Hma Hval]. split; [econstructor; eassumption|exact Hval].
    + split; assumption.
Qed.

Lemma eval_app_decomp : forall t1 t2 r w,
  evaluates (tm_app t1 t2 r) w ->
  exists f a, evaluates t1 f /\ evaluates t2 a /\ value f /\ value a /\
    evaluates (tm_app f a r) w.
Proof.
  intros t1 t2 r w [Hm Hw].
  remember (tm_app t1 t2 r) as src eqn:Esrc in Hm.
  revert t1 t2 Esrc. dependent induction Hm.
  - intros u1 u2 Esrc. inversion Esrc; subst. inversion Hw.
  - intros u1 u2 Esrc. inversion Esrc; subst. inversion H; subst.
    + exists (tm_abs T body kappa), u2. split.
      * split; [constructor|exact H4].
      * split.
        -- split; [constructor|exact H6].
        -- split; [exact H4|].
           split; [exact H6|]. split; [econstructor; eassumption|exact Hw].
    + destruct (IHHm Hw t1' u2 eq_refl) as [f [a [Hf [Ha [Hfv [Hav Happ]]]]]].
      exists f,a. split.
      * destruct Hf as [Hmf Hvf]. split; [econstructor; eassumption|exact Hvf].
      * split; [exact Ha|]. split; [exact Hfv|]. split; assumption.
    + destruct (IHHm Hw u1 t2' eq_refl) as [f [a [Hf [Ha [Hfv [Hav Happ]]]]]].
      pose proof (evaluates_value_id u1 f H5 Hf) as Ef. subst f.
      exists u1,a. split; [split; [constructor|exact H5]|].
      split.
      * destruct Ha as [Hma Hva]. split; [econstructor; eassumption|exact Hva].
      * split; [exact H5|]. split; [exact Hav|exact Happ].
Qed.

Lemma eval_fst_inv : forall t r w,
  evaluates (tm_fst t r) w ->
  exists a b k, evaluates t (tm_pair a b k) /\ value a /\ value b /\
    flows_to (reader k) r /\ evaluates (tm_protect (indirect_reader k) a) w.
Proof.
  intros t r w [Hm Hw]. remember (tm_fst t r) as src eqn:Esrc in Hm.
  revert t Esrc. dependent induction Hm.
  - intros u Esrc. inversion Esrc; subst. inversion Hw.
  - intros u Esrc. inversion Esrc; subst. inversion H; subst.
    + exists v1, v2, kappa. split.
      * split; [constructor|constructor; assumption].
      * split; [exact H3|]. split; [exact H4|]. split; [exact H6|].
        split; [exact Hm|exact Hw].
    + destruct (IHHm Hw t' eq_refl) as [a [b [k [Et [Ha [Hb [Hflow Ewrap]]]]]]].
      exists a,b,k. split.
      * destruct Et as [Hmt Hpair]. split; [econstructor; eassumption|exact Hpair].
      * split; [exact Ha|]. split; [exact Hb|]. split; [exact Hflow|exact Ewrap].
Qed.

Lemma eval_snd_inv : forall t r w,
  evaluates (tm_snd t r) w ->
  exists a b k, evaluates t (tm_pair a b k) /\ value a /\ value b /\
    flows_to (reader k) r /\ evaluates (tm_protect (indirect_reader k) b) w.
Proof.
  intros t r w [Hm Hw]. remember (tm_snd t r) as src eqn:Esrc in Hm.
  revert t Esrc. dependent induction Hm.
  - intros u Esrc. inversion Esrc; subst. inversion Hw.
  - intros u Esrc. inversion Esrc; subst. inversion H; subst.
    + exists v1, v2, kappa. split.
      * split; [constructor|constructor; assumption].
      * split; [exact H3|]. split; [exact H4|]. split; [exact H6|].
        split; [exact Hm|exact Hw].
    + destruct (IHHm Hw t' eq_refl) as [a [b [k [Et [Ha [Hb [Hflow Ewrap]]]]]]].
      exists a,b,k. split.
      * destruct Et as [Hmt Hpair]. split; [econstructor; eassumption|exact Hpair].
      * split; [exact Ha|]. split; [exact Hb|]. split; [exact Hflow|exact Ewrap].
Qed.

Lemma eval_case_inv : forall t body1 body2 r w,
  evaluates (tm_case t body1 body2 r) w ->
  (exists a k, evaluates t (tm_inl a k) /\ value a /\
      flows_to (reader k) r /\
      evaluates (tm_protect (indirect_reader k) (open body1 a)) w) \/
  (exists a k, evaluates t (tm_inr a k) /\ value a /\
      flows_to (reader k) r /\
      evaluates (tm_protect (indirect_reader k) (open body2 a)) w).
Proof.
  intros t body1 body2 r w [Hm Hw].
  remember (tm_case t body1 body2 r) as src eqn:Esrc in Hm.
  revert t Esrc. dependent induction Hm.
  - intros u Esrc. inversion Esrc; subst. inversion Hw.
  - intros u Esrc. inversion Esrc; subst. inversion H; subst.
    + left. exists v, kappa. split.
      * split; [constructor|constructor; assumption].
      * split; [assumption|]. split; [assumption|].
        split; [exact Hm|assumption].
    + right. exists v, kappa. split.
      * split; [constructor|constructor; assumption].
      * split; [assumption|]. split; [assumption|].
        split; [exact Hm|assumption].
    + destruct (IHHm Hw t' eq_refl) as [Hl|Hr].
      * left. destruct Hl as [a [k [Et [Va [Fl Ebr]]]]]. exists a,k.
        split. { destruct Et as [Met Vt]. split; [econstructor; eassumption|exact Vt]. }
        split; [exact Va|]. split; [exact Fl|exact Ebr].
      * right. destruct Hr as [a [k [Et [Va [Fl Ebr]]]]]. exists a,k.
        split. { destruct Et as [Met Vt]. split; [econstructor; eassumption|exact Vt]. }
        split; [exact Va|]. split; [exact Fl|exact Ebr].
Qed.


Inductive subtype : ty -> ty -> Prop :=
  | S_Unit : forall kappa1 kappa2,
      wf_security kappa1 -> wf_security kappa2 -> security_le kappa1 kappa2 ->
      subtype (Ty_Unit kappa1) (Ty_Unit kappa2)
  | S_Sum : forall T1 T2 U1 U2 kappa1 kappa2,
      subtype T1 U1 -> subtype T2 U2 ->
      wf_security kappa1 -> wf_security kappa2 -> security_le kappa1 kappa2 ->
      subtype (Ty_Sum T1 T2 kappa1) (Ty_Sum U1 U2 kappa2)
  | S_Prod : forall T1 T2 U1 U2 kappa1 kappa2,
      subtype T1 U1 -> subtype T2 U2 ->
      wf_security kappa1 -> wf_security kappa2 -> security_le kappa1 kappa2 ->
      subtype (Ty_Prod T1 T2 kappa1) (Ty_Prod U1 U2 kappa2)
  | S_Arrow : forall T1 T2 U1 U2 kappa1 kappa2,
      subtype U1 T1 -> subtype T2 U2 ->
      wf_security kappa1 -> wf_security kappa2 -> security_le kappa1 kappa2 ->
      subtype (Ty_Arrow T1 T2 kappa1) (Ty_Arrow U1 U2 kappa2)
  | S_Trans : forall T U V, subtype T U -> subtype U V -> subtype T V.

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      lookup_context x Gamma = Some T -> wf_ty T ->
      has_type Gamma (tm_fvar x) T
  | T_Unit : forall Gamma kappa,
      wf_security kappa -> has_type Gamma (tm_unit kappa) (Ty_Unit kappa)
  | T_Abs : forall (L : list atom) Gamma T1 body T2 kappa,
      wf_ty T1 -> wf_security kappa ->
      (forall x : atom, ~ In x L ->
        has_type (update Gamma x T1) (open body (tm_fvar x)) T2) ->
      has_type Gamma (tm_abs T1 body kappa) (Ty_Arrow T1 T2 kappa)
  | T_App : forall Gamma t1 t2 T1 T2 kappa r,
      has_type Gamma t1 (Ty_Arrow T1 T2 kappa) ->
      has_type Gamma t2 T1 -> flows_to kappa.(reader) r ->
      has_type Gamma (tm_app t1 t2 r) (ty_protect kappa.(indirect_reader) T2)
  | T_Pair : forall Gamma t1 t2 T1 T2 kappa,
      has_type Gamma t1 T1 -> has_type Gamma t2 T2 -> wf_security kappa ->
      has_type Gamma (tm_pair t1 t2 kappa) (Ty_Prod T1 T2 kappa)
  | T_Fst : forall Gamma t T1 T2 kappa r,
      has_type Gamma t (Ty_Prod T1 T2 kappa) -> flows_to kappa.(reader) r ->
      has_type Gamma (tm_fst t r) (ty_protect kappa.(indirect_reader) T1)
  | T_Snd : forall Gamma t T1 T2 kappa r,
      has_type Gamma t (Ty_Prod T1 T2 kappa) -> flows_to kappa.(reader) r ->
      has_type Gamma (tm_snd t r) (ty_protect kappa.(indirect_reader) T2)
  | T_Inl : forall Gamma t T1 T2 kappa,
      has_type Gamma t T1 -> wf_ty T2 -> wf_security kappa ->
      has_type Gamma (tm_inl t kappa) (Ty_Sum T1 T2 kappa)
  | T_Inr : forall Gamma t T1 T2 kappa,
      wf_ty T1 -> has_type Gamma t T2 -> wf_security kappa ->
      has_type Gamma (tm_inr t kappa) (Ty_Sum T1 T2 kappa)
  | T_Case : forall (L : list atom) Gamma t body1 body2 T1 T2 T kappa r,
      has_type Gamma t (Ty_Sum T1 T2 kappa) -> flows_to kappa.(reader) r ->
      (forall x : atom, ~ In x L ->
        has_type (update Gamma x T1) (open body1 (tm_fvar x)) T) ->
      (forall x : atom, ~ In x L ->
        has_type (update Gamma x T2) (open body2 (tm_fvar x)) T) ->
      has_type Gamma (tm_case t body1 body2 r)
        (ty_protect kappa.(indirect_reader) T)
  | T_Protect : forall Gamma t T l,
      has_type Gamma t T -> has_type Gamma (tm_protect l t) (ty_protect l T)
  | T_Sub : forall Gamma t T U,
      has_type Gamma t T -> subtype T U -> has_type Gamma t U.

Fixpoint max_atom_list (xs : list atom) : atom :=
  match xs with
  | [] => 0
  | x :: xs' => Nat.max x (max_atom_list xs')
  end.

Definition fresh_atom (xs : list atom) : atom := S (max_atom_list xs).

Lemma in_le_max_atom_list : forall xs x, In x xs -> x <= max_atom_list xs.
Proof.
  induction xs as [|a xs IH]; simpl; intros x Hin; [contradiction|].
  destruct Hin as [<-|Hin]; [apply Nat.le_max_l|].
  eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma fresh_atom_notin : forall xs, ~ In (fresh_atom xs) xs.
Proof.
  intros xs Hin. unfold fresh_atom in Hin.
  pose proof (in_le_max_atom_list xs (S (max_atom_list xs)) Hin). lia.
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty; simpl; try exact I; try tauto.
  - pose (x := fresh_atom L). assert (Hx : ~ In x L).
    { subst x. apply fresh_atom_notin. }
    specialize (H2 x Hx).
    apply lc_open_rec_inv with (k := 0) (x := x).
    exact H2.
  - split; assumption.
  - split; assumption.
  - simpl. split; [exact IHHty|]. split.
    + apply lc_open_rec_inv with (k := 0) (x := fresh_atom L).
      apply H1 with (x := fresh_atom L). apply fresh_atom_notin.
    + apply lc_open_rec_inv with (k := 0) (x := fresh_atom L).
      apply H3 with (x := fresh_atom L). apply fresh_atom_notin.
Qed.

Inductive program_context : Type :=
  | C_Hole : program_context
  | C_Abs : ty -> program_context -> security -> program_context
  | C_AppLeft : program_context -> tm -> label -> program_context
  | C_AppRight : tm -> program_context -> label -> program_context
  | C_PairLeft : program_context -> tm -> security -> program_context
  | C_PairRight : tm -> program_context -> security -> program_context
  | C_Fst : program_context -> label -> program_context
  | C_Snd : program_context -> label -> program_context
  | C_Inl : program_context -> security -> program_context
  | C_Inr : program_context -> security -> program_context
  | C_CaseScrutinee : program_context -> tm -> tm -> label -> program_context
  | C_CaseLeft : tm -> program_context -> tm -> label -> program_context
  | C_CaseRight : tm -> tm -> program_context -> label -> program_context
  | C_Protect : label -> program_context -> program_context.

Fixpoint plug (C : program_context) (t : tm) : tm :=
  match C with
  | C_Hole => t
  | C_Abs T C' kappa => tm_abs T (plug C' t) kappa
  | C_AppLeft C' t2 r => tm_app (plug C' t) t2 r
  | C_AppRight t1 C' r => tm_app t1 (plug C' t) r
  | C_PairLeft C' t2 kappa => tm_pair (plug C' t) t2 kappa
  | C_PairRight t1 C' kappa => tm_pair t1 (plug C' t) kappa
  | C_Fst C' r => tm_fst (plug C' t) r
  | C_Snd C' r => tm_snd (plug C' t) r
  | C_Inl C' kappa => tm_inl (plug C' t) kappa
  | C_Inr C' kappa => tm_inr (plug C' t) kappa
  | C_CaseScrutinee C' body1 body2 r => tm_case (plug C' t) body1 body2 r
  | C_CaseLeft t0 C' body2 r => tm_case t0 (plug C' t) body2 r
  | C_CaseRight t0 body1 C' r => tm_case t0 body1 (plug C' t) r
  | C_Protect l C' => tm_protect l (plug C' t)
  end.

Definition context_has_type (C : program_context) (T_hole T_result : ty) : Prop :=
  exists L : list atom, forall x : atom, ~ In x L ->
    has_type (update empty x T_hole) (plug C (tm_fvar x)) T_result.

Fixpoint ground (T : ty) : Prop :=
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ => ground T1 /\ ground T2
  | Ty_Arrow _ _ _ => False
  end.

Fixpoint transparent_at (kappa : security) (T : ty) : Prop :=
  security_le (security_of T) kappa /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      transparent_at kappa T1 /\ transparent_at kappa T2
  end.

Definition transparent (T : ty) : Prop := transparent_at (security_of T) T.

Lemma flows_to_low_inv : forall l, flows_to l Low -> l = Low.
Proof. destruct l; simpl; intros H; [reflexivity|contradiction]. Qed.

Lemma transparent_indirect_low : forall T kappa,
  transparent_at kappa T -> kappa.(indirect_reader) = Low ->
  (security_of T).(indirect_reader) = Low.
Proof.
  destruct T; intros kappa Htrans Hlow; simpl in *;
    destruct Htrans as [[_ Hflow] _];
    rewrite Hlow in Hflow; apply flows_to_low_inv; exact Hflow.
Qed.



Lemma transparent_ground_children_low : forall T,
  ground T -> transparent T -> (security_of T).(indirect_reader) = Low ->
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ =>
      (security_of T1).(indirect_reader) = Low /\
      (security_of T2).(indirect_reader) = Low
  | Ty_Arrow _ _ _ => False
  end.
Proof.
  destruct T; simpl; intros Hg Htr Hlow.
  - exact I.
  - destruct Hg as [Hg1 Hg2].
    unfold transparent in Htr; simpl in Htr.
    destruct Htr as [_ [Htr1 Htr2]]. split;
      eapply transparent_indirect_low; eauto.
  - destruct Hg as [Hg1 Hg2].
    unfold transparent in Htr; simpl in Htr.
    destruct Htr as [_ [Htr1 Htr2]]. split;
      eapply transparent_indirect_low; eauto.
  - contradiction.
Qed.

Definition same_result (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm,
    evaluates t1 v1 -> evaluates t2 v2 ->
    erase_security v1 = erase_security v2.

Fixpoint value_rel (T : ty) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_Unit kappa =>
      match kappa.(indirect_reader) with
      | High => True
      | Low => erase_security v1 = erase_security v2
      end
  | Ty_Sum T1 T2 kappa =>
      match kappa.(indirect_reader) with
      | High => True
      | Low =>
          (exists a1 a2 k1 k2,
             v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\
             indirect_reader k1 = Low /\ indirect_reader k2 = Low /\ value_rel T1 a1 a2) \/
          (exists b1 b2 k1 k2,
             v1 = tm_inr b1 k1 /\ v2 = tm_inr b2 k2 /\
             indirect_reader k1 = Low /\ indirect_reader k2 = Low /\ value_rel T2 b1 b2)
      end
  | Ty_Prod T1 T2 kappa =>
      match kappa.(indirect_reader) with
      | High => True
      | Low => exists a1 b1 a2 b2 k1 k2,
          v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
          indirect_reader k1 = Low /\ indirect_reader k2 = Low /\
          value_rel T1 a1 a2 /\ value_rel T2 b1 b2
      end
  | Ty_Arrow T1 T2 kappa =>
      match kappa.(indirect_reader) with
      | High => True
      | Low => forall r, flows_to kappa.(reader) r ->
          forall a1 a2,
          value a1 -> value a2 -> value_rel T1 a1 a2 ->
          forall w1 w2,
          evaluates (tm_app v1 a1 r) w1 ->
          evaluates (tm_app v2 a2 r) w2 -> value_rel T2 w1 w2
      end
  end.

Lemma flows_to_trans : forall a b c,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. destruct a, b, c; simpl; intuition. Qed.

Lemma security_le_trans : forall a b c,
  security_le a b -> security_le b c -> security_le a c.
Proof.
  intros [ar ai] [br bi] [cr ci] [Hab1 Hab2] [Hbc1 Hbc2].
  split; eapply flows_to_trans; eauto.
Qed.

Lemma value_rel_subtype : forall T U v1 v2,
  subtype T U -> value_rel T v1 v2 -> value_rel U v1 v2.
Proof.
  intros T U v1 v2 Hsub. revert v1 v2.
  induction Hsub; intros v1 v2 Hrel; simpl in *.
  - destruct kappa1 as [r1 i1], kappa2 as [r2 i2].
    destruct H1 as [_ Hflow]. simpl in *. destruct i2.
    + pose proof (flows_to_low_inv _ Hflow) as Hi.
      rewrite Hi in Hrel. exact Hrel.
    + exact I.
  - destruct kappa1 as [r1 i1], kappa2 as [r2 i2].
    destruct H1 as [_ Hflow]. simpl in *. destruct i2.
    + pose proof (flows_to_low_inv _ Hflow) as Hi.
      rewrite Hi in Hrel. simpl in Hrel.
      destruct Hrel as [[a1 [a2 [ka [kb [E1 [E2 [Hka [Hkb Ha]]]]]]]]|
                        [b1 [b2 [ka [kb [E1 [E2 [Hka [Hkb Hb]]]]]]]]].
      * left. exists a1, a2, ka, kb. repeat split; try assumption.
        eapply IHHsub1; eassumption.
      * right. exists b1, b2, ka, kb. repeat split; try assumption.
        eapply IHHsub2; eassumption.
    + exact I.
  - destruct kappa1 as [r1 i1], kappa2 as [r2 i2].
    destruct H1 as [_ Hflow]. simpl in *. destruct i2.
    + pose proof (flows_to_low_inv _ Hflow) as Hi.
      rewrite Hi in Hrel. simpl in Hrel.
      destruct Hrel as [a1 [b1 [a2 [b2 [ka [kb [E1 [E2 [Hka [Hkb [Ha Hb]]]]]]]]]]].
      exists a1, b1, a2, b2, ka, kb. repeat split; try assumption.
      * eapply IHHsub1; eassumption.
      * eapply IHHsub2; eassumption.
    + exact I.
  - destruct kappa1 as [r1 i1], kappa2 as [r2 i2].
    destruct H1 as [Hreader12 Hflow]. simpl in *. destruct i2.
    + pose proof (flows_to_low_inv _ Hflow) as Hi.
      rewrite Hi in Hrel. simpl in Hrel.
      intros r Hr a1 a2 Hva1 Hva2 Harg w1 w2 E1 E2.
      assert (Hreader1 : flows_to r1 r) by
        (eapply flows_to_trans; eauto).
      specialize (Hrel r Hreader1 a1 a2 Hva1 Hva2).
      specialize (Hrel (IHHsub1 a1 a2 Harg) w1 w2 E1 E2).
      eapply IHHsub2; eauto.
    + exact I.
  - eapply IHHsub2. eapply IHHsub1. exact Hrel.
Qed.

Lemma value_rel_protected : forall T l v1 v2,
  value v1 -> value v2 -> value_rel T v1 v2 ->
  value_rel (ty_protect l T) (protect_value v1 l) (protect_value v2 l).
Proof.
  intros T l v1 v2 Hv1 Hv2 Hrel. destruct l.
  - rewrite ty_protect_low. rewrite (protect_value_low_id v1 Hv1), (protect_value_low_id v2 Hv2).
    exact Hrel.
  - destruct T; simpl; destruct (indirect_reader s); exact I.
Qed.

Lemma value_rel_opaque : forall T v1 v2,
  (security_of T).(indirect_reader) = High -> value_rel T v1 v2.
Proof.
  destruct T; simpl; intros v1 v2 H; rewrite H; exact I.
Qed.

Lemma value_rel_ground_transparent : forall T kappa v1 v2,
  ground T -> transparent_at kappa T ->
  kappa.(indirect_reader) = Low ->
  (security_of T).(indirect_reader) = Low ->
  value_rel T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  induction T; intros kappa v1 v2 Hg Htr Hlow Htype Hrel; simpl in *.
  - rewrite Htype in Hrel. simpl in Hrel. exact Hrel.
  - destruct Hg as [Hg1 Hg2]. destruct Htr as [Hsec [Htr1 Htr2]].
    pose proof (transparent_indirect_low T1 kappa Htr1 Hlow) as Hlow1.
    pose proof (transparent_indirect_low T2 kappa Htr2 Hlow) as Hlow2.
    rewrite Htype in Hrel. simpl in Hrel.
    destruct Hrel as [[a1 [a2 [k1 [k2 [E1 [E2 [_ [_ Ha]]]]]]]]|
                      [b1 [b2 [k1 [k2 [E1 [E2 [_ [_ Hb]]]]]]]]].
    + subst v1 v2. simpl. f_equal.
      eapply IHT1; eauto.
    + subst v1 v2. simpl. f_equal.
      eapply IHT2; eauto.
  - destruct Hg as [Hg1 Hg2]. destruct Htr as [Hsec [Htr1 Htr2]].
    pose proof (transparent_indirect_low T1 kappa Htr1 Hlow) as Hlow1.
    pose proof (transparent_indirect_low T2 kappa Htr2 Hlow) as Hlow2.
    rewrite Htype in Hrel. simpl in Hrel.
    destruct Hrel as [a1 [b1 [a2 [b2 [k1 [k2 [E1 [E2 [_ [_ [Ha Hb]]]]]]]]]]].
    subst v1 v2. simpl. f_equal.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - contradiction.
Qed.

Definition term_rel (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, evaluates t1 v1 -> evaluates t2 v2 -> value_rel T v1 v2.


Definition env_rel (Gamma : context) (rho1 rho2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> term_rel T (rho1 x) (rho2 x).

Definition env_closed (rho : atom -> tm) : Prop :=
  forall x, locally_closed (rho x).

Definition env_update (rho : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else rho y.

Lemma subst_env_ext : forall t rho1 rho2,
  (forall x, In x (fv t) -> rho1 x = rho2 x) ->
  subst_env rho1 t = subst_env rho2 t.
Proof.
  induction t; simpl; intros rho1 rho2 Hagree; try reflexivity.
  - apply Hagree. simpl. auto.
  - f_equal. apply IHt. intros x Hin. apply Hagree. exact Hin.
  - f_equal.
    + apply IHt1. intros x Hin. apply Hagree. apply in_or_app. tauto.
    + apply IHt2. intros x Hin. apply Hagree. apply in_or_app. tauto.
  - f_equal.
    + apply IHt1. intros x Hin. apply Hagree. apply in_or_app. tauto.
    + apply IHt2. intros x Hin. apply Hagree. apply in_or_app. tauto.
  - f_equal. apply IHt. intros x Hin. apply Hagree. exact Hin.
  - f_equal. apply IHt. intros x Hin. apply Hagree. exact Hin.
  - f_equal. apply IHt. intros x Hin. apply Hagree. exact Hin.
  - f_equal. apply IHt. intros x Hin. apply Hagree. exact Hin.
  - f_equal.
    + apply IHt1. intros x Hin. apply Hagree. apply in_or_app. tauto.
    + apply IHt2. intros x Hin. apply Hagree. apply in_or_app. right. apply in_or_app. tauto.
    + apply IHt3. intros x Hin. apply Hagree. apply in_or_app. right. apply in_or_app. tauto.
  - f_equal. apply IHt. intros x Hin. apply Hagree. exact Hin.
Qed.

Lemma subst_env_update_fresh : forall rho x u t,
  ~ In x (fv t) -> subst_env (env_update rho x u) t = subst_env rho t.
Proof.
  intros. apply subst_env_ext. intros y Hy. unfold env_update.
  destruct (Nat.eqb y x) eqn:E; auto.
  apply Nat.eqb_eq in E. subst y. contradiction.
Qed.


Lemma lookup_update : forall Gamma x T y,
  lookup_context y (update Gamma x T) =
  if Nat.eqb y x then Some T else lookup_context y Gamma.
Proof. reflexivity. Qed.

Lemma value_term_rel : forall T a1 a2,
  value a1 -> value a2 -> value_rel T a1 a2 -> term_rel T a1 a2.
Proof.
  intros T a1 a2 Ha1 Ha2 Hrel w1 w2 E1 E2.
  pose proof (evaluates_value_id a1 w1 Ha1 E1) as Ew1.
  pose proof (evaluates_value_id a2 w2 Ha2 E2) as Ew2.
  subst w1. subst w2. exact Hrel.
Qed.

Lemma env_rel_update : forall Gamma rho1 rho2 x T a1 a2,
  env_rel Gamma rho1 rho2 -> term_rel T a1 a2 ->
  env_rel (update Gamma x T)
    (env_update rho1 x a1) (env_update rho2 x a2).
Proof.
  intros Gamma rho1 rho2 x T a1 a2 Henv Harg y U Hlookup.
  rewrite lookup_update in Hlookup. unfold env_update.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst U. exact Harg.
  - eapply Henv; eassumption.
Qed.

Lemma env_closed_update : forall rho x u,
  env_closed rho -> locally_closed u -> env_closed (env_update rho x u).
Proof.
  intros rho x u Hrho Hu y. unfold env_update.
  destruct (Nat.eqb y x); auto.
Qed.

Lemma fundamental_branch : forall Gamma L body A T,
  (forall x, ~ In x L -> has_type (update Gamma x A) (open body (tm_fvar x)) T) ->
  (forall x, ~ In x L -> forall rho1 rho2,
    env_rel (update Gamma x A) rho1 rho2 -> env_closed rho1 -> env_closed rho2 ->
    term_rel T (subst_env rho1 (open body (tm_fvar x)))
               (subst_env rho2 (open body (tm_fvar x)))) ->
  forall rho1 rho2 a1 a2 w1 w2,
    env_rel Gamma rho1 rho2 -> env_closed rho1 -> env_closed rho2 ->
    value a1 -> value a2 -> value_rel A a1 a2 ->
    evaluates (open (subst_env rho1 body) a1) w1 ->
    evaluates (open (subst_env rho2 body) a2) w2 -> value_rel T w1 w2.
Proof.
  intros Gamma L body A T Hty Hih rho1 rho2 a1 a2 w1 w2 Henv Hcl1 Hcl2
    Va1 Va2 Harg E1 E2.
  set (x := fresh_atom (L ++ fv body)).
  assert (Hx : ~ In x (L ++ fv body)) by (subst x; apply fresh_atom_notin).
  assert (HxL : ~ In x L) by (intro Q; apply Hx; apply in_or_app; left; exact Q).
  assert (Hxbody : ~ In x (fv body)) by (intro Q; apply Hx; apply in_or_app; right; exact Q).
  pose proof (has_type_lc _ _ _ (Hty x HxL)) as Hopenlc.
  unfold locally_closed, open in Hopenlc.
  pose proof (lc_open_rec_inv body 0 x Hopenlc) as Hbodylc.
  assert (Hargrel : term_rel A a1 a2) by (eapply value_term_rel; eauto).
  pose proof (env_rel_update Gamma rho1 rho2 x A a1 a2 Henv Hargrel) as Henvarg.
  pose proof (env_closed_update rho1 x a1 Hcl1 (value_lc a1 Va1)) as Hclarg1.
  pose proof (env_closed_update rho2 x a2 Hcl2 (value_lc a2 Va2)) as Hclarg2.
  specialize (Hih x HxL (env_update rho1 x a1) (env_update rho2 x a2)
    Henvarg Hclarg1 Hclarg2).
  assert (Ebody1 : subst_env (env_update rho1 x a1) (open body (tm_fvar x)) =
                       open (subst_env rho1 body) a1).
  { rewrite subst_env_open; [|exact Hclarg1].
    rewrite (subst_env_update_fresh rho1 x a1 body Hxbody).
    unfold env_update. simpl. rewrite Nat.eqb_refl. reflexivity. }
  assert (Ebody2 : subst_env (env_update rho2 x a2) (open body (tm_fvar x)) =
                       open (subst_env rho2 body) a2).
  { rewrite subst_env_open; [|exact Hclarg2].
    rewrite (subst_env_update_fresh rho2 x a2 body Hxbody).
    unfold env_update. simpl. rewrite Nat.eqb_refl. reflexivity. }
  rewrite <- Ebody1 in E1. rewrite <- Ebody2 in E2.
  exact (Hih w1 w2 E1 E2).
Qed.

Theorem fundamental : forall Gamma t T, has_type Gamma t T ->
  forall rho1 rho2, env_rel Gamma rho1 rho2 -> env_closed rho1 -> env_closed rho2 ->
  term_rel T (subst_env rho1 t) (subst_env rho2 t).
Proof.
  intros Gamma t T Hty. induction Hty;
    intros rho1 rho2 Henv Hclosed1 Hclosed2;
    unfold term_rel; intros v1 v2 E1 E2.
  - simpl in E1, E2. eapply (Henv x T H); eassumption.
  - simpl in E1, E2.
    pose proof (evaluates_value_id (tm_unit kappa) v1 (v_unit kappa) E1) as Ev1.
    pose proof (evaluates_value_id (tm_unit kappa) v2 (v_unit kappa) E2) as Ev2.
    subst v1; subst v2. simpl. destruct (indirect_reader kappa); reflexivity.
  - set (x := fresh_atom (L ++ fv body)).
    assert (Hx : ~ In x (L ++ fv body)).
    { subst x. apply fresh_atom_notin. }
    assert (HxL : ~ In x L) by (intro Hin; apply Hx; apply in_or_app; left; exact Hin).
    assert (Hxbody : ~ In x (fv body)) by (intro Hin; apply Hx; apply in_or_app; right; exact Hin).
    pose proof (has_type_lc (update Gamma x T1) (open body (tm_fvar x)) T2 (H1 x HxL)) as Hopenlc.
    unfold locally_closed, open in Hopenlc.
    pose proof (lc_open_rec_inv body 0 x Hopenlc) as Hbodylc.
    assert (Hfun1 : value (tm_abs T1 (subst_env rho1 body) kappa)).
    { apply v_abs. simpl. eapply lc_subst_env; eauto. }
    assert (Hfun2 : value (tm_abs T1 (subst_env rho2 body) kappa)).
    { apply v_abs. simpl. eapply lc_subst_env; eauto. }
    simpl in E1, E2.
    pose proof (evaluates_value_id _ _ Hfun1 E1) as Eabs1.
    pose proof (evaluates_value_id _ _ Hfun2 E2) as Eabs2.
    subst v1; subst v2.
    cbn [value_rel security_of].
    destruct (indirect_reader kappa) eqn:Hvis; cbn.
    + intros r Hr a1 a2 Hva1 Hva2 Harg w1 w2 Happ1 Happ2.
      assert (Hargrel : term_rel T1 a1 a2).
      { eapply value_term_rel; eauto. }
      pose proof (env_rel_update Gamma rho1 rho2 x T1 a1 a2 Henv Hargrel) as Henvarg.
      pose proof (env_closed_update rho1 x a1 Hclosed1 (value_lc a1 Hva1)) as Hclarg1.
      pose proof (env_closed_update rho2 x a2 Hclosed2 (value_lc a2 Hva2)) as Hclarg2.
      specialize (H2 x HxL (env_update rho1 x a1) (env_update rho2 x a2)
        Henvarg Hclarg1 Hclarg2).
      destruct (eval_abs_app_inv T1 (subst_env rho1 body) kappa a1 r w1 Hfun1 Happ1)
        as [av1 [Eav1 [Vav1 Ewrap1]]].
      destruct (eval_abs_app_inv T1 (subst_env rho2 body) kappa a2 r w2 Hfun2 Happ2)
        as [av2 [Eav2 [Vav2 Ewrap2]]].
      pose proof (evaluates_value_id a1 av1 Hva1 Eav1) as Eava1. subst av1.
      pose proof (evaluates_value_id a2 av2 Hva2 Eav2) as Eava2. subst av2.
      destruct (evaluates_protect_inv (indirect_reader kappa)
        (open (subst_env rho1 body) a1) w1 Ewrap1) as [z1 [Ez1 Ew1]].
      destruct (evaluates_protect_inv (indirect_reader kappa)
        (open (subst_env rho2 body) a2) w2 Ewrap2) as [z2 [Ez2 Ew2]].
      rewrite Hvis in Ew1, Ew2.
      rewrite (protect_value_low_id z1 (proj2 Ez1)) in Ew1.
      rewrite (protect_value_low_id z2 (proj2 Ez2)) in Ew2.
      subst w1; subst w2.
      assert (Ebody1 : subst_env (env_update rho1 x a1) (open body (tm_fvar x)) =
                       open (subst_env rho1 body) a1).
      { rewrite subst_env_open; [|exact Hclarg1].
        rewrite (subst_env_update_fresh rho1 x a1 body Hxbody).
        unfold env_update. simpl. rewrite Nat.eqb_refl. reflexivity. }
      assert (Ebody2 : subst_env (env_update rho2 x a2) (open body (tm_fvar x)) =
                       open (subst_env rho2 body) a2).
      { rewrite subst_env_open; [|exact Hclarg2].
        rewrite (subst_env_update_fresh rho2 x a2 body Hxbody).
        unfold env_update. simpl. rewrite Nat.eqb_refl. reflexivity. }
      rewrite <- Ebody1 in Ez1. rewrite <- Ebody2 in Ez2.
      eapply H2; eassumption.
    + exact I.
  - simpl in E1, E2.
    destruct (eval_app_decomp (subst_env rho1 t1) (subst_env rho1 t2) r v1 E1)
      as [f1 [a1 [Ef1 [Ea1 [Vf1 [Va1 Eapp1]]]]]].
    destruct (eval_app_decomp (subst_env rho2 t1) (subst_env rho2 t2) r v2 E2)
      as [f2 [a2 [Ef2 [Ea2 [Vf2 [Va2 Eapp2]]]]]].
    pose proof (IHHty1 rho1 rho2 Henv Hclosed1 Hclosed2 f1 f2 Ef1 Ef2) as Hfunrel.
    pose proof (IHHty2 rho1 rho2 Henv Hclosed1 Hclosed2 a1 a2 Ea1 Ea2) as Hargrel.
    destruct (indirect_reader kappa) eqn:Hind.
    + rewrite ty_protect_low. cbn [value_rel] in Hfunrel. rewrite Hind in Hfunrel.
      exact (Hfunrel r H a1 a2 Va1 Va2 Hargrel v1 v2 Eapp1 Eapp2).
    + apply value_rel_opaque. apply ty_protect_high_indirect.
  - simpl in E1, E2.
    destruct (eval_pair_inv (subst_env rho1 t1) (subst_env rho1 t2) kappa v1 E1)
      as [a1 [b1 [Ea1 [Eb1 [Ha1 [Hb1 Eq1]]]]]].
    destruct (eval_pair_inv (subst_env rho2 t1) (subst_env rho2 t2) kappa v2 E2)
      as [a2 [b2 [Ea2 [Eb2 [Ha2 [Hb2 Eq2]]]]]].
    pose proof (IHHty1 rho1 rho2 Henv Hclosed1 Hclosed2 a1 a2 Ea1 Ea2) as Hrel1.
    pose proof (IHHty2 rho1 rho2 Henv Hclosed1 Hclosed2 b1 b2 Eb1 Eb2) as Hrel2.
    rewrite Eq1, Eq2. cbn [value_rel].
    destruct (indirect_reader kappa) eqn:Hind.
    + exists a1, b1, a2, b2, kappa, kappa. repeat split; try reflexivity; try (rewrite Hind; reflexivity); assumption.
    + exact I.
  - simpl in E1, E2.
    destruct (eval_fst_inv (subst_env rho1 t) r v1 E1)
      as [a1 [b1 [k1 [Et1 [Va1 [Vb1 [Fl1 Ep1]]]]]]].
    destruct (eval_fst_inv (subst_env rho2 t) r v2 E2)
      as [a2 [b2 [k2 [Et2 [Va2 [Vb2 [Fl2 Ep2]]]]]]].
    pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2
      (tm_pair a1 b1 k1) (tm_pair a2 b2 k2) Et1 Et2) as Hpairs.
    destruct kappa as [kr ki]. simpl in *.
    destruct ki.
    + cbn [value_rel] in Hpairs.
      destruct Hpairs as [c1 [d1 [c2 [d2 [j1 [j2 [Eq1 [Eq2 [Hj1 [Hj2 [Hfirst Hsecond]]]]]]]]]]].
      inversion Eq1; inversion Eq2; subst.
      destruct (evaluates_protect_inv (indirect_reader j1) c1 v1 Ep1)
        as [z1 [Ez1 Out1]].
      destruct (evaluates_protect_inv (indirect_reader j2) c2 v2 Ep2)
        as [z2 [Ez2 Out2]].
      pose proof (evaluates_value_id c1 z1 Va1 Ez1) as Eza1. subst z1.
      pose proof (evaluates_value_id c2 z2 Va2 Ez2) as Eza2. subst z2.
      rewrite Hj1 in Out1. rewrite Hj2 in Out2.
      rewrite (protect_value_low_id c1 Va1) in Out1.
      rewrite (protect_value_low_id c2 Va2) in Out2.
      rewrite Out1, Out2. rewrite ty_protect_low.
      exact Hfirst.
    + apply value_rel_opaque. apply ty_protect_high_indirect.
  - simpl in E1, E2.
    destruct (eval_snd_inv (subst_env rho1 t) r v1 E1)
      as [a1 [b1 [k1 [Et1 [Va1 [Vb1 [Fl1 Ep1]]]]]]].
    destruct (eval_snd_inv (subst_env rho2 t) r v2 E2)
      as [a2 [b2 [k2 [Et2 [Va2 [Vb2 [Fl2 Ep2]]]]]]].
    pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2
      (tm_pair a1 b1 k1) (tm_pair a2 b2 k2) Et1 Et2) as Hpairs.
    destruct kappa as [kr ki]. simpl in *.
    destruct ki.
    + cbn [value_rel] in Hpairs.
      destruct Hpairs as [c1 [d1 [c2 [d2 [j1 [j2 [Eq1 [Eq2 [Hj1 [Hj2 [Hfirst Hsecond]]]]]]]]]]].
      inversion Eq1; inversion Eq2; subst.
      destruct (evaluates_protect_inv (indirect_reader j1) d1 v1 Ep1)
        as [z1 [Ez1 Out1]].
      destruct (evaluates_protect_inv (indirect_reader j2) d2 v2 Ep2)
        as [z2 [Ez2 Out2]].
      pose proof (evaluates_value_id d1 z1 Vb1 Ez1) as Eza1. subst z1.
      pose proof (evaluates_value_id d2 z2 Vb2 Ez2) as Eza2. subst z2.
      rewrite Hj1 in Out1. rewrite Hj2 in Out2.
      rewrite (protect_value_low_id d1 Vb1) in Out1.
      rewrite (protect_value_low_id d2 Vb2) in Out2.
      rewrite Out1, Out2. rewrite ty_protect_low.
      exact Hsecond.
    + apply value_rel_opaque. apply ty_protect_high_indirect.
  - simpl in E1, E2.
    destruct (eval_inl_inv (subst_env rho1 t) kappa v1 E1)
      as [a1 [Ea1 [Va1 Eq1]]].
    destruct (eval_inl_inv (subst_env rho2 t) kappa v2 E2)
      as [a2 [Ea2 [Va2 Eq2]]].
    pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2 a1 a2 Ea1 Ea2) as Hrel.
    rewrite Eq1, Eq2. cbn [value_rel]. destruct (indirect_reader kappa) eqn:Hind.
    + left. exists a1, a2, kappa, kappa. repeat split; try reflexivity; try (rewrite Hind; reflexivity); assumption.
    + exact I.
  - simpl in E1, E2.
    destruct (eval_inr_inv (subst_env rho1 t) kappa v1 E1)
      as [a1 [Ea1 [Va1 Eq1]]].
    destruct (eval_inr_inv (subst_env rho2 t) kappa v2 E2)
      as [a2 [Ea2 [Va2 Eq2]]].
    pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2 a1 a2 Ea1 Ea2) as Hrel.
    rewrite Eq1, Eq2. cbn [value_rel]. destruct (indirect_reader kappa) eqn:Hind.
    + right. exists a1, a2, kappa, kappa.
      repeat split; try reflexivity; try (rewrite Hind; reflexivity); assumption.
    + exact I.
  - destruct (indirect_reader kappa) eqn:Hind.
    + rewrite ty_protect_low. simpl in E1, E2.
      destruct (eval_case_inv (subst_env rho1 t) (subst_env rho1 body1)
        (subst_env rho1 body2) r v1 E1)
        as [[a1 [k1 [Es1 [Va1 [Fl1 Ebr1]]]]]|[a1 [k1 [Es1 [Va1 [Fl1 Ebr1]]]]]];
      destruct (eval_case_inv (subst_env rho2 t) (subst_env rho2 body1)
        (subst_env rho2 body2) r v2 E2)
        as [[a2 [k2 [Es2 [Va2 [Fl2 Ebr2]]]]]|[a2 [k2 [Es2 [Va2 [Fl2 Ebr2]]]]]].
      * pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2
          (tm_inl a1 k1) (tm_inl a2 k2) Es1 Es2) as Hsr.
        cbn [value_rel] in Hsr. rewrite Hind in Hsr.
        destruct Hsr as [Hlr|Hrr].
        -- destruct Hlr as [b1 [b2 [j1 [j2 [Q1 [Q2 [J1 [J2 Harg]]]]]]]].
           injection Q1 as Epay1 Eann1. injection Q2 as Epay2 Eann2.
           subst b1 j1 b2 j2.
           destruct (evaluates_protect_inv (indirect_reader k1)
             (open (subst_env rho1 body1) a1) v1 Ebr1) as [z1 [Ez1 Qout1]].
           destruct (evaluates_protect_inv (indirect_reader k2)
             (open (subst_env rho2 body1) a2) v2 Ebr2) as [z2 [Ez2 Qout2]].
           rewrite J1 in Qout1. rewrite J2 in Qout2.
           rewrite (protect_value_low_id z1 (proj2 Ez1)) in Qout1.
           rewrite (protect_value_low_id z2 (proj2 Ez2)) in Qout2.
           subst v1. subst v2.
           eapply (fundamental_branch Gamma L body1 T1 T H0 H1
             rho1 rho2 a1 a2 z1 z2 Henv Hclosed1 Hclosed2 Va1 Va2 Harg Ez1 Ez2).
        -- destruct Hrr as [b1 [b2 [j1 [j2 [Q1 [Q2 [J1 [J2 _]]]]]]]]. inversion Q1.
      * pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2
          (tm_inl a1 k1) (tm_inr a2 k2) Es1 Es2) as Hsr.
        cbn [value_rel] in Hsr. rewrite Hind in Hsr.
        destruct Hsr as [Hlr|Hrr].
        -- destruct Hlr as [b1 [b2 [j1 [j2 [Q1 [Q2 [J1 [J2 _]]]]]]]]. inversion Q2.
        -- destruct Hrr as [b1 [b2 [j1 [j2 [Q1 [Q2 [J1 [J2 _]]]]]]]]. inversion Q1.
      * pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2
          (tm_inr a1 k1) (tm_inl a2 k2) Es1 Es2) as Hsr.
        cbn [value_rel] in Hsr. rewrite Hind in Hsr.
        destruct Hsr as [Hlr|Hrr].
        -- destruct Hlr as [b1 [b2 [j1 [j2 [Q1 [Q2 [J1 [J2 _]]]]]]]]. inversion Q1.
        -- destruct Hrr as [b1 [b2 [j1 [j2 [Q1 [Q2 [J1 [J2 _]]]]]]]]. inversion Q2.
      * pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2
          (tm_inr a1 k1) (tm_inr a2 k2) Es1 Es2) as Hsr.
        cbn [value_rel] in Hsr. rewrite Hind in Hsr.
        destruct Hsr as [Hlr|Hrr].
        -- destruct Hlr as [b1 [b2 [j1 [j2 [Q1 [Q2 [J1 [J2 _]]]]]]]]. inversion Q1.
        -- destruct Hrr as [b1 [b2 [j1 [j2 [Q1 [Q2 [J1 [J2 Harg]]]]]]]].
           injection Q1 as Epay1 Eann1. injection Q2 as Epay2 Eann2.
           subst b1 j1 b2 j2.
           destruct (evaluates_protect_inv (indirect_reader k1)
             (open (subst_env rho1 body2) a1) v1 Ebr1) as [z1 [Ez1 Qout1]].
           destruct (evaluates_protect_inv (indirect_reader k2)
             (open (subst_env rho2 body2) a2) v2 Ebr2) as [z2 [Ez2 Qout2]].
           rewrite J1 in Qout1. rewrite J2 in Qout2.
           rewrite (protect_value_low_id z1 (proj2 Ez1)) in Qout1.
           rewrite (protect_value_low_id z2 (proj2 Ez2)) in Qout2.
           subst v1. subst v2.
           eapply (fundamental_branch Gamma L body2 T2 T H2 H3
             rho1 rho2 a1 a2 z1 z2 Henv Hclosed1 Hclosed2 Va1 Va2 Harg Ez1 Ez2).
    + apply value_rel_opaque. apply ty_protect_high_indirect.
  - simpl in E1, E2.
    destruct (evaluates_protect_inv l (subst_env rho1 t) v1 E1)
      as [z1 [Ez1 Q1]].
    destruct (evaluates_protect_inv l (subst_env rho2 t) v2 E2)
      as [z2 [Ez2 Q2]].
    pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2 z1 z2 Ez1 Ez2) as Hrel.
    rewrite Q1, Q2. eapply value_rel_protected.
    + exact (proj2 Ez1).
    + exact (proj2 Ez2).
    + exact Hrel.
  - pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2 v1 v2 E1 E2) as Hrel.
    eapply value_rel_subtype; eauto.
Qed.

Theorem noninterference_from_term_rel : forall (C : program_context) (t1 t2 : tm)
    (T_secret T_result : ty),
  term_rel T_result (plug C t1) (plug C t2) ->
  ground T_result ->
  transparent T_result ->
  ~ flows_to (security_of T_secret).(indirect_reader)
      (security_of T_result).(indirect_reader) ->
  same_result (plug C t1) (plug C t2).
Proof.
  intros C t1 t2 T_secret T_result Hrel Hground Htrans Hnf v1 v2 He1 He2.
  destruct (no_flow_labels _ _ Hnf) as [_ Hlow].
  eapply value_rel_ground_transparent with (kappa := security_of T_result).
  - exact Hground.
  - exact Htrans.
  - exact Hlow.
  - exact Hlow.
  -
  eapply Hrel; eassumption.
Qed.

Fixpoint context_fv (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ | C_Fst C' _ | C_Snd C' _ | C_Inl C' _ | C_Inr C' _
  | C_Protect _ C' => context_fv C'
  | C_AppLeft C' t _ | C_PairLeft C' t _ => context_fv C' ++ fv t
  | C_AppRight t C' _ | C_PairRight t C' _ => fv t ++ context_fv C'
  | C_CaseScrutinee C' b1 b2 _ => context_fv C' ++ fv b1 ++ fv b2
  | C_CaseLeft t0 C' b2 _ => fv t0 ++ context_fv C' ++ fv b2
  | C_CaseRight t0 b1 C' _ => fv t0 ++ fv b1 ++ context_fv C'
  end.

Lemma notin_app_left : forall (xs ys : list atom) x,
  ~ In x (xs ++ ys) -> ~ In x xs.
Proof. intros xs ys x H Hin. apply H. apply in_or_app; left; exact Hin. Qed.

Lemma notin_app_right : forall (xs ys : list atom) x,
  ~ In x (xs ++ ys) -> ~ In x ys.
Proof. intros xs ys x H Hin. apply H. apply in_or_app; right; exact Hin. Qed.

Lemma subst_env_identity : forall t,
  subst_env (fun y => tm_fvar y) t = t.
Proof.
  induction t; simpl; try reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt. reflexivity.
Qed.

Lemma subst_env_replace_fresh : forall x u t,
  ~ In x (fv t) ->
  subst_env (env_update (fun y => tm_fvar y) x u) t = t.
Proof.
  intros x u t Hfresh. transitivity (subst_env (fun y => tm_fvar y) t).
  - apply (subst_env_ext t
      (env_update (fun y => tm_fvar y) x u) (fun y => tm_fvar y)).
    intros y Hy.
    unfold env_update. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. contradiction.
    + reflexivity.
  - apply subst_env_identity.
Qed.

Lemma subst_env_replace_plug : forall C x u,
  ~ In x (context_fv C) ->
  subst_env (env_update (fun y => tm_fvar y) x u) (plug C (tm_fvar x)) = plug C u.
Proof.
  induction C; intros x u Hfresh; simpl in *.
  - unfold env_update. simpl. rewrite Nat.eqb_refl. reflexivity.
  - f_equal. apply IHC. exact Hfresh.
  - assert (Hc : ~ In x (context_fv C)) by (eapply notin_app_left; eassumption).
    assert (Ht : ~ In x (fv t)) by (eapply notin_app_right; eassumption).
    f_equal; [apply IHC; exact Hc|apply subst_env_replace_fresh; exact Ht].
  - assert (Ht : ~ In x (fv t)) by (eapply notin_app_left; eassumption).
    assert (Hc : ~ In x (context_fv C)) by (eapply notin_app_right; eassumption).
    f_equal; [apply subst_env_replace_fresh; exact Ht|apply IHC; exact Hc].
  - assert (Hc : ~ In x (context_fv C)) by (eapply notin_app_left; eassumption).
    assert (Ht : ~ In x (fv t)) by (eapply notin_app_right; eassumption).
    f_equal; [apply IHC; exact Hc|apply subst_env_replace_fresh; exact Ht].
  - assert (Ht : ~ In x (fv t)) by (eapply notin_app_left; eassumption).
    assert (Hc : ~ In x (context_fv C)) by (eapply notin_app_right; eassumption).
    f_equal; [apply subst_env_replace_fresh; exact Ht|apply IHC; exact Hc].
  - f_equal. apply IHC. exact Hfresh.
  - f_equal. apply IHC. exact Hfresh.
  - f_equal. apply IHC. exact Hfresh.
  - f_equal. apply IHC. exact Hfresh.
  - assert (Hc : ~ In x (context_fv C)).
    { apply (notin_app_left (context_fv C) (fv t ++ fv t0) x Hfresh). }
    pose proof (notin_app_right (context_fv C) (fv t ++ fv t0) x Hfresh) as Hsuffix.
    assert (Hb1 : ~ In x (fv t)).
    { exact (notin_app_left (fv t) (fv t0) x Hsuffix). }
    assert (Hb2 : ~ In x (fv t0)).
    { exact (notin_app_right (fv t) (fv t0) x Hsuffix). }
    simpl. f_equal; [apply IHC; exact Hc|apply subst_env_replace_fresh; exact Hb1|apply subst_env_replace_fresh; exact Hb2].
  - assert (Ht0 : ~ In x (fv t)) by (apply (notin_app_left (fv t) (context_fv C ++ fv t0) x Hfresh)).
    pose proof (notin_app_right (fv t) (context_fv C ++ fv t0) x Hfresh) as Hsuffix.
    assert (Hc : ~ In x (context_fv C)) by (apply (notin_app_left (context_fv C) (fv t0) x Hsuffix)).
    assert (Hb2 : ~ In x (fv t0)) by (apply (notin_app_right (context_fv C) (fv t0) x Hsuffix)).
    simpl. f_equal; [apply subst_env_replace_fresh; exact Ht0|apply IHC; exact Hc|apply subst_env_replace_fresh; exact Hb2].
  - assert (Ht0 : ~ In x (fv t)) by (apply (notin_app_left (fv t) (fv t0 ++ context_fv C) x Hfresh)).
    pose proof (notin_app_right (fv t) (fv t0 ++ context_fv C) x Hfresh) as Hsuffix.
    assert (Hb1 : ~ In x (fv t0)) by (apply (notin_app_left (fv t0) (context_fv C) x Hsuffix)).
    assert (Hc : ~ In x (context_fv C)) by
      (exact (notin_app_right (fv t0) (context_fv C) x Hsuffix)).
    simpl. f_equal; [apply subst_env_replace_fresh; exact Ht0|apply subst_env_replace_fresh; exact Hb1|apply IHC; exact Hc].
  - f_equal. apply IHC. exact Hfresh.
Qed.

Theorem noninterference : forall (C : program_context) (t1 t2 : tm)
    (T_secret T_result : ty),
  has_type empty t1 T_secret ->
  has_type empty t2 T_secret ->
  context_has_type C T_secret T_result ->
  ground T_result ->
  transparent T_result ->
  ~ flows_to (security_of T_secret).(indirect_reader)
      (security_of T_result).(indirect_reader) ->
  same_result (plug C t1) (plug C t2).
Proof.
  intros C t1 t2 T_secret T_result Hty1 Hty2 [L HC] Hground Htrans Hnf.
  set (x := fresh_atom (L ++ context_fv C)).
  assert (Hx : ~ In x (L ++ context_fv C)).
  { subst x. apply fresh_atom_notin. }
  assert (HxL : ~ In x L).
  { intro Hin. apply Hx. apply in_or_app. left. exact Hin. }
  assert (HxC : ~ In x (context_fv C)).
  { intro Hin. apply Hx. apply in_or_app. right. exact Hin. }
  set (rho1 := env_update (fun y => tm_fvar y) x t1).
  set (rho2 := env_update (fun y => tm_fvar y) x t2).
  assert (Henv : env_rel (update empty x T_secret) rho1 rho2).
  { intros y U Hlookup. rewrite lookup_update in Hlookup.
    unfold rho1, rho2.
    destruct (Nat.eqb y x) eqn:E.
    - inversion Hlookup; subst U.
      unfold term_rel. intros v1 v2 Ev1 Ev2.
      destruct (secret_result_labels T_secret T_result Hnf) as [Hsecret _].
      apply value_rel_opaque. exact Hsecret.
    - simpl in Hlookup. discriminate.
  }
  assert (Hclosed1 : env_closed rho1).
  { intro y. unfold rho1, env_update. destruct (Nat.eqb y x).
    - eapply has_type_lc; exact Hty1.
    - simpl. exact I. }
  assert (Hclosed2 : env_closed rho2).
  { intro y. unfold rho2, env_update. destruct (Nat.eqb y x).
    - eapply has_type_lc; exact Hty2.
    - simpl. exact I. }
  pose proof (fundamental (update empty x T_secret)
    (plug C (tm_fvar x)) T_result (HC x HxL) rho1 rho2 Henv Hclosed1 Hclosed2)
    as Hrel.
  unfold rho1, rho2 in Hrel.
  rewrite (subst_env_replace_plug C x t1 HxC) in Hrel.
  rewrite (subst_env_replace_plug C x t2 HxC) in Hrel.
  eapply noninterference_from_term_rel; eauto.
Qed.
