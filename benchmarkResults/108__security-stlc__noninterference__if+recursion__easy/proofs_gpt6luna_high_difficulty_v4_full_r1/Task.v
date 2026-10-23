From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.
Reserved Notation "t '-->' t'" (at level 40).

Inductive label : Type := Low | High.

Definition flows_to (l1 l2 : label) : Prop :=
  match l1, l2 with
  | High, Low => False
  | _, _ => True
  end.

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
  | Ty_Arrow : ty -> ty -> security -> ty
  | Ty_Nat : security -> ty.

Definition security_of (T : ty) : security :=
  match T with
  | Ty_Unit kappa | Ty_Nat kappa => kappa
  | Ty_Sum _ _ kappa | Ty_Prod _ _ kappa | Ty_Arrow _ _ kappa => kappa
  end.

Definition ty_protect (l : label) (T : ty) : ty :=
  match T with
  | Ty_Unit kappa => Ty_Unit (protect_security kappa l)
  | Ty_Nat kappa => Ty_Nat (protect_security kappa l)
  | Ty_Sum T1 T2 kappa => Ty_Sum T1 T2 (protect_security kappa l)
  | Ty_Prod T1 T2 kappa => Ty_Prod T1 T2 (protect_security kappa l)
  | Ty_Arrow T1 T2 kappa => Ty_Arrow T1 T2 (protect_security kappa l)
  end.

Fixpoint wf_ty (T : ty) : Prop :=
  match T with
  | Ty_Unit kappa | Ty_Nat kappa => wf_security kappa
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
  | tm_protect : label -> tm -> tm
  | tm_nat : nat -> security -> tm
  | tm_succ : tm -> label -> tm
  | tm_natrec : tm -> tm -> tm -> label -> tm
  | tm_if : tm -> tm -> tm -> label -> tm.

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
  | Ty_Nat _ => Ty_Nat public
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
  | ST_Succ : forall t t' r,
      t --> t' -> tm_succ t r --> tm_succ t' r
  | ST_SuccNat : forall n k r,
      flows_to k.(reader) r ->
      tm_succ (tm_nat n k) r --> tm_protect k.(indirect_reader) (tm_nat (S n) public)
  | ST_RecArg : forall n n' b s r,
      n --> n' -> tm_natrec n b s r --> tm_natrec n' b s r
  | ST_RecBase : forall n k b b' s r,
      b --> b' -> tm_natrec (tm_nat n k) b s r --> tm_natrec (tm_nat n k) b' s r
  | ST_RecStep : forall n k b s s' r,
      value b -> s --> s' -> tm_natrec (tm_nat n k) b s r --> tm_natrec (tm_nat n k) b s' r
  | ST_RecUnroll : forall n k b s r,
      value b -> value s -> flows_to k.(reader) r ->
      tm_natrec (tm_nat n k) b s r --> tm_protect k.(indirect_reader) (natrec_unroll n b s r)
  | ST_If : forall c c' yes no r,
      c --> c' -> tm_if c yes no r --> tm_if c' yes no r
  | ST_IfTrue : forall v k yes no r,
      value v -> flows_to k.(reader) r ->
      tm_if (tm_inl v k) yes no r --> tm_protect k.(indirect_reader) yes
  | ST_IfFalse : forall v k yes no r,
      value v -> flows_to k.(reader) r ->
      tm_if (tm_inr v k) yes no r --> tm_protect k.(indirect_reader) no
where "t '-->' t'" := (step t t').

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      step t1 t2 -> multi t2 t3 -> multi t1 t3.

Notation "t '-->*' t'" := (multi t t') (at level 40).

Definition evaluates (t v : tm) : Prop := t -->* v /\ value v.

Lemma value_no_step : forall v,
  value v -> forall t, ~ step v t.
Proof.
  intros v Hv. induction Hv; intros t Hstep; inversion Hstep; subst;
    match goal with
    | IH : forall u, ~ step ?v u, H : step ?v ?u |- False => exact (IH u H)
    end.
Qed.

Lemma multi_trans : forall t1 t2 t3,
  t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H12 H23. induction H12.
  - exact H23.
  - eapply multi_step; [exact H | apply IHmulti; exact H23].
Qed.

Lemma value_multi_inv : forall v t,
  value v -> v -->* t -> t = v.
Proof.
  intros v t Hv Hmulti. inversion Hmulti; subst.
  - reflexivity.
  - exfalso. eapply value_no_step; eassumption.
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
  | S_Trans : forall T U V, subtype T U -> subtype U V -> subtype T V
  | S_Nat : forall k1 k2, wf_security k1 -> wf_security k2 -> security_le k1 k2 ->
      subtype (Ty_Nat k1) (Ty_Nat k2).

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
      has_type Gamma t T -> subtype T U -> has_type Gamma t U
  | T_Nat : forall Gamma n k, wf_security k -> has_type Gamma (tm_nat n k) (Ty_Nat k)
  | T_Succ : forall Gamma t k r,
      has_type Gamma t (Ty_Nat k) -> flows_to k.(reader) r ->
      has_type Gamma (tm_succ t r) (ty_protect k.(indirect_reader) (Ty_Nat public))
  | T_NatRec : forall Gamma n b s k T r,
      has_type Gamma n (Ty_Nat k) -> has_type Gamma b T ->
      has_type Gamma s (Ty_Arrow (Ty_Nat public) (Ty_Arrow T T public) public) ->
      flows_to k.(reader) r ->
      has_type Gamma (tm_natrec n b s r) (ty_protect k.(indirect_reader) T)
  | T_If : forall Gamma c yes no k T r,
      has_type Gamma c (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) ->
      has_type Gamma yes T -> has_type Gamma no T -> flows_to k.(reader) r ->
      has_type Gamma (tm_if c yes no r) (ty_protect k.(indirect_reader) T).

Lemma ty_protect_wf : forall T l,
  wf_ty T -> wf_ty (ty_protect l T).
Proof.
  assert (forall k l, wf_security k -> wf_security (protect_security k l)) as Hprotect.
  { intros [r ir] l. destruct r, ir, l;
      unfold wf_security, protect_security; simpl; tauto. }
  destruct T; simpl; intros l H; intuition.
Qed.

Lemma subtype_regular : forall T U,
  subtype T U -> wf_ty T /\ wf_ty U.
Proof. intros T U H. induction H; simpl in *; tauto. Qed.

Lemma subtype_erasure : forall T U,
  subtype T U -> erase_type T = erase_type U.
Proof. intros T U H. induction H; simpl; congruence. Qed.

Lemma security_le_refl : forall k, security_le k k.
Proof. intros [r ir]. split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros k1 k2 k3 [Hr1 Hi1] [Hr2 Hi2]. split; eapply flows_to_trans; eassumption.
Qed.

Lemma subtype_refl : forall T, wf_ty T -> subtype T T.
Proof.
  induction T; simpl; intros Hwf.
  - apply S_Unit; try assumption; apply security_le_refl.
  - destruct Hwf as [H1 [H2 Hk]]. apply S_Sum; auto using security_le_refl.
  - destruct Hwf as [H1 [H2 Hk]]. apply S_Prod; auto using security_le_refl.
  - destruct Hwf as [H1 [H2 Hk]]. apply S_Arrow; auto using security_le_refl.
  - apply S_Nat; try assumption; apply security_le_refl.
Qed.

Lemma security_protect_mono : forall k1 k2 l1 l2,
  security_le k1 k2 -> flows_to l1 l2 ->
  security_le (protect_security k1 l1) (protect_security k2 l2).
Proof.
  intros [r1 ir1] [r2 ir2] l1 l2.
  destruct r1, ir1, r2, ir2, l1, l2;
    unfold security_le, protect_security; simpl; tauto.
Qed.

Lemma protect_security_wf : forall k l,
  wf_security k -> wf_security (protect_security k l).
Proof.
  intros [r ir] l; destruct r, ir, l;
    unfold wf_security, protect_security; simpl; tauto.
Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof.
  destruct T; destruct s as [r ir]; destruct r, ir; reflexivity.
Qed.

Lemma subtype_protect : forall T U, subtype T U -> forall l1 l2,
  flows_to l1 l2 -> subtype (ty_protect l1 T) (ty_protect l2 U).
Proof.
  intros T U Hsub. induction Hsub; intros l1 l2 Hl; simpl.
  - apply S_Unit; auto using protect_security_wf, security_protect_mono.
  - apply S_Sum; auto using protect_security_wf, security_protect_mono.
  - apply S_Prod; auto using protect_security_wf, security_protect_mono.
  - apply S_Arrow; auto using protect_security_wf, security_protect_mono.
  - eapply S_Trans; [apply IHHsub1; exact Hl | apply IHHsub2; apply flows_to_refl].
  - apply S_Nat; auto using protect_security_wf, security_protect_mono.
Qed.

Lemma subtype_arrow_inv : forall T U,
  subtype T U -> forall A B k,
  T = Ty_Arrow A B k ->
  exists A' B' k', U = Ty_Arrow A' B' k' /\
    subtype A' A /\ subtype B B' /\ security_le k k'.
Proof.
  intros T U Hsub. induction Hsub; intros A B k Heq; inversion Heq; subst.
  - exists U1, U2, kappa2. auto.
  - destruct (IHHsub1 _ _ _ eq_refl) as [Am [Bm [km [-> [Ha [Hb Hk]]]]]].
    destruct (IHHsub2 _ _ _ eq_refl) as [Ac [Bc [kc [-> [Ha' [Hb' Hk']]]]]].
    exists Ac, Bc, kc. split; [reflexivity | ]. repeat split.
    + eapply S_Trans; eassumption.
    + eapply S_Trans; eassumption.
    + eapply flows_to_trans; [exact (proj1 Hk) | exact (proj1 Hk')].
    + eapply flows_to_trans; [exact (proj2 Hk) | exact (proj2 Hk')].
Qed.

Lemma subtype_prod_inv : forall T U,
  subtype T U -> forall A B k,
  T = Ty_Prod A B k ->
  exists A' B' k', U = Ty_Prod A' B' k' /\
    subtype A A' /\ subtype B B' /\ security_le k k'.
Proof.
  intros T U Hsub. induction Hsub; intros A B k Heq; inversion Heq; subst.
  - exists U1, U2, kappa2. auto.
  - destruct (IHHsub1 _ _ _ eq_refl) as [Am [Bm [km [-> [Ha [Hb Hk]]]]]].
    destruct (IHHsub2 _ _ _ eq_refl) as [Ac [Bc [kc [-> [Ha' [Hb' Hk']]]]]].
    exists Ac, Bc, kc. split; [reflexivity | ]. repeat split.
    + eapply S_Trans; eassumption.
    + eapply S_Trans; eassumption.
    + eapply flows_to_trans; [exact (proj1 Hk) | exact (proj1 Hk')].
    + eapply flows_to_trans; [exact (proj2 Hk) | exact (proj2 Hk')].
Qed.

Lemma subtype_sum_inv : forall T U,
  subtype T U -> forall A B k,
  T = Ty_Sum A B k ->
  exists A' B' k', U = Ty_Sum A' B' k' /\
    subtype A A' /\ subtype B B' /\ security_le k k'.
Proof.
  intros T U Hsub. induction Hsub; intros A B k Heq; inversion Heq; subst.
  - exists U1, U2, kappa2. auto.
  - destruct (IHHsub1 _ _ _ eq_refl) as [Am [Bm [km [-> [Ha [Hb Hk]]]]]].
    destruct (IHHsub2 _ _ _ eq_refl) as [Ac [Bc [kc [-> [Ha' [Hb' Hk']]]]]].
    exists Ac, Bc, kc. split; [reflexivity | ]. repeat split.
    + eapply S_Trans; eassumption.
    + eapply S_Trans; eassumption.
    + eapply flows_to_trans; [exact (proj1 Hk) | exact (proj1 Hk')].
    + eapply flows_to_trans; [exact (proj2 Hk) | exact (proj2 Hk')].
Qed.

Lemma subtype_nat_inv : forall T U, subtype T U -> forall k,
  T = Ty_Nat k -> exists k', U = Ty_Nat k' /\ security_le k k'.
Proof.
  intros T U H. induction H; intros k E; inversion E; subst.
  - destruct (IHsubtype1 _ eq_refl) as [km [-> Hm]].
    destruct (IHsubtype2 _ eq_refl) as [ku [-> Hu]].
    exists ku. split; [reflexivity | eapply security_le_trans; eassumption].
  - exists k2. auto.
Qed.

Lemma typing_regular : forall Gamma t T,
  has_type Gamma t T -> locally_closed t /\ wf_ty T.
Proof.
  intros Gamma t T H. induction H; unfold locally_closed, open in *; simpl in *.
  - tauto.
  - tauto.
  - destruct (fresh_atom L) as [x Hfresh].
    destruct (H2 x Hfresh) as [Hlc Hwf].
    split; [eapply lc_at_open_inv; exact Hlc | tauto].
  - destruct IHhas_type1 as [Hlc1 [Hwf1 [Hwf2 Hk]]].
    destruct IHhas_type2 as [Hlc2 _]. split; [tauto | apply ty_protect_wf; exact Hwf2].
  - tauto.
  - destruct IHhas_type as [Hlc [Hwf1 [Hwf2 Hk]]].
    split; [exact Hlc | apply ty_protect_wf; exact Hwf1].
  - destruct IHhas_type as [Hlc [Hwf1 [Hwf2 Hk]]].
    split; [exact Hlc | apply ty_protect_wf; exact Hwf2].
  - tauto.
  - tauto.
  - destruct (fresh_atom L) as [x Hfresh].
    destruct (H2 x Hfresh) as [Hlc1 Hwf1].
    destruct (H4 x Hfresh) as [Hlc2 Hwf2].
    split.
    + split; [tauto | ]. split; eapply lc_at_open_inv; eassumption.
    + apply ty_protect_wf; exact Hwf1.
  - split; [tauto | apply ty_protect_wf; tauto].
  - split; [tauto | exact (proj2 (subtype_regular _ _ H0))].
  - tauto.
  - split; [tauto | destruct k as [r0 ir]; destruct r0, ir; exact I].
  - split; [tauto | apply ty_protect_wf; tauto].
  - split; [tauto | apply ty_protect_wf; tauto].
Qed.

Inductive big_step : tm -> tm -> Prop :=
  | B_Unit : forall k,
      big_step (tm_unit k) (tm_unit k)
  | B_Abs : forall A body k,
      locally_closed (tm_abs A body k) ->
      big_step (tm_abs A body k) (tm_abs A body k)
  | B_App : forall f a r A body k v w,
      big_step f (tm_abs A body k) -> big_step a v ->
      flows_to k.(reader) r -> big_step (open body v) w ->
      big_step (tm_app f a r) (protect_value w k.(indirect_reader))
  | B_Pair : forall a b k v w,
      big_step a v -> big_step b w ->
      big_step (tm_pair a b k) (tm_pair v w k)
  | B_Fst : forall t r a b k,
      big_step t (tm_pair a b k) -> flows_to k.(reader) r ->
      big_step (tm_fst t r) (protect_value a k.(indirect_reader))
  | B_Snd : forall t r a b k,
      big_step t (tm_pair a b k) -> flows_to k.(reader) r ->
      big_step (tm_snd t r) (protect_value b k.(indirect_reader))
  | B_Inl : forall t k v,
      big_step t v -> big_step (tm_inl t k) (tm_inl v k)
  | B_Inr : forall t k v,
      big_step t v -> big_step (tm_inr t k) (tm_inr v k)
  | B_CaseLeft : forall t b1 b2 r v k w,
      big_step t (tm_inl v k) -> flows_to k.(reader) r ->
      big_step (open b1 v) w ->
      big_step (tm_case t b1 b2 r) (protect_value w k.(indirect_reader))
  | B_CaseRight : forall t b1 b2 r v k w,
      big_step t (tm_inr v k) -> flows_to k.(reader) r ->
      big_step (open b2 v) w ->
      big_step (tm_case t b1 b2 r) (protect_value w k.(indirect_reader))
  | B_Protect : forall l t v,
      big_step t v -> big_step (tm_protect l t) (protect_value v l)
  | B_Nat : forall n k, big_step (tm_nat n k) (tm_nat n k)
  | B_Succ : forall t n k r,
      big_step t (tm_nat n k) -> flows_to k.(reader) r ->
      big_step (tm_succ t r) (protect_value (tm_nat (S n) public) k.(indirect_reader))
  | B_NatRec : forall n b s r m k vb vs result,
      big_step n (tm_nat m k) -> big_step b vb -> big_step s vs ->
      flows_to k.(reader) r -> big_step (natrec_unroll m vb vs r) result ->
      big_step (tm_natrec n b s r) (protect_value result k.(indirect_reader))
  | B_IfTrue : forall c yes no r v k result,
      big_step c (tm_inl v k) -> flows_to k.(reader) r -> big_step yes result ->
      big_step (tm_if c yes no r) (protect_value result k.(indirect_reader))
  | B_IfFalse : forall c yes no r v k result,
      big_step c (tm_inr v k) -> flows_to k.(reader) r -> big_step no result ->
      big_step (tm_if c yes no r) (protect_value result k.(indirect_reader)).

Lemma value_protect : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv. inversion Hv; subst; simpl;
    eauto using v_unit, v_abs, v_pair, v_inl, v_inr, v_nat.
Qed.

Lemma big_step_result_value : forall t v, big_step t v -> value v.
Proof.
  intros t v H. induction H;
    eauto using v_unit, v_abs, v_pair, v_inl, v_inr, v_nat, value_protect.
  - inversion IHbig_step; subst. apply value_protect; assumption.
  - inversion IHbig_step; subst. apply value_protect; assumption.
Qed.

Lemma big_step_value_refl : forall v, value v -> big_step v v.
Proof.
  intros v Hv. induction Hv;
    eauto using B_Unit, B_Abs, B_Pair, B_Inl, B_Inr, B_Nat.
Qed.

Lemma big_step_value_inv : forall v w, value v -> big_step v w -> w = v.
Proof.
  intros v w Hv. generalize dependent w. induction Hv;
    intros w Heval; inversion Heval; subst; f_equal; eauto.
Qed.

Lemma multi_congruence : forall (C : tm -> tm),
  (forall t t', step t t' -> step (C t) (C t')) ->
  forall t t', multi t t' -> multi (C t) (C t').
Proof.
  intros C HC t t' H. induction H.
  - apply multi_refl.
  - eapply multi_step; [apply HC; exact H | exact IHmulti].
Qed.

Lemma big_step_sound : forall t v, big_step t v -> evaluates t v.
Proof.
  intros t v H. split; [| eapply big_step_result_value; exact H].
  induction H.
  - apply multi_refl.
  - apply multi_refl.
  - eapply multi_trans.
    + apply (multi_congruence (fun f => tm_app f a r)); eauto using ST_App1.
    + eapply multi_trans.
      * apply (multi_congruence (fun a => tm_app (tm_abs A body k) a r));
          eauto using ST_App2, big_step_result_value.
      * eapply multi_step.
        -- eapply ST_AppAbs; eauto using big_step_result_value.
        -- eapply multi_trans.
           ++ apply (multi_congruence (tm_protect k.(indirect_reader)));
                eauto using ST_Protect.
           ++ eapply multi_step; [apply ST_ProtectValue;
                eauto using big_step_result_value | apply multi_refl].
  - eapply multi_trans.
    + apply (multi_congruence (fun a => tm_pair a b k)); eauto using ST_Pair1.
    + apply (multi_congruence (fun b => tm_pair v b k));
        eauto using ST_Pair2, big_step_result_value.
  - eapply multi_trans.
    + apply (multi_congruence (fun t => tm_fst t r)); eauto using ST_Fst.
    + pose proof (big_step_result_value _ _ H) as Hv. inversion Hv; subst.
      eapply multi_step; [apply ST_FstPair; eassumption |].
      eapply multi_step; [apply ST_ProtectValue; assumption | apply multi_refl].
  - eapply multi_trans.
    + apply (multi_congruence (fun t => tm_snd t r)); eauto using ST_Snd.
    + pose proof (big_step_result_value _ _ H) as Hv. inversion Hv; subst.
      eapply multi_step; [apply ST_SndPair; eassumption |].
      eapply multi_step; [apply ST_ProtectValue; assumption | apply multi_refl].
  - apply (multi_congruence (fun t => tm_inl t k)); eauto using ST_Inl.
  - apply (multi_congruence (fun t => tm_inr t k)); eauto using ST_Inr.
  - eapply multi_trans.
    + apply (multi_congruence (fun t => tm_case t b1 b2 r)); eauto using ST_Case.
    + pose proof (big_step_result_value _ _ H) as Hv. inversion Hv; subst.
      eapply multi_step; [apply ST_CaseLeft; eassumption |].
      eapply multi_trans.
      * apply (multi_congruence (tm_protect k.(indirect_reader)));
          eauto using ST_Protect.
      * eapply multi_step; [apply ST_ProtectValue;
          eauto using big_step_result_value | apply multi_refl].
  - eapply multi_trans.
    + apply (multi_congruence (fun t => tm_case t b1 b2 r)); eauto using ST_Case.
    + pose proof (big_step_result_value _ _ H) as Hv. inversion Hv; subst.
      eapply multi_step; [apply ST_CaseRight; eassumption |].
      eapply multi_trans.
      * apply (multi_congruence (tm_protect k.(indirect_reader)));
          eauto using ST_Protect.
      * eapply multi_step; [apply ST_ProtectValue;
          eauto using big_step_result_value | apply multi_refl].
  - eapply multi_trans.
    + apply (multi_congruence (tm_protect l)); eauto using ST_Protect.
    + eapply multi_step; [apply ST_ProtectValue;
        eauto using big_step_result_value | apply multi_refl].
  - apply multi_refl.
  - eapply multi_trans.
    + apply (multi_congruence (fun t => tm_succ t r)); eauto using ST_Succ.
    + eapply multi_step; [apply ST_SuccNat; assumption |].
      eapply multi_step; [apply ST_ProtectValue; apply v_nat | apply multi_refl].
  - eapply multi_trans.
    + apply (multi_congruence (fun n => tm_natrec n b s r)); eauto using ST_RecArg.
    + eapply multi_trans.
      * apply (multi_congruence (fun b => tm_natrec (tm_nat m k) b s r)); eauto using ST_RecBase.
      * eapply multi_trans.
        -- apply (multi_congruence (fun s => tm_natrec (tm_nat m k) vb s r));
             eauto using ST_RecStep, big_step_result_value.
        -- eapply multi_step; [apply ST_RecUnroll; eauto using big_step_result_value |].
           eapply multi_trans.
           ++ apply (multi_congruence (tm_protect k.(indirect_reader))); eauto using ST_Protect.
           ++ eapply multi_step; [apply ST_ProtectValue; eauto using big_step_result_value | apply multi_refl].
  - eapply multi_trans.
    + apply (multi_congruence (fun c => tm_if c yes no r)); eauto using ST_If.
    + pose proof (big_step_result_value _ _ H) as Hv. inversion Hv; subst.
      eapply multi_step; [apply ST_IfTrue; eassumption |].
      eapply multi_trans.
      * apply (multi_congruence (tm_protect k.(indirect_reader))); eauto using ST_Protect.
      * eapply multi_step; [apply ST_ProtectValue; eauto using big_step_result_value | apply multi_refl].
  - eapply multi_trans.
    + apply (multi_congruence (fun c => tm_if c yes no r)); eauto using ST_If.
    + pose proof (big_step_result_value _ _ H) as Hv. inversion Hv; subst.
      eapply multi_step; [apply ST_IfFalse; eassumption |].
      eapply multi_trans.
      * apply (multi_congruence (tm_protect k.(indirect_reader))); eauto using ST_Protect.
      * eapply multi_step; [apply ST_ProtectValue; eauto using big_step_result_value | apply multi_refl].
Qed.

Lemma step_big_step : forall t t', step t t' ->
  forall v, big_step t' v -> big_step t v.
Proof.
  intros t t' Hstep. induction Hstep; intros result Heval.
  all: try solve [
    pose proof (big_step_value_inv _ _ (value_protect _ _ H) Heval) as ->;
    apply B_Protect; apply big_step_value_refl; exact H].
  all: inversion Heval; subst;
    eauto using B_Unit, B_Abs, B_App, B_Pair, B_Fst, B_Snd,
      B_Inl, B_Inr, B_CaseLeft, B_CaseRight, B_Protect, B_IfTrue, B_IfFalse, B_Nat, B_Succ, B_NatRec,
      big_step_value_refl.
  all: try (match goal with Hv : value ?v, He : big_step ?v ?w |- _ =>
    pose proof (big_step_value_inv v w Hv He); subst w end).
  all: try solve [eauto using B_App, B_Fst, B_Snd, B_CaseLeft,
    B_CaseRight, B_Protect, B_IfTrue, B_IfFalse, B_Nat, B_Succ, B_NatRec, B_Pair, B_Inl, B_Inr, big_step_value_refl].
  inversion H3; subst. apply B_Succ; [apply B_Nat | exact H].
Qed.

Theorem big_step_iff_evaluates : forall t v, big_step t v <-> evaluates t v.
Proof.
  intros t v. split; [apply big_step_sound |].
  intros [Hsteps Hv]. induction Hsteps.
  - apply big_step_value_refl; exact Hv.
  - eapply step_big_step; [exact H | apply IHHsteps; exact Hv].
Qed.

Lemma protect_value_compose : forall v l1 l2,
  protect_value (protect_value v l1) l2 = protect_value v (join l1 l2).
Proof.
  intros v l1 l2. destruct v; simpl; try reflexivity;
    match goal with k : security |- _ => destruct k as [r ir] end;
    destruct r, ir, l1, l2; reflexivity.
Qed.

Lemma erase_protect_value : forall v l,
  erase_security (protect_value v l) = erase_security v.
Proof. intros v l. destruct v; reflexivity. Qed.

Lemma evaluates_protected_function : forall f arg l result,
  value f -> value arg ->
  evaluates (tm_app (protect_value f l) arg High) result ->
  exists original,
    evaluates (tm_app f arg High) original /\
    result = protect_value original l.
Proof.
  intros f arg l result Hf Ha Heval.
  apply big_step_iff_evaluates in Heval. inversion Heval; subst.
  match goal with H : big_step (protect_value f l) _ |- _ =>
    pose proof (big_step_value_inv _ _ (value_protect _ _ Hf) H) as Hshape
  end.
  destruct f; simpl in Hshape; try discriminate Hshape.
  inversion Hshape; subst.
  match goal with H : big_step arg _ |- _ =>
    pose proof (big_step_value_inv _ _ Ha H) as ->
  end.
  exists (protect_value w s.(indirect_reader)). split.
  - apply big_step_iff_evaluates. eapply B_App;
      eauto using big_step_value_refl.
    destruct s.(reader); exact I.
  - rewrite protect_value_compose. reflexivity.
Qed.

Lemma lookup_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_update_neq : forall Gamma x y T,
  x <> y -> lookup_context x (update Gamma y T) = lookup_context x Gamma.
Proof.
  intros Gamma x y T Hneq. simpl.
  destruct (Nat.eqb x y) eqn:Heq; [apply Nat.eqb_eq in Heq; contradiction | reflexivity].
Qed.

Definition context_included (Gamma Gamma' : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> lookup_context x Gamma' = Some T.

Lemma context_included_update : forall Gamma Gamma' x T,
  context_included Gamma Gamma' ->
  context_included (update Gamma x T) (update Gamma' x T).
Proof.
  intros Gamma Gamma' x T H y U Hy. simpl in *.
  destruct (Nat.eqb y x); [exact Hy | apply H; exact Hy].
Qed.

Lemma typing_weaken : forall Gamma t T,
  has_type Gamma t T -> forall Gamma', context_included Gamma Gamma' -> has_type Gamma' t T.
Proof.
  intros Gamma t T H. induction H; intros Gamma' Hinc.
  - apply T_Var; [apply Hinc; exact H | exact H0].
  - apply T_Unit; exact H.
  - apply T_Abs with (L := L); try assumption.
    intros x Hfresh. apply H2; [exact Hfresh | apply context_included_update; exact Hinc].
  - eapply T_App; eauto.
  - apply T_Pair; eauto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
  - apply T_Inl; eauto.
  - apply T_Inr; eauto.
  - eapply T_Case with (L := L); try eassumption.
    + apply IHhas_type; exact Hinc.
    + intros x Hfresh. apply H2; [exact Hfresh | apply context_included_update; exact Hinc].
    + intros x Hfresh. apply H4; [exact Hfresh | apply context_included_update; exact Hinc].
  - apply T_Protect; auto.
  - eapply T_Sub; eauto.
  - apply T_Nat; assumption.
  - eapply T_Succ; eauto.
  - eapply T_NatRec; eauto.
  - eapply T_If; eauto.
Qed.

Lemma typing_weaken_empty : forall t T Gamma,
  has_type empty t T -> has_type Gamma t T.
Proof.
  intros t T Gamma H. eapply typing_weaken; [exact H | ].
  intros x U Hlookup. discriminate Hlookup.
Qed.

Lemma context_substitution_update : forall Gamma Gamma' x y U A,
  x <> y -> lookup_context x Gamma = Some U ->
  (forall z T, z <> x -> lookup_context z Gamma = Some T ->
    lookup_context z Gamma' = Some T) ->
  lookup_context x (update Gamma y A) = Some U /\
  (forall z T, z <> x -> lookup_context z (update Gamma y A) = Some T ->
    lookup_context z (update Gamma' y A) = Some T).
Proof.
  intros Gamma Gamma' x y U A Hneq Hlookup Hinc. split.
  - rewrite lookup_update_neq; assumption.
  - intros z T Hneqz Hlookupz. simpl in *.
    destruct (Nat.eqb z y); [exact Hlookupz | apply Hinc; assumption].
Qed.

Lemma subst_open_fresh : forall body x y u,
  x <> y -> locally_closed u ->
  subst x u (open body (tm_fvar y)) = open (subst x u body) (tm_fvar y).
Proof.
  intros body x y u Hneq Hlc. unfold open.
  rewrite subst_open_rec by exact Hlc. simpl.
  destruct (Nat.eqb x y) eqn:Heq; [apply Nat.eqb_eq in Heq; contradiction | reflexivity].
Qed.

Lemma typing_subst_closed : forall Gamma t T,
  has_type Gamma t T -> forall x U u Gamma',
  lookup_context x Gamma = Some U ->
  (forall y A, y <> x -> lookup_context y Gamma = Some A ->
    lookup_context y Gamma' = Some A) ->
  has_type empty u U -> has_type Gamma' (subst x u t) T.
Proof.
  intros Gamma t T Htyped. induction Htyped; intros z Us u Gamma' Hz Hinc Hu; simpl.
  - destruct (Nat.eqb z x) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst z. rewrite H in Hz. inversion Hz; subst.
      apply typing_weaken_empty; exact Hu.
    + apply T_Var; [apply Hinc; [apply Nat.eqb_neq in Heq; congruence | exact H] | exact H0].
  - apply T_Unit; exact H.
  - apply T_Abs with (L := z :: L); try assumption.
    intros y Hfresh. assert (z <> y /\ ~ In y L) as [Hneq Hy] by (simpl in Hfresh; tauto).
    destruct (context_substitution_update _ _ _ _ _ T1 Hneq Hz Hinc) as [Hz' Hinc'].
    rewrite <- subst_open_fresh by (try exact Hneq; exact (proj1 (typing_regular _ _ _ Hu))).
    eapply H2; eassumption.
  - eapply T_App; eauto.
  - apply T_Pair; eauto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
  - apply T_Inl; eauto.
  - apply T_Inr; eauto.
  - eapply T_Case with (L := z :: L); try eassumption.
    + eapply IHHtyped; eassumption.
    + intros y Hfresh. assert (z <> y /\ ~ In y L) as [Hneq Hy] by (simpl in Hfresh; tauto).
      destruct (context_substitution_update _ _ _ _ _ T1 Hneq Hz Hinc) as [Hz' Hinc'].
      rewrite <- subst_open_fresh by (try exact Hneq; exact (proj1 (typing_regular _ _ _ Hu))).
      eapply H1; eassumption.
    + intros y Hfresh. assert (z <> y /\ ~ In y L) as [Hneq Hy] by (simpl in Hfresh; tauto).
      destruct (context_substitution_update _ _ _ _ _ T2 Hneq Hz Hinc) as [Hz' Hinc'].
      rewrite <- subst_open_fresh by (try exact Hneq; exact (proj1 (typing_regular _ _ _ Hu))).
      eapply H3; eassumption.
  - apply T_Protect. eapply IHHtyped; eassumption.
  - eapply T_Sub; [eapply IHHtyped; eassumption | exact H].
  - apply T_Nat; assumption.
  - eapply T_Succ; eauto.
  - eapply T_NatRec; eauto.
  - eapply T_If; eauto.
Qed.

Lemma typing_open_closed : forall Gamma body T U L u,
  (forall x, ~ In x L -> has_type (update Gamma x U) (open body (tm_fvar x)) T) ->
  has_type empty u U -> has_type Gamma (open body u) T.
Proof.
  intros Gamma body T U L u Hbody Hu.
  destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
  rewrite in_app_iff in Hfresh.
  rewrite (open_subst_intro body x u) by (try tauto; exact (proj1 (typing_regular _ _ _ Hu))).
  eapply typing_subst_closed.
  - apply Hbody; tauto.
  - apply lookup_update_eq.
  - intros y A Hneq Hlookup. rewrite lookup_update_neq in Hlookup by exact Hneq. exact Hlookup.
  - exact Hu.
Qed.

Lemma typing_abs_inv : forall Gamma t T,
  has_type Gamma t T -> forall A body k,
  t = tm_abs A body k ->
  exists B L, subtype (Ty_Arrow A B k) T /\
    (forall x, ~ In x L -> has_type (update Gamma x A) (open body (tm_fvar x)) B).
Proof.
  intros Gamma t T Htyped. induction Htyped; intros AA bb kk Heq; inversion Heq; subst.
  - exists T2, L. split; [apply subtype_refl | exact H1].
    destruct (fresh_atom L) as [x Hx].
    pose proof (proj2 (typing_regular _ _ _ (H1 x Hx))). simpl. tauto.
  - destruct (IHHtyped _ _ _ eq_refl) as [B [L [Hs Hb]]].
    exists B, L. split; [eapply S_Trans; eassumption | exact Hb].
Qed.

Lemma typing_pair_inv : forall Gamma t T,
  has_type Gamma t T -> forall a b k,
  t = tm_pair a b k ->
  exists A B, has_type Gamma a A /\ has_type Gamma b B /\ subtype (Ty_Prod A B k) T.
Proof.
  intros Gamma t T Htyped. induction Htyped; intros aa bb kk Heq; inversion Heq; subst.
  - exists T1, T2. repeat split; try assumption. apply subtype_refl. simpl.
    pose proof (proj2 (typing_regular _ _ _ Htyped1)).
    pose proof (proj2 (typing_regular _ _ _ Htyped2)). tauto.
  - destruct (IHHtyped _ _ _ eq_refl) as [A [B [Ha [Hb Hs]]]].
    exists A, B. repeat split; try assumption. eapply S_Trans; eassumption.
Qed.

Lemma typing_inl_inv : forall Gamma t T,
  has_type Gamma t T -> forall a k,
  t = tm_inl a k ->
  exists A B, has_type Gamma a A /\ subtype (Ty_Sum A B k) T.
Proof.
  intros Gamma t T Htyped. induction Htyped; intros a kk Heq; inversion Heq; subst.
  - exists T1, T2. split; [exact Htyped | apply subtype_refl].
    pose proof (proj2 (typing_regular _ _ _ Htyped)). simpl. tauto.
  - destruct (IHHtyped _ _ eq_refl) as [A [B [Ha Hs]]].
    exists A, B. split; [exact Ha | eapply S_Trans; eassumption].
Qed.

Lemma typing_inr_inv : forall Gamma t T,
  has_type Gamma t T -> forall a k,
  t = tm_inr a k ->
  exists A B, has_type Gamma a B /\ subtype (Ty_Sum A B k) T.
Proof.
  intros Gamma t T Htyped. induction Htyped; intros a kk Heq; inversion Heq; subst.
  - exists T1, T2. split; [exact Htyped | apply subtype_refl].
    pose proof (proj2 (typing_regular _ _ _ Htyped)). simpl. tauto.
  - destruct (IHHtyped _ _ eq_refl) as [A [B [Ha Hs]]].
    exists A, B. split; [exact Ha | eapply S_Trans; eassumption].
Qed.

Lemma typing_protect_value : forall Gamma v T,
  has_type Gamma v T -> value v -> forall l,
  has_type Gamma (protect_value v l) (ty_protect l T).
Proof.
  intros Gamma v T Htyped. induction Htyped; intros Hv lp;
    try solve [inversion Hv]; simpl;
    try solve [apply T_Unit; apply protect_security_wf; assumption];
    try solve [apply T_Abs with (L := L); auto using protect_security_wf];
    try solve [apply T_Pair; auto using protect_security_wf];
    try solve [apply T_Inl; auto using protect_security_wf];
    try solve [apply T_Inr; auto using protect_security_wf];
    try solve [apply T_Nat; auto using protect_security_wf].
  eapply T_Sub; [apply IHHtyped; exact Hv | apply subtype_protect; [exact H | apply flows_to_refl]].
Qed.

Lemma typing_beta : forall A body k v T1 T2 kt,
  has_type empty (tm_abs A body k) (Ty_Arrow T1 T2 kt) ->
  has_type empty v T1 ->
  has_type empty (tm_protect k.(indirect_reader) (open body v))
    (ty_protect kt.(indirect_reader) T2).
Proof.
  intros A body k v T1 T2 kt Hfun Hv.
  destruct (typing_abs_inv _ _ _ Hfun _ _ _ eq_refl) as [B [L [Hsub Hbody]]].
  destruct (subtype_arrow_inv _ _ Hsub _ _ _ eq_refl) as [C [D [kc [Heq [Ha [Hb Hk]]]]]].
  inversion Heq; subst.
  eapply T_Sub.
  - apply T_Protect. eapply typing_open_closed; [exact Hbody | eapply T_Sub; eassumption].
  - apply subtype_protect; [exact Hb | exact (proj2 Hk)].
Qed.

Lemma typing_project_left : forall a b k T1 T2 kt,
  has_type empty (tm_pair a b k) (Ty_Prod T1 T2 kt) ->
  has_type empty (tm_protect k.(indirect_reader) a) (ty_protect kt.(indirect_reader) T1).
Proof.
  intros a b k T1 T2 kt Hpair.
  destruct (typing_pair_inv _ _ _ Hpair _ _ _ eq_refl) as [A [B [Ha [Hb Hsub]]]].
  destruct (subtype_prod_inv _ _ Hsub _ _ _ eq_refl) as [C [D [kc [Heq [Hs1 [Hs2 Hk]]]]]].
  inversion Heq; subst. eapply T_Sub; [apply T_Protect; exact Ha | ].
  apply subtype_protect; [exact Hs1 | exact (proj2 Hk)].
Qed.

Lemma typing_project_right : forall a b k T1 T2 kt,
  has_type empty (tm_pair a b k) (Ty_Prod T1 T2 kt) ->
  has_type empty (tm_protect k.(indirect_reader) b) (ty_protect kt.(indirect_reader) T2).
Proof.
  intros a b k T1 T2 kt Hpair.
  destruct (typing_pair_inv _ _ _ Hpair _ _ _ eq_refl) as [A [B [Ha [Hb Hsub]]]].
  destruct (subtype_prod_inv _ _ Hsub _ _ _ eq_refl) as [C [D [kc [Heq [Hs1 [Hs2 Hk]]]]]].
  inversion Heq; subst. eapply T_Sub; [apply T_Protect; exact Hb | ].
  apply subtype_protect; [exact Hs2 | exact (proj2 Hk)].
Qed.

Lemma typing_case_left : forall a k T1 T2 kt body T L,
  has_type empty (tm_inl a k) (Ty_Sum T1 T2 kt) ->
  (forall x, ~ In x L -> has_type (update empty x T1) (open body (tm_fvar x)) T) ->
  has_type empty (tm_protect k.(indirect_reader) (open body a))
    (ty_protect kt.(indirect_reader) T).
Proof.
  intros a k T1 T2 kt body T L Hinj Hbody.
  destruct (typing_inl_inv _ _ _ Hinj _ _ eq_refl) as [A [B [Ha Hsub]]].
  destruct (subtype_sum_inv _ _ Hsub _ _ _ eq_refl) as [C [D [kc [Heq [Hs1 [Hs2 Hk]]]]]].
  inversion Heq; subst.
  assert (has_type empty (open body a) T) as Hopen.
  { eapply typing_open_closed; [exact Hbody | eapply T_Sub; eassumption]. }
  eapply T_Sub; [apply T_Protect; exact Hopen | ].
  apply subtype_protect; [apply subtype_refl; exact (proj2 (typing_regular _ _ _ Hopen)) | exact (proj2 Hk)].
Qed.

Lemma typing_case_right : forall a k T1 T2 kt body T L,
  has_type empty (tm_inr a k) (Ty_Sum T1 T2 kt) ->
  (forall x, ~ In x L -> has_type (update empty x T2) (open body (tm_fvar x)) T) ->
  has_type empty (tm_protect k.(indirect_reader) (open body a))
    (ty_protect kt.(indirect_reader) T).
Proof.
  intros a k T1 T2 kt body T L Hinj Hbody.
  destruct (typing_inr_inv _ _ _ Hinj _ _ eq_refl) as [A [B [Ha Hsub]]].
  destruct (subtype_sum_inv _ _ Hsub _ _ _ eq_refl) as [C [D [kc [Heq [Hs1 [Hs2 Hk]]]]]].
  inversion Heq; subst.
  assert (has_type empty (open body a) T) as Hopen.
  { eapply typing_open_closed; [exact Hbody | eapply T_Sub; eassumption]. }
  eapply T_Sub; [apply T_Protect; exact Hopen | ].
  apply subtype_protect; [apply subtype_refl; exact (proj2 (typing_regular _ _ _ Hopen)) | exact (proj2 Hk)].
Qed.

Lemma typing_nat_shape : forall Gamma t T, has_type Gamma t T ->
  forall n k, t = tm_nat n k -> exists kt, T = Ty_Nat kt /\ security_le k kt.
Proof.
  intros Gamma t T H. induction H; intros m kn Et; inversion Et; subst.
  - destruct (IHhas_type _ _ eq_refl) as [km [-> Hm]].
    destruct (subtype_nat_inv _ _ H0 _ eq_refl) as [ku [-> Hu]].
    exists ku. split; [reflexivity | eapply security_le_trans; eassumption].
  - exists kn. split; [reflexivity | apply security_le_refl].
Qed.

Lemma typing_nat_inv : forall Gamma n k kt,
  has_type Gamma (tm_nat n k) (Ty_Nat kt) -> security_le k kt.
Proof.
  intros Gamma n k kt H.
  destruct (typing_nat_shape _ _ _ H _ _ eq_refl) as [ku [E Hk]].
  inversion E; subst. exact Hk.
Qed.

Lemma typing_unroll : forall n Gamma b s T r,
  has_type Gamma b T ->
  has_type Gamma s (Ty_Arrow (Ty_Nat public) (Ty_Arrow T T public) public) ->
  has_type Gamma (natrec_unroll n b s r) T.
Proof.
  induction n; intros Gamma b s T r Hb Hs; simpl; [exact Hb |].
  rewrite <- (ty_protect_low T).
  eapply T_App with (T1 := T) (kappa := public).
  - change (has_type Gamma (tm_app s (tm_nat n public) r)
      (ty_protect Low (Ty_Arrow T T public))).
    eapply T_App with (T1 := Ty_Nat public) (kappa := public);
      [exact Hs | apply T_Nat; exact I | exact I].
  - apply IHn; assumption.
  - exact I.
Qed.

Lemma typing_if_protect_left : forall Gamma a k kt yes T,
  has_type Gamma (tm_inl a k) (Ty_Sum (Ty_Unit public) (Ty_Unit public) kt) ->
  has_type Gamma yes T ->
  has_type Gamma (tm_protect k.(indirect_reader) yes) (ty_protect kt.(indirect_reader) T).
Proof.
  intros Gamma a k kt yes T Hc Hy.
  destruct (typing_inl_inv _ _ _ Hc _ _ eq_refl) as [A [B [Ha Hsub]]].
  destruct (subtype_sum_inv _ _ Hsub _ _ _ eq_refl) as [C [D [kc [E [_ [_ Hk]]]]]].
  inversion E; subst. eapply T_Sub; [apply T_Protect; exact Hy |].
  apply subtype_protect; [apply subtype_refl; exact (proj2 (typing_regular _ _ _ Hy)) | exact (proj2 Hk)].
Qed.

Lemma typing_if_protect_right : forall Gamma a k kt no T,
  has_type Gamma (tm_inr a k) (Ty_Sum (Ty_Unit public) (Ty_Unit public) kt) ->
  has_type Gamma no T ->
  has_type Gamma (tm_protect k.(indirect_reader) no) (ty_protect kt.(indirect_reader) T).
Proof.
  intros Gamma a k kt no T Hc Hn.
  destruct (typing_inr_inv _ _ _ Hc _ _ eq_refl) as [A [B [Ha Hsub]]].
  destruct (subtype_sum_inv _ _ Hsub _ _ _ eq_refl) as [C [D [kc [E [_ [_ Hk]]]]]].
  inversion E; subst. eapply T_Sub; [apply T_Protect; exact Hn |].
  apply subtype_protect; [apply subtype_refl; exact (proj2 (typing_regular _ _ _ Hn)) | exact (proj2 Hk)].
Qed.

Theorem preservation : forall t T,
  has_type empty t T -> forall t', step t t' -> has_type empty t' T.
Proof.
  intros t T Htyped. remember empty as Gamma eqn:Hempty.
  induction Htyped; intros t' Hstep; subst Gamma;
    try solve [inversion Hstep];
    try solve [eapply T_Sub; [eapply IHHtyped; [reflexivity | exact Hstep] | exact H]].
  all: inversion Hstep; subst;
    eauto using typing_beta, typing_project_left, typing_project_right,
      typing_case_left, typing_case_right, typing_protect_value,
      typing_if_protect_left, typing_if_protect_right, T_If,
      T_App, T_Pair, T_Fst, T_Snd, T_Inl, T_Inr, T_Protect, T_Succ, T_NatRec.
  - eapply T_Case with (L := L); eauto.
  - eapply T_Sub.
    + apply T_Protect. apply T_Nat. exact I.
    + apply subtype_protect; [apply subtype_refl; exact I |].
      exact (proj2 (typing_nat_inv _ _ _ _ Htyped)).
  - eapply T_Sub.
    + apply T_Protect. apply typing_unroll; eassumption.
    + apply subtype_protect.
      * apply subtype_refl. exact (proj2 (typing_regular _ _ _ Htyped2)).
      * exact (proj2 (typing_nat_inv _ _ _ _ Htyped1)).
Qed.

Lemma preservation_multi : forall t t' T,
  t -->* t' -> has_type empty t T -> has_type empty t' T.
Proof.
  intros t t' T Hmulti. induction Hmulti; intros Htyped.
  - exact Htyped.
  - apply IHHmulti. eapply preservation; eassumption.
Qed.

Definition erase_context (Gamma : context) : context :=
  map (fun entry => (fst entry, erase_type (snd entry))) Gamma.

Lemma erase_type_wf : forall T, wf_ty (erase_type T).
Proof. induction T; simpl; repeat split; auto; exact I. Qed.

Lemma erase_ty_protect : forall T l, erase_type (ty_protect l T) = erase_type T.
Proof. destruct T; reflexivity. Qed.

Lemma lookup_erase_context : forall Gamma x T,
  lookup_context x Gamma = Some T -> lookup_context x (erase_context Gamma) = Some (erase_type T).
Proof.
  induction Gamma as [ | [y U] Gamma IH]; intros x T H; simpl in *; [discriminate H | ].
  destruct (Nat.eqb x y); [inversion H; reflexivity | apply IH; exact H].
Qed.

Lemma erase_open_rec : forall t k u,
  erase_security (open_rec k u t) = open_rec k (erase_security u) (erase_security t).
Proof.
  induction t; intros k u; simpl; try reflexivity;
    try (f_equal; eauto).
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma typing_erasure : forall Gamma t T,
  has_type Gamma t T -> has_type (erase_context Gamma) (erase_security t) (erase_type T).
Proof.
  intros Gamma t T Htyped. induction Htyped; simpl.
  - apply T_Var; [apply lookup_erase_context; exact H | apply erase_type_wf].
  - apply T_Unit; exact I.
  - apply T_Abs with (L := L); [apply erase_type_wf | exact I | ].
    intros x Hx. specialize (H2 x Hx). unfold open in *.
    rewrite erase_open_rec in H2. exact H2.
  - rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type T2)) at 1.
    eapply T_App with (kappa := public); [exact IHHtyped1 | exact IHHtyped2 | exact I].
  - apply T_Pair; [exact IHHtyped1 | exact IHHtyped2 | exact I].
  - rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type T1)) at 1.
    eapply T_Fst with (kappa := public); [exact IHHtyped | exact I].
  - rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type T2)) at 1.
    eapply T_Snd with (kappa := public); [exact IHHtyped | exact I].
  - apply T_Inl; [exact IHHtyped | apply erase_type_wf | exact I].
  - apply T_Inr; [apply erase_type_wf | exact IHHtyped | exact I].
  - rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type T)) at 1.
    eapply T_Case with (L := L) (kappa := public); [exact IHHtyped | exact I | | ].
    + intros x Hx. specialize (H1 x Hx). unfold open in *. rewrite erase_open_rec in H1. exact H1.
    + intros x Hx. specialize (H3 x Hx). unfold open in *. rewrite erase_open_rec in H3. exact H3.
  - rewrite erase_ty_protect. exact IHHtyped.
  - rewrite <- (subtype_erasure _ _ H). exact IHHtyped.
  - apply T_Nat. exact I.
  - change (has_type (erase_context Gamma) (tm_succ (erase_security t) Low)
      (ty_protect Low (Ty_Nat public))).
    eapply T_Succ with (k := public); [exact IHHtyped | exact I].
  - rewrite erase_ty_protect. rewrite <- (ty_protect_low (erase_type T)) at 1.
    eapply T_NatRec with (k := public);
      [exact IHHtyped1 | exact IHHtyped2 | exact IHHtyped3 | exact I].
  - rewrite erase_ty_protect. rewrite <- (ty_protect_low (erase_type T)) at 1.
    eapply T_If with (k := public); [exact IHHtyped1 | exact IHHtyped2 | exact IHHtyped3 | exact I].
Qed.

Lemma erase_lc_at : forall t k, lc_at k t -> lc_at k (erase_security t).
Proof.
  induction t; intros k H; simpl in *; intuition eauto.
Qed.

Lemma protect_value_low : forall v, protect_value v Low = v.
Proof.
  destruct v; simpl; try reflexivity;
    match goal with k : security |- _ => destruct k as [r ir] end;
    destruct r, ir; reflexivity.
Qed.

Lemma erase_unroll : forall n b s r,
  erase_security (natrec_unroll n b s r) =
  natrec_unroll n (erase_security b) (erase_security s) Low.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma big_step_erasure : forall t v,
  big_step t v -> big_step (erase_security t) (erase_security v).
Proof.
  intros t v Heval. induction Heval; simpl.
  - apply B_Unit.
  - apply B_Abs. apply erase_lc_at; exact H.
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security w)).
    eapply B_App with (k := public);
      [exact IHHeval1 | exact IHHeval2 | exact I |].
    unfold open in *. rewrite <- erase_open_rec. exact IHHeval3.
  - apply B_Pair; assumption.
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security a)).
    eapply B_Fst with (k := public); [exact IHHeval | exact I].
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security b)).
    eapply B_Snd with (k := public); [exact IHHeval | exact I].
  - apply B_Inl; assumption.
  - apply B_Inr; assumption.
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security w)).
    eapply B_CaseLeft with (k := public);
      [exact IHHeval1 | exact I |].
    unfold open in *. rewrite <- erase_open_rec. exact IHHeval2.
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security w)).
    eapply B_CaseRight with (k := public);
      [exact IHHeval1 | exact I |].
    unfold open in *. rewrite <- erase_open_rec. exact IHHeval2.
  - rewrite erase_protect_value. exact IHHeval.
  - apply B_Nat.
  - change (big_step (tm_succ (erase_security t) Low)
      (protect_value (tm_nat (S n) public) Low)).
    eapply B_Succ with (k := public); [exact IHHeval | exact I].
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security result)).
    eapply B_NatRec with (k := public).
    + exact IHHeval1.
    + exact IHHeval2.
    + exact IHHeval3.
    + exact I.
    + rewrite <- erase_unroll with (r := r). exact IHHeval4.
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security result)).
    eapply B_IfTrue with (k := public); [exact IHHeval1 | exact I | exact IHHeval2].
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security result)).
    eapply B_IfFalse with (k := public); [exact IHHeval1 | exact I | exact IHHeval2].
Qed.

Lemma evaluates_erasure : forall t v,
  evaluates t v -> evaluates (erase_security t) (erase_security v).
Proof.
  intros t v H. apply big_step_iff_evaluates.
  apply big_step_erasure. apply big_step_iff_evaluates. exact H.
Qed.

Definition term_substitution := atom -> tm.

Fixpoint instantiate (rho : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit k => tm_unit k
  | tm_abs T body k => tm_abs T (instantiate rho body) k
  | tm_app t1 t2 r => tm_app (instantiate rho t1) (instantiate rho t2) r
  | tm_pair t1 t2 k => tm_pair (instantiate rho t1) (instantiate rho t2) k
  | tm_fst t r => tm_fst (instantiate rho t) r
  | tm_snd t r => tm_snd (instantiate rho t) r
  | tm_inl t k => tm_inl (instantiate rho t) k
  | tm_inr t k => tm_inr (instantiate rho t) k
  | tm_case t b1 b2 r => tm_case (instantiate rho t)
      (instantiate rho b1) (instantiate rho b2) r
  | tm_protect l t => tm_protect l (instantiate rho t)
  | tm_if c yes no r => tm_if (instantiate rho c) (instantiate rho yes) (instantiate rho no) r
  | tm_nat n k => tm_nat n k
  | tm_succ t r => tm_succ (instantiate rho t) r
  | tm_natrec n b s r => tm_natrec (instantiate rho n) (instantiate rho b) (instantiate rho s) r
  end.

Definition substitution_update (rho : term_substitution) (x : atom) (u : tm)
    : term_substitution := fun y => if Nat.eqb x y then u else rho y.

Lemma fv_open_includes : forall t k u x,
  In x (fv t) -> In x (fv (open_rec k u t)).
Proof.
  induction t; intros k u x H; simpl in *; try contradiction;
    repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma lookup_context_key : forall Gamma x T,
  lookup_context x Gamma = Some T -> In x (map fst Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T H; simpl in *; [discriminate |].
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. auto.
  - right. eapply IH; exact H.
Qed.

Lemma context_included_fresh_update : forall Gamma x T,
  ~ In x (map fst Gamma) -> context_included Gamma (update Gamma x T).
Proof.
  intros Gamma x T Hfresh y U Hlookup.
  rewrite lookup_update_neq; [exact Hlookup |].
  intro E. subst y. apply Hfresh. eapply lookup_context_key; exact Hlookup.
Qed.

Lemma typing_substitution_update : forall Gamma Gamma' rho x A,
  (forall y U, lookup_context y Gamma = Some U -> has_type Gamma' (rho y) U) ->
  ~ In x (map fst Gamma') -> wf_ty A ->
  forall y U, lookup_context y (update Gamma x A) = Some U ->
  has_type (update Gamma' x A) (substitution_update rho x (tm_fvar x) y) U.
Proof.
  intros Gamma Gamma' rho x A Hmap Hfresh Hwf y U Hlookup.
  unfold substitution_update. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite lookup_update_eq in Hlookup.
    inversion Hlookup; subst U. apply T_Var; [apply lookup_update_eq | exact Hwf].
  - apply Nat.eqb_neq in E. rewrite lookup_update_neq in Hlookup by congruence.
    eapply typing_weaken; [apply Hmap; exact Hlookup |].
    apply context_included_fresh_update; exact Hfresh.
Qed.

Lemma typing_free_variable : forall Gamma t T,
  has_type Gamma t T -> forall x, In x (fv t) ->
  exists U, lookup_context x Gamma = Some U.
Proof.
  intros Gamma t T Ht. induction Ht; intros z Hz; simpl in Hz;
    repeat rewrite in_app_iff in Hz; try contradiction; try solve [intuition eauto].
  - destruct Hz as [<- | []]. eauto.
  - destruct (fresh_atom (z :: L)) as [x Hx].
    assert (x <> z /\ ~ In x L) as [Hneq Hfresh] by (simpl in Hx; intuition congruence).
    destruct (H2 x Hfresh z (fv_open_includes _ 0 _ _ Hz)) as [U HU].
    rewrite lookup_update_neq in HU by congruence. eauto.
  - destruct Hz as [Hz | [Hz | Hz]].
    + eauto.
    + destruct (fresh_atom (z :: L)) as [x Hx].
      assert (x <> z /\ ~ In x L) as [Hneq Hfresh] by (simpl in Hx; intuition congruence).
      destruct (H1 x Hfresh z (fv_open_includes _ 0 _ _ Hz)) as [U HU].
      rewrite lookup_update_neq in HU by congruence. eauto.
    + destruct (fresh_atom (z :: L)) as [x Hx].
      assert (x <> z /\ ~ In x L) as [Hneq Hfresh] by (simpl in Hx; intuition congruence).
      destruct (H3 x Hfresh z (fv_open_includes _ 0 _ _ Hz)) as [U HU].
      rewrite lookup_update_neq in HU by congruence. eauto.
Qed.

Lemma instantiate_ext : forall t rho sigma,
  (forall x, In x (fv t) -> rho x = sigma x) ->
  instantiate rho t = instantiate sigma t.
Proof.
  induction t; intros rho sigma H; simpl in *; try reflexivity;
    try (f_equal; apply IHt; exact H);
    try (f_equal; [apply IHt1 | apply IHt2]);
    try (f_equal; [apply IHt1 | apply IHt2 | apply IHt3]);
    try (intros x Hx; apply H; repeat rewrite in_app_iff; tauto).
  apply H. auto.
Qed.

Lemma instantiate_open : forall t rho k u,
  (forall x, In x (fv t) -> locally_closed (rho x)) ->
  instantiate rho (open_rec k u t) = open_rec k (instantiate rho u) (instantiate rho t).
Proof.
  induction t; intros rho k u H; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply (open_rec_lc_at (rho a) 0 k (instantiate rho u)).
    + apply H. auto.
    + apply Nat.le_0_l.
  - f_equal. apply IHt; exact H.
  - f_equal; [apply IHt1 | apply IHt2]; intros x Hx;
      apply H; rewrite in_app_iff; tauto.
  - f_equal; [apply IHt1 | apply IHt2]; intros x Hx;
      apply H; rewrite in_app_iff; tauto.
  - f_equal. apply IHt; exact H.
  - f_equal. apply IHt; exact H.
  - f_equal. apply IHt; exact H.
  - f_equal. apply IHt; exact H.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; intros x Hx;
      apply H; repeat rewrite in_app_iff; tauto.
  - f_equal. apply IHt; exact H.
  - f_equal. apply IHt; exact H.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; intros x Hx;
      apply H; repeat rewrite in_app_iff; tauto.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; intros x Hx;
      apply H; repeat rewrite in_app_iff; tauto.
Qed.

Lemma instantiate_open_update : forall body rho x u,
  ~ In x (fv body) ->
  (forall y, In y (fv body) -> locally_closed (rho y)) ->
  instantiate (substitution_update rho x u) (open body (tm_fvar x)) =
  open (instantiate rho body) u.
Proof.
  intros body rho x u Hfresh Hlc. unfold open.
  rewrite instantiate_open.
  - simpl. unfold substitution_update at 1. rewrite Nat.eqb_refl.
    f_equal. apply instantiate_ext. intros y Hy.
    unfold substitution_update. destruct (Nat.eqb x y) eqn:E; [|reflexivity].
    apply Nat.eqb_eq in E. subst y. contradiction.
  - intros y Hy. unfold substitution_update. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. contradiction.
    + apply Hlc; exact Hy.
Qed.

Lemma typing_substitution_lc : forall Gamma t T Gamma' rho,
  has_type Gamma t T ->
  (forall x U, lookup_context x Gamma = Some U -> has_type Gamma' (rho x) U) ->
  forall x, In x (fv t) -> locally_closed (rho x).
Proof.
  intros Gamma t T Gamma' rho Ht Hmap x Hx.
  destruct (typing_free_variable _ _ _ Ht x Hx) as [U HU].
  exact (proj1 (typing_regular _ _ _ (Hmap x U HU))).
Qed.

Lemma typing_instantiate : forall Gamma t T,
  has_type Gamma t T -> forall Gamma' rho,
  (forall x U, lookup_context x Gamma = Some U -> has_type Gamma' (rho x) U) ->
  has_type Gamma' (instantiate rho t) T.
Proof.
  intros Gamma t T Ht. induction Ht; intros Gamma' rho Hmap; simpl.
  - apply Hmap; exact H.
  - apply T_Unit; exact H.
  - apply T_Abs with (L := L ++ fv body ++ map fst Gamma'); try assumption.
    intros x Hfresh. repeat rewrite in_app_iff in Hfresh.
    rewrite <- instantiate_open_update with (x := x) by
      (first [tauto | eapply typing_substitution_lc with
        (t := tm_abs T1 body kappa) (T := Ty_Arrow T1 T2 kappa);
        [eapply T_Abs; eassumption | exact Hmap]]).
    apply H2; [tauto |]. apply typing_substitution_update; tauto.
  - eapply T_App; eauto.
  - apply T_Pair; eauto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
  - apply T_Inl; eauto.
  - apply T_Inr; eauto.
  - eapply T_Case with (L := L ++ fv body1 ++ fv body2 ++ map fst Gamma');
      [eapply IHHt; exact Hmap | exact H | |].
    + intros x Hfresh. repeat rewrite in_app_iff in Hfresh.
      rewrite <- instantiate_open_update with (x := x) by
        (first [tauto | intros y Hy; eapply typing_substitution_lc with
          (t := tm_case t body1 body2 r) (T := ty_protect kappa.(indirect_reader) T);
          [eapply T_Case; eassumption | exact Hmap | simpl; repeat rewrite in_app_iff; tauto]]).
      apply H1; [tauto |]. apply typing_substitution_update; try tauto.
      exact (proj1 (proj2 (typing_regular _ _ _ Ht))).
    + intros x Hfresh. repeat rewrite in_app_iff in Hfresh.
      rewrite <- instantiate_open_update with (x := x) by
        (first [tauto | intros y Hy; eapply typing_substitution_lc with
          (t := tm_case t body1 body2 r) (T := ty_protect kappa.(indirect_reader) T);
          [eapply T_Case; eassumption | exact Hmap | simpl; repeat rewrite in_app_iff; tauto]]).
      apply H3; [tauto |]. apply typing_substitution_update; try tauto.
      exact (proj1 (proj2 (proj2 (typing_regular _ _ _ Ht)))).
  - apply T_Protect; eauto.
  - eapply T_Sub; eauto.
  - apply T_Nat; assumption.
  - eapply T_Succ; eauto.
  - eapply T_NatRec; eauto.
  - eapply T_If; eauto.
Qed.

Lemma erase_instantiate : forall t rho,
  erase_security (instantiate rho t) =
  instantiate (fun x => erase_security (rho x)) (erase_security t).
Proof. induction t; intros rho; simpl; f_equal; auto. Qed.

Lemma lookup_erase_context_inv : forall Gamma x U,
  lookup_context x (erase_context Gamma) = Some U ->
  exists T, lookup_context x Gamma = Some T /\ U = erase_type T.
Proof.
  induction Gamma as [|[y T] Gamma IH]; intros x U H; simpl in *; [discriminate |].
  destruct (Nat.eqb x y); [inversion H; subst; eauto | apply IH; exact H].
Qed.

Lemma typing_instantiate_erased : forall Gamma t T rho,
  has_type Gamma t T ->
  (forall x U, lookup_context x Gamma = Some U ->
    has_type empty (erase_security (rho x)) (erase_type U)) ->
  has_type empty (erase_security (instantiate rho t)) (erase_type T).
Proof.
  intros Gamma t T rho Ht Hmap. rewrite erase_instantiate.
  eapply typing_instantiate; [apply typing_erasure; exact Ht |].
  intros x U HU. destruct (lookup_erase_context_inv _ _ _ HU) as [V [HV ->]].
  apply Hmap; exact HV.
Qed.

Lemma erase_lc_inv : forall t k, lc_at k (erase_security t) -> lc_at k t.
Proof. induction t; intros k H; simpl in *; intuition eauto. Qed.

Definition expression_lifting (R : tm -> tm -> Prop) (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm, evaluates t1 v1 -> evaluates t2 v2 -> R v1 v2.

Definition underlying_typed (T : ty) (t : tm) : Prop :=
  has_type empty (erase_security t) (erase_type T).

Fixpoint value_relation (observer : label) (T : ty) (v1 v2 : tm) : Prop :=
  value v1 /\ value v2 /\
  underlying_typed T v1 /\ underlying_typed T v2 /\
  (flows_to (security_of T).(indirect_reader) observer ->
    match T with
    | Ty_Unit _ =>
        exists kappa1 kappa2 : security,
          v1 = tm_unit kappa1 /\ v2 = tm_unit kappa2
    | Ty_Sum T1 T2 _ =>
        (exists (u1 u2 : tm) (kappa1 kappa2 : security),
          v1 = tm_inl u1 kappa1 /\ v2 = tm_inl u2 kappa2 /\
          value_relation observer T1 u1 u2) \/
        (exists (u1 u2 : tm) (kappa1 kappa2 : security),
          v1 = tm_inr u1 kappa1 /\ v2 = tm_inr u2 kappa2 /\
          value_relation observer T2 u1 u2)
    | Ty_Prod T1 T2 _ =>
        exists (a1 b1 a2 b2 : tm) (kappa1 kappa2 : security),
          v1 = tm_pair a1 b1 kappa1 /\ v2 = tm_pair a2 b2 kappa2 /\
          value_relation observer T1 a1 a2 /\
          value_relation observer T2 b1 b2
    | Ty_Arrow T1 T2 _ =>
        exists (U1 U2 : ty) (body1 body2 : tm) (kappa1 kappa2 : security),
          v1 = tm_abs U1 body1 kappa1 /\ v2 = tm_abs U2 body2 kappa2 /\
          forall arg1 arg2 : tm,
            value_relation observer T1 arg1 arg2 ->
            expression_lifting (value_relation observer T2)
              (tm_app v1 arg1 High) (tm_app v2 arg2 High)
    | Ty_Nat _ => exists n k1 k2, v1 = tm_nat n k1 /\ v2 = tm_nat n k2
    end).

Definition expression_relation (observer : label) (T : ty) (t1 t2 : tm) : Prop :=
  underlying_typed T t1 /\ underlying_typed T t2 /\
  expression_lifting (value_relation observer T) t1 t2.

Lemma value_relation_properties : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  value v1 /\ value v2 /\ underlying_typed T v1 /\ underlying_typed T v2.
Proof. intros observer T. destruct T; simpl; tauto. Qed.

Lemma underlying_typed_evaluates : forall T t v,
  underlying_typed T t -> evaluates t v -> underlying_typed T v.
Proof.
  intros T t v Ht Heval. unfold underlying_typed in *.
  destruct (evaluates_erasure _ _ Heval) as [Hsteps _].
  eapply preservation_multi; eassumption.
Qed.

Lemma flows_to_dec : forall l observer,
  {flows_to l observer} + {~ flows_to l observer}.
Proof. destruct l, observer; simpl; auto. Defined.

Lemma related_values_are_related_expressions : forall observer T v1 v2,
  value_relation observer T v1 v2 -> expression_relation observer T v1 v2.
Proof.
  intros observer T v1 v2 Hrelated.
  destruct (value_relation_properties _ _ _ _ Hrelated) as [Hv1 [Hv2 [Ht1 Ht2]]].
  split; [exact Ht1 | ]. split; [exact Ht2 | ].
  intros u1 u2 [Hsteps1 _] [Hsteps2 _].
  apply (value_multi_inv _ _ Hv1) in Hsteps1.
  apply (value_multi_inv _ _ Hv2) in Hsteps2.
  subst u1 u2. exact Hrelated.
Qed.

Definition related_expression_substitutions
    (observer : label) (Gamma : context) (rho1 rho2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    expression_relation observer T (rho1 x) (rho2 x).

Lemma related_expression_update : forall observer Gamma rho1 rho2 x T v1 v2,
  related_expression_substitutions observer Gamma rho1 rho2 ->
  value_relation observer T v1 v2 ->
  related_expression_substitutions observer (update Gamma x T)
    (substitution_update rho1 x v1) (substitution_update rho2 x v2).
Proof.
  intros observer Gamma rho1 rho2 x T v1 v2 Henv Hv y U HU.
  unfold substitution_update. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite lookup_update_eq in HU.
    inversion HU; subst U. apply related_values_are_related_expressions; exact Hv.
  - apply Nat.eqb_neq in E. rewrite lookup_update_neq in HU by congruence.
    apply Henv; exact HU.
Qed.

Lemma related_instantiations_typed : forall Gamma t T observer rho1 rho2,
  has_type Gamma t T -> related_expression_substitutions observer Gamma rho1 rho2 ->
  underlying_typed T (instantiate rho1 t) /\ underlying_typed T (instantiate rho2 t).
Proof.
  intros Gamma t T observer rho1 rho2 Ht Henv.
  split; apply typing_instantiate_erased with (Gamma := Gamma); try exact Ht;
    intros x U HU; specialize (Henv x U HU); destruct Henv as [H1 [H2 _]]; assumption.
Qed.

Lemma related_substitution_lc : forall Gamma t T observer rho1 rho2,
  has_type Gamma t T -> related_expression_substitutions observer Gamma rho1 rho2 ->
  forall x, In x (fv t) -> locally_closed (rho1 x) /\ locally_closed (rho2 x).
Proof.
  intros Gamma t T observer rho1 rho2 Ht Henv x Hx.
  destruct (typing_free_variable _ _ _ Ht x Hx) as [U HU].
  destruct (Henv x U HU) as [H1 [H2 _]].
  split; apply erase_lc_inv; [exact (proj1 (typing_regular _ _ _ H1)) |
    exact (proj1 (typing_regular _ _ _ H2))].
Qed.


(* Optional reference theorem statement.
Theorem fundamental_expressions : forall Gamma t T,
  has_type Gamma t T ->
  forall observer rho1 rho2,
    related_expression_substitutions observer Gamma rho1 rho2 ->
    expression_relation observer T (instantiate rho1 t) (instantiate rho2 t).
*)


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
  | C_Protect : label -> program_context -> program_context
  | C_Succ : program_context -> label -> program_context
  | C_RecArg : program_context -> tm -> tm -> label -> program_context
  | C_RecBase : tm -> program_context -> tm -> label -> program_context
  | C_RecStep : tm -> tm -> program_context -> label -> program_context
  | C_IfCondition : program_context -> tm -> tm -> label -> program_context
  | C_IfThen : tm -> program_context -> tm -> label -> program_context
  | C_IfElse : tm -> tm -> program_context -> label -> program_context.

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
  | C_IfCondition C' y n r => tm_if (plug C' t) y n r
  | C_IfThen c C' n r => tm_if c (plug C' t) n r
  | C_IfElse c y C' r => tm_if c y (plug C' t) r
  | C_Succ C' r => tm_succ (plug C' t) r
  | C_RecArg C' b s r => tm_natrec (plug C' t) b s r
  | C_RecBase n C' s r => tm_natrec n (plug C' t) s r
  | C_RecStep n b C' r => tm_natrec n b (plug C' t) r
  end.

Fixpoint context_support (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ | C_Fst C' _ | C_Snd C' _ | C_Inl C' _ | C_Inr C' _
  | C_Protect _ C' | C_Succ C' _ => context_support C'
  | C_AppLeft C' t _ | C_PairLeft C' t _ => context_support C' ++ fv t
  | C_AppRight t C' _ | C_PairRight t C' _ => fv t ++ context_support C'
  | C_CaseScrutinee C' t1 t2 _ | C_IfCondition C' t1 t2 _ =>
      context_support C' ++ fv t1 ++ fv t2
  | C_CaseLeft t0 C' t2 _ | C_IfThen t0 C' t2 _ =>
      fv t0 ++ context_support C' ++ fv t2
  | C_CaseRight t0 t1 C' _ | C_IfElse t0 t1 C' _ =>
      fv t0 ++ fv t1 ++ context_support C'
  | C_RecArg C' b s _ => context_support C' ++ fv b ++ fv s
  | C_RecBase n C' s _ => fv n ++ context_support C' ++ fv s
  | C_RecStep n b C' _ => fv n ++ fv b ++ context_support C'
  end.

Fixpoint instantiate_context (rho : term_substitution) (C : program_context) : program_context :=
  match C with
  | C_Hole => C_Hole
  | C_Abs T C' k => C_Abs T (instantiate_context rho C') k
  | C_AppLeft C' t r => C_AppLeft (instantiate_context rho C') (instantiate rho t) r
  | C_AppRight t C' r => C_AppRight (instantiate rho t) (instantiate_context rho C') r
  | C_PairLeft C' t k => C_PairLeft (instantiate_context rho C') (instantiate rho t) k
  | C_PairRight t C' k => C_PairRight (instantiate rho t) (instantiate_context rho C') k
  | C_Fst C' r => C_Fst (instantiate_context rho C') r
  | C_Snd C' r => C_Snd (instantiate_context rho C') r
  | C_Inl C' k => C_Inl (instantiate_context rho C') k
  | C_Inr C' k => C_Inr (instantiate_context rho C') k
  | C_CaseScrutinee C' b1 b2 r => C_CaseScrutinee (instantiate_context rho C') (instantiate rho b1) (instantiate rho b2) r
  | C_CaseLeft t0 C' b2 r => C_CaseLeft (instantiate rho t0) (instantiate_context rho C') (instantiate rho b2) r
  | C_CaseRight t0 b1 C' r => C_CaseRight (instantiate rho t0) (instantiate rho b1) (instantiate_context rho C') r
  | C_Protect l C' => C_Protect l (instantiate_context rho C')
  | C_Succ C' r => C_Succ (instantiate_context rho C') r
  | C_RecArg C' b s r => C_RecArg (instantiate_context rho C') (instantiate rho b) (instantiate rho s) r
  | C_RecBase n C' s r => C_RecBase (instantiate rho n) (instantiate_context rho C') (instantiate rho s) r
  | C_RecStep n b C' r => C_RecStep (instantiate rho n) (instantiate rho b) (instantiate_context rho C') r
  | C_IfCondition C' y n r => C_IfCondition (instantiate_context rho C') (instantiate rho y) (instantiate rho n) r
  | C_IfThen c C' n r => C_IfThen (instantiate rho c) (instantiate_context rho C') (instantiate rho n) r
  | C_IfElse c y C' r => C_IfElse (instantiate rho c) (instantiate rho y) (instantiate_context rho C') r
  end.

Lemma instantiate_context_plug : forall C t rho,
  instantiate rho (plug C t) = plug (instantiate_context rho C) (instantiate rho t).
Proof. induction C; intros u rho; simpl; f_equal; eauto. Qed.

Lemma instantiate_identity : forall t,
  instantiate (fun y => tm_fvar y) t = t.
Proof. induction t; simpl; f_equal; eauto. Qed.

Lemma instantiate_update_fresh : forall t x u,
  ~ In x (fv t) ->
  instantiate (substitution_update (fun y => tm_fvar y) x u) t = t.
Proof.
  intros t x u Hfresh. rewrite <- instantiate_identity.
  eapply instantiate_ext with (sigma := fun y => tm_fvar y). intros y Hy.
  unfold substitution_update. destruct (Nat.eqb x y) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. subst y. contradiction.
Qed.

Lemma instantiate_context_identity : forall C x u,
  ~ In x (context_support C) ->
  instantiate_context (substitution_update (fun y => tm_fvar y) x u) C = C.
Proof.
  induction C; intros x u Hfresh; simpl in *; f_equal; try apply IHC;
    try (apply instantiate_update_fresh; intro Hin; apply Hfresh; simpl; repeat rewrite in_app_iff; tauto).
  all: try reflexivity.
  all: intro Hin; apply Hfresh; simpl in *; repeat rewrite in_app_iff; tauto.
Qed.

Definition context_has_type (C : program_context) (T_hole T_result : ty) : Prop :=
  exists L : list atom, forall x : atom, ~ In x L ->
    has_type (update empty x T_hole) (plug C (tm_fvar x)) T_result.

Fixpoint ground (T : ty) : Prop :=
  match T with
  | Ty_Unit _ | Ty_Nat _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ => ground T1 /\ ground T2
  | Ty_Arrow _ _ _ => False
  end.

Fixpoint transparent_at (kappa : security) (T : ty) : Prop :=
  security_le (security_of T) kappa /\
  match T with
  | Ty_Unit _ | Ty_Nat _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      transparent_at kappa T1 /\ transparent_at kappa T2
  end.

Definition transparent (T : ty) : Prop := transparent_at (security_of T) T.

Lemma transparent_at_security : forall kappa T,
  transparent_at kappa T -> security_le (security_of T) kappa.
Proof. intros kappa T; destruct T; simpl; tauto. Qed.

Definition same_result (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm,
    evaluates t1 v1 -> evaluates t2 v2 ->
    erase_security v1 = erase_security v2.

Lemma observable_related_values_equal_at : forall observer kappa T v1 v2,
  ground T -> transparent_at kappa T ->
  security_le (security_of T) kappa -> flows_to kappa.(indirect_reader) observer ->
  value_relation observer T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  intros observer kappa T. induction T; intros v1 v2 Hground Htransparent Hsec Hobserve Hrel;
    simpl in *.
  - destruct Hrel as [_ [_ [_ [_ Hrel]]]].
    destruct (Hrel (flows_to_trans _ _ _ (proj2 Hsec) Hobserve)) as [k1 [k2 [-> ->]]]. reflexivity.
  - destruct Hground as [G1 G2].
    destruct Htransparent as [_ [Htr1 Htr2]].
    destruct Hrel as [_ [_ [_ [_ Hrel]]]].
    destruct (Hrel (flows_to_trans _ _ _ (proj2 Hsec) Hobserve)) as
      [[u1 [u2 [k1 [k2 [-> [-> Hvalues]]]]]] |
       [u1 [u2 [k1 [k2 [-> [-> Hvalues]]]]]]].
    + simpl. f_equal. eapply IHT1; [exact G1 | exact Htr1 | apply transparent_at_security; exact Htr1 | exact Hobserve | exact Hvalues].
    + simpl. f_equal. eapply IHT2; [exact G2 | exact Htr2 | apply transparent_at_security; exact Htr2 | exact Hobserve | exact Hvalues].
  - destruct Hground as [G1 G2].
    destruct Htransparent as [_ [Htr1 Htr2]].
    destruct Hrel as [_ [_ [_ [_ Hrel]]]].
    destruct (Hrel (flows_to_trans _ _ _ (proj2 Hsec) Hobserve)) as
      [a1 [b1 [a2 [b2 [k1 [k2 [-> [-> [Ha Hb]]]]]]]]].
    simpl. f_equal.
    + eapply IHT1; [exact G1 | exact Htr1 | apply transparent_at_security; exact Htr1 | exact Hobserve | exact Ha].
    + eapply IHT2; [exact G2 | exact Htr2 | apply transparent_at_security; exact Htr2 | exact Hobserve | exact Hb].
  - contradiction.
  - destruct Hrel as [_ [_ [_ [_ Hrel]]]].
    destruct (Hrel (flows_to_trans _ _ _ (proj2 Hsec) Hobserve)) as [n [k1 [k2 [-> ->]]]]. reflexivity.
Qed.

Lemma observable_related_values_equal : forall observer T v1 v2,
  ground T -> transparent T ->
  flows_to (security_of T).(indirect_reader) observer ->
  value_relation observer T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  intros observer T v1 v2 Hground Htransparent Hobserve Hrel.
  unfold transparent in Htransparent.
  eapply observable_related_values_equal_at; eauto using security_le_refl.
Qed.

Lemma opaque_typed_inputs_related : forall observer T t1 t2,
  has_type empty t1 T -> has_type empty t2 T ->
  ~ flows_to (security_of T).(indirect_reader) observer ->
  expression_relation observer T t1 t2.
Proof.
  intros observer T. induction T; intros t1 t2 Ht1 Ht2 Hopaque.
  all: simpl in *.
  all: unfold expression_relation; split;
    [ unfold underlying_typed; exact (typing_erasure _ _ _ Ht1) | idtac ].
  all: split;
    [ unfold underlying_typed; exact (typing_erasure _ _ _ Ht2) | idtac ].
  all: intros v1 v2 [Hs1 Hv1] [Hs2 Hv2].
  all: unfold value_relation; simpl; repeat split; try assumption.
  all: try (eapply underlying_typed_evaluates;
    [unfold underlying_typed; exact (typing_erasure _ _ _ Ht1) | split; assumption]).
  all: try (eapply underlying_typed_evaluates;
    [unfold underlying_typed; exact (typing_erasure _ _ _ Ht2) | split; assumption]).
  all: intros Hflow; contradiction.
Qed.

Lemma value_relation_protect_invariant : forall observer T v1 v2 l,
  value_relation observer T v1 v2 ->
  value_relation observer T (protect_value v1 l) (protect_value v2 l).
Proof.
  intros observer T. induction T; intros v1 v2 l Hrel.
  all: unfold value_relation in *; simpl in *.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape Hobs) as [k1 [k2 [-> ->]]].
      exists (protect_security k1 l), (protect_security k2 l). simpl. auto.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape Hobs) as [Hleft | Hright].
      * destruct Hleft as [u1 [u2 [k1 [k2 [-> [-> Hchild]]]]]].
        left. exists u1, u2, (protect_security k1 l), (protect_security k2 l).
        simpl. repeat split; try reflexivity; assumption.
      * destruct Hright as [u1 [u2 [k1 [k2 [-> [-> Hchild]]]]]].
        right. exists u1, u2, (protect_security k1 l), (protect_security k2 l).
        simpl. repeat split; try reflexivity; assumption.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape Hobs) as
        [a1 [b1 [a2 [b2 [k1 [k2 [-> [-> [Ha Hb]]]]]]]]].
      exists a1, b1, a2, b2, (protect_security k1 l), (protect_security k2 l).
      simpl. repeat split; try reflexivity; assumption.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape Hobs) as [U1 [U2 [b1 [b2 [k1 [k2 [E1 [E2 Hext]]]]]]]].
      exists U1, U2, b1, b2, (protect_security k1 l), (protect_security k2 l).
      split; [rewrite E1; simpl; reflexivity |].
      split; [rewrite E2; simpl; reflexivity |].
      intros a1 a2 Hargs r1 r2 Er1 Er2.
      rewrite E1 in Hext, Hv1, Er1. rewrite E2 in Hext, Hv2, Er2.
      destruct (evaluates_protected_function (tm_abs U1 b1 k1) a1 l r1
        Hv1
        (proj1 (value_relation_properties _ _ _ _ Hargs)) Er1)
        as [o1 [Eo1 ->]].
      destruct (evaluates_protected_function (tm_abs U2 b2 k2) a2 l r2
        Hv2
        (proj1 (proj2 (value_relation_properties _ _ _ _ Hargs))) Er2)
        as [o2 [Eo2 ->]].
      specialize (Hext a1 a2 Hargs).
      pose proof (Hext o1 o2 Eo1 Eo2) as Hout.
      eapply IHT2; eassumption.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape Hobs) as [n [k1 [k2 [-> ->]]]].
      exists n, (protect_security k1 l), (protect_security k2 l). simpl. auto.
Qed.

Lemma value_relation_protect_invariant_asym : forall observer T v1 v2 l1 l2,
  value_relation observer T v1 v2 ->
  value_relation observer T (protect_value v1 l1) (protect_value v2 l2).
Proof.
  intros observer T. induction T; intros v1 v2 l1 l2 Hrel.
  all: unfold value_relation in *; simpl in *.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape Hobs) as [k1 [k2 [-> ->]]].
      exists (protect_security k1 l1), (protect_security k2 l2). simpl. auto.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape Hobs) as [Hleft | Hright].
      * destruct Hleft as [u1 [u2 [k1 [k2 [-> [-> Hchild]]]]]].
        left. exists u1, u2, (protect_security k1 l1), (protect_security k2 l2).
        simpl. repeat split; try reflexivity; assumption.
      * destruct Hright as [u1 [u2 [k1 [k2 [-> [-> Hchild]]]]]].
        right. exists u1, u2, (protect_security k1 l1), (protect_security k2 l2).
        simpl. repeat split; try reflexivity; assumption.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape Hobs) as
        [a1 [b1 [a2 [b2 [k1 [k2 [-> [-> [Ha Hb]]]]]]]]].
      exists a1, b1, a2, b2, (protect_security k1 l1), (protect_security k2 l2).
      simpl. repeat split; try reflexivity; assumption.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape Hobs) as [U1 [U2 [b1 [b2 [k1 [k2 [E1 [E2 Hext]]]]]]]].
      exists U1, U2, b1, b2, (protect_security k1 l1), (protect_security k2 l2).
      split; [rewrite E1; simpl; reflexivity |].
      split; [rewrite E2; simpl; reflexivity |].
      intros a1 a2 Hargs r1 r2 Er1 Er2.
      rewrite E1 in Hext, Hv1, Er1. rewrite E2 in Hext, Hv2, Er2.
      destruct (evaluates_protected_function (tm_abs U1 b1 k1) a1 l1 r1 Hv1
        (proj1 (value_relation_properties _ _ _ _ Hargs)) Er1) as [o1 [Eo1 ->]].
      destruct (evaluates_protected_function (tm_abs U2 b2 k2) a2 l2 r2 Hv2
        (proj1 (proj2 (value_relation_properties _ _ _ _ Hargs))) Er2) as [o2 [Eo2 ->]].
      specialize (Hext a1 a2 Hargs). pose proof (Hext o1 o2 Eo1 Eo2) as Hout.
      eapply IHT2; eassumption.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape Hobs) as [n [k1 [k2 [-> ->]]]].
      exists n, (protect_security k1 l1), (protect_security k2 l2). simpl. auto.
Qed.

Lemma flows_to_join_left : forall a b o,
  flows_to (join a b) o -> flows_to a o.
Proof. destruct a, b, o; simpl; tauto. Qed.

Lemma flows_to_join_right : forall a b o,
  flows_to (join a b) o -> flows_to b o.
Proof. destruct a, b, o; simpl; tauto. Qed.

Lemma security_of_protect : forall l T,
  (security_of (ty_protect l T)).(indirect_reader) =
  join (security_of T).(indirect_reader) l.
Proof. intros l T; destruct T; reflexivity. Qed.

Lemma underlying_typed_subtype : forall T U t,
  subtype T U -> underlying_typed T t -> underlying_typed U t.
Proof.
  intros T U t Hsub Ht. unfold underlying_typed in *.
  rewrite <- (subtype_erasure _ _ Hsub). exact Ht.
Qed.

Lemma subtype_self_protect : forall T l,
  wf_ty T -> subtype T (ty_protect l T).
Proof.
  intros T l Hwf.
  assert (Hsub : subtype (ty_protect Low T) (ty_protect l T)).
  { apply subtype_protect.
    - apply subtype_refl. exact Hwf.
    - destruct l; exact I. }
  rewrite ty_protect_low in Hsub. exact Hsub.
Qed.

Lemma value_relation_protect_type : forall observer T v1 v2 l,
  value_relation observer T v1 v2 ->
  value_relation observer (ty_protect l T) (protect_value v1 l) (protect_value v2 l).
Proof.
  intros observer T. induction T; intros v1 v2 l Hrel.
  all: unfold value_relation in *; simpl in *.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape (flows_to_join_left _ _ _ Hobs)) as [k1 [k2 [-> ->]]].
      exists (protect_security k1 l), (protect_security k2 l). simpl. auto.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape (flows_to_join_left _ _ _ Hobs)) as [Hleft | Hright].
      * destruct Hleft as [u1 [u2 [k1 [k2 [-> [-> Hchild]]]]]].
        left. exists u1, u2, (protect_security k1 l), (protect_security k2 l).
        simpl. repeat split; try reflexivity; assumption.
      * destruct Hright as [u1 [u2 [k1 [k2 [-> [-> Hchild]]]]]].
        right. exists u1, u2, (protect_security k1 l), (protect_security k2 l).
        simpl. repeat split; try reflexivity; assumption.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape (flows_to_join_left _ _ _ Hobs)) as
        [a1 [b1 [a2 [b2 [k1 [k2 [-> [-> [Ha Hb]]]]]]]]].
      exists a1, b1, a2, b2, (protect_security k1 l), (protect_security k2 l).
      simpl. repeat split; try reflexivity; assumption.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape (flows_to_join_left _ _ _ Hobs)) as [U1 [U2 [b1 [b2 [k1 [k2 [E1 [E2 Hext]]]]]]]].
      exists U1, U2, b1, b2, (protect_security k1 l), (protect_security k2 l).
      split; [rewrite E1; simpl; reflexivity |].
      split; [rewrite E2; simpl; reflexivity |].
      intros a1 a2 Hargs r1 r2 Er1 Er2.
      rewrite E1 in Hext, Hv1, Er1. rewrite E2 in Hext, Hv2, Er2.
      destruct (evaluates_protected_function (tm_abs U1 b1 k1) a1 l r1 Hv1
        (proj1 (value_relation_properties _ _ _ _ Hargs)) Er1) as [o1 [Eo1 ->]].
      destruct (evaluates_protected_function (tm_abs U2 b2 k2) a2 l r2 Hv2
        (proj1 (proj2 (value_relation_properties _ _ _ _ Hargs))) Er2) as [o2 [Eo2 ->]].
      specialize (Hext a1 a2 Hargs). pose proof (Hext o1 o2 Eo1 Eo2) as Hout.
      eapply value_relation_protect_invariant; eassumption.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try (eapply value_protect; eassumption).
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + unfold underlying_typed in *. rewrite !erase_protect_value. assumption.
    + intros Hobs. destruct (Hshape (flows_to_join_left _ _ _ Hobs)) as [n [k1 [k2 [-> ->]]]].
      exists n, (protect_security k1 l), (protect_security k2 l). simpl. auto.
Qed.

Lemma value_relation_subtype : forall observer T U v1 v2,
  subtype T U -> value_relation observer T v1 v2 -> value_relation observer U v1 v2.
Proof.
  intros observer T U v1 v2 Hsub. revert v1 v2.
  induction Hsub; intros v1 v2 Hrel.
  all: unfold value_relation in *; simpl in *.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    unfold value_relation; simpl in *.
    split; [exact Hv1 |]. split; [exact Hv2 |].
    split; [eapply underlying_typed_subtype; [exact (S_Unit _ _ H H0 H1) | exact Ht1] |].
    split; [eapply underlying_typed_subtype; [exact (S_Unit _ _ H H0 H1) | exact Ht2] |].
    intros Hobs. apply Hshape. eapply flows_to_trans; [exact (proj2 H1) | exact Hobs].
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    unfold value_relation; simpl in *.
    split; [exact Hv1 |]. split; [exact Hv2 |].
    split; [eapply underlying_typed_subtype; [exact (S_Sum _ _ _ _ _ _ Hsub1 Hsub2 H H0 H1) | exact Ht1] |].
    split; [eapply underlying_typed_subtype; [exact (S_Sum _ _ _ _ _ _ Hsub1 Hsub2 H H0 H1) | exact Ht2] |].
    intros Hobs. destruct (Hshape (flows_to_trans _ _ _ (proj2 H1) Hobs)) as [Hleft | Hright].
    + destruct Hleft as [a [b [k1 [k2 [-> [-> Ha]]]]]].
      left. exists a, b, k1, k2. repeat split; try reflexivity.
      eapply IHHsub1; exact Ha.
    + destruct Hright as [a [b [k1 [k2 [-> [-> Hb]]]]]].
      right. exists a, b, k1, k2. repeat split; try reflexivity.
      eapply IHHsub2; exact Hb.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    unfold value_relation; simpl in *.
    split; [exact Hv1 |]. split; [exact Hv2 |].
    split; [eapply underlying_typed_subtype; [exact (S_Prod _ _ _ _ _ _ Hsub1 Hsub2 H H0 H1) | exact Ht1] |].
    split; [eapply underlying_typed_subtype; [exact (S_Prod _ _ _ _ _ _ Hsub1 Hsub2 H H0 H1) | exact Ht2] |].
    intros Hobs. destruct (Hshape (flows_to_trans _ _ _ (proj2 H1) Hobs)) as
      [a1 [b1 [a2 [b2 [k1 [k2 [-> [-> [Ha Hb]]]]]]]]].
    exists a1, b1, a2, b2, k1, k2. repeat split; try reflexivity.
    + eapply IHHsub1; exact Ha.
    + eapply IHHsub2; exact Hb.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    unfold value_relation; simpl in *.
    split; [exact Hv1 |]. split; [exact Hv2 |].
    split; [eapply underlying_typed_subtype; [exact (S_Arrow _ _ _ _ _ _ Hsub1 Hsub2 H H0 H1) | exact Ht1] |].
    split; [eapply underlying_typed_subtype; [exact (S_Arrow _ _ _ _ _ _ Hsub1 Hsub2 H H0 H1) | exact Ht2] |].
    intros Hobs. destruct (Hshape (flows_to_trans _ _ _ (proj2 H1) Hobs)) as
      [A [B [body1 [body2 [k1 [k2 [E1 [E2 Hext]]]]]]]].
    exists A, B, body1, body2, k1, k2. split; [exact E1 |]. split; [exact E2 |].
    intros arg1 arg2 Harg.
    specialize (Hext arg1 arg2 (IHHsub1 arg1 arg2 Harg)).
    intros w1 w2 Ew1 Ew2.
    eapply IHHsub2; eapply Hext; eassumption.
  - eapply IHHsub2. eapply IHHsub1. exact Hrel.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    unfold value_relation; simpl in *.
    split; [exact Hv1 |]. split; [exact Hv2 |].
    split; [eapply underlying_typed_subtype; [exact (S_Nat _ _ H H0 H1) | exact Ht1] |].
    split; [eapply underlying_typed_subtype; [exact (S_Nat _ _ H H0 H1) | exact Ht2] |].
    intros Hobs. destruct (Hshape (flows_to_trans _ _ _ (proj2 H1) Hobs)) as [nval [ka [kb [-> ->]]]].
    exists nval, ka, kb. auto.
Qed.

Lemma value_relation_subtype_conditional : forall observer T U v1 v2,
  subtype T U -> value v1 -> value v2 ->
  underlying_typed U v1 -> underlying_typed U v2 ->
  (flows_to (security_of U).(indirect_reader) observer ->
    value_relation observer T v1 v2) ->
  value_relation observer U v1 v2.
Proof.
  intros observer T U v1 v2 Hsub Hv1 Hv2 Hu1 Hu2 Hpayload.
  destruct U; simpl in *; unfold value_relation; simpl.
  all: split; [exact Hv1 |].
  all: split; [exact Hv2 |].
  all: split; [exact Hu1 |].
  all: split; [exact Hu2 |].
  all: intros Hobs.
  all: pose proof (value_relation_subtype observer T _ v1 v2 Hsub (Hpayload Hobs)) as Hrel.
  all: unfold value_relation in Hrel; simpl in Hrel.
  all: destruct Hrel as [_ [_ [_ [_ Hshape]]]].
  all: exact (Hshape Hobs).
Qed.

Theorem fundamental_expressions : forall Gamma t T,
  has_type Gamma t T ->
  forall observer rho1 rho2,
    related_expression_substitutions observer Gamma rho1 rho2 ->
    expression_relation observer T (instantiate rho1 t) (instantiate rho2 t).
Proof.
  intros Gamma t T Htype. induction Htype; intros observer rho1 rho2 Henv.
  all: match goal with
  | |- expression_relation ?obs ?Ty (instantiate ?r1 ?term) (instantiate ?r2 ?term) =>
      assert (Hinst1 : underlying_typed Ty (instantiate r1 term));
      [ eapply typing_instantiate_erased;
        [eauto 20 using has_type | intros y Uenv Hlookup;
          destruct (Henv y Uenv Hlookup) as [Hrel1 [Hrel2 _]]; exact Hrel1] | idtac ]
  end.
  all: match goal with
  | |- expression_relation ?obs ?Ty (instantiate ?r1 ?term) (instantiate ?r2 ?term) =>
      assert (Hinst2 : underlying_typed Ty (instantiate r2 term));
      [ eapply typing_instantiate_erased;
        [eauto 20 using has_type | intros y Uenv Hlookup;
          destruct (Henv y Uenv Hlookup) as [Hrel1 [Hrel2 _]]; exact Hrel2] | idtac ]
  end.
  all: unfold expression_relation; split; [exact Hinst1 | idtac].
  all: split; [exact Hinst2 | idtac].
  all: intros v1 v2 Heval1 Heval2.
  - destruct (Henv x T H) as [_ [_ Hlift]]. exact (Hlift v1 v2 Heval1 Heval2).
  - change (evaluates (tm_unit kappa) v1) in Heval1.
    change (evaluates (tm_unit kappa) v2) in Heval2.
    assert (E1 : v1 = tm_unit kappa).
    { eapply value_multi_inv; [constructor | exact (proj1 Heval1)]. }
    assert (E2 : v2 = tm_unit kappa).
    { eapply value_multi_inv; [constructor | exact (proj1 Heval2)]. }
    subst v1. subst v2. unfold value_relation; simpl.
    split; [exact (proj2 Heval1) |]. split; [exact (proj2 Heval2) |].
    split; [eapply underlying_typed_evaluates; eauto |].
    split; [eapply underlying_typed_evaluates; eauto |].
    intros Hobserve. exists kappa, kappa. auto.
  - simpl in Heval1, Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst. inversion Heval2; subst.
    unfold value_relation; simpl.
    apply conj; [eapply big_step_result_value; exact Heval1 |].
    split; [eapply big_step_result_value; exact Heval2 |].
    split; [eapply underlying_typed_evaluates; [exact Hinst1 | exact (proj1 (big_step_iff_evaluates _ _) Heval1)] |].
    split; [eapply underlying_typed_evaluates; [exact Hinst2 | exact (proj1 (big_step_iff_evaluates _ _) Heval2)] |].
    intros Hobs. destruct (fresh_atom (L ++ fv body ++ map fst Gamma)) as [x Hfresh].
    assert (HxL : ~ In x L) by (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (Hxbody : ~ In x (fv body)) by (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (HxGamma : ~ In x (map fst Gamma)) by (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (Hroot : has_type Gamma (tm_abs T1 body kappa) (Ty_Arrow T1 T2 kappa)).
    { eapply T_Abs with (L := L); eauto. }
    pose proof (related_substitution_lc Gamma (tm_abs T1 body kappa)
      (Ty_Arrow T1 T2 kappa) observer rho1 rho2 Hroot Henv) as Hlc.
    exists T1, T1, (instantiate rho1 body), (instantiate rho2 body), kappa, kappa.
    split; [reflexivity |]. split; [reflexivity |].
    intros arg1 arg2 Hargs w1 w2 Ew1 Ew2.
    assert (Henv' : related_expression_substitutions observer (update Gamma x T1)
      (substitution_update rho1 x arg1) (substitution_update rho2 x arg2)).
    { eapply related_expression_update; eassumption. }
    destruct (H2 x HxL observer (substitution_update rho1 x arg1)
      (substitution_update rho2 x arg2) Henv') as [_ [_ Hbodylift]].
    assert (Eloc1 : forall y, In y (fv body) -> locally_closed (rho1 y)).
    { intros y Hy. exact (proj1 (Hlc y Hy)). }
    assert (Eloc2 : forall y, In y (fv body) -> locally_closed (rho2 y)).
    { intros y Hy. exact (proj2 (Hlc y Hy)). }
    assert (Eopen1 : instantiate (substitution_update rho1 x arg1)
       (open body (tm_fvar x)) = open (instantiate rho1 body) arg1).
    { apply instantiate_open_update; [exact Hxbody | exact Eloc1]. }
    assert (Eopen2 : instantiate (substitution_update rho2 x arg2)
       (open body (tm_fvar x)) = open (instantiate rho2 body) arg2).
    { apply instantiate_open_update; [exact Hxbody | exact Eloc2]. }
    apply big_step_iff_evaluates in Ew1. apply big_step_iff_evaluates in Ew2.
    inversion Ew1; subst. inversion Ew2; subst.
    inversion H6; subst. inversion H10; subst.
    assert (Earg1 : v = arg1).
    { eapply big_step_value_inv; [exact (proj1 (value_relation_properties _ _ _ _ Hargs)) | exact H9]. }
    assert (Earg2 : v0 = arg2).
    { eapply big_step_value_inv; [exact (proj1 (proj2 (value_relation_properties _ _ _ _ Hargs))) | exact H13]. }
    subst v. subst v0.
    assert (Hbase : value_relation observer T2 w w0).
    { eapply Hbodylift.
      - rewrite Eopen1. exact (proj1 (big_step_iff_evaluates _ _) H12).
      - rewrite Eopen2. exact (proj1 (big_step_iff_evaluates _ _) H16). }
    eapply value_relation_protect_invariant; exact Hbase.
  - simpl in Heval1, Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst. inversion Heval2; subst.
    assert (Hfrel : value_relation observer (Ty_Arrow T1 T2 kappa)
      (tm_abs A body k) (tm_abs A0 body0 k0)).
    { destruct (IHHtype1 observer rho1 rho2 Henv) as [_ [_ Hlift]].
      eapply Hlift.
      - exact (proj1 (big_step_iff_evaluates _ _) H3).
      - exact (proj1 (big_step_iff_evaluates _ _) H5). }
    assert (Harel : value_relation observer T1 v v0).
    { destruct (IHHtype2 observer rho1 rho2 Henv) as [_ [_ Hlift]].
      eapply Hlift.
      - exact (proj1 (big_step_iff_evaluates _ _) H4).
      - exact (proj1 (big_step_iff_evaluates _ _) H8). }
    pose proof (proj2 (typing_regular _ _ _ Htype1)) as Hwfarr.
    simpl in Hwfarr. destruct Hwfarr as [_ [HwfT2 _]].
    eapply value_relation_subtype_conditional.
    + apply subtype_self_protect. exact HwfT2.
    + eapply big_step_result_value. exact Heval1.
    + eapply big_step_result_value. exact Heval2.
    + eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1].
    + eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2].
    + intros Hobserve.
      assert (Harrowobs : flows_to (indirect_reader kappa) observer).
      { rewrite security_of_protect in Hobserve. eapply flows_to_join_right. exact Hobserve. }
      destruct Hfrel as [_ [_ [_ [_ Hshape]]]].
      destruct (Hshape Harrowobs) as [U1 [U2 [b1 [b2 [kf1 [kf2 [E1 [E2 Hext]]]]]]]].
      assert (Happs := Hext v v0 Harel).
      assert (Hlcabs1 : locally_closed (tm_abs A body k)).
      { pose proof (big_step_result_value _ _ H3) as Hv. inversion Hv; assumption. }
      assert (Hlcabs2 : locally_closed (tm_abs A0 body0 k0)).
      { pose proof (big_step_result_value _ _ H5) as Hv. inversion Hv; assumption. }
      assert (Hvarg1 : value v) by (eapply big_step_result_value; exact H4).
      assert (Hvarg2 : value v0) by (eapply big_step_result_value; exact H8).
      assert (Happ1 : evaluates (tm_app (tm_abs A body k) v High)
        (protect_value w (indirect_reader k))).
      { apply (proj1 (big_step_iff_evaluates _ _)).
        eapply B_App with (A := A) (body := body) (k := k) (v := v) (w := w).
        - apply B_Abs. exact Hlcabs1.
        - apply big_step_value_refl. exact Hvarg1.
        - destruct k as [rk ik]; simpl; destruct rk; simpl; exact I.
        - exact H7. }
      assert (Happ2 : evaluates (tm_app (tm_abs A0 body0 k0) v0 High)
        (protect_value w0 (indirect_reader k0))).
      { apply (proj1 (big_step_iff_evaluates _ _)).
        eapply B_App with (A := A0) (body := body0) (k := k0) (v := v0) (w := w0).
        - apply B_Abs. exact Hlcabs2.
        - apply big_step_value_refl. exact Hvarg2.
        - destruct k0 as [rk0 ik0]; simpl; destruct rk0; simpl; exact I.
        - exact H11. }
      exact (Happs _ _ Happ1 Happ2).
  - simpl in Heval1, Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst. inversion Heval2; subst.
    assert (Hleft : value_relation observer T1 v v0).
    { destruct (IHHtype1 observer rho1 rho2 Henv) as [_ [_ Hlift]].
      eapply Hlift.
      - exact ((proj1 (big_step_iff_evaluates _ _)) H4).
      - exact ((proj1 (big_step_iff_evaluates _ _)) H6). }
    assert (Hright : value_relation observer T2 w w0).
    { destruct (IHHtype2 observer rho1 rho2 Henv) as [_ [_ Hlift]].
      eapply Hlift.
      - exact ((proj1 (big_step_iff_evaluates _ _)) H5).
      - exact ((proj1 (big_step_iff_evaluates _ _)) H7). }
    unfold value_relation; simpl.
    split; [eapply big_step_result_value; exact Heval1 |].
    split; [eapply big_step_result_value; exact Heval2 |].
    split; [eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1] |].
    split; [eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2] |].
    intros Hobserve. exists v, w, v0, w0, kappa, kappa.
    repeat split; try reflexivity; assumption.
  - simpl in Heval1, Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst. inversion Heval2; subst.
    assert (Hp : value_relation observer (Ty_Prod T1 T2 kappa) (tm_pair a b k) (tm_pair a0 b0 k0)).
    { destruct (IHHtype observer rho1 rho2 Henv) as [_ [_ Hlift]].
      eapply Hlift.
      - exact (proj1 (big_step_iff_evaluates _ _) H2).
      - exact (proj1 (big_step_iff_evaluates _ _) H3). }
    pose proof (proj2 (typing_regular _ _ _ Htype)) as Hwfprod.
    simpl in Hwfprod. destruct Hwfprod as [HwfT1 [HwfT2 _]].
    eapply value_relation_subtype_conditional.
    + apply subtype_self_protect. exact HwfT1.
    + eapply big_step_result_value. exact Heval1.
    + eapply big_step_result_value. exact Heval2.
    + eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1].
    + eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2].
    + intros Hobserve. rewrite security_of_protect in Hobserve.
      assert (Hprodobs : flows_to (indirect_reader kappa) observer).
      { eapply flows_to_join_right. exact Hobserve. }
      destruct Hp as [_ [_ [_ [_ Hshape]]]].
      destruct (Hshape Hprodobs) as [a1 [b1 [a2 [b2 [kp1 [kp2 [E1 [E2 [Ha Hb]]]]]]]]].
      simpl in E1, E2. inversion E1; inversion E2; subst.
      eapply value_relation_protect_invariant_asym; exact Ha.
  - simpl in Heval1, Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst. inversion Heval2; subst.
    assert (Hp : value_relation observer (Ty_Prod T1 T2 kappa) (tm_pair a b k) (tm_pair a0 b0 k0)).
    { destruct (IHHtype observer rho1 rho2 Henv) as [_ [_ Hlift]].
      eapply Hlift.
      - exact (proj1 (big_step_iff_evaluates _ _) H2).
      - exact (proj1 (big_step_iff_evaluates _ _) H3). }
    pose proof (proj2 (typing_regular _ _ _ Htype)) as Hwfprod.
    simpl in Hwfprod. destruct Hwfprod as [HwfT1 [HwfT2 _]].
    eapply value_relation_subtype_conditional.
    + apply subtype_self_protect. exact HwfT2.
    + eapply big_step_result_value. exact Heval1.
    + eapply big_step_result_value. exact Heval2.
    + eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1].
    + eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2].
    + intros Hobserve. rewrite security_of_protect in Hobserve.
      assert (Hprodobs : flows_to (indirect_reader kappa) observer).
      { eapply flows_to_join_right. exact Hobserve. }
      destruct Hp as [_ [_ [_ [_ Hshape]]]].
      destruct (Hshape Hprodobs) as [a1 [b1 [a2 [b2 [kp1 [kp2 [E1 [E2 [Ha Hb]]]]]]]]].
      simpl in E1, E2. inversion E1; inversion E2; subst.
      eapply value_relation_protect_invariant_asym; exact Hb.
  - simpl in Heval1, Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst. inversion Heval2; subst.
    assert (Hp : value_relation observer T1 v v0).
    { destruct (IHHtype observer rho1 rho2 Henv) as [_ [_ Hlift]].
      eapply Hlift; [exact ((proj1 (big_step_iff_evaluates _ _)) H4) |
        exact ((proj1 (big_step_iff_evaluates _ _)) H5)]. }
    unfold value_relation; simpl.
    split; [eapply big_step_result_value; exact Heval1 |].
    split; [eapply big_step_result_value; exact Heval2 |].
    split; [eapply underlying_typed_evaluates; [exact Hinst1 | exact (proj1 (big_step_iff_evaluates _ _) Heval1)] |].
    split; [eapply underlying_typed_evaluates; [exact Hinst2 | exact (proj1 (big_step_iff_evaluates _ _) Heval2)] |].
    intros Hobserve. left. exists v, v0, kappa, kappa. repeat split; try reflexivity; assumption.
  - simpl in Heval1, Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst. inversion Heval2; subst.
    assert (Hp : value_relation observer T2 v v0).
    { destruct (IHHtype observer rho1 rho2 Henv) as [_ [_ Hlift]].
      eapply Hlift; [exact ((proj1 (big_step_iff_evaluates _ _)) H4) |
        exact ((proj1 (big_step_iff_evaluates _ _)) H5)]. }
    unfold value_relation; simpl.
    split; [eapply big_step_result_value; exact Heval1 |].
    split; [eapply big_step_result_value; exact Heval2 |].
    split; [eapply underlying_typed_evaluates; [exact Hinst1 | exact (proj1 (big_step_iff_evaluates _ _) Heval1)] |].
    split; [eapply underlying_typed_evaluates; [exact Hinst2 | exact (proj1 (big_step_iff_evaluates _ _) Heval2)] |].
    intros Hobserve. right. exists v, v0, kappa, kappa. repeat split; try reflexivity; assumption.
  - simpl in Heval1, Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst. all: inversion Heval2; subst.
    assert (Hctrl : value_relation observer (Ty_Sum T1 T2 kappa)
      (tm_inl v k) (tm_inl v0 k0)).
    { destruct (IHHtype observer rho1 rho2 Henv) as [_ [_ Hlift]].
      eapply Hlift.
      - exact (proj1 (big_step_iff_evaluates _ _) H9).
      - exact (proj1 (big_step_iff_evaluates _ _) H12). }
    destruct (fresh_atom (L ++ fv body1 ++ fv body2 ++ map fst Gamma)) as [x0 Hfresh0].
    assert (HxL : ~ In x0 L) by (intro Hin; apply Hfresh0; repeat rewrite in_app_iff; tauto).
    pose proof (proj2 (typing_regular _ _ _ (H0 x0 HxL))) as HwfT.
    eapply value_relation_subtype_conditional.
    + apply subtype_self_protect. exact HwfT.
    + eapply big_step_result_value. exact Heval1.
    + eapply big_step_result_value. exact Heval2.
    + eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1].
    + eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2].
    + intros Hobserve. rewrite security_of_protect in Hobserve.
      assert (Hkobs : flows_to (indirect_reader kappa) observer).
      { eapply flows_to_join_right. exact Hobserve. }
      destruct Hctrl as [_ [_ [_ [_ Hshape]]]].
      destruct (Hshape Hkobs) as [Hleft | Hright].
      * destruct Hleft as [a1 [a2 [ka [kb [E1 [E2 Harg]]]]]].
        inversion E1; inversion E2; subst.
        assert (Hxbody : ~ In x0 (fv body1)) by (intro Hin; apply Hfresh0; repeat rewrite in_app_iff; tauto).
        assert (Henv' : related_expression_substitutions observer (update Gamma x0 T1)
          (substitution_update rho1 x0 a1) (substitution_update rho2 x0 a2)).
        { eapply related_expression_update; eassumption. }
        destruct (H1 x0 HxL observer (substitution_update rho1 x0 a1)
          (substitution_update rho2 x0 a2) Henv') as [_ [_ Hbodylift]].
        assert (Hlc : forall y, In y (fv body1) -> locally_closed (rho1 y) /\ locally_closed (rho2 y)).
        { intros y Hy. assert (Hyopen : In y (fv (open body1 (tm_fvar x0))))
            by (eapply fv_open_includes; exact Hy).
          destruct (related_substitution_lc (update Gamma x0 T1)
            (open body1 (tm_fvar x0)) T observer
            (substitution_update rho1 x0 a1) (substitution_update rho2 x0 a2)
            (H0 x0 HxL) Henv' y Hyopen) as [Hl1 Hl2].
          assert (Hneq : x0 <> y) by (intro Heq; subst y; contradiction).
          unfold substitution_update in Hl1, Hl2.
          destruct (Nat.eqb x0 y) eqn:E; [apply Nat.eqb_eq in E; contradiction | simpl in Hl1, Hl2].
          split; assumption. }
        assert (Eopen1 : instantiate (substitution_update rho1 x0 a1)
          (open body1 (tm_fvar x0)) = open (instantiate rho1 body1) a1).
        { apply instantiate_open_update; [exact Hxbody | intros y Hy; exact (proj1 (Hlc y Hy))]. }
        assert (Eopen2 : instantiate (substitution_update rho2 x0 a2)
          (open body1 (tm_fvar x0)) = open (instantiate rho2 body1) a2).
        { apply instantiate_open_update; [exact Hxbody | intros y Hy; exact (proj2 (Hlc y Hy))]. }
        assert (Hbody : value_relation observer T w w0).
        { eapply Hbodylift.
          - rewrite Eopen1. exact (proj1 (big_step_iff_evaluates _ _) H11).
          - rewrite Eopen2. exact (proj1 (big_step_iff_evaluates _ _) H14). }
        eapply value_relation_protect_invariant_asym. exact Hbody.
      * destruct Hright as [a1 [a2 [ka [kb [E1 [E2 Harg]]]]]]. discriminate E1.
    + assert (Hctrl : value_relation observer (Ty_Sum T1 T2 kappa)
        (tm_inl v k) (tm_inr v0 k0)).
      { destruct (IHHtype observer rho1 rho2 Henv) as [_ [_ Hlift]].
        eapply Hlift.
        - exact (proj1 (big_step_iff_evaluates _ _) H9).
        - exact (proj1 (big_step_iff_evaluates _ _) H12). }
      destruct (fresh_atom (L ++ fv body1 ++ fv body2 ++ map fst Gamma)) as [x0 Hfresh0].
      assert (HxL : ~ In x0 L) by (intro Hin; apply Hfresh0; repeat rewrite in_app_iff; tauto).
      pose proof (proj2 (typing_regular _ _ _ (H0 x0 HxL))) as HwfT.
      eapply value_relation_subtype_conditional.
      * apply subtype_self_protect. exact HwfT.
      * eapply big_step_result_value. exact Heval1.
      * eapply big_step_result_value. exact Heval2.
      * eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1].
      * eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2].
      * intros Hobserve. rewrite security_of_protect in Hobserve.
        assert (Hkobs : flows_to (indirect_reader kappa) observer).
        { eapply flows_to_join_right. exact Hobserve. }
        destruct Hctrl as [_ [_ [_ [_ Hshape]]]].
        destruct (Hshape Hkobs) as [Hleft | Hright].
        -- destruct Hleft as [a1 [a2 [ka [kb [E1 [E2 Ha]]]]]]. discriminate E2.
        -- destruct Hright as [a1 [a2 [ka [kb [E1 [E2 Hb]]]]]]. discriminate E1.
    + assert (Hctrl : value_relation observer (Ty_Sum T1 T2 kappa)
        (tm_inr v k) (tm_inl v0 k0)).
      { destruct (IHHtype observer rho1 rho2 Henv) as [_ [_ Hlift]].
        eapply Hlift.
        - exact (proj1 (big_step_iff_evaluates _ _) H9).
        - exact (proj1 (big_step_iff_evaluates _ _) H12). }
      destruct (fresh_atom (L ++ fv body1 ++ fv body2 ++ map fst Gamma)) as [x0 Hfresh0].
      assert (HxL : ~ In x0 L) by (intro Hin; apply Hfresh0; repeat rewrite in_app_iff; tauto).
      pose proof (proj2 (typing_regular _ _ _ (H0 x0 HxL))) as HwfT.
      eapply value_relation_subtype_conditional.
      * apply subtype_self_protect. exact HwfT.
      * eapply big_step_result_value. exact Heval1.
      * eapply big_step_result_value. exact Heval2.
      * eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1].
      * eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2].
      * intros Hobserve. rewrite security_of_protect in Hobserve.
        assert (Hkobs : flows_to (indirect_reader kappa) observer).
        { eapply flows_to_join_right. exact Hobserve. }
        destruct Hctrl as [_ [_ [_ [_ Hshape]]]].
        destruct (Hshape Hkobs) as [Hleft | Hright].
        -- destruct Hleft as [a1 [a2 [ka [kb [E1 [E2 Ha]]]]]]. discriminate E1.
        -- destruct Hright as [a1 [a2 [ka [kb [E1 [E2 Hb]]]]]]. discriminate E2.
    + assert (Hctrl : value_relation observer (Ty_Sum T1 T2 kappa)
        (tm_inr v k) (tm_inr v0 k0)).
      { destruct (IHHtype observer rho1 rho2 Henv) as [_ [_ Hlift]].
        eapply Hlift.
        - exact (proj1 (big_step_iff_evaluates _ _) H9).
        - exact (proj1 (big_step_iff_evaluates _ _) H12). }
      destruct (fresh_atom (L ++ fv body1 ++ fv body2 ++ map fst Gamma)) as [x0 Hfresh0].
      assert (HxL : ~ In x0 L) by (intro Hin; apply Hfresh0; repeat rewrite in_app_iff; tauto).
      pose proof (proj2 (typing_regular _ _ _ (H2 x0 HxL))) as HwfT.
      eapply value_relation_subtype_conditional.
      * apply subtype_self_protect. exact HwfT.
      * eapply big_step_result_value. exact Heval1.
      * eapply big_step_result_value. exact Heval2.
      * eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1].
      * eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2].
      * intros Hobserve. rewrite security_of_protect in Hobserve.
        assert (Hkobs : flows_to (indirect_reader kappa) observer).
        { eapply flows_to_join_right. exact Hobserve. }
        destruct Hctrl as [_ [_ [_ [_ Hshape]]]].
        destruct (Hshape Hkobs) as [Hleft | Hright].
        -- destruct Hleft as [a1 [a2 [ka [kb [E1 [E2 Ha]]]]]]. discriminate E1.
        -- destruct Hright as [a1 [a2 [ka [kb [E1 [E2 Harg]]]]]].
           inversion E1; inversion E2; subst.
           assert (Hxbody : ~ In x0 (fv body2)) by (intro Hin; apply Hfresh0; repeat rewrite in_app_iff; tauto).
           assert (Henv' : related_expression_substitutions observer (update Gamma x0 T2)
             (substitution_update rho1 x0 a1) (substitution_update rho2 x0 a2)).
           { eapply related_expression_update; eassumption. }
           destruct (H3 x0 HxL observer (substitution_update rho1 x0 a1)
             (substitution_update rho2 x0 a2) Henv') as [_ [_ Hbodylift]].
           assert (Hlc : forall y, In y (fv body2) -> locally_closed (rho1 y) /\ locally_closed (rho2 y)).
           { intros y Hy. assert (Hyopen : In y (fv (open body2 (tm_fvar x0))))
               by (eapply fv_open_includes; exact Hy).
             destruct (related_substitution_lc (update Gamma x0 T2)
               (open body2 (tm_fvar x0)) T observer
               (substitution_update rho1 x0 a1) (substitution_update rho2 x0 a2)
               (H2 x0 HxL) Henv' y Hyopen) as [Hl1 Hl2].
             assert (Hneq : x0 <> y) by (intro Heq; subst y; contradiction).
             unfold substitution_update in Hl1, Hl2.
             destruct (Nat.eqb x0 y) eqn:E; [apply Nat.eqb_eq in E; contradiction | simpl in Hl1, Hl2].
             split; assumption. }
           assert (Eopen1 : instantiate (substitution_update rho1 x0 a1)
             (open body2 (tm_fvar x0)) = open (instantiate rho1 body2) a1).
           { apply instantiate_open_update; [exact Hxbody | intros y Hy; exact (proj1 (Hlc y Hy))]. }
           assert (Eopen2 : instantiate (substitution_update rho2 x0 a2)
             (open body2 (tm_fvar x0)) = open (instantiate rho2 body2) a2).
           { apply instantiate_open_update; [exact Hxbody | intros y Hy; exact (proj2 (Hlc y Hy))]. }
           assert (Hbody : value_relation observer T w w0).
           { eapply Hbodylift.
             - rewrite Eopen1. exact (proj1 (big_step_iff_evaluates _ _) H11).
             - rewrite Eopen2. exact (proj1 (big_step_iff_evaluates _ _) H14). }
           eapply value_relation_protect_invariant_asym. exact Hbody.
  - simpl in Heval1, Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst. inversion Heval2; subst.
    destruct (IHHtype observer rho1 rho2 Henv) as [_ [_ Hlift]].
    assert (Hrel : value_relation observer T v v0).
    { eapply Hlift; [exact ((proj1 (big_step_iff_evaluates _ _)) H2) |
        exact ((proj1 (big_step_iff_evaluates _ _)) H3)]. }
    exact (value_relation_protect_type observer T v v0 l Hrel).
  - destruct (IHHtype observer rho1 rho2 Henv) as [_ [_ Hlift]].
    eapply value_relation_subtype; [exact H | eapply Hlift; eassumption].
  - change (evaluates (tm_nat n k) v1) in Heval1.
    change (evaluates (tm_nat n k) v2) in Heval2.
    destruct Heval1 as [Hs1 Hv1]. destruct Heval2 as [Hs2 Hv2].
    assert (E1 : v1 = tm_nat n k) by (eapply value_multi_inv; [constructor | exact Hs1]).
    assert (E2 : v2 = tm_nat n k) by (eapply value_multi_inv; [constructor | exact Hs2]).
    subst v1. subst v2. unfold value_relation; simpl.
    split; [exact Hv1 |]. split; [exact Hv2 |].
    split; [eapply underlying_typed_evaluates; [exact Hinst1 | split; assumption] |].
    split; [eapply underlying_typed_evaluates; [exact Hinst2 | split; assumption] |].
    intros Hobserve. exists n, k, k. auto.
  - simpl in Heval1, Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst. inversion Heval2; subst.
    assert (Hnums : value_relation observer (Ty_Nat k) (tm_nat n k0) (tm_nat n0 k1)).
    { destruct (IHHtype observer rho1 rho2 Henv) as [_ [_ Hlift]].
      eapply Hlift.
      - exact (proj1 (big_step_iff_evaluates _ _) H2).
      - exact (proj1 (big_step_iff_evaluates _ _) H3). }
    eapply value_relation_subtype_conditional.
    + apply subtype_self_protect. simpl; exact I.
    + eapply big_step_result_value. exact Heval1.
    + eapply big_step_result_value. exact Heval2.
    + eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1].
    + eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2].
    + intros Hobserve. rewrite security_of_protect in Hobserve.
      assert (Hkobs : flows_to (indirect_reader k) observer).
      { eapply flows_to_join_right. exact Hobserve. }
      destruct Hnums as [_ [_ [_ [_ Hshape]]]].
      destruct (Hshape Hkobs) as [nval [ka [kb [E1 E2]]]].
      assert (En : n = nval) by congruence. subst nval.
      assert (En0 : n0 = n) by congruence. subst n0.
      assert (Hbase : value_relation observer (Ty_Nat public)
        (tm_nat (S n) public) (tm_nat (S n) public)).
      { unfold value_relation; simpl.
        split; [constructor |]. split; [constructor |].
        split; [unfold underlying_typed; simpl; apply T_Nat; cbn; exact I |].
        split; [unfold underlying_typed; simpl; apply T_Nat; cbn; exact I |].
        - intros _. exists (S n), public, public. auto. }
      eapply value_relation_protect_invariant_asym with
        (l1 := indirect_reader k0) (l2 := indirect_reader k1).
      exact Hbase.
  - simpl in Heval1, Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst. inversion Heval2; subst.
    all: admit.
  - simpl in Heval1, Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst. all: inversion Heval2; subst.
    assert (Hctrl : value_relation observer
      (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
      (tm_inl v k0) (tm_inl v0 k1)).
    { destruct (IHHtype1 observer rho1 rho2 Henv) as [_ [_ Hlift]].
      eapply Hlift.
      - exact (proj1 (big_step_iff_evaluates _ _) H5).
      - exact (proj1 (big_step_iff_evaluates _ _) H8). }
    pose proof (proj2 (typing_regular _ _ _ Htype2)) as HwfT.
    eapply value_relation_subtype_conditional.
    + apply subtype_self_protect. exact HwfT.
    + eapply big_step_result_value. exact Heval1.
    + eapply big_step_result_value. exact Heval2.
    + eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1].
    + eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2].
    + intros Hobserve. rewrite security_of_protect in Hobserve.
      assert (Hkobs : flows_to (indirect_reader k) observer).
      { eapply flows_to_join_right. exact Hobserve. }
      destruct Hctrl as [_ [_ [_ [_ Hshape]]]].
      destruct (Hshape Hkobs) as [Hleft | Hright].
      * destruct Hleft as [x [y [sx [sy [E1 [E2 Hunit]]]]]].
        inversion E1; inversion E2; subst. clear Hunit.
        destruct (IHHtype2 observer rho1 rho2 Henv) as [_ [_ Hlift]].
        assert (Hyes : value_relation observer T result result0).
        { eapply Hlift.
          - exact (proj1 (big_step_iff_evaluates _ _) H7).
          - exact (proj1 (big_step_iff_evaluates _ _) H10). }
        eapply value_relation_protect_invariant_asym. exact Hyes.
      * destruct Hright as [x [y [sx [sy [E1 [E2 Hunit]]]]]].
        discriminate E1.
    + assert (Hctrl : value_relation observer
        (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
        (tm_inl v k0) (tm_inr v0 k1)).
      { destruct (IHHtype1 observer rho1 rho2 Henv) as [_ [_ Hlift]].
        eapply Hlift.
        - exact (proj1 (big_step_iff_evaluates _ _) H5).
        - exact (proj1 (big_step_iff_evaluates _ _) H8). }
      pose proof (proj2 (typing_regular _ _ _ Htype2)) as HwfT.
      eapply value_relation_subtype_conditional.
      * apply subtype_self_protect. exact HwfT.
      * eapply big_step_result_value. exact Heval1.
      * eapply big_step_result_value. exact Heval2.
      * eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1].
      * eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2].
      * intros Hobserve. rewrite security_of_protect in Hobserve.
        assert (Hkobs : flows_to (indirect_reader k) observer).
        { eapply flows_to_join_right. exact Hobserve. }
        destruct Hctrl as [_ [_ [_ [_ Hshape]]]].
        destruct (Hshape Hkobs) as [Hleft | Hright].
        -- destruct Hleft as [a [b [ka [kb [E1 [E2 Hab]]]]]]. discriminate E2.
        -- destruct Hright as [a [b [ka [kb [E1 [E2 Hab]]]]]]. discriminate E1.
    + assert (Hctrl : value_relation observer
        (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
        (tm_inr v k0) (tm_inl v0 k1)).
      { destruct (IHHtype1 observer rho1 rho2 Henv) as [_ [_ Hlift]].
        eapply Hlift.
        - exact (proj1 (big_step_iff_evaluates _ _) H5).
        - exact (proj1 (big_step_iff_evaluates _ _) H8). }
      pose proof (proj2 (typing_regular _ _ _ Htype2)) as HwfT.
      eapply value_relation_subtype_conditional.
      * apply subtype_self_protect. exact HwfT.
      * eapply big_step_result_value. exact Heval1.
      * eapply big_step_result_value. exact Heval2.
      * eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1].
      * eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2].
      * intros Hobserve. rewrite security_of_protect in Hobserve.
        assert (Hkobs : flows_to (indirect_reader k) observer).
        { eapply flows_to_join_right. exact Hobserve. }
        destruct Hctrl as [_ [_ [_ [_ Hshape]]]].
        destruct (Hshape Hkobs) as [Hleft | Hright].
        -- destruct Hleft as [a [b [ka [kb [E1 [E2 Hab]]]]]]. discriminate E1.
        -- destruct Hright as [a [b [ka [kb [E1 [E2 Hab]]]]]]. discriminate E2.
    + assert (Hctrl : value_relation observer
        (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
        (tm_inr v k0) (tm_inr v0 k1)).
      { destruct (IHHtype1 observer rho1 rho2 Henv) as [_ [_ Hlift]].
        eapply Hlift.
        - exact (proj1 (big_step_iff_evaluates _ _) H5).
        - exact (proj1 (big_step_iff_evaluates _ _) H8). }
      pose proof (proj2 (typing_regular _ _ _ Htype3)) as HwfT.
      eapply value_relation_subtype_conditional.
      * apply subtype_self_protect. exact HwfT.
      * eapply big_step_result_value. exact Heval1.
      * eapply big_step_result_value. exact Heval2.
      * eapply underlying_typed_evaluates; [exact Hinst1 | apply big_step_iff_evaluates; exact Heval1].
      * eapply underlying_typed_evaluates; [exact Hinst2 | apply big_step_iff_evaluates; exact Heval2].
      * intros Hobserve. rewrite security_of_protect in Hobserve.
        assert (Hkobs : flows_to (indirect_reader k) observer).
        { eapply flows_to_join_right. exact Hobserve. }
        destruct Hctrl as [_ [_ [_ [_ Hshape]]]].
        destruct (Hshape Hkobs) as [Hleft | Hright].
        -- destruct Hleft as [a [b [ka [kb [E1 [E2 Hab]]]]]]. discriminate E1.
        -- destruct Hright as [a [b [ka [kb [E1 [E2 Hab]]]]]].
           inversion E1; inversion E2; subst. clear Hab.
           destruct (IHHtype3 observer rho1 rho2 Henv) as [_ [_ Hlift]].
           assert (Hno : value_relation observer T result result0).
           { eapply Hlift.
             - exact (proj1 (big_step_iff_evaluates _ _) H7).
             - exact (proj1 (big_step_iff_evaluates _ _) H10). }
           eapply value_relation_protect_invariant_asym. exact Hno.
Admitted.

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
  intros C t1 t2 T_secret T_result Ht1 Ht2 Hctx Hground Htransparent Hflow.
  destruct Hctx as [L Hctx].
  destruct (fresh_atom (L ++ context_support C)) as [x Hfresh].
  assert (HxL : ~ In x L) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
  assert (HxSupport : ~ In x (context_support C))
    by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
  specialize (Hctx x HxL) as Hroot.
  set (rho1 := substitution_update (fun y => tm_fvar y) x t1).
  set (rho2 := substitution_update (fun y => tm_fvar y) x t2).
  assert (Hopaque : expression_relation (security_of T_result).(indirect_reader)
    T_secret t1 t2).
  { eapply opaque_typed_inputs_related; eauto. }
  assert (Henv : related_expression_substitutions (security_of T_result).(indirect_reader)
    (update empty x T_secret) rho1 rho2).
  { intros y U Hlookup.
    unfold rho1, rho2, substitution_update.
    destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. rewrite lookup_update_eq in Hlookup.
      inversion Hlookup; subst U. rewrite !Nat.eqb_refl. exact Hopaque.
    - rewrite lookup_update_neq in Hlookup by (apply Nat.eqb_neq; exact E).
      simpl in Hlookup. discriminate. }
  pose proof (fundamental_expressions _ _ _ Hroot (security_of T_result).(indirect_reader)
    rho1 rho2 Henv) as Hrelctx.
  assert (Erho1 : instantiate rho1 (plug C (tm_fvar x)) = plug C t1).
  { unfold rho1. rewrite instantiate_context_plug.
    rewrite (instantiate_context_identity C x t1) by exact HxSupport.
    simpl. unfold rho1, substitution_update. rewrite Nat.eqb_refl. reflexivity. }
  assert (Erho2 : instantiate rho2 (plug C (tm_fvar x)) = plug C t2).
  { unfold rho2. rewrite instantiate_context_plug.
    rewrite (instantiate_context_identity C x t2) by exact HxSupport.
    simpl. unfold rho2, substitution_update. rewrite Nat.eqb_refl. reflexivity. }
  destruct Hrelctx as [_ [_ Hlift]].
  intros v1 v2 Heval1 Heval2.
  rewrite <- Erho1 in Heval1. rewrite <- Erho2 in Heval2.
  pose proof (Hlift v1 v2 Heval1 Heval2) as Hvalues.
  eapply observable_related_values_equal.
  - exact Hground.
  - exact Htransparent.
  - apply flows_to_refl.
  - exact Hvalues.
Qed.
