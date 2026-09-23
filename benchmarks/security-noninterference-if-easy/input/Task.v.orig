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
  | Ty_Arrow : ty -> ty -> security -> ty.

Definition security_of (T : ty) : security :=
  match T with
  | Ty_Unit kappa => kappa
  | Ty_Sum _ _ kappa | Ty_Prod _ _ kappa | Ty_Arrow _ _ kappa => kappa
  end.

Definition ty_protect (l : label) (T : ty) : ty :=
  match T with
  | Ty_Unit kappa => Ty_Unit (protect_security kappa l)
  | Ty_Sum T1 T2 kappa => Ty_Sum T1 T2 (protect_security kappa l)
  | Ty_Prod T1 T2 kappa => Ty_Prod T1 T2 (protect_security kappa l)
  | Ty_Arrow T1 T2 kappa => Ty_Arrow T1 T2 (protect_security kappa l)
  end.

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
  | tm_protect : label -> tm -> tm
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
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_unit _ => []
  | tm_fvar x => [x]
  | tm_abs _ body _ => fv body
  | tm_app t1 t2 _ | tm_pair t1 t2 _ => fv t1 ++ fv t2
  | tm_fst t1 _ | tm_snd t1 _ | tm_inl t1 _ | tm_inr t1 _
  | tm_protect _ t1 => fv t1
  | tm_case t0 body1 body2 _ | tm_if t0 body1 body2 _ => fv t0 ++ fv body1 ++ fv body2
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
  | v_inr : forall v kappa, value v -> value (tm_inr v kappa).

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
  | tm_if c yes no _ => tm_if (erase_security c) (erase_security yes) (erase_security no) Low
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
      has_type Gamma t T -> subtype T U -> has_type Gamma t U
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

Lemma subtype_refl : forall T, wf_ty T -> subtype T T.
Proof.
  induction T; simpl; intros Hwf.
  - apply S_Unit; try assumption; apply security_le_refl.
  - destruct Hwf as [H1 [H2 Hk]]. apply S_Sum; auto using security_le_refl.
  - destruct Hwf as [H1 [H2 Hk]]. apply S_Prod; auto using security_le_refl.
  - destruct Hwf as [H1 [H2 Hk]]. apply S_Arrow; auto using security_le_refl.
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
  | B_IfTrue : forall c yes no r v k result,
      big_step c (tm_inl v k) -> flows_to k.(reader) r -> big_step yes result ->
      big_step (tm_if c yes no r) (protect_value result k.(indirect_reader))
  | B_IfFalse : forall c yes no r v k result,
      big_step c (tm_inr v k) -> flows_to k.(reader) r -> big_step no result ->
      big_step (tm_if c yes no r) (protect_value result k.(indirect_reader)).

Lemma value_protect : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv. inversion Hv; subst; simpl;
    eauto using v_unit, v_abs, v_pair, v_inl, v_inr.
Qed.

Lemma big_step_result_value : forall t v, big_step t v -> value v.
Proof.
  intros t v H. induction H;
    eauto using v_unit, v_abs, v_pair, v_inl, v_inr, value_protect.
  - inversion IHbig_step; subst. apply value_protect; assumption.
  - inversion IHbig_step; subst. apply value_protect; assumption.
Qed.

Lemma big_step_value_refl : forall v, value v -> big_step v v.
Proof.
  intros v Hv. induction Hv;
    eauto using B_Unit, B_Abs, B_Pair, B_Inl, B_Inr.
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
      B_Inl, B_Inr, B_CaseLeft, B_CaseRight, B_Protect, B_IfTrue, B_IfFalse,
      big_step_value_refl.
  all: try (match goal with Hv : value ?v, He : big_step ?v ?w |- _ =>
    pose proof (big_step_value_inv v w Hv He); subst w end).
  all: try solve [eauto using B_App, B_Fst, B_Snd, B_CaseLeft,
    B_CaseRight, B_Protect, B_IfTrue, B_IfFalse, B_Pair, B_Inl, B_Inr, big_step_value_refl].
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
    try solve [apply T_Inr; auto using protect_security_wf].
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
      T_App, T_Pair, T_Fst, T_Snd, T_Inl, T_Inr, T_Protect.
  - eapply T_Case with (L := L); eauto.
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
    end).

Definition expression_relation (observer : label) (T : ty) (t1 t2 : tm) : Prop :=
  underlying_typed T t1 /\ underlying_typed T t2 /\
  expression_lifting (value_relation observer T) t1 t2.

Lemma value_relation_properties : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  value v1 /\ value v2 /\ underlying_typed T v1 /\ underlying_typed T v2.
Proof. intros observer T. destruct T; simpl; tauto. Qed.

Lemma value_relation_protect_values : forall T observer v1 v2 l1 l2,
  value_relation observer T v1 v2 ->
  value_relation observer T (protect_value v1 l1) (protect_value v2 l2).
Proof.
  induction T; intros observer v1 v2 l1 l2 Hrel;
    destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hrel]]]].
  all: split; [apply value_protect; exact Hv1 |].
  all: split; [apply value_protect; exact Hv2 |].
  all: split; [unfold underlying_typed; rewrite erase_protect_value; exact Ht1 |].
  all: split; [unfold underlying_typed; rewrite erase_protect_value; exact Ht2 |].
  all: intros Hvis; specialize (Hrel Hvis).
  - destruct Hrel as [k1 [k2 [-> ->]]].
    exists (protect_security k1 l1), (protect_security k2 l2). auto.
  - destruct Hrel as [Hl | Hr].
    + left. destruct Hl as [a1 [a2 [k1 [k2 [-> [-> Ha]]]]]].
      exists a1, a2, (protect_security k1 l1), (protect_security k2 l2). auto.
    + right. destruct Hr as [a1 [a2 [k1 [k2 [-> [-> Ha]]]]]].
      exists a1, a2, (protect_security k1 l1), (protect_security k2 l2). auto.
  - destruct Hrel as [a1 [b1 [a2 [b2 [k1 [k2 [-> [-> [Ha Hb]]]]]]]]].
    exists a1, b1, a2, b2, (protect_security k1 l1), (protect_security k2 l2). auto.
  - destruct Hrel as [A1 [A2 [b1 [b2 [k1 [k2 [-> [-> Hfun]]]]]]]].
    exists A1, A2, b1, b2, (protect_security k1 l1), (protect_security k2 l2).
    split; [reflexivity |]. split; [reflexivity |].
    intros a1 a2 Ha w1 w2 Heval1 Heval2.
    destruct (value_relation_properties _ _ _ _ Ha) as [Ha1 [Ha2 _]].
    destruct (evaluates_protected_function _ _ _ _ Hv1 Ha1 Heval1)
      as [u1 [Hu1 ->]].
    destruct (evaluates_protected_function _ _ _ _ Hv2 Ha2 Heval2)
      as [u2 [Hu2 ->]].
    apply IHT2. eapply Hfun; eassumption.
Qed.

Lemma value_relation_ty_protect : forall T observer l v1 v2,
  value_relation observer (ty_protect l T) v1 v2 <->
  value v1 /\ value v2 /\ underlying_typed T v1 /\ underlying_typed T v2 /\
  (flows_to l observer -> value_relation observer T v1 v2).
Proof.
  intros T observer l v1 v2. destruct T; destruct s as [r ir];
    destruct r, ir, observer, l; simpl; unfold underlying_typed; simpl; tauto.
Qed.

Lemma value_relation_protect : forall T observer l v1 v2,
  value_relation observer T v1 v2 ->
  value_relation observer (ty_protect l T)
    (protect_value v1 l) (protect_value v2 l).
Proof.
  intros T observer l v1 v2 Hrel.
  destruct (value_relation_properties _ _ _ _ Hrel) as [Hv1 [Hv2 [Ht1 Ht2]]].
  apply value_relation_ty_protect.
  split; [apply value_protect; exact Hv1 |].
  split; [apply value_protect; exact Hv2 |].
  split; [unfold underlying_typed; rewrite erase_protect_value; exact Ht1 |].
  split; [unfold underlying_typed; rewrite erase_protect_value; exact Ht2 |].
  intros _. apply value_relation_protect_values; assumption.
Qed.

Lemma underlying_typed_evaluates : forall T t v,
  underlying_typed T t -> evaluates t v -> underlying_typed T v.
Proof.
  intros T t v Ht Heval. unfold underlying_typed in *.
  destruct (evaluates_erasure _ _ Heval) as [Hsteps _].
  eapply preservation_multi; eassumption.
Qed.

Lemma hidden_values_related : forall observer T v1 v2,
  ~ flows_to (security_of T).(indirect_reader) observer ->
  value v1 -> value v2 -> underlying_typed T v1 -> underlying_typed T v2 ->
  value_relation observer T v1 v2.
Proof.
  intros observer T v1 v2 Hhidden Hv1 Hv2 Ht1 Ht2.
  destruct T.
  all: split; [exact Hv1 |].
  all: split; [exact Hv2 |].
  all: split; [exact Ht1 |].
  all: split; [exact Ht2 |].
  all: contradiction.
Qed.

Lemma hidden_expressions_related : forall observer T t1 t2,
  ~ flows_to (security_of T).(indirect_reader) observer ->
  underlying_typed T t1 -> underlying_typed T t2 ->
  expression_relation observer T t1 t2.
Proof.
  intros observer T t1 t2 Hhidden Ht1 Ht2.
  split; [exact Ht1 |]. split; [exact Ht2 |].
  intros v1 v2 Heval1 Heval2. apply hidden_values_related; try assumption.
  - exact (proj2 Heval1).
  - exact (proj2 Heval2).
  - exact (underlying_typed_evaluates _ _ _ Ht1 Heval1).
  - exact (underlying_typed_evaluates _ _ _ Ht2 Heval2).
Qed.

Lemma expression_relation_protect : forall observer T t1 t2 l,
  expression_relation observer T t1 t2 ->
  expression_relation observer (ty_protect l T)
    (tm_protect l t1) (tm_protect l t2).
Proof.
  intros observer T t1 t2 l [Ht1 [Ht2 Hrel]].
  split; [unfold underlying_typed in *; simpl; rewrite erase_ty_protect; exact Ht1 |].
  split; [unfold underlying_typed in *; simpl; rewrite erase_ty_protect; exact Ht2 |].
  intros v1 v2 Heval1 Heval2.
  apply big_step_iff_evaluates in Heval1, Heval2.
  inversion Heval1; subst. inversion Heval2; subst.
  apply value_relation_protect. apply Hrel;
    apply big_step_iff_evaluates; assumption.
Qed.

Lemma flows_to_dec : forall l observer,
  {flows_to l observer} + {~ flows_to l observer}.
Proof. destruct l, observer; simpl; auto. Defined.

Lemma visible_ty_protect : forall T l observer,
  flows_to (security_of (ty_protect l T)).(indirect_reader) observer ->
  flows_to l observer.
Proof.
  destruct T; intros l observer; destruct s as [r ir];
    destruct ir, l, observer; simpl; tauto.
Qed.

Lemma value_relation_raise_type : forall observer T l v1 v2,
  value_relation observer T v1 v2 ->
  value_relation observer (ty_protect l T) v1 v2.
Proof.
  intros observer T l v1 v2 H.
  destruct (value_relation_properties _ _ _ _ H) as [Hv1 [Hv2 [Ht1 Ht2]]].
  apply value_relation_ty_protect. auto.
Qed.

Lemma expression_relation_app : forall observer A B k f1 f2 a1 a2 r,
  expression_relation observer (Ty_Arrow A B k) f1 f2 ->
  expression_relation observer A a1 a2 ->
  expression_relation observer (ty_protect k.(indirect_reader) B)
    (tm_app f1 a1 r) (tm_app f2 a2 r).
Proof.
  intros observer A B k f1 f2 a1 a2 r [Hf1 [Hf2 Hf]] [Ha1 [Ha2 Ha]].
  assert (underlying_typed (ty_protect k.(indirect_reader) B)
    (tm_app f1 a1 r)) as Htyped1.
  { unfold underlying_typed in *. simpl. rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type B)).
    eapply T_App with (kappa := public); [exact Hf1 | exact Ha1 | exact I]. }
  assert (underlying_typed (ty_protect k.(indirect_reader) B)
    (tm_app f2 a2 r)) as Htyped2.
  { unfold underlying_typed in *. simpl. rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type B)).
    eapply T_App with (kappa := public); [exact Hf2 | exact Ha2 | exact I]. }
  destruct (flows_to_dec k.(indirect_reader) observer) as [Hvis | Hhidden].
  - split; [exact Htyped1 |]. split; [exact Htyped2 |].
    intros w1 w2 Heval1 Heval2.
    apply big_step_iff_evaluates in Heval1, Heval2.
    inversion Heval1; subst. inversion Heval2; subst.
    assert (value_relation observer (Ty_Arrow A B k)
      (tm_abs A0 body k0) (tm_abs A1 body0 k1)) as Hfunctions.
    { apply Hf; apply big_step_iff_evaluates; assumption. }
    destruct Hfunctions as [Hval1 [Hval2 [_ [_ Hfunctions]]]].
    specialize (Hfunctions Hvis).
    destruct Hfunctions as [U1 [U2 [b1 [b2 [ka [kb [E1 [E2 Hfunctions]]]]]]]].
    inversion E1; inversion E2; subst.
    apply value_relation_raise_type.
    eapply Hfunctions.
    + apply Ha; apply big_step_iff_evaluates; eassumption.
    + apply big_step_iff_evaluates. eapply B_App;
        eauto using big_step_value_refl, big_step_result_value.
      destruct ka.(reader); exact I.
    + apply big_step_iff_evaluates. eapply B_App;
        eauto using big_step_value_refl, big_step_result_value.
      destruct kb.(reader); exact I.
  - apply hidden_expressions_related; try assumption.
    intro Hvisible. apply Hhidden. eapply visible_ty_protect; exact Hvisible.
Qed.

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

Lemma expression_relation_unit : forall observer k,
  expression_relation observer (Ty_Unit k) (tm_unit k) (tm_unit k).
Proof.
  intros observer k. apply related_values_are_related_expressions.
  split; [constructor |]. split; [constructor |].
  split; [apply T_Unit; exact I |]. split; [apply T_Unit; exact I |].
  intros _. exists k, k. auto.
Qed.

Lemma expression_relation_abs : forall observer A B k body1 body2,
  underlying_typed (Ty_Arrow A B k) (tm_abs A body1 k) ->
  underlying_typed (Ty_Arrow A B k) (tm_abs A body2 k) ->
  locally_closed (tm_abs A body1 k) -> locally_closed (tm_abs A body2 k) ->
  (forall a1 a2, value_relation observer A a1 a2 ->
    expression_relation observer B (open body1 a1) (open body2 a2)) ->
  expression_relation observer (Ty_Arrow A B k)
    (tm_abs A body1 k) (tm_abs A body2 k).
Proof.
  intros observer A B k body1 body2 Ht1 Ht2 Hlc1 Hlc2 Hb.
  apply related_values_are_related_expressions.
  split; [apply v_abs; exact Hlc1 |]. split; [apply v_abs; exact Hlc2 |].
  split; [exact Ht1 |]. split; [exact Ht2 |]. intros Hvis.
  exists A, A, body1, body2, k, k. split; [reflexivity |]. split; [reflexivity |].
  intros a1 a2 Ha w1 w2 He1 He2.
  destruct (value_relation_properties _ _ _ _ Ha) as [Hva1 [Hva2 _]].
  destruct (Hb a1 a2 Ha) as [_ [_ Hbody]].
  apply big_step_iff_evaluates in He1, He2.
  inversion He1; subst. inversion He2; subst.
  repeat match goal with
  | He : big_step (tm_abs _ _ _) _ |- _ => inversion He; subst; clear He
  | Hv : value ?v, He : big_step ?v ?w |- _ =>
      pose proof (big_step_value_inv _ _ Hv He) as ->; clear He
  end.
  apply value_relation_protect_values.
  apply Hbody; apply big_step_iff_evaluates; assumption.
Qed.

Lemma expression_relation_pair : forall observer A B k a1 a2 b1 b2,
  expression_relation observer A a1 a2 ->
  expression_relation observer B b1 b2 ->
  expression_relation observer (Ty_Prod A B k)
    (tm_pair a1 b1 k) (tm_pair a2 b2 k).
Proof.
  intros observer A B k a1 a2 b1 b2 [Ha1 [Ha2 Ha]] [Hb1 [Hb2 Hb]].
  split; [apply T_Pair; [exact Ha1 | exact Hb1 | exact I] |].
  split; [apply T_Pair; [exact Ha2 | exact Hb2 | exact I] |].
  intros v1 v2 He1 He2. apply big_step_iff_evaluates in He1, He2.
  inversion He1; subst. inversion He2; subst.
  assert (value_relation observer A v v0) as Hva
    by (apply Ha; apply big_step_iff_evaluates; assumption).
  assert (value_relation observer B w w0) as Hvb
    by (apply Hb; apply big_step_iff_evaluates; assumption).
  destruct (value_relation_properties _ _ _ _ Hva) as [Hav1 [Hav2 [Hat1 Hat2]]].
  destruct (value_relation_properties _ _ _ _ Hvb) as [Hbv1 [Hbv2 [Hbt1 Hbt2]]].
  split; [apply v_pair; assumption |]. split; [apply v_pair; assumption |].
  split; [apply T_Pair; [exact Hat1 | exact Hbt1 | exact I] |].
  split; [apply T_Pair; [exact Hat2 | exact Hbt2 | exact I] |].
  intros _. exists v, w, v0, w0, k, k. auto.
Qed.

Lemma expression_relation_inl : forall observer A B k t1 t2,
  expression_relation observer A t1 t2 ->
  expression_relation observer (Ty_Sum A B k) (tm_inl t1 k) (tm_inl t2 k).
Proof.
  intros observer A B k t1 t2 [Ht1 [Ht2 Hr]].
  split; [apply T_Inl; [exact Ht1 | apply erase_type_wf | exact I] |].
  split; [apply T_Inl; [exact Ht2 | apply erase_type_wf | exact I] |].
  intros v1 v2 He1 He2. apply big_step_iff_evaluates in He1, He2.
  inversion He1; subst. inversion He2; subst.
  assert (value_relation observer A v v0) as Hv
    by (apply Hr; apply big_step_iff_evaluates; assumption).
  destruct (value_relation_properties _ _ _ _ Hv) as [Hval1 [Hval2 [Hv1 Hv2]]].
  split; [apply v_inl; exact Hval1 |]. split; [apply v_inl; exact Hval2 |].
  split; [apply T_Inl; [exact Hv1 | apply erase_type_wf | exact I] |].
  split; [apply T_Inl; [exact Hv2 | apply erase_type_wf | exact I] |].
  intros _. left. exists v, v0, k, k. auto.
Qed.

Lemma expression_relation_inr : forall observer A B k t1 t2,
  expression_relation observer B t1 t2 ->
  expression_relation observer (Ty_Sum A B k) (tm_inr t1 k) (tm_inr t2 k).
Proof.
  intros observer A B k t1 t2 [Ht1 [Ht2 Hr]].
  split; [apply T_Inr; [apply erase_type_wf | exact Ht1 | exact I] |].
  split; [apply T_Inr; [apply erase_type_wf | exact Ht2 | exact I] |].
  intros v1 v2 He1 He2. apply big_step_iff_evaluates in He1, He2.
  inversion He1; subst. inversion He2; subst.
  assert (value_relation observer B v v0) as Hv
    by (apply Hr; apply big_step_iff_evaluates; assumption).
  destruct (value_relation_properties _ _ _ _ Hv) as [Hval1 [Hval2 [Hv1 Hv2]]].
  split; [apply v_inr; exact Hval1 |]. split; [apply v_inr; exact Hval2 |].
  split; [apply T_Inr; [apply erase_type_wf | exact Hv1 | exact I] |].
  split; [apply T_Inr; [apply erase_type_wf | exact Hv2 | exact I] |].
  intros _. right. exists v, v0, k, k. auto.
Qed.

Lemma expression_relation_fst : forall observer A B k t1 t2 r,
  expression_relation observer (Ty_Prod A B k) t1 t2 ->
  expression_relation observer (ty_protect k.(indirect_reader) A)
    (tm_fst t1 r) (tm_fst t2 r).
Proof.
  intros observer A B k t1 t2 r [Ht1 [Ht2 Hr]].
  assert (underlying_typed (ty_protect k.(indirect_reader) A) (tm_fst t1 r)) as HT1.
  { unfold underlying_typed in *. simpl. rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type A)).
    eapply T_Fst with (kappa := public); [exact Ht1 | exact I]. }
  assert (underlying_typed (ty_protect k.(indirect_reader) A) (tm_fst t2 r)) as HT2.
  { unfold underlying_typed in *. simpl. rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type A)).
    eapply T_Fst with (kappa := public); [exact Ht2 | exact I]. }
  destruct (flows_to_dec k.(indirect_reader) observer) as [Hvis | Hhidden].
  - split; [exact HT1 |]. split; [exact HT2 |].
    intros w1 w2 He1 He2. apply big_step_iff_evaluates in He1, He2.
    inversion He1; subst. inversion He2; subst.
    assert (value_relation observer (Ty_Prod A B k)
      (tm_pair a b k0) (tm_pair a0 b0 k1)) as Hpair
      by (apply Hr; apply big_step_iff_evaluates; assumption).
    destruct Hpair as [_ [_ [_ [_ Hpair]]]]. specialize (Hpair Hvis).
    destruct Hpair as [p1 [q1 [p2 [q2 [ka [kb [E1 [E2 [Hp Hq]]]]]]]]].
    inversion E1; inversion E2; subst.
    apply value_relation_raise_type. apply value_relation_protect_values. exact Hp.
  - apply hidden_expressions_related; try assumption.
    intro Hvisible. apply Hhidden. eapply visible_ty_protect; exact Hvisible.
Qed.

Lemma expression_relation_snd : forall observer A B k t1 t2 r,
  expression_relation observer (Ty_Prod A B k) t1 t2 ->
  expression_relation observer (ty_protect k.(indirect_reader) B)
    (tm_snd t1 r) (tm_snd t2 r).
Proof.
  intros observer A B k t1 t2 r [Ht1 [Ht2 Hr]].
  assert (underlying_typed (ty_protect k.(indirect_reader) B) (tm_snd t1 r)) as HT1.
  { unfold underlying_typed in *. simpl. rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type B)).
    eapply T_Snd with (kappa := public); [exact Ht1 | exact I]. }
  assert (underlying_typed (ty_protect k.(indirect_reader) B) (tm_snd t2 r)) as HT2.
  { unfold underlying_typed in *. simpl. rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type B)).
    eapply T_Snd with (kappa := public); [exact Ht2 | exact I]. }
  destruct (flows_to_dec k.(indirect_reader) observer) as [Hvis | Hhidden].
  - split; [exact HT1 |]. split; [exact HT2 |].
    intros w1 w2 He1 He2. apply big_step_iff_evaluates in He1, He2.
    inversion He1; subst. inversion He2; subst.
    assert (value_relation observer (Ty_Prod A B k)
      (tm_pair a b k0) (tm_pair a0 b0 k1)) as Hpair
      by (apply Hr; apply big_step_iff_evaluates; assumption).
    destruct Hpair as [_ [_ [_ [_ Hpair]]]]. specialize (Hpair Hvis).
    destruct Hpair as [p1 [q1 [p2 [q2 [ka [kb [E1 [E2 [Hp Hq]]]]]]]]].
    inversion E1; inversion E2; subst.
    apply value_relation_raise_type. apply value_relation_protect_values. exact Hq.
  - apply hidden_expressions_related; try assumption.
    intro Hvisible. apply Hhidden. eapply visible_ty_protect; exact Hvisible.
Qed.

Lemma expression_relation_case : forall observer A B T k t1 t2 b11 b12 b21 b22 r,
  underlying_typed (ty_protect k.(indirect_reader) T) (tm_case t1 b11 b12 r) ->
  underlying_typed (ty_protect k.(indirect_reader) T) (tm_case t2 b21 b22 r) ->
  expression_relation observer (Ty_Sum A B k) t1 t2 ->
  (forall a1 a2, value_relation observer A a1 a2 ->
    expression_relation observer T (open b11 a1) (open b21 a2)) ->
  (forall a1 a2, value_relation observer B a1 a2 ->
    expression_relation observer T (open b12 a1) (open b22 a2)) ->
  expression_relation observer (ty_protect k.(indirect_reader) T)
    (tm_case t1 b11 b12 r) (tm_case t2 b21 b22 r).
Proof.
  intros observer A B T k t1 t2 b11 b12 b21 b22 r HT1 HT2 [_ [_ Hr]] Hl Hright.
  destruct (flows_to_dec k.(indirect_reader) observer) as [Hvis | Hhidden].
  - split; [exact HT1 |]. split; [exact HT2 |].
    intros w1 w2 He1 He2. apply big_step_iff_evaluates in He1, He2.
    inversion He1; subst; inversion He2; subst.
    all: match goal with
    | Hrel : expression_lifting _ ?scr1 ?scr2,
      E1 : big_step ?scr1 ?v1, E2 : big_step ?scr2 ?v2 |- _ =>
      pose proof (Hrel v1 v2 (big_step_sound _ _ E1) (big_step_sound _ _ E2)) as Hsum
    end.
    all: destruct Hsum as [_ [_ [_ [_ Hsum]]]]; specialize (Hsum Hvis).
    all: destruct Hsum as [Hsum | Hsum];
      destruct Hsum as [p1 [p2 [ka [kb [E1 [E2 Hp]]]]]];
      inversion E1; inversion E2; subst.
    all: apply value_relation_raise_type; apply value_relation_protect_values.
    + destruct (Hl _ _ Hp) as [_ [_ Hbranch]].
      apply Hbranch; apply big_step_iff_evaluates; assumption.
    + destruct (Hright _ _ Hp) as [_ [_ Hbranch]].
      apply Hbranch; apply big_step_iff_evaluates; assumption.
  - apply hidden_expressions_related; try assumption.
    intro Hvisible. apply Hhidden. eapply visible_ty_protect; exact Hvisible.
Qed.

Lemma value_relation_subtype : forall T U,
  subtype T U -> forall observer v1 v2,
  value_relation observer T v1 v2 -> value_relation observer U v1 v2.
Proof.
  intros T U Hsub. induction Hsub; intros observer v1 v2 Hrelated.
  - destruct Hrelated as [Hv1 [Hv2 [Ht1 [Ht2 Hrel]]]].
    repeat split; try assumption. intros Hvis.
    apply Hrel. eapply flows_to_trans; [exact (proj2 H1) | exact Hvis].
  - destruct Hrelated as [Hv1 [Hv2 [Ht1 [Ht2 Hrel]]]].
    assert (erase_type (Ty_Sum T1 T2 kappa1) = erase_type (Ty_Sum U1 U2 kappa2)) as Herase.
    { simpl. rewrite (subtype_erasure _ _ Hsub1), (subtype_erasure _ _ Hsub2). reflexivity. }
    split; [exact Hv1 | ]. split; [exact Hv2 | ].
    split; [unfold underlying_typed in *; rewrite <- Herase; exact Ht1 | ].
    split; [unfold underlying_typed in *; rewrite <- Herase; exact Ht2 | ].
    intros Hvis. specialize (Hrel (flows_to_trans _ _ _ (proj2 H1) Hvis)).
    destruct Hrel as [Hleft | Hright].
    + left. destruct Hleft as [a1 [a2 [k1 [k2 [Heq1 [Heq2 Ha]]]]]].
      exists a1, a2, k1, k2. repeat split; try assumption. apply IHHsub1; exact Ha.
    + right. destruct Hright as [a1 [a2 [k1 [k2 [Heq1 [Heq2 Ha]]]]]].
      exists a1, a2, k1, k2. repeat split; try assumption. apply IHHsub2; exact Ha.
  - destruct Hrelated as [Hv1 [Hv2 [Ht1 [Ht2 Hrel]]]].
    assert (erase_type (Ty_Prod T1 T2 kappa1) = erase_type (Ty_Prod U1 U2 kappa2)) as Herase.
    { simpl. rewrite (subtype_erasure _ _ Hsub1), (subtype_erasure _ _ Hsub2). reflexivity. }
    split; [exact Hv1 | ]. split; [exact Hv2 | ].
    split; [unfold underlying_typed in *; rewrite <- Herase; exact Ht1 | ].
    split; [unfold underlying_typed in *; rewrite <- Herase; exact Ht2 | ].
    intros Hvis. specialize (Hrel (flows_to_trans _ _ _ (proj2 H1) Hvis)).
    destruct Hrel as [a1 [b1 [a2 [b2 [k1 [k2 [Heq1 [Heq2 [Ha Hb]]]]]]]]].
    exists a1, b1, a2, b2, k1, k2. repeat split; try assumption.
    + apply IHHsub1; exact Ha.
    + apply IHHsub2; exact Hb.
  - destruct Hrelated as [Hv1 [Hv2 [Ht1 [Ht2 Hrel]]]].
    assert (erase_type (Ty_Arrow T1 T2 kappa1) = erase_type (Ty_Arrow U1 U2 kappa2)) as Herase.
    { simpl. rewrite (subtype_erasure _ _ Hsub1), (subtype_erasure _ _ Hsub2). reflexivity. }
    split; [exact Hv1 | ]. split; [exact Hv2 | ].
    split; [unfold underlying_typed in *; rewrite <- Herase; exact Ht1 | ].
    split; [unfold underlying_typed in *; rewrite <- Herase; exact Ht2 | ].
    intros Hvis. specialize (Hrel (flows_to_trans _ _ _ (proj2 H1) Hvis)).
    destruct Hrel as [A1 [A2 [body1 [body2 [k1 [k2 [Heq1 [Heq2 Hfunctions]]]]]]]].
    exists A1, A2, body1, body2, k1, k2. split; [exact Heq1 | ]. split; [exact Heq2 | ].
    intros arg1 arg2 Hargs result1 result2 Heval1 Heval2.
    apply IHHsub2. apply (Hfunctions arg1 arg2).
    + apply IHHsub1; exact Hargs.
    + exact Heval1.
    + exact Heval2.
  - apply IHHsub2. apply IHHsub1. exact Hrelated.
Qed.

Lemma expression_relation_subtype : forall T U,
  subtype T U -> forall observer t1 t2,
  expression_relation observer T t1 t2 -> expression_relation observer U t1 t2.
Proof.
  intros T U Hsub observer t1 t2 [Ht1 [Ht2 Hrelated]].
  split.
  - unfold underlying_typed in *. rewrite <- (subtype_erasure _ _ Hsub). exact Ht1.
  - split.
    + unfold underlying_typed in *. rewrite <- (subtype_erasure _ _ Hsub). exact Ht2.
    + intros v1 v2 H1 H2. eapply value_relation_subtype.
      * exact Hsub.
      * apply Hrelated; assumption.
Qed.

Lemma expression_relation_if : forall observer k T c1 c2 y1 y2 n1 n2 r,
  expression_relation observer (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) c1 c2 ->
  expression_relation observer T y1 y2 -> expression_relation observer T n1 n2 ->
  expression_relation observer (ty_protect k.(indirect_reader) T)
    (tm_if c1 y1 n1 r) (tm_if c2 y2 n2 r).
Proof.
  intros observer k T c1 c2 y1 y2 n1 n2 r [Hc1 [Hc2 Hc]] [Hy1 [Hy2 Hy]] [Hn1 [Hn2 Hn]].
  assert (forall c y n,
    underlying_typed (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) c ->
    underlying_typed T y -> underlying_typed T n ->
    underlying_typed (ty_protect k.(indirect_reader) T) (tm_if c y n r)) as HT.
  { intros c y n Hct Hyt Hnt. unfold underlying_typed in *. simpl in *.
    rewrite erase_ty_protect. rewrite <- (ty_protect_low (erase_type T)).
    eapply T_If with (k := public); eauto. exact I. }
  destruct (flows_to_dec k.(indirect_reader) observer) as [Hvis | Hhidden].
  - split; [apply HT; assumption |]. split; [apply HT; assumption |].
    intros w1 w2 He1 He2. apply big_step_iff_evaluates in He1, He2.
    inversion He1; subst; inversion He2; subst.
    all: match goal with
      Hr : expression_lifting (value_relation _ (Ty_Sum _ _ _)) ?c1 ?c2,
      E1 : big_step ?c1 ?v1, E2 : big_step ?c2 ?v2 |- _ =>
      pose proof (Hr v1 v2 (big_step_sound _ _ E1) (big_step_sound _ _ E2)) as Hsum
    end.
    all: destruct Hsum as [_ [_ [_ [_ Hsum]]]]; specialize (Hsum Hvis).
    all: destruct Hsum as [Hsum | Hsum];
      destruct Hsum as [a1 [a2 [ka [kb [E1 [E2 Hargs]]]]]];
      inversion E1; inversion E2; subst.
    all: apply value_relation_raise_type; apply value_relation_protect_values.
    + apply Hy; apply big_step_iff_evaluates; assumption.
    + apply Hn; apply big_step_iff_evaluates; assumption.
  - apply hidden_expressions_related; try (apply HT; assumption).
    intro H. apply Hhidden. eapply visible_ty_protect; exact H.
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

Theorem fundamental_expressions : forall Gamma t T,
  has_type Gamma t T ->
  forall observer rho1 rho2,
    related_expression_substitutions observer Gamma rho1 rho2 ->
    expression_relation observer T (instantiate rho1 t) (instantiate rho2 t).
Proof.
  intros Gamma t T Ht. pose proof Ht as Htyping.
  induction Ht; intros observer rho1 rho2 Henv.
  all: pose proof (related_instantiations_typed _ _ _ _ _ _ Htyping Henv) as [HT1 HT2].
  all: pose proof (related_substitution_lc _ _ _ _ _ _ Htyping Henv) as Hlc.
  - apply Henv; exact H.
  - apply expression_relation_unit.
  - apply expression_relation_abs; try exact HT1; try exact HT2.
    + apply erase_lc_inv. exact (proj1 (typing_regular _ _ _ HT1)).
    + apply erase_lc_inv. exact (proj1 (typing_regular _ _ _ HT2)).
    + intros a1 a2 Ha. destruct (fresh_atom (L ++ fv body)) as [x Hx].
      rewrite in_app_iff in Hx.
      rewrite <- !instantiate_open_update with (x := x) by
        (first [tauto | intros y Hy; specialize (Hlc y Hy); tauto]).
      apply H2; [tauto | apply H1; tauto |].
      apply related_expression_update; assumption.
  - eapply expression_relation_app; [apply IHHt1 | apply IHHt2]; assumption.
  - apply expression_relation_pair; [apply IHHt1 | apply IHHt2]; assumption.
  - eapply expression_relation_fst. apply IHHt; assumption.
  - eapply expression_relation_snd. apply IHHt; assumption.
  - apply expression_relation_inl. apply IHHt; assumption.
  - apply expression_relation_inr. apply IHHt; assumption.
  - eapply expression_relation_case; [exact HT1 | exact HT2 | apply IHHt; assumption | |].
    + intros a1 a2 Ha. destruct (fresh_atom (L ++ fv body1)) as [x Hx].
      rewrite in_app_iff in Hx.
      rewrite <- !instantiate_open_update with (x := x) by
        (first [tauto | intros y Hy; assert (In y (fv (tm_case t body1 body2 r))) as Hmem
          by (simpl; repeat rewrite in_app_iff; tauto); specialize (Hlc y Hmem); tauto]).
      apply H1; [tauto | apply H0; tauto |]. apply related_expression_update; assumption.
    + intros a1 a2 Ha. destruct (fresh_atom (L ++ fv body2)) as [x Hx].
      rewrite in_app_iff in Hx.
      rewrite <- !instantiate_open_update with (x := x) by
        (first [tauto | intros y Hy; assert (In y (fv (tm_case t body1 body2 r))) as Hmem
          by (simpl; repeat rewrite in_app_iff; tauto); specialize (Hlc y Hmem); tauto]).
      apply H3; [tauto | apply H2; tauto |]. apply related_expression_update; assumption.
  - apply expression_relation_protect. apply IHHt; assumption.
  - eapply expression_relation_subtype; [exact H | apply IHHt; assumption].
  - eapply expression_relation_if; [apply IHHt1 | apply IHHt2 | apply IHHt3]; assumption.
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
  | C_Protect : label -> program_context -> program_context
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

Definition same_result (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm,
    evaluates t1 v1 -> evaluates t2 v2 ->
    erase_security v1 = erase_security v2.

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
Admitted.
