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
      has_type Gamma t T -> subtype T U -> has_type Gamma t U.

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
      big_step t v -> big_step (tm_protect l t) (protect_value v l).

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
      B_Inl, B_Inr, B_CaseLeft, B_CaseRight, B_Protect,
      big_step_value_refl.
  all: try (match goal with Hv : value ?v, He : big_step ?v ?w |- _ =>
    pose proof (big_step_value_inv v w Hv He); subst w end).
  all: try solve [eauto using B_App, B_Fst, B_Snd, B_CaseLeft,
    B_CaseRight, B_Protect, B_Pair, B_Inl, B_Inr, big_step_value_refl].
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
  intros Gamma t T Htyped. induction Htyped; intros A b k Heq; inversion Heq; subst.
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
  intros Gamma t T Htyped. induction Htyped; intros a b k Heq; inversion Heq; subst.
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
  intros Gamma t T Htyped. induction Htyped; intros a k Heq; inversion Heq; subst.
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
  intros Gamma t T Htyped. induction Htyped; intros a k Heq; inversion Heq; subst.
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

Lemma value_relation_properties : forall (observer : label) T v1 v2,
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

Lemma related_values_are_related_expressions : forall (observer : label) T v1 v2,
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

Definition same_result (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm,
    evaluates t1 v1 -> evaluates t2 v2 ->
    erase_security v1 = erase_security v2.


Lemma related_ground_values_equal : forall (kappa : security) (observer : label) T v1 v2,
  ground T -> transparent_at kappa T ->
  flows_to kappa.(indirect_reader) observer ->
  flows_to (security_of T).(indirect_reader) kappa.(indirect_reader) ->
  value_relation observer T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  assert (forall k T, transparent_at k T ->
    security_le (security_of T) k) as Htrans.
  { intros k T. destruct T; simpl; intros H; tauto. }
  induction T; intros v1 v2 Hg Htr Hflow Hsecflow Hr; simpl in *.
  - destruct Hr as [Hv1 [Hv2 [_ [_ Hshape]]]].
    specialize (Hshape (flows_to_trans _ _ _ Hsecflow Hflow)).
    destruct Hshape as [k1 [k2 [E1 E2]]]. subst v1. subst v2. reflexivity.
  - destruct Hg as [Hg1 Hg2]. destruct Htr as [Hsec [Ht1 Ht2]].
    unfold transparent_at in Ht1, Ht2; simpl in Ht1, Ht2.
    destruct Hr as [Hv1 [Hv2 [_ [_ Hshape]]]].
    specialize (Hshape (flows_to_trans _ _ _ Hsecflow Hflow)).
    destruct Hshape as [Hleft | Hright].
    + destruct Hleft as [u1 [u2 [k1 [k2 [-> [-> Hrel]]]]]].
      simpl. f_equal. eapply IHT1; [exact Hg1 | exact Ht1 | exact Hflow |
        exact (proj2 (Htrans kappa T1 Ht1)) | exact Hrel].
    + destruct Hright as [u1 [u2 [k1 [k2 [-> [-> Hrel]]]]]].
      simpl. f_equal. eapply IHT2; [exact Hg2 | exact Ht2 | exact Hflow |
        exact (proj2 (Htrans kappa T2 Ht2)) | exact Hrel].
  - destruct Hg as [Hg1 Hg2]. destruct Htr as [Hsec [Ht1 Ht2]].
    unfold transparent_at in Ht1, Ht2; simpl in Ht1, Ht2.
    destruct Hr as [Hv1 [Hv2 [_ [_ Hshape]]]].
    specialize (Hshape (flows_to_trans _ _ _ Hsecflow Hflow)).
    destruct Hshape as [a1 [b1 [a2 [b2 [k1 [k2 [-> [-> [Ha Hb]]]]]]]]].
    simpl. f_equal.
    + eapply IHT1; [exact Hg1 | exact Ht1 | exact Hflow |
        exact (proj2 (Htrans kappa T1 Ht1)) | exact Ha].
    + eapply IHT2; [exact Hg2 | exact Ht2 | exact Hflow |
        exact (proj2 (Htrans kappa T2 Ht2)) | exact Hb].
  - contradiction.
Qed.

Lemma underlying_typed_of_typing : forall T t,
  has_type empty t T -> underlying_typed T t.
Proof.
  intros T t H. unfold underlying_typed. pose proof (typing_erasure _ _ _ H) as E.
  unfold erase_context, empty in E. simpl in E. exact E.
Qed.

Lemma secret_values_related : forall observer T v1 v2,
  underlying_typed T v1 -> underlying_typed T v2 ->
  value v1 -> value v2 ->
  ~ flows_to (security_of T).(indirect_reader) observer ->
  value_relation observer T v1 v2.
Proof.
  intros observer T v1 v2 Ht1 Ht2 Hv1 Hv2 Hn.
  destruct T; simpl.
  all: split; [exact Hv1 |].
  all: split; [exact Hv2 |].
  all: split; [exact Ht1 |].
  all: split; [exact Ht2 |].
  all: intros Hflow; exfalso; apply Hn; exact Hflow.
Qed.

Lemma secret_expressions_related : forall observer T t1 t2,
  has_type empty t1 T -> has_type empty t2 T ->
  ~ flows_to (security_of T).(indirect_reader) observer ->
  expression_relation observer T t1 t2.
Proof.
  intros observer T t1 t2 Ht1 Ht2 Hn. split.
  - apply underlying_typed_of_typing; assumption.
  - split.
    + apply underlying_typed_of_typing; assumption.
    + intros v1 v2 He1 He2.
      assert (underlying_typed T v1) as Htv1.
      { pose proof (underlying_typed_of_typing _ _ Ht1) as Hu.
        eapply underlying_typed_evaluates; eassumption. }
      assert (underlying_typed T v2) as Htv2.
      { pose proof (underlying_typed_of_typing _ _ Ht2) as Hu.
        eapply underlying_typed_evaluates; eassumption. }
      eapply secret_values_related; [exact Htv1 | exact Htv2 |
        eapply big_step_result_value; apply big_step_iff_evaluates; exact He1 |
        eapply big_step_result_value; apply big_step_iff_evaluates; exact He2 |
        exact Hn].
Qed.

Lemma related_values_subtype : forall observer T U v1 v2,
  subtype T U -> value_relation observer T v1 v2 ->
  value_relation observer U v1 v2.
Proof.
  intros observer T U v1 v2 Hsub. revert v1 v2. induction Hsub; intros v1 v2 Hrel; simpl in *.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    split; [exact Hv1|]. split; [exact Hv2|].
    split; [exact Ht1|]. split; [exact Ht2|].
    intros Hflow. apply Hshape. eapply flows_to_trans; [exact (proj2 H1)|exact Hflow].
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    split; [exact Hv1|]. split; [exact Hv2|].
    split.
    + unfold underlying_typed in *. cbn [erase_type].
      rewrite <- (subtype_erasure _ _ Hsub1), <- (subtype_erasure _ _ Hsub2). exact Ht1.
    + split.
      * unfold underlying_typed in *. cbn [erase_type].
        rewrite <- (subtype_erasure _ _ Hsub1), <- (subtype_erasure _ _ Hsub2). exact Ht2.
      * intros Hflow. destruct (Hshape (flows_to_trans _ _ _ (proj2 H1) Hflow)) as [Hl|Hr].
          -- left. destruct Hl as [u1 [u2 [k1 [k2 [-> [-> Hx]]]]]].
          exists u1,u2,k1,k2. repeat split; try reflexivity. eapply IHHsub1; exact Hx.
          -- right. destruct Hr as [u1 [u2 [k1 [k2 [-> [-> Hx]]]]]].
          exists u1,u2,k1,k2. repeat split; try reflexivity. eapply IHHsub2; exact Hx.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    split; [exact Hv1|]. split; [exact Hv2|].
    split.
    + unfold underlying_typed in *. cbn [erase_type].
      rewrite <- (subtype_erasure _ _ Hsub1), <- (subtype_erasure _ _ Hsub2). exact Ht1.
    + split.
      * unfold underlying_typed in *. cbn [erase_type].
        rewrite <- (subtype_erasure _ _ Hsub1), <- (subtype_erasure _ _ Hsub2). exact Ht2.
      * intros Hflow. destruct (Hshape (flows_to_trans _ _ _ (proj2 H1) Hflow))
          as [a1 [b1 [a2 [b2 [k1 [k2 [-> [-> [Ha Hb]]]]]]]]].
        exists a1,b1,a2,b2,k1,k2. repeat split; try reflexivity.
          -- eapply IHHsub1; exact Ha.
          -- eapply IHHsub2; exact Hb.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    split; [exact Hv1|]. split; [exact Hv2|].
    split.
    + unfold underlying_typed in *. cbn [erase_type].
      rewrite (subtype_erasure _ _ Hsub1), <- (subtype_erasure _ _ Hsub2). exact Ht1.
    + split.
      * unfold underlying_typed in *. cbn [erase_type].
        rewrite (subtype_erasure _ _ Hsub1), <- (subtype_erasure _ _ Hsub2). exact Ht2.
      * intros Hflow.
        destruct (Hshape (flows_to_trans _ _ _ (proj2 H1) Hflow))
          as [A1 [A2 [b1 [b2 [k1 [k2 [-> [-> Hfun]]]]]]]].
        exists A1,A2,b1,b2,k1,k2. repeat split; try reflexivity.
        intros arg1 arg2 Hargs.
        assert (value_relation observer T1 arg1 arg2) as HargsT.
        { eapply IHHsub1; exact Hargs. }
        specialize (Hfun arg1 arg2 HargsT). unfold expression_lifting in Hfun.
        intros w1 w2 He1 He2. eapply IHHsub2. apply Hfun; assumption.
  - eapply IHHsub2. eapply IHHsub1. exact Hrel.
Qed.


Lemma flows_to_join_left : forall l1 l2 observer,
  flows_to (join l1 l2) observer -> flows_to l1 observer.
Proof. destruct l1, l2, observer; simpl; tauto. Qed.

Lemma flows_to_join_right : forall l1 l2 observer,
  flows_to (join l1 l2) observer -> flows_to l2 observer.
Proof. destruct l1, l2, observer; simpl; tauto. Qed.

Lemma subtype_protect_self : forall T l,
  wf_ty T -> subtype T (ty_protect l T).
Proof.
  intros T l Hwf.
  pose proof (subtype_protect T T (subtype_refl T Hwf) Low l) as Hsub.
  assert (flows_to Low l) as Hlow by (destruct l; exact I).
  specialize (Hsub Hlow). rewrite ty_protect_low in Hsub. exact Hsub.
Qed.

Lemma protected_result_relation : forall observer (l : label) T v1 v2,
  wf_ty T -> value v1 -> value v2 ->
  underlying_typed (ty_protect l T) v1 ->
  underlying_typed (ty_protect l T) v2 ->
  (flows_to l observer -> value_relation observer T v1 v2) ->
  value_relation observer (ty_protect l T) v1 v2.
Proof.
  intros observer k T v1 v2 Hwf Hv1 Hv2 Ht1 Ht2 Hbase.
  destruct T; simpl in *.
  all: split; [exact Hv1|].
  all: split; [exact Hv2|].
  all: split; [exact Ht1|].
  all: split; [exact Ht2|].
  all: intros Hflow;
    pose proof (Hbase (flows_to_join_right _ _ _ Hflow)) as Hsrc;
    destruct Hsrc as [_ [_ [_ [_ Hshape]]]];
    apply Hshape; eapply flows_to_join_left; exact Hflow.
Qed.

Lemma arrow_protect_apps : forall observer A B f1 f2 l1 l2,
  value f1 -> value f2 ->
  (forall a1 a2, value_relation observer A a1 a2 ->
    expression_lifting (value_relation observer B)
      (tm_app f1 a1 High) (tm_app f2 a2 High)) ->
  (forall w1 w2, value_relation observer B w1 w2 ->
    value_relation observer B (protect_value w1 l1) (protect_value w2 l2)) ->
  forall a1 a2, value_relation observer A a1 a2 ->
    expression_lifting (value_relation observer B)
      (tm_app (protect_value f1 l1) a1 High)
      (tm_app (protect_value f2 l2) a2 High).
Proof.
  intros observer A B f1 f2 l1 l2 Hf1 Hf2 Hfun Hprotect a1 a2 Hargs.
  unfold expression_lifting. intros r1 r2 He1 He2.
  destruct (value_relation_properties _ _ _ _ Hargs) as [Ha1 [Ha2 _]].
  destruct (evaluates_protected_function f1 a1 l1 r1 Hf1 Ha1 He1) as [w1 [Hw1 ->]].
  destruct (evaluates_protected_function f2 a2 l2 r2 Hf2 Ha2 He2) as [w2 [Hw2 ->]].
  apply Hprotect. eapply Hfun; eauto.
Qed.

Lemma related_values_protect_pair : forall observer T v1 v2 l1 l2,
  value_relation observer T v1 v2 ->
  value_relation observer T (protect_value v1 l1) (protect_value v2 l2).
Proof.
  intros observer T. induction T; intros v1 v2 l1 l2 Hrel; simpl in *.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    split; [apply value_protect; exact Hv1|]. split; [apply value_protect; exact Hv2|].
    split; [unfold underlying_typed in *; rewrite erase_protect_value; exact Ht1|].
    split; [unfold underlying_typed in *; rewrite erase_protect_value; exact Ht2|].
    intros Hflow. pose proof (Hshape Hflow) as Hunit; destruct Hunit as [k1 [k2 [E1 E2]]]; subst v1; subst v2.
    simpl. exists (protect_security k1 l1),(protect_security k2 l2). auto.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    split; [apply value_protect; exact Hv1|]. split; [apply value_protect; exact Hv2|].
    split; [unfold underlying_typed in *; rewrite erase_protect_value; exact Ht1|].
    split; [unfold underlying_typed in *; rewrite erase_protect_value; exact Ht2|].
    intros Hflow. destruct (Hshape Hflow) as [Hl|Hr].
    + left. destruct Hl as [u1 [u2 [k1 [k2 [-> [-> Hx]]]]]].
      exists u1,u2,(protect_security k1 l1),(protect_security k2 l2).
      repeat split; try reflexivity; exact Hx.
    + right. destruct Hr as [u1 [u2 [k1 [k2 [-> [-> Hx]]]]]].
      exists u1,u2,(protect_security k1 l1),(protect_security k2 l2).
      repeat split; try reflexivity; exact Hx.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    split; [apply value_protect; exact Hv1|]. split; [apply value_protect; exact Hv2|].
    split; [unfold underlying_typed in *; rewrite erase_protect_value; exact Ht1|].
    split; [unfold underlying_typed in *; rewrite erase_protect_value; exact Ht2|].
    intros Hflow. destruct (Hshape Hflow)
      as [a1 [b1 [a2 [b2 [k1 [k2 [-> [-> [Ha Hb]]]]]]]]].
    exists a1,b1,a2,b2,(protect_security k1 l1),(protect_security k2 l2).
    repeat split; try reflexivity; assumption.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    split; [apply value_protect; exact Hv1|]. split; [apply value_protect; exact Hv2|].
    split; [unfold underlying_typed in *; rewrite erase_protect_value; exact Ht1|].
    split; [unfold underlying_typed in *; rewrite erase_protect_value; exact Ht2|].
    intros Hflow. destruct (Hshape Hflow)
      as [A1 [A2 [b1 [b2 [k1 [k2 [-> [-> Hfun]]]]]]]].
    exists A1,A2,b1,b2,(protect_security k1 l1),(protect_security k2 l2).
    split; [simpl; reflexivity|]. split; [simpl; reflexivity|].
    intros a1 a2 Hargs.
    eapply arrow_protect_apps.
    + exact Hv1.
    + exact Hv2.
    + exact Hfun.
    + intros w1 w2 Hout. exact (IHT2 w1 w2 l1 l2 Hout).
    + exact Hargs.
Qed.

Lemma related_opened_body : forall Gamma L body Targ Tresult observer rho1 rho2 v1 v2 w1 w2,
  (forall x, ~ In x L -> has_type (update Gamma x Targ)
    (open body (tm_fvar x)) Tresult) ->
  (forall x, ~ In x L -> forall rho1' rho2',
    related_expression_substitutions observer (update Gamma x Targ) rho1' rho2' ->
    expression_relation observer Tresult
      (instantiate rho1' (open body (tm_fvar x)))
      (instantiate rho2' (open body (tm_fvar x)))) ->
  related_expression_substitutions observer Gamma rho1 rho2 ->
  value_relation observer Targ v1 v2 ->
  big_step (open (instantiate rho1 body) v1) w1 ->
  big_step (open (instantiate rho2 body) v2) w2 ->
  value_relation observer Tresult w1 w2.
Proof.
  intros Gamma L body Targ Tresult observer rho1 rho2 v1 v2 w1 w2
    Htyping Hfund Henv Hargs Hstep1 Hstep2.
  destruct (fresh_atom (L ++ fv body)) as [x Hx].
  rewrite in_app_iff in Hx.
  assert (HxL : ~ In x L) by (intro Hin; apply Hx; left; exact Hin).
  assert (Hxbody : ~ In x (fv body)) by (intro Hin; apply Hx; right; exact Hin).
  pose proof (related_expression_update observer Gamma rho1 rho2 x Targ v1 v2 Henv Hargs)
    as Henvarg.
  pose proof (Htyping x HxL) as HbodyTyping.
  pose proof (Hfund x HxL (substitution_update rho1 x v1)
    (substitution_update rho2 x v2) Henvarg) as HbodyRel.
  destruct HbodyRel as [Hbu1 [Hbu2 Hblift]].
  unfold expression_lifting in Hblift.
  assert (Hlcarg1 : forall y, In y (fv body) ->
    locally_closed (substitution_update rho1 x v1 y)).
  { intros y Hy. assert (Hyopen : In y (fv (open body (tm_fvar x))))
      by (eapply fv_open_includes; exact Hy).
    destruct (related_substitution_lc (update Gamma x Targ)
      (open body (tm_fvar x)) Tresult observer
      (substitution_update rho1 x v1) (substitution_update rho2 x v2)
      HbodyTyping Henvarg y Hyopen) as [Hlc _]. exact Hlc. }
  assert (Hlcarg2 : forall y, In y (fv body) ->
    locally_closed (substitution_update rho2 x v2 y)).
  { intros y Hy. assert (Hyopen : In y (fv (open body (tm_fvar x))))
      by (eapply fv_open_includes; exact Hy).
    destruct (related_substitution_lc (update Gamma x Targ)
      (open body (tm_fvar x)) Tresult observer
      (substitution_update rho1 x v1) (substitution_update rho2 x v2)
      HbodyTyping Henvarg y Hyopen) as [_ Hlc]. exact Hlc. }
  assert (Hrho1 : forall y, In y (fv body) -> locally_closed (rho1 y)).
  { intros y Hy. specialize (Hlcarg1 y Hy). unfold substitution_update in Hlcarg1.
    destruct (Nat.eqb x y) eqn:E; [apply Nat.eqb_eq in E; subst; contradiction|exact Hlcarg1]. }
  assert (Hrho2 : forall y, In y (fv body) -> locally_closed (rho2 y)).
  { intros y Hy. specialize (Hlcarg2 y Hy). unfold substitution_update in Hlcarg2.
    destruct (Nat.eqb x y) eqn:E; [apply Nat.eqb_eq in E; subst; contradiction|exact Hlcarg2]. }
  pose proof (instantiate_open_update body rho1 x v1 Hxbody Hrho1) as Eopen1.
  pose proof (instantiate_open_update body rho2 x v2 Hxbody Hrho2) as Eopen2.
  apply Hblift.
  - rewrite Eopen1. apply big_step_sound. exact Hstep1.
  - rewrite Eopen2. apply big_step_sound. exact Hstep2.
Qed.

Theorem fundamental_package : forall Gamma t T, has_type Gamma t T ->
  has_type Gamma t T /\
  (forall observer rho1 rho2,
    related_expression_substitutions observer Gamma rho1 rho2 ->
    expression_relation observer T (instantiate rho1 t) (instantiate rho2 t)).
Proof.
  intros Gamma t T Htyped. induction Htyped as
    [Gamma x T Hlookup Hwf
    | Gamma kappa Hwf
    | L Gamma T1 body T2 kappa HwfT HwfK Hbody IHbody
    | Gamma t1 t2 T1 T2 kappa r Hfun IHfun Harg IHarg Hflow
    | Gamma t1 t2 T1 T2 kappa Hleft IHleft Hright IHright HwfK
    | Gamma t T1 T2 kappa r Hprod IHprod Hflow
    | Gamma t T1 T2 kappa r Hprod IHprod Hflow
    | Gamma t T1 T2 kappa Hterm IHterm HwfT2 HwfK
    | Gamma t T1 T2 kappa HwfT1 Hterm IHterm HwfK
    | L Gamma t body1 body2 T1 T2 T kappa r Hscr IHscr Hflow Hb1 IHb1 Hb2 IHb2
    | Gamma t T l Hterm IHterm
    | Gamma t T U Hterm IHterm Hsub].
  - split; [constructor; assumption|]. intros observer rho1 rho2 Henv. exact (Henv x T Hlookup).
  - split; [constructor; assumption|]. intros observer rho1 rho2 Henv.
    pose proof (related_instantiations_typed Gamma (tm_unit kappa) (Ty_Unit kappa)
      observer rho1 rho2 (T_Unit Gamma kappa Hwf) Henv) as [Hu1 Hu2].
    split; [exact Hu1|]. split; [exact Hu2|].
    intros v1 v2 He1 He2.
    pose proof (value_multi_inv (tm_unit kappa) v1 (v_unit kappa) (proj1 He1)) as ->.
    pose proof (value_multi_inv (tm_unit kappa) v2 (v_unit kappa) (proj1 He2)) as ->.
    split; [constructor|]. split; [constructor|]. split; [exact Hu1|]. split; [exact Hu2|].
    intros Hobs. exists kappa,kappa. auto.
  - split; [exact (T_Abs L Gamma T1 body T2 kappa HwfT HwfK Hbody)|].
    intros observer rho1 rho2 Henv.
    pose proof (related_instantiations_typed Gamma (tm_abs T1 body kappa)
      (Ty_Arrow T1 T2 kappa) observer rho1 rho2
      (T_Abs L Gamma T1 body T2 kappa HwfT HwfK Hbody) Henv) as [Hu1 Hu2].
    split; [exact Hu1|]. split; [exact Hu2|].
    intros v1 v2 He1 He2.
    assert (Hlc1 : locally_closed (tm_abs T1 (instantiate rho1 body) kappa)).
    { apply erase_lc_inv. exact (proj1 (typing_regular _ _ _ Hu1)). }
    assert (Hlc2 : locally_closed (tm_abs T1 (instantiate rho2 body) kappa)).
    { apply erase_lc_inv. exact (proj1 (typing_regular _ _ _ Hu2)). }
    assert (Hval1 : value (tm_abs T1 (instantiate rho1 body) kappa)) by
      (constructor; exact Hlc1).
    assert (Hval2 : value (tm_abs T1 (instantiate rho2 body) kappa)) by
      (constructor; exact Hlc2).
    pose proof (value_multi_inv _ _ Hval1 (proj1 He1)) as E1. subst v1.
    pose proof (value_multi_inv _ _ Hval2 (proj1 He2)) as E2. subst v2.
    split; [exact Hval1|]. split; [exact Hval2|]. split; [exact Hu1|]. split; [exact Hu2|].
    intros Hflow.
    exists T1,T1,(instantiate rho1 body),(instantiate rho2 body),kappa,kappa.
    split; [reflexivity|]. split; [reflexivity|].
    intros arg1 arg2 Hargs.
    destruct (fresh_atom (L ++ fv body)) as [x Hx].
    rewrite in_app_iff in Hx.
    assert (HxL : ~ In x L) by (intro Hin; apply Hx; left; exact Hin).
    assert (Hxbody : ~ In x (fv body)) by (intro Hin; apply Hx; right; exact Hin).
    pose proof (related_expression_update observer Gamma rho1 rho2 x T1 arg1 arg2 Henv Hargs)
      as Henvarg.
    destruct (IHbody x HxL) as [HbodyTyping HbodyFund].
    pose proof (HbodyFund observer (substitution_update rho1 x arg1)
      (substitution_update rho2 x arg2) Henvarg) as HbodyRel.
    assert (Hlcarg1 : forall y, In y (fv body) ->
      locally_closed (substitution_update rho1 x arg1 y)).
    { intros y Hy. assert (Hyopen : In y (fv (open body (tm_fvar x))))
        by (eapply fv_open_includes; exact Hy).
      destruct (related_substitution_lc (update Gamma x T1)
        (open body (tm_fvar x)) T2 observer
        (substitution_update rho1 x arg1) (substitution_update rho2 x arg2)
        HbodyTyping Henvarg y Hyopen) as [Hlc _]. exact Hlc. }
    assert (Hlcarg2 : forall y, In y (fv body) ->
      locally_closed (substitution_update rho2 x arg2 y)).
    { intros y Hy. assert (Hyopen : In y (fv (open body (tm_fvar x))))
        by (eapply fv_open_includes; exact Hy).
      destruct (related_substitution_lc (update Gamma x T1)
        (open body (tm_fvar x)) T2 observer
        (substitution_update rho1 x arg1) (substitution_update rho2 x arg2)
        HbodyTyping Henvarg y Hyopen) as [_ Hlc]. exact Hlc. }
    assert (Hrho1 : forall y, In y (fv body) -> locally_closed (rho1 y)).
    { intros y Hy. specialize (Hlcarg1 y Hy). unfold substitution_update in Hlcarg1.
      destruct (Nat.eqb x y) eqn:E; [apply Nat.eqb_eq in E; subst; contradiction|exact Hlcarg1]. }
    assert (Hrho2 : forall y, In y (fv body) -> locally_closed (rho2 y)).
    { intros y Hy. specialize (Hlcarg2 y Hy). unfold substitution_update in Hlcarg2.
      destruct (Nat.eqb x y) eqn:E; [apply Nat.eqb_eq in E; subst; contradiction|exact Hlcarg2]. }
    pose proof (instantiate_open_update body rho1 x arg1 Hxbody Hrho1) as Eopen1.
    pose proof (instantiate_open_update body rho2 x arg2 Hxbody Hrho2) as Eopen2.
    destruct HbodyRel as [_ [_ Hbodylift]].
    unfold expression_lifting. intros result1 result2 Heval1 Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst; inversion Heval2; subst.
    pose proof (big_step_value_inv _ _ Hval1 H2) as Efun1. inversion Efun1; subst.
    pose proof (big_step_value_inv _ _ Hval2 H4) as Efun2. inversion Efun2; subst.
    pose proof (value_relation_properties _ _ _ _ Hargs) as [Ha1 [Ha2 _]].
    pose proof (big_step_value_inv _ _ Ha1 H3) as Earg1. subst v.
    pose proof (big_step_value_inv _ _ Ha2 H7) as Earg2. subst v0.
    unfold expression_lifting in Hbodylift.
    match goal with
    | |- value_relation observer T2
          (protect_value ?w1 ?l1)
          (protect_value ?w2 ?l2) =>
        assert (Hbase : value_relation observer T2 w1 w2) by
          (apply (Hbodylift w1 w2);
           [rewrite Eopen1; apply big_step_sound; exact H6 |
            rewrite Eopen2; apply big_step_sound; exact H10]);
        exact (related_values_protect_pair observer T2 w1 w2 l1 l2 Hbase)
    end.
  - assert (Hcurrent : has_type Gamma (tm_app t1 t2 r)
      (ty_protect kappa.(indirect_reader) T2)) by (eapply T_App; eauto).
    split; [exact Hcurrent|]. intros observer rho1 rho2 Henv.
    pose proof (related_instantiations_typed Gamma (tm_app t1 t2 r)
      (ty_protect kappa.(indirect_reader) T2) observer rho1 rho2 Hcurrent Henv)
      as [Hu1 Hu2].
    split; [exact Hu1|]. split; [exact Hu2|].
    destruct IHfun as [Htf Hfundf]. destruct IHarg as [Hta Hfunda].
    destruct (Hfundf observer rho1 rho2 Henv) as [_ [_ Hliftf]].
    destruct (Hfunda observer rho1 rho2 Henv) as [_ [_ Hliftarg]].
    unfold expression_lifting in Hliftf, Hliftarg.
    intros result1 result2 Heval1 Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst; inversion Heval2; subst.
    assert (Hfunrel : value_relation observer (Ty_Arrow T1 T2 kappa)
      (tm_abs A body k) (tm_abs A0 body0 k0)).
    { apply Hliftf; [apply big_step_sound; exact H2|apply big_step_sound; exact H4]. }
    assert (Hargrel : value_relation observer T1 v v0).
    { apply Hliftarg; [apply big_step_sound; exact H3|apply big_step_sound; exact H7]. }
    destruct Hfunrel as [Hfv1 [Hfv2 [Hfu1 [Hfu2 Hfshape]]]].
    assert (HwfT2 : wf_ty T2) by
      (pose proof (proj2 (typing_regular _ _ _ Hfun)) as Hw; simpl in Hw; tauto).
    assert (Hresv1 : value (protect_value w (indirect_reader k))) by
      (eapply big_step_result_value; exact Heval1).
    assert (Hresv2 : value (protect_value w0 (indirect_reader k0))) by
      (eapply big_step_result_value; exact Heval2).
    assert (Hrest1 : underlying_typed (ty_protect kappa.(indirect_reader) T2)
      (protect_value w (indirect_reader k))).
    { eapply underlying_typed_evaluates; [exact Hu1|apply big_step_sound; exact Heval1]. }
    assert (Hrest2 : underlying_typed (ty_protect kappa.(indirect_reader) T2)
      (protect_value w0 (indirect_reader k0))).
    { eapply underlying_typed_evaluates; [exact Hu2|apply big_step_sound; exact Heval2]. }
    eapply (protected_result_relation observer kappa.(indirect_reader) T2
      (protect_value w (indirect_reader k)) (protect_value w0 (indirect_reader k0)));
      try eassumption.
    intros Hkobs.
    destruct (Hfshape Hkobs) as [U1 [U2 [fb1 [fb2 [kf1 [kf2 [Efun1 [Efun2 Happly]]]]]]]].
    inversion Efun1; inversion Efun2; subst.
    specialize (Happly v v0 Hargrel). unfold expression_lifting in Happly.
    pose proof (value_relation_properties _ _ _ _ Hargrel) as [Hva1 [Hva2 _]].
    assert (Hhi1 : evaluates (tm_app (tm_abs U1 fb1 kf1) v High)
      (protect_value w (indirect_reader kf1))).
    { apply big_step_iff_evaluates. eapply B_App.
      - apply B_Abs. inversion Hfv1; subst; assumption.
      - apply big_step_value_refl. exact Hva1.
      - destruct (reader kf1); exact I.
      - exact H6. }
    assert (Hhi2 : evaluates (tm_app (tm_abs U2 fb2 kf2) v0 High)
      (protect_value w0 (indirect_reader kf2))).
    { apply big_step_iff_evaluates. eapply B_App.
      - apply B_Abs. inversion Hfv2; subst; assumption.
      - apply big_step_value_refl. exact Hva2.
      - destruct (reader kf2); exact I.
      - exact H10. }
    eapply Happly; eassumption.
  - assert (Hcurrent : has_type Gamma (tm_pair t1 t2 kappa)
      (Ty_Prod T1 T2 kappa)) by (eapply T_Pair; eauto).
    split; [exact Hcurrent|]. intros observer rho1 rho2 Henv.
    pose proof (related_instantiations_typed Gamma (tm_pair t1 t2 kappa)
      (Ty_Prod T1 T2 kappa) observer rho1 rho2 Hcurrent Henv) as [Hu1 Hu2].
    destruct IHleft as [Ht1 Hfund1]. destruct IHright as [Ht2 Hfund2].
    destruct (Hfund1 observer rho1 rho2 Henv) as [_ [_ Hl1]].
    destruct (Hfund2 observer rho1 rho2 Henv) as [_ [_ Hl2]].
    unfold expression_lifting in Hl1, Hl2.
    split; [exact Hu1|]. split; [exact Hu2|].
    unfold expression_lifting. intros result1 result2 Heval1 Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst; inversion Heval2; subst.
    split; [eauto using big_step_result_value|].
    split; [eauto using big_step_result_value|].
    split; [eapply underlying_typed_evaluates; [exact Hu1|apply big_step_sound; exact Heval1]|].
    split; [eapply underlying_typed_evaluates; [exact Hu2|apply big_step_sound; exact Heval2]|].
    intros Hflow. exists v, w, v0, w0, kappa, kappa.
    repeat split; try reflexivity.
    + apply Hl1; apply big_step_sound; assumption.
    + apply Hl2; apply big_step_sound; assumption.
  - assert (Hcurrent : has_type Gamma (tm_fst t r)
      (ty_protect kappa.(indirect_reader) T1)) by (eapply T_Fst; eauto).
    split; [exact Hcurrent|]. intros observer rho1 rho2 Henv.
    pose proof (related_instantiations_typed Gamma (tm_fst t r)
      (ty_protect kappa.(indirect_reader) T1) observer rho1 rho2 Hcurrent Henv)
      as [Hu1 Hu2].
    destruct IHprod as [Htp Hfund].
    destruct (Hfund observer rho1 rho2 Henv) as [_ [_ Hlift]].
    unfold expression_lifting in Hlift.
    split; [exact Hu1|]. split; [exact Hu2|]. unfold expression_lifting.
    intros result1 result2 Heval1 Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst; inversion Heval2; subst.
    pose proof (Hlift (tm_pair a b k) (tm_pair a0 b0 k0)
      (big_step_sound _ _ H1) (big_step_sound _ _ H2)) as Hpairrel.
    assert (HwfT1 : wf_ty T1) by
      (pose proof (proj2 (typing_regular _ _ _ Hprod)) as Hw; simpl in Hw; tauto).
    eapply (protected_result_relation observer kappa.(indirect_reader) T1
      (protect_value a (indirect_reader k))
      (protect_value a0 (indirect_reader k0))).
    + exact HwfT1.
    + eapply big_step_result_value; exact Heval1.
    + eapply big_step_result_value; exact Heval2.
    + eapply underlying_typed_evaluates; [exact Hu1|apply big_step_sound; exact Heval1].
    + eapply underlying_typed_evaluates; [exact Hu2|apply big_step_sound; exact Heval2].
    + intros Hobs. destruct Hpairrel as [_ [_ [_ [_ Hshape]]]].
      destruct (Hshape Hobs) as [x1 [y1 [x2 [y2 [q1 [q2 [E1 [E2 [Hrelx _]]]]]]]]].
      inversion E1; inversion E2; subst.
      eapply related_values_protect_pair; exact Hrelx.
  - assert (Hcurrent : has_type Gamma (tm_snd t r)
      (ty_protect kappa.(indirect_reader) T2)) by (eapply T_Snd; eauto).
    split; [exact Hcurrent|]. intros observer rho1 rho2 Henv.
    pose proof (related_instantiations_typed Gamma (tm_snd t r)
      (ty_protect kappa.(indirect_reader) T2) observer rho1 rho2 Hcurrent Henv)
      as [Hu1 Hu2].
    destruct IHprod as [Htp Hfund].
    destruct (Hfund observer rho1 rho2 Henv) as [_ [_ Hlift]].
    unfold expression_lifting in Hlift.
    split; [exact Hu1|]. split; [exact Hu2|]. unfold expression_lifting.
    intros result1 result2 Heval1 Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst; inversion Heval2; subst.
    pose proof (Hlift (tm_pair a b k) (tm_pair a0 b0 k0)
      (big_step_sound _ _ H1) (big_step_sound _ _ H2)) as Hpairrel.
    assert (HwfT2 : wf_ty T2) by
      (pose proof (proj2 (typing_regular _ _ _ Hprod)) as Hw; simpl in Hw; tauto).
    eapply (protected_result_relation observer kappa.(indirect_reader) T2
      (protect_value b (indirect_reader k))
      (protect_value b0 (indirect_reader k0))).
    + exact HwfT2.
    + eapply big_step_result_value; exact Heval1.
    + eapply big_step_result_value; exact Heval2.
    + eapply underlying_typed_evaluates; [exact Hu1|apply big_step_sound; exact Heval1].
    + eapply underlying_typed_evaluates; [exact Hu2|apply big_step_sound; exact Heval2].
    + intros Hobs. destruct Hpairrel as [_ [_ [_ [_ Hshape]]]].
      destruct (Hshape Hobs) as [x1 [y1 [x2 [y2 [q1 [q2 [E1 [E2 [_ Hrely]]]]]]]]].
      inversion E1; inversion E2; subst. eapply related_values_protect_pair; exact Hrely.
  - assert (Hcurrent : has_type Gamma (tm_inl t kappa)
      (Ty_Sum T1 T2 kappa)) by (eapply T_Inl; eauto).
    split; [exact Hcurrent|]. intros observer rho1 rho2 Henv.
    pose proof (related_instantiations_typed Gamma (tm_inl t kappa)
      (Ty_Sum T1 T2 kappa) observer rho1 rho2 Hcurrent Henv) as [Hu1 Hu2].
    destruct IHterm as [Htt Hfund].
    destruct (Hfund observer rho1 rho2 Henv) as [_ [_ Hlift]].
    unfold expression_lifting in Hlift.
    split; [exact Hu1|]. split; [exact Hu2|]. unfold expression_lifting.
    intros result1 result2 Heval1 Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst; inversion Heval2; subst.
    split; [eapply big_step_result_value; exact Heval1|].
    split; [eapply big_step_result_value; exact Heval2|].
    split. { eapply underlying_typed_evaluates; [exact Hu1|apply big_step_sound; exact Heval1]. }
    split. { eapply underlying_typed_evaluates; [exact Hu2|apply big_step_sound; exact Heval2]. }
    intros Hflow. left. exists v, v0, kappa, kappa. repeat split; try reflexivity.
    apply Hlift; apply big_step_sound; assumption.
  - assert (Hcurrent : has_type Gamma (tm_inr t kappa)
      (Ty_Sum T1 T2 kappa)) by (eapply T_Inr; eauto).
    split; [exact Hcurrent|]. intros observer rho1 rho2 Henv.
    pose proof (related_instantiations_typed Gamma (tm_inr t kappa)
      (Ty_Sum T1 T2 kappa) observer rho1 rho2 Hcurrent Henv) as [Hu1 Hu2].
    destruct IHterm as [Htt Hfund].
    destruct (Hfund observer rho1 rho2 Henv) as [_ [_ Hlift]].
    unfold expression_lifting in Hlift.
    split; [exact Hu1|]. split; [exact Hu2|]. unfold expression_lifting.
    intros result1 result2 Heval1 Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst; inversion Heval2; subst.
    split; [eapply big_step_result_value; exact Heval1|].
    split; [eapply big_step_result_value; exact Heval2|].
    split. { eapply underlying_typed_evaluates; [exact Hu1|apply big_step_sound; exact Heval1]. }
    split. { eapply underlying_typed_evaluates; [exact Hu2|apply big_step_sound; exact Heval2]. }
    intros Hflow. right. exists v, v0, kappa, kappa. repeat split; try reflexivity.
    apply Hlift; apply big_step_sound; assumption.
  - assert (Hcurrent : has_type Gamma (tm_case t body1 body2 r)
      (ty_protect kappa.(indirect_reader) T)) by (eapply T_Case; eauto).
    split; [exact Hcurrent|]. intros observer rho1 rho2 Henv.
    pose proof (related_instantiations_typed Gamma (tm_case t body1 body2 r)
      (ty_protect kappa.(indirect_reader) T) observer rho1 rho2 Hcurrent Henv)
      as [Hu1 Hu2].
    destruct IHscr as [Hts Hfund].
    destruct (Hfund observer rho1 rho2 Henv) as [_ [_ Hlift]].
    unfold expression_lifting in Hlift.
    split; [exact Hu1|]. split; [exact Hu2|]. unfold expression_lifting.
    assert (HwfT : wf_ty T).
    { destruct (fresh_atom L) as [x Hfresh].
      assert (Hx : ~ In x L) by (intro Hin; apply Hfresh; exact Hin).
      pose proof (Hb1 x Hx) as Hbx.
      exact (proj2 (typing_regular _ _ _ Hbx)). }
    intros result1 result2 Heval1 Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst; inversion Heval2; subst.
    pose proof (Hlift (tm_inl v k) (tm_inl v0 k0)
      (big_step_sound _ _ H4) (big_step_sound _ _ H7)) as Hscrrel.
    eapply (protected_result_relation observer kappa.(indirect_reader) T
      (protect_value w (indirect_reader k))
      (protect_value w0 (indirect_reader k0))).
    + exact HwfT.
    + eapply big_step_result_value; exact Heval1.
    + eapply big_step_result_value; exact Heval2.
    + eapply underlying_typed_evaluates; [exact Hu1|apply big_step_sound; exact Heval1].
    + eapply underlying_typed_evaluates; [exact Hu2|apply big_step_sound; exact Heval2].
    + intros Hobs. destruct Hscrrel as [_ [_ [_ [_ Hshape]]]].
      destruct (Hshape Hobs) as [Hleft|Hright].
      * destruct Hleft as [x1 [x2 [q1 [q2 [E1 [E2 Hpayload]]]]]].
        inversion E1; inversion E2; subst.
        assert (Hfundleft : forall x, ~ In x L -> forall s1 s2,
          related_expression_substitutions observer (update Gamma x T1) s1 s2 ->
          expression_relation observer T
            (instantiate s1 (open body1 (tm_fvar x)))
            (instantiate s2 (open body1 (tm_fvar x)))).
        { intros x Hx s1 s2 He. destruct (IHb1 x Hx) as [_ Hf]. eapply Hf; exact He. }
        pose proof (related_opened_body Gamma L body1 T1 T observer rho1 rho2
          x1 x2 w w0 Hb1 Hfundleft Henv Hpayload H6 H9) as Hbodyrel.
        eapply related_values_protect_pair; exact Hbodyrel.
      * destruct Hright as [x1 [x2 [q1 [q2 [E1 [E2 _]]]]]]. discriminate E1.
  + pose proof (Hlift (tm_inl v k) (tm_inr v0 k0)
      (big_step_sound _ _ H4) (big_step_sound _ _ H7)) as Hscrrel.
    eapply (protected_result_relation observer kappa.(indirect_reader) T
      (protect_value w (indirect_reader k))
      (protect_value w0 (indirect_reader k0))).
    * exact HwfT.
    * eapply big_step_result_value; exact Heval1.
    * eapply big_step_result_value; exact Heval2.
    * eapply underlying_typed_evaluates; [exact Hu1|apply big_step_sound; exact Heval1].
    * eapply underlying_typed_evaluates; [exact Hu2|apply big_step_sound; exact Heval2].
    * intros Hobs. destruct Hscrrel as [_ [_ [_ [_ Hshape]]]].
      destruct (Hshape Hobs) as [Hleft|Hright].
      -- destruct Hleft as [x1 [x2 [q1 [q2 [E1 [E2 _]]]]]]. discriminate E2.
      -- destruct Hright as [x1 [x2 [q1 [q2 [E1 [E2 _]]]]]]. discriminate E1.
  + pose proof (Hlift (tm_inr v k) (tm_inl v0 k0)
      (big_step_sound _ _ H4) (big_step_sound _ _ H7)) as Hscrrel.
    eapply (protected_result_relation observer kappa.(indirect_reader) T
      (protect_value w (indirect_reader k))
      (protect_value w0 (indirect_reader k0))).
    * exact HwfT.
    * eapply big_step_result_value; exact Heval1.
    * eapply big_step_result_value; exact Heval2.
    * eapply underlying_typed_evaluates; [exact Hu1|apply big_step_sound; exact Heval1].
    * eapply underlying_typed_evaluates; [exact Hu2|apply big_step_sound; exact Heval2].
    * intros Hobs. destruct Hscrrel as [_ [_ [_ [_ Hshape]]]].
      destruct (Hshape Hobs) as [Hleft|Hright].
      -- destruct Hleft as [x1 [x2 [q1 [q2 [E1 [E2 _]]]]]]. discriminate E1.
      -- destruct Hright as [x1 [x2 [q1 [q2 [E1 [E2 _]]]]]]. discriminate E2.
  + pose proof (Hlift (tm_inr v k) (tm_inr v0 k0)
      (big_step_sound _ _ H4) (big_step_sound _ _ H7)) as Hscrrel.
    eapply (protected_result_relation observer kappa.(indirect_reader) T
      (protect_value w (indirect_reader k))
      (protect_value w0 (indirect_reader k0))).
    * exact HwfT.
    * eapply big_step_result_value; exact Heval1.
    * eapply big_step_result_value; exact Heval2.
    * eapply underlying_typed_evaluates; [exact Hu1|apply big_step_sound; exact Heval1].
    * eapply underlying_typed_evaluates; [exact Hu2|apply big_step_sound; exact Heval2].
    * intros Hobs. destruct Hscrrel as [_ [_ [_ [_ Hshape]]]].
      destruct (Hshape Hobs) as [Hleft|Hright].
      -- destruct Hleft as [x1 [x2 [q1 [q2 [E1 [E2 _]]]]]]. discriminate E1.
      -- destruct Hright as [x1 [x2 [q1 [q2 [E1 [E2 Hpayload]]]]]].
         inversion E1; inversion E2; subst.
         assert (Hfundright : forall x, ~ In x L -> forall s1 s2,
           related_expression_substitutions observer (update Gamma x T2) s1 s2 ->
           expression_relation observer T
             (instantiate s1 (open body2 (tm_fvar x)))
             (instantiate s2 (open body2 (tm_fvar x)))).
         { intros x Hx s1 s2 He. destruct (IHb2 x Hx) as [_ Hf]. eapply Hf; exact He. }
         pose proof (related_opened_body Gamma L body2 T2 T observer rho1 rho2
           x1 x2 w w0 Hb2 Hfundright Henv Hpayload H6 H9) as Hbodyrel.
         eapply related_values_protect_pair; exact Hbodyrel.
  - assert (Hcurrent : has_type Gamma (tm_protect l t) (ty_protect l T))
      by (eapply T_Protect; exact Hterm).
    split; [exact Hcurrent|]. intros observer rho1 rho2 Henv.
    pose proof (related_instantiations_typed Gamma (tm_protect l t)
      (ty_protect l T) observer rho1 rho2 Hcurrent Henv) as [Hu1 Hu2].
    destruct IHterm as [Htt Hfund].
    destruct (Hfund observer rho1 rho2 Henv) as [_ [_ Hlift]].
    unfold expression_lifting in Hlift.
    split; [exact Hu1|]. split; [exact Hu2|]. unfold expression_lifting.
    intros result1 result2 Heval1 Heval2.
    apply big_step_iff_evaluates in Heval1. apply big_step_iff_evaluates in Heval2.
    inversion Heval1; subst; inversion Heval2; subst.
    pose proof (Hlift v v0 (big_step_sound _ _ H2) (big_step_sound _ _ H3)) as Hrel.
    assert (HwfT : wf_ty T) by
      (pose proof (proj2 (typing_regular _ _ _ Hterm)) as Hw; exact Hw).
    eapply (protected_result_relation observer l T
      (protect_value v l) (protect_value v0 l)).
    + exact HwfT.
    + eapply big_step_result_value; exact Heval1.
    + eapply big_step_result_value; exact Heval2.
    + eapply underlying_typed_evaluates; [exact Hu1|apply big_step_sound; exact Heval1].
    + eapply underlying_typed_evaluates; [exact Hu2|apply big_step_sound; exact Heval2].
    + intros _. eapply related_values_protect_pair; exact Hrel.
  - assert (Hcurrent : has_type Gamma t U) by (eapply T_Sub; eauto).
    split; [exact Hcurrent|]. intros observer rho1 rho2 Henv.
    pose proof (related_instantiations_typed Gamma t U observer rho1 rho2 Hcurrent Henv)
      as [Hu1 Hu2].
    destruct IHterm as [Htt Hfund].
    split; [exact Hu1|]. split; [exact Hu2|].
    destruct (Hfund observer rho1 rho2 Henv) as [_ [_ Hlift]].
    unfold expression_lifting in Hlift. unfold expression_lifting.
    intros result1 result2 Heval1 Heval2.
    eapply related_values_subtype; [exact Hsub|].
    apply Hlift; assumption.
Qed.

Theorem fundamental_expressions : forall Gamma t T,
  has_type Gamma t T -> forall observer rho1 rho2,
    related_expression_substitutions observer Gamma rho1 rho2 ->
    expression_relation observer T (instantiate rho1 t) (instantiate rho2 t).
Proof.
  intros Gamma t T H. destruct (fundamental_package _ _ _ H) as [_ Hfund].
  eauto.
Qed.

Fixpoint context_support (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ | C_Fst C' _ | C_Snd C' _
  | C_Inl C' _ | C_Inr C' _ | C_Protect _ C' => context_support C'
  | C_AppLeft C' t _ | C_PairLeft C' t _ => context_support C' ++ fv t
  | C_AppRight t C' _ | C_PairRight t C' _ => fv t ++ context_support C'
  | C_CaseScrutinee C' b1 b2 _ => context_support C' ++ fv b1 ++ fv b2
  | C_CaseLeft t0 C' b2 _ => fv t0 ++ context_support C' ++ fv b2
  | C_CaseRight t0 b1 C' _ => fv t0 ++ fv b1 ++ context_support C'
  end.

Lemma instantiate_identity : forall t,
  instantiate (fun y => tm_fvar y) t = t.
Proof.
  induction t; simpl; try reflexivity; f_equal; assumption.
Qed.

Lemma fv_plug_supported : forall C hole y,
  In y (fv (plug C hole)) -> In y (context_support C) \/ In y (fv hole).
Proof.
  intros C hole y H. induction C; simpl in *; unfold context_support in *;
    simpl in *; repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma instantiate_plug_update : forall C x replacement rho,
  rho x = replacement ->
  (forall y, In y (context_support C) -> rho y = tm_fvar y) ->
  instantiate rho (plug C (tm_fvar x)) = plug C replacement.
Proof.
  intros C x replacement rho Hx Hsupport. induction C; simpl in *.
  - exact Hx.
  - f_equal. apply IHC. intros y Hy. apply Hsupport. exact Hy.
  - f_equal.
    + apply IHC. intros y Hy. apply Hsupport. apply in_or_app; left; exact Hy.
    + match goal with |- instantiate rho ?u = ?u => replace u with (instantiate (fun y => tm_fvar y) u) at 2 by (exact (instantiate_identity u)) end.
      apply instantiate_ext. intros y Hy. apply Hsupport. apply in_or_app; right; exact Hy.
  - f_equal.
    + match goal with |- instantiate rho ?u = ?u => replace u with (instantiate (fun y => tm_fvar y) u) at 2 by (exact (instantiate_identity u)) end.
      apply instantiate_ext. intros y Hy. apply Hsupport. apply in_or_app; left; exact Hy.
    + apply IHC. intros y Hy. apply Hsupport. apply in_or_app; right; exact Hy.
  - f_equal.
    + apply IHC. intros y Hy. apply Hsupport. apply in_or_app; left; exact Hy.
    + match goal with |- instantiate rho ?u = ?u => replace u with (instantiate (fun y => tm_fvar y) u) at 2 by (exact (instantiate_identity u)) end.
      apply instantiate_ext. intros y Hy. apply Hsupport. apply in_or_app; right; exact Hy.
  - f_equal.
    + match goal with |- instantiate rho ?u = ?u => replace u with (instantiate (fun y => tm_fvar y) u) at 2 by (exact (instantiate_identity u)) end.
      apply instantiate_ext. intros y Hy. apply Hsupport. apply in_or_app; left; exact Hy.
    + apply IHC. intros y Hy. apply Hsupport. apply in_or_app; right; exact Hy.
  - f_equal. apply IHC. intros y Hy. apply Hsupport. exact Hy.
  - f_equal. apply IHC. intros y Hy. apply Hsupport. exact Hy.
  - f_equal. apply IHC. intros y Hy. apply Hsupport. exact Hy.
  - f_equal. apply IHC. intros y Hy. apply Hsupport. exact Hy.
  - f_equal.
    + apply IHC. intros y Hy. apply Hsupport. apply in_or_app; left; exact Hy.
    + match goal with |- instantiate rho ?u = ?u => replace u with (instantiate (fun y => tm_fvar y) u) at 2 by (exact (instantiate_identity u)) end.
      apply instantiate_ext. intros y Hy. apply Hsupport. apply in_or_app; right. apply in_or_app; left; exact Hy.
    + match goal with |- instantiate rho ?u = ?u => replace u with (instantiate (fun y => tm_fvar y) u) at 2 by (exact (instantiate_identity u)) end.
      apply instantiate_ext. intros y Hy. apply Hsupport. apply in_or_app; right. apply in_or_app; right; exact Hy.
  - f_equal.
    + match goal with |- instantiate rho ?u = ?u => replace u with (instantiate (fun y => tm_fvar y) u) at 2 by (exact (instantiate_identity u)) end.
      apply instantiate_ext. intros y Hy. apply Hsupport. apply in_or_app; left; exact Hy.
    + apply IHC. intros y Hy. apply Hsupport. apply in_or_app; right. apply in_or_app; left; exact Hy.
    + match goal with |- instantiate rho ?u = ?u => replace u with (instantiate (fun y => tm_fvar y) u) at 2 by (exact (instantiate_identity u)) end.
      apply instantiate_ext. intros y Hy. apply Hsupport. apply in_or_app; right. apply in_or_app; right; exact Hy.
  - f_equal.
    + match goal with |- instantiate rho ?u = ?u => replace u with (instantiate (fun y => tm_fvar y) u) at 2 by (exact (instantiate_identity u)) end.
      apply instantiate_ext. intros y Hy. apply Hsupport. apply in_or_app; left; exact Hy.
    + match goal with |- instantiate rho ?u = ?u => replace u with (instantiate (fun y => tm_fvar y) u) at 2 by (exact (instantiate_identity u)) end.
      apply instantiate_ext. intros y Hy. apply Hsupport. apply in_or_app; right. apply in_or_app; left; exact Hy.
    + apply IHC. intros y Hy. apply Hsupport. apply in_or_app; right. apply in_or_app; right; exact Hy.
  - f_equal. apply IHC. intros y Hy. apply Hsupport. exact Hy.
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 Hcontext Hground Htransparent Hno.
  destruct Hcontext as [L Hctx].
  destruct (fresh_atom (L ++ context_support C)) as [x Hfresh].
  assert (HxL : ~ In x L).
  { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
  assert (Hxsupport : ~ In x (context_support C)).
  { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
  set (rho1 := substitution_update (fun y => tm_fvar y) x t1).
  set (rho2 := substitution_update (fun y => tm_fvar y) x t2).
  assert (Henv : related_expression_substitutions
      (security_of T_result).(indirect_reader) (update empty x T_secret) rho1 rho2).
  { intros y U Hlookup. unfold rho1, rho2, substitution_update.
    destruct (Nat.eqb x y) eqn:E.
    - apply Nat.eqb_eq in E. subst y. rewrite lookup_update_eq in Hlookup.
      inversion Hlookup; subst U.
      apply secret_expressions_related; assumption.
    - apply Nat.eqb_neq in E. rewrite lookup_update_neq in Hlookup by congruence.
      simpl in Hlookup. discriminate. }
  pose proof (Hctx x HxL) as Htyped_context.
  pose proof (fundamental_expressions _ _ _ Htyped_context
    (security_of T_result).(indirect_reader) rho1 rho2 Henv) as Hctxrel.
  assert (Hrho1x : rho1 x = t1).
  { unfold rho1, substitution_update. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hrho2x : rho2 x = t2).
  { unfold rho2, substitution_update. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hsupport1 : forall y, In y (context_support C) -> rho1 y = tm_fvar y).
  { intros y Hy. unfold rho1, substitution_update.
    destruct (Nat.eqb x y) eqn:E.
    - apply Nat.eqb_eq in E. subst y. contradiction.
    - reflexivity. }
  assert (Hsupport2 : forall y, In y (context_support C) -> rho2 y = tm_fvar y).
  { intros y Hy. unfold rho2, substitution_update.
    destruct (Nat.eqb x y) eqn:E.
    - apply Nat.eqb_eq in E. subst y. contradiction.
    - reflexivity. }
  pose proof (instantiate_plug_update C x t1 rho1 Hrho1x Hsupport1) as Eplug1.
  pose proof (instantiate_plug_update C x t2 rho2 Hrho2x Hsupport2) as Eplug2.
  destruct Hctxrel as [_ [_ Hlift]].
  rewrite Eplug1, Eplug2 in Hlift.
  intros v1 v2 Heval1 Heval2.
  pose proof (Hlift v1 v2 Heval1 Heval2) as Hrelated.
  eapply related_ground_values_equal with
    (kappa := security_of T_result)
    (observer := (security_of T_result).(indirect_reader)).
  - exact Hground.
  - exact Htransparent.
  - apply flows_to_refl.
  - apply flows_to_refl.
  - exact Hrelated.
Qed.
