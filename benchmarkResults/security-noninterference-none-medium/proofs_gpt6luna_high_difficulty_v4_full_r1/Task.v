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

Lemma security_le_refl : forall k, security_le k k.
Proof. intros [r ir]. split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3] [Hr12 Hi12] [Hr23 Hi23].
  split; eapply flows_to_trans; eauto.
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

Lemma multi_congruence : forall (C : tm -> tm),
  (forall t t', step t t' -> step (C t) (C t')) ->
  forall t t', multi t t' -> multi (C t) (C t').
Proof.
  intros C HC t t' H. induction H.
  - apply multi_refl.
  - eapply multi_step; [apply HC; exact H | exact IHmulti].
Qed.

Lemma protect_value_compose : forall v l1 l2,
  protect_value (protect_value v l1) l2 = protect_value v (join l1 l2).
Proof.
  intros v l1 l2. destruct v; simpl; try reflexivity;
    match goal with k : security |- _ => destruct k as [r ir] end;
    destruct r, ir, l1, l2; reflexivity.
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

Definition erase_context (Gamma : context) : context :=
  map (fun entry => (fst entry, erase_type (snd entry))) Gamma.

Lemma protect_value_low : forall v, protect_value v Low = v.
Proof.
  destruct v; simpl; try reflexivity;
    match goal with k : security |- _ => destruct k as [r ir] end;
    destruct r, ir; reflexivity.
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

Lemma lookup_context_key : forall Gamma x T,
  lookup_context x Gamma = Some T -> In x (map fst Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T H; simpl in *; [discriminate |].
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. auto.
  - right. eapply IH; exact H.
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

(* The value relation forgets the contents of values whose indirect reader is
   High.  At public types it compares constructors recursively; public
   functions are compared by applying them to related arguments. *)
Fixpoint value_rel (T : ty) (v1 v2 : tm) : Prop :=
  match (security_of T).(indirect_reader) with
  | High => True
  | Low =>
      match T with
      | Ty_Unit _ => exists k1 k2, v1 = tm_unit k1 /\ v2 = tm_unit k2
      | Ty_Sum A B kt =>
          (exists a1 a2 k1 k2, v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\
             security_le k1 kt /\ security_le k2 kt /\ value_rel A a1 a2) \/
          (exists b1 b2 k1 k2, v1 = tm_inr b1 k1 /\ v2 = tm_inr b2 k2 /\
             security_le k1 kt /\ security_le k2 kt /\ value_rel B b1 b2)
      | Ty_Prod A B kt =>
          exists a1 a2 b1 b2 k1 k2,
            v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
            security_le k1 kt /\ security_le k2 kt /\
            value_rel A a1 a2 /\ value_rel B b1 b2
      | Ty_Arrow A B kt =>
          exists A1 b1 k1 A2 b2 k2,
            v1 = tm_abs A1 b1 k1 /\ v2 = tm_abs A2 b2 k2 /\
            security_le k1 kt /\ security_le k2 kt /\
            forall a1 a2 w1 w2,
              value a1 -> value a2 -> value_rel A a1 a2 ->
              big_step (open b1 a1) w1 -> big_step (open b2 a2) w2 ->
              value_rel B w1 w2
      end
  end.

Definition term_rel (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, big_step t1 v1 -> big_step t2 v2 -> value_rel T v1 v2.

Definition context_rel (C : program_context) (T_hole T_result : ty) : Prop :=
  forall t1 t2, term_rel T_hole t1 t2 ->
    term_rel T_result (plug C t1) (plug C t2).

Lemma value_rel_typrotect_high : forall T v1 v2,
  value_rel (ty_protect High T) v1 v2.
Proof. intros T v1 v2; destruct T; destruct s as [r ir]; destruct r, ir; simpl; exact I. Qed.

Lemma high_type_term_rel : forall T t1 t2,
  (security_of T).(indirect_reader) = High -> term_rel T t1 t2.
Proof.
  intros T t1 t2 Hhigh. unfold term_rel. intros v1 v2 Hb1 Hb2.
  destruct T; simpl in *; rewrite Hhigh; exact I.
Qed.

Lemma transparent_at_security_le : forall k T,
  transparent_at k T -> security_le (security_of T) k.
Proof. intros k T H; destruct T; simpl in *; tauto. Qed.

Lemma flows_to_low_inv : forall l, flows_to l Low -> l = Low.
Proof. destruct l; simpl; [reflexivity | contradiction]. Qed.

Lemma value_rel_subtype : forall T U v1 v2,
  subtype T U -> value_rel T v1 v2 -> value_rel U v1 v2.
Proof.
  intros T U v1 v2 Hsub. revert v1 v2. induction Hsub; intros v1 v2 Hrel;
    unfold value_rel in *; simpl in *.
  - destruct (indirect_reader kappa2) eqn:E; [|exact I].
    assert (indirect_reader kappa1 = Low) as Hlow.
    { pose proof (proj2 H1) as Hflow. rewrite E in Hflow. eapply flows_to_low_inv; eauto. }
    rewrite Hlow in Hrel. destruct Hrel as [a [b [-> ->]]].
    exists a, b. split; reflexivity.
  - destruct (indirect_reader kappa2) eqn:E; [|exact I].
    assert (indirect_reader kappa1 = Low) as Hlow.
    { pose proof (proj2 H1) as Hflow. rewrite E in Hflow. eapply flows_to_low_inv; eauto. }
    rewrite Hlow in Hrel. destruct Hrel as [[a [b [ka [kb [-> [-> [Hka [Hkb Hab]]]]]]]] |
                                              [a [b [ka [kb [-> [-> [Hka [Hkb Hab]]]]]]]]].
    + left. exists a, b, ka, kb. split; [reflexivity |]. split; [reflexivity |].
      split; [eapply security_le_trans; eauto |]. split; [eapply security_le_trans; eauto |].
      eapply IHHsub1; exact Hab.
    + right. exists a, b, ka, kb. split; [reflexivity |]. split; [reflexivity |].
      split; [eapply security_le_trans; eauto |]. split; [eapply security_le_trans; eauto |].
      eapply IHHsub2; exact Hab.
  - destruct (indirect_reader kappa2) eqn:E; [|exact I].
    assert (indirect_reader kappa1 = Low) as Hlow.
    { pose proof (proj2 H1) as Hflow. rewrite E in Hflow. eapply flows_to_low_inv; eauto. }
    rewrite Hlow in Hrel. destruct Hrel as [a [b [c [d [ka [kb [Heq1 [Heq2 [Hka [Hkb [Hab Hcd]]]]]]]]]]].
    subst v1 v2.
    exists a, b, c, d, ka, kb. split; [reflexivity |]. split; [reflexivity |].
    split; [eapply security_le_trans; eauto |]. split; [eapply security_le_trans; eauto |].
    split; [eapply IHHsub1; exact Hab | eapply IHHsub2; exact Hcd].
  - destruct (indirect_reader kappa2) eqn:E; [|exact I].
    assert (indirect_reader kappa1 = Low) as Hlow.
    { pose proof (proj2 H1) as Hflow. rewrite E in Hflow. eapply flows_to_low_inv; eauto. }
    rewrite Hlow in Hrel.
    destruct Hrel as [A1 [b1 [k1 [A2 [b2 [k2 [-> [-> [Hsk1 [Hsk2 Hfun]]]]]]]]]].
    exists A1, b1, k1, A2, b2, k2.
    split; [reflexivity |]. split; [reflexivity |].
    split; [eapply security_le_trans; eauto |].
    split; [eapply security_le_trans; eauto |].
    intros a b w1 w2 Hva Hvb Hab Hstep1 Hstep2.
    eapply IHHsub2.
    eapply Hfun.
    + exact Hva.
    + exact Hvb.
    + eapply IHHsub1; exact Hab.
    + exact Hstep1.
    + exact Hstep2.
  - eapply IHHsub2. eapply IHHsub1. exact Hrel.
Qed.

Lemma value_rel_ground_erase : forall T k v1 v2,
  ground T -> transparent_at k T -> (k.(indirect_reader) = Low) ->
  value_rel T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  induction T as [k0 | A IHA B IHB k0 | A IHA B IHB k0 | A IHA B IHB k0];
    intros k v1 v2 Hg Htr Hlow Hrel; destruct k as [kr kir]; simpl in *.
  - destruct (indirect_reader k0) eqn:E.
    + destruct Hrel as [k1 [k2 [-> ->]]]. reflexivity.
    + destruct Htr as [Hle _]. destruct Hle as [_ Hflow].
      rewrite E in Hflow. rewrite Hlow in Hflow. simpl in Hflow. contradiction.
  - destruct Hg as [Hg1 Hg2]. destruct Htr as [Houter [Htr1 Htr2]].
    destruct (indirect_reader k0) eqn:E.
    + assert (indirect_reader (security_of A) = Low) as Hlow1.
      { pose proof (transparent_at_security_le _ _ Htr1) as Hle. unfold security_le in Hle. destruct Hle as [_ Hflow].
        rewrite Hlow in Hflow. destruct (security_of A).(indirect_reader);
          simpl in Hflow; [reflexivity | contradiction]. }
      assert (indirect_reader (security_of B) = Low) as Hlow2.
      { pose proof (transparent_at_security_le _ _ Htr2) as Hle. unfold security_le in Hle. destruct Hle as [_ Hflow].
        rewrite Hlow in Hflow. destruct (security_of B).(indirect_reader);
          simpl in Hflow; [reflexivity | contradiction]. }
      destruct Hrel as [Hleft | Hright].
      * destruct Hleft as [a1 [a2 [k1 [k2 [Heq1 [Heq2 [Hsec1 [Hsec2 Ha]]]]]]]].
        subst v1 v2. simpl. f_equal. eapply IHA; eauto.
      * destruct Hright as [b1 [b2 [k1 [k2 [Heq1 [Heq2 [Hsec1 [Hsec2 Hb]]]]]]]].
        subst v1 v2. simpl. f_equal. eapply IHB; eauto.
    + destruct Houter as [_ Hflow]. rewrite E in Hflow. rewrite Hlow in Hflow. simpl in Hflow. contradiction.
  - destruct Hg as [Hg1 Hg2]. destruct Htr as [Houter [Htr1 Htr2]].
    destruct (indirect_reader k0) eqn:E.
    + assert (indirect_reader (security_of A) = Low) as Hlow1.
      { pose proof (transparent_at_security_le _ _ Htr1) as Hle. unfold security_le in Hle. destruct Hle as [_ Hflow].
        rewrite Hlow in Hflow. destruct (security_of A).(indirect_reader);
          simpl in Hflow; [reflexivity | contradiction]. }
      assert (indirect_reader (security_of B) = Low) as Hlow2.
      { pose proof (transparent_at_security_le _ _ Htr2) as Hle. unfold security_le in Hle. destruct Hle as [_ Hflow].
        rewrite Hlow in Hflow. destruct (security_of B).(indirect_reader);
          simpl in Hflow; [reflexivity | contradiction]. }
      destruct Hrel as (a1 & a2 & b1 & b2 & k1 & k2 & Heq1 & Heq2 & Hsec1 & Hsec2 & Ha & Hb).
      subst v1 v2. simpl. f_equal.
      * eapply IHA; eauto.
      * eapply IHB; eauto.
    + destruct Houter as [_ Hflow]. rewrite E in Hflow. rewrite Hlow in Hflow. simpl in Hflow. contradiction.
  - contradiction.
Qed.

Lemma nonflow_labels : forall l1 l2,
  ~ flows_to l1 l2 -> l1 = High /\ l2 = Low.
Proof. destruct l1, l2; simpl; intuition congruence. Qed.

Lemma instantiate_open_rec : forall t rho k u,
  (forall x, locally_closed (rho x)) ->
  instantiate rho (open_rec k u t) =
  open_rec k (instantiate rho u) (instantiate rho t).
Proof.
  induction t as [i | x | k0 | A b IHb k0 | t1 IH1 t2 IH2 r |
                  t1 IH1 t2 IH2 k0 | t0 IH0 r | t0 IH0 r |
                  t0 IH0 k0 | t0 IH0 k0 | t0 IH0 b1 IH1 b2 IH2 r |
                  l t0 IH0]; intros rho k u Hclosed; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - unfold locally_closed in Hclosed. simpl.
    symmetry. eapply open_rec_lc_at; [apply Hclosed | lia].
  - reflexivity.
  - f_equal. apply IHb; assumption.
  - rewrite (IH1 rho k u Hclosed), (IH2 rho k u Hclosed). reflexivity.
  - rewrite (IH1 rho k u Hclosed), (IH2 rho k u Hclosed). reflexivity.
  - f_equal. apply IH0; assumption.
  - f_equal. apply IH0; assumption.
  - f_equal. apply IH0; assumption.
  - f_equal. apply IH0; assumption.
  - rewrite (IH0 rho k u Hclosed), (IH1 rho (S k) u Hclosed),
      (IH2 rho (S k) u Hclosed). reflexivity.
  - f_equal. apply IH0; assumption.
Qed.

Lemma instantiate_open : forall t rho u,
  (forall x, locally_closed (rho x)) ->
  instantiate rho (open t u) = open (instantiate rho t) (instantiate rho u).
Proof. intros; apply instantiate_open_rec; assumption. Qed.

Lemma instantiate_update_fresh : forall t rho x u,
  ~ In x (fv t) ->
  instantiate (substitution_update rho x u) t = instantiate rho t.
Proof.
  induction t as [i | y | k0 | A b IHb k0 | t1 IH1 t2 IH2 r |
                  t1 IH1 t2 IH2 k0 | t0 IH0 r | t0 IH0 r |
                  t0 IH0 k0 | t0 IH0 k0 | t0 IH0 b1 IH1 b2 IH2 r |
                  l t0 IH0]; intros rho x u Hfresh; simpl in *.
  - reflexivity.
  - unfold substitution_update. destruct (Nat.eqb x y) eqn:E; [|reflexivity].
    apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
  - reflexivity.
  - f_equal. apply IHb. exact Hfresh.
  - f_equal.
    + apply IH1. intro Hin. apply Hfresh. apply in_or_app. auto.
    + apply IH2. intro Hin. apply Hfresh. apply in_or_app. auto.
  - f_equal.
    + apply IH1. intro Hin. apply Hfresh. apply in_or_app. auto.
    + apply IH2. intro Hin. apply Hfresh. apply in_or_app. auto.
  - f_equal. apply IH0. exact Hfresh.
  - f_equal. apply IH0. exact Hfresh.
  - f_equal. apply IH0. exact Hfresh.
  - f_equal. apply IH0. exact Hfresh.
  - f_equal.
    + apply IH0. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IH1. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply IH2. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - f_equal. apply IH0. exact Hfresh.
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty as
    [Gamma x0 T Hlook Hwf
    | Gamma kappa Hwf
    | L Gamma T1 body T2 kappa Hty1 Hk Hbody IHbody
    | Gamma t1 t2 T1 T2 kappa r Ht1 IHt1 Ht2 IHt2 Hflow
    | Gamma t1 t2 T1 T2 kappa Ht1 IHt1 Ht2 IHt2 Hk
    | Gamma t T1 T2 kappa r Ht IHt Hflow
    | Gamma t T1 T2 kappa r Ht IHt Hflow
    | Gamma t T1 T2 kappa Ht IHt Hw Hk
    | Gamma t T1 T2 kappa Hw Ht IHt Hk
    | L Gamma t body1 body2 T1 T2 T kappa r Ht IHt Hflow
        Hbody1 IHbody1 Hbody2 IHbody2
    | Gamma t T l Ht IHt
    | Gamma t T U Ht IHt Hsub];
    unfold locally_closed in *; simpl in *.
  - exact I.
  - exact I.
  - destruct (fresh_atom L) as [x Hx].
    specialize (IHbody x Hx). unfold locally_closed in IHbody.
    eapply lc_at_open_inv; exact IHbody.
  - split; assumption.
  - split; assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - repeat split; try assumption.
    + destruct (fresh_atom L) as [x Hx]. specialize (IHbody1 x Hx).
      unfold locally_closed in IHbody1. eapply lc_at_open_inv; exact IHbody1.
    + destruct (fresh_atom L) as [x Hx]. specialize (IHbody2 x Hx).
      unfold locally_closed in IHbody2. eapply lc_at_open_inv; exact IHbody2.
  - assumption.
  - assumption.
Qed.

Lemma fv_open_rec_preserve : forall t k y x,
  x <> y -> In x (fv t) -> In x (fv (open_rec k (tm_fvar y) t)).
Proof.
  induction t as [i | z | k0 | A b IHb k0 | t1 IH1 t2 IH2 r |
                  t1 IH1 t2 IH2 k0 | t0 IH0 r | t0 IH0 r |
                  t0 IH0 k0 | t0 IH0 k0 | t0 IH0 b1 IH1 b2 IH2 r |
                  l t0 IH0]; intros k y x Hneq Hin; simpl in *; try contradiction.
  - simpl in Hin. destruct Hin as [Heq | []]. subst x. simpl. auto.
  - eapply IHb; eauto.
  - apply in_app_iff in Hin as [Hin | Hin]; apply in_app_iff.
    + left. eapply IH1; eauto.
    + right. eapply IH2; eauto.
  - apply in_app_iff in Hin as [Hin | Hin]; apply in_app_iff.
    + left. eapply IH1; eauto.
    + right. eapply IH2; eauto.
  - eapply IH0; eauto.
  - eapply IH0; eauto.
  - eapply IH0; eauto.
  - eapply IH0; eauto.
  - repeat rewrite in_app_iff in Hin |- *.
    destruct Hin as [Hin | [Hin | Hin]].
    + left. eapply IH0; eauto.
    + right; left. eapply IH1; eauto.
    + right; right. eapply IH2; eauto.
  - eapply IH0; eauto.
Qed.

Lemma fv_open_preserve : forall t y x,
  x <> y -> In x (fv t) -> In x (fv (open t (tm_fvar y))).
Proof. intros; unfold open; eapply fv_open_rec_preserve; eauto. Qed.

Lemma has_type_fv : forall Gamma t T, has_type Gamma t T ->
  forall x, In x (fv t) -> exists U, lookup_context x Gamma = Some U.
Proof.
  intros Gamma t T Hty. induction Hty as
    [Gamma x T Hlook Hwf
    | Gamma kappa Hwf
    | L Gamma T1 body T2 kappa Hty1 Hk Hbody IHbody
    | Gamma t1 t2 T1 T2 kappa r Ht1 IHt1 Ht2 IHt2 Hflow
    | Gamma t1 t2 T1 T2 kappa Ht1 IHt1 Ht2 IHt2 Hk
    | Gamma t T1 T2 kappa r Ht IHt Hflow
    | Gamma t T1 T2 kappa r Ht IHt Hflow
    | Gamma t T1 T2 kappa Ht IHt Hw Hk
    | Gamma t T1 T2 kappa Hw Ht IHt Hk
    | L Gamma t body1 body2 T1 T2 T kappa r Ht IHt Hflow
        Hbody1 IHbody1 Hbody2 IHbody2
    | Gamma t T l Ht IHt
    | Gamma t T U Ht IHt Hsub]; intros x_fv Hfv; simpl in *.
  - destruct Hfv as [Heq | []]. subst x_fv. exists T. exact Hlook.
  - contradiction.
  - destruct (fresh_atom (x_fv :: L)) as [y Hy].
    assert (~ In y L) as HnotL by (intro Hin; apply Hy; right; exact Hin).
    assert (x_fv <> y) as Hneq by (intro Heq; subst; apply Hy; left; reflexivity).
    specialize (IHbody y HnotL x_fv (fv_open_preserve body y x_fv Hneq Hfv)).
    destruct IHbody as [U HU]. exists U.
    assert (Nat.eqb x_fv y = false) as Heqb by (apply Nat.eqb_neq; congruence).
    rewrite Heqb in HU. exact HU.
  - apply in_app_iff in Hfv as [Hfv | Hfv].
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - apply in_app_iff in Hfv as [Hfv | Hfv]; [eapply IHt1 | eapply IHt2]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - repeat rewrite in_app_iff in Hfv.
    destruct Hfv as [Hfv | [Hfv | Hfv]].
    + eapply IHt; eauto.
    + destruct (fresh_atom (x_fv :: L)) as [y Hy].
      assert (~ In y L) as HnotL by (intro Hin; apply Hy; right; exact Hin).
      assert (x_fv <> y) as Hneq by (intro Heq; subst; apply Hy; left; reflexivity).
      specialize (IHbody1 y HnotL x_fv (fv_open_preserve body1 y x_fv Hneq Hfv)).
      destruct IHbody1 as [U HU]. exists U.
      assert (Nat.eqb x_fv y = false) as Heqb by (apply Nat.eqb_neq; congruence).
      rewrite Heqb in HU. exact HU.
    + destruct (fresh_atom (x_fv :: L)) as [y Hy].
      assert (~ In y L) as HnotL by (intro Hin; apply Hy; right; exact Hin).
      assert (x_fv <> y) as Hneq by (intro Heq; subst; apply Hy; left; reflexivity).
      specialize (IHbody2 y HnotL x_fv (fv_open_preserve body2 y x_fv Hneq Hfv)).
      destruct IHbody2 as [U HU]. exists U.
      assert (Nat.eqb x_fv y = false) as Heqb by (apply Nat.eqb_neq; congruence).
      rewrite Heqb in HU. exact HU.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
Qed.

Lemma subst_fresh : forall t x u,
  ~ In x (fv t) -> subst x u t = t.
Proof.
  induction t as [i | y | k0 | A b IHb k0 | t1 IH1 t2 IH2 r |
                  t1 IH1 t2 IH2 k0 | t0 IH0 r | t0 IH0 r |
                  t0 IH0 k0 | t0 IH0 k0 | t0 IH0 b1 IH1 b2 IH2 r |
                  l t0 IH0]; intros x u Hfresh; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x y) eqn:E; [apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; simpl; auto | reflexivity].
  - reflexivity.
  - f_equal. apply IHb. exact Hfresh.
  - f_equal.
    + apply IH1. intro H; apply Hfresh; apply in_or_app; auto.
    + apply IH2. intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal.
    + apply IH1. intro H; apply Hfresh; apply in_or_app; auto.
    + apply IH2. intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal. apply IH0. exact Hfresh.
  - f_equal. apply IH0. exact Hfresh.
  - f_equal. apply IH0. exact Hfresh.
  - f_equal. apply IH0. exact Hfresh.
  - f_equal.
    + apply IH0. intro H; apply Hfresh; apply in_or_app; left; exact H.
    + apply IH1. intro H; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact H.
    + apply IH2. intro H; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact H.
  - f_equal. apply IH0. exact Hfresh.
Qed.

Lemma instantiate_subst : forall t x u,
  instantiate (substitution_update (fun y => tm_fvar y) x u) t = subst x u t.
Proof.
  induction t as [i | y | k0 | A b IHb k0 | t1 IH1 t2 IH2 r |
                  t1 IH1 t2 IH2 k0 | t0 IH0 r | t0 IH0 r |
                  t0 IH0 k0 | t0 IH0 k0 | t0 IH0 b1 IH1 b2 IH2 r |
                  l t0 IH0]; intros x u; simpl.
  - reflexivity.
  - unfold substitution_update. destruct (Nat.eqb x y); reflexivity.
  - reflexivity.
  - f_equal. apply IHb.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - f_equal; apply IH0.
  - f_equal; apply IH0.
  - f_equal; apply IH0.
  - f_equal; apply IH0.
  - rewrite IH0, IH1, IH2. reflexivity.
  - f_equal; apply IH0.
Qed.

Fixpoint program_context_fv (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ => program_context_fv C'
  | C_AppLeft C' t _ | C_PairLeft C' t _ => program_context_fv C' ++ fv t
  | C_AppRight t C' _ | C_PairRight t C' _ => fv t ++ program_context_fv C'
  | C_Fst C' _ | C_Snd C' _ | C_Inl C' _ | C_Inr C' _ | C_Protect _ C' =>
      program_context_fv C'
  | C_CaseScrutinee C' b1 b2 _ => program_context_fv C' ++ fv b1 ++ fv b2
  | C_CaseLeft t0 C' b2 _ => fv t0 ++ program_context_fv C' ++ fv b2
  | C_CaseRight t0 b1 C' _ => fv t0 ++ fv b1 ++ program_context_fv C'
  end.

Lemma subst_program_context_fresh : forall C x u,
  ~ In x (program_context_fv C) ->
  subst x u (plug C (tm_fvar x)) = plug C u.
Proof.
  induction C; intros x u Hfresh; simpl in *.
  - simpl. unfold subst. rewrite Nat.eqb_refl. reflexivity.
  - f_equal. apply IHC. exact Hfresh.
  - f_equal.
    + apply IHC. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply subst_fresh. intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply subst_fresh. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHC. intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply IHC. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply subst_fresh. intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply subst_fresh. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHC. intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - f_equal. apply IHC. exact Hfresh.
  - f_equal. apply IHC. exact Hfresh.
  - f_equal. apply IHC. exact Hfresh.
  - f_equal. apply IHC. exact Hfresh.
  - f_equal.
    + apply IHC. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply subst_fresh. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply subst_fresh. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply subst_fresh. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHC. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply subst_fresh. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply subst_fresh. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply subst_fresh. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply IHC. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - f_equal. apply IHC. exact Hfresh.
Qed.

Lemma instantiate_only_x : forall t rho x u,
  (forall y, In y (fv t) -> y = x) -> rho x = u ->
  instantiate rho t = subst x u t.
Proof.
  induction t as [i | y | k0 | A b IHb k0 | t1 IH1 t2 IH2 r |
                  t1 IH1 t2 IH2 k0 | t0 IH0 r | t0 IH0 r |
                  t0 IH0 k0 | t0 IH0 k0 | t0 IH0 b1 IH1 b2 IH2 r |
                  l t0 IH0]; intros rho x u Honly Hrx; simpl.
  - reflexivity.
  - assert (y = x) as Heq by (apply Honly; simpl; auto). subst y.
    rewrite Hrx. unfold subst. rewrite Nat.eqb_refl. reflexivity.
  - reflexivity.
  - f_equal. apply IHb; [intros; eapply Honly; eassumption | exact Hrx].
  - f_equal.
    + apply IH1; [intros z Hz; apply Honly; apply in_or_app; left; exact Hz | exact Hrx].
    + apply IH2; [intros z Hz; apply Honly; apply in_or_app; right; exact Hz | exact Hrx].
  - f_equal.
    + apply IH1; [intros z Hz; apply Honly; apply in_or_app; left; exact Hz | exact Hrx].
    + apply IH2; [intros z Hz; apply Honly; apply in_or_app; right; exact Hz | exact Hrx].
  - f_equal. apply IH0; [intros; eapply Honly; eassumption | exact Hrx].
  - f_equal. apply IH0; [intros; eapply Honly; eassumption | exact Hrx].
  - f_equal. apply IH0; [intros; eapply Honly; eassumption | exact Hrx].
  - f_equal. apply IH0; [intros; eapply Honly; eassumption | exact Hrx].
  - f_equal.
    + apply IH0; [intros z Hz; apply Honly; apply in_or_app; left; exact Hz | exact Hrx].
    + apply IH1; [intros z Hz; apply Honly; apply in_or_app; right; apply in_or_app; left; exact Hz | exact Hrx].
    + apply IH2; [intros z Hz; apply Honly; apply in_or_app; right; apply in_or_app; right; exact Hz | exact Hrx].
  - f_equal. apply IH0; [intros; eapply Honly; eassumption | exact Hrx].
Qed.

Definition semantic_environment (Gamma : context)
    (rho1 rho2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    forall v1 v2, big_step (rho1 x) v1 -> big_step (rho2 x) v2 ->
      value_rel T v1 v2.

Lemma value_big_step : forall v, value v -> big_step v v.
Proof.
  intros v Hv. induction Hv.
  - constructor.
  - apply B_Abs. assumption.
  - eapply B_Pair; eassumption.
  - apply B_Inl. assumption.
  - apply B_Inr. assumption.
Qed.

Lemma value_big_step_inv : forall v w, value v -> big_step v w -> w = v.
Proof.
  intros v w Hv. revert w. induction Hv; intros w Hb; inversion Hb; subst; try reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv; unfold locally_closed in *; simpl in *; auto.
Qed.

Lemma protect_value_is_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv. inversion Hv; subst; destruct l; simpl; constructor; eauto.
Qed.

Lemma big_step_value : forall t v, big_step t v -> value v.
Proof.
  intros t v H. induction H.
  - constructor.
  - constructor; assumption.
  - apply protect_value_is_value. assumption.
  - constructor; assumption.
  - match goal with Hpair : value (tm_pair _ _ _) |- _ =>
      inversion Hpair; subst; apply protect_value_is_value; assumption end.
  - match goal with Hpair : value (tm_pair _ _ _) |- _ =>
      inversion Hpair; subst; apply protect_value_is_value; assumption end.
  - constructor; assumption.
  - constructor; assumption.
  - match goal with Hsum : value (tm_inl _ _) |- _ =>
      inversion Hsum; subst; apply protect_value_is_value; assumption end.
  - match goal with Hsum : value (tm_inr _ _) |- _ =>
      inversion Hsum; subst; apply protect_value_is_value; assumption end.
  - apply protect_value_is_value. assumption.
Qed.

Lemma step_big_step_inv : forall t t' w,
  step t t' -> big_step t' w -> big_step t w.
Proof.
  intros t t' w Hstep. revert w. induction Hstep; intros w Hb.
  - inversion Hb; subst. eapply B_App; eauto using value_big_step.
  - inversion Hb; subst. eapply B_App.
    + match goal with IH : forall z, big_step ?t' z -> big_step ?t z |- _ => eapply IH; eassumption end.
    + eassumption.
    + eassumption.
    + eassumption.
  - inversion Hb; subst. eapply B_App.
    + match goal with Hv : value ?f, Hbf : big_step ?f ?abs |- _ =>
        pose proof (value_big_step_inv _ _ Hv Hbf); subst end.
      apply value_big_step; assumption.
    + match goal with IH : forall z, big_step ?t' z -> big_step ?t z |- _ => eapply IH; eassumption end.
    + eassumption.
    + eassumption.
  - inversion Hb; subst. eapply B_Pair.
    + match goal with IH : forall z, big_step ?t' z -> big_step ?t z |- _ => eapply IH; eassumption end.
    + eassumption.
  - inversion Hb; subst.
    match goal with Hv : value ?a, Hba : big_step ?a ?b |- _ =>
      pose proof (value_big_step_inv _ _ Hv Hba); subst end.
    eapply B_Pair.
    + apply value_big_step; assumption.
    + match goal with IH : forall z, big_step ?t' z -> big_step ?t z |- _ => eapply IH; eassumption end.
  - inversion Hb; subst.
    match goal with Hv : value ?v, Hbv : big_step ?v ?u |- _ =>
      pose proof (value_big_step_inv _ _ Hv Hbv); subst end.
    eapply B_Fst.
    + apply value_big_step. constructor; assumption.
    + assumption.
  - inversion Hb; subst. eapply B_Fst; eauto.
  - inversion Hb; subst.
    match goal with Hv : value ?v, Hbv : big_step ?v ?u |- _ =>
      pose proof (value_big_step_inv _ _ Hv Hbv); subst end.
    eapply B_Snd.
    + apply value_big_step. constructor; assumption.
    + assumption.
  - inversion Hb; subst. eapply B_Snd; eauto.
  - inversion Hb; subst. eapply B_Inl; eauto.
  - inversion Hb; subst. eapply B_Inr; eauto.
  - inversion Hb; subst. assert (value (tm_inl v kappa)) by (constructor; assumption).
    eapply B_CaseLeft; eauto using value_big_step.
  - inversion Hb; subst. assert (value (tm_inr v kappa)) by (constructor; assumption).
    eapply B_CaseRight; eauto using value_big_step.
  - inversion Hb; subst; [eapply B_CaseLeft | eapply B_CaseRight]; eauto.
  - pose proof (protect_value_is_value v l H) as Hpv.
    pose proof (value_big_step_inv (protect_value v l) w Hpv Hb) as ->.
    eapply B_Protect; eauto using value_big_step.
  - inversion Hb; subst. eapply B_Protect; eauto.
Qed.

Lemma multi_big_step : forall t v,
  multi t v -> value v -> big_step t v.
Proof.
  intros t v Hm. induction Hm; intros Hv.
  - subst. apply value_big_step. exact Hv.
  - eapply step_big_step_inv; [exact H | apply IHHm; exact Hv].
Qed.

Lemma lookup_update_neq' : forall Gamma y x U T,
  y <> x -> lookup_context y (update Gamma x T) = Some U ->
  lookup_context y Gamma = Some U.
Proof.
  intros Gamma y x U T Hneq H. rewrite lookup_update_neq in H; auto.
Qed.

Lemma substitution_update_env : forall Gamma rho1 rho2 x T a1 a2,
  semantic_environment Gamma rho1 rho2 -> value_rel T a1 a2 ->
  value a1 -> value a2 ->
  semantic_environment (update Gamma x T)
    (substitution_update rho1 x a1) (substitution_update rho2 x a2).
Proof.
  intros Gamma rho1 rho2 x T a1 a2 Henv Hrel Hva1 Hva2 y U Hlookup.
  destruct (Nat.eq_dec y x) as [-> | Hneq].
  - rewrite lookup_update_eq in Hlookup. inversion Hlookup; subst U.
    intros w1 w2 Hb1 Hb2. unfold substitution_update in Hb1, Hb2.
    rewrite Nat.eqb_refl in Hb1, Hb2.
    pose proof (value_big_step_inv _ _ Hva1 Hb1) as ->.
    pose proof (value_big_step_inv _ _ Hva2 Hb2) as ->. exact Hrel.
  - rewrite lookup_update_neq in Hlookup by congruence.
    intros v1 v2 Hb1 Hb2. specialize (Henv y U Hlookup v1 v2).
    unfold substitution_update in Hb1, Hb2.
    assert (Nat.eqb x y = false) as E by (apply Nat.eqb_neq; congruence).
    rewrite E in Hb1, Hb2. eauto.
Qed.

Lemma cofinite_body_fundamental : forall L Gamma A body B rho1 rho2,
  (forall y, locally_closed (rho1 y)) ->
  (forall y, locally_closed (rho2 y)) ->
  semantic_environment Gamma rho1 rho2 ->
  (forall x, ~ In x L -> forall rho1' rho2',
    semantic_environment (update Gamma x A) rho1' rho2' ->
    (forall y, locally_closed (rho1' y)) ->
    (forall y, locally_closed (rho2' y)) ->
    term_rel B (instantiate rho1' (open body (tm_fvar x)))
      (instantiate rho2' (open body (tm_fvar x)))) ->
  forall a1 a2 w1 w2,
    value a1 -> value a2 -> value_rel A a1 a2 ->
    big_step (open (instantiate rho1 body) a1) w1 ->
    big_step (open (instantiate rho2 body) a2) w2 ->
    value_rel B w1 w2.
Proof.
  intros L Gamma A body B rho1 rho2 Hlc1 Hlc2 Henv Hcof a1 a2 w1 w2 Hva1 Hva2 Hrel Hb1 Hb2.
  destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
  assert (~ In x L) as HnotL by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
  assert (~ In x (fv body)) as Hnotbody by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
  set (rho1' := substitution_update rho1 x a1).
  set (rho2' := substitution_update rho2 x a2).
  assert (Henv' : semantic_environment (update Gamma x A) rho1' rho2').
  { unfold rho1', rho2'.
    eapply substitution_update_env; [exact Henv | exact Hrel | exact Hva1 | exact Hva2]. }
  assert (Hlc1' : forall y, locally_closed (rho1' y)).
  { intro y. unfold rho1'. unfold substitution_update.
    destruct (Nat.eqb x y) eqn:E1.
    - apply Nat.eqb_eq in E1. subst y. apply value_lc. exact Hva1.
    - apply Hlc1. }
  assert (Hlc2' : forall y, locally_closed (rho2' y)).
  { intro y. unfold rho2'. unfold substitution_update.
    destruct (Nat.eqb x y) eqn:E1.
    - apply Nat.eqb_eq in E1. subst y. apply value_lc. exact Hva2.
    - apply Hlc2. }
  assert (Hinst1 : instantiate rho1' (open body (tm_fvar x)) =
      open (instantiate rho1 body) a1).
  { unfold rho1'. rewrite instantiate_open by exact Hlc1'.
    rewrite (instantiate_update_fresh body rho1 x a1 Hnotbody).
    unfold substitution_update. simpl. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hinst2 : instantiate rho2' (open body (tm_fvar x)) =
      open (instantiate rho2 body) a2).
  { unfold rho2'. rewrite instantiate_open by exact Hlc2'.
    rewrite (instantiate_update_fresh body rho2 x a2 Hnotbody).
    unfold substitution_update. simpl. rewrite Nat.eqb_refl. reflexivity. }
  pose proof (Hcof x HnotL rho1' rho2' Henv' Hlc1' Hlc2') as Hbodyrel.
  unfold term_rel in Hbodyrel. rewrite <- Hinst1 in Hb1. rewrite <- Hinst2 in Hb2.
  eapply Hbodyrel; eassumption.
Qed.

Lemma fundamental : forall Gamma t T, has_type Gamma t T ->
  forall rho1 rho2,
    semantic_environment Gamma rho1 rho2 ->
    (forall x, locally_closed (rho1 x)) ->
    (forall x, locally_closed (rho2 x)) ->
    term_rel T (instantiate rho1 t) (instantiate rho2 t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho1 rho2 Henv Hlc1 Hlc2.
  - unfold term_rel. simpl. intros v1 v2 Hb1 Hb2. eapply Henv; eauto.
  - unfold term_rel. simpl. intros v1 v2 Hb1 Hb2.
    inversion Hb1; inversion Hb2; subst. simpl. unfold value_rel. simpl.
    destruct (indirect_reader kappa); [exists kappa, kappa; auto | exact I].
  - unfold term_rel. simpl. intros f1 f2 Hf1 Hf2.
    inversion Hf1; inversion Hf2; subst. unfold value_rel. simpl.
    destruct (indirect_reader kappa) eqn:E; [|exact I].
    exists T1, (instantiate rho1 body), kappa, T1, (instantiate rho2 body), kappa.
    split; [reflexivity |]. split; [reflexivity |].
    split; [apply security_le_refl |]. split; [apply security_le_refl |].
    intros a1 a2 w1 w2 Hva1 Hva2 Harg Hbody1 Hbody2.
    destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
    assert (~ In x L) as HnotL by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (~ In x (fv body)) as Hnotbody by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    set (rho1' := substitution_update rho1 x a1).
    set (rho2' := substitution_update rho2 x a2).
    assert (Henv' : semantic_environment (update Gamma x T1) rho1' rho2').
    { unfold rho1', rho2'. eapply substitution_update_env; eauto. }
    assert (Hlc1' : forall y, locally_closed (rho1' y)).
    { intro y. unfold rho1'. unfold substitution_update.
      destruct (Nat.eqb x y) eqn:E1.
      - apply Nat.eqb_eq in E1. subst y. apply value_lc. exact Hva1.
      - apply Hlc1. }
    assert (Hlc2' : forall y, locally_closed (rho2' y)).
    { intro y. unfold rho2'. unfold substitution_update.
      destruct (Nat.eqb x y) eqn:E1.
      - apply Nat.eqb_eq in E1. subst y. apply value_lc. exact Hva2.
      - apply Hlc2. }
    assert (Hinst1 : instantiate rho1' (open body (tm_fvar x)) =
        open (instantiate rho1 body) a1).
    { unfold rho1'. rewrite instantiate_open by exact Hlc1'.
      rewrite (instantiate_update_fresh body rho1 x a1 Hnotbody).
      unfold substitution_update. simpl. rewrite Nat.eqb_refl. reflexivity. }
    assert (Hinst2 : instantiate rho2' (open body (tm_fvar x)) =
        open (instantiate rho2 body) a2).
    { unfold rho2'. rewrite instantiate_open by exact Hlc2'.
      rewrite (instantiate_update_fresh body rho2 x a2 Hnotbody).
      unfold substitution_update. simpl. rewrite Nat.eqb_refl. reflexivity. }
    pose proof (H2 x HnotL rho1' rho2' Henv' Hlc1' Hlc2') as Hbodyrel.
    unfold term_rel in Hbodyrel.
    rewrite <- Hinst1 in Hbody1. rewrite <- Hinst2 in Hbody2.
    eapply Hbodyrel; eassumption.
  - unfold term_rel. simpl. intros w1 w2 Hb1 Hb2.
    inversion Hb1; inversion Hb2; subst.
    pose proof (IHHty1 rho1 rho2 Henv Hlc1 Hlc2) as Hfunrel.
    pose proof (IHHty2 rho1 rho2 Henv Hlc1 Hlc2) as Hargrel.
    unfold term_rel in Hfunrel, Hargrel.
    destruct (indirect_reader kappa) eqn:E; [|apply value_rel_typrotect_high].
    pose proof (Hfunrel _ _ H3 H11) as Hfr.
    unfold value_rel in Hfr. simpl in Hfr. rewrite E in Hfr.
    destruct Hfr as [A1 [b1 [k1 [A2 [b2 [k2 [Heq1 [Heq2 [Hsec1 [Hsec2 Hbody]]]]]]]]]].
    inversion Heq1; inversion Heq2; subst.
    pose proof (Hargrel _ _ H4 H12) as Harg.
    pose proof (Hbody v v0 w w0 (big_step_value _ _ H4) (big_step_value _ _ H12)
      Harg H7 H15) as Hout.
    assert (indirect_reader k1 = Low) as Hklow.
    { pose proof (proj2 Hsec1) as Hflow. rewrite E in Hflow.
      eapply flows_to_low_inv; exact Hflow. }
    assert (indirect_reader k2 = Low) as Hk0low.
    { pose proof (proj2 Hsec2) as Hflow. rewrite E in Hflow.
      eapply flows_to_low_inv; exact Hflow. }
    rewrite Hklow, Hk0low, ty_protect_low, protect_value_low, protect_value_low.
    exact Hout.
  - unfold term_rel. simpl. intros w1 w2 Hb1 Hb2.
    inversion Hb1; inversion Hb2; subst.
    pose proof (IHHty1 rho1 rho2 Henv Hlc1 Hlc2) as Hleft.
    pose proof (IHHty2 rho1 rho2 Henv Hlc1 Hlc2) as Hright.
    unfold term_rel in Hleft, Hright.
    destruct (indirect_reader kappa); [|exact I].
    repeat eexists; repeat split; try reflexivity; try apply security_le_refl; eauto.
  - unfold term_rel. simpl. intros w1 w2 Hb1 Hb2.
    inversion Hb1; inversion Hb2; subst.
    pose proof (IHHty rho1 rho2 Henv Hlc1 Hlc2) as Hscrutrel.
    unfold term_rel in Hscrutrel.
    destruct (indirect_reader kappa) eqn:E; [|apply value_rel_typrotect_high].
    pose proof (Hscrutrel _ _ H2 H7) as Hpairrel.
    unfold value_rel in Hpairrel. simpl in Hpairrel. rewrite E in Hpairrel.
    destruct Hpairrel as (p1 & p2 & q1 & q2 & pk1 & pk2 & Heq1 & Heq2 & Hsec1 & Hsec2 & Hleft & Hright).
    inversion Heq1; inversion Heq2; subst.
    assert (indirect_reader pk1 = Low) as Hklow.
    { pose proof (proj2 Hsec1) as Hflow. rewrite E in Hflow.
      eapply flows_to_low_inv; exact Hflow. }
    assert (indirect_reader pk2 = Low) as Hk0low.
    { pose proof (proj2 Hsec2) as Hflow. rewrite E in Hflow.
      eapply flows_to_low_inv; exact Hflow. }
    rewrite Hklow, Hk0low, ty_protect_low, protect_value_low, protect_value_low.
    exact Hleft.
  - unfold term_rel. simpl. intros w1 w2 Hb1 Hb2.
    inversion Hb1; inversion Hb2; subst.
    pose proof (IHHty rho1 rho2 Henv Hlc1 Hlc2) as Hscrutrel.
    unfold term_rel in Hscrutrel.
    destruct (indirect_reader kappa) eqn:E; [|apply value_rel_typrotect_high].
    pose proof (Hscrutrel _ _ H2 H7) as Hpairrel.
    unfold value_rel in Hpairrel. simpl in Hpairrel. rewrite E in Hpairrel.
    destruct Hpairrel as (p1 & p2 & q1 & q2 & pk1 & pk2 & Heq1 & Heq2 & Hsec1 & Hsec2 & Hleft & Hright).
    inversion Heq1; inversion Heq2; subst.
    assert (indirect_reader pk1 = Low) as Hk1low.
    { pose proof (proj2 Hsec1) as Hflow. rewrite E in Hflow.
      eapply flows_to_low_inv; exact Hflow. }
    assert (indirect_reader pk2 = Low) as Hk2low.
    { pose proof (proj2 Hsec2) as Hflow. rewrite E in Hflow.
      eapply flows_to_low_inv; exact Hflow. }
    rewrite Hk1low, Hk2low, ty_protect_low, protect_value_low, protect_value_low.
    exact Hright.
  - unfold term_rel. simpl. intros w1 w2 Hb1 Hb2.
    inversion Hb1; inversion Hb2; subst.
    pose proof (IHHty rho1 rho2 Henv Hlc1 Hlc2) as Hpayload.
    unfold term_rel in Hpayload.
    destruct (indirect_reader kappa); [left; repeat eexists; repeat split;
      try reflexivity; try apply security_le_refl; eauto | exact I].
  - unfold term_rel. simpl. intros w1 w2 Hb1 Hb2.
    inversion Hb1; inversion Hb2; subst.
    pose proof (IHHty rho1 rho2 Henv Hlc1 Hlc2) as Hpayload.
    unfold term_rel in Hpayload.
    destruct (indirect_reader kappa); [right; repeat eexists; repeat split;
      try reflexivity; try apply security_le_refl; eauto | exact I].
  - unfold term_rel. simpl. intros w1 w2 Hb1 Hb2.
    inversion Hb1; inversion Hb2; subst.
    all: pose proof (IHHty rho1 rho2 Henv Hlc1 Hlc2) as Hsumterm.
    all: unfold term_rel in Hsumterm.
    all: destruct (indirect_reader kappa) eqn:E; [|apply value_rel_typrotect_high].
    all: pose proof (Hsumterm _ _ H9 H17) as Hsumrel.
    all: unfold value_rel in Hsumrel; simpl in Hsumrel; rewrite E in Hsumrel.
    all: destruct Hsumrel as [Hleft | Hright].
    all: try (destruct Hleft as (a1 & a2 & sk1 & sk2 & Heq1 & Heq2 & Hsec1 & Hsec2 & Hpayload);
      inversion Heq1; inversion Heq2; subst;
      assert (value a1) as Hva by
        (pose proof (big_step_value _ _ H9) as Hv; inversion Hv; assumption);
      assert (value a2) as Hva0 by
        (pose proof (big_step_value _ _ H17) as Hv; inversion Hv; assumption);
      pose proof (cofinite_body_fundamental L Gamma T1 body1 T rho1 rho2
        Hlc1 Hlc2 Henv H1 a1 a2 w w0 Hva Hva0 Hpayload H11 H19) as Hout;
      assert (indirect_reader sk1 = Low) as Hklow by
        (pose proof (proj2 Hsec1) as Hflow; rewrite E in Hflow; eapply flows_to_low_inv; exact Hflow);
      assert (indirect_reader sk2 = Low) as Hk0low by
        (pose proof (proj2 Hsec2) as Hflow; rewrite E in Hflow; eapply flows_to_low_inv; exact Hflow);
      rewrite Hklow, Hk0low, ty_protect_low, protect_value_low, protect_value_low;
      exact Hout).
    all: try (destruct Hright as (a1 & a2 & sk1 & sk2 & Heq1 & Heq2 & Hsec1 & Hsec2 & Hpayload);
      inversion Heq1; inversion Heq2; subst;
      assert (value a1) as Hva by
        (pose proof (big_step_value _ _ H9) as Hv; inversion Hv; assumption);
      assert (value a2) as Hva0 by
        (pose proof (big_step_value _ _ H17) as Hv; inversion Hv; assumption);
      pose proof (cofinite_body_fundamental L Gamma T2 body2 T rho1 rho2
        Hlc1 Hlc2 Henv H3 a1 a2 w w0 Hva Hva0 Hpayload H11 H19) as Hout;
      assert (indirect_reader sk1 = Low) as Hklow by
        (pose proof (proj2 Hsec1) as Hflow; rewrite E in Hflow; eapply flows_to_low_inv; exact Hflow);
      assert (indirect_reader sk2 = Low) as Hk0low by
        (pose proof (proj2 Hsec2) as Hflow; rewrite E in Hflow; eapply flows_to_low_inv; exact Hflow);
      rewrite Hklow, Hk0low, ty_protect_low, protect_value_low, protect_value_low;
      exact Hout).
  - unfold term_rel. simpl. intros w1 w2 Hb1 Hb2.
    inversion Hb1; inversion Hb2; subst.
    pose proof (IHHty rho1 rho2 Henv Hlc1 Hlc2) as Hinner.
    unfold term_rel in Hinner.
    destruct l.
    + rewrite ty_protect_low, protect_value_low, protect_value_low.
      eapply Hinner; eassumption.
    + apply value_rel_typrotect_high.
  - unfold term_rel. simpl. intros w1 w2 Hb1 Hb2.
    pose proof (IHHty rho1 rho2 Henv Hlc1 Hlc2) as Hinner.
    unfold term_rel in Hinner.
    eapply value_rel_subtype.
    + match goal with Hsub : subtype _ _ |- _ => exact Hsub end.
    + eapply Hinner; eassumption.
Qed.

Lemma value_rel_protect : forall l T v1 v2,
  value_rel T v1 v2 ->
  value_rel (ty_protect l T) (protect_value v1 l) (protect_value v2 l).
Proof.
  intros l T v1 v2 Hrel. destruct l.
  - rewrite ty_protect_low. rewrite protect_value_low. rewrite protect_value_low. exact Hrel.
  - destruct T; destruct s as [r ir]; destruct r, ir; simpl; exact I.
Qed.

Lemma value_rel_protect_mono : forall l1 l2 T v1 v2,
  value_rel T v1 v2 -> flows_to l1 l2 ->
  value_rel (ty_protect l2 T) (protect_value v1 l1) (protect_value v2 l1).
Proof.
  intros l1 l2 T v1 v2 Hrel Hflow. destruct l2.
  - apply flows_to_low_inv in Hflow. subst l1.
    rewrite ty_protect_low, protect_value_low, protect_value_low. exact Hrel.
  - apply value_rel_typrotect_high.
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
  intros C t1 t2 T_secret T_result Hty1 Hty2 Hctx Hground Htransparent Hnoflow.
  unfold same_result. intros v1 v2 Heval1 Heval2.
  destruct Heval1 as [Hmulti1 Hvalue1].
  destruct Heval2 as [Hmulti2 Hvalue2].
  pose proof (multi_big_step _ _ Hmulti1 Hvalue1) as Hbig1.
  pose proof (multi_big_step _ _ Hmulti2 Hvalue2) as Hbig2.
  destruct (nonflow_labels _ _ Hnoflow) as [HsecretHigh HresultLow].
  destruct Hctx as [L Hctx].
  destruct (fresh_atom (L ++ program_context_fv C)) as [x Hfresh].
  assert (~ In x L) as HnotL by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
  assert (~ In x (program_context_fv C)) as HnotC by
    (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
  pose proof (Hctx x HnotL) as Htyped.
  set (rho1 := fun y => if Nat.eqb x y then t1 else tm_unit public).
  set (rho2 := fun y => if Nat.eqb x y then t2 else tm_unit public).
  assert (Henv : semantic_environment (update empty x T_secret) rho1 rho2).
  { unfold semantic_environment. intros y U Hlookup u1 u2 Hu1 Hu2.
    simpl in Hlookup. destruct (Nat.eqb y x) eqn:Eyx.
    - apply Nat.eqb_eq in Eyx. subst y. inversion Hlookup; subst U.
      unfold rho1, rho2 in Hu1, Hu2. rewrite Nat.eqb_refl in Hu1, Hu2.
      eapply high_type_term_rel; eauto.
    - discriminate. }
  assert (Hlc1 : forall y, locally_closed (rho1 y)).
  { intro y. unfold rho1. destruct (Nat.eqb x y); [eapply has_type_lc; eauto | simpl; exact I]. }
  assert (Hlc2 : forall y, locally_closed (rho2 y)).
  { intro y. unfold rho2. destruct (Nat.eqb x y); [eapply has_type_lc; eauto | simpl; exact I]. }
  assert (Honly : forall y, In y (fv (plug C (tm_fvar x))) -> y = x).
  { intros y Hy. destruct (has_type_fv _ _ _ Htyped y Hy) as [U Hlookup].
    simpl in Hlookup. destruct (Nat.eqb y x) eqn:Eyx.
    - apply Nat.eqb_eq. exact Eyx.
    - discriminate. }
  assert (Hrho1 : rho1 x = t1) by (unfold rho1; rewrite Nat.eqb_refl; reflexivity).
  assert (Hrho2 : rho2 x = t2) by (unfold rho2; rewrite Nat.eqb_refl; reflexivity).
  assert (Hinst1 : instantiate rho1 (plug C (tm_fvar x)) = plug C t1).
  { rewrite (instantiate_only_x _ rho1 x t1 Honly Hrho1).
    apply subst_program_context_fresh. exact HnotC. }
  assert (Hinst2 : instantiate rho2 (plug C (tm_fvar x)) = plug C t2).
  { rewrite (instantiate_only_x _ rho2 x t2 Honly Hrho2).
    apply subst_program_context_fresh. exact HnotC. }
  pose proof (fundamental _ _ _ Htyped rho1 rho2 Henv Hlc1 Hlc2) as Hfund.
  unfold term_rel in Hfund.
  rewrite <- Hinst1 in Hbig1. rewrite <- Hinst2 in Hbig2.
  pose proof (Hfund v1 v2 Hbig1 Hbig2) as Hrel.
  unfold transparent in Htransparent.
  eapply value_rel_ground_erase; eauto.
Qed.
