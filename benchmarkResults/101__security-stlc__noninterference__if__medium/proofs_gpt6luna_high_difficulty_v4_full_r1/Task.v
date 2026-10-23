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

Lemma security_le_refl : forall k, security_le k k.
Proof. intros [r ir]. split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3] [Hr1 Hi1] [Hr2 Hi2].
  split; eapply flows_to_trans; eassumption.
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
      big_step t v -> big_step (tm_protect l t) (protect_value v l)
  | B_IfTrue : forall c yes no r v k result,
      big_step c (tm_inl v k) -> flows_to k.(reader) r -> big_step yes result ->
      big_step (tm_if c yes no r) (protect_value result k.(indirect_reader))
  | B_IfFalse : forall c yes no r v k result,
      big_step c (tm_inr v k) -> flows_to k.(reader) r -> big_step no result ->
      big_step (tm_if c yes no r) (protect_value result k.(indirect_reader)).

Lemma multi_congruence : forall (C : tm -> tm),
  (forall t t', step t t' -> step (C t) (C t')) ->
  forall t t', multi t t' -> multi (C t) (C t').
Proof.
  intros C HC t t' H. induction H.
  - apply multi_refl.
  - eapply multi_step; [apply HC; exact H | exact IHmulti].
Qed.

Lemma multi_app_left : forall t t' a r,
  t -->* t' -> tm_app t a r -->* tm_app t' a r.
Proof. intros t t' a r H; eapply (multi_congruence (fun x => tm_app x a r));
  [intros; apply ST_App1; eassumption | exact H]. Qed.
Lemma multi_app_right : forall f t t' r,
  value f -> t -->* t' -> tm_app f t r -->* tm_app f t' r.
Proof. intros f t t' r Hf H; eapply (multi_congruence (fun x => tm_app f x r));
  [intros; apply ST_App2; eassumption | exact H]. Qed.
Lemma multi_pair_left : forall t t' b k,
  t -->* t' -> tm_pair t b k -->* tm_pair t' b k.
Proof. intros t t' b k H; eapply (multi_congruence (fun x => tm_pair x b k));
  [intros; apply ST_Pair1; eassumption | exact H]. Qed.
Lemma multi_pair_right : forall a t t' k,
  value a -> t -->* t' -> tm_pair a t k -->* tm_pair a t' k.
Proof. intros a t t' k Ha H; eapply (multi_congruence (fun x => tm_pair a x k));
  [intros; apply ST_Pair2; eassumption | exact H]. Qed.
Lemma multi_fst : forall t t' r,
  t -->* t' -> tm_fst t r -->* tm_fst t' r.
Proof. intros t t' r H; eapply (multi_congruence (fun x => tm_fst x r));
  [intros; apply ST_Fst; eassumption | exact H]. Qed.
Lemma multi_snd : forall t t' r,
  t -->* t' -> tm_snd t r -->* tm_snd t' r.
Proof. intros t t' r H; eapply (multi_congruence (fun x => tm_snd x r));
  [intros; apply ST_Snd; eassumption | exact H]. Qed.
Lemma multi_inl : forall t t' k,
  t -->* t' -> tm_inl t k -->* tm_inl t' k.
Proof. intros t t' k H; eapply (multi_congruence (fun x => tm_inl x k));
  [intros; apply ST_Inl; eassumption | exact H]. Qed.
Lemma multi_inr : forall t t' k,
  t -->* t' -> tm_inr t k -->* tm_inr t' k.
Proof. intros t t' k H; eapply (multi_congruence (fun x => tm_inr x k));
  [intros; apply ST_Inr; eassumption | exact H]. Qed.
Lemma multi_case_scrutinee : forall t t' b1 b2 r,
  t -->* t' -> tm_case t b1 b2 r -->* tm_case t' b1 b2 r.
Proof. intros t t' b1 b2 r H; eapply (multi_congruence (fun x => tm_case x b1 b2 r));
  [intros; apply ST_Case; eassumption | exact H]. Qed.
Lemma multi_protect : forall l t t',
  t -->* t' -> tm_protect l t -->* tm_protect l t'.
Proof. intros l t t' H; eapply (multi_congruence (fun x => tm_protect l x));
  [intros; apply ST_Protect; eassumption | exact H]. Qed.
Lemma multi_if_scrutinee : forall c c' y n r,
  c -->* c' -> tm_if c y n r -->* tm_if c' y n r.
Proof. intros c c' y n r H; eapply (multi_congruence (fun x => tm_if x y n r));
  [intros; apply ST_If; eassumption | exact H]. Qed.

Lemma protect_value_is_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l Hv. inversion Hv; subst; simpl.
  - constructor.
  - constructor. destruct kappa as [r ir]. destruct r, ir, l; simpl in *; assumption.
  - constructor; assumption.
  - constructor. destruct kappa as [r ir]. destruct r, ir, l; simpl in *; assumption.
  - constructor. destruct kappa as [r ir]. destruct r, ir, l; simpl in *; assumption.
Qed.

Lemma value_big_step : forall v, value v -> big_step v v.
Proof.
  intros v Hv. induction Hv.
  - constructor.
  - constructor. assumption.
  - eapply B_Pair; eassumption.
  - eapply B_Inl. exact IHHv.
  - eapply B_Inr. exact IHHv.
Qed.

Lemma big_step_evaluates : forall t v,
  big_step t v -> evaluates t v.
Proof.
  intros t v H. induction H.
  - split; [apply multi_refl | constructor].
  - split; [apply multi_refl | constructor; assumption].
  - destruct IHbig_step1 as [Hf Hfunval]. destruct IHbig_step2 as [Ha Haval].
    destruct IHbig_step3 as [Hb Hwv].
    assert (Hfctx : tm_app f a r -->* tm_app (tm_abs A body k) a r).
    { apply multi_app_left. exact Hf. }
    assert (Hactx : tm_app (tm_abs A body k) a r -->*
        tm_app (tm_abs A body k) v r).
    { apply multi_app_right; [exact Hfunval | exact Ha]. }
    assert (Hbeta : tm_app (tm_abs A body k) v r -->*
        tm_protect k.(indirect_reader) (open body v)).
    { eapply multi_step.
      - apply ST_AppAbs; assumption.
      - constructor. }
    assert (Hbody : tm_protect k.(indirect_reader) (open body v) -->*
        tm_protect k.(indirect_reader) w).
    { apply multi_protect. exact Hb. }
    assert (Hprotect : tm_protect k.(indirect_reader) w -->*
        protect_value w k.(indirect_reader)).
    { eapply multi_step; [apply ST_ProtectValue; assumption | constructor]. }
    split.
    + eapply multi_trans; [exact Hfctx |]. eapply multi_trans; [exact Hactx |].
      eapply multi_trans; [exact Hbeta |]. eapply multi_trans; eassumption.
    + eapply protect_value_is_value; assumption.
  - destruct IHbig_step1 as [Ha Hva]. destruct IHbig_step2 as [Hb Hvb].
    assert (Ha' : tm_pair a b k -->* tm_pair v w k).
    { eapply multi_trans.
      - apply multi_pair_left. exact Ha.
      - apply multi_pair_right; assumption. }
    split; [exact Ha' | constructor; assumption].
  - destruct IHbig_step as [Ht Hpairval]. inversion Hpairval; subst.
    assert (Hctx : tm_fst t r -->* tm_fst (tm_pair a b k) r).
    { apply multi_fst. exact Ht. }
    assert (Hred : tm_fst (tm_pair a b k) r -->* tm_protect k.(indirect_reader) a).
    { eapply multi_step; [apply ST_FstPair; assumption | constructor]. }
    assert (Hpr : tm_protect k.(indirect_reader) a -->* protect_value a k.(indirect_reader)).
    { eapply multi_step; [apply ST_ProtectValue; assumption | constructor]. }
    split; [eapply multi_trans; [exact Hctx | eapply multi_trans; eassumption] |].
    eapply protect_value_is_value; eassumption.
  - destruct IHbig_step as [Ht Hpairval]. inversion Hpairval; subst.
    assert (Hctx : tm_snd t r -->* tm_snd (tm_pair a b k) r).
    { apply multi_snd. exact Ht. }
    assert (Hred : tm_snd (tm_pair a b k) r -->* tm_protect k.(indirect_reader) b).
    { eapply multi_step; [apply ST_SndPair; assumption | constructor]. }
    assert (Hpr : tm_protect k.(indirect_reader) b -->* protect_value b k.(indirect_reader)).
    { eapply multi_step; [apply ST_ProtectValue; assumption | constructor]. }
    split; [eapply multi_trans; [exact Hctx | eapply multi_trans; eassumption] |].
    eapply protect_value_is_value; eassumption.
  - destruct IHbig_step as [Ht Hv].
    assert (Hctx : tm_inl t k -->* tm_inl v k).
    { apply multi_inl. exact Ht. }
    split; [exact Hctx | constructor; assumption].
  - destruct IHbig_step as [Ht Hv].
    assert (Hctx : tm_inr t k -->* tm_inr v k).
    { apply multi_inr. exact Ht. }
    split; [exact Hctx | constructor; assumption].
  - destruct IHbig_step1 as [Ht Hsumval]. inversion Hsumval; subst.
    destruct IHbig_step2 as [Hb Hwv].
    assert (Hcase : tm_case t b1 b2 r -->* tm_case (tm_inl v k) b1 b2 r).
    { apply multi_case_scrutinee. exact Ht. }
    assert (Hred : tm_case (tm_inl v k) b1 b2 r -->*
        tm_protect k.(indirect_reader) (open b1 v)).
    { eapply multi_step; [apply ST_CaseLeft; assumption | constructor]. }
    assert (Hbody : tm_protect k.(indirect_reader) (open b1 v) -->*
        tm_protect k.(indirect_reader) w).
    { apply multi_protect. exact Hb. }
    assert (Hpr : tm_protect k.(indirect_reader) w -->* protect_value w k.(indirect_reader)).
    { eapply multi_step; [apply ST_ProtectValue; assumption | constructor]. }
    split; [eapply multi_trans; [exact Hcase | eapply multi_trans; [exact Hred | eapply multi_trans; eassumption]] |].
    eapply protect_value_is_value; eassumption.
  - destruct IHbig_step1 as [Ht Hsumval]. inversion Hsumval; subst.
    destruct IHbig_step2 as [Hb Hwv].
    assert (Hcase : tm_case t b1 b2 r -->* tm_case (tm_inr v k) b1 b2 r).
    { apply multi_case_scrutinee. exact Ht. }
    assert (Hred : tm_case (tm_inr v k) b1 b2 r -->*
        tm_protect k.(indirect_reader) (open b2 v)).
    { eapply multi_step; [apply ST_CaseRight; assumption | constructor]. }
    assert (Hbody : tm_protect k.(indirect_reader) (open b2 v) -->*
        tm_protect k.(indirect_reader) w).
    { apply multi_protect. exact Hb. }
    assert (Hpr : tm_protect k.(indirect_reader) w -->* protect_value w k.(indirect_reader)).
    { eapply multi_step; [apply ST_ProtectValue; assumption | constructor]. }
    split; [eapply multi_trans; [exact Hcase | eapply multi_trans; [exact Hred | eapply multi_trans; eassumption]] |].
    eapply protect_value_is_value; eassumption.
  - destruct IHbig_step as [Ht Hv].
    assert (Hctx : tm_protect l t -->* tm_protect l v).
    { apply multi_protect. exact Ht. }
    assert (Hpr : tm_protect l v -->* protect_value v l).
    { eapply multi_step; [apply ST_ProtectValue; assumption | constructor]. }
    split; [eapply multi_trans; eassumption |]. eapply protect_value_is_value; eassumption.
  - destruct IHbig_step1 as [Hc Hsumval]. inversion Hsumval; subst.
    destruct IHbig_step2 as [Hy Hwv].
    assert (Hctx : tm_if c yes no r -->* tm_if (tm_inl v k) yes no r).
    { apply multi_if_scrutinee. exact Hc. }
    assert (Hred : tm_if (tm_inl v k) yes no r -->* tm_protect k.(indirect_reader) yes).
    { eapply multi_step; [apply ST_IfTrue; assumption | constructor]. }
    assert (Hbody : tm_protect k.(indirect_reader) yes -->*
        tm_protect k.(indirect_reader) result).
    { apply multi_protect. exact Hy. }
    assert (Hpr : tm_protect k.(indirect_reader) result -->*
        protect_value result k.(indirect_reader)).
    { eapply multi_step; [apply ST_ProtectValue; assumption | constructor]. }
    split; [eapply multi_trans; [exact Hctx | eapply multi_trans; [exact Hred | eapply multi_trans; eassumption]] |].
    eapply protect_value_is_value; eassumption.
  - destruct IHbig_step1 as [Hc Hsumval]. inversion Hsumval; subst.
    destruct IHbig_step2 as [Hn Hwv].
    assert (Hctx : tm_if c yes no r -->* tm_if (tm_inr v k) yes no r).
    { apply multi_if_scrutinee. exact Hc. }
    assert (Hred : tm_if (tm_inr v k) yes no r -->* tm_protect k.(indirect_reader) no).
    { eapply multi_step; [apply ST_IfFalse; assumption | constructor]. }
    assert (Hbody : tm_protect k.(indirect_reader) no -->*
        tm_protect k.(indirect_reader) result).
    { apply multi_protect. exact Hn. }
    assert (Hpr : tm_protect k.(indirect_reader) result -->*
        protect_value result k.(indirect_reader)).
    { eapply multi_step; [apply ST_ProtectValue; assumption | constructor]. }
    split; [eapply multi_trans; [exact Hctx | eapply multi_trans; [exact Hred | eapply multi_trans; eassumption]] |].
    eapply protect_value_is_value; eassumption.
Qed.

Lemma big_step_value_inv : forall v w,
  value v -> big_step v w -> v = w.
Proof.
  intros v w Hv. revert w. induction Hv; intros w Hb; inversion Hb; subst.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + eapply IHHv1; eauto.
    + eapply IHHv2; eauto.
  - f_equal. eapply IHHv; eauto.
  - f_equal. eapply IHHv; eauto.
Qed.

Lemma step_big_step_back : forall t t' v,
  step t t' -> big_step t' v -> big_step t v.
Proof.
  intros t t' v Hstep. revert v. induction Hstep; intros out Hb.
  all: try match goal with
       | Hv : value ?val, Htarget : big_step (protect_value ?val ?lbl) ?out |- _ =>
           assert (protect_value val lbl = out) as E
             by (eapply big_step_value_inv; [apply protect_value_is_value; exact Hv | exact Htarget]);
           rewrite <- E; apply B_Protect; apply value_big_step; exact Hv
       end.
  all: inversion Hb; subst; eauto using big_step, value_big_step.
Qed.

Lemma evaluates_big_step : forall t v,
  evaluates t v -> big_step t v.
Proof.
  intros t v [Hmulti Hv]. induction Hmulti.
  - subst. eapply value_big_step; eassumption.
  - eapply step_big_step_back; eauto.
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
  | tm_if c yes no r => tm_if (instantiate rho c) (instantiate rho yes) (instantiate rho no) r
  end.

Definition substitution_update (rho : term_substitution) (x : atom) (u : tm)
    : term_substitution := fun y => if Nat.eqb x y then u else rho y.

Lemma instantiate_open_rec : forall rho,
  (forall x, locally_closed (rho x)) -> forall t k u,
  instantiate rho (open_rec k u t) =
  open_rec k (instantiate rho u) (instantiate rho t).
Proof.
  intros rho Hlc t. induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - unfold locally_closed in Hlc. simpl. symmetry. apply open_rec_lc_at with (d := 0).
    + apply Hlc.
    + lia.
  - reflexivity.
  - f_equal. apply IHt.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, (IHt2 (S k) u), (IHt3 (S k) u). reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma instantiate_open : forall rho,
  (forall x, locally_closed (rho x)) -> forall body u,
  instantiate rho (open body u) = open (instantiate rho body) (instantiate rho u).
Proof. intros rho Hlc body u. unfold open. apply instantiate_open_rec; assumption. Qed.

Lemma not_in_app_inv : forall (A : Type) (x : A) l1 l2,
  ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof. intros A x l1 l2 H. split; intro Hin; apply H; apply in_or_app; tauto. Qed.

Lemma instantiate_update_irrelevant : forall rho x u t,
  ~ In x (fv t) ->
  instantiate (substitution_update rho x u) t = instantiate rho t.
Proof.
  intros rho x u t. induction t; intros Hfresh; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold substitution_update. rewrite E. reflexivity.
  - reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - apply not_in_app_inv in Hfresh as [H1 H2].
    rewrite (IHt1 H1), (IHt2 H2). reflexivity.
  - apply not_in_app_inv in Hfresh as [H1 H2].
    rewrite (IHt1 H1), (IHt2 H2). reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - apply not_in_app_inv in Hfresh as [H0 Hrest].
    apply not_in_app_inv in Hrest as [H1 H2].
    rewrite (IHt1 H0), (IHt2 H1), (IHt3 H2). reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - apply not_in_app_inv in Hfresh as [H0 Hrest].
    apply not_in_app_inv in Hrest as [H1 H2].
    rewrite (IHt1 H0), (IHt2 H1), (IHt3 H2). reflexivity.
Qed.

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

Lemma erase_protect_value : forall v l,
  erase_security (protect_value v l) = erase_security v.
Proof.
  intros v l. destruct v; simpl; try reflexivity;
    destruct s as [r ir]; destruct r, ir, l; reflexivity.
Qed.

(* The value relation observes a type only when its indirect-reader level is
   visible at Low.  In the arrow case it is closed under applying related
   arguments; this is the function clause needed by the fundamental theorem. *)
Definition flows_to_dec (l1 l2 : label) : {flows_to l1 l2} + {~ flows_to l1 l2}.
Proof. destruct l1, l2; simpl; intuition. Defined.

Fixpoint value_rel (T : ty) (v1 v2 : tm) : Prop :=
  if flows_to_dec (security_of T).(indirect_reader) Low then
    match T with
    | Ty_Unit _ => exists k1 k2, v1 = tm_unit k1 /\ v2 = tm_unit k2
    | Ty_Sum A B _ =>
        (exists w1 w2 k1 k2, v1 = tm_inl w1 k1 /\ v2 = tm_inl w2 k2 /\
                              security_le k1 (security_of T) /\
                              security_le k2 (security_of T) /\ value_rel A w1 w2) \/
        (exists w1 w2 k1 k2, v1 = tm_inr w1 k1 /\ v2 = tm_inr w2 k2 /\
                              security_le k1 (security_of T) /\
                              security_le k2 (security_of T) /\ value_rel B w1 w2)
    | Ty_Prod A B _ =>
        exists a1 a2 b1 b2 k1 k2,
          v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
          security_le k1 (security_of T) /\ security_le k2 (security_of T) /\
          value_rel A a1 a2 /\ value_rel B b1 b2
    | Ty_Arrow A B k =>
        exists A1 b1 k1 A2 b2 k2,
          v1 = tm_abs A1 b1 k1 /\ v2 = tm_abs A2 b2 k2 /\
          security_le k1 k /\ security_le k2 k /\
          (forall a1 a2 w1 w2 r,
            value a1 -> value a2 ->
            value_rel A a1 a2 ->
            flows_to k.(reader) r ->
            evaluates (tm_app v1 a1 r) w1 ->
            evaluates (tm_app v2 a2 r) w2 ->
            value_rel B w1 w2)
    end
  else True.

Definition term_rel (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, evaluates t1 v1 -> evaluates t2 v2 -> value_rel T v1 v2.

Definition substitution_rel (Gamma : context)
    (rho1 rho2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    term_rel T (rho1 x) (rho2 x).

Lemma no_flow_forces_low_target : forall l1 l2,
  ~ flows_to l1 l2 -> l1 = High /\ l2 = Low.
Proof. destruct l1, l2; simpl; intuition discriminate. Qed.

Lemma hidden_type_rel : forall T v1 v2,
  ~ flows_to (security_of T).(indirect_reader) Low -> value_rel T v1 v2.
Proof.
  intros T v1 v2 Hhidden. destruct T; simpl in *;
    destruct s as [r ir]; destruct r, ir; simpl in *; try contradiction; exact I.
Qed.

Lemma value_rel_protected : forall T v1 v2 l,
  value_rel T v1 v2 ->
  value_rel (ty_protect l T) (protect_value v1 l) (protect_value v2 l).
Proof.
  intros T v1 v2 l Hrel. destruct l.
  - rewrite ty_protect_low, !protect_value_low. exact Hrel.
  - eapply hidden_type_rel. destruct T; simpl; destruct s as [r ir];
      destruct r, ir; simpl; tauto.
Qed.

Lemma hidden_terms_related : forall T t1 t2,
  ~ flows_to (security_of T).(indirect_reader) Low -> term_rel T t1 t2.
Proof.
  intros T t1 t2 Hhidden v1 v2 _ _. eapply hidden_type_rel; eauto.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv; simpl; try exact I; try split; assumption.
Qed.

Lemma value_rel_term_rel : forall T v1 v2,
  value v1 -> value v2 -> value_rel T v1 v2 -> term_rel T v1 v2.
Proof.
  intros T v1 v2 Hv1 Hv2 Hrel w1 w2 [M1 V1] [M2 V2].
  assert (w1 = v1) by (eapply value_multi_inv; eassumption).
  assert (w2 = v2) by (eapply value_multi_inv; eassumption).
  subst. exact Hrel.
Qed.

Definition substitution_closed (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Lemma substitution_closed_update : forall rho x a,
  substitution_closed rho -> value a ->
  substitution_closed (substitution_update rho x a).
Proof.
  intros rho x a Hclosed Hva y. unfold substitution_update.
  destruct (Nat.eqb x y); [apply value_locally_closed | apply Hclosed].
  all: assumption.
Qed.

Lemma has_type_locally_closed : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty; simpl; try exact I; try tauto.
  - destruct (fresh_atom L) as [x Hx].
    specialize (H2 x Hx). eapply lc_at_open_inv; exact H2.
  - split; assumption.
  - split; assumption.
  - split; [eauto |]. split.
    + destruct (fresh_atom L) as [x Hx].
      specialize (H1 x Hx). eapply lc_at_open_inv; exact H1.
    + destruct (fresh_atom L) as [x Hx].
      specialize (H3 x Hx). eapply lc_at_open_inv; exact H3.
  - repeat split; assumption.
Qed.

Lemma substitution_rel_update : forall Gamma rho1 rho2 x T a1 a2,
  substitution_rel Gamma rho1 rho2 ->
  value_rel T a1 a2 -> value a1 -> value a2 ->
  substitution_rel (update Gamma x T)
    (substitution_update rho1 x a1) (substitution_update rho2 x a2).
Proof.
  intros Gamma rho1 rho2 x T a1 a2 Hrel Hval Hva1 Hva2 y U Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst U.
    unfold substitution_update. rewrite Nat.eqb_refl.
    eapply value_rel_term_rel; eassumption.
  - assert (Hbase : lookup_context y Gamma = Some U).
    { exact Hlookup. }
    specialize (Hrel y U Hbase).
    unfold substitution_update. rewrite Nat.eqb_sym, E. exact Hrel.
Qed.

Lemma value_rel_ground_erases : forall T v1 v2 kappa,
  ground T -> transparent_at kappa T ->
  flows_to kappa.(indirect_reader) Low ->
  value_rel T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  induction T; intros v1 v2 kappa Hground Htrans Hlow Hrel;
    simpl in *.
  - unfold value_rel in Hrel. destruct (flows_to_dec (indirect_reader s) Low).
    + destruct Hrel as [k1 [k2 [-> ->]]]. reflexivity.
    + exfalso. apply n. eapply flows_to_trans.
      * exact (proj2 (proj1 Htrans)).
      * exact Hlow.
  - destruct Hground as [HA HB]. destruct Htrans as [Hroot [HtransA HtransB]].
    unfold value_rel in Hrel. simpl in Hrel.
    destruct (flows_to_dec (indirect_reader s) Low) as [Hobs | Hnot].
    + destruct Hrel as [Hleft | Hright].
      * destruct Hleft as [w1 [w2 [k1 [k2 Hleft]]]].
        destruct Hleft as [E1 [E2 [_ [_ Hchild]]]]. subst v1 v2.
        simpl. f_equal. eapply IHT1; eauto.
      * destruct Hright as [w1 [w2 [k1 [k2 Hright]]]].
        destruct Hright as [E1 [E2 [_ [_ Hchild]]]]. subst v1 v2.
        simpl. f_equal. eapply IHT2; eauto.
    + exfalso. apply Hnot. eapply flows_to_trans.
      * exact (proj2 Hroot).
      * exact Hlow.
  - destruct Hground as [HA HB]. destruct Htrans as [Hroot [HtransA HtransB]].
    unfold value_rel in Hrel. simpl in Hrel.
    destruct (flows_to_dec (indirect_reader s) Low) as [Hobs | Hnot].
    + destruct Hrel as [a1 [a2 [b1 [b2 [k1 [k2 Hprod]]]]]].
      destruct Hprod as [E1 [E2 [_ [_ [Hra Hrb]]]]]. subst v1 v2.
      simpl. f_equal.
      * eapply IHT1; eauto.
      * eapply IHT2; eauto.
    + exfalso. apply Hnot. eapply flows_to_trans.
      * exact (proj2 Hroot).
      * exact Hlow.
  - contradiction.
Qed.

Lemma value_rel_subtype : forall T U v1 v2,
  subtype T U -> value_rel T v1 v2 -> value_rel U v1 v2.
Proof.
  intros T U v1 v2 Hsub. revert v1 v2. induction Hsub; intros v1 v2 Hrel.
  - destruct (flows_to_dec kappa2.(indirect_reader) Low) as [Hvis | Hhidden] eqn:Htarget_dec.
    + assert (Hsrc : flows_to kappa1.(indirect_reader) Low).
      { exact (flows_to_trans _ _ _ (proj2 H1) Hvis). }
      unfold value_rel in Hrel |- *. cbn [security_of] in Hrel |- *.
      destruct (flows_to_dec (indirect_reader kappa1) Low) as [Hsv | Hsn] eqn:Hsd; [|contradiction].
      destruct (flows_to_dec (indirect_reader kappa2) Low) as [Htv | Htn] eqn:Htd; [|contradiction].
      exact Hrel.
    + eapply hidden_type_rel. exact Hhidden.
  - destruct (flows_to_dec kappa2.(indirect_reader) Low) as [Hvis | Hhidden] eqn:Htarget_dec.
    + assert (Hsrc : flows_to kappa1.(indirect_reader) Low).
      { match goal with Hle : security_le _ _ |- _ =>
          exact (flows_to_trans _ _ _ (proj2 Hle) Hvis) end. }
      unfold value_rel in Hrel |- *. cbn [security_of] in Hrel |- *.
      destruct (flows_to_dec (indirect_reader kappa1) Low) as [Hsv | Hsn] eqn:Hsd; [|contradiction].
      destruct (flows_to_dec (indirect_reader kappa2) Low) as [Htv | Htn] eqn:Htd; [|contradiction].
      destruct Hrel as [Hleft | Hright].
      * destruct Hleft as [a [b [ka [kb [E1 [E2 [Hka [Hkb Hab]]]]]]]].
        subst v1 v2. left. exists a, b, ka, kb.
        split; [reflexivity |]. split; [reflexivity |].
        split; [eapply security_le_trans; eassumption |].
        split; [eapply security_le_trans; eassumption |].
        eapply IHHsub1; eassumption.
      * destruct Hright as [a [b [ka [kb [E1 [E2 [Hka [Hkb Hab]]]]]]]].
        subst v1 v2. right. exists a, b, ka, kb.
        split; [reflexivity |]. split; [reflexivity |].
        split; [eapply security_le_trans; eassumption |].
        split; [eapply security_le_trans; eassumption |].
        eapply IHHsub2; eassumption.
    + eapply hidden_type_rel. exact Hhidden.
  - destruct (flows_to_dec kappa2.(indirect_reader) Low) as [Hvis | Hhidden] eqn:Htarget_dec.
    + assert (Hsrc : flows_to kappa1.(indirect_reader) Low).
      { match goal with Hle : security_le _ _ |- _ =>
          exact (flows_to_trans _ _ _ (proj2 Hle) Hvis) end. }
      unfold value_rel in Hrel |- *. cbn [security_of] in Hrel |- *.
      destruct (flows_to_dec (indirect_reader kappa1) Low) as [Hsv | Hsn] eqn:Hsd; [|contradiction].
      destruct (flows_to_dec (indirect_reader kappa2) Low) as [Htv | Htn] eqn:Htd; [|contradiction].
      destruct Hrel as [a1 [a2 [b1 [b2 [ka [kb Hprod]]]]]].
      destruct Hprod as [E1 [E2 [Hka [Hkb [Ha Hb]]]]].
      subst v1 v2. exists a1, a2, b1, b2, ka, kb.
      split; [reflexivity |]. split; [reflexivity |].
      split; [eapply security_le_trans; eassumption |].
      split; [eapply security_le_trans; eassumption |]. split.
      * eapply IHHsub1; eassumption.
      * eapply IHHsub2; eassumption.
    + eapply hidden_type_rel. exact Hhidden.
  - destruct (flows_to_dec kappa2.(indirect_reader) Low) as [Hvis | Hhidden] eqn:Htarget_dec.
    + assert (Hsrc : flows_to kappa1.(indirect_reader) Low).
      { match goal with Hle : security_le _ _ |- _ =>
          exact (flows_to_trans _ _ _ (proj2 Hle) Hvis) end. }
      unfold value_rel in Hrel |- *. cbn [security_of] in Hrel |- *.
      destruct (flows_to_dec (indirect_reader kappa1) Low) as [Hsv | Hsn] eqn:Hsd; [|contradiction].
      destruct (flows_to_dec (indirect_reader kappa2) Low) as [Htv | Htn] eqn:Htd; [|contradiction].
      destruct Hrel as [A1 [b1 [k1 [A2 [b2 [k2 [Heq1 [Heq2 [Hle1 [Hle2 Hfun]]]]]]]]]].
      subst v1 v2.
      exists A1, b1, k1, A2, b2, k2.
      split; [reflexivity |]. split; [reflexivity |].
      split; [eapply security_le_trans; eassumption |].
      split; [eapply security_le_trans; eassumption |].
      intros a1 a2 w1 w2 r Hva1 Hva2 Harg Hflow E1 E2.
        assert (Hflow1 : flows_to (reader kappa1) r).
        { eapply flows_to_trans; [exact (proj1 H1) | exact Hflow]. }
        apply IHHsub2.
        eapply Hfun; [exact Hva1 | exact Hva2 | eapply IHHsub1; eassumption |
                       exact Hflow1 | exact E1 | exact E2].
    + eapply hidden_type_rel. exact Hhidden.
  - eapply IHHsub2. eapply IHHsub1. exact Hrel.
Qed.

Lemma value_rel_unit_intro : forall k v1 v2,
  value_rel (Ty_Unit k) (tm_unit v1) (tm_unit v2).
Proof.
  intros. unfold value_rel. cbn [security_of].
  destruct (flows_to_dec (indirect_reader k) Low) eqn:E.
  - exists v1, v2. split; reflexivity.
  - exact I.
Qed.

Lemma value_rel_inl_intro : forall A B k v1 v2 k1 k2,
  security_le k1 k -> security_le k2 k ->
  value_rel A v1 v2 ->
  value_rel (Ty_Sum A B k) (tm_inl v1 k1) (tm_inl v2 k2).
Proof.
  intros A B k v1 v2 k1 k2 Hle1 Hle2 Hrel. unfold value_rel. cbn [security_of].
  destruct (flows_to_dec (indirect_reader k) Low) eqn:E.
  - left. exists v1, v2, k1, k2.
    split; [reflexivity |]. split; [reflexivity |].
    split; [exact Hle1 |]. split; [exact Hle2 | exact Hrel].
  - exact I.
Qed.

Lemma value_rel_inr_intro : forall A B k v1 v2 k1 k2,
  security_le k1 k -> security_le k2 k ->
  value_rel B v1 v2 ->
  value_rel (Ty_Sum A B k) (tm_inr v1 k1) (tm_inr v2 k2).
Proof.
  intros A B k v1 v2 k1 k2 Hle1 Hle2 Hrel. unfold value_rel. cbn [security_of].
  destruct (flows_to_dec (indirect_reader k) Low) eqn:E.
  - right. exists v1, v2, k1, k2.
    split; [reflexivity |]. split; [reflexivity |].
    split; [exact Hle1 |]. split; [exact Hle2 | exact Hrel].
  - exact I.
Qed.

Lemma value_rel_pair_intro : forall A B k a1 a2 b1 b2 k1 k2,
  security_le k1 k -> security_le k2 k ->
  value_rel A a1 a2 -> value_rel B b1 b2 ->
  value_rel (Ty_Prod A B k)
    (tm_pair a1 b1 k1) (tm_pair a2 b2 k2).
Proof.
  intros A B k a1 a2 b1 b2 k1 k2 Hle1 Hle2 Hra Hrb. unfold value_rel. cbn [security_of].
  destruct (flows_to_dec (indirect_reader k) Low) eqn:E.
  - exists a1, a2, b1, b2, k1, k2.
    split; [reflexivity |]. split; [reflexivity |].
    split; [exact Hle1 |]. split; [exact Hle2 |]. split; assumption.
  - exact I.
Qed.

Lemma value_rel_sum_inv : forall A B k v1 v2,
  flows_to (indirect_reader k) Low ->
  value_rel (Ty_Sum A B k) v1 v2 ->
  (exists a1 a2 k1 k2,
     v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\
     security_le k1 k /\ security_le k2 k /\ value_rel A a1 a2) \/
  (exists a1 a2 k1 k2,
     v1 = tm_inr a1 k1 /\ v2 = tm_inr a2 k2 /\
     security_le k1 k /\ security_le k2 k /\ value_rel B a1 a2).
Proof.
  intros A B k v1 v2 Hlow Hrel. unfold value_rel in Hrel. cbn [security_of] in Hrel.
  destruct (flows_to_dec (indirect_reader k) Low) as [Hyes | Hno] eqn:E.
  - exact Hrel.
  - contradiction.
Qed.

Lemma value_rel_prod_inv : forall A B k v1 v2,
  flows_to (indirect_reader k) Low ->
  value_rel (Ty_Prod A B k) v1 v2 ->
  exists a1 a2 b1 b2 k1 k2,
    v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
    security_le k1 k /\ security_le k2 k /\
    value_rel A a1 a2 /\ value_rel B b1 b2.
Proof.
  intros A B k v1 v2 Hlow Hrel. unfold value_rel in Hrel.
  cbn [security_of] in Hrel.
  destruct (flows_to_dec (indirect_reader k) Low) as [Hyes | Hno] eqn:E.
  - exact Hrel.
  - contradiction.
Qed.

Lemma related_ground_terms_same_result : forall T t1 t2,
  ground T -> transparent T ->
  flows_to (security_of T).(indirect_reader) Low ->
  term_rel T t1 t2 -> same_result t1 t2.
Proof.
  intros T t1 t2 Hg Htrans Hlow Hrel.
  unfold same_result. intros v1 v2 E1 E2.
  eapply value_rel_ground_erases with (kappa := security_of T); eauto.
Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho1 rho2,
    substitution_rel Gamma rho1 rho2 ->
    substitution_closed rho1 -> substitution_closed rho2 ->
    forall v1 v2,
      big_step (instantiate rho1 t) v1 ->
      big_step (instantiate rho2 t) v2 ->
      value_rel T v1 v2.
Proof.
  intros Gamma t T Hty. induction Hty;
    intros rho1 rho2 Henv Hclosed1 Hclosed2 v1 v2 E1 E2; simpl in *.
  - specialize (Henv x T H). unfold term_rel in Henv.
    eapply Henv; [eapply big_step_evaluates; exact E1 | eapply big_step_evaluates; exact E2].
  - inversion E1; inversion E2; subst. apply value_rel_unit_intro.
  - inversion E1; subst. inversion E2; subst.
    unfold value_rel. cbn [security_of].
    destruct (flows_to_dec (indirect_reader kappa) Low) as [Hvisible | Hhidden] eqn:Hdec.
    + exists T1, (instantiate rho1 body), kappa,
        T1, (instantiate rho2 body), kappa.
      split; [reflexivity |]. split; [reflexivity |].
      split; [apply security_le_refl |]. split; [apply security_le_refl |].
      intros a1 a2 w1 w2 r Hva1 Hva2 Harg Hflow Heval1 Heval2.
      destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
      apply not_in_app_inv in Hfresh as [HxL Hxfv].
      assert (Henv'1 : substitution_rel (update Gamma x T1)
          (substitution_update rho1 x a1) (substitution_update rho2 x a2)).
      { eapply substitution_rel_update; eassumption. }
      assert (Hclosed'1 : substitution_closed (substitution_update rho1 x a1)).
      { eapply substitution_closed_update; eassumption. }
      assert (Hclosed'2 : substitution_closed (substitution_update rho2 x a2)).
      { eapply substitution_closed_update; eassumption. }
      assert (Hopen1 : instantiate (substitution_update rho1 x a1)
          (open body (tm_fvar x)) = open (instantiate rho1 body) a1).
      { rewrite instantiate_open; [|exact Hclosed'1].
        rewrite (instantiate_update_irrelevant rho1 x a1 body Hxfv).
        unfold instantiate, substitution_update. rewrite Nat.eqb_refl. reflexivity. }
      assert (Hopen2 : instantiate (substitution_update rho2 x a2)
          (open body (tm_fvar x)) = open (instantiate rho2 body) a2).
      { rewrite instantiate_open; [|exact Hclosed'2].
        rewrite (instantiate_update_irrelevant rho2 x a2 body Hxfv).
        unfold instantiate, substitution_update. rewrite Nat.eqb_refl. reflexivity. }
      pose proof (evaluates_big_step _ _ Heval1) as Happ1.
      pose proof (evaluates_big_step _ _ Heval2) as Happ2.
      inversion Happ1; subst. inversion Happ2; subst.
      inversion H6; subst. inversion H10; subst.
      assert (v = a1) by (symmetry; eapply big_step_value_inv; eassumption). subst v.
      assert (v0 = a2) by (symmetry; eapply big_step_value_inv; eassumption). subst v0.
      destruct (indirect_reader k0) eqn:Hir; simpl in Hvisible; try contradiction.
      rewrite !protect_value_low.
      eapply (H2 x HxL (substitution_update rho1 x a1)
        (substitution_update rho2 x a2) Henv'1 Hclosed'1 Hclosed'2).
      * rewrite Hopen1. exact H12.
      * rewrite Hopen2. exact H16.
    + exact I.
  - inversion E1; subst. inversion E2; subst.
    pose proof (IHHty1 rho1 rho2 Henv Hclosed1 Hclosed2 _ _ H3 H5) as Hfr.
    pose proof (IHHty2 rho1 rho2 Henv Hclosed1 Hclosed2 _ _ H4 H8) as Har.
    destruct (indirect_reader kappa) eqn:Hir.
    +
      destruct Hfr as [A1 [b1 [k1 [A2 [b2 [k2 [Heq1 [Heq2 [Hle1 [Hle2 Hfun]]]]]]]]]].
      inversion Heq1; subst A1 b1 k1. inversion Heq2; subst A2 b2 k2.
      destruct Hle1 as [_ Hbound1]. destruct Hle2 as [_ Hbound2].
      rewrite Hir in Hbound1, Hbound2.
      destruct (indirect_reader k) eqn:Hik; simpl in Hbound1; try contradiction.
      destruct (indirect_reader k0) eqn:Hik0; simpl in Hbound2; try contradiction.
      assert (Hva : value v) by (destruct (big_step_evaluates _ _ H4) as [_ Hv]; exact Hv).
      assert (Hva0 : value v0) by (destruct (big_step_evaluates _ _ H8) as [_ Hv]; exact Hv).
      assert (Habs : value (tm_abs A body k))
        by (destruct (big_step_evaluates _ _ H3) as [_ Hv]; exact Hv).
      assert (Habs0 : value (tm_abs A0 body0 k0))
        by (destruct (big_step_evaluates _ _ H5) as [_ Hv]; exact Hv).
      assert (Happ1 : evaluates (tm_app (tm_abs A body k) v r)
          (protect_value w (indirect_reader k))).
      { apply big_step_evaluates. eapply B_App;
          [apply value_big_step; exact Habs | apply value_big_step; exact Hva | exact H6 | exact H7]. }
      assert (Happ2 : evaluates (tm_app (tm_abs A0 body0 k0) v0 r)
          (protect_value w0 (indirect_reader k0))).
      { apply big_step_evaluates. eapply B_App;
          [apply value_big_step; exact Habs0 | apply value_big_step; exact Hva0 | exact H10 | exact H11]. }
      rewrite Hik in Happ1. rewrite Hik0 in Happ2.
      rewrite !protect_value_low in Happ1, Happ2.
      rewrite ty_protect_low, !protect_value_low.
      eapply (Hfun v v0 w w0 r); [exact Hva | exact Hva0 | exact Har |
        exact H | exact Happ1 | exact Happ2].
    + eapply hidden_type_rel. destruct T2; simpl; destruct s as [rr ii];
        destruct rr, ii; simpl; tauto.
  - inversion E1; subst. inversion E2; subst.
    eapply value_rel_pair_intro; [apply security_le_refl | apply security_le_refl | |].
    + eapply IHHty1; eassumption.
    + eapply IHHty2; eassumption.
  - inversion E1; subst. inversion E2; subst.
    pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2 _ _ H2 H3) as Hprod.
    destruct (indirect_reader kappa) eqn:Hir.
    + assert (Hlow : flows_to (indirect_reader kappa) Low) by (rewrite Hir; apply flows_to_refl).
      cbn [flows_to_dec] in Hprod.
      destruct Hprod as [a1 [a2 [b1 [b2 [k1 [k2 Hpair]]]]]].
      destruct Hpair as [Eleft [Eright [Hbound1 [Hbound2 [Hra Hrb]]]]].
      inversion Eleft; inversion Eright; subst.
      destruct (indirect_reader k1) eqn:Hik.
      * destruct (indirect_reader k2) eqn:Hik0.
        -- rewrite !protect_value_low, ty_protect_low. exact Hra.
        -- destruct Hbound2 as [_ Hbad]. rewrite Hik0, Hir in Hbad. simpl in Hbad. contradiction.
      * destruct Hbound1 as [_ Hbad]. rewrite Hik, Hir in Hbad. simpl in Hbad. contradiction.
    + eapply hidden_type_rel. destruct T1; simpl; destruct s as [rr ii];
        destruct rr, ii; simpl; tauto.
  - inversion E1; subst. inversion E2; subst.
    pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2 _ _ H2 H3) as Hprod.
    destruct (indirect_reader kappa) eqn:Hir.
    + assert (Hlow : flows_to (indirect_reader kappa) Low) by (rewrite Hir; apply flows_to_refl).
      cbn [flows_to_dec] in Hprod.
      destruct Hprod as [a1 [a2 [b1 [b2 [k1 [k2 Hpair]]]]]].
      destruct Hpair as [Eleft [Eright [Hbound1 [Hbound2 [Hra Hrb]]]]].
      inversion Eleft; inversion Eright; subst.
      destruct (indirect_reader k1) eqn:Hik.
      * destruct (indirect_reader k2) eqn:Hik0.
        -- rewrite !protect_value_low, ty_protect_low. exact Hrb.
        -- destruct Hbound2 as [_ Hbad]. rewrite Hik0, Hir in Hbad. simpl in Hbad. contradiction.
      * destruct Hbound1 as [_ Hbad]. rewrite Hik, Hir in Hbad. simpl in Hbad. contradiction.
    + eapply hidden_type_rel. destruct T2; simpl; destruct s as [rr ii];
        destruct rr, ii; simpl; tauto.
  - inversion E1; subst. inversion E2; subst.
    eapply value_rel_inl_intro; [apply security_le_refl | apply security_le_refl |].
    eapply IHHty; eassumption.
  - inversion E1; subst. inversion E2; subst.
    eapply value_rel_inr_intro; [apply security_le_refl | apply security_le_refl |].
    eapply IHHty; eassumption.
  - destruct (indirect_reader kappa) eqn:Hir.
    + inversion E1; subst; inversion E2; subst.
      * pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2 _ _ H9 H12) as Hsum.
        cbn [flows_to_dec] in Hsum.
        destruct Hsum as [Hleft | Hright].
        2: { destruct Hright as [a1 [a2 [ka1 [ka2 [Heq1 [Heq2 _]]]]]].
             discriminate Heq1. }
        destruct Hleft as [a1 [a2 [ka1 [ka2 [Heq1 [Heq2 [Hbound1 [Hbound2 Hpayload]]]]]]]].
        inversion Heq1; inversion Heq2; subst.
        destruct (fresh_atom (L ++ fv body1)) as [x Hfresh].
        apply not_in_app_inv in Hfresh as [HxL Hxfv].
        assert (Henv' : substitution_rel (update Gamma x T1)
            (substitution_update rho1 x a1) (substitution_update rho2 x a2)).
        { eapply substitution_rel_update.
          - exact Henv.
          - exact Hpayload.
          - destruct (big_step_evaluates _ _ H9) as [_ Hv]. inversion Hv; assumption.
          - destruct (big_step_evaluates _ _ H12) as [_ Hv]. inversion Hv; assumption. }
        assert (Hclosed' : substitution_closed (substitution_update rho1 x a1)).
        { eapply substitution_closed_update; [exact Hclosed1 |].
          destruct (big_step_evaluates _ _ H9) as [_ Hv]. inversion Hv; assumption. }
        assert (Hclosed0' : substitution_closed (substitution_update rho2 x a2)).
        { eapply substitution_closed_update; [exact Hclosed2 |].
          destruct (big_step_evaluates _ _ H12) as [_ Hv]. inversion Hv; assumption. }
        assert (Hopen1 : instantiate (substitution_update rho1 x a1)
            (open body1 (tm_fvar x)) = open (instantiate rho1 body1) a1).
        { rewrite instantiate_open; [|exact Hclosed'].
          rewrite (instantiate_update_irrelevant rho1 x a1 body1 Hxfv).
          unfold instantiate, substitution_update. rewrite Nat.eqb_refl. reflexivity. }
        assert (Hopen2 : instantiate (substitution_update rho2 x a2)
            (open body1 (tm_fvar x)) = open (instantiate rho2 body1) a2).
        { rewrite instantiate_open; [|exact Hclosed0'].
          rewrite (instantiate_update_irrelevant rho2 x a2 body1 Hxfv).
          unfold instantiate, substitution_update. rewrite Nat.eqb_refl. reflexivity. }
        destruct (indirect_reader ka1) eqn:Hik.
        { destruct (indirect_reader ka2) eqn:Hik0.
          { rewrite !protect_value_low, ty_protect_low.
            eapply (H1 x HxL (substitution_update rho1 x a1)
              (substitution_update rho2 x a2) Henv' Hclosed' Hclosed0').
            - rewrite Hopen1. exact H11.
            - rewrite Hopen2. exact H14. }
          { destruct Hbound2 as [_ Hbad]. rewrite Hik0, Hir in Hbad. simpl in Hbad. contradiction. } }
        { destruct Hbound1 as [_ Hbad]. rewrite Hik, Hir in Hbad. simpl in Hbad. contradiction. }
      * pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2 _ _ H9 H12) as Hsum.
        cbn [flows_to_dec] in Hsum.
        destruct Hsum as [Hleft | Hright].
        { destruct Hleft as (a1 & a2 & ka1 & ka2 & Heq1 & Heq2 & _ & _ & _).
          discriminate Heq2. }
        { destruct Hright as (a1 & a2 & ka1 & ka2 & Heq1 & Heq2 & _ & _ & _).
          discriminate Heq1. }
      * pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2 _ _ H9 H12) as Hsum.
        cbn [flows_to_dec] in Hsum.
        destruct Hsum as [Hleft | Hright].
        { destruct Hleft as (a1 & a2 & ka1 & ka2 & Heq1 & Heq2 & _ & _ & _).
          discriminate Heq1. }
        { destruct Hright as (a1 & a2 & ka1 & ka2 & Heq1 & Heq2 & _ & _ & _).
          discriminate Heq2. }
      * pose proof (IHHty rho1 rho2 Henv Hclosed1 Hclosed2 _ _ H9 H12) as Hsum.
        cbn [flows_to_dec] in Hsum.
        destruct Hsum as [Hleft | Hright].
        1: { destruct Hleft as (a1 & a2 & ka1 & ka2 & Heq1 & Heq2 & _ & _ & _).
             discriminate Heq2. }
        destruct Hright as [a1 [a2 [ka1 [ka2 [Heq1 [Heq2 [Hbound1 [Hbound2 Hpayload]]]]]]]].
        inversion Heq1; inversion Heq2; subst.
        destruct (fresh_atom (L ++ fv body2)) as [x Hfresh].
        apply not_in_app_inv in Hfresh as [HxL Hxfv].
        assert (Henv' : substitution_rel (update Gamma x T2)
            (substitution_update rho1 x a1) (substitution_update rho2 x a2)).
        { eapply substitution_rel_update.
          - exact Henv.
          - exact Hpayload.
          - destruct (big_step_evaluates _ _ H9) as [_ Hv]. inversion Hv; assumption.
          - destruct (big_step_evaluates _ _ H12) as [_ Hv]. inversion Hv; assumption. }
        assert (Hclosed' : substitution_closed (substitution_update rho1 x a1)).
        { eapply substitution_closed_update; [exact Hclosed1 |].
          destruct (big_step_evaluates _ _ H9) as [_ Hv]. inversion Hv; assumption. }
        assert (Hclosed0' : substitution_closed (substitution_update rho2 x a2)).
        { eapply substitution_closed_update; [exact Hclosed2 |].
          destruct (big_step_evaluates _ _ H12) as [_ Hv]. inversion Hv; assumption. }
        assert (Hopen1 : instantiate (substitution_update rho1 x a1)
            (open body2 (tm_fvar x)) = open (instantiate rho1 body2) a1).
        { rewrite instantiate_open; [|exact Hclosed'].
          rewrite (instantiate_update_irrelevant rho1 x a1 body2 Hxfv).
          unfold instantiate, substitution_update. rewrite Nat.eqb_refl. reflexivity. }
        assert (Hopen2 : instantiate (substitution_update rho2 x a2)
            (open body2 (tm_fvar x)) = open (instantiate rho2 body2) a2).
        { rewrite instantiate_open; [|exact Hclosed0'].
          rewrite (instantiate_update_irrelevant rho2 x a2 body2 Hxfv).
          unfold instantiate, substitution_update. rewrite Nat.eqb_refl. reflexivity. }
        destruct (indirect_reader ka1) eqn:Hik.
        { destruct (indirect_reader ka2) eqn:Hik0.
          { rewrite !protect_value_low, ty_protect_low.
            eapply (H3 x HxL (substitution_update rho1 x a1)
              (substitution_update rho2 x a2) Henv' Hclosed' Hclosed0').
            - rewrite Hopen1. exact H11.
            - rewrite Hopen2. exact H14. }
          { destruct Hbound2 as [_ Hbad]. rewrite Hik0, Hir in Hbad. simpl in Hbad. contradiction. } }
        { destruct Hbound1 as [_ Hbad]. rewrite Hik, Hir in Hbad. simpl in Hbad. contradiction. }
    + eapply hidden_type_rel. destruct T; simpl; destruct s as [rr ii];
        destruct rr, ii; simpl; tauto.
  - inversion E1; subst. inversion E2; subst.
    eapply value_rel_protected. eapply IHHty; eassumption.
  - eapply value_rel_subtype; [exact H |]. eapply IHHty; eassumption.
  - destruct (indirect_reader k) eqn:Hir.
    + inversion E1; subst; inversion E2; subst.
      * pose proof (IHHty1 rho1 rho2 Henv Hclosed1 Hclosed2 _ _ H5 H8) as Hsum.
        cbn [flows_to_dec] in Hsum.
        destruct Hsum as [Hleft | Hright].
        2: { destruct Hright as (a1 & a2 & ka1 & ka2 & Heq1 & _ & _ & _ & _).
             discriminate Heq1. }
        destruct Hleft as (a1 & a2 & ka1 & ka2 & Heq1 & Heq2 & Hbound1 & Hbound2 & Hunit).
        inversion Heq1; inversion Heq2; subst.
        destruct (indirect_reader ka1) eqn:Hik.
        { destruct (indirect_reader ka2) eqn:Hik0.
          { rewrite !protect_value_low, ty_protect_low.
            eapply IHHty2; eassumption. }
          { destruct Hbound2 as [_ Hbad]. rewrite Hik0, Hir in Hbad. simpl in Hbad. contradiction. } }
        { destruct Hbound1 as [_ Hbad]. rewrite Hik, Hir in Hbad. simpl in Hbad. contradiction. }
      * pose proof (IHHty1 rho1 rho2 Henv Hclosed1 Hclosed2 _ _ H5 H8) as Hsum.
        cbn [flows_to_dec] in Hsum.
        destruct Hsum as [Hleft | Hright].
        { destruct Hleft as (a1 & a2 & ka1 & ka2 & Heq1 & Heq2 & _ & _ & _).
          discriminate Heq2. }
        { destruct Hright as (a1 & a2 & ka1 & ka2 & Heq1 & Heq2 & _ & _ & _).
          discriminate Heq1. }
      * pose proof (IHHty1 rho1 rho2 Henv Hclosed1 Hclosed2 _ _ H5 H8) as Hsum.
        cbn [flows_to_dec] in Hsum.
        destruct Hsum as [Hleft | Hright].
        { destruct Hleft as (a1 & a2 & ka1 & ka2 & Heq1 & Heq2 & _ & _ & _).
          discriminate Heq1. }
        { destruct Hright as (a1 & a2 & ka1 & ka2 & Heq1 & Heq2 & _ & _ & _).
          discriminate Heq2. }
      * pose proof (IHHty1 rho1 rho2 Henv Hclosed1 Hclosed2 _ _ H5 H8) as Hsum.
        cbn [flows_to_dec] in Hsum.
        destruct Hsum as [Hleft | Hright].
        1: { destruct Hleft as (a1 & a2 & ka1 & ka2 & Heq1 & Heq2 & _ & _ & _).
             discriminate Heq1. }
        destruct Hright as (a1 & a2 & ka1 & ka2 & Heq1 & Heq2 & Hbound1 & Hbound2 & Hunit).
        inversion Heq1; inversion Heq2; subst.
        destruct (indirect_reader ka1) eqn:Hik.
        { destruct (indirect_reader ka2) eqn:Hik0.
          { rewrite !protect_value_low, ty_protect_low.
            eapply IHHty3; eassumption. }
          { destruct Hbound2 as [_ Hbad]. rewrite Hik0, Hir in Hbad. simpl in Hbad. contradiction. } }
        { destruct Hbound1 as [_ Hbad]. rewrite Hik, Hir in Hbad. simpl in Hbad. contradiction. }
    + eapply hidden_type_rel. destruct T; simpl; destruct s as [rr ii];
        destruct rr, ii; simpl; tauto.
Qed.

Lemma instantiate_identity : forall t,
  instantiate (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
    try rewrite IHt3; reflexivity.
Qed.

Lemma substitution_closed_update_lc : forall rho x u,
  substitution_closed rho -> locally_closed u ->
  substitution_closed (substitution_update rho x u).
Proof.
  intros rho x u Hclosed Hu y. unfold substitution_update.
  destruct (Nat.eqb x y); [exact Hu | apply Hclosed].
Qed.

Lemma not_in_app3_inv : forall (A : Type) (x : A) a b c,
  ~ In x (a ++ b ++ c) -> ~ In x a /\ ~ In x b /\ ~ In x c.
Proof.
  intros A x a b c H. apply not_in_app_inv in H as [Ha Hbc].
  apply not_in_app_inv in Hbc as [Hb Hc]. tauto.
Qed.

Lemma instantiate_plug_update_id : forall C x u,
  ~ In x (fv (plug C (tm_unit public))) ->
  instantiate (substitution_update (fun y => tm_fvar y) x u)
    (plug C (tm_fvar x)) = plug C u.
Proof.
  induction C; intros x u Hfresh; simpl in *.
  - unfold instantiate, substitution_update. rewrite Nat.eqb_refl. reflexivity.
  - f_equal. eapply IHC. exact Hfresh.
  - apply not_in_app_inv in Hfresh as [Hctx Hstatic].
    simpl. rewrite (IHC x u Hctx).
    rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t Hstatic).
    rewrite instantiate_identity. reflexivity.
  - apply not_in_app_inv in Hfresh as [Hstatic Hctx].
    simpl. rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t Hstatic).
    rewrite instantiate_identity. rewrite (IHC x u Hctx). reflexivity.
  - apply not_in_app_inv in Hfresh as [Hctx Hstatic].
    simpl. rewrite (IHC x u Hctx).
    rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t Hstatic).
    rewrite instantiate_identity. reflexivity.
  - apply not_in_app_inv in Hfresh as [Hstatic Hctx].
    simpl. rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t Hstatic).
    rewrite instantiate_identity. rewrite (IHC x u Hctx). reflexivity.
  - f_equal. eapply IHC. exact Hfresh.
  - f_equal. eapply IHC. exact Hfresh.
  - f_equal. eapply IHC. exact Hfresh.
  - f_equal. eapply IHC. exact Hfresh.
  - apply not_in_app3_inv in Hfresh as [Hctx [Hbody1 Hbody2]].
    simpl. rewrite (IHC x u Hctx).
    rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t Hbody1).
    rewrite instantiate_identity.
    rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t0 Hbody2).
    rewrite instantiate_identity. reflexivity.
  - apply not_in_app3_inv in Hfresh as [Hstatic1 [Hctx Hstatic2]].
    simpl. rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t Hstatic1).
    rewrite instantiate_identity. rewrite (IHC x u Hctx).
    rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t0 Hstatic2).
    rewrite instantiate_identity. reflexivity.
  - apply not_in_app3_inv in Hfresh as [Hstatic1 [Hstatic2 Hctx]].
    simpl. rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t Hstatic1).
    rewrite instantiate_identity.
    rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t0 Hstatic2).
    rewrite instantiate_identity. rewrite (IHC x u Hctx). reflexivity.
  - f_equal. eapply IHC. exact Hfresh.
  - apply not_in_app3_inv in Hfresh as [Hctx [Hyes Hno]].
    simpl. rewrite (IHC x u Hctx).
    rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t Hyes).
    rewrite instantiate_identity.
    rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t0 Hno).
    rewrite instantiate_identity. reflexivity.
  - apply not_in_app3_inv in Hfresh as [Hstatic1 [Hctx Hstatic2]].
    simpl. rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t Hstatic1).
    rewrite instantiate_identity. rewrite (IHC x u Hctx).
    rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t0 Hstatic2).
    rewrite instantiate_identity. reflexivity.
  - apply not_in_app3_inv in Hfresh as [Hstatic1 [Hstatic2 Hctx]].
    simpl. rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t Hstatic1).
    rewrite instantiate_identity.
    rewrite (instantiate_update_irrelevant (fun y => tm_fvar y) x u t0 Hstatic2).
    rewrite instantiate_identity. rewrite (IHC x u Hctx). reflexivity.
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 HC Hground Htransparent Hnoflow.
  destruct (no_flow_forces_low_target
    (security_of T_secret).(indirect_reader)
    (security_of T_result).(indirect_reader) Hnoflow) as [Hsecret Hresult].
  subst.
  eapply (related_ground_terms_same_result T_result (plug C t1) (plug C t2)).
  - exact Hground.
  - unfold transparent in Htransparent. exact Htransparent.
  - rewrite Hresult. apply flows_to_refl.
  - destruct HC as [L Htyped].
    destruct (fresh_atom (L ++ fv (plug C (tm_unit public)))) as [x Hfresh].
    apply not_in_app_inv in Hfresh as [HxL Hxctx].
    pose (rho1 := substitution_update (fun y => tm_fvar y) x t1).
    pose (rho2 := substitution_update (fun y => tm_fvar y) x t2).
    assert (Hhidden : ~ flows_to (indirect_reader (security_of T_secret)) Low).
    { rewrite Hsecret. simpl. tauto. }
    assert (Henv : substitution_rel (update empty x T_secret) rho1 rho2).
    { intros y U Hlookup. simpl in Hlookup.
      destruct (Nat.eqb y x) eqn:Hyx.
      - apply Nat.eqb_eq in Hyx. subst y. inversion Hlookup; subst U.
        unfold rho1, rho2. simpl.
        eapply hidden_terms_related. exact Hhidden.
      - discriminate. }
    assert (Hidclosed : substitution_closed (fun y => tm_fvar y)).
    { intros y. exact I. }
    assert (Hclosed1 : substitution_closed rho1).
    { unfold rho1. eapply substitution_closed_update_lc; [exact Hidclosed |].
      eapply has_type_locally_closed. exact Ht1. }
    assert (Hclosed2 : substitution_closed rho2).
    { unfold rho2. eapply substitution_closed_update_lc; [exact Hidclosed |].
      eapply has_type_locally_closed. exact Ht2. }
    assert (Hct : has_type (update empty x T_secret)
        (plug C (tm_fvar x)) T_result).
    { eapply Htyped. exact HxL. }
    unfold term_rel. intros w1 w2 Ev1 Ev2.
    eapply (fundamental (update empty x T_secret) (plug C (tm_fvar x))
      T_result Hct rho1 rho2 Henv Hclosed1 Hclosed2 w1 w2).
    + apply evaluates_big_step. unfold rho1.
      rewrite (instantiate_plug_update_id C x t1 Hxctx). exact Ev1.
    + apply evaluates_big_step. unfold rho2.
      rewrite (instantiate_plug_update_id C x t2 Hxctx). exact Ev2.
Qed.
