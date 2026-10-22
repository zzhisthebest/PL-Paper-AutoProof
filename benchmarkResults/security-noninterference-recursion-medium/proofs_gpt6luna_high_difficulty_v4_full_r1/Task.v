From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From Stdlib Require Import Program.Equality.
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
  | tm_natrec : tm -> tm -> tm -> label -> tm.

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
  | tm_case t0 body1 body2 _ => fv t0 ++ fv body1 ++ fv body2
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

Lemma value_locally_closed : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv; unfold locally_closed in *; simpl in *; intuition.
Qed.

Lemma protect_value_is_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l Hv. induction Hv; destruct l; simpl.
  - constructor.
  - constructor.
  - eapply v_abs. exact H.
  - eapply v_abs. exact H.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor.
  - constructor.
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
      has_type Gamma (tm_natrec n b s r) (ty_protect k.(indirect_reader) T).

Lemma security_le_refl : forall k, security_le k k.
Proof. intros [r ir]. split; apply flows_to_refl. Qed.

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
  | B_Nat : forall n k, big_step (tm_nat n k) (tm_nat n k)
  | B_Succ : forall t n k r,
      big_step t (tm_nat n k) -> flows_to k.(reader) r ->
      big_step (tm_succ t r) (protect_value (tm_nat (S n) public) k.(indirect_reader))
  | B_NatRec : forall n b s r m k vb vs result,
      big_step n (tm_nat m k) -> big_step b vb -> big_step s vs ->
      flows_to k.(reader) r -> big_step (natrec_unroll m vb vs r) result ->
      big_step (tm_natrec n b s r) (protect_value result k.(indirect_reader)).

Lemma multi_congruence : forall (C : tm -> tm),
  (forall t t', step t t' -> step (C t) (C t')) ->
  forall t t', multi t t' -> multi (C t) (C t').
Proof.
  intros C HC t t' H. induction H.
  - apply multi_refl.
  - eapply multi_step; [apply HC; exact H | exact IHmulti].
Qed.

Lemma evaluates_protect : forall l t v,
  evaluates t v -> evaluates (tm_protect l t) (protect_value v l).
Proof.
  intros l t v [M Hv]. split.
  - eapply multi_trans.
    + eapply multi_congruence; [intros; econstructor; eassumption|exact M].
    + eapply multi_step; [constructor; exact Hv|constructor].
  - apply protect_value_is_value. exact Hv.
Qed.

Lemma evaluates_protect_inv : forall l t v,
  evaluates (tm_protect l t) v ->
  exists u, evaluates t u /\ v = protect_value u l.
Proof.
  intros l t v [M Hv].
  remember (tm_protect l t) as q eqn:Eq in M.
  revert l t Eq. induction M; intros l body Eq.
  - inversion Eq; subst. inversion Hv.
  - inversion Eq; subst.
    inversion H; subst.
    + assert (Hpv : value (protect_value body l)) by (apply protect_value_is_value; assumption).
      pose proof (value_multi_inv _ _ Hpv M) as E. subst.
      exists body. split; [split; [constructor|assumption]|reflexivity].
    + destruct (IHM Hv l t' eq_refl) as [u [Hu Ev]].
      exists u. split.
      * destruct Hu as [M' Vu]. split; [eapply multi_step; [exact H4|exact M']|exact Vu].
      * exact Ev.
Qed.

Lemma multi_first_step : forall t v,
  multi t v -> value v -> ~ value t -> exists t', step t t' /\ multi t' v.
Proof.
  intros t v M Hv. inversion M; subst.
  - intros Hnot. exfalso. apply Hnot. exact Hv.
  - intros _. eauto.
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
  | tm_nat n k => tm_nat n k
  | tm_succ t r => tm_succ (instantiate rho t) r
  | tm_natrec n b s r => tm_natrec (instantiate rho n) (instantiate rho b) (instantiate rho s) r
  end.

Lemma instantiate_open_rec : forall rho t k u,
  (forall x, locally_closed (rho x)) ->
  instantiate rho (open_rec k u t) =
  open_rec k (instantiate rho u) (instantiate rho t).
Proof.
  intros rho t. induction t; intros k u Hrho; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - unfold locally_closed in Hrho. simpl.
    rewrite open_rec_lc_at with (d := 0) (k := k) (u := instantiate rho u).
    + reflexivity.
    + match goal with x : atom |- _ => apply (Hrho x) end.
    + lia.
  - reflexivity.
  - f_equal. apply IHt. exact Hrho.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt1, IHt2; auto.
  - f_equal. apply IHt. exact Hrho.
  - f_equal. apply IHt. exact Hrho.
  - f_equal. apply IHt. exact Hrho.
  - f_equal. apply IHt. exact Hrho.
  - rewrite IHt1, IHt2, IHt3; auto.
  - f_equal. apply IHt. exact Hrho.
  - reflexivity.
  - f_equal. apply IHt. exact Hrho.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma instantiate_open : forall rho body u,
  (forall x, locally_closed (rho x)) ->
  instantiate rho (open body u) = open (instantiate rho body) (instantiate rho u).
Proof. intros. unfold open. apply instantiate_open_rec. exact H. Qed.

Lemma lc_at_mono : forall t k k', lc_at k t -> k <= k' -> lc_at k' t.
Proof.
  induction t; intros k k' Hlc Hkk'; simpl in *; try exact I.
  - lia.
  - eapply IHt; [exact Hlc|lia].
  - destruct Hlc as [H1 H2]. split; [eapply IHt1|eapply IHt2]; eauto.
  - destruct Hlc as [H1 H2]. split; [eapply IHt1|eapply IHt2]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct Hlc as [H0 [H1 H2]]. repeat split.
    + eapply IHt1; eauto.
    + eapply IHt2; [exact H1|lia].
    + eapply IHt3; [exact H2|lia].
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct Hlc as [H0 [H1 H2]]. repeat split.
    + eapply IHt1; eauto.
    + eapply IHt2; [exact H1|lia].
    + eapply IHt3; [exact H2|lia].
Qed.

Lemma instantiate_lc_at : forall rho t k,
  lc_at k t -> (forall x, locally_closed (rho x)) ->
  lc_at k (instantiate rho t).
Proof.
  intros rho t. induction t; intros k Hlc Hrho; simpl in *.
  - exact Hlc.
  - unfold locally_closed in Hrho. eapply lc_at_mono; [apply Hrho|lia].
  - exact I.
  - apply IHt. exact Hlc. exact Hrho.
  - destruct Hlc. split; [eapply IHt1|eapply IHt2]; eauto.
  - destruct Hlc. split; [eapply IHt1|eapply IHt2]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct Hlc as [H0 [H1 H2]]. repeat split; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - eapply IHt; eauto.
  - exact I.
  - eapply IHt; eauto.
  - destruct Hlc as [H0 [H1 H2]]. repeat split; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
Qed.

Definition substitution_update (rho : term_substitution) (x : atom) (u : tm)
    : term_substitution := fun y => if Nat.eqb x y then u else rho y.

Lemma instantiate_single_substitution : forall x u t,
  instantiate (fun y => if Nat.eqb x y then u else tm_fvar y) t = subst x u t.
Proof.
  intros x u t. induction t; simpl.
  - reflexivity.
  - destruct (Nat.eqb x a); reflexivity.
  - reflexivity.
  - f_equal. exact IHt.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - f_equal. exact IHt.
  - f_equal. exact IHt.
  - f_equal. exact IHt.
  - f_equal. exact IHt.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - f_equal. exact IHt.
  - reflexivity.
  - f_equal. exact IHt.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
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
  | C_Succ : program_context -> label -> program_context
  | C_RecArg : program_context -> tm -> tm -> label -> program_context
  | C_RecBase : tm -> program_context -> tm -> label -> program_context
  | C_RecStep : tm -> tm -> program_context -> label -> program_context.

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
  | C_Succ C' r => tm_succ (plug C' t) r
  | C_RecArg C' b s r => tm_natrec (plug C' t) b s r
  | C_RecBase n C' s r => tm_natrec n (plug C' t) s r
  | C_RecStep n b C' r => tm_natrec n b (plug C' t) r
  end.

Fixpoint context_fv (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ => context_fv C'
  | C_AppLeft C' t2 _ | C_PairLeft C' t2 _ => context_fv C' ++ fv t2
  | C_AppRight t1 C' _ | C_PairRight t1 C' _ => fv t1 ++ context_fv C'
  | C_Fst C' _ | C_Snd C' _ | C_Inl C' _ | C_Inr C' _
  | C_Protect _ C' | C_Succ C' _ => context_fv C'
  | C_CaseScrutinee C' b1 b2 _ => context_fv C' ++ fv b1 ++ fv b2
  | C_CaseLeft t0 C' b2 _ => fv t0 ++ context_fv C' ++ fv b2
  | C_CaseRight t0 b1 C' _ => fv t0 ++ fv b1 ++ context_fv C'
  | C_RecArg C' b s _ => context_fv C' ++ fv b ++ fv s
  | C_RecBase n C' s _ => fv n ++ context_fv C' ++ fv s
  | C_RecStep n b C' _ => fv n ++ fv b ++ context_fv C'
  end.

Lemma not_in_app_inv : forall (x : atom) (xs ys : list atom),
  ~ In x (xs ++ ys) -> ~ In x xs /\ ~ In x ys.
Proof.
  intros x xs ys H. split; intros Hin; apply H; apply in_or_app; auto.
Qed.

Lemma fresh_for_context : forall L C,
  exists x, ~ In x L /\ ~ In x (context_fv C).
Proof.
  intros L C. destruct (fresh_atom (L ++ context_fv C)) as [x Hx].
  exists x. split; intros H; apply Hx; apply in_or_app; auto.
Qed.

Lemma subst_notin_fv : forall t x u,
  ~ In x (fv t) -> subst x u t = t.
Proof.
  induction t; intros x u H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. simpl. auto.
    + reflexivity.
  - reflexivity.
  - f_equal. apply IHt. exact H.
  - apply not_in_app_inv in H as [H1 H2]. rewrite IHt1, IHt2; auto.
  - apply not_in_app_inv in H as [H1 H2]. rewrite IHt1, IHt2; auto.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - apply not_in_app_inv in H as [H0 Hrest].
    apply not_in_app_inv in Hrest as [H1 H2].
    rewrite IHt1, IHt2, IHt3; auto.
  - f_equal. apply IHt. exact H.
  - reflexivity.
  - f_equal. apply IHt. exact H.
  - apply not_in_app_inv in H as [H0 Hrest].
    apply not_in_app_inv in Hrest as [H1 H2].
    rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma subst_plug_fresh : forall C x u t,
  ~ In x (context_fv C) ->
  subst x u (plug C t) = plug C (subst x u t).
Proof.
  induction C; intros x u hole_term Havoid; simpl in *.
  - reflexivity.
  - f_equal. apply IHC. exact Havoid.
  - apply not_in_app_inv in Havoid as [Hc Hside].
    rewrite (IHC x u hole_term Hc).
    rewrite (subst_notin_fv t x u Hside). reflexivity.
  - apply not_in_app_inv in Havoid as [Hside Hc].
    rewrite (subst_notin_fv t x u Hside).
    rewrite (IHC x u hole_term Hc). reflexivity.
  - apply not_in_app_inv in Havoid as [Hc Hside].
    rewrite (IHC x u hole_term Hc).
    rewrite (subst_notin_fv t x u Hside). reflexivity.
  - apply not_in_app_inv in Havoid as [Hside Hc].
    rewrite (subst_notin_fv t x u Hside).
    rewrite (IHC x u hole_term Hc). reflexivity.
  - f_equal. apply IHC. exact Havoid.
  - f_equal. apply IHC. exact Havoid.
  - f_equal. apply IHC. exact Havoid.
  - f_equal. apply IHC. exact Havoid.
  - apply not_in_app_inv in Havoid as [Hc Hrest].
    apply not_in_app_inv in Hrest as [Hb1 Hb2].
    rewrite (IHC x u hole_term Hc).
    rewrite (subst_notin_fv t x u Hb1).
    rewrite (subst_notin_fv t0 x u Hb2). reflexivity.
  - apply not_in_app_inv in Havoid as [Ht0 Hrest].
    apply not_in_app_inv in Hrest as [Hc Hb2].
    rewrite (subst_notin_fv t x u Ht0).
    rewrite (IHC x u hole_term Hc).
    rewrite (subst_notin_fv t0 x u Hb2). reflexivity.
  - apply not_in_app_inv in Havoid as [Ht0 Hrest].
    apply not_in_app_inv in Hrest as [Hb1 Hc].
    rewrite (subst_notin_fv t x u Ht0).
    rewrite (subst_notin_fv t0 x u Hb1).
    rewrite (IHC x u hole_term Hc). reflexivity.
  - f_equal. apply IHC. exact Havoid.
  - f_equal. apply IHC. exact Havoid.
  - apply not_in_app_inv in Havoid as [Hc Hrest].
    apply not_in_app_inv in Hrest as [Hb Hs].
    rewrite (IHC x u hole_term Hc).
    rewrite (subst_notin_fv t x u Hb).
    rewrite (subst_notin_fv t0 x u Hs). reflexivity.
  - apply not_in_app_inv in Havoid as [Hn Hrest].
    apply not_in_app_inv in Hrest as [Hc Hs0].
    rewrite (subst_notin_fv t x u Hn).
    rewrite (IHC x u hole_term Hc).
    rewrite (subst_notin_fv t0 x u Hs0). reflexivity.
  - apply not_in_app_inv in Havoid as [Hn Hrest].
    apply not_in_app_inv in Hrest as [Hb Hc].
    rewrite (subst_notin_fv t x u Hn).
    rewrite (subst_notin_fv t0 x u Hb).
    rewrite (IHC x u hole_term Hc). reflexivity.
Qed.

Lemma instantiate_context_hole : forall C x u,
  ~ In x (context_fv C) ->
  instantiate (fun y => if Nat.eqb x y then u else tm_fvar y)
    (plug C (tm_fvar x)) = plug C u.
Proof.
  intros C x u Hfresh. rewrite instantiate_single_substitution.
  rewrite subst_plug_fresh by exact Hfresh. simpl. rewrite Nat.eqb_refl. reflexivity.
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

Lemma transparent_at_indirect : forall kappa T,
  transparent_at kappa T ->
  flows_to (security_of T).(indirect_reader) kappa.(indirect_reader).
Proof.
  intros kappa T H. destruct T; simpl in *; unfold security_le in *; tauto.
Qed.

Definition same_result (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm,
    evaluates t1 v1 -> evaluates t2 v2 ->
    erase_security v1 = erase_security v2.

(* At a low observation point, relate values by their observable shape.  A
   high-indirect value is deliberately opaque.  Arrow values are handled
   extensionally by the fundamental theorem; ground observations never need
   to inspect their bodies. *)
Fixpoint value_rel (T : ty) (v1 v2 : tm) : Prop :=
  flows_to (security_of T).(indirect_reader) Low ->
    match T with
    | Ty_Unit _ => exists k1 k2, v1 = tm_unit k1 /\ v2 = tm_unit k2
    | Ty_Nat _ => exists n k1 k2, v1 = tm_nat n k1 /\ v2 = tm_nat n k2
    | Ty_Sum T1 T2 _ =>
        (exists w1 w2 k1 k2, v1 = tm_inl w1 k1 /\ v2 = tm_inl w2 k2 /\ value_rel T1 w1 w2) \/
        (exists w1 w2 k1 k2, v1 = tm_inr w1 k1 /\ v2 = tm_inr w2 k2 /\ value_rel T2 w1 w2)
    | Ty_Prod T1 T2 _ =>
        exists a1 a2 b1 b2 k1 k2,
          v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
          value_rel T1 a1 a2 /\ value_rel T2 b1 b2
    | Ty_Arrow A B k =>
        forall a1 a2, value_rel A a1 a2 ->
        forall r w1 w2, flows_to k.(reader) r ->
          evaluates (tm_app v1 a1 r) w1 ->
          evaluates (tm_app v2 a2 r) w2 ->
          value_rel B w1 w2
    end.

Definition term_rel (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, evaluates t1 v1 -> evaluates t2 v2 -> value_rel T v1 v2.

Lemma term_rel_unit : forall k,
  term_rel (Ty_Unit k) (tm_unit k) (tm_unit k).
Proof.
  intros k v1 v2 [M1 V1] [M2 V2].
  assert (E1 : v1 = tm_unit k) by (eapply value_multi_inv; [constructor|exact M1]).
  assert (E2 : v2 = tm_unit k) by (eapply value_multi_inv; [constructor|exact M2]).
  subst. unfold value_rel. simpl. intros _. eauto.
Qed.

Lemma term_rel_nat : forall n k,
  term_rel (Ty_Nat k) (tm_nat n k) (tm_nat n k).
Proof.
  intros n k v1 v2 [M1 V1] [M2 V2].
  assert (E1 : v1 = tm_nat n k) by (eapply value_multi_inv; [constructor|exact M1]).
  assert (E2 : v2 = tm_nat n k) by (eapply value_multi_inv; [constructor|exact M2]).
  subst. unfold value_rel. simpl. intros _. eauto.
Qed.


Definition related_substitutions (Gamma : context)
    (rho1 rho2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    term_rel T (rho1 x) (rho2 x).

Lemma related_substitutions_update : forall Gamma x T rho1 rho2 a1 a2,
  related_substitutions Gamma rho1 rho2 -> term_rel T a1 a2 ->
  related_substitutions (update Gamma x T)
    (substitution_update rho1 x a1) (substitution_update rho2 x a2).
Proof.
  intros Gamma x T rho1 rho2 a1 a2 Henv Hnew y U Hlookup.
  unfold related_substitutions, term_rel in *.
  simpl in Hlookup. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst U.
    unfold substitution_update. rewrite Nat.eqb_refl. apply Hnew.
  - assert (Hneq : y <> x) by (intro Heq; subst; rewrite Nat.eqb_refl in E; discriminate).
    specialize (Henv y U Hlookup).
    assert (E' : Nat.eqb x y = false).
    { apply Nat.eqb_neq. intro Heq. apply Hneq. symmetry. exact Heq. }
    unfold substitution_update. rewrite E'.
    apply Henv.
Qed.

Lemma substitution_update_locally_closed : forall rho x u,
  (forall y, locally_closed (rho y)) -> locally_closed u ->
  forall y, locally_closed (substitution_update rho x u y).
Proof.
  intros rho x u Hrho Hu y. unfold substitution_update.
  destruct (Nat.eqb x y); auto.
Qed.

Definition context_interpretation (C : program_context)
    (T_hole T_result : ty) : Prop :=
  forall t1 t2, term_rel T_hole t1 t2 -> term_rel T_result (plug C t1) (plug C t2).

Lemma value_rel_ground_erases : forall T kappa v1 v2,
  ground T -> transparent_at kappa T -> flows_to kappa.(indirect_reader) Low ->
  value_rel T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  induction T; intros kappa v1 v2 Hg Ht Hlow Hr; simpl in *.
  - assert (Hown : flows_to (indirect_reader s) Low).
    { eapply flows_to_trans; [exact (proj2 (proj1 Ht))|exact Hlow]. }
    apply Hr in Hown. destruct Hown as [k1 [k2 [-> ->]]]. reflexivity.
  - assert (Hown : flows_to (indirect_reader s) Low).
    { eapply flows_to_trans; [exact (proj2 (proj1 Ht))|exact Hlow]. }
    apply Hr in Hown. destruct Hg as [Hg1 Hg2]. destruct Hown as [Hbranch|Hbranch].
    + destruct Hbranch as [w1 [w2 [k1 [k2 [-> [-> Hrel]]]]]].
      simpl. f_equal. eapply IHT1; [exact Hg1| | |exact Hrel].
      * destruct Ht as [_ [Ht1 _]]. exact Ht1.
      * exact Hlow.
    + destruct Hbranch as [w1 [w2 [k1 [k2 [-> [-> Hrel]]]]]].
      simpl. f_equal. eapply IHT2; [exact Hg2| | |exact Hrel].
      * destruct Ht as [_ [_ Ht2]]. exact Ht2.
      * exact Hlow.
  - assert (Hown : flows_to (indirect_reader s) Low).
    { eapply flows_to_trans; [exact (proj2 (proj1 Ht))|exact Hlow]. }
    apply Hr in Hown. destruct Hg as [Hg1 Hg2].
    destruct Hown as [a1 [a2 [b1 [b2 [k1 [k2 [-> [-> [Ha Hb]]]]]]]]].
    simpl. f_equal.
    + eapply IHT1; [exact Hg1| | |exact Ha].
      * destruct Ht as [_ [Ht1 _]]. exact Ht1.
      * exact Hlow.
    + eapply IHT2; [exact Hg2| | |exact Hb].
      * destruct Ht as [_ [_ Ht2]]. exact Ht2.
      * exact Hlow.
  - contradiction.
  - assert (Hown : flows_to (indirect_reader s) Low).
    { eapply flows_to_trans; [exact (proj2 (proj1 Ht))|exact Hlow]. }
    apply Hr in Hown. destruct Hown as [n [k1 [k2 [-> ->]]]]. reflexivity.
Qed.

Lemma value_rel_protect_high : forall T v1 v2,
  value_rel (ty_protect High T) v1 v2.
Proof.
  intros T v1 v2. destruct T; simpl; try destruct s as [r ir]; simpl;
    unfold value_rel; simpl; intros H;
    unfold flows_to, join in H; destruct ir; simpl in H; contradiction.
Qed.

Lemma value_rel_protect_low : forall T v1 v2,
  value_rel T v1 v2 -> value_rel (ty_protect Low T) v1 v2.
Proof. intros T v1 v2 H. rewrite ty_protect_low. exact H. Qed.

Lemma value_rel_protect_value : forall T l v1 v2,
  value_rel T v1 v2 ->
  value_rel (ty_protect l T) (protect_value v1 l) (protect_value v2 l).
Proof.
  intros T l v1 v2 H. destruct l.
  - rewrite ty_protect_low. repeat rewrite protect_value_low. exact H.
  - apply value_rel_protect_high.
Qed.

Lemma term_rel_protect : forall T l t1 t2,
  term_rel T t1 t2 ->
  term_rel (ty_protect l T) (tm_protect l t1) (tm_protect l t2).
Proof.
  intros T l t1 t2 Hrel v1 v2 E1 E2.
  destruct (evaluates_protect_inv _ _ _ E1) as [u1 [Hu1 Ev1]].
  destruct (evaluates_protect_inv _ _ _ E2) as [u2 [Hu2 Ev2]].
  subst v1 v2. apply value_rel_protect_value. eapply Hrel; eassumption.
Qed.

Lemma context_interpretation_protect : forall C T_hole T,
  context_interpretation C T_hole T ->
  forall l, context_interpretation (C_Protect l C) T_hole (ty_protect l T).
Proof.
  intros C T_hole T HCI l t1 t2 Hterms.
  unfold context_interpretation in *. simpl. apply term_rel_protect.
  apply HCI. exact Hterms.
Qed.


Lemma value_rel_nat_eq : forall k n1 n2 k1 k2,
  flows_to k.(indirect_reader) Low ->
  value_rel (Ty_Nat k) (tm_nat n1 k1) (tm_nat n2 k2) -> n1 = n2.
Proof.
  intros k n1 n2 k1 k2 Hlow Hrel. simpl in Hrel.
  specialize (Hrel Hlow). destruct Hrel as [n [ka [kb [H1 H2]]]].
  inversion H1; inversion H2; reflexivity.
Qed.

Lemma value_rel_inl : forall T1 T2 k a b ka kb,
  value_rel T1 a b ->
  value_rel (Ty_Sum T1 T2 k) (tm_inl a ka) (tm_inl b kb).
Proof. intros. unfold value_rel. simpl. intros _. left. eauto 8. Qed.

Lemma value_rel_inr : forall T1 T2 k a b ka kb,
  value_rel T2 a b ->
  value_rel (Ty_Sum T1 T2 k) (tm_inr a ka) (tm_inr b kb).
Proof. intros. unfold value_rel. simpl. intros _. right. eauto 8. Qed.

Lemma value_rel_pair : forall T1 T2 k a1 a2 b1 b2 ka kb,
  value_rel T1 a1 a2 -> value_rel T2 b1 b2 ->
  value_rel (Ty_Prod T1 T2 k)
    (tm_pair a1 b1 ka) (tm_pair a2 b2 kb).
Proof.
  intros T1 T2 k a1 a2 b1 b2 ka kb H1 H2.
  unfold value_rel. simpl. intros _.
  exists a1, a2, b1, b2, ka, kb. repeat split; assumption.
Qed.

Lemma erase_protect_value : forall v l,
  value v -> erase_security (protect_value v l) = erase_security v.
Proof.
  intros v l Hv. inversion Hv; subst; destruct l; simpl;
    try reflexivity; destruct kappa as [r ir]; destruct r, ir; reflexivity.
Qed.

Lemma value_rel_subtype : forall T U, subtype T U ->
  forall v1 v2, value_rel T v1 v2 -> value_rel U v1 v2.
Proof.
  intros T U H. induction H; intros v1 v2 Hrel; simpl in *.
  - intro Hlow. apply Hrel. eapply flows_to_trans with (l2 := kappa2.(indirect_reader));
      [exact (proj2 H1)|exact Hlow].
  - intro Hlow. assert (Hsrc : flows_to (indirect_reader kappa1) Low).
    { eapply flows_to_trans with (l2 := kappa2.(indirect_reader));
        [exact (proj2 H3)|exact Hlow]. }
    specialize (Hrel Hsrc). destruct Hrel as [HL|HR].
    + left. destruct HL as [a [b [ka [kb [E1 [E2 Hab]]]]]].
      exists a, b, ka, kb. repeat split; eauto.
    + right. destruct HR as [a [b [ka [kb [E1 [E2 Hab]]]]]].
      exists a, b, ka, kb. repeat split; eauto.
  - intro Hlow. assert (Hsrc : flows_to (indirect_reader kappa1) Low).
    { eapply flows_to_trans with (l2 := kappa2.(indirect_reader));
        [exact (proj2 H3)|exact Hlow]. }
    specialize (Hrel Hsrc). destruct Hrel as [a [b [c [d [ka [kb [E1 [E2 [Hab Hcd]]]]]]]]].
    exists a, b, c, d, ka, kb. repeat split; eauto.
  - intro Hlow. assert (Hsrc : flows_to (indirect_reader kappa1) Low).
    { eapply flows_to_trans with (l2 := kappa2.(indirect_reader));
        [exact (proj2 H3)|exact Hlow]. }
    specialize (Hrel Hsrc).
    intros a b Hab r w1 w2 Hr E1 E2.
    pose proof (Hrel a b (IHsubtype1 a b Hab) r w1 w2
      (flows_to_trans (reader kappa1) (reader kappa2) r (proj1 H3) Hr) E1 E2) as Hout.
    exact (IHsubtype2 w1 w2 Hout).
  - apply IHsubtype2. apply IHsubtype1. exact Hrel.
  - intro Hlow. assert (Hsrc : flows_to (indirect_reader k1) Low).
    { eapply flows_to_trans with (l2 := k2.(indirect_reader));
        [exact (proj2 H1)|exact Hlow]. }
    specialize (Hrel Hsrc). exact Hrel.
Qed.

Lemma term_rel_subtype : forall T U t1 t2,
  subtype T U -> term_rel T t1 t2 -> term_rel U t1 t2.
Proof.
  intros T U t1 t2 Hsub Hrel v1 v2 E1 E2.
  eapply value_rel_subtype; [exact Hsub|eapply Hrel; eassumption].
Qed.

Lemma context_interpretation_subtype : forall C T_hole T U,
  context_interpretation C T_hole T -> subtype T U ->
  context_interpretation C T_hole U.
Proof.
  intros C T_hole T U HCI Hsub t1 t2 Hterms.
  unfold context_interpretation in *.
  intros w1 w2 E1 E2. eapply value_rel_subtype; [exact Hsub|].
  eapply HCI; eassumption.
Qed.

Lemma subtype_wf : forall T U, subtype T U -> wf_ty T /\ wf_ty U.
Proof.
  intros T U H. induction H.
  - simpl. repeat split; assumption.
  - simpl. destruct IHsubtype1 as [H11 H12]. destruct IHsubtype2 as [H21 H22].
    repeat split; assumption.
  - simpl. destruct IHsubtype1 as [H11 H12]. destruct IHsubtype2 as [H21 H22].
    repeat split; assumption.
  - simpl. destruct IHsubtype1 as [H11 H12]. destruct IHsubtype2 as [H21 H22].
    repeat split; assumption.
  - destruct IHsubtype1 as [HT HU]. destruct IHsubtype2 as [HU' HV].
    split; assumption.
  - simpl. repeat split; assumption.
Qed.

Lemma subtype_refl_wf : forall T, wf_ty T -> subtype T T.
Proof.
  induction T; intros Hwf; simpl in Hwf.
  - destruct s as [r ir]. constructor; try assumption.
    split; apply flows_to_refl.
  - destruct Hwf as [H1 [H2 Hk]]. constructor; try assumption.
    + apply IHT1; exact H1.
    + apply IHT2; exact H2.
    + apply security_le_refl.
  - destruct Hwf as [H1 [H2 Hk]]. constructor; try assumption.
    + apply IHT1; exact H1.
    + apply IHT2; exact H2.
    + apply security_le_refl.
  - destruct Hwf as [H1 [H2 Hk]]. constructor; try assumption.
    + apply IHT1; exact H1.
    + apply IHT2; exact H2.
    + apply security_le_refl.
  - destruct s as [r ir]. constructor; try assumption.
    split; apply flows_to_refl.
Qed.

Lemma ty_protect_wf : forall l T, wf_ty T -> wf_ty (ty_protect l T).
Proof.
  intros l T H. destruct T; simpl in *.
  - apply protect_security_wf. exact H.
  - destruct H as [H1 [H2 Hk]]. repeat split; try assumption.
    apply protect_security_wf. exact Hk.
  - destruct H as [H1 [H2 Hk]]. repeat split; try assumption.
    apply protect_security_wf. exact Hk.
  - destruct H as [H1 [H2 Hk]]. repeat split; try assumption.
    apply protect_security_wf. exact Hk.
  - apply protect_security_wf. exact H.
Qed.

Lemma flows_to_not_inv : forall l1 l2,
  ~ flows_to l1 l2 -> l1 = High /\ l2 = Low.
Proof. destruct l1, l2; simpl; intuition congruence. Qed.

Lemma noninterference_from_interpretation : forall C t1 t2 T_secret T_result,
  context_interpretation C T_secret T_result ->
  ground T_result -> transparent T_result ->
  ~ flows_to (security_of T_secret).(indirect_reader)
      (security_of T_result).(indirect_reader) ->
  same_result (plug C t1) (plug C t2).
Proof.
  intros C t1 t2 T_secret T_result HCI HG HT Hnf.
  assert (Hsecret_low : ~ flows_to (security_of T_secret).(indirect_reader) Low).
  { intros Hsl. apply Hnf.
    eapply flows_to_trans; [exact Hsl|destruct (security_of T_result).(indirect_reader); exact I]. }
  assert (Hterm : term_rel T_secret t1 t2).
  { unfold term_rel. intros v1 v2 E1 E2.
    destruct T_secret; simpl in *; unfold value_rel; simpl; intros Hsl;
      exfalso; exact (Hsecret_low Hsl). }
  unfold same_result. intros v1 v2 E1 E2.
  pose proof (HCI t1 t2 Hterm v1 v2 E1 E2) as Hrel.
  eapply value_rel_ground_erases; [exact HG| | |exact Hrel].
  - exact HT.
  - rewrite (proj2 (flows_to_not_inv _ _ Hnf)). apply flows_to_refl.
Qed.

Lemma context_interpretation_hole : forall T U,
  subtype T U -> context_interpretation C_Hole T U.
Proof.
  intros T U Hsub. unfold context_interpretation, term_rel, plug.
  intros t1 t2 Hrel v1 v2 E1 E2.
  eapply value_rel_subtype; [exact Hsub|].
  eapply Hrel; eassumption.
Qed.

Lemma typing_lookup_subtype : forall Gamma t U,
  has_type Gamma t U -> forall x, t = tm_fvar x ->
  exists T, lookup_context x Gamma = Some T /\ subtype T U.
Proof.
  intros Gamma t U Hty. induction Hty; intros x0 Heq; try discriminate.
  - inversion Heq; subst. exists T. split; [exact H|].
    apply subtype_refl_wf. exact H0.
  - destruct (IHHty x0 Heq) as [V [Hv Hsub]].
    exists V. split; [exact Hv|eapply S_Trans; eauto].
Qed.

Lemma lookup_context_functional : forall Gamma x T U,
  lookup_context x Gamma = Some T -> lookup_context x Gamma = Some U -> T = U.
Proof.
  induction Gamma as [|[y V] Gamma IH]; intros x T U H1 H2; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H1; inversion H2; subst; reflexivity.
    + eapply IH; eassumption.
Qed.

Lemma context_hole_subtype : forall T U,
  context_has_type C_Hole T U -> subtype T U.
Proof.
  intros T U [L HT]. destruct (fresh_atom L) as [x Hx].
  specialize (HT x Hx). simpl in HT.
  destruct (typing_lookup_subtype _ _ _ HT x eq_refl) as [V [Hlook Hsub]].
  assert (V = T).
  { eapply lookup_context_functional; [exact Hlook|apply lookup_update_eq]. }
  subst V. exact Hsub.
Qed.

Lemma context_hole_interpretation : forall T U,
  context_has_type C_Hole T U -> context_interpretation C_Hole T U.
Proof.
  intros T U Htyped. apply context_interpretation_hole.
  eapply context_hole_subtype; exact Htyped.
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
  intros C t1 t2 T_secret T_result HT1 HT2 HC Hground Htransparent Hnot.
  pose proof (proj2 (flows_to_not_inv
    (security_of T_secret).(indirect_reader)
    (security_of T_result).(indirect_reader) Hnot)) as Hresult_low.
  eapply noninterference_from_interpretation; eauto.
Qed.
