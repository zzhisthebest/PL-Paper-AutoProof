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
      big_step (tm_natrec n b s r) (protect_value result k.(indirect_reader))
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
  | tm_nat n k => tm_nat n k
  | tm_succ t r => tm_succ (instantiate rho t) r
  | tm_natrec n b s r => tm_natrec (instantiate rho n) (instantiate rho b) (instantiate rho s) r
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

Definition same_result (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm,
    evaluates t1 v1 -> evaluates t2 v2 ->
    erase_security v1 = erase_security v2.

(* The value relation used by the fundamental lemma.  The first clause of
   each constructor is deliberately controlled by the indirect reader: a
   value protected at High is opaque, while a Low value is compared by its
   observable shape. *)
Fixpoint value_rel (T : ty) (v w : tm) : Prop :=
  match T with
  | Ty_Unit k =>
      match k.(indirect_reader) with
      | High => True
      | Low => exists k1 k2, v = tm_unit k1 /\ w = tm_unit k2
      end
  | Ty_Nat k =>
      match k.(indirect_reader) with
      | High => True
      | Low => exists n k1 k2, v = tm_nat n k1 /\ w = tm_nat n k2 /\
          security_le k1 k /\ security_le k2 k
      end
  | Ty_Sum A B k =>
      match k.(indirect_reader) with
      | High => True
      | Low =>
        (exists v1 w1 k1 k2,
          v = tm_inl v1 k1 /\ w = tm_inl w1 k2 /\
          security_le k1 k /\ security_le k2 k /\ value_rel A v1 w1) \/
        (exists v1 w1 k1 k2,
          v = tm_inr v1 k1 /\ w = tm_inr w1 k2 /\
          security_le k1 k /\ security_le k2 k /\ value_rel B v1 w1)
      end
  | Ty_Prod A B k =>
      match k.(indirect_reader) with
      | High => True
      | Low => exists a1 a2 b1 b2 k1 k2,
          v = tm_pair a1 a2 k1 /\ w = tm_pair b1 b2 k2 /\
          security_le k1 k /\ security_le k2 k /\
          value_rel A a1 b1 /\ value_rel B a2 b2
      end
  | Ty_Arrow A B k =>
      match k.(indirect_reader) with
      | High => True
      | Low => exists A1 A2 body1 body2 ka kb,
          v = tm_abs A1 body1 ka /\ w = tm_abs A2 body2 kb /\
          security_le ka k /\ security_le kb k /\
          (forall a b va vb,
            value a -> value b -> value_rel A a b ->
            big_step (open body1 a) va -> big_step (open body2 b) vb ->
            value_rel B va vb)
      end
  end.

Fixpoint all_indirect_low (T : ty) : Prop :=
  match T with
  | Ty_Unit k | Ty_Nat k => k.(indirect_reader) = Low
  | Ty_Sum A B k | Ty_Prod A B k | Ty_Arrow A B k =>
      k.(indirect_reader) = Low /\ all_indirect_low A /\ all_indirect_low B
  end.

Lemma value_rel_high : forall T v w,
  value_rel (ty_protect High T) v w.
Proof.
  intros T v w. destruct T; simpl; destruct s as [r ir]; destruct ir; simpl; exact I.
Qed.

Lemma transparent_indirect_low_gen : forall T K,
  transparent_at K T -> K.(indirect_reader) = Low -> all_indirect_low T.
Proof.
  induction T as [k|A IHA B IHB k|A IHA B IHB k|A IHA B IHB k|k];
    intros K Htrans Hlow; simpl in *.
  - destruct Htrans as [Hsec _]. destruct Hsec as [_ Hir].
    destruct k as [r ir], K as [r' ir']; simpl in *.
    destruct ir, ir'; simpl in *; intuition.
  - destruct Htrans as [Hsec [HA HB]]. destruct Hsec as [_ Hir].
    assert (Hk : k.(indirect_reader) = Low).
    { destruct k as [r ir], K as [r' ir']; simpl in *;
      destruct ir, ir'; simpl in *; intuition. }
    repeat split; [exact Hk| |]; [eapply IHA|eapply IHB]; eauto.
  - destruct Htrans as [Hsec [HA HB]]. destruct Hsec as [_ Hir].
    assert (Hk : k.(indirect_reader) = Low).
    { destruct k as [r ir], K as [r' ir']; simpl in *;
      destruct ir, ir'; simpl in *; intuition. }
    repeat split; [exact Hk| |]; [eapply IHA|eapply IHB]; eauto.
  - destruct Htrans as [Hsec [HA HB]]. destruct Hsec as [_ Hir].
    assert (Hk : k.(indirect_reader) = Low).
    { destruct k as [r ir], K as [r' ir']; simpl in *;
      destruct ir, ir'; simpl in *; intuition. }
    repeat split; [exact Hk| |]; [eapply IHA|eapply IHB]; eauto.
  - destruct Htrans as [Hsec _]. destruct Hsec as [_ Hir].
    destruct k as [r ir], K as [r' ir']; simpl in *.
    destruct ir, ir'; simpl in *; intuition.
Qed.

Lemma nonflow_to_low : forall l1 l2,
  ~ flows_to l1 l2 -> l1 = High /\ l2 = Low.
Proof. destruct l1, l2; simpl; intuition. Qed.

Lemma value_rel_protect : forall T v w l,
  value_rel T v w ->
  value_rel (ty_protect l T) (protect_value v l) (protect_value w l).
Proof.
  intros T v w l Hrel. destruct l.
  - rewrite ty_protect_low, !protect_value_low. exact Hrel.
  - destruct T as [k|A B k|A B k|A B k|k];
      destruct k as [r ir]; destruct ir; simpl; exact I.
Qed.

Lemma value_rel_protect_le : forall T v w l1 l2 l,
  flows_to l1 l -> flows_to l2 l -> value_rel T v w ->
  value_rel (ty_protect l T) (protect_value v l1) (protect_value w l2).
Proof.
  intros T v w l1 l2 l H1 H2 Hrel. destruct l.
  - assert (l1 = Low) by (destruct l1; simpl in *; tauto).
    assert (l2 = Low) by (destruct l2; simpl in *; tauto).
    subst l1 l2. rewrite ty_protect_low, !protect_value_low. exact Hrel.
  - destruct T as [k|A B k|A B k|A B k|k];
      destruct k as [r ir]; destruct ir; simpl; exact I.
Qed.

Lemma instantiate_open_rec : forall rho,
  (forall x, locally_closed (rho x)) -> forall k u t,
  instantiate rho (open_rec k u t) =
  open_rec k (instantiate rho u) (instantiate rho t).
Proof.
  intros rho Hlc k u t. revert k u. induction t; intros k u; simpl; try reflexivity.
  all: try (destruct (Nat.eqb k n); reflexivity).
  all: try (f_equal; eauto).
  - rewrite open_rec_lc_at with (d := 0); [reflexivity|apply Hlc|lia].
Qed.

Lemma not_in_app : forall (x : atom) l1 l2,
  ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros x l1 l2 H. split; intro Hin; apply H; apply in_or_app; auto.
Qed.

Lemma instantiate_update_away : forall rho x u t,
  ~ In x (fv t) ->
  instantiate (substitution_update rho x u) t = instantiate rho t.
Proof.
  intros rho x u t. induction t; simpl; intros Hnot; try reflexivity.
  - simpl in Hnot. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hnot. simpl; auto.
    + unfold substitution_update. simpl. rewrite E. reflexivity.
  - f_equal. apply IHt. exact Hnot.
  - simpl in Hnot. destruct (not_in_app _ _ _ Hnot).
    f_equal; eauto.
  - simpl in Hnot. destruct (not_in_app _ _ _ Hnot).
    f_equal; eauto.
  - f_equal. apply IHt; exact Hnot.
  - f_equal. apply IHt; exact Hnot.
  - f_equal. apply IHt; exact Hnot.
  - f_equal. apply IHt; exact Hnot.
  - simpl in Hnot. destruct (not_in_app _ _ _ Hnot) as [H0 H12].
    destruct (not_in_app _ _ _ H12) as [H1 H2].
    f_equal; eauto.
  - f_equal. apply IHt; exact Hnot.
  - f_equal. apply IHt; exact Hnot.
  - simpl in Hnot. destruct (not_in_app _ _ _ Hnot) as [H0 H12].
    destruct (not_in_app _ _ _ H12) as [H1 H2].
    f_equal; eauto.
  - simpl in Hnot. destruct (not_in_app _ _ _ Hnot) as [H0 H12].
    destruct (not_in_app _ _ _ H12) as [H1 H2].
    f_equal; eauto.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv; unfold locally_closed in *; simpl in *; auto.
Qed.

Lemma typing_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty;
    unfold locally_closed in *; simpl in *; try tauto; try exact I.
  - destruct (fresh_atom L) as [x Hx].
    specialize (H2 x Hx). eapply lc_at_open_inv; exact H2.
  - destruct (fresh_atom L) as [x Hx].
    specialize (H1 x Hx). specialize (H3 x Hx).
    split; [assumption|]. split; [eapply lc_at_open_inv; exact H1|eapply lc_at_open_inv; exact H3].
Qed.

Lemma lc_at_mono : forall t d d',
  lc_at d t -> d <= d' -> lc_at d' t.
Proof.
  induction t; intros d d' Hlc Hdd; simpl in *; try lia; try exact I; try tauto.
  all: try (eapply IHt; [exact Hlc|lia]).
  all: try (destruct Hlc as [H1 H2]; split;
    [eapply IHt1|eapply IHt2]; [exact H1|lia|exact H2|lia]).
  all: try (destruct Hlc as [H0 [H1 H2]]; repeat split;
    [eapply IHt1|eapply IHt2|eapply IHt3];
    [exact H0|lia|exact H1|lia|exact H2|lia]).
Qed.

Lemma instantiate_lc_at : forall t d rho,
  lc_at d t -> (forall x, locally_closed (rho x)) ->
  lc_at d (instantiate rho t).
Proof.
  induction t; intros d rho Hlc Hrho; simpl in *; try assumption; try exact I.
  - eapply lc_at_mono; [apply Hrho|lia].
  - eapply IHt; eassumption.
  - destruct Hlc as [H1 H2]. split; [eapply IHt1|eapply IHt2]; eassumption.
  - destruct Hlc as [H1 H2]. split; [eapply IHt1|eapply IHt2]; eassumption.
  - eapply IHt; eassumption.
  - eapply IHt; eassumption.
  - eapply IHt; eassumption.
  - eapply IHt; eassumption.
  - destruct Hlc as [H0 [H1 H2]]. repeat split;
      [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
  - eapply IHt; eassumption.
  - eapply IHt; eassumption.
  - destruct Hlc as [H0 [H1 H2]]. repeat split;
      [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
  - destruct Hlc as [H0 [H1 H2]]. repeat split;
      [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
Qed.

Definition substitution_values (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Lemma substitution_values_lc : forall rho,
  substitution_values rho -> forall x, locally_closed (rho x).
Proof. auto. Qed.

Definition term_rel (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, big_step t1 v1 -> big_step t2 v2 -> value_rel T v1 v2.

Lemma big_step_value_inv : forall v w,
  value v -> big_step v w -> w = v.
Proof.
  intros v w Hv. revert w. induction Hv; intros w Hstep; inversion Hstep; subst;
    try reflexivity; f_equal; eauto.
Qed.

Lemma value_rel_app : forall A B k f g a b r v w,
  value_rel (Ty_Arrow A B k) f g ->
  value a -> value b -> value_rel A a b ->
  big_step (tm_app f a r) v -> big_step (tm_app g b r) w ->
  value_rel (ty_protect (indirect_reader k) B) v w.
Proof.
  intros A B k f g a b r v w Hfun Ha Hb Harg E1 E2.
  destruct (indirect_reader k) eqn:Hir.
  - unfold value_rel in Hfun. rewrite Hir in Hfun. simpl in Hfun.
    destruct Hfun as (A1 & A2 & body1 & body2 & ka & kb & Ef & Eg & Ska & Skb & Hbody).
    subst f g. inversion E1; subst. inversion E2; subst.
    inversion H2; subst. inversion H4; subst.
    assert (v0 = a) by (eapply big_step_value_inv; [exact Ha|exact H3]).
    assert (v = b) by (eapply big_step_value_inv; [exact Hb|exact H7]).
    subst v0 v.
    unfold security_le in Ska, Skb; simpl in Ska, Skb.
    rewrite Hir in Ska, Skb.
    destruct k0 as [ra ia], k1 as [rb ib].
    destruct ia; simpl in Ska; [|destruct Ska as [_ Hbad]; contradiction].
    destruct ib; simpl in Skb; [|destruct Skb as [_ Hbad]; contradiction].
    rewrite ty_protect_low, !protect_value_low.
    eapply (Hbody a b w0 w1); eauto.
  - apply value_rel_high.
Qed.

Definition env_rel (Gamma : context) (rho1 rho2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    term_rel T (rho1 x) (rho2 x).

Lemma env_rel_update : forall Gamma rho1 rho2 x A u1 u2,
  env_rel Gamma rho1 rho2 -> value u1 -> value u2 -> value_rel A u1 u2 ->
  env_rel (update Gamma x A)
    (substitution_update rho1 x u1) (substitution_update rho2 x u2).
Proof.
  intros Gamma rho1 rho2 x A u1 u2 Henv Hu1 Hu2 Hrel y T Hlook.
  unfold update, substitution_update in *. simpl in *.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlook; subst.
    simpl. rewrite Nat.eqb_refl. intros v1 v2 E1 E2.
    assert (v1 = u1) by (eapply big_step_value_inv; eauto).
    assert (v2 = u2) by (eapply big_step_value_inv; eauto).
    subst. exact Hrel.
  - apply Nat.eqb_neq in E.
    assert (E' : Nat.eqb x y = false) by (apply Nat.eqb_neq; congruence).
    rewrite E' in *. eapply Henv; eauto.
Qed.

Lemma substitution_values_update : forall rho x u,
  substitution_values rho -> locally_closed u ->
  substitution_values (substitution_update rho x u).
Proof.
  intros rho x u Hrho Hu y. unfold substitution_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma instantiate_open_update : forall rho x a body,
  substitution_values rho -> value a -> ~ In x (fv body) ->
  instantiate (substitution_update rho x a) (open body (tm_fvar x)) =
  open (instantiate rho body) a.
Proof.
  intros rho x a body Hrho Ha Haway. unfold open.
  rewrite instantiate_open_rec.
  2:{ apply substitution_values_lc. eapply substitution_values_update;
      [exact Hrho|apply value_locally_closed; exact Ha]. }
  simpl.
  assert (Hx : substitution_update rho x a x = a).
  { unfold substitution_update. simpl. rewrite Nat.eqb_refl. reflexivity. }
  rewrite Hx.
  rewrite instantiate_update_away by exact Haway. reflexivity.
Qed.

Lemma protect_value_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l Hv. induction Hv; destruct l; simpl; constructor; auto.
Qed.

Lemma big_step_value : forall t v,
  big_step t v -> value v.
Proof.
  intros t v H. induction H; try constructor; eauto using protect_value_value.
  - inversion IHbig_step; subst. apply protect_value_value. assumption.
  - inversion IHbig_step; subst. apply protect_value_value. assumption.
Qed.

Lemma big_step_case_inv : forall c b1 b2 r z,
  big_step (tm_case c b1 b2 r) z ->
  (exists v k w, big_step c (tm_inl v k) /\ flows_to k.(reader) r /\
      big_step (open b1 v) w /\ z = protect_value w k.(indirect_reader)) \/
  (exists v k w, big_step c (tm_inr v k) /\ flows_to k.(reader) r /\
      big_step (open b2 v) w /\ z = protect_value w k.(indirect_reader)).
Proof.
  intros c b1 b2 r z H. inversion H; subst.
  - left. exists v, k, w. repeat split; assumption.
  - right. exists v, k, w. repeat split; assumption.
Qed.

Lemma big_step_app_inv : forall f a r z,
  big_step (tm_app f a r) z ->
  exists A body k va raw,
    big_step f (tm_abs A body k) /\ big_step a va /\
    flows_to k.(reader) r /\ big_step (open body va) raw /\
    z = protect_value raw k.(indirect_reader).
Proof.
  intros f a r z H. inversion H; subst.
  do 5 eexists. repeat split; eauto.
Qed.

Lemma big_step_if_inv : forall c yes no r z,
  big_step (tm_if c yes no r) z ->
  (exists v k result,
      big_step c (tm_inl v k) /\ flows_to k.(reader) r /\
      big_step yes result /\ z = protect_value result k.(indirect_reader)) \/
  (exists v k result,
      big_step c (tm_inr v k) /\ flows_to k.(reader) r /\
      big_step no result /\ z = protect_value result k.(indirect_reader)).
Proof.
  intros c yes no r z H. inversion H; subst.
  - left. do 3 eexists. repeat split; eauto.
  - right. do 3 eexists. repeat split; eauto.
Qed.

Lemma security_le_indirect_low : forall a b,
  security_le a b -> indirect_reader b = Low -> indirect_reader a = Low.
Proof.
  intros [ra ia] [rb ib] [_ Hflow] Hlow. simpl in *.
  destruct ia, ib; simpl in *; intuition.
Qed.

Lemma value_rel_inl_inv : forall A B k a b ka kb,
  indirect_reader k = Low ->
  value_rel (Ty_Sum A B k) (tm_inl a ka) (tm_inl b kb) ->
  security_le ka k /\ security_le kb k /\ value_rel A a b.
Proof.
  intros A B k a b ka kb Hlow Hrel. unfold value_rel in Hrel.
  rewrite Hlow in Hrel. simpl in Hrel. destruct Hrel as [Hl|Hr].
  - destruct Hl as [a' [b' [k1 [k2 [E1 [E2 [S1 [S2 H]]]]]]]].
    inversion E1; inversion E2; subst. exact (conj S1 (conj S2 H)).
  - destruct Hr as [a' [b' [k1 [k2 [E1 [E2 _]]]]]]. discriminate.
Qed.

Lemma value_rel_inr_inv : forall A B k a b ka kb,
  indirect_reader k = Low ->
  value_rel (Ty_Sum A B k) (tm_inr a ka) (tm_inr b kb) ->
  security_le ka k /\ security_le kb k /\ value_rel B a b.
Proof.
  intros A B k a b ka kb Hlow Hrel. unfold value_rel in Hrel.
  rewrite Hlow in Hrel. simpl in Hrel. destruct Hrel as [Hl|Hr].
  - destruct Hl as [a' [b' [k1 [k2 [E1 [E2 _]]]]]]. discriminate.
  - destruct Hr as [a' [b' [k1 [k2 [E1 [E2 [S1 [S2 H]]]]]]]].
    inversion E1; inversion E2; subst. exact (conj S1 (conj S2 H)).
Qed.

Lemma big_step_abs_self : forall f A body k,
  big_step f (tm_abs A body k) ->
  big_step (tm_abs A body k) (tm_abs A body k).
Proof.
  intros f A body k H. pose proof (big_step_value _ _ H) as Hv.
  inversion Hv; subst. constructor; assumption.
Qed.

Lemma big_step_value_self : forall v,
  value v -> big_step v v.
Proof.
  intros v Hv. induction Hv.
  - constructor.
  - constructor. assumption.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - constructor.
Qed.

Lemma natrec_unroll_rel : forall T n b1 b2 s1 s2 r z1 z2,
  value b1 -> value b2 -> value s1 -> value s2 ->
  value_rel T b1 b2 ->
  value_rel (Ty_Arrow (Ty_Nat public)
    (Ty_Arrow T T public) public) s1 s2 ->
  big_step (natrec_unroll n b1 s1 r) z1 ->
  big_step (natrec_unroll n b2 s2 r) z2 ->
  value_rel T z1 z2.
Proof.
  intros T n. induction n; intros b1 b2 s1 s2 r z1 z2 Hb1 Hb2 Hs1 Hs2 Hbase Hstep E1 E2.
  - simpl in E1, E2.
    assert (z1 = b1) by (eapply big_step_value_inv; eauto).
    assert (z2 = b2) by (eapply big_step_value_inv; eauto).
    subst. exact Hbase.
  - simpl in E1, E2.
    destruct (big_step_app_inv _ _ _ _ E1)
      as [A1 [body1 [k1 [arg1 [raw1 [Ef1 [Ea1 [Fl1 [Eb1 Eq1]]]]]]]]].
    destruct (big_step_app_inv _ _ _ _ E2)
      as [A2 [body2 [k2 [arg2 [raw2 [Ef2 [Ea2 [Fl2 [Eb2 Eq2]]]]]]]]].
    assert (Hnat : value_rel (Ty_Nat public)
      (tm_nat n public) (tm_nat n public)).
    { simpl. exists n, public, public. repeat split; try reflexivity; apply security_le_refl. }
    assert (Hinner : value_rel (Ty_Arrow T T public)
      (tm_abs A1 body1 k1) (tm_abs A2 body2 k2)).
    { change (value_rel (ty_protect (indirect_reader public)
          (Ty_Arrow T T public)) (tm_abs A1 body1 k1) (tm_abs A2 body2 k2)).
      eapply (value_rel_app (Ty_Nat public) (Ty_Arrow T T public) public
        s1 s2 (tm_nat n public) (tm_nat n public) r
        (tm_abs A1 body1 k1) (tm_abs A2 body2 k2)).
      - exact Hstep.
      - constructor.
      - constructor.
      - exact Hnat.
      - exact Ef1.
      - exact Ef2. }
    assert (Harg1 : value arg1) by (eapply big_step_value; exact Ea1).
    assert (Harg2 : value arg2) by (eapply big_step_value; exact Ea2).
    assert (Hrec : value_rel T arg1 arg2).
    { eapply (IHn b1 b2 s1 s2 r arg1 arg2);
        [exact Hb1|exact Hb2|exact Hs1|exact Hs2|exact Hbase|exact Hstep|exact Ea1|exact Ea2]. }
    assert (Eapp1 : big_step (tm_app (tm_abs A1 body1 k1) arg1 r) z1).
    { rewrite Eq1. econstructor;
        [eapply big_step_abs_self; exact Ef1|apply big_step_value_self; exact Harg1|
         exact Fl1|exact Eb1]. }
    assert (Eapp2 : big_step (tm_app (tm_abs A2 body2 k2) arg2 r) z2).
    { rewrite Eq2. econstructor;
        [eapply big_step_abs_self; exact Ef2|apply big_step_value_self; exact Harg2|
         exact Fl2|exact Eb2]. }
    assert (Hout : value_rel (ty_protect (indirect_reader public) T) z1 z2).
    { eapply (value_rel_app T T public (tm_abs A1 body1 k1) (tm_abs A2 body2 k2)
        arg1 arg2 r z1 z2).
      - exact Hinner.
      - exact Harg1.
      - exact Harg2.
      - exact Hrec.
      - exact Eapp1.
      - exact Eapp2. }
    unfold public in Hout. simpl in Hout. rewrite ty_protect_low in Hout.
    exact Hout.
Qed.

Lemma step_big_step_back : forall t t' v,
  step t t' -> big_step t' v -> big_step t v.
Proof.
  intros t t' z Hstep. revert z. induction Hstep; intros z Hbig.
  - inversion Hbig; subst. eapply B_App.
    + apply big_step_value_self. exact H.
    + apply big_step_value_self. exact H0.
    + exact H1.
    + assumption.
  - inversion Hbig; subst. eapply B_App.
    + eapply IHHstep; eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
  - inversion Hbig; subst. eapply B_App.
    + eassumption.
    + eapply IHHstep; eassumption.
    + eassumption.
    + eassumption.
  - inversion Hbig; subst. eapply B_Pair; [eapply IHHstep; eassumption|eassumption].
  - inversion Hbig; subst. eapply B_Pair; [eassumption|eapply IHHstep; eassumption].
  - inversion Hbig; subst.
    assert (v = v1) by (eapply big_step_value_inv; eauto). subst v.
    eapply B_Fst.
    + eapply B_Pair.
      * apply big_step_value_self. exact H.
      * apply big_step_value_self. exact H0.
    + assumption.
  - inversion Hbig; subst. eapply B_Fst; [eapply IHHstep; eassumption|eassumption].
  - inversion Hbig; subst.
    assert (v = v2) by (eapply big_step_value_inv; eauto). subst v.
    eapply B_Snd.
    + eapply B_Pair.
      * apply big_step_value_self. exact H.
      * apply big_step_value_self. exact H0.
    + assumption.
  - inversion Hbig; subst. eapply B_Snd; [eapply IHHstep; eassumption|eassumption].
  - inversion Hbig; subst. eapply B_Inl. eapply IHHstep; eassumption.
  - inversion Hbig; subst. eapply B_Inr. eapply IHHstep; eassumption.
  - inversion Hbig; subst. eapply B_CaseLeft.
    + apply B_Inl. apply big_step_value_self. assumption.
    + assumption.
    + assumption.
  - inversion Hbig; subst. eapply B_CaseRight.
    + apply B_Inr. apply big_step_value_self. assumption.
    + assumption.
    + assumption.
  - inversion Hbig; subst.
    + eapply B_CaseLeft; [eapply IHHstep; eassumption|eassumption|eassumption].
    + eapply B_CaseRight; [eapply IHHstep; eassumption|eassumption|eassumption].
  - assert (z = protect_value v l).
    { eapply big_step_value_inv; [apply protect_value_value; exact H|exact Hbig]. }
    subst z. apply B_Protect. apply big_step_value_self. exact H.
  - inversion Hbig; subst. apply B_Protect. eapply IHHstep; eassumption.
  - inversion Hbig; subst. eapply B_Succ; [eapply IHHstep; eassumption|eassumption].
  - inversion Hbig; subst.
    assert (v = tm_nat (S n) public).
    { eapply big_step_value_inv; [constructor|exact H3]. }
    subst v. eapply B_Succ.
    + apply B_Nat.
    + assumption.
  - inversion Hbig; subst. eapply B_NatRec.
    + eapply IHHstep; eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
  - inversion Hbig; subst.
    assert (Hcount : tm_nat m k0 = tm_nat n k)
      by (eapply big_step_value_inv; [constructor|exact H3]).
    inversion Hcount; subst m k0.
    eapply B_NatRec.
    + apply B_Nat.
    + eapply IHHstep; eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
  - inversion Hbig; subst.
    assert (Hcount : tm_nat m k0 = tm_nat n k)
      by (eapply big_step_value_inv; [constructor|exact H4]).
    inversion Hcount; subst m k0.
    eapply B_NatRec.
    + apply B_Nat.
    + eassumption.
    + eapply IHHstep; eassumption.
    + eassumption.
    + eassumption.
  - inversion Hbig; subst. eapply B_NatRec.
    + apply B_Nat.
    + apply big_step_value_self. exact H.
    + apply big_step_value_self. exact H0.
    + exact H1.
    + assumption.
  - inversion Hbig; subst.
    + eapply B_IfTrue; [eapply IHHstep; eassumption|eassumption|eassumption].
    + eapply B_IfFalse; [eapply IHHstep; eassumption|eassumption|eassumption].
  - inversion Hbig; subst. eapply B_IfTrue.
    + apply B_Inl. apply big_step_value_self. assumption.
    + assumption.
    + assumption.
  - inversion Hbig; subst. eapply B_IfFalse.
    + apply B_Inr. apply big_step_value_self. assumption.
    + assumption.
    + assumption.
Qed.

Lemma evaluates_big_step : forall t v,
  evaluates t v -> big_step t v.
Proof.
  intros t v [Hmulti Hv]. induction Hmulti.
  - subst. apply big_step_value_self. exact Hv.
  - eapply step_big_step_back; [exact H|apply IHHmulti; exact Hv].
Qed.

Lemma value_rel_high_gate : forall T v w,
  (security_of T).(indirect_reader) = High -> value_rel T v w.
Proof.
  destruct T; simpl; intros v w H; rewrite H; exact I.
Qed.

Lemma value_rel_erase_ground : forall T,
  ground T -> all_indirect_low T -> forall v w,
  value_rel T v w -> erase_security v = erase_security w.
Proof.
  induction T as [k|A IHA B IHB k|A IHA B IHB k|A IHA B IHB k|k];
    simpl; intros Hground Hlow v w Hrel.
  - rewrite Hlow in Hrel. simpl in Hrel.
    destruct Hrel as [k1 [k2 [-> ->]]]. reflexivity.
  - destruct Hground as [Hga Hgb]. destruct Hlow as [Hk [Ha Hb]].
    rewrite Hk in Hrel. simpl in Hrel. destruct Hrel as [Hl|Hr].
    + destruct Hl as [a [b [ka [kb [-> [-> [_ [_ Hab]]]]]]]].
      simpl. f_equal. eapply IHA; eauto.
    + destruct Hr as [a [b [ka [kb [-> [-> [_ [_ Hab]]]]]]]].
      simpl. f_equal. eapply IHB; eauto.
  - destruct Hground as [Hga Hgb]. destruct Hlow as [Hk [Ha Hb]].
    rewrite Hk in Hrel. simpl in Hrel.
    destruct Hrel as [a1 [a2 [b1 [b2 [ka [kb [-> [-> [_ [_ [HaRel HbRel]]]]]]]]]]].
    simpl. f_equal; [eapply IHA|eapply IHB]; eauto.
  - destruct Hground as [].
  - rewrite Hlow in Hrel. simpl in Hrel.
    destruct Hrel as [n [ka [kb [-> [-> [_ _]]]]]]. reflexivity.
Qed.

Definition identity_substitution : term_substitution := fun x => tm_fvar x.

Lemma instantiate_identity : forall t,
  instantiate identity_substitution t = t.
Proof.
  induction t; simpl; try f_equal; auto.
Qed.

Lemma instantiate_update_away_identity : forall x u t,
  ~ In x (fv t) ->
  instantiate (substitution_update identity_substitution x u) t = t.
Proof.
  intros x u t Haway. rewrite instantiate_update_away by exact Haway.
  apply instantiate_identity.
Qed.

Lemma instantiate_update_plug : forall C x u,
  ~ In x (fv (plug C (tm_unit public))) ->
  instantiate (substitution_update identity_substitution x u)
      (plug C (tm_fvar x)) = plug C u.
Proof.
  induction C; intros x u Hfresh; simpl in *.
  - unfold substitution_update. simpl. rewrite Nat.eqb_refl. reflexivity.
  - f_equal. apply IHC. exact Hfresh.
  - apply not_in_app in Hfresh as [Hc Ht]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact Ht. reflexivity.
  - apply not_in_app in Hfresh as [Ht Hc]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact Ht. reflexivity.
  - apply not_in_app in Hfresh as [Hc Ht]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact Ht. reflexivity.
  - apply not_in_app in Hfresh as [Ht Hc]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact Ht. reflexivity.
  - f_equal. apply IHC. exact Hfresh.
  - f_equal. apply IHC. exact Hfresh.
  - f_equal. apply IHC. exact Hfresh.
  - f_equal. apply IHC. exact Hfresh.
  - apply not_in_app in Hfresh as [Hc H12].
    apply not_in_app in H12 as [H1 H2]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact H1.
    rewrite instantiate_update_away_identity by exact H2. reflexivity.
  - apply not_in_app in Hfresh as [H0 H12].
    apply not_in_app in H12 as [Hc H2]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact H0.
    rewrite instantiate_update_away_identity by exact H2. reflexivity.
  - apply not_in_app in Hfresh as [H0 H12].
    apply not_in_app in H12 as [H1 Hc]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact H0.
    rewrite instantiate_update_away_identity by exact H1. reflexivity.
  - f_equal. apply IHC. exact Hfresh.
  - f_equal. apply IHC. exact Hfresh.
  - apply not_in_app in Hfresh as [Hc H12].
    apply not_in_app in H12 as [H1 H2]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact H1.
    rewrite instantiate_update_away_identity by exact H2. reflexivity.
  - apply not_in_app in Hfresh as [H0 H12].
    apply not_in_app in H12 as [Hc H2]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact H0.
    rewrite instantiate_update_away_identity by exact H2. reflexivity.
  - apply not_in_app in Hfresh as [H0 H12].
    apply not_in_app in H12 as [H1 Hc]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact H0.
    rewrite instantiate_update_away_identity by exact H1. reflexivity.
  - apply not_in_app in Hfresh as [Hc H12].
    apply not_in_app in H12 as [H1 H2]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact H1.
    rewrite instantiate_update_away_identity by exact H2. reflexivity.
  - apply not_in_app in Hfresh as [H0 H12].
    apply not_in_app in H12 as [Hc H2]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact H0.
    rewrite instantiate_update_away_identity by exact H2. reflexivity.
  - apply not_in_app in Hfresh as [H0 H12].
    apply not_in_app in H12 as [H1 Hc]. simpl.
    rewrite (IHC x u Hc).
    rewrite instantiate_update_away_identity by exact H0.
    rewrite instantiate_update_away_identity by exact H1. reflexivity.
Qed.

Lemma security_le_trans : forall a b c,
  security_le a b -> security_le b c -> security_le a c.
Proof.
  intros [ar ai] [br bi] [cr ci] [H1 H2] [H3 H4]. split;
    eapply flows_to_trans; eassumption.
Qed.

Lemma value_rel_subtype : forall T U,
  subtype T U -> forall v w, value_rel T v w -> value_rel U v w.
Proof.
  intros T U Hsub. induction Hsub; intros v w Hrel; simpl in *.
  - destruct kappa1 as [r1 i1], kappa2 as [r2 i2].
    destruct i1, i2; unfold security_le in *; simpl in *; try exact I;
      try (destruct H1 as [_ Hbad]; contradiction); exact Hrel.
  - destruct kappa1 as [r1 i1], kappa2 as [r2 i2].
    destruct i1, i2; unfold security_le in *; simpl in *; try exact I;
      try (destruct H1 as [_ Hbad]; contradiction).
    destruct Hrel as [Hleft|Hright].
    + destruct Hleft as [a [b [ka [kb [Eq1 [Eq2 [S1 [S2 Hab]]]]]]]].
      subst v w. left. exists a, b, ka, kb.
      split; [reflexivity|]. split; [reflexivity|]. split.
      * unfold security_le; simpl. split;
          [eapply flows_to_trans; [exact (proj1 S1)|exact (proj1 H1)]|
           exact (proj2 S1)].
      * split.
        -- unfold security_le; simpl. split;
             [eapply flows_to_trans; [exact (proj1 S2)|exact (proj1 H1)]|
              exact (proj2 S2)].
        -- eapply IHHsub1; exact Hab.
    + destruct Hright as [a [b [ka [kb [Eq1 [Eq2 [S1 [S2 Hab]]]]]]]].
      subst v w. right. exists a, b, ka, kb.
      split; [reflexivity|]. split; [reflexivity|]. split.
      * unfold security_le; simpl. split;
          [eapply flows_to_trans; [exact (proj1 S1)|exact (proj1 H1)]|
           exact (proj2 S1)].
      * split.
        -- unfold security_le; simpl. split;
             [eapply flows_to_trans; [exact (proj1 S2)|exact (proj1 H1)]|
              exact (proj2 S2)].
        -- eapply IHHsub2; exact Hab.
  - destruct kappa1 as [r1 i1], kappa2 as [r2 i2].
    destruct i1, i2; unfold security_le in *; simpl in *; try exact I;
      try (destruct H1 as [_ Hbad]; contradiction).
    destruct Hrel as [a1 [a2 [b1 [b2 [ka [kb [-> [-> [S1 [S2 [Hleft Hright]]]]]]]]]]].
    exists a1, a2, b1, b2, ka, kb.
    split; [reflexivity|]. split; [reflexivity|]. split.
    + unfold security_le; simpl. split;
        [eapply flows_to_trans; [exact (proj1 S1)|exact (proj1 H1)]|
         exact (proj2 S1)].
    + split.
      * unfold security_le; simpl. split;
          [eapply flows_to_trans; [exact (proj1 S2)|exact (proj1 H1)]|
           exact (proj2 S2)].
      * split; [eapply IHHsub1; exact Hleft|eapply IHHsub2; exact Hright].
  - destruct kappa1 as [r1 i1], kappa2 as [r2 i2].
    destruct i1, i2; unfold security_le in *; simpl in *; try exact I;
      try (destruct H1 as [_ Hbad]; contradiction).
    destruct Hrel as [A1 [A2 [body1 [body2 [ka [kb [Eq1 [Eq2 [S1 [S2 Hfun]]]]]]]]]].
    exists A1, A2, body1, body2, ka, kb.
    rewrite Eq1, Eq2.
    split; [reflexivity|]. split; [reflexivity|]. split.
    + unfold security_le; simpl. split;
        [eapply flows_to_trans; [exact (proj1 S1)|exact (proj1 H1)]|
         exact (proj2 S1)].
    + split.
      * unfold security_le; simpl. split;
          [eapply flows_to_trans; [exact (proj1 S2)|exact (proj1 H1)]|
           exact (proj2 S2)].
      * intros a b va vb Hva Hvb Hab Ea Eb.
        eapply IHHsub2. eapply Hfun; [exact Hva|exact Hvb|eapply IHHsub1; exact Hab|exact Ea|exact Eb].
  - eapply IHHsub2. eapply IHHsub1. exact Hrel.
  - destruct k1 as [r1 i1], k2 as [r2 i2].
    destruct i1, i2; unfold security_le in *; simpl in *; try exact I;
      try (destruct H1 as [_ Hbad]; contradiction).
    destruct Hrel as [n [ka [kb [-> [-> [S1 S2]]]]]].
    exists n, ka, kb. split; [reflexivity|]. split; [reflexivity|]. split.
    + unfold security_le; simpl. split;
        [eapply flows_to_trans; [exact (proj1 S1)|exact (proj1 H1)]|
         exact (proj2 S1)].
    + unfold security_le; simpl. split;
        [eapply flows_to_trans; [exact (proj1 S2)|exact (proj1 H1)]|
         exact (proj2 S2)].
Qed.

Lemma fundamental_relation : forall Gamma t T,
  has_type Gamma t T -> forall rho1 rho2,
  env_rel Gamma rho1 rho2 -> substitution_values rho1 -> substitution_values rho2 ->
  forall v1 v2,
    big_step (instantiate rho1 t) v1 ->
    big_step (instantiate rho2 t) v2 ->
    value_rel T v1 v2.
Proof.
  intros Gamma t T Hty. induction Hty;
    intros rho1 rho2 Henv Hvals1 Hvals2 v1 v2 E1 E2; simpl in *.
  - eapply Henv; eauto.
  - inversion E1; subst. inversion E2; subst.
    destruct (indirect_reader kappa); simpl.
    + eexists; eexists; split; reflexivity.
    + exact I.
  - inversion E1; subst. inversion E2; subst.
    destruct (indirect_reader kappa); simpl.
    + exists T1, T1, (instantiate rho1 body), (instantiate rho2 body), kappa, kappa.
      split; [reflexivity|]. split; [reflexivity|].
      split; [apply security_le_refl|]. split; [apply security_le_refl|].
      intros a b va vb Hva Hvb Harg Eb1 Eb2.
      destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
      apply not_in_app in Hfresh as [HxL HxFV].
      pose proof (env_rel_update Gamma rho1 rho2 x T1 a b Henv Hva Hvb Harg) as Henv'.
      pose proof (substitution_values_update rho1 x a Hvals1 (value_locally_closed a Hva)) as Hvals1'.
      pose proof (substitution_values_update rho2 x b Hvals2 (value_locally_closed b Hvb)) as Hvals2'.
      rewrite <- (instantiate_open_update rho1 x a body Hvals1 Hva HxFV) in Eb1.
      rewrite <- (instantiate_open_update rho2 x b body Hvals2 Hvb HxFV) in Eb2.
      eapply H2; eauto.
    + exact I.
  - inversion E1; subst. inversion E2; subst.
    destruct (indirect_reader kappa) eqn:Htype.
    + pose proof (IHHty1 rho1 rho2 Henv Hvals1 Hvals2
        (tm_abs A body k) (tm_abs A0 body0 k0) H3 H5) as Hfr.
      destruct Hfr as [A1 [A2 [body1 [body2 [ka [kb [Efr1 [Efr2 [Hka [Hkb Hfun]]]]]]]]]].
      injection Efr1 as HA Hb Hkaeq. injection Efr2 as HA0 Hb0 Hkbeq.
      subst A A0 body body0 k k0.
      pose proof (IHHty2 rho1 rho2 Henv Hvals1 Hvals2 v v0 H4 H8) as Harg.
      assert (Hraw : value_rel T2 w w0).
      { eapply Hfun; [eapply big_step_value; exact H4|eapply big_step_value; exact H8|
          exact Harg|exact H7|exact H11]. }
      destruct Hka as [_ Hka]. destruct Hkb as [_ Hkb].
      rewrite Htype in Hka, Hkb.
      eapply value_rel_protect_le; [exact Hka|exact Hkb|exact Hraw].
    + apply value_rel_high.
  - inversion E1; subst. inversion E2; subst.
    pose proof (IHHty1 rho1 rho2 Henv Hvals1 Hvals2 v v0 H4 H6) as Hleft.
    pose proof (IHHty2 rho1 rho2 Henv Hvals1 Hvals2 w w0 H5 H7) as Hright.
    destruct (indirect_reader kappa); simpl.
    + exists v, w, v0, w0, kappa, kappa.
      repeat split; try reflexivity; try apply security_le_refl; assumption.
    + exact I.
  - inversion E1; subst. inversion E2; subst.
    destruct (indirect_reader kappa) eqn:Htype.
    + pose proof (IHHty rho1 rho2 Henv Hvals1 Hvals2
        (tm_pair a b k) (tm_pair a0 b0 k0) H2 H3) as Hpair.
      destruct Hpair as [a1 [a2 [b1 [b2 [k1 [k2 [Heq1 [Heq2 [Hsec1 [Hsec2 [Hrel1 Hrel2]]]]]]]]]]].
      inversion Heq1; subst a1 a2 k1. inversion Heq2; subst b1 b2 k2.
      destruct Hsec1 as [_ Hsec1]. destruct Hsec2 as [_ Hsec2].
      rewrite Htype in Hsec1, Hsec2.
      eapply value_rel_protect_le; [exact Hsec1|exact Hsec2|exact Hrel1].
    + apply value_rel_high.
  - inversion E1; subst. inversion E2; subst.
    destruct (indirect_reader kappa) eqn:Htype.
    + pose proof (IHHty rho1 rho2 Henv Hvals1 Hvals2
        (tm_pair a b k) (tm_pair a0 b0 k0) H2 H3) as Hpair.
      destruct Hpair as [a1 [a2 [b1 [b2 [k1 [k2 [Heq1 [Heq2 [Hsec1 [Hsec2 [Hrel1 Hrel2]]]]]]]]]]].
      inversion Heq1; subst a1 a2 k1. inversion Heq2; subst b1 b2 k2.
      destruct Hsec1 as [_ Hsec1]. destruct Hsec2 as [_ Hsec2].
      rewrite Htype in Hsec1, Hsec2.
      eapply value_rel_protect_le; [exact Hsec1|exact Hsec2|exact Hrel2].
    + apply value_rel_high.
  - inversion E1; subst. inversion E2; subst.
    pose proof (IHHty rho1 rho2 Henv Hvals1 Hvals2 v v0 H4 H5) as Harg.
    destruct (indirect_reader kappa); simpl.
    + left. exists v, v0, kappa, kappa. repeat split; try reflexivity;
        try apply security_le_refl; assumption.
    + exact I.
  - inversion E1; subst. inversion E2; subst.
    pose proof (IHHty rho1 rho2 Henv Hvals1 Hvals2 v v0 H4 H5) as Harg.
    destruct (indirect_reader kappa); simpl.
    + right. exists v, v0, kappa, kappa. repeat split; try reflexivity;
        try apply security_le_refl; assumption.
    + exact I.
  - destruct (big_step_case_inv _ _ _ _ _ E1) as [Hcase1|Hcase1].
    + destruct Hcase1 as [a [ka [wa [Ec1 [Fl1 [Eb1 Ez1]]]]]]. subst v1.
      destruct (big_step_case_inv _ _ _ _ _ E2) as [Hcase2|Hcase2].
      * destruct Hcase2 as [b [kb [wb [Ec2 [Fl2 [Eb2 Ez2]]]]]]. subst v2.
        pose proof (IHHty rho1 rho2 Henv Hvals1 Hvals2
          (tm_inl a ka) (tm_inl b kb) Ec1 Ec2) as Hcond.
        destruct (indirect_reader kappa) eqn:Htype in Hcond |- *.
        -- destruct Hcond as [Hsame|Hother].
           ++ destruct Hsame as [a' [b' [k1 [k2 [Eq1 [Eq2 [S1 [S2 Hp]]]]]]]].
              inversion Eq1; subst a' k1. inversion Eq2; subst b' k2.
              destruct (fresh_atom (L ++ fv body1)) as [x Hfresh].
              apply not_in_app in Hfresh as [HxL HxFV].
              assert (Ha : value a) by (pose proof (big_step_value _ _ Ec1) as Q; inversion Q; assumption).
              assert (Hb : value b) by (pose proof (big_step_value _ _ Ec2) as Q; inversion Q; assumption).
              pose proof (env_rel_update Gamma rho1 rho2 x T1 a b Henv Ha Hb Hp) as Henv'.
              pose proof (substitution_values_update rho1 x a Hvals1 (value_locally_closed a Ha)) as Hv1'.
              pose proof (substitution_values_update rho2 x b Hvals2 (value_locally_closed b Hb)) as Hv2'.
              rewrite <- (instantiate_open_update rho1 x a body1 Hvals1 Ha HxFV) in Eb1.
              rewrite <- (instantiate_open_update rho2 x b body1 Hvals2 Hb HxFV) in Eb2.
              pose proof (H1 x HxL _ _ Henv' Hv1' Hv2' wa wb Eb1 Eb2) as Hraw.
              destruct S1 as [_ S1]. destruct S2 as [_ S2].
              rewrite Htype in S1, S2.
              eapply value_rel_protect_le; eauto.
           ++ destruct Hother as [a' [b' [k1 [k2 [Eq1 [Eq2 _]]]]]]. discriminate.
        -- apply value_rel_high.
      * destruct Hcase2 as [b [kb [wb [Ec2 [Fl2 [Eb2 Ez2]]]]]]. subst v2.
        pose proof (IHHty rho1 rho2 Henv Hvals1 Hvals2
          _ _ Ec1 Ec2) as Hcond.
        destruct (indirect_reader kappa) eqn:Htype in Hcond |- *.
        -- destruct Hcond as [Hl|Hr].
           ++ destruct Hl as [a' [b' [k1 [k2 [Eq1 [Eq2 _]]]]]]. discriminate.
           ++ destruct Hr as [a' [b' [k1 [k2 [Eq1 [Eq2 _]]]]]]. discriminate.
        -- apply value_rel_high.
    + destruct Hcase1 as [a [ka [wa [Ec1 [Fl1 [Eb1 Ez1]]]]]]. subst v1.
      destruct (big_step_case_inv _ _ _ _ _ E2) as [Hcase2|Hcase2].
      * destruct Hcase2 as [b [kb [wb [Ec2 [Fl2 [Eb2 Ez2]]]]]]. subst v2.
        pose proof (IHHty rho1 rho2 Henv Hvals1 Hvals2 _ _ Ec1 Ec2) as Hcond.
        destruct (indirect_reader kappa) eqn:Htype in Hcond |- *.
        -- destruct Hcond as [Hl|Hr].
           ++ destruct Hl as [a' [b' [k1 [k2 [Eq1 [Eq2 _]]]]]]. discriminate.
           ++ destruct Hr as [a' [b' [k1 [k2 [Eq1 [Eq2 _]]]]]]. discriminate.
        -- apply value_rel_high.
      * destruct Hcase2 as [b [kb [wb [Ec2 [Fl2 [Eb2 Ez2]]]]]]. subst v2.
        pose proof (IHHty rho1 rho2 Henv Hvals1 Hvals2
          (tm_inr a ka) (tm_inr b kb) Ec1 Ec2) as Hcond.
        destruct (indirect_reader kappa) eqn:Htype in Hcond |- *.
        -- destruct Hcond as [Hother|Hsame].
           ++ destruct Hother as [a' [b' [k1 [k2 [Eq1 [Eq2 _]]]]]]. discriminate.
           ++ destruct Hsame as [a' [b' [k1 [k2 [Eq1 [Eq2 [S1 [S2 Hp]]]]]]]].
              inversion Eq1; subst a' k1. inversion Eq2; subst b' k2.
              destruct (fresh_atom (L ++ fv body2)) as [x Hfresh].
              apply not_in_app in Hfresh as [HxL HxFV].
              assert (Ha : value a) by (pose proof (big_step_value _ _ Ec1) as Q; inversion Q; assumption).
              assert (Hb : value b) by (pose proof (big_step_value _ _ Ec2) as Q; inversion Q; assumption).
              pose proof (env_rel_update Gamma rho1 rho2 x T2 a b Henv Ha Hb Hp) as Henv'.
              pose proof (substitution_values_update rho1 x a Hvals1 (value_locally_closed a Ha)) as Hv1'.
              pose proof (substitution_values_update rho2 x b Hvals2 (value_locally_closed b Hb)) as Hv2'.
              rewrite <- (instantiate_open_update rho1 x a body2 Hvals1 Ha HxFV) in Eb1.
              rewrite <- (instantiate_open_update rho2 x b body2 Hvals2 Hb HxFV) in Eb2.
              pose proof (H3 x HxL _ _ Henv' Hv1' Hv2' wa wb Eb1 Eb2) as Hraw.
              destruct S1 as [_ S1]. destruct S2 as [_ S2].
              rewrite Htype in S1, S2.
              eapply value_rel_protect_le; eauto.
        -- apply value_rel_high.
  - inversion E1; subst. inversion E2; subst.
    eapply value_rel_protect; eauto.
  - pose proof (IHHty rho1 rho2 Henv Hvals1 Hvals2 v1 v2 E1 E2) as Hraw.
    eapply value_rel_subtype; eauto.
  - inversion E1; subst. inversion E2; subst.
    destruct (indirect_reader k); simpl.
    + exists n, k, k. repeat split; try reflexivity; apply security_le_refl.
    + exact I.
  - inversion E1; subst. inversion E2; subst.
    pose proof (IHHty rho1 rho2 Henv Hvals1 Hvals2
      (tm_nat n k0) (tm_nat n0 k1) H2 H3) as Hnums.
    destruct (indirect_reader k) eqn:Hir; simpl.
    + destruct Hnums as [nval [ka [kb [Eq1 [Eq2 [S1 S2]]]]]].
      inversion Eq1; inversion Eq2; subst.
      destruct ka as [ra ia], kb as [rb ib].
      unfold security_le in S1, S2; simpl in S1, S2.
      rewrite Hir in S1, S2.
      destruct ia; simpl in S1.
      destruct ib; simpl in S2.
      all: try (destruct S1 as [_ Hbad]; contradiction).
      all: try (destruct S2 as [_ Hbad]; contradiction).
      simpl. exists (S nval), public, public.
      split; [reflexivity|]. split; [reflexivity|]. split;
        apply security_le_refl.
    + exact I.
  - inversion E1; subst. inversion E2; subst.
    destruct (indirect_reader k) eqn:Hir.
    + pose proof (IHHty1 rho1 rho2 Henv Hvals1 Hvals2
        (tm_nat m k0) (tm_nat m0 k1) H4 H6) as Hnums.
      destruct Hnums as [nval [ka [kb [Eq1 [Eq2 [S1 S2]]]]]].
      inversion Eq1; inversion Eq2; subst.
      assert (Hka : indirect_reader ka = Low).
      { unfold security_le in S1; simpl in S1. rewrite Hir in S1.
        destruct ka as [rr ii]; simpl in S1. destruct ii; [reflexivity|].
        destruct S1 as [_ Hbad]; contradiction. }
      assert (Hkb : indirect_reader kb = Low).
      { unfold security_le in S2; simpl in S2. rewrite Hir in S2.
        destruct kb as [rr ii]; simpl in S2. destruct ii; [reflexivity|].
        destruct S2 as [_ Hbad]; contradiction. }
      assert (Hbase : value_rel T vb vb0).
      { eapply IHHty2; eauto. }
      assert (Hstep : value_rel
        (Ty_Arrow (Ty_Nat public) (Ty_Arrow T T public) public) vs vs0).
      { eapply IHHty3; eauto. }
      assert (Hbv : value vb) by (eapply big_step_value; exact H5).
      assert (Hbv0 : value vb0) by (eapply big_step_value; exact H10).
      assert (Hsv : value vs) by (eapply big_step_value; exact H7).
      assert (Hsv0 : value vs0) by (eapply big_step_value; exact H12).
      pose proof (natrec_unroll_rel T nval vb vb0 vs vs0 r result result0
        Hbv Hbv0 Hsv Hsv0 Hbase Hstep H9 H14) as Hresult.
      rewrite Hka, Hkb, ty_protect_low, !protect_value_low.
      exact Hresult.
    + apply value_rel_high.
  - destruct (big_step_if_inv _ _ _ _ _ E1) as [Hif1|Hif1].
    + destruct Hif1 as [a [ka [wa [Ec1 [Fl1 [Ey1 Eq1]]]]]]. subst v1.
      destruct (big_step_if_inv _ _ _ _ _ E2) as [Hif2|Hif2].
      * destruct Hif2 as [b' [kb [wb [Ec2 [Fl2 [Ey2 Eq2]]]]]]. subst v2.
        pose proof (IHHty1 rho1 rho2 Henv Hvals1 Hvals2
          (tm_inl a ka) (tm_inl b' kb) Ec1 Ec2) as Hcond.
        change (value_rel (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
          (tm_inl a ka) (tm_inl b' kb)) in Hcond.
        destruct (indirect_reader k) eqn:Htype.
        -- pose proof (value_rel_inl_inv (Ty_Unit public) (Ty_Unit public)
             k a b' ka kb Htype Hcond) as [S1 [S2 Hp]].
           pose proof (IHHty2 rho1 rho2 Henv Hvals1 Hvals2 wa wb Ey1 Ey2) as Hraw.
           assert (Hka : indirect_reader ka = Low)
             by (eapply security_le_indirect_low; eauto).
           assert (Hkb : indirect_reader kb = Low)
             by (eapply security_le_indirect_low; eauto).
           rewrite Hka, Hkb, ty_protect_low, !protect_value_low. exact Hraw.
        -- apply value_rel_high.
      * destruct Hif2 as [b' [kb [wb [Ec2 [Fl2 [En2 Eq2]]]]]]. subst v2.
        pose proof (IHHty1 rho1 rho2 Henv Hvals1 Hvals2
          (tm_inl a ka) (tm_inr b' kb) Ec1 Ec2) as Hcond.
        change (value_rel (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
          (tm_inl a ka) (tm_inr b' kb)) in Hcond.
        destruct (indirect_reader k) eqn:Htype.
        -- unfold value_rel in Hcond. rewrite Htype in Hcond. simpl in Hcond.
           destruct Hcond as [Hl|Hr].
           ++ destruct Hl as [a' [b'' [k1 [k2 [EqL [EqR _]]]]]]. discriminate.
           ++ destruct Hr as [a' [b'' [k1 [k2 [EqL [EqR _]]]]]]. discriminate.
        -- apply value_rel_high.
    + destruct Hif1 as [a [ka [wa [Ec1 [Fl1 [En1 Eq1]]]]]]. subst v1.
      destruct (big_step_if_inv _ _ _ _ _ E2) as [Hif2|Hif2].
      * destruct Hif2 as [b' [kb [wb [Ec2 [Fl2 [Ey2 Eq2]]]]]]. subst v2.
        pose proof (IHHty1 rho1 rho2 Henv Hvals1 Hvals2
          (tm_inr a ka) (tm_inl b' kb) Ec1 Ec2) as Hcond.
        change (value_rel (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
          (tm_inr a ka) (tm_inl b' kb)) in Hcond.
        destruct (indirect_reader k) eqn:Htype.
        -- unfold value_rel in Hcond. rewrite Htype in Hcond. simpl in Hcond.
           destruct Hcond as [Hl|Hr].
           ++ destruct Hl as [a' [b'' [k1 [k2 [EqL [EqR _]]]]]]. discriminate.
           ++ destruct Hr as [a' [b'' [k1 [k2 [EqL [EqR _]]]]]]. discriminate.
        -- apply value_rel_high.
      * destruct Hif2 as [b' [kb [wb [Ec2 [Fl2 [En2 Eq2]]]]]]. subst v2.
        pose proof (IHHty1 rho1 rho2 Henv Hvals1 Hvals2
          (tm_inr a ka) (tm_inr b' kb) Ec1 Ec2) as Hcond.
        change (value_rel (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
          (tm_inr a ka) (tm_inr b' kb)) in Hcond.
        destruct (indirect_reader k) eqn:Htype.
        -- pose proof (value_rel_inr_inv (Ty_Unit public) (Ty_Unit public)
             k a b' ka kb Htype Hcond) as [S1 [S2 Hp]].
           pose proof (IHHty3 rho1 rho2 Henv Hvals1 Hvals2 wa wb En1 En2) as Hraw.
           assert (Hka : indirect_reader ka = Low)
             by (eapply security_le_indirect_low; eauto).
           assert (Hkb : indirect_reader kb = Low)
             by (eapply security_le_indirect_low; eauto).
           rewrite Hka, Hkb, ty_protect_low, !protect_value_low. exact Hraw.
        -- apply value_rel_high.
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
  intros C t1 t2 T_secret T_result Hty1 Hty2 Hctx Hground Htrans Hnot v1 v2 Heval1 Heval2.
  destruct (nonflow_to_low
    (security_of T_secret).(indirect_reader)
    (security_of T_result).(indirect_reader) Hnot) as [Hsecret Hresult].
  pose proof (transparent_indirect_low_gen T_result (security_of T_result)
    Htrans Hresult) as Hall.
  destruct Hctx as [L Hctx].
  destruct (fresh_atom (L ++ fv (plug C (tm_unit public)))) as [x Hfresh].
  apply not_in_app in Hfresh as [HxL HxC].
  pose proof (Hctx x HxL) as Hcty.
  assert (Hlc1 : locally_closed t1) by (eapply typing_lc; exact Hty1).
  assert (Hlc2 : locally_closed t2) by (eapply typing_lc; exact Hty2).
  set (rho1 := substitution_update identity_substitution x t1).
  set (rho2 := substitution_update identity_substitution x t2).
  assert (Hvals1 : substitution_values rho1).
  { intros y. unfold rho1, substitution_update, identity_substitution.
    destruct (Nat.eqb x y); simpl; [exact Hlc1|exact I]. }
  assert (Hvals2 : substitution_values rho2).
  { intros y. unfold rho2, substitution_update, identity_substitution.
    destruct (Nat.eqb x y); simpl; [exact Hlc2|exact I]. }
  assert (Henv : env_rel (update empty x T_secret) rho1 rho2).
  { intros y T Hlook. unfold update, empty in Hlook. simpl in Hlook.
    destruct (Nat.eqb y x) eqn:Heq; [|discriminate].
    apply Nat.eqb_eq in Heq. subst y. inversion Hlook; subst T.
    unfold rho1, rho2, substitution_update, identity_substitution.
    simpl. rewrite Nat.eqb_refl. intros u w Eu Ew.
    eapply value_rel_high_gate. exact Hsecret. }
  pose proof (instantiate_update_plug C x t1 HxC) as Eplug1.
  pose proof (instantiate_update_plug C x t2 HxC) as Eplug2.
  assert (Hbig1 : big_step (instantiate rho1 (plug C (tm_fvar x))) v1).
  { unfold rho1. rewrite Eplug1. eapply evaluates_big_step. exact Heval1. }
  assert (Hbig2 : big_step (instantiate rho2 (plug C (tm_fvar x))) v2).
  { unfold rho2. rewrite Eplug2. eapply evaluates_big_step. exact Heval2. }
  pose proof (fundamental_relation (update empty x T_secret)
    (plug C (tm_fvar x)) T_result Hcty rho1 rho2 Henv Hvals1 Hvals2
    v1 v2 Hbig1 Hbig2) as Hrel.
  eapply value_rel_erase_ground; eauto.
Qed.
