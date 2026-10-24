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

(* ================================================================ *)
(* Section 1: basic lemmas about labels, security, and types        *)
(* ================================================================ *)

Lemma flows_to_refl : forall l, flows_to l l.
Proof. intros l; destruct l; simpl; auto. Qed.

Lemma flows_to_trans : forall l1 l2 l3,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof. intros l1 l2 l3 H1 H2; destruct l1, l2, l3; simpl in *; auto. Qed.

Lemma flows_to_high : forall l, flows_to l High.
Proof. intros l; destruct l; simpl; auto. Qed.

Lemma join_high : forall l, join l High = High.
Proof. intros l; destruct l; reflexivity. Qed.

Lemma join_low : forall l, join l Low = l.
Proof. intros l; destruct l; reflexivity. Qed.

Lemma join_low_l : forall l, join Low l = l.
Proof. intros l; destruct l; reflexivity. Qed.

Lemma not_flows_to_inv : forall l1 l2,
  ~ flows_to l1 l2 -> l1 = High /\ l2 = Low.
Proof. intros l1 l2 H; destruct l1, l2; simpl in *; tauto. Qed.

Lemma protect_security_low : forall k, protect_security k Low = k.
Proof. intros [r i]; destruct r, i; reflexivity. Qed.

Lemma protect_security_high : forall k, protect_security k High = secret.
Proof. intros [r i]; destruct r, i; reflexivity. Qed.

Lemma protect_value_low : forall v, protect_value v Low = v.
Proof.
  intros v; destruct v; try reflexivity;
  simpl; rewrite protect_security_low; reflexivity.
Qed.

Lemma security_of_ty_protect : forall l T,
  security_of (ty_protect l T) = protect_security (security_of T) l.
Proof. intros l T; destruct T; reflexivity. Qed.

Definition sec_of_tm (v : tm) : security :=
  match v with
  | tm_unit k => k
  | tm_abs _ _ k => k
  | tm_pair _ _ k => k
  | tm_inl _ k => k
  | tm_inr _ k => k
  | _ => public
  end.

(* ================================================================ *)
(* Section 2: locally-closed lemmas                                  *)
(* ================================================================ *)

Lemma lc_at_mono : forall k k' t, k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t. revert k k'.
  induction t; intros k k' Hle Hlc; simpl in *.
  - lia.
  - exact I.
  - exact I.
  - exact (IHt (S k) (S k') ltac:(lia) Hlc).
  - destruct Hlc as [H1 H2]; split.
    + exact (IHt1 k k' Hle H1).
    + exact (IHt2 k k' Hle H2).
  - destruct Hlc as [H1 H2]; split.
    + exact (IHt1 k k' Hle H1).
    + exact (IHt2 k k' Hle H2).
  - exact (IHt k k' Hle Hlc).
  - exact (IHt k k' Hle Hlc).
  - exact (IHt k k' Hle Hlc).
  - exact (IHt k k' Hle Hlc).
  - destruct Hlc as [H1 [H2 H3]]; split.
    + exact (IHt1 k k' Hle H1).
    + split.
      * exact (IHt2 (S k) (S k') ltac:(lia) H2).
      * exact (IHt3 (S k) (S k') ltac:(lia) H3).
  - exact (IHt k k' Hle Hlc).
  - destruct Hlc as [H1 [H2 H3]]; split.
    + exact (IHt1 k k' Hle H1).
    + split.
      * exact (IHt2 k k' Hle H2).
      * exact (IHt3 k k' Hle H3).
Qed.

Lemma lc_at_0_mono : forall k t, lc_at 0 t -> lc_at k t.
Proof. intros k t H; apply (lc_at_mono 0 k); [lia | exact H]. Qed.

Lemma open_rec_fvar_lc_inv : forall k x t,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k x t. revert k.
  induction t; simpl; intros k H.
  - destruct (Nat.eqb k n) eqn:E; simpl in H.
    + apply Nat.eqb_eq in E; lia.
    + apply Nat.eqb_neq in E; lia.
  - exact I.
  - exact I.
  - exact (IHt (S k) H).
  - destruct H as [H1 H2]; split.
    + exact (IHt1 k H1).
    + exact (IHt2 k H2).
  - destruct H as [H1 H2]; split.
    + exact (IHt1 k H1).
    + exact (IHt2 k H2).
  - exact (IHt k H).
  - exact (IHt k H).
  - exact (IHt k H).
  - exact (IHt k H).
  - destruct H as [H1 [H2 H3]]; split.
    + exact (IHt1 k H1).
    + split.
      * exact (IHt2 (S k) H2).
      * exact (IHt3 (S k) H3).
  - exact (IHt k H).
  - destruct H as [H1 [H2 H3]]; split.
    + exact (IHt1 k H1).
    + split.
      * exact (IHt2 k H2).
      * exact (IHt3 k H3).
Qed.

(* ================================================================ *)
(* Section 3: a fresh atom constructor                               *)
(* ================================================================ *)

Definition fresh (l : list atom) : atom :=
  S (fold_right Nat.max 0 l).

Lemma in_lt_fresh : forall l x, In x l -> x < fresh l.
Proof.
  induction l as [| a l IH]; intros x Hin.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Hx | Hin].
    + rewrite Hx. unfold fresh. simpl.
      pose proof (Nat.le_max_l x (fold_right Nat.max 0 l)).
      lia.
    + unfold fresh in *. simpl.
      pose proof (IH x Hin).
      pose proof (Nat.le_max_r a (fold_right Nat.max 0 l)).
      lia.
Qed.

Lemma fresh_spec : forall l, ~ In (fresh l) l.
Proof.
  intros l Hin. apply in_lt_fresh in Hin. lia.
Qed.

(* ================================================================ *)
(* Section 4: simultaneous substitution of free variables            *)
(* ================================================================ *)

Definition env := atom -> tm.

Definition upd (x : atom) (u : tm) : env :=
  fun y => if Nat.eqb y x then u else tm_fvar y.

Definition extend (gamma : env) (x : atom) (u : tm) : env :=
  fun y => if Nat.eqb y x then u else gamma y.

Fixpoint subst_env (gamma : env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_unit k => tm_unit k
  | tm_abs T body k => tm_abs T (subst_env gamma body) k
  | tm_app t1 t2 r => tm_app (subst_env gamma t1) (subst_env gamma t2) r
  | tm_pair t1 t2 k => tm_pair (subst_env gamma t1) (subst_env gamma t2) k
  | tm_fst t r => tm_fst (subst_env gamma t) r
  | tm_snd t r => tm_snd (subst_env gamma t) r
  | tm_inl t k => tm_inl (subst_env gamma t) k
  | tm_inr t k => tm_inr (subst_env gamma t) k
  | tm_case t b1 b2 r =>
      tm_case (subst_env gamma t) (subst_env gamma b1) (subst_env gamma b2) r
  | tm_protect l t => tm_protect l (subst_env gamma t)
  | tm_if c y n r =>
      tm_if (subst_env gamma c) (subst_env gamma y) (subst_env gamma n) r
  end.

Lemma subst_env_id : forall t, subst_env (fun y => tm_fvar y) t = t.
Proof. induction t; simpl; f_equal; auto. Qed.

Lemma open_rec_lc : forall k u t, lc_at k t -> open_rec k u t = t.
Proof.
  intros k u t. revert k.
  induction t as [ i | x | kap | T body IHbody kap | t1 IH1 t2 IH2 r
                 | t1 IH1 t2 IH2 kap | t1 IH1 r | t1 IH1 r | t1 IH1 kap | t1 IH1 kap
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y IHy n IHn r ];
  simpl; intros k Hlc.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IHbody (S k) Hlc). reflexivity.
  - destruct Hlc as [H1 H2]; rewrite (IH1 k H1), (IH2 k H2); reflexivity.
  - destruct Hlc as [H1 H2]; rewrite (IH1 k H1), (IH2 k H2); reflexivity.
  - rewrite (IH1 k Hlc); reflexivity.
  - rewrite (IH1 k Hlc); reflexivity.
  - rewrite (IH1 k Hlc); reflexivity.
  - rewrite (IH1 k Hlc); reflexivity.
  - destruct Hlc as [H0 [H1 H2]];
    rewrite (IH0 k H0), (IH1 (S k) H1), (IH2 (S k) H2); reflexivity.
  - rewrite (IH1 k Hlc); reflexivity.
  - destruct Hlc as [H1 [H2 H3]];
    rewrite (IHc k H1), (IHy k H2), (IHn k H3); reflexivity.
Qed.

Lemma not_in_app_l : forall (x : atom) (l1 l2 : list atom),
  ~ In x (l1 ++ l2) -> ~ In x l1.
Proof. intros x l1 l2 H Hin. apply H. apply in_app_iff. left. exact Hin. Qed.

Lemma not_in_app_r : forall (x : atom) (l1 l2 : list atom),
  ~ In x (l1 ++ l2) -> ~ In x l2.
Proof. intros x l1 l2 H Hin. apply H. apply in_app_iff. right. exact Hin. Qed.

Lemma subst_env_lc : forall gamma k t,
  (forall y, lc_at 0 (gamma y)) ->
  lc_at k t -> lc_at k (subst_env gamma t).
Proof.
  intros gamma k t. revert k.
  induction t as [ i | x | kap | T body IHbody kap | t1 IH1 t2 IH2 r
                 | t1 IH1 t2 IH2 kap | t1 IH1 r | t1 IH1 r | t1 IH1 kap | t1 IH1 kap
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y IHy n IHn r ];
  simpl; intros k Henv Hlc.
  - exact Hlc.
  - apply lc_at_0_mono; apply Henv.
  - exact I.
  - apply (IHbody (S k) Henv Hlc).
  - destruct Hlc as [H1 H2]; split.
    + apply (IH1 k Henv H1).
    + apply (IH2 k Henv H2).
  - destruct Hlc as [H1 H2]; split.
    + apply (IH1 k Henv H1).
    + apply (IH2 k Henv H2).
  - apply (IH1 k Henv Hlc).
  - apply (IH1 k Henv Hlc).
  - apply (IH1 k Henv Hlc).
  - apply (IH1 k Henv Hlc).
  - destruct Hlc as [H0 [H1 H2]]; split.
    + apply (IH0 k Henv H0).
    + split.
      * apply (IH1 (S k) Henv H1).
      * apply (IH2 (S k) Henv H2).
  - apply (IH1 k Henv Hlc).
  - destruct Hlc as [H1 [H2 H3]]; split.
    + apply (IHc k Henv H1).
    + split.
      * apply (IHy k Henv H2).
      * apply (IHn k Henv H3).
Qed.

Lemma open_rec_subst_env : forall k gamma x body,
  (forall y, lc_at 0 (gamma y)) ->
  subst_env gamma (open_rec k (tm_fvar x) body) =
  open_rec k (gamma x) (subst_env gamma body).
Proof.
  intros k gamma x body. revert k.
  induction body as [ i | y | kap | T b IHb kap | t1 IH1 t2 IH2 r
                 | t1 IH1 t2 IH2 kap | t1 IH1 r | t1 IH1 r | t1 IH1 kap | t1 IH1 kap
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y2 IHy n IHn r ];
  simpl; intros k Henv.
  - destruct (Nat.eqb k i) eqn:E; reflexivity.
  - symmetry. apply open_rec_lc. apply lc_at_0_mono. apply Henv.
  - reflexivity.
  - rewrite (IHb (S k) Henv). reflexivity.
  - rewrite (IH1 k Henv), (IH2 k Henv). reflexivity.
  - rewrite (IH1 k Henv), (IH2 k Henv). reflexivity.
  - rewrite (IH1 k Henv). reflexivity.
  - rewrite (IH1 k Henv). reflexivity.
  - rewrite (IH1 k Henv). reflexivity.
  - rewrite (IH1 k Henv). reflexivity.
  - rewrite (IH0 k Henv), (IH1 (S k) Henv), (IH2 (S k) Henv). reflexivity.
  - rewrite (IH1 k Henv). reflexivity.
  - rewrite (IHc k Henv), (IHy k Henv), (IHn k Henv). reflexivity.
Qed.

Lemma subst_env_extend_fresh : forall gamma x u t,
  ~ In x (fv t) -> subst_env (extend gamma x u) t = subst_env gamma t.
Proof.
  intros gamma x u t. revert gamma.
  induction t as [ i | y | kap | T b IHb kap | t1 IH1 t2 IH2 r
                 | t1 IH1 t2 IH2 kap | t1 IH1 r | t1 IH1 r | t1 IH1 kap | t1 IH1 kap
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y2 IHy n IHn r ];
  simpl; intros gamma Hfresh.
  - reflexivity.
  - destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hfresh. simpl. auto.
    + unfold extend. rewrite E. reflexivity.
  - reflexivity.
  - rewrite (IHb gamma Hfresh); reflexivity.
  - assert (H1 : ~ In x (fv t1)) by (apply (not_in_app_l x (fv t1) (fv t2)); exact Hfresh).
    assert (H2 : ~ In x (fv t2)) by (apply (not_in_app_r x (fv t1) (fv t2)); exact Hfresh).
    rewrite (IH1 gamma H1), (IH2 gamma H2); reflexivity.
  - assert (H1 : ~ In x (fv t1)) by (apply (not_in_app_l x (fv t1) (fv t2)); exact Hfresh).
    assert (H2 : ~ In x (fv t2)) by (apply (not_in_app_r x (fv t1) (fv t2)); exact Hfresh).
    rewrite (IH1 gamma H1), (IH2 gamma H2); reflexivity.
  - rewrite (IH1 gamma Hfresh); reflexivity.
  - rewrite (IH1 gamma Hfresh); reflexivity.
  - rewrite (IH1 gamma Hfresh); reflexivity.
  - rewrite (IH1 gamma Hfresh); reflexivity.
  - assert (H0 : ~ In x (fv t0)) by (apply (not_in_app_l x (fv t0) (fv b1 ++ fv b2)); exact Hfresh).
    assert (H12 : ~ In x (fv b1 ++ fv b2)) by (apply (not_in_app_r x (fv t0) (fv b1 ++ fv b2)); exact Hfresh).
    assert (H1 : ~ In x (fv b1)) by (apply (not_in_app_l x (fv b1) (fv b2)); exact H12).
    assert (H2 : ~ In x (fv b2)) by (apply (not_in_app_r x (fv b1) (fv b2)); exact H12).
    rewrite (IH0 gamma H0), (IH1 gamma H1), (IH2 gamma H2); reflexivity.
  - rewrite (IH1 gamma Hfresh); reflexivity.
  - assert (H1 : ~ In x (fv c)) by (apply (not_in_app_l x (fv c) (fv y2 ++ fv n)); exact Hfresh).
    assert (H23 : ~ In x (fv y2 ++ fv n)) by (apply (not_in_app_r x (fv c) (fv y2 ++ fv n)); exact Hfresh).
    assert (H2 : ~ In x (fv y2)) by (apply (not_in_app_l x (fv y2) (fv n)); exact H23).
    assert (H3 : ~ In x (fv n)) by (apply (not_in_app_r x (fv y2) (fv n)); exact H23).
    rewrite (IHc gamma H1), (IHy gamma H2), (IHn gamma H3); reflexivity.
Qed.

Lemma subst_env_upd_id : forall x u s,
  ~ In x (fv s) -> subst_env (upd x u) s = s.
Proof.
  intros x u s. revert u.
  induction s as [ i | y | kap | T b IHb kap | t1 IH1 t2 IH2 r
                 | t1 IH1 t2 IH2 kap | t1 IH1 r | t1 IH1 r | t1 IH1 kap | t1 IH1 kap
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y2 IHy n IHn r ];
  simpl; intros u Hfresh.
  - reflexivity.
  - destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hfresh. simpl. auto.
    + unfold upd. rewrite E. reflexivity.
  - reflexivity.
  - rewrite (IHb u Hfresh); reflexivity.
  - assert (H1 : ~ In x (fv t1)) by (apply (not_in_app_l x (fv t1) (fv t2)); exact Hfresh).
    assert (H2 : ~ In x (fv t2)) by (apply (not_in_app_r x (fv t1) (fv t2)); exact Hfresh).
    rewrite (IH1 u H1), (IH2 u H2); reflexivity.
  - assert (H1 : ~ In x (fv t1)) by (apply (not_in_app_l x (fv t1) (fv t2)); exact Hfresh).
    assert (H2 : ~ In x (fv t2)) by (apply (not_in_app_r x (fv t1) (fv t2)); exact Hfresh).
    rewrite (IH1 u H1), (IH2 u H2); reflexivity.
  - rewrite (IH1 u Hfresh); reflexivity.
  - rewrite (IH1 u Hfresh); reflexivity.
  - rewrite (IH1 u Hfresh); reflexivity.
  - rewrite (IH1 u Hfresh); reflexivity.
  - assert (H0 : ~ In x (fv t0)) by (apply (not_in_app_l x (fv t0) (fv b1 ++ fv b2)); exact Hfresh).
    assert (H12 : ~ In x (fv b1 ++ fv b2)) by (apply (not_in_app_r x (fv t0) (fv b1 ++ fv b2)); exact Hfresh).
    assert (H1 : ~ In x (fv b1)) by (apply (not_in_app_l x (fv b1) (fv b2)); exact H12).
    assert (H2 : ~ In x (fv b2)) by (apply (not_in_app_r x (fv b1) (fv b2)); exact H12).
    rewrite (IH0 u H0), (IH1 u H1), (IH2 u H2); reflexivity.
  - rewrite (IH1 u Hfresh); reflexivity.
  - assert (H1 : ~ In x (fv c)) by (apply (not_in_app_l x (fv c) (fv y2 ++ fv n)); exact Hfresh).
    assert (H23 : ~ In x (fv y2 ++ fv n)) by (apply (not_in_app_r x (fv c) (fv y2 ++ fv n)); exact Hfresh).
    assert (H2 : ~ In x (fv y2)) by (apply (not_in_app_l x (fv y2) (fv n)); exact H23).
    assert (H3 : ~ In x (fv n)) by (apply (not_in_app_r x (fv y2) (fv n)); exact H23).
    rewrite (IHc u H1), (IHy u H2), (IHn u H3); reflexivity.
Qed.

(* ================================================================ *)
(* Section 5: free variables of a program context                    *)
(* ================================================================ *)

Fixpoint fv_context (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ => fv_context C'
  | C_AppLeft C' t _ => fv_context C' ++ fv t
  | C_AppRight t C' _ => fv t ++ fv_context C'
  | C_PairLeft C' t _ => fv_context C' ++ fv t
  | C_PairRight t C' _ => fv t ++ fv_context C'
  | C_Fst C' _ => fv_context C'
  | C_Snd C' _ => fv_context C'
  | C_Inl C' _ => fv_context C'
  | C_Inr C' _ => fv_context C'
  | C_CaseScrutinee C' b1 b2 _ => fv_context C' ++ fv b1 ++ fv b2
  | C_CaseLeft b0 C' b2 _ => fv b0 ++ fv_context C' ++ fv b2
  | C_CaseRight b0 b1 C' _ => fv b0 ++ fv b1 ++ fv_context C'
  | C_Protect _ C' => fv_context C'
  | C_IfCondition C' y n _ => fv_context C' ++ fv y ++ fv n
  | C_IfThen c C' n _ => fv c ++ fv_context C' ++ fv n
  | C_IfElse c y C' _ => fv c ++ fv y ++ fv_context C'
  end.

Lemma subst_env_plug : forall C x u,
  ~ In x (fv_context C) ->
  subst_env (upd x u) (plug C (tm_fvar x)) = plug C u.
Proof.
  intros C0. induction C0 as [ | T C IHC kap | C IHC t r | t C IHC r
      | C IHC t kap | t C IHC kap | C IHC r | C IHC r | C IHC kap | C IHC kap
      | C IHC b1 b2 r | t0 C IHC b2 r | t0 b1 C IHC r | l C IHC
      | C IHC y n r | c C IHC n r | c y C IHC r ];
    intros x u Hfresh; simpl in *.
  - (* C_Hole *) unfold upd. rewrite Nat.eqb_refl. reflexivity.
  - (* C_Abs *) rewrite (IHC x u Hfresh). reflexivity.
  - (* C_AppLeft *)
    assert (Hc : ~ In x (fv_context C)) by
      (apply (not_in_app_l x (fv_context C) (fv t)); exact Hfresh).
    assert (Ht : ~ In x (fv t)) by
      (apply (not_in_app_r x (fv_context C) (fv t)); exact Hfresh).
    rewrite (IHC x u Hc). rewrite (subst_env_upd_id x u t Ht). reflexivity.
  - (* C_AppRight *)
    assert (Ht : ~ In x (fv t)) by
      (apply (not_in_app_l x (fv t) (fv_context C)); exact Hfresh).
    assert (Hc : ~ In x (fv_context C)) by
      (apply (not_in_app_r x (fv t) (fv_context C)); exact Hfresh).
    rewrite (IHC x u Hc). rewrite (subst_env_upd_id x u t Ht). reflexivity.
  - (* C_PairLeft *)
    assert (Hc : ~ In x (fv_context C)) by
      (apply (not_in_app_l x (fv_context C) (fv t)); exact Hfresh).
    assert (Ht : ~ In x (fv t)) by
      (apply (not_in_app_r x (fv_context C) (fv t)); exact Hfresh).
    rewrite (IHC x u Hc). rewrite (subst_env_upd_id x u t Ht). reflexivity.
  - (* C_PairRight *)
    assert (Ht : ~ In x (fv t)) by
      (apply (not_in_app_l x (fv t) (fv_context C)); exact Hfresh).
    assert (Hc : ~ In x (fv_context C)) by
      (apply (not_in_app_r x (fv t) (fv_context C)); exact Hfresh).
    rewrite (IHC x u Hc). rewrite (subst_env_upd_id x u t Ht). reflexivity.
  - (* C_Fst *) rewrite (IHC x u Hfresh). reflexivity.
  - (* C_Snd *) rewrite (IHC x u Hfresh). reflexivity.
  - (* C_Inl *) rewrite (IHC x u Hfresh). reflexivity.
  - (* C_Inr *) rewrite (IHC x u Hfresh). reflexivity.
  - (* C_CaseScrutinee *)
    assert (Hc : ~ In x (fv_context C)) by
      (apply (not_in_app_l x (fv_context C) (fv b1 ++ fv b2)); exact Hfresh).
    assert (H12 : ~ In x (fv b1 ++ fv b2)) by
      (apply (not_in_app_r x (fv_context C) (fv b1 ++ fv b2)); exact Hfresh).
    assert (H1 : ~ In x (fv b1)) by
      (apply (not_in_app_l x (fv b1) (fv b2)); exact H12).
    assert (H2 : ~ In x (fv b2)) by
      (apply (not_in_app_r x (fv b1) (fv b2)); exact H12).
    rewrite (IHC x u Hc).
    rewrite (subst_env_upd_id x u b1 H1), (subst_env_upd_id x u b2 H2).
    reflexivity.
  - (* C_CaseLeft *)
    assert (H0 : ~ In x (fv t0)) by
      (apply (not_in_app_l x (fv t0) (fv_context C ++ fv b2)); exact Hfresh).
    assert (Hcb : ~ In x (fv_context C ++ fv b2)) by
      (apply (not_in_app_r x (fv t0) (fv_context C ++ fv b2)); exact Hfresh).
    assert (Hc : ~ In x (fv_context C)) by
      (apply (not_in_app_l x (fv_context C) (fv b2)); exact Hcb).
    assert (H2 : ~ In x (fv b2)) by
      (apply (not_in_app_r x (fv_context C) (fv b2)); exact Hcb).
    rewrite (IHC x u Hc).
    rewrite (subst_env_upd_id x u t0 H0), (subst_env_upd_id x u b2 H2).
    reflexivity.
  - (* C_CaseRight *)
    assert (H0 : ~ In x (fv t0)) by
      (apply (not_in_app_l x (fv t0) (fv b1 ++ fv_context C)); exact Hfresh).
    assert (H1c : ~ In x (fv b1 ++ fv_context C)) by
      (apply (not_in_app_r x (fv t0) (fv b1 ++ fv_context C)); exact Hfresh).
    assert (H1 : ~ In x (fv b1)) by
      (apply (not_in_app_l x (fv b1) (fv_context C)); exact H1c).
    assert (Hc : ~ In x (fv_context C)) by
      (apply (not_in_app_r x (fv b1) (fv_context C)); exact H1c).
    rewrite (IHC x u Hc).
    rewrite (subst_env_upd_id x u t0 H0), (subst_env_upd_id x u b1 H1).
    reflexivity.
  - (* C_Protect *) rewrite (IHC x u Hfresh). reflexivity.
  - (* C_IfCondition *)
    assert (Hc : ~ In x (fv_context C)) by
      (apply (not_in_app_l x (fv_context C) (fv y ++ fv n)); exact Hfresh).
    assert (H12 : ~ In x (fv y ++ fv n)) by
      (apply (not_in_app_r x (fv_context C) (fv y ++ fv n)); exact Hfresh).
    assert (Hy : ~ In x (fv y)) by
      (apply (not_in_app_l x (fv y) (fv n)); exact H12).
    assert (Hn : ~ In x (fv n)) by
      (apply (not_in_app_r x (fv y) (fv n)); exact H12).
    rewrite (IHC x u Hc).
    rewrite (subst_env_upd_id x u y Hy), (subst_env_upd_id x u n Hn).
    reflexivity.
  - (* C_IfThen *)
    assert (Hc0 : ~ In x (fv c)) by
      (apply (not_in_app_l x (fv c) (fv_context C ++ fv n)); exact Hfresh).
    assert (Hcn : ~ In x (fv_context C ++ fv n)) by
      (apply (not_in_app_r x (fv c) (fv_context C ++ fv n)); exact Hfresh).
    assert (Hc : ~ In x (fv_context C)) by
      (apply (not_in_app_l x (fv_context C) (fv n)); exact Hcn).
    assert (Hn : ~ In x (fv n)) by
      (apply (not_in_app_r x (fv_context C) (fv n)); exact Hcn).
    rewrite (IHC x u Hc).
    rewrite (subst_env_upd_id x u c Hc0), (subst_env_upd_id x u n Hn).
    reflexivity.
  - (* C_IfElse *)
    assert (Hc0 : ~ In x (fv c)) by
      (apply (not_in_app_l x (fv c) (fv y ++ fv_context C)); exact Hfresh).
    assert (Hyc : ~ In x (fv y ++ fv_context C)) by
      (apply (not_in_app_r x (fv c) (fv y ++ fv_context C)); exact Hfresh).
    assert (Hy : ~ In x (fv y)) by
      (apply (not_in_app_l x (fv y) (fv_context C)); exact Hyc).
    assert (Hc : ~ In x (fv_context C)) by
      (apply (not_in_app_r x (fv y) (fv_context C)); exact Hyc).
    rewrite (IHC x u Hc).
    rewrite (subst_env_upd_id x u c Hc0), (subst_env_upd_id x u y Hy).
    reflexivity.
Qed.

(* ================================================================ *)
(* Section 6: value lemmas                                          *)
(* ================================================================ *)

Lemma value_no_step : forall t, value t -> forall t', ~ (t --> t').
Proof.
  intros t Hv. induction Hv as [ kap | T body kap Hlc | v1 v2 kap H1 IH1 H2 IH2
                               | v1 kap H1 IH1 | v1 kap H1 IH1 ]; intros t' Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst; firstorder.
  - inversion Hstep; subst; firstorder.
  - inversion Hstep; subst; firstorder.
Qed.

Lemma multi_value : forall t v, multi t v -> value t -> v = t.
Proof.
  intros t v Hm. induction Hm as [ s | s mid u Hstep Htail IH ].
  - intros Hv. reflexivity.
  - intros Hv. exfalso. eapply value_no_step; eauto.
Qed.

Lemma value_lc : forall v, value v -> lc_at 0 v.
Proof.
  intros v Hv. induction Hv as [ kap | T body kap Hlc | v1 v2 kap H1 IH1 H2 IH2
                               | v1 kap H1 IH1 | v1 kap H1 IH1 ]; simpl.
  - exact I.
  - exact Hlc.
  - split; assumption.
  - assumption.
  - assumption.
Qed.

Lemma value_lc_at : forall v k, value v -> lc_at k v.
Proof. intros v k Hv. apply lc_at_0_mono. apply value_lc. exact Hv. Qed.

Lemma value_protect_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv. induction Hv as [ kap | T body kap Hlc | v1 v2 kap H1 IH1 H2 IH2
                                  | v1 kap H1 IH1 | v1 kap H1 IH1 ]; simpl.
  - apply v_unit.
  - apply v_abs. exact Hlc.
  - apply v_pair; assumption.
  - apply v_inl; assumption.
  - apply v_inr; assumption.
Qed.

(* ================================================================ *)
(* Section 7: step inversion lemmas                                 *)
(* ================================================================ *)

Lemma step_pair_inv : forall t1 t2 kap u,
  tm_pair t1 t2 kap --> u ->
  (exists t1', t1 --> t1' /\ u = tm_pair t1' t2 kap) \/
  (value t1 /\ exists t2', t2 --> t2' /\ u = tm_pair t1 t2' kap).
Proof. intros; inversion H; subst; firstorder. Qed.

Lemma step_inl_inv : forall t kap u,
  tm_inl t kap --> u -> exists t', t --> t' /\ u = tm_inl t' kap.
Proof. intros; inversion H; subst; firstorder. Qed.

Lemma step_inr_inv : forall t kap u,
  tm_inr t kap --> u -> exists t', t --> t' /\ u = tm_inr t' kap.
Proof. intros; inversion H; subst; firstorder. Qed.

Lemma step_protect_inv : forall l t u,
  tm_protect l t --> u ->
  (value t /\ u = protect_value t l) \/ (exists t', t --> t' /\ u = tm_protect l t').
Proof. intros; inversion H; subst; firstorder. Qed.

Lemma step_app_inv : forall f a r u,
  tm_app f a r --> u ->
  (exists T body kap, f = tm_abs T body kap /\ value (tm_abs T body kap) /\
      value a /\ flows_to kap.(reader) r /\
      u = tm_protect kap.(indirect_reader) (open body a))
  \/ (exists f', f --> f' /\ u = tm_app f' a r)
  \/ (value f /\ exists a', a --> a' /\ u = tm_app f a' r).
Proof.
  intros f a r u H. inversion H; subst.
  - left. exists T, body, kappa. repeat split; auto.
  - right. left. eauto.
  - right. right. eauto.
Qed.

Lemma step_fst_inv : forall t r u,
  tm_fst t r --> u ->
  (exists w1 w2 kap, t = tm_pair w1 w2 kap /\ value w1 /\ value w2 /\
      flows_to kap.(reader) r /\ u = tm_protect kap.(indirect_reader) w1)
  \/ (exists t', t --> t' /\ u = tm_fst t' r).
Proof. intros; inversion H; subst; firstorder. Qed.

Lemma step_snd_inv : forall t r u,
  tm_snd t r --> u ->
  (exists w1 w2 kap, t = tm_pair w1 w2 kap /\ value w1 /\ value w2 /\
      flows_to kap.(reader) r /\ u = tm_protect kap.(indirect_reader) w2)
  \/ (exists t', t --> t' /\ u = tm_snd t' r).
Proof. intros; inversion H; subst; firstorder. Qed.

Lemma step_case_inv : forall t b1 b2 r u,
  tm_case t b1 b2 r --> u ->
  (exists w kap, t = tm_inl w kap /\ value w /\ flows_to kap.(reader) r /\
      u = tm_protect kap.(indirect_reader) (open b1 w))
  \/ (exists w kap, t = tm_inr w kap /\ value w /\ flows_to kap.(reader) r /\
      u = tm_protect kap.(indirect_reader) (open b2 w))
  \/ (exists t', t --> t' /\ u = tm_case t' b1 b2 r).
Proof. intros; inversion H; subst; firstorder. Qed.

Lemma step_if_inv : forall c yes no r u,
  tm_if c yes no r --> u ->
  (exists c', c --> c' /\ u = tm_if c' yes no r)
  \/ (exists w kap, c = tm_inl w kap /\ value w /\ flows_to kap.(reader) r /\
      u = tm_protect kap.(indirect_reader) yes)
  \/ (exists w kap, c = tm_inr w kap /\ value w /\ flows_to kap.(reader) r /\
      u = tm_protect kap.(indirect_reader) no).
Proof. intros; inversion H; subst; firstorder. Qed.

(* ================================================================ *)
(* Section 8: evaluation decomposition lemmas                       *)
(* ================================================================ *)

Lemma multi_pair_inv : forall X v, multi X v -> value v ->
  forall t1 t2 kap, X = tm_pair t1 t2 kap ->
  exists u1 u2, v = tm_pair u1 u2 kap /\ multi t1 u1 /\ multi t2 u2 /\
                value u1 /\ value u2.
Proof.
  intros X v Hm. induction Hm as [ s | s mid u Hstep Htail IH ].
  - intros Hv t1 t2 kap Heq. subst s.
    inversion Hv; subst. exists t1, t2. repeat split; auto using multi_refl.
  - intros Hv t1 t2 kap Heq. subst s.
    apply step_pair_inv in Hstep as
      [[t1' [Hst Hu]] | [Hval1 [t2' [Hst Hu]]]]; subst mid.
    + destruct (IH Hv t1' t2 kap eq_refl) as [u1 [u2 [H1 [Hm1 [Hm2 [Hv1 Hv2]]]]]].
      exists u1, u2. repeat split; auto. apply multi_step with (t2 := t1'); auto.
    + destruct (IH Hv t1 t2' kap eq_refl) as [u1 [u2 [H1 [Hm1 [Hm2 [Hv1 Hv2]]]]]].
      exists u1, u2. repeat split; auto. apply multi_step with (t2 := t2'); auto.
Qed.

Lemma multi_app_inv : forall X v, multi X v -> value v ->
  forall f a r, X = tm_app f a r ->
  exists vf va, multi f vf /\ multi a va /\ value vf /\ value va /\
                multi (tm_app vf va r) v.
Proof.
  intros X v Hm. induction Hm as [ s | s mid u Hstep Htail IH ].
  - intros Hv f a r Heq. subst s. inversion Hv.
  - intros Hv f a r Heq. subst s.
    apply step_app_inv in Hstep as
      [[T [body [kap [Hf [Habs [Hva [Hfl Hu]]]]]]] |
       [[f' [Hst Hu]] | [Hvf [a' [Hst Hu]]]]]; subst mid.
    + subst f. exists (tm_abs T body kap), a.
      split. { apply multi_refl. }
      split. { apply multi_refl. }
      split. { exact Habs. }
      split. { exact Hva. }
      apply multi_step with (t2 := tm_protect kap.(indirect_reader) (open body a)).
      * apply ST_AppAbs; auto.
      * exact Htail.
    + destruct (IH Hv f' a r eq_refl) as [vf [va [Hmf [Hma [Hvf [Hva Hm]]]]]].
      exists vf, va.
      split. { apply multi_step with (t2 := f'); auto. }
      split. { exact Hma. }
      split. { exact Hvf. }
      split. { exact Hva. }
      exact Hm.
    + destruct (IH Hv f a' r eq_refl) as [vf [va [Hmf [Hma [Hvf' [Hva' Hm]]]]]].
      exists vf, va.
      split. { exact Hmf. }
      split. { apply multi_step with (t2 := a'); auto. }
      split. { exact Hvf'. }
      split. { exact Hva'. }
      exact Hm.
Qed.

Lemma multi_inl_inv : forall X v, multi X v -> value v ->
  forall t kap, X = tm_inl t kap -> exists u, v = tm_inl u kap /\ multi t u /\ value u.
Proof.
  intros X v Hm. induction Hm as [ s | s mid u Hstep Htail IH ].
  - intros Hv t kap Heq. subst s. inversion Hv; subst.
    exists t. repeat split; auto using multi_refl.
  - intros Hv t kap Heq. subst s.
    apply step_inl_inv in Hstep as [t' [Hst Hu]]; subst mid.
    destruct (IH Hv t' kap eq_refl) as [u' [H1 [H2 H3]]].
    exists u'. repeat split; auto. apply multi_step with (t2 := t'); auto.
Qed.

Lemma multi_inr_inv : forall X v, multi X v -> value v ->
  forall t kap, X = tm_inr t kap -> exists u, v = tm_inr u kap /\ multi t u /\ value u.
Proof.
  intros X v Hm. induction Hm as [ s | s mid u Hstep Htail IH ].
  - intros Hv t kap Heq. subst s. inversion Hv; subst.
    exists t. repeat split; auto using multi_refl.
  - intros Hv t kap Heq. subst s.
    apply step_inr_inv in Hstep as [t' [Hst Hu]]; subst mid.
    destruct (IH Hv t' kap eq_refl) as [u' [H1 [H2 H3]]].
    exists u'. repeat split; auto. apply multi_step with (t2 := t'); auto.
Qed.

Lemma multi_protect_inv : forall X v, multi X v -> value v ->
  forall l t, X = tm_protect l t ->
  exists u, multi t u /\ value u /\ v = protect_value u l.
Proof.
  intros X v Hm. induction Hm as [ s | s mid u Hstep Htail IH ].
  - intros Hv l t Heq. subst s. inversion Hv.
  - intros Hv l t Heq. subst s.
    apply step_protect_inv in Hstep as [[Hval Hu] | [t' [Hst Hu]]]; subst mid.
    + exists t. split. { apply multi_refl. } split. { exact Hval. }
      apply multi_value with (t := protect_value t l).
      * exact Htail.
      * apply value_protect_value; exact Hval.
    + destruct (IH Hv l t' eq_refl) as [u' [Hm' [Hval' Heq']]].
      exists u'. repeat split; auto. apply multi_step with (t2 := t'); auto.
Qed.

Lemma multi_fst_inv : forall X v, multi X v -> value v ->
  forall t r, X = tm_fst t r ->
  exists w1 w2 kap, multi t (tm_pair w1 w2 kap) /\ value w1 /\ value w2 /\
                    flows_to kap.(reader) r /\
                    v = protect_value w1 kap.(indirect_reader).
Proof.
  intros X v Hm. induction Hm as [ s | s mid u Hstep Htail IH ].
  - intros Hv t r Heq. subst s. inversion Hv.
  - intros Hv t r Heq. subst s.
    apply step_fst_inv in Hstep as
      [[w1 [w2 [kap [Ht [Hv1 [Hv2 [Hfl Hu]]]]]]] | [t' [Hst Hu]]]; subst mid.
    + subst t.
      destruct (multi_protect_inv (tm_protect kap.(indirect_reader) w1) u Htail Hv
                  kap.(indirect_reader) w1 eq_refl) as [uu [Hmu [Hvu Heq']]].
      assert (Huu : uu = w1) by (apply multi_value with (t := w1); auto).
      subst uu. exists w1, w2, kap. repeat split; auto using multi_refl.
    + destruct (IH Hv t' r eq_refl) as [w1 [w2 [kap [Hm' [Hv1 [Hv2 [Hfl Heq']]]]]]].
      exists w1, w2, kap. repeat split; auto. apply multi_step with (t2 := t'); auto.
Qed.

Lemma multi_snd_inv : forall X v, multi X v -> value v ->
  forall t r, X = tm_snd t r ->
  exists w1 w2 kap, multi t (tm_pair w1 w2 kap) /\ value w1 /\ value w2 /\
                    flows_to kap.(reader) r /\
                    v = protect_value w2 kap.(indirect_reader).
Proof.
  intros X v Hm. induction Hm as [ s | s mid u Hstep Htail IH ].
  - intros Hv t r Heq. subst s. inversion Hv.
  - intros Hv t r Heq. subst s.
    apply step_snd_inv in Hstep as
      [[w1 [w2 [kap [Ht [Hv1 [Hv2 [Hfl Hu]]]]]]] | [t' [Hst Hu]]]; subst mid.
    + subst t.
      destruct (multi_protect_inv (tm_protect kap.(indirect_reader) w2) u Htail Hv
                  kap.(indirect_reader) w2 eq_refl) as [uu [Hmu [Hvu Heq']]].
      assert (Huu : uu = w2) by (apply multi_value with (t := w2); auto).
      subst uu. exists w1, w2, kap. repeat split; auto using multi_refl.
    + destruct (IH Hv t' r eq_refl) as [w1 [w2 [kap [Hm' [Hv1 [Hv2 [Hfl Heq']]]]]]].
      exists w1, w2, kap. repeat split; auto. apply multi_step with (t2 := t'); auto.
Qed.

Lemma multi_case_inv : forall X v, multi X v -> value v ->
  forall t b1 b2 r, X = tm_case t b1 b2 r ->
  (exists w kap u, multi t (tm_inl w kap) /\ value w /\ flows_to kap.(reader) r /\
      multi (open b1 w) u /\ value u /\ v = protect_value u kap.(indirect_reader))
  \/
  (exists w kap u, multi t (tm_inr w kap) /\ value w /\ flows_to kap.(reader) r /\
      multi (open b2 w) u /\ value u /\ v = protect_value u kap.(indirect_reader)).
Proof.
  intros X v Hm. induction Hm as [ s | s mid u Hstep Htail IH ].
  - intros Hv t b1 b2 r Heq. subst s. inversion Hv.
  - intros Hv t b1 b2 r Heq. subst s.
    apply step_case_inv in Hstep as
      [[w [kap [Ht [Hv1 [Hfl Hu]]]]] |
       [[w [kap [Ht [Hv1 [Hfl Hu]]]]] | [t' [Hst Hu]]]]; subst mid.
    + subst t.
      destruct (multi_protect_inv (tm_protect kap.(indirect_reader) (open b1 w)) u Htail Hv
                  kap.(indirect_reader) (open b1 w) eq_refl) as [uu [Hmu [Hvu Heq']]].
      left. exists w, kap, uu. repeat split; auto using multi_refl.
    + subst t.
      destruct (multi_protect_inv (tm_protect kap.(indirect_reader) (open b2 w)) u Htail Hv
                  kap.(indirect_reader) (open b2 w) eq_refl) as [uu [Hmu [Hvu Heq']]].
      right. exists w, kap, uu. repeat split; auto using multi_refl.
    + destruct (IH Hv t' b1 b2 r eq_refl) as
        [[w [kap [uu [Hm' [Hv1 [Hfl [Hmu [Hvu Heq']]]]]]]] |
         [w [kap [uu [Hm' [Hv1 [Hfl [Hmu [Hvu Heq']]]]]]]]].
      * left. exists w, kap, uu. repeat split; auto. apply multi_step with (t2 := t'); auto.
      * right. exists w, kap, uu. repeat split; auto. apply multi_step with (t2 := t'); auto.
Qed.

Lemma multi_if_inv : forall X v, multi X v -> value v ->
  forall c yes no r, X = tm_if c yes no r ->
  (exists w kap u, multi c (tm_inl w kap) /\ value w /\ flows_to kap.(reader) r /\
      multi yes u /\ value u /\ v = protect_value u kap.(indirect_reader))
  \/
  (exists w kap u, multi c (tm_inr w kap) /\ value w /\ flows_to kap.(reader) r /\
      multi no u /\ value u /\ v = protect_value u kap.(indirect_reader)).
Proof.
  intros X v Hm. induction Hm as [ s | s mid u Hstep Htail IH ].
  - intros Hv c yes no r Heq. subst s. inversion Hv.
  - intros Hv c yes no r Heq. subst s.
    apply step_if_inv in Hstep as
      [[c' [Hst Hu]] |
       [[w [kap [Hc [Hv1 [Hfl Hu]]]]] | [w [kap [Hc [Hv1 [Hfl Hu]]]]]]]; subst mid.
    + destruct (IH Hv c' yes no r eq_refl) as
        [[w [kap [uu [Hm' [Hv1 [Hfl [Hmu [Hvu Heq']]]]]]]] |
         [w [kap [uu [Hm' [Hv1 [Hfl [Hmu [Hvu Heq']]]]]]]]].
      * left. exists w, kap, uu. repeat split; auto. apply multi_step with (t2 := c'); auto.
      * right. exists w, kap, uu. repeat split; auto. apply multi_step with (t2 := c'); auto.
    + subst c.
      destruct (multi_protect_inv (tm_protect kap.(indirect_reader) yes) u Htail Hv
                  kap.(indirect_reader) yes eq_refl) as [uu [Hmu [Hvu Heq']]].
      left. exists w, kap, uu. repeat split; auto using multi_refl.
    + subst c.
      destruct (multi_protect_inv (tm_protect kap.(indirect_reader) no) u Htail Hv
                  kap.(indirect_reader) no eq_refl) as [uu [Hmu [Hvu Heq']]].
      right. exists w, kap, uu. repeat split; auto using multi_refl.
Qed.

Lemma multi_app_abs_inv : forall T body kap w r v,
  value w -> flows_to kap.(reader) r ->
  multi (tm_app (tm_abs T body kap) w r) v -> value v ->
  multi (tm_protect kap.(indirect_reader) (open body w)) v.
Proof.
  intros T body kap w r v Hw Hfl Hm.
  remember (tm_app (tm_abs T body kap) w r) as src eqn:Heq.
  revert T body kap w r Hw Hfl Heq.
  induction Hm as [ s | s mid u Hstep Htail IH ].
  - intros T body kap w r Hw Hfl Heq Hv. subst s.
    inversion Hv.
  - intros T body kap w r Hw Hfl Heq Hv. subst s.
    apply step_app_inv in Hstep as
      [[T' [body' [kap' [Hf [Habs [Hwa [Hfl' Hu]]]]]]] |
       [[f' [Hst Hu]] | [Hvf [a' [Hst Hu]]]]].
    + inversion Hf; subst. exact Htail.
    + inversion Hst.
    + exfalso. exact (value_no_step w Hw a' Hst).
Qed.

(* ================================================================ *)
(* Section 9: typing implies locally closed                        *)
(* ================================================================ *)

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T H.
  induction H as [ Gamma x T Hlook Hwf
                 | Gamma kappa Hwf
                 | L Gamma T1 body T2 kappa HwfT1 Hwfkap Hbody IHbody
                 | Gamma t1 t2 T1 T2 kappa r H1 IH1 H2 IH2 Hflow
                 | Gamma t1 t2 T1 T2 kappa H1 IH1 H2 IH2 Hwf
                 | Gamma t T1 T2 kappa r H1 IH1 Hflow
                 | Gamma t T1 T2 kappa r H1 IH1 Hflow
                 | Gamma t T1 T2 kappa H1 IH1 HwfT2 Hwfkap
                 | Gamma t T1 T2 kappa HwfT1 H1 IH1 Hwfkap
                 | L Gamma t body1 body2 T1 T2 T kappa r H1 IH1 Hflow Hb1 IHb1 Hb2 IHb2
                 | Gamma t T l H1 IH1
                 | Gamma t T U H1 IH1 Hsub
                 | Gamma c yes no k T r H1 IH1 H2 IH2 H3 IH3 Hflow ];
  simpl in *.
  - exact I.
  - exact I.
  - apply open_rec_fvar_lc_inv with (k := 0) (x := fresh L).
    apply (IHbody (fresh L) (fresh_spec L)).
  - split; assumption.
  - split; assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - split. { exact IH1. } split.
    + apply open_rec_fvar_lc_inv with (k := 0) (x := fresh L).
      apply (IHb1 (fresh L) (fresh_spec L)).
    + apply open_rec_fvar_lc_inv with (k := 0) (x := fresh L).
      apply (IHb2 (fresh L) (fresh_spec L)).
  - assumption.
  - assumption.
  - split. { exact IH1. } split; assumption.
Qed.

(* ================================================================ *)
(* Section 10: the logical relation                                 *)
(* ================================================================ *)

Fixpoint VR (T : ty) (kappa : security) (v1 v2 : tm) : Prop :=
  flows_to (sec_of_tm v1).(indirect_reader) kappa.(indirect_reader) /\
  flows_to (sec_of_tm v2).(indirect_reader) kappa.(indirect_reader) /\
  match T with
  | Ty_Unit _ =>
      kappa.(indirect_reader) = High \/
      (exists k1 k2, v1 = tm_unit k1 /\ v2 = tm_unit k2)
  | Ty_Sum T1 T2 _ =>
      kappa.(indirect_reader) = High \/
      (exists k1 k2 w1 w2, v1 = tm_inl w1 k1 /\ v2 = tm_inl w2 k2 /\
         VR T1 (security_of T1) w1 w2) \/
      (exists k1 k2 w1 w2, v1 = tm_inr w1 k1 /\ v2 = tm_inr w2 k2 /\
         VR T2 (security_of T2) w1 w2)
  | Ty_Prod T1 T2 _ =>
      kappa.(indirect_reader) = High \/
      (exists k1 k2 w1 w2 x1 x2, v1 = tm_pair w1 x1 k1 /\ v2 = tm_pair w2 x2 k2 /\
         VR T1 (security_of T1) w1 w2 /\ VR T2 (security_of T2) x1 x2)
  | Ty_Arrow T1 T2 _ =>
      kappa.(indirect_reader) = High \/
      (forall r w1 w2, value w1 -> value w2 -> flows_to kappa.(reader) r ->
         VR T1 (security_of T1) w1 w2 ->
         forall u1 u2, evaluates (tm_app v1 w1 r) u1 -> evaluates (tm_app v2 w2 r) u2 ->
           VR T2 (protect_security (security_of T2) kappa.(indirect_reader)) u1 u2)
  end.

Definition IR (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, evaluates t1 v1 -> evaluates t2 v2 -> VR T (security_of T) v1 v2.

(* ================================================================ *)
(* Section 11: basic properties of the relation                     *)
(* ================================================================ *)

Lemma VR_protect : forall T kappa l1 l2 v1 v2,
  flows_to l1 l2 ->
  VR T kappa v1 v2 ->
  VR T (protect_security kappa l2) (protect_value v1 l1) (protect_value v2 l1).
Proof.
  intros T kappa l1 l2 v1 v2 Hfl HVR.
  destruct l2.
  - destruct l1; simpl in Hfl.
    + rewrite !protect_security_low, !protect_value_low. exact HVR.
    + exfalso; exact Hfl.
  - destruct T; simpl in *.
    all: split; [ rewrite join_high; apply flows_to_high
                | split; [ rewrite join_high; apply flows_to_high
                         | left; rewrite join_high; reflexivity ] ].
Qed.

Lemma VR_cross_high : forall T v1 v2,
  (security_of T).(indirect_reader) = High ->
  VR T (security_of T) v1 v1 ->
  VR T (security_of T) v2 v2 ->
  VR T (security_of T) v1 v2.
Proof.
  intros T v1 v2 Hh H1 H2. destruct T; simpl in *;
    destruct H1 as [C1 _]; destruct H2 as [C2 _];
    (split; [ exact C1 | split; [ exact C2 | left; exact Hh ] ]).
Qed.

Lemma IR_of_values : forall T v1 v2,
  value v1 -> value v2 -> VR T (security_of T) v1 v2 -> IR T v1 v2.
Proof.
  intros T v1 v2 Hv1 Hv2 HVR u1 u2 [Hm1 Hval1] [Hm2 Hval2].
  assert (Hu1 : u1 = v1) by (apply multi_value with (t := v1); auto).
  assert (Hu2 : u2 = v2) by (apply multi_value with (t := v2); auto).
  subst u1; subst u2. exact HVR.
Qed.

Lemma IR_cross_high : forall T t1 t2,
  (security_of T).(indirect_reader) = High ->
  IR T t1 t1 -> IR T t2 t2 -> IR T t1 t2.
Proof.
  intros T t1 t2 Hh H1 H2 v1 v2 E1 E2.
  unfold IR in *.
  pose proof (H1 v1 v1 E1 E1) as R1.
  pose proof (H2 v2 v2 E2 E2) as R2.
  eapply VR_cross_high; eauto.
Qed.

Lemma subtype_VR : forall T U, subtype T U ->
  forall v1 v2, VR T (security_of T) v1 v2 -> VR U (security_of U) v1 v2.
Proof.
  intros T U Hsub. induction Hsub as
    [ kappa1 kappa2 Hwf1 Hwf2 Hle
    | T1 T2 U1 U2 kappa1 kappa2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hle
    | T1 T2 U1 U2 kappa1 kappa2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hle
    | T1 T2 U1 U2 kappa1 kappa2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hle
    | T U V Hsub1 IH1 Hsub2 IH2 ]; intros v1 v2 HVR.
  - (* S_Unit *) simpl in *.
    destruct Hle as [Hr Hi].
    destruct HVR as [C1 [C2 S]].
    split. { eapply flows_to_trans; eauto. }
    split. { eapply flows_to_trans; eauto. }
    destruct S as [Hh | Hs].
    + left. destruct (kappa2.(indirect_reader)) eqn:E2.
      * exfalso. rewrite Hh in Hi. simpl in Hi. exact Hi.
      * reflexivity.
    + right. exact Hs.
  - (* S_Sum *) simpl in *.
    destruct Hle as [Hr Hi].
    destruct HVR as [C1 [C2 Hmain]].
    split. { eapply flows_to_trans; eauto. }
    split. { eapply flows_to_trans; eauto. }
    destruct (kappa2.(indirect_reader)) eqn:E2.
    + destruct Hmain as [Hk | Hstruct].
      * rewrite Hk in Hi. simpl in Hi. exfalso; exact Hi.
      * destruct Hstruct as
          [[k1' [k2' [w1 [w2 [E1' [E2'' Hrel]]]]]] |
           [k1' [k2' [w1 [w2 [E1' [E2'' Hrel]]]]]]].
        -- right. left. exists k1', k2', w1, w2.
           split. { exact E1'. } split. { exact E2''. } apply IH1; exact Hrel.
        -- right. right. exists k1', k2', w1, w2.
           split. { exact E1'. } split. { exact E2''. } apply IH2; exact Hrel.
    + left. reflexivity.
  - (* S_Prod *) simpl in *.
    destruct Hle as [Hr Hi].
    destruct HVR as [C1 [C2 Hmain]].
    split. { eapply flows_to_trans; eauto. }
    split. { eapply flows_to_trans; eauto. }
    destruct (kappa2.(indirect_reader)) eqn:E2.
    + destruct Hmain as [Hk | Hstruct].
      * rewrite Hk in Hi. simpl in Hi. exfalso; exact Hi.
      * destruct Hstruct as
          [k1' [k2' [w1 [w2 [x1 [x2 [E1' [E2'' [Hrel1 Hrel2]]]]]]]]].
        right. exists k1', k2', w1, w2, x1, x2.
        split. { exact E1'. } split. { exact E2''. } split.
        -- apply IH1; exact Hrel1.
        -- apply IH2; exact Hrel2.
    + left. reflexivity.
  - (* S_Arrow *) simpl in *.
    destruct Hle as [Hr Hi].
    destruct HVR as [C1 [C2 Hmain]].
    split. { eapply flows_to_trans; eauto. }
    split. { eapply flows_to_trans; eauto. }
    destruct (kappa2.(indirect_reader)) eqn:E2.
    + assert (Hk1 : kappa1.(indirect_reader) = Low).
      { destruct kappa1.(indirect_reader); auto.
        exfalso. simpl in Hi. exact Hi. }
      destruct Hmain as [Hk | Hclause].
      * rewrite Hk in Hi. simpl in Hi. exfalso; exact Hi.
      * right. intros r w1 w2 Hv1 Hv2 Hfl2 Hrel u1 u2 Hu1 Hu2.
        assert (Hfl1 : flows_to (reader kappa1) r).
        { apply flows_to_trans with (reader kappa2); auto. }
        assert (Hrel1 : VR T1 (security_of T1) w1 w2).
        { apply IH1; exact Hrel. }
        assert (Hc := Hclause r w1 w2 Hv1 Hv2 Hfl1 Hrel1 u1 u2 Hu1 Hu2).
        rewrite Hk1 in Hc. rewrite protect_security_low in Hc.
        rewrite protect_security_low.
        apply IH2. exact Hc.
    + left. reflexivity.
  - (* S_Trans *) apply IH2. apply IH1. exact HVR.
Qed.

(* ================================================================ *)
(* Section 12: environment helpers                                  *)
(* ================================================================ *)

Definition env_rel (Gamma : context) (gamma1 gamma2 : env) : Prop :=
  (forall y, lc_at 0 (gamma1 y)) /\
  (forall y, lc_at 0 (gamma2 y)) /\
  (forall x T, lookup_context x Gamma = Some T -> IR T (gamma1 x) (gamma2 x)).

Lemma env_rel_intro : forall Gamma gamma1 gamma2,
  (forall y, lc_at 0 (gamma1 y)) ->
  (forall y, lc_at 0 (gamma2 y)) ->
  (forall x T, lookup_context x Gamma = Some T -> IR T (gamma1 x) (gamma2 x)) ->
  env_rel Gamma gamma1 gamma2.
Proof. intros. split; [exact H | split; [exact H0 | exact H1]]. Qed.

Lemma typing_open_lc : forall L Gamma T1 body T2,
  (forall x, ~ In x L -> has_type (update Gamma x T1) (open body (tm_fvar x)) T2) ->
  lc_at 1 body.
Proof.
  intros L Gamma T1 body T2 H.
  apply open_rec_fvar_lc_inv with (k := 0) (x := fresh L).
  apply (has_type_lc _ _ _ (H (fresh L) (fresh_spec L))).
Qed.

Lemma lookup_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof.
  intros Gamma x T. unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_update_neq : forall Gamma x T y,
  y <> x -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x T y Hneq. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E; auto.
  apply Nat.eqb_eq in E. exfalso. auto.
Qed.

Lemma extend_lc : forall gamma x w y,
  (forall z, lc_at 0 (gamma z)) -> lc_at 0 w -> lc_at 0 (extend gamma x w y).
Proof.
  intros gamma x w y Hlc Hw. unfold extend.
  destruct (Nat.eqb y x); [exact Hw | apply Hlc].
Qed.

Lemma env_rel_update : forall Gamma gamma1 gamma2 x T1 w1 w2,
  env_rel Gamma gamma1 gamma2 ->
  value w1 -> value w2 -> IR T1 w1 w2 ->
  env_rel (update Gamma x T1) (extend gamma1 x w1) (extend gamma2 x w2).
Proof.
  intros Gamma gamma1 gamma2 x T1 w1 w2 [Hlc1 [Hlc2 HIR]] Hv1 Hv2 HIr.
  split. { intros y. apply extend_lc; auto. apply value_lc; auto. }
  split. { intros y. apply extend_lc; auto. apply value_lc; auto. }
  intros y T Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    rewrite lookup_update_eq in Hlook. injection Hlook as HT. subst T.
    unfold extend. rewrite Nat.eqb_refl. exact HIr.
  - assert (Hneq : y <> x) by (apply Nat.eqb_neq; exact E).
    rewrite (lookup_update_neq Gamma x T1 y Hneq) in Hlook.
    unfold extend. rewrite E. exact (HIR y T Hlook).
Qed.

Lemma subst_env_open_extend : forall gamma x w body,
  (forall y, lc_at 0 (gamma y)) ->
  lc_at 0 w ->
  ~ In x (fv body) ->
  subst_env (extend gamma x w) (open body (tm_fvar x)) = open (subst_env gamma body) w.
Proof.
  intros gamma x w body Hlc Hw Hfresh.
  assert (H1 : subst_env (extend gamma x w) (open body (tm_fvar x)) =
               open_rec 0 (extend gamma x w x) (subst_env (extend gamma x w) body)).
  { apply open_rec_subst_env. intros y. apply extend_lc; auto. }
  rewrite H1.
  assert (Hx : extend gamma x w x = w).
  { unfold extend. rewrite Nat.eqb_refl. reflexivity. }
  rewrite Hx.
  rewrite (subst_env_extend_fresh gamma x w body Hfresh).
  reflexivity.
Qed.

(* ================================================================ *)
(* Section 13: extracting the low cases of the relation             *)
(* ================================================================ *)

Lemma VR_coh1 : forall T kappa v1 v2,
  VR T kappa v1 v2 -> flows_to (sec_of_tm v1).(indirect_reader) kappa.(indirect_reader).
Proof. intros T kappa v1 v2 H. destruct T; simpl in *; tauto. Qed.

Lemma VR_coh2 : forall T kappa v1 v2,
  VR T kappa v1 v2 -> flows_to (sec_of_tm v2).(indirect_reader) kappa.(indirect_reader).
Proof. intros T kappa v1 v2 H. destruct T; simpl in *; tauto. Qed.

Lemma VR_sum_low : forall T1 T2 kappa v1 v2,
  kappa.(indirect_reader) = Low -> VR (Ty_Sum T1 T2 kappa) kappa v1 v2 ->
  (exists k1 k2 w1 w2, v1 = tm_inl w1 k1 /\ v2 = tm_inl w2 k2 /\
      VR T1 (security_of T1) w1 w2) \/
  (exists k1 k2 w1 w2, v1 = tm_inr w1 k1 /\ v2 = tm_inr w2 k2 /\
      VR T2 (security_of T2) w1 w2).
Proof.
  intros T1 T2 kappa v1 v2 Hlow HVR. simpl in HVR.
  destruct HVR as [_ [_ [Hh | H]]].
  - rewrite Hlow in Hh. discriminate.
  - exact H.
Qed.

Lemma VR_prod_low : forall T1 T2 kappa v1 v2,
  kappa.(indirect_reader) = Low -> VR (Ty_Prod T1 T2 kappa) kappa v1 v2 ->
  exists k1 k2 w1 w2 x1 x2, v1 = tm_pair w1 x1 k1 /\ v2 = tm_pair w2 x2 k2 /\
    VR T1 (security_of T1) w1 w2 /\ VR T2 (security_of T2) x1 x2.
Proof.
  intros T1 T2 kappa v1 v2 Hlow HVR. simpl in HVR.
  destruct HVR as [_ [_ [Hh | H]]].
  - rewrite Hlow in Hh. discriminate.
  - exact H.
Qed.

Lemma VR_arrow_low : forall T1 T2 kappa v1 v2,
  kappa.(indirect_reader) = Low -> VR (Ty_Arrow T1 T2 kappa) kappa v1 v2 ->
  forall r w1 w2, value w1 -> value w2 -> flows_to kappa.(reader) r ->
    VR T1 (security_of T1) w1 w2 ->
    forall u1 u2, evaluates (tm_app v1 w1 r) u1 -> evaluates (tm_app v2 w2 r) u2 ->
      VR T2 (protect_security (security_of T2) kappa.(indirect_reader)) u1 u2.
Proof.
  intros T1 T2 kappa v1 v2 Hlow HVR. simpl in HVR.
  destruct HVR as [_ [_ [Hh | H]]].
  - rewrite Hlow in Hh. discriminate.
  - exact H.
Qed.

(* ================================================================ *)
(* Section 14: erasing ground transparent low results               *)
(* ================================================================ *)

Fixpoint all_low (T : ty) : Prop :=
  (security_of T).(indirect_reader) = Low /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ => all_low T1 /\ all_low T2
  end.

Lemma transparent_all_low : forall T kappa,
  transparent_at kappa T -> kappa.(indirect_reader) = Low -> all_low T.
Proof.
  intros T. induction T as [ s | T1 IH1 T2 IH2 s | T1 IH1 T2 IH2 s | T1 IH1 T2 IH2 s ];
    intros kappa Htr Hk; simpl in *.
  - (* unit *) destruct Htr as [Hle _]. destruct Hle as [Hr Hi].
    destruct s.(indirect_reader); simpl in *; auto.
    exfalso. rewrite Hk in Hi. simpl in Hi. exact Hi.
  - (* sum *) destruct Htr as [Hle [Ht1 Ht2]]. destruct Hle as [Hr Hi].
    split.
    + destruct s.(indirect_reader); simpl in *; auto.
      exfalso. rewrite Hk in Hi. simpl in Hi. exact Hi.
    + split; [apply (IH1 kappa) | apply (IH2 kappa)]; auto.
  - (* prod *) destruct Htr as [Hle [Ht1 Ht2]]. destruct Hle as [Hr Hi].
    split.
    + destruct s.(indirect_reader); simpl in *; auto.
      exfalso. rewrite Hk in Hi. simpl in Hi. exact Hi.
    + split; [apply (IH1 kappa) | apply (IH2 kappa)]; auto.
  - (* arrow *) destruct Htr as [Hle [Ht1 Ht2]]. destruct Hle as [Hr Hi].
    split.
    + destruct s.(indirect_reader); simpl in *; auto.
      exfalso. rewrite Hk in Hi. simpl in Hi. exact Hi.
    + split; [apply (IH1 kappa) | apply (IH2 kappa)]; auto.
Qed.

Lemma VR_erase : forall T v1 v2,
  ground T -> all_low T -> VR T (security_of T) v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  intros T. induction T as [ s | T1 IH1 T2 IH2 s | T1 IH1 T2 IH2 s | T1 IH1 T2 IH2 s ];
    intros v1 v2 Hg Hl HVR; simpl in *.
  - (* unit *) destruct Hl as [Hlow _].
    destruct HVR as [_ [_ [Hh | Hshape]]].
    + rewrite Hlow in Hh. discriminate.
    + destruct Hshape as [k1 [k2 [E1 E2]]]. rewrite E1, E2. reflexivity.
  - (* sum *) destruct Hg as [Hg1 Hg2]. destruct Hl as [Hlow [Hl1 Hl2]].
    destruct HVR as [_ [_ [Hh | Hstruct]]].
    + rewrite Hlow in Hh. discriminate.
    + destruct Hstruct as
        [[k1 [k2 [w1 [w2 [E1 [E2 HR]]]]]] |
         [k1 [k2 [w1 [w2 [E1 [E2 HR]]]]]]].
      * rewrite E1, E2. simpl. rewrite (IH1 w1 w2 Hg1 Hl1 HR). reflexivity.
      * rewrite E1, E2. simpl. rewrite (IH2 w1 w2 Hg2 Hl2 HR). reflexivity.
  - (* prod *) destruct Hg as [Hg1 Hg2]. destruct Hl as [Hlow [Hl1 Hl2]].
    destruct HVR as [_ [_ [Hh | Hstruct]]].
    + rewrite Hlow in Hh. discriminate.
    + destruct Hstruct as [k1 [k2 [w1 [w2 [x1 [x2 [E1 [E2 [HR1 HR2]]]]]]]]].
      rewrite E1, E2. simpl.
      rewrite (IH1 w1 w2 Hg1 Hl1 HR1), (IH2 x1 x2 Hg2 Hl2 HR2). reflexivity.
  - (* arrow *) destruct Hg.
Qed.

(* ================================================================ *)
(* Section 15: sum-relation helpers and coherence                   *)
(* ================================================================ *)

Lemma VR_sum_inl : forall T1 T2 kappa w1 w2 ka1 ka2,
  kappa.(indirect_reader) = Low ->
  VR (Ty_Sum T1 T2 kappa) kappa (tm_inl w1 ka1) (tm_inl w2 ka2) ->
  VR T1 (security_of T1) w1 w2.
Proof.
  intros T1 T2 kappa w1 w2 ka1 ka2 Hlow HVR.
  destruct (VR_sum_low T1 T2 kappa (tm_inl w1 ka1) (tm_inl w2 ka2) Hlow HVR) as [H | H].
  - destruct H as [k1 [k2 [v1 [v2 [E1 [E2 HR]]]]]].
    injection E1 as Ev1 _. injection E2 as Ev2 _. subst v1. subst v2. exact HR.
  - destruct H as [k1 [k2 [v1 [v2 [E1 [E2 HR]]]]]]. discriminate E1.
Qed.

Lemma VR_sum_inr : forall T1 T2 kappa w1 w2 ka1 ka2,
  kappa.(indirect_reader) = Low ->
  VR (Ty_Sum T1 T2 kappa) kappa (tm_inr w1 ka1) (tm_inr w2 ka2) ->
  VR T2 (security_of T2) w1 w2.
Proof.
  intros T1 T2 kappa w1 w2 ka1 ka2 Hlow HVR.
  destruct (VR_sum_low T1 T2 kappa (tm_inr w1 ka1) (tm_inr w2 ka2) Hlow HVR) as [H | H].
  - destruct H as [k1 [k2 [v1 [v2 [E1 [E2 HR]]]]]]. discriminate E1.
  - destruct H as [k1 [k2 [v1 [v2 [E1 [E2 HR]]]]]].
    injection E1 as Ev1 _. injection E2 as Ev2 _. subst v1. subst v2. exact HR.
Qed.

Lemma VR_sum_mismatch_lr : forall T1 T2 kappa w1 w2 ka1 ka2,
  kappa.(indirect_reader) = Low ->
  VR (Ty_Sum T1 T2 kappa) kappa (tm_inl w1 ka1) (tm_inr w2 ka2) -> False.
Proof.
  intros T1 T2 kappa w1 w2 ka1 ka2 Hlow HVR.
  destruct (VR_sum_low T1 T2 kappa (tm_inl w1 ka1) (tm_inr w2 ka2) Hlow HVR) as [H | H].
  - destruct H as [k1 [k2 [v1 [v2 [E1 [E2 HR]]]]]]. discriminate E2.
  - destruct H as [k1 [k2 [v1 [v2 [E1 [E2 HR]]]]]]. discriminate E1.
Qed.

Lemma VR_sum_mismatch_rl : forall T1 T2 kappa w1 w2 ka1 ka2,
  kappa.(indirect_reader) = Low ->
  VR (Ty_Sum T1 T2 kappa) kappa (tm_inr w1 ka1) (tm_inl w2 ka2) -> False.
Proof.
  intros T1 T2 kappa w1 w2 ka1 ka2 Hlow HVR.
  destruct (VR_sum_low T1 T2 kappa (tm_inr w1 ka1) (tm_inl w2 ka2) Hlow HVR) as [H | H].
  - destruct H as [k1 [k2 [v1 [v2 [E1 [E2 HR]]]]]]. discriminate E1.
  - destruct H as [k1 [k2 [v1 [v2 [E1 [E2 HR]]]]]]. discriminate E2.
Qed.

Lemma sec_low_of_coh : forall v kappa,
  kappa.(indirect_reader) = Low ->
  flows_to (sec_of_tm v).(indirect_reader) kappa.(indirect_reader) ->
  (sec_of_tm v).(indirect_reader) = Low.
Proof.
  intros v kappa Hlow Hfl.
  destruct (sec_of_tm v).(indirect_reader); auto.
  exfalso. rewrite Hlow in Hfl. simpl in Hfl. exact Hfl.
Qed.

(* ================================================================ *)
(* Section 16: further relation helpers                             *)
(* ================================================================ *)

Lemma VR_secret : forall T v1 v2, VR T secret v1 v2.
Proof.
  intros T. destruct T; intros v1 v2; simpl;
    (split; [ apply flows_to_high | split; [ apply flows_to_high | left; reflexivity ] ]).
Qed.

Lemma VR_protected_high : forall T v1 v2,
  VR T (protect_security (security_of T) High) v1 v2.
Proof.
  intros T v1 v2. rewrite protect_security_high. apply VR_secret.
Qed.

Lemma VR_ty_protect_fwd : forall T l kappa v1 v2,
  VR (ty_protect l T) kappa v1 v2 -> VR T kappa v1 v2.
Proof. intros T l kappa v1 v2. destruct T; simpl; auto. Qed.

Lemma VR_ty_protect_bwd : forall T l kappa v1 v2,
  VR T kappa v1 v2 -> VR (ty_protect l T) kappa v1 v2.
Proof. intros T l kappa v1 v2. destruct T; simpl; auto. Qed.

Lemma env_rel_body : forall Gamma gamma1 gamma2 x T1 w1 w2,
  env_rel Gamma gamma1 gamma2 -> value w1 -> value w2 ->
  VR T1 (security_of T1) w1 w2 ->
  env_rel (update Gamma x T1) (extend gamma1 x w1) (extend gamma2 x w2).
Proof.
  intros. apply env_rel_update; auto. apply IR_of_values; auto.
Qed.

Lemma body_rel_apply : forall T body gamma1 gamma2 w1 w2 x0 x1 x2,
  (forall y, lc_at 0 (gamma1 y)) ->
  (forall y, lc_at 0 (gamma2 y)) ->
  value w1 -> value w2 ->
  ~ In x0 (fv body) ->
  IR T (subst_env (extend gamma1 x0 w1) (open body (tm_fvar x0)))
       (subst_env (extend gamma2 x0 w2) (open body (tm_fvar x0))) ->
  multi (open (subst_env gamma1 body) w1) x1 -> value x1 ->
  multi (open (subst_env gamma2 body) w2) x2 -> value x2 ->
  VR T (security_of T) x1 x2.
Proof.
  intros T body gamma1 gamma2 w1 w2 x0 x1 x2 Hlc1 Hlc2 Hv1 Hv2 Hfresh HB Hm1 Hx1 Hm2 Hx2.
  assert (Hop1 : subst_env (extend gamma1 x0 w1) (open body (tm_fvar x0)) =
                 open (subst_env gamma1 body) w1).
  { apply subst_env_open_extend; auto. apply value_lc; exact Hv1. }
  assert (Hop2 : subst_env (extend gamma2 x0 w2) (open body (tm_fvar x0)) =
                 open (subst_env gamma2 body) w2).
  { apply subst_env_open_extend; auto. apply value_lc; exact Hv2. }
  unfold IR in HB.
  apply HB.
  - rewrite Hop1. split; assumption.
  - rewrite Hop2. split; assumption.
Qed.

(* ================================================================ *)
(* Section 17: the fundamental theorem                              *)
(* ================================================================ *)

Lemma fundamental : forall Gamma t T, has_type Gamma t T ->
  forall gamma1 gamma2, env_rel Gamma gamma1 gamma2 ->
  IR T (subst_env gamma1 t) (subst_env gamma2 t).
Proof.
  intros Gamma t T H.
  induction H as
    [ Gamma x T Hlook Hwf
    | Gamma kappa Hwf
    | L Gamma T1 body T2 kappa HwfT1 Hwfkap Hbody IHbody
    | Gamma t1 t2 T1 T2 kappa r H1 IH1 H2 IH2 Hflow
    | Gamma t1 t2 T1 T2 kappa H1 IH1 H2 IH2 Hwf
    | Gamma t T1 T2 kappa r H1 IH1 Hflow
    | Gamma t T1 T2 kappa r H1 IH1 Hflow
    | Gamma t T1 T2 kappa H1 IH1 HwfT2 Hwfkap
    | Gamma t T1 T2 kappa HwfT1 H1 IH1 Hwfkap
    | L Gamma t body1 body2 T1 T2 T kappa r H1 IH1 Hflow Hb1 IHb1 Hb2 IHb2
    | Gamma t T l H1 IH1
    | Gamma t T U H1 IH1 Hsub
    | Gamma c yes no k T r H1 IH1 H2 IH2 H3 IH3 Hflow ];
  intros gamma1 gamma2 Henv; simpl.
  - (* T_Var *) pose proof (proj1 Henv) as Hlc1.
    pose proof (proj1 (proj2 Henv)) as Hlc2.
    pose proof (proj2 (proj2 Henv)) as HIR. exact (HIR x T Hlook).
  - (* T_Unit *)
    unfold IR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    assert (E1 : v1 = tm_unit kappa) by (apply multi_value with (t := tm_unit kappa); [exact Hm1 | apply v_unit]).
    assert (E2 : v2 = tm_unit kappa) by (apply multi_value with (t := tm_unit kappa); [exact Hm2 | apply v_unit]).
    subst v1; subst v2. simpl.
    split. { apply flows_to_refl. }
    split. { apply flows_to_refl. }
    destruct (kappa.(indirect_reader)) eqn:Ek.
    + right. exists kappa, kappa. split; reflexivity.
    + left. reflexivity.
  - (* T_Abs *)
    unfold IR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    pose proof (proj1 Henv) as Hlc1.
    pose proof (proj1 (proj2 Henv)) as Hlc2.
    pose proof (proj2 (proj2 Henv)) as HIR.
    assert (Hbody_lc : lc_at 1 body) by (apply (typing_open_lc L Gamma T1 body T2 Hbody)).
    assert (Hva1 : value (tm_abs T1 (subst_env gamma1 body) kappa)).
    { apply v_abs. simpl. apply subst_env_lc; [exact Hlc1 | exact Hbody_lc]. }
    assert (Hva2 : value (tm_abs T1 (subst_env gamma2 body) kappa)).
    { apply v_abs. simpl. apply subst_env_lc; [exact Hlc2 | exact Hbody_lc]. }
    assert (E1 : v1 = tm_abs T1 (subst_env gamma1 body) kappa)
      by (apply multi_value with (t := tm_abs T1 (subst_env gamma1 body) kappa); auto).
    assert (E2 : v2 = tm_abs T1 (subst_env gamma2 body) kappa)
      by (apply multi_value with (t := tm_abs T1 (subst_env gamma2 body) kappa); auto).
    subst v1; subst v2. simpl.
    split. { apply flows_to_refl. }
    split. { apply flows_to_refl. }
    destruct (kappa.(indirect_reader)) eqn:Ek; [idtac | left; reflexivity].
    right. intros r w1 w2 Hw1 Hw2 Hfl Hrel u1 u2 Hu1 Hu2.
      destruct Hu1 as [Hu1m Hu1v]. destruct Hu2 as [Hu2m Hu2v].
      assert (Hprot1 : multi (tm_protect kappa.(indirect_reader) (open (subst_env gamma1 body) w1)) u1).
      { exact (multi_app_abs_inv T1 (subst_env gamma1 body) kappa w1 r u1 Hw1 Hfl Hu1m Hu1v). }
      assert (Hprot2 : multi (tm_protect kappa.(indirect_reader) (open (subst_env gamma2 body) w2)) u2).
      { exact (multi_app_abs_inv T1 (subst_env gamma2 body) kappa w2 r u2 Hw2 Hfl Hu2m Hu2v). }
      destruct (multi_protect_inv (tm_protect kappa.(indirect_reader) (open (subst_env gamma1 body) w1))
                  u1 Hprot1 Hu1v kappa.(indirect_reader) (open (subst_env gamma1 body) w1) eq_refl)
        as [x1 [Hx1m [Hx1v Heq1]]].
      destruct (multi_protect_inv (tm_protect kappa.(indirect_reader) (open (subst_env gamma2 body) w2))
                  u2 Hprot2 Hu2v kappa.(indirect_reader) (open (subst_env gamma2 body) w2) eq_refl)
        as [x2 [Hx2m [Hx2v Heq2]]].
      pose proof (fresh_spec (L ++ fv body)) as Hx0.
      assert (HxL : ~ In (fresh (L ++ fv body)) L).
      { apply (not_in_app_l (fresh (L ++ fv body)) L (fv body)). exact Hx0. }
      assert (Hxb : ~ In (fresh (L ++ fv body)) (fv body)).
      { apply (not_in_app_r (fresh (L ++ fv body)) L (fv body)). exact Hx0. }
      assert (Henv' : env_rel (update Gamma (fresh (L ++ fv body)) T1)
                            (extend gamma1 (fresh (L ++ fv body)) w1)
                            (extend gamma2 (fresh (L ++ fv body)) w2)).
      { apply env_rel_body.
        - split; [exact Hlc1 | split; [exact Hlc2 | exact HIR]].
        - exact Hw1.
        - exact Hw2.
        - exact Hrel. }
      pose proof (IHbody (fresh (L ++ fv body)) HxL
                    (extend gamma1 (fresh (L ++ fv body)) w1)
                    (extend gamma2 (fresh (L ++ fv body)) w2) Henv') as HB.
      assert (Hbodyrel : VR T2 (security_of T2) x1 x2).
      { apply (body_rel_apply T2 body gamma1 gamma2 w1 w2 (fresh (L ++ fv body)) x1 x2);
          auto. }
      rewrite protect_security_low.
      rewrite Heq1, Heq2, Ek, !protect_value_low.
      exact Hbodyrel.
  - (* T_App *)
    unfold IR. intros u1 u2 [Hm1 Hv1] [Hm2 Hv2].
    pose proof (proj1 Henv) as Hlc1.
    pose proof (proj1 (proj2 Henv)) as Hlc2.
    pose proof (proj2 (proj2 Henv)) as HIR.
    rewrite security_of_ty_protect.
    destruct (multi_app_inv (tm_app (subst_env gamma1 t1) (subst_env gamma1 t2) r) u1 Hm1 Hv1
                (subst_env gamma1 t1) (subst_env gamma1 t2) r eq_refl)
      as [vf1 [va1 [Hmf1 [Hma1 [Hvf1 [Hva1 Hmapp1]]]]]].
    destruct (multi_app_inv (tm_app (subst_env gamma2 t1) (subst_env gamma2 t2) r) u2 Hm2 Hv2
                (subst_env gamma2 t1) (subst_env gamma2 t2) r eq_refl)
      as [vf2 [va2 [Hmf2 [Hma2 [Hvf2 [Hva2 Hmapp2]]]]]].
    assert (HVRf : VR (Ty_Arrow T1 T2 kappa) kappa vf1 vf2).
    { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv); split; assumption. }
    assert (HVRa : VR T1 (security_of T1) va1 va2).
    { unfold IR in IH2. apply (IH2 gamma1 gamma2 Henv); split; assumption. }
    destruct (kappa.(indirect_reader)) eqn:Ek; [idtac | rewrite protect_security_high; apply VR_secret].
    assert (Hres := VR_arrow_low T1 T2 kappa vf1 vf2 Ek HVRf r va1 va2
                     Hva1 Hva2 Hflow HVRa u1 u2 (conj Hmapp1 Hv1) (conj Hmapp2 Hv2)).
    rewrite Ek in Hres. apply VR_ty_protect_bwd. exact Hres.
  - (* T_Pair *)
    unfold IR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct (multi_pair_inv (tm_pair (subst_env gamma1 t1) (subst_env gamma1 t2) kappa) v1 Hm1 Hv1
                (subst_env gamma1 t1) (subst_env gamma1 t2) kappa eq_refl)
      as [u1 [u2 [E1 [Hm1' [Hm2' [Hv1' Hv2']]]]]].
    destruct (multi_pair_inv (tm_pair (subst_env gamma2 t1) (subst_env gamma2 t2) kappa) v2 Hm2 Hv2
                (subst_env gamma2 t1) (subst_env gamma2 t2) kappa eq_refl)
      as [u1b [u2b [E1b [Hm1b [Hm2b [Hv1b Hv2b]]]]]].
    assert (HVR1 : VR T1 (security_of T1) u1 u1b).
    { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv); split; assumption. }
    assert (HVR2 : VR T2 (security_of T2) u2 u2b).
    { unfold IR in IH2. apply (IH2 gamma1 gamma2 Henv); split; assumption. }
    subst v1; subst v2. simpl.
    split. { apply flows_to_refl. }
    split. { apply flows_to_refl. }
    destruct (kappa.(indirect_reader)) eqn:Ek; [idtac | left; reflexivity].
    right. exists kappa, kappa, u1, u1b, u2, u2b. repeat split; auto.
  - (* T_Fst *)
    unfold IR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    pose proof (proj1 Henv) as Hlc1.
    pose proof (proj1 (proj2 Henv)) as Hlc2.
    pose proof (proj2 (proj2 Henv)) as HIR.
    rewrite security_of_ty_protect.
    destruct (multi_fst_inv (tm_fst (subst_env gamma1 t) r) v1 Hm1 Hv1
                (subst_env gamma1 t) r eq_refl)
      as [w1 [w2 [k1 [Hmt1 [Hw1 [Hw2 [Hfl1 Heq1]]]]]]].
    destruct (multi_fst_inv (tm_fst (subst_env gamma2 t) r) v2 Hm2 Hv2
                (subst_env gamma2 t) r eq_refl)
      as [w1b [w2b [k2 [Hmt2 [Hw1b [Hw2b [Hfl2 Heq2]]]]]]].
    assert (HVRp : VR (Ty_Prod T1 T2 kappa) kappa (tm_pair w1 w2 k1) (tm_pair w1b w2b k2)).
    { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv).
      - split. { exact Hmt1. } { apply v_pair; assumption. }
      - split. { exact Hmt2. } { apply v_pair; assumption. } }
    destruct (kappa.(indirect_reader)) eqn:Ek; [idtac | rewrite protect_security_high; apply VR_secret].
    destruct (VR_prod_low T1 T2 kappa (tm_pair w1 w2 k1) (tm_pair w1b w2b k2) Ek HVRp)
      as [ka [kb [p1 [q1 [p2 [q2 [Eq1 [Eq2 [HR1 HR2]]]]]]]]].
    injection Eq1 as Ep1 Eq1' Ek1. injection Eq2 as Ep2 Eq2' Ek2.
    subst p1. subst q1. subst ka. subst p2. subst q2. subst kb.
    assert (Hkk1 : k1.(indirect_reader) = Low).
    { pose proof (VR_coh1 (Ty_Prod T1 T2 kappa) kappa (tm_pair w1 w2 k1) (tm_pair w1b w2b k2) HVRp) as Hc.
      simpl in Hc. exact (sec_low_of_coh (tm_pair w1 w2 k1) kappa Ek Hc). }
    assert (Hkk2 : k2.(indirect_reader) = Low).
    { pose proof (VR_coh2 (Ty_Prod T1 T2 kappa) kappa (tm_pair w1 w2 k1) (tm_pair w1b w2b k2) HVRp) as Hc.
      simpl in Hc. exact (sec_low_of_coh (tm_pair w1b w2b k2) kappa Ek Hc). }
    rewrite protect_security_low.
    rewrite Heq1, Heq2, Hkk1, Hkk2, !protect_value_low.
    apply VR_ty_protect_bwd. exact HR1.
  - (* T_Snd *)
    unfold IR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    pose proof (proj1 Henv) as Hlc1.
    pose proof (proj1 (proj2 Henv)) as Hlc2.
    pose proof (proj2 (proj2 Henv)) as HIR.
    rewrite security_of_ty_protect.
    destruct (multi_snd_inv (tm_snd (subst_env gamma1 t) r) v1 Hm1 Hv1
                (subst_env gamma1 t) r eq_refl)
      as [w1 [w2 [k1 [Hmt1 [Hw1 [Hw2 [Hfl1 Heq1]]]]]]].
    destruct (multi_snd_inv (tm_snd (subst_env gamma2 t) r) v2 Hm2 Hv2
                (subst_env gamma2 t) r eq_refl)
      as [w1b [w2b [k2 [Hmt2 [Hw1b [Hw2b [Hfl2 Heq2]]]]]]].
    assert (HVRp : VR (Ty_Prod T1 T2 kappa) kappa (tm_pair w1 w2 k1) (tm_pair w1b w2b k2)).
    { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv).
      - split. { exact Hmt1. } { apply v_pair; assumption. }
      - split. { exact Hmt2. } { apply v_pair; assumption. } }
    destruct (kappa.(indirect_reader)) eqn:Ek; [idtac | rewrite protect_security_high; apply VR_secret].
    destruct (VR_prod_low T1 T2 kappa (tm_pair w1 w2 k1) (tm_pair w1b w2b k2) Ek HVRp)
      as [ka [kb [p1 [q1 [p2 [q2 [Eq1 [Eq2 [HR1 HR2]]]]]]]]].
    injection Eq1 as Ep1 Eq1' Ek1. injection Eq2 as Ep2 Eq2' Ek2.
    subst p1. subst q1. subst ka. subst p2. subst q2. subst kb.
    assert (Hkk1 : k1.(indirect_reader) = Low).
    { pose proof (VR_coh1 (Ty_Prod T1 T2 kappa) kappa (tm_pair w1 w2 k1) (tm_pair w1b w2b k2) HVRp) as Hc.
      simpl in Hc. exact (sec_low_of_coh (tm_pair w1 w2 k1) kappa Ek Hc). }
    assert (Hkk2 : k2.(indirect_reader) = Low).
    { pose proof (VR_coh2 (Ty_Prod T1 T2 kappa) kappa (tm_pair w1 w2 k1) (tm_pair w1b w2b k2) HVRp) as Hc.
      simpl in Hc. exact (sec_low_of_coh (tm_pair w1b w2b k2) kappa Ek Hc). }
    rewrite protect_security_low.
    rewrite Heq1, Heq2, Hkk1, Hkk2, !protect_value_low.
    apply VR_ty_protect_bwd. exact HR2.
  - (* T_Inl *)
    unfold IR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct (multi_inl_inv (tm_inl (subst_env gamma1 t) kappa) v1 Hm1 Hv1
                (subst_env gamma1 t) kappa eq_refl) as [u1 [E1 [Hm1' Hv1']]].
    destruct (multi_inl_inv (tm_inl (subst_env gamma2 t) kappa) v2 Hm2 Hv2
                (subst_env gamma2 t) kappa eq_refl) as [u2 [E2 [Hm2' Hv2']]].
    assert (HVR1 : VR T1 (security_of T1) u1 u2).
    { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv); split; assumption. }
    subst v1; subst v2. simpl.
    split. { apply flows_to_refl. }
    split. { apply flows_to_refl. }
    destruct (kappa.(indirect_reader)) eqn:Ek; [idtac | left; reflexivity].
    right. left. exists kappa, kappa, u1, u2. repeat split; auto.
  - (* T_Inr *)
    unfold IR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct (multi_inr_inv (tm_inr (subst_env gamma1 t) kappa) v1 Hm1 Hv1
                (subst_env gamma1 t) kappa eq_refl) as [u1 [E1 [Hm1' Hv1']]].
    destruct (multi_inr_inv (tm_inr (subst_env gamma2 t) kappa) v2 Hm2 Hv2
                (subst_env gamma2 t) kappa eq_refl) as [u2 [E2 [Hm2' Hv2']]].
    assert (HVR1 : VR T2 (security_of T2) u1 u2).
    { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv); split; assumption. }
    subst v1; subst v2. simpl.
    split. { apply flows_to_refl. }
    split. { apply flows_to_refl. }
    destruct (kappa.(indirect_reader)) eqn:Ek; [idtac | left; reflexivity].
    right. right. exists kappa, kappa, u1, u2. repeat split; auto.
  - (* T_Case *)
    unfold IR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    rewrite security_of_ty_protect.
    destruct (kappa.(indirect_reader)) eqn:Ek.
    + pose proof (proj1 Henv) as Hlc1.
    pose proof (proj1 (proj2 Henv)) as Hlc2.
    pose proof (proj2 (proj2 Henv)) as HIR.
      pose proof (fresh_spec (L ++ fv body1 ++ fv body2)) as Hx0.
      assert (HxL : ~ In (fresh (L ++ fv body1 ++ fv body2)) L).
      { apply (not_in_app_l (fresh (L ++ fv body1 ++ fv body2)) L (fv body1 ++ fv body2)). exact Hx0. }
      assert (Hxb1 : ~ In (fresh (L ++ fv body1 ++ fv body2)) (fv body1)).
      { apply (not_in_app_l (fresh (L ++ fv body1 ++ fv body2)) (fv body1) (fv body2)).
        apply (not_in_app_r (fresh (L ++ fv body1 ++ fv body2)) L (fv body1 ++ fv body2)). exact Hx0. }
      assert (Hxb2 : ~ In (fresh (L ++ fv body1 ++ fv body2)) (fv body2)).
      { apply (not_in_app_r (fresh (L ++ fv body1 ++ fv body2)) (fv body1) (fv body2)).
        apply (not_in_app_r (fresh (L ++ fv body1 ++ fv body2)) L (fv body1 ++ fv body2)). exact Hx0. }
      destruct (multi_case_inv (tm_case (subst_env gamma1 t) (subst_env gamma1 body1) (subst_env gamma1 body2) r)
                  v1 Hm1 Hv1 (subst_env gamma1 t) (subst_env gamma1 body1) (subst_env gamma1 body2) r eq_refl)
        as [D1l | D1r].
      * destruct (multi_case_inv (tm_case (subst_env gamma2 t) (subst_env gamma2 body1) (subst_env gamma2 body2) r)
                    v2 Hm2 Hv2 (subst_env gamma2 t) (subst_env gamma2 body1) (subst_env gamma2 body2) r eq_refl)
          as [D2l | D2r].
        -- (* both inl *)
           destruct D1l as [w1 [ka1 [x1 [Hmt1 [Hw1 [Hfl1 [Hmx1 [Hx1 Heq1]]]]]]]].
           destruct D2l as [w2 [ka2 [x2 [Hmt2 [Hw2 [Hfl2 [Hmx2 [Hx2 Heq2]]]]]]]].
           assert (EVR : VR (Ty_Sum T1 T2 kappa) kappa (tm_inl w1 ka1) (tm_inl w2 ka2)).
           { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv).
             - split. { exact Hmt1. } { apply v_inl; exact Hw1. }
             - split. { exact Hmt2. } { apply v_inl; exact Hw2. } }
           assert (Hrelw : VR T1 (security_of T1) w1 w2).
           { apply (VR_sum_inl T1 T2 kappa w1 w2 ka1 ka2 Ek EVR). }
           assert (Hka1 : ka1.(indirect_reader) = Low).
           { pose proof (VR_coh1 (Ty_Sum T1 T2 kappa) kappa (tm_inl w1 ka1) (tm_inl w2 ka2) EVR) as Hc.
             simpl in Hc. exact (sec_low_of_coh (tm_inl w1 ka1) kappa Ek Hc). }
           assert (Hka2 : ka2.(indirect_reader) = Low).
           { pose proof (VR_coh2 (Ty_Sum T1 T2 kappa) kappa (tm_inl w1 ka1) (tm_inl w2 ka2) EVR) as Hc.
             simpl in Hc. exact (sec_low_of_coh (tm_inl w2 ka2) kappa Ek Hc). }
           assert (Henv' : env_rel (update Gamma (fresh (L ++ fv body1 ++ fv body2)) T1)
                                 (extend gamma1 (fresh (L ++ fv body1 ++ fv body2)) w1)
                                 (extend gamma2 (fresh (L ++ fv body1 ++ fv body2)) w2)).
           { apply env_rel_body.
             - split; [exact Hlc1 | split; [exact Hlc2 | exact HIR]].
             - exact Hw1.
             - exact Hw2.
             - exact Hrelw. }
           pose proof (IHb1 (fresh (L ++ fv body1 ++ fv body2)) HxL
                         (extend gamma1 (fresh (L ++ fv body1 ++ fv body2)) w1)
                         (extend gamma2 (fresh (L ++ fv body1 ++ fv body2)) w2) Henv') as HB.
           assert (Hbodyrel : VR T (security_of T) x1 x2).
           { apply (body_rel_apply T body1 gamma1 gamma2 w1 w2
                      (fresh (L ++ fv body1 ++ fv body2)) x1 x2); auto. }
           rewrite protect_security_low.
           rewrite Heq1, Heq2, Hka1, Hka2, !protect_value_low.
           apply VR_ty_protect_bwd. exact Hbodyrel.
        -- (* inl / inr mismatch *)
           destruct D1l as [w1 [ka1 [x1 [Hmt1 [Hw1 [Hfl1 [Hmx1 [Hx1 Heq1]]]]]]]].
           destruct D2r as [w2r [ka2r [x2r [Hmt2r [Hw2r [Hfl2r [Hmx2r [Hx2r Heq2r]]]]]]]].
           assert (EVR : VR (Ty_Sum T1 T2 kappa) kappa (tm_inl w1 ka1) (tm_inr w2r ka2r)).
           { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv).
             - split. { exact Hmt1. } { apply v_inl; exact Hw1. }
             - split. { exact Hmt2r. } { apply v_inr; exact Hw2r. } }
           exfalso. exact (VR_sum_mismatch_lr T1 T2 kappa w1 w2r ka1 ka2r Ek EVR).
      * destruct (multi_case_inv (tm_case (subst_env gamma2 t) (subst_env gamma2 body1) (subst_env gamma2 body2) r)
                    v2 Hm2 Hv2 (subst_env gamma2 t) (subst_env gamma2 body1) (subst_env gamma2 body2) r eq_refl)
          as [D2l | D2r].
        -- (* inr / inl mismatch *)
           destruct D1r as [w1r [ka1r [x1r [Hmt1r [Hw1r [Hfl1r [Hmx1r [Hx1r Heq1r]]]]]]]].
           destruct D2l as [w2 [ka2 [x2 [Hmt2 [Hw2 [Hfl2 [Hmx2 [Hx2 Heq2]]]]]]]].
           assert (EVR : VR (Ty_Sum T1 T2 kappa) kappa (tm_inr w1r ka1r) (tm_inl w2 ka2)).
           { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv).
             - split. { exact Hmt1r. } { apply v_inr; exact Hw1r. }
             - split. { exact Hmt2. } { apply v_inl; exact Hw2. } }
           exfalso. exact (VR_sum_mismatch_rl T1 T2 kappa w1r w2 ka1r ka2 Ek EVR).
        -- (* both inr *)
           destruct D1r as [w1r [ka1r [x1r [Hmt1r [Hw1r [Hfl1r [Hmx1r [Hx1r Heq1r]]]]]]]].
           destruct D2r as [w2r [ka2r [x2r [Hmt2r [Hw2r [Hfl2r [Hmx2r [Hx2r Heq2r]]]]]]]].
           assert (EVR : VR (Ty_Sum T1 T2 kappa) kappa (tm_inr w1r ka1r) (tm_inr w2r ka2r)).
           { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv).
             - split. { exact Hmt1r. } { apply v_inr; exact Hw1r. }
             - split. { exact Hmt2r. } { apply v_inr; exact Hw2r. } }
           assert (Hrelw : VR T2 (security_of T2) w1r w2r).
           { apply (VR_sum_inr T1 T2 kappa w1r w2r ka1r ka2r Ek EVR). }
           assert (Hka1 : ka1r.(indirect_reader) = Low).
           { pose proof (VR_coh1 (Ty_Sum T1 T2 kappa) kappa (tm_inr w1r ka1r) (tm_inr w2r ka2r) EVR) as Hc.
             simpl in Hc. exact (sec_low_of_coh (tm_inr w1r ka1r) kappa Ek Hc). }
           assert (Hka2 : ka2r.(indirect_reader) = Low).
           { pose proof (VR_coh2 (Ty_Sum T1 T2 kappa) kappa (tm_inr w1r ka1r) (tm_inr w2r ka2r) EVR) as Hc.
             simpl in Hc. exact (sec_low_of_coh (tm_inr w2r ka2r) kappa Ek Hc). }
           assert (Henv' : env_rel (update Gamma (fresh (L ++ fv body1 ++ fv body2)) T2)
                                 (extend gamma1 (fresh (L ++ fv body1 ++ fv body2)) w1r)
                                 (extend gamma2 (fresh (L ++ fv body1 ++ fv body2)) w2r)).
           { apply env_rel_body.
             - split; [exact Hlc1 | split; [exact Hlc2 | exact HIR]].
             - exact Hw1r.
             - exact Hw2r.
             - exact Hrelw. }
           pose proof (IHb2 (fresh (L ++ fv body1 ++ fv body2)) HxL
                         (extend gamma1 (fresh (L ++ fv body1 ++ fv body2)) w1r)
                         (extend gamma2 (fresh (L ++ fv body1 ++ fv body2)) w2r) Henv') as HB.
           assert (Hbodyrel : VR T (security_of T) x1r x2r).
           { apply (body_rel_apply T body2 gamma1 gamma2 w1r w2r
                      (fresh (L ++ fv body1 ++ fv body2)) x1r x2r); auto. }
           rewrite protect_security_low.
           rewrite Heq1r, Heq2r, Hka1, Hka2, !protect_value_low.
           apply VR_ty_protect_bwd. exact Hbodyrel.
    + rewrite protect_security_high. apply VR_secret.
  - (* T_Protect *)
    unfold IR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    rewrite security_of_ty_protect.
    destruct (multi_protect_inv (tm_protect l (subst_env gamma1 t)) v1 Hm1 Hv1 l (subst_env gamma1 t) eq_refl)
      as [u1 [Hm1' [Hv1' Heq1]]].
    destruct (multi_protect_inv (tm_protect l (subst_env gamma2 t)) v2 Hm2 Hv2 l (subst_env gamma2 t) eq_refl)
      as [u2 [Hm2' [Hv2' Heq2]]].
    subst v1; subst v2.
    apply VR_ty_protect_bwd.
    apply VR_protect with (l1 := l) (l2 := l).
    + apply flows_to_refl.
    + unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv); split; assumption.
  - (* T_Sub *)
    unfold IR in *. intros v1 v2 E1 E2.
    eapply subtype_VR.
    + exact Hsub.
    + apply (IH1 gamma1 gamma2 Henv); auto.
  - (* T_If *)
    unfold IR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    rewrite security_of_ty_protect.
    destruct (k.(indirect_reader)) eqn:Ek.
    + pose proof (proj1 Henv) as Hlc1.
    pose proof (proj1 (proj2 Henv)) as Hlc2.
    pose proof (proj2 (proj2 Henv)) as HIR.
      destruct (multi_if_inv (tm_if (subst_env gamma1 c) (subst_env gamma1 yes) (subst_env gamma1 no) r)
                  v1 Hm1 Hv1 (subst_env gamma1 c) (subst_env gamma1 yes) (subst_env gamma1 no) r eq_refl)
        as [D1l | D1r].
      * destruct (multi_if_inv (tm_if (subst_env gamma2 c) (subst_env gamma2 yes) (subst_env gamma2 no) r)
                    v2 Hm2 Hv2 (subst_env gamma2 c) (subst_env gamma2 yes) (subst_env gamma2 no) r eq_refl)
          as [D2l | D2r].
        -- (* both inl *)
           destruct D1l as [wc1 [ka1 [u1 [Hmc1 [Hwc1 [Hfl1 [Hmu1 [Hu1 Heq1]]]]]]]].
           destruct D2l as [wc2 [ka2 [u2 [Hmc2 [Hwc2 [Hfl2 [Hmu2 [Hu2 Heq2]]]]]]]].
           assert (EVR : VR (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) k
                            (tm_inl wc1 ka1) (tm_inl wc2 ka2)).
           { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv).
             - split. { exact Hmc1. } { apply v_inl; exact Hwc1. }
             - split. { exact Hmc2. } { apply v_inl; exact Hwc2. } }
           assert (Hka1 : ka1.(indirect_reader) = Low).
           { pose proof (VR_coh1 (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) k
                            (tm_inl wc1 ka1) (tm_inl wc2 ka2) EVR) as Hc.
             simpl in Hc. exact (sec_low_of_coh (tm_inl wc1 ka1) k Ek Hc). }
           assert (Hka2 : ka2.(indirect_reader) = Low).
           { pose proof (VR_coh2 (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) k
                            (tm_inl wc1 ka1) (tm_inl wc2 ka2) EVR) as Hc.
             simpl in Hc. exact (sec_low_of_coh (tm_inl wc2 ka2) k Ek Hc). }
           assert (Hbodyrel : VR T (security_of T) u1 u2).
           { unfold IR in IH2. apply (IH2 gamma1 gamma2 Henv); split; assumption. }
           rewrite protect_security_low.
           rewrite Heq1, Heq2, Hka1, Hka2, !protect_value_low.
           apply VR_ty_protect_bwd. exact Hbodyrel.
        -- (* inl / inr mismatch *)
           destruct D1l as [wc1 [ka1 [u1 [Hmc1 [Hwc1 [Hfl1 [Hmu1 [Hu1 Heq1]]]]]]]].
           destruct D2r as [wc2r [ka2r [u2r [Hmc2r [Hwc2r [Hfl2r [Hmu2r [Hu2r Heq2r]]]]]]]].
           assert (EVR : VR (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) k
                            (tm_inl wc1 ka1) (tm_inr wc2r ka2r)).
           { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv).
             - split. { exact Hmc1. } { apply v_inl; exact Hwc1. }
             - split. { exact Hmc2r. } { apply v_inr; exact Hwc2r. } }
           exfalso. exact (VR_sum_mismatch_lr (Ty_Unit public) (Ty_Unit public) k wc1 wc2r ka1 ka2r Ek EVR).
      * destruct (multi_if_inv (tm_if (subst_env gamma2 c) (subst_env gamma2 yes) (subst_env gamma2 no) r)
                    v2 Hm2 Hv2 (subst_env gamma2 c) (subst_env gamma2 yes) (subst_env gamma2 no) r eq_refl)
          as [D2l | D2r].
        -- (* inr / inl mismatch *)
           destruct D1r as [wc1r [ka1r [u1r [Hmc1r [Hwc1r [Hfl1r [Hmu1r [Hu1r Heq1r]]]]]]]].
           destruct D2l as [wc2 [ka2 [u2 [Hmc2 [Hwc2 [Hfl2 [Hmu2 [Hu2 Heq2]]]]]]]].
           assert (EVR : VR (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) k
                            (tm_inr wc1r ka1r) (tm_inl wc2 ka2)).
           { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv).
             - split. { exact Hmc1r. } { apply v_inr; exact Hwc1r. }
             - split. { exact Hmc2. } { apply v_inl; exact Hwc2. } }
           exfalso. exact (VR_sum_mismatch_rl (Ty_Unit public) (Ty_Unit public) k wc1r wc2 ka1r ka2 Ek EVR).
        -- (* both inr *)
           destruct D1r as [wc1r [ka1r [u1r [Hmc1r [Hwc1r [Hfl1r [Hmu1r [Hu1r Heq1r]]]]]]]].
           destruct D2r as [wc2r [ka2r [u2r [Hmc2r [Hwc2r [Hfl2r [Hmu2r [Hu2r Heq2r]]]]]]]].
           assert (EVR : VR (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) k
                            (tm_inr wc1r ka1r) (tm_inr wc2r ka2r)).
           { unfold IR in IH1. apply (IH1 gamma1 gamma2 Henv).
             - split. { exact Hmc1r. } { apply v_inr; exact Hwc1r. }
             - split. { exact Hmc2r. } { apply v_inr; exact Hwc2r. } }
           assert (Hka1 : ka1r.(indirect_reader) = Low).
           { pose proof (VR_coh1 (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) k
                            (tm_inr wc1r ka1r) (tm_inr wc2r ka2r) EVR) as Hc.
             simpl in Hc. exact (sec_low_of_coh (tm_inr wc1r ka1r) k Ek Hc). }
           assert (Hka2 : ka2r.(indirect_reader) = Low).
           { pose proof (VR_coh2 (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) k
                            (tm_inr wc1r ka1r) (tm_inr wc2r ka2r) EVR) as Hc.
             simpl in Hc. exact (sec_low_of_coh (tm_inr wc2r ka2r) k Ek Hc). }
           assert (Hbodyrel : VR T (security_of T) u1r u2r).
           { unfold IR in IH3. apply (IH3 gamma1 gamma2 Henv); split; assumption. }
           rewrite protect_security_low.
           rewrite Heq1r, Heq2r, Hka1, Hka2, !protect_value_low.
           apply VR_ty_protect_bwd. exact Hbodyrel.
      + rewrite protect_security_high. apply VR_secret.
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 HC Hg Htr Hnf.
  unfold same_result. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
  destruct HC as [L HC].
  assert (Hx0 : ~ In (fresh (L ++ fv_context C)) (L ++ fv_context C)) by (apply fresh_spec).
  assert (HxL : ~ In (fresh (L ++ fv_context C)) L).
  { apply (not_in_app_l (fresh (L ++ fv_context C)) L (fv_context C)). exact Hx0. }
  assert (HxC : ~ In (fresh (L ++ fv_context C)) (fv_context C)).
  { apply (not_in_app_r (fresh (L ++ fv_context C)) L (fv_context C)). exact Hx0. }
  pose proof (HC (fresh (L ++ fv_context C)) HxL) as Htyped.
  assert (Hself1 : IR T_secret t1 t1).
  { pose proof (fundamental empty t1 T_secret Ht1
                  (fun y => tm_fvar y) (fun y => tm_fvar y)) as Hf.
    assert (Henv_empty : env_rel empty (fun y => tm_fvar y) (fun y => tm_fvar y)).
    { apply env_rel_intro.
      - intros y. exact I.
      - intros y. exact I.
      - intros y T Hlook. simpl in Hlook. discriminate. }
    specialize (Hf Henv_empty).
    rewrite subst_env_id in Hf. exact Hf. }
  assert (Hself2 : IR T_secret t2 t2).
  { pose proof (fundamental empty t2 T_secret Ht2
                  (fun y => tm_fvar y) (fun y => tm_fvar y)) as Hf.
    assert (Henv_empty : env_rel empty (fun y => tm_fvar y) (fun y => tm_fvar y)).
    { apply env_rel_intro.
      - intros y. exact I.
      - intros y. exact I.
      - intros y T Hlook. simpl in Hlook. discriminate. }
    specialize (Hf Henv_empty).
    rewrite subst_env_id in Hf. exact Hf. }
  assert (Hhigh : (security_of T_secret).(indirect_reader) = High).
  { destruct (security_of T_secret).(indirect_reader);
      destruct (security_of T_result).(indirect_reader); simpl in Hnf; tauto. }
  assert (Hlow : (security_of T_result).(indirect_reader) = Low).
  { destruct (security_of T_secret).(indirect_reader);
      destruct (security_of T_result).(indirect_reader); simpl in Hnf; tauto. }
  assert (HIRsec : IR T_secret t1 t2).
  { apply (IR_cross_high T_secret t1 t2 Hhigh Hself1 Hself2). }
  assert (Henv : env_rel (update empty (fresh (L ++ fv_context C)) T_secret)
                        (upd (fresh (L ++ fv_context C)) t1)
                        (upd (fresh (L ++ fv_context C)) t2)).
  { apply env_rel_intro.
    - intros y. unfold upd.
      destruct (Nat.eqb y (fresh (L ++ fv_context C))).
      + apply (has_type_lc empty t1 T_secret Ht1).
      + exact I.
    - intros y. unfold upd.
      destruct (Nat.eqb y (fresh (L ++ fv_context C))).
      + apply (has_type_lc empty t2 T_secret Ht2).
      + exact I.
    - intros y T Hlook.
      unfold update in Hlook. simpl in Hlook.
      destruct (Nat.eqb y (fresh (L ++ fv_context C))) eqn:E.
      + apply Nat.eqb_eq in E. subst y.
        injection Hlook as HT. subst T.
        unfold upd. rewrite Nat.eqb_refl. exact HIRsec.
      + simpl in Hlook. discriminate. }
  pose proof (fundamental (update empty (fresh (L ++ fv_context C)) T_secret)
                (plug C (tm_fvar (fresh (L ++ fv_context C)))) T_result Htyped
                (upd (fresh (L ++ fv_context C)) t1)
                (upd (fresh (L ++ fv_context C)) t2) Henv) as Hfund.
  assert (Hp1 : subst_env (upd (fresh (L ++ fv_context C)) t1)
                  (plug C (tm_fvar (fresh (L ++ fv_context C)))) = plug C t1).
  { apply subst_env_plug. exact HxC. }
  assert (Hp2 : subst_env (upd (fresh (L ++ fv_context C)) t2)
                  (plug C (tm_fvar (fresh (L ++ fv_context C)))) = plug C t2).
  { apply subst_env_plug. exact HxC. }
  rewrite Hp1, Hp2 in Hfund.
  unfold IR in Hfund.
  assert (HVR : VR T_result (security_of T_result) v1 v2).
  { apply Hfund.
    - split; assumption.
    - split; assumption. }
  assert (Hall : all_low T_result).
  { apply (transparent_all_low T_result (security_of T_result)).
    - unfold transparent in Htr. exact Htr.
    - exact Hlow. }
  exact (VR_erase T_result v1 v2 Hg Hall HVR).
Qed.
