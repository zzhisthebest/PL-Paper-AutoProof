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


(* ================================================================== *)
(* Part 1: Basic lemmas about labels, flows, join, security           *)
(* ================================================================== *)

Lemma flows_to_refl : forall l, flows_to l l.
Proof. intros l; destruct l; simpl; trivial. Qed.

Lemma flows_to_trans : forall l1 l2 l3,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof.
  intros l1 l2 l3 H1 H2. destruct l1, l2, l3; simpl in *; auto;
    try contradiction.
Qed.

Lemma flows_to_false : forall l1 l2, ~ flows_to l1 l2 -> l1 = High /\ l2 = Low.
Proof.
  intros l1 l2 H. destruct l1, l2; simpl in *;
    try (exfalso; apply H; exact I); auto.
Qed.

Lemma flows_to_true : forall l1 l2, l1 = High -> l2 = Low -> ~ flows_to l1 l2.
Proof. intros l1 l2 E1 E2; subst; simpl; tauto. Qed.

Lemma join_comm : forall l1 l2, join l1 l2 = join l2 l1.
Proof. intros l1 l2; destruct l1, l2; reflexivity. Qed.

Lemma join_low : forall l1 l2, join l1 l2 = Low <-> l1 = Low /\ l2 = Low.
Proof. intros l1 l2; destruct l1, l2; simpl; tauto. Qed.

Lemma join_high_l : forall l, join High l = High.
Proof. intros l; destruct l; reflexivity. Qed.

Lemma join_high_r : forall l, join l High = High.
Proof. intros l; destruct l; reflexivity. Qed.

Lemma flows_to_join_l : forall l1 l2, flows_to l1 (join l1 l2).
Proof. intros l1 l2; destruct l1, l2; simpl; trivial. Qed.

Lemma flows_to_join_r : forall l1 l2, flows_to l2 (join l1 l2).
Proof. intros l1 l2; destruct l1, l2; simpl; trivial. Qed.

Lemma flows_to_join_inv_l : forall l1 l2 l,
  flows_to (join l1 l2) l -> flows_to l1 l.
Proof. intros l1 l2 l H; eapply flows_to_trans; [apply flows_to_join_l | exact H]. Qed.

Lemma flows_to_join_inv_r : forall l1 l2 l,
  flows_to (join l1 l2) l -> flows_to l2 l.
Proof. intros l1 l2 l H; eapply flows_to_trans; [apply flows_to_join_r | exact H]. Qed.

Lemma security_of_ty_protect : forall l T,
  security_of (ty_protect l T) = protect_security (security_of T) l.
Proof. intros l T; destruct T; reflexivity. Qed.

Lemma indirect_ty_protect : forall l T,
  (security_of (ty_protect l T)).(indirect_reader)
    = join (security_of T).(indirect_reader) l.
Proof.
  intros l T; rewrite security_of_ty_protect. destruct T; reflexivity.
Qed.

(* ================================================================== *)
(* Part 2: Protection of values and erasure                           *)
(* ================================================================== *)

Lemma erase_protect_value : forall v l,
  erase_security (protect_value v l) = erase_security v.
Proof. intros v l; destruct v; reflexivity. Qed.

Lemma value_protect_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv. destruct Hv; simpl; constructor; assumption.
Qed.

(* ================================================================== *)
(* Part 3: Values do not step, and multi from values                  *)
(* ================================================================== *)

Lemma value_app : forall f a r, ~ value (tm_app f a r).
Proof. intros f a r H; inversion H. Qed.

Lemma value_fst : forall t r, ~ value (tm_fst t r).
Proof. intros t r H; inversion H. Qed.

Lemma value_snd : forall t r, ~ value (tm_snd t r).
Proof. intros t r H; inversion H. Qed.

Lemma value_case : forall t b1 b2 r, ~ value (tm_case t b1 b2 r).
Proof. intros t b1 b2 r H; inversion H. Qed.

Lemma value_if : forall c y n r, ~ value (tm_if c y n r).
Proof. intros c y n r H; inversion H. Qed.

Lemma value_protect_tm : forall l t, ~ value (tm_protect l t).
Proof. intros l t H; inversion H. Qed.

Lemma value_bvar : forall i, ~ value (tm_bvar i).
Proof. intros i H; inversion H. Qed.

Lemma value_fvar : forall x, ~ value (tm_fvar x).
Proof. intros x H; inversion H. Qed.

Lemma value_stuck : forall v, value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv. induction Hv; intros t Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst;
      match goal with H : ?a --> ?b |- False =>
        first [ exact (IHHv1 _ H) | exact (IHHv2 _ H) ] end.
  - inversion Hstep; subst;
      match goal with H : ?a --> ?b |- False => exact (IHHv _ H) end.
  - inversion Hstep; subst;
      match goal with H : ?a --> ?b |- False => exact (IHHv _ H) end.
Qed.

Lemma multi_value_eq : forall v t, value v -> multi v t -> t = v.
Proof.
  intros v t Hval Hm. induction Hm.
  - reflexivity.
  - exfalso; eapply value_stuck; eauto.
Qed.

Lemma multi_value_value : forall v t, value v -> multi v t -> value t.
Proof. intros v t Hv Hm; apply multi_value_eq in Hm; subst; assumption. Qed.

(* ================================================================== *)
(* Part 4: Locally closed terms and values                            *)
(* ================================================================== *)

Lemma lc_at_weaken : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H. revert k H. induction t; simpl; intros k H.
  - lia.
  - exact I.
  - exact I.
  - apply IHt; exact H.
  - destruct H as [H1 H2]; split; [apply IHt1; exact H1 | apply IHt2; exact H2].
  - destruct H as [H1 H2]; split; [apply IHt1; exact H1 | apply IHt2; exact H2].
  - apply IHt; exact H.
  - apply IHt; exact H.
  - apply IHt; exact H.
  - apply IHt; exact H.
  - destruct H as [H1 [H2 H3]]; split; [apply IHt1; exact H1 | split; [apply IHt2; exact H2 | apply IHt3; exact H3]].
  - apply IHt; exact H.
  - destruct H as [H1 [H2 H3]]; split; [apply IHt1; exact H1 | split; [apply IHt2; exact H2 | apply IHt3; exact H3]].
Qed.

Lemma lc_at_open_rec_S : forall t k u,
  lc_at k (open_rec k u t) -> lc_at k u -> lc_at (S k) t.
Proof.
  intros t. induction t; intros k u H Hu; simpl in *.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E; simpl in *.
    + apply Nat.eqb_eq in E; subst; lia.
    + apply Nat.eqb_neq in E; lia.
  - (* fvar *) exact I.
  - (* unit *) exact I.
  - (* abs *) apply IHt with (k := S k) (u := u); [exact H | apply lc_at_weaken; exact Hu].
  - (* app *) destruct H as [H1 H2]; split;
      [apply IHt1 with (k:=k) (u:=u) | apply IHt2 with (k:=k) (u:=u)]; auto.
  - (* pair *) destruct H as [H1 H2]; split;
      [apply IHt1 with (k:=k) (u:=u) | apply IHt2 with (k:=k) (u:=u)]; auto.
  - (* fst *) apply IHt with (k:=k) (u:=u); auto.
  - (* snd *) apply IHt with (k:=k) (u:=u); auto.
  - (* inl *) apply IHt with (k:=k) (u:=u); auto.
  - (* inr *) apply IHt with (k:=k) (u:=u); auto.
  - (* case *) destruct H as [H1 [H2 H3]]; split;
      [apply IHt1 with (k:=k) (u:=u); auto | split].
    + apply IHt2 with (k:=S k) (u:=u); [exact H2 | apply lc_at_weaken; exact Hu].
    + apply IHt3 with (k:=S k) (u:=u); [exact H3 | apply lc_at_weaken; exact Hu].
  - (* protect *) apply IHt with (k:=k) (u:=u); auto.
  - (* if *) destruct H as [H1 [H2 H3]]; split;
      [apply IHt1 with (k:=k) (u:=u); auto | split];
      [apply IHt2 with (k:=k) (u:=u); auto | apply IHt3 with (k:=k) (u:=u); auto].
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv; simpl.
  - exact I.
  - assumption.
  - split; assumption.
  - assumption.
  - assumption.
Qed.

Lemma le_succ_succ : forall m k : nat, m <= k -> S m <= S k.
Proof. intros; lia. Qed.

Lemma lc_open_rec : forall t m k u, lc_at m t -> m <= k -> open_rec k u t = t.
Proof.
  intros t. induction t; intros m k u H Hle; simpl in *.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E; simpl.
    + apply Nat.eqb_eq in E; subst; exfalso; lia.
    + reflexivity.
  - (* fvar *) reflexivity.
  - (* unit *) reflexivity.
  - (* abs *) rewrite (IHt (S m) (S k) u H (le_succ_succ m k Hle)). reflexivity.
  - (* app *) destruct H as [H1 H2].
    rewrite (IHt1 m k u H1 Hle). rewrite (IHt2 m k u H2 Hle). reflexivity.
  - (* pair *) destruct H as [H1 H2].
    rewrite (IHt1 m k u H1 Hle). rewrite (IHt2 m k u H2 Hle). reflexivity.
  - (* fst *) rewrite (IHt m k u H Hle). reflexivity.
  - (* snd *) rewrite (IHt m k u H Hle). reflexivity.
  - (* inl *) rewrite (IHt m k u H Hle). reflexivity.
  - (* inr *) rewrite (IHt m k u H Hle). reflexivity.
  - (* case *) destruct H as [H1 [H2 H3]].
    rewrite (IHt1 m k u H1 Hle).
    rewrite (IHt2 (S m) (S k) u H2 (le_succ_succ m k Hle)).
    rewrite (IHt3 (S m) (S k) u H3 (le_succ_succ m k Hle)).
    reflexivity.
  - (* protect *) rewrite (IHt m k u H Hle). reflexivity.
  - (* if *) destruct H as [H1 [H2 H3]].
    rewrite (IHt1 m k u H1 Hle).
    rewrite (IHt2 m k u H2 Hle).
    rewrite (IHt3 m k u H3 Hle).
    reflexivity.
Qed.

Lemma locally_closed_open_rec : forall t k u,
  locally_closed t -> open_rec k u t = t.
Proof. intros t k u H; apply lc_open_rec with (m := 0); auto; lia. Qed.

(* ================================================================== *)
(* Part 5: Simultaneous atom substitution                             *)
(* ================================================================== *)

Fixpoint subst_atoms (s : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => s x
  | tm_unit kappa => tm_unit kappa
  | tm_abs T body kappa => tm_abs T (subst_atoms s body) kappa
  | tm_app t1 t2 r => tm_app (subst_atoms s t1) (subst_atoms s t2) r
  | tm_pair t1 t2 kappa => tm_pair (subst_atoms s t1) (subst_atoms s t2) kappa
  | tm_fst t1 r => tm_fst (subst_atoms s t1) r
  | tm_snd t1 r => tm_snd (subst_atoms s t1) r
  | tm_inl t1 kappa => tm_inl (subst_atoms s t1) kappa
  | tm_inr t1 kappa => tm_inr (subst_atoms s t1) kappa
  | tm_case t0 body1 body2 r =>
      tm_case (subst_atoms s t0) (subst_atoms s body1) (subst_atoms s body2) r
  | tm_protect l t1 => tm_protect l (subst_atoms s t1)
  | tm_if c yes no r => tm_if (subst_atoms s c) (subst_atoms s yes) (subst_atoms s no) r
  end.

Definition extend (x : atom) (u : tm) (s : atom -> tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else s y.

Lemma extend_eq : forall x u s, extend x u s x = u.
Proof. intros; unfold extend; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma extend_neq : forall x y u s, x <> y -> extend x u s y = s y.
Proof.
  intros x y u s H. unfold extend. apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma subst_atoms_id : forall t, subst_atoms tm_fvar t = t.
Proof.
  induction t; simpl; try reflexivity; f_equal; auto.
Qed.

Lemma subst_atoms_agree : forall t s1 s2,
  (forall x, In x (fv t) -> s1 x = s2 x) ->
  subst_atoms s1 t = subst_atoms s2 t.
Proof.
  induction t; simpl; intros s1 s2 Hagree.
  - (* bvar *) reflexivity.
  - (* fvar *) apply Hagree; simpl; auto.
  - (* unit *) reflexivity.
  - (* abs *) f_equal. apply IHt. intros x Hx. apply Hagree. simpl. exact Hx.
  - (* app *) rewrite (IHt1 s1 s2). rewrite (IHt2 s1 s2). reflexivity.
    + intros x Hx. apply Hagree. simpl. repeat rewrite in_app_iff. auto.
    + intros x Hx. apply Hagree. simpl. repeat rewrite in_app_iff. auto.
  - (* pair *) rewrite (IHt1 s1 s2). rewrite (IHt2 s1 s2). reflexivity.
    + intros x Hx. apply Hagree. simpl. repeat rewrite in_app_iff. auto.
    + intros x Hx. apply Hagree. simpl. repeat rewrite in_app_iff. auto.
  - (* fst *) f_equal. apply IHt. intros x Hx. apply Hagree. simpl. exact Hx.
  - (* snd *) f_equal. apply IHt. intros x Hx. apply Hagree. simpl. exact Hx.
  - (* inl *) f_equal. apply IHt. intros x Hx. apply Hagree. simpl. exact Hx.
  - (* inr *) f_equal. apply IHt. intros x Hx. apply Hagree. simpl. exact Hx.
  - (* case *) rewrite (IHt1 s1 s2). rewrite (IHt2 s1 s2). rewrite (IHt3 s1 s2).
    reflexivity.
    + intros x Hx. apply Hagree. simpl. repeat rewrite in_app_iff. auto.
    + intros x Hx. apply Hagree. simpl. repeat rewrite in_app_iff. auto.
    + intros x Hx. apply Hagree. simpl. repeat rewrite in_app_iff. auto.
  - (* protect *) f_equal. apply IHt. intros x Hx. apply Hagree. simpl. exact Hx.
  - (* if *) rewrite (IHt1 s1 s2). rewrite (IHt2 s1 s2). rewrite (IHt3 s1 s2).
    reflexivity.
    + intros x Hx. apply Hagree. simpl. repeat rewrite in_app_iff. auto.
    + intros x Hx. apply Hagree. simpl. repeat rewrite in_app_iff. auto.
    + intros x Hx. apply Hagree. simpl. repeat rewrite in_app_iff. auto.
Qed.

Lemma subst_atoms_extend_fresh : forall t x u s,
  ~ In x (fv t) -> subst_atoms (extend x u s) t = subst_atoms s t.
Proof.
  intros t x u s Hx. apply subst_atoms_agree. intros y Hy.
  unfold extend. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst; exfalso; auto.
  - reflexivity.
Qed.

Lemma subst_atoms_open_rec_lc : forall t s0 k u,
  (forall y, locally_closed (s0 y)) ->
  subst_atoms s0 (open_rec k u t)
    = open_rec k (subst_atoms s0 u) (subst_atoms s0 t).
Proof.
  intros t. induction t; intros s0 k u Hlc; simpl in *.
  - (* bvar *) destruct (Nat.eqb k n); reflexivity.
  - (* fvar *) rewrite locally_closed_open_rec; auto.
  - (* unit *) reflexivity.
  - (* abs *) f_equal. apply IHt with (k := S k). exact Hlc.
  - (* app *) rewrite (IHt1 s0 k u Hlc). rewrite (IHt2 s0 k u Hlc). reflexivity.
  - (* pair *) rewrite (IHt1 s0 k u Hlc). rewrite (IHt2 s0 k u Hlc). reflexivity.
  - (* fst *) f_equal. apply IHt with (k := k). exact Hlc.
  - (* snd *) f_equal. apply IHt with (k := k). exact Hlc.
  - (* inl *) f_equal. apply IHt with (k := k). exact Hlc.
  - (* inr *) f_equal. apply IHt with (k := k). exact Hlc.
  - (* case *) rewrite (IHt1 s0 k u Hlc).
    rewrite (IHt2 s0 (S k) u Hlc). rewrite (IHt3 s0 (S k) u Hlc). reflexivity.
  - (* protect *) f_equal. apply IHt with (k := k). exact Hlc.
  - (* if *) rewrite (IHt1 s0 k u Hlc). rewrite (IHt2 s0 k u Hlc).
    rewrite (IHt3 s0 k u Hlc). reflexivity.
Qed.

(* A fresh atom outside a finite list *)
Definition fresh_atom (l : list atom) : atom := fold_right Nat.max 0 l + 1.

Lemma in_le_fold_max : forall (l : list atom) (x : atom),
  In x l -> x <= fold_right Nat.max 0 l.
Proof.
  induction l as [| a l IH]; intros x Hx.
  - inversion Hx.
  - simpl in Hx. destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hx | apply Nat.le_max_r].
Qed.

Lemma fresh_atom_spec : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l Hx. unfold fresh_atom in Hx.
  pose proof (in_le_fold_max l (fold_right Nat.max 0 l + 1) Hx). lia.
Qed.

(* ================================================================== *)
(* Part 4b: Well-typed terms are locally closed                       *)
(* ================================================================== *)

Lemma lc_body_of_open : forall body L,
  (forall x : atom, ~ In x L -> lc_at 0 (open body (tm_fvar x))) ->
  lc_at 1 body.
Proof.
  intros body L H.
  pose proof (H (fresh_atom L) (fresh_atom_spec L)) as Hx.
  apply lc_at_open_rec_S with (k := 0) (u := tm_fvar (fresh_atom L)).
  - exact Hx.
  - exact I.
Qed.

Lemma has_type_locally_closed : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H; simpl.
  - (* T_Var *) exact I.
  - (* T_Unit *) exact I.
  - (* T_Abs *) unfold locally_closed in *; simpl.
    match goal with
    | Hgen : forall x : atom, ~ In x ?L -> lc_at 0 (open ?body (tm_fvar x))
             |- lc_at 1 ?body => exact (lc_body_of_open body L Hgen)
    end.
  - (* T_App *) split; assumption.
  - (* T_Pair *) split; assumption.
  - (* T_Fst *) assumption.
  - (* T_Snd *) assumption.
  - (* T_Inl *) assumption.
  - (* T_Inr *) assumption.
  - (* T_Case *) unfold locally_closed in *; simpl; split; [ assumption | split ].
    + match goal with
      | Hgen : forall x : atom, ~ In x ?L -> lc_at 0 (open ?body (tm_fvar x))
               |- lc_at 1 ?body => exact (lc_body_of_open body L Hgen)
      end.
    + match goal with
      | Hgen : forall x : atom, ~ In x ?L -> lc_at 0 (open ?body (tm_fvar x))
               |- lc_at 1 ?body => exact (lc_body_of_open body L Hgen)
      end.
  - (* T_Protect *) assumption.
  - (* T_Sub *) assumption.
  - (* T_If *) split; [ assumption | split; assumption ].
Qed.


(* ================================================================== *)
(* Part 6: The logical relation                                       *)
(* ================================================================== *)

Fixpoint VR (l : label) (T : ty) (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_Unit kappa =>
      flows_to kappa.(indirect_reader) l ->
      erase_security v1 = erase_security v2
  | Ty_Sum T1 T2 kappa =>
      flows_to kappa.(indirect_reader) l ->
      match v1, v2 with
      | tm_inl w1 _, tm_inl w2 _ => VR l T1 w1 w2
      | tm_inr w1 _, tm_inr w2 _ => VR l T2 w1 w2
      | _, _ => False
      end
  | Ty_Prod T1 T2 kappa =>
      flows_to kappa.(indirect_reader) l ->
      match v1, v2 with
      | tm_pair a1 b1 _, tm_pair a2 b2 _ => VR l T1 a1 a2 /\ VR l T2 b1 b2
      | _, _ => False
      end
  | Ty_Arrow T1 T2 kappa =>
      flows_to kappa.(indirect_reader) l ->
      match v1, v2 with
      | tm_abs _ b1 _, tm_abs _ b2 _ =>
          forall (u1 u2 : tm), value u1 -> value u2 -> VR l T1 u1 u2 ->
            forall (w1 w2 : tm), evaluates (open b1 u1) w1 -> evaluates (open b2 u2) w2 ->
              VR l T2 w1 w2
      | _, _ => False
      end
  end.

Definition TR (l : label) (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm, evaluates t1 v1 -> evaluates t2 v2 -> VR l T v1 v2.

Lemma VR_vacuous : forall l T,
  ~ flows_to (security_of T).(indirect_reader) l ->
  forall v1 v2, VR l T v1 v2.
Proof.
  intros l T H v1 v2.
  destruct T; simpl in *; intro Hf; exfalso; apply H; exact Hf.
Qed.

Lemma VR_to_TR_value : forall l T v1 v2,
  value v1 -> value v2 -> VR l T v1 v2 -> TR l T v1 v2.
Proof.
  intros l T v1 v2 Hv1 Hv2 Hvr. unfold TR.
  intros w1 w2 [Hm1 Hval1] [Hm2 Hval2].
  rewrite (multi_value_eq v1 w1 Hv1 Hm1).
  rewrite (multi_value_eq v2 w2 Hv2 Hm2).
  exact Hvr.
Qed.

Lemma TR_value : forall l T v1 v2,
  value v1 -> value v2 -> VR l T v1 v2 -> TR l T v1 v2.
Proof. intros; eapply VR_to_TR_value; eauto. Qed.

(* Weakening the guard: protecting the type annotation *)
Lemma VR_protect_ty : forall l T j v1 v2,
  VR l T v1 v2 -> VR l (ty_protect j T) v1 v2.
Proof.
  intros l T. induction T; intros j v1 v2 H; simpl in *.
  - (* Unit *) intro Hf. apply H. apply flows_to_join_inv_l in Hf. exact Hf.
  - (* Sum *) intro Hf. apply H. apply flows_to_join_inv_l in Hf. exact Hf.
  - (* Prod *) intro Hf. apply H. apply flows_to_join_inv_l in Hf. exact Hf.
  - (* Arrow *) intro Hf. apply H. apply flows_to_join_inv_l in Hf. exact Hf.
Qed.

(* protect_value does not change relatedness at the same type *)
Lemma VR_protect_value_same : forall l T v1 v2 j1 j2,
  VR l T v1 v2 -> VR l T (protect_value v1 j1) (protect_value v2 j2).
Proof.
  intros l T. destruct T as [k | T1 T2 k | T1 T2 k | T1 T2 k];
    intros v1 v2 j1 j2 H.
  - (* Unit *) simpl. intro Hf. rewrite !erase_protect_value. apply H; exact Hf.
  - (* Sum *) simpl. intro Hf. pose proof (H Hf) as Hm.
    destruct v1; destruct v2; simpl in *; try contradiction; assumption.
  - (* Prod *) simpl. intro Hf. pose proof (H Hf) as Hm.
    destruct v1; destruct v2; simpl in *; try contradiction;
      try (destruct Hm as [Hm1 Hm2]; split; assumption).
  - (* Arrow *) simpl. intro Hf. pose proof (H Hf) as Hm.
    destruct v1; destruct v2; simpl in *; try contradiction; exact Hm.
Qed.

Lemma VR_protect_value : forall l T v1 v2 j j1 j2,
  VR l T v1 v2 ->
  VR l (ty_protect j T) (protect_value v1 j1) (protect_value v2 j2).
Proof.
  intros. apply VR_protect_value_same. apply VR_protect_ty. assumption.
Qed.

(* Monotonicity of the relation under subtyping *)
Lemma VR_sub : forall l T U, subtype T U ->
  forall v1 v2, VR l T v1 v2 -> VR l U v1 v2.
Proof.
  intros l T U Hsub.
  induction Hsub as
    [ k1 k2 Hw1 Hw2 Hle
    | T1 T2 U1 U2 k1 k2 Hs1 IH1 Hs2 IH2 Hw1 Hw2 Hle
    | T1 T2 U1 U2 k1 k2 Hs1 IH1 Hs2 IH2 Hw1 Hw2 Hle
    | T1 T2 U1 U2 k1 k2 Hs1 IH1 Hs2 IH2 Hw1 Hw2 Hle
    | T U V Hs1 IH1 Hs2 IH2 ]; intros v1 v2 Hv.
  - (* S_Unit *) simpl in *. intro Hf. apply Hv.
    eapply flows_to_trans; [exact (proj2 Hle) | exact Hf].
  - (* S_Sum *) simpl in *. intro Hf.
    assert (Hf' : flows_to k1.(indirect_reader) l).
    { eapply flows_to_trans; [exact (proj2 Hle) | exact Hf]. }
    pose proof (Hv Hf') as Hm.
    destruct v1; destruct v2; simpl in *; try contradiction; auto.
  - (* S_Prod *) simpl in *. intro Hf.
    assert (Hf' : flows_to k1.(indirect_reader) l).
    { eapply flows_to_trans; [exact (proj2 Hle) | exact Hf]. }
    pose proof (Hv Hf') as Hm.
    destruct v1; destruct v2; simpl in *; try contradiction;
      try (destruct Hm as [Hm1 Hm2]; split; auto).
  - (* S_Arrow *) simpl in *. intro Hf.
    assert (Hf' : flows_to k1.(indirect_reader) l).
    { eapply flows_to_trans; [exact (proj2 Hle) | exact Hf]. }
    pose proof (Hv Hf') as Hm.
    destruct v1; destruct v2; simpl in *; try contradiction.
    intros u1 u2 Hvu1 Hvu2 Hu w1 w2 E1 E2.
    apply IH2. apply Hm with (u1 := u1) (u2 := u2);
      [exact Hvu1 | exact Hvu2 | apply IH1; exact Hu | exact E1 | exact E2].
  - (* S_Trans *) apply IH2. apply IH1. exact Hv.
Qed.

Lemma TR_sub : forall l T U, subtype T U ->
  forall t1 t2, TR l T t1 t2 -> TR l U t1 t2.
Proof.
  intros l T U Hs t1 t2 H. unfold TR in *.
  intros v1 v2 E1 E2. eapply VR_sub; [exact Hs | apply H; assumption].
Qed.


(* ================================================================== *)
(* Part 7: Inversion lemmas for single steps                          *)
(* ================================================================== *)

Lemma step_app_inv : forall f a r t,
  tm_app f a r --> t ->
  (exists T body k v, f = tm_abs T body k /\ a = v /\
     value (tm_abs T body k) /\ value v /\ flows_to k.(reader) r /\
     t = tm_protect k.(indirect_reader) (open body v))
  \/ (exists f', f --> f' /\ t = tm_app f' a r)
  \/ (exists a', value f /\ a --> a' /\ t = tm_app f a' r).
Proof. intros f a r t H; inversion H; subst; eauto 12. Qed.

Lemma step_protect_inv : forall j t u,
  tm_protect j t --> u ->
  (value t /\ u = protect_value t j) \/ (exists t', t --> t' /\ u = tm_protect j t').
Proof. intros j t u H; inversion H; subst; eauto 10. Qed.

Lemma step_pair_inv : forall a b k u,
  tm_pair a b k --> u ->
  (exists a', a --> a' /\ u = tm_pair a' b k)
  \/ (exists b', value a /\ b --> b' /\ u = tm_pair a b' k).
Proof. intros a b k u H; inversion H; subst; eauto 10. Qed.

Lemma step_inl_inv : forall t k u,
  tm_inl t k --> u -> exists t', t --> t' /\ u = tm_inl t' k.
Proof. intros t k u H; inversion H; subst; eauto. Qed.

Lemma step_inr_inv : forall t k u,
  tm_inr t k --> u -> exists t', t --> t' /\ u = tm_inr t' k.
Proof. intros t k u H; inversion H; subst; eauto. Qed.

Lemma step_fst_inv : forall t r u,
  tm_fst t r --> u ->
  (exists v1 v2 k, t = tm_pair v1 v2 k /\ value v1 /\ value v2 /\
     flows_to k.(reader) r /\ u = tm_protect k.(indirect_reader) v1)
  \/ (exists t', t --> t' /\ u = tm_fst t' r).
Proof. intros t r u H; inversion H; subst; eauto 12. Qed.

Lemma step_snd_inv : forall t r u,
  tm_snd t r --> u ->
  (exists v1 v2 k, t = tm_pair v1 v2 k /\ value v1 /\ value v2 /\
     flows_to k.(reader) r /\ u = tm_protect k.(indirect_reader) v2)
  \/ (exists t', t --> t' /\ u = tm_snd t' r).
Proof. intros t r u H; inversion H; subst; eauto 12. Qed.

Lemma step_case_inv : forall t b1 b2 r u,
  tm_case t b1 b2 r --> u ->
  (exists v k, t = tm_inl v k /\ value v /\ flows_to k.(reader) r /\
     u = tm_protect k.(indirect_reader) (open b1 v))
  \/ (exists v k, t = tm_inr v k /\ value v /\ flows_to k.(reader) r /\
     u = tm_protect k.(indirect_reader) (open b2 v))
  \/ (exists t', t --> t' /\ u = tm_case t' b1 b2 r).
Proof. intros t b1 b2 r u H; inversion H; subst; eauto 12. Qed.

Lemma step_if_inv : forall c y n r u,
  tm_if c y n r --> u ->
  (exists v k, c = tm_inl v k /\ value v /\ flows_to k.(reader) r /\
     u = tm_protect k.(indirect_reader) y)
  \/ (exists v k, c = tm_inr v k /\ value v /\ flows_to k.(reader) r /\
     u = tm_protect k.(indirect_reader) n)
  \/ (exists c', c --> c' /\ u = tm_if c' y n r).
Proof. intros c y n r u H; inversion H; subst; eauto 12. Qed.

(* ================================================================== *)
(* Part 8: Decomposition of evaluations                               *)
(* ================================================================== *)

Lemma multi_protect_inv : forall s v,
  multi s v -> value v ->
  forall j t, s = tm_protect j t ->
    exists w, multi t w /\ value w /\ v = protect_value w j.
Proof.
  intros s v Hm. induction Hm; intros Hval j0 t0 Es.
  - rewrite Es in Hval. exfalso. exact (value_protect_tm j0 t0 Hval).
  - rewrite Es in H.
    destruct (step_protect_inv j0 t0 t2 H) as [[Hval0 Heq] | [t' [Hstep' Heq]]].
    + subst t2. exists t0. split; [apply multi_refl | split; [exact Hval0 |]].
      apply (multi_value_eq (protect_value t0 j0) t3);
        [apply value_protect_value; exact Hval0 | exact Hm].
    + subst t2. destruct (IHHm Hval j0 t' eq_refl) as [w [Hm' [Hvw Heq']]].
      exists w. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_app_inv : forall s v,
  multi s v -> value v ->
  forall f a r, s = tm_app f a r ->
  exists (fv av : tm) (Ta : ty) (body : tm) (k : security),
    multi f fv /\ value fv /\ fv = tm_abs Ta body k /\
    multi a av /\ value av /\ flows_to k.(reader) r /\
    multi (tm_protect k.(indirect_reader) (open body av)) v.
Proof.
  intros s v Hm. induction Hm; intros Hval f0 a0 r0 Es.
  - rewrite Es in Hval. exfalso. exact (value_app f0 a0 r0 Hval).
  - rewrite Es in H.
    destruct (step_app_inv f0 a0 r0 t2 H) as
      [ [T [body [k [v0 [Ef [Ea [Hvabs [Hv0 [Hflow Heq]]]]]]]]]
      | [ [f' [Hf' Heq]] | [a' [Hvf [Ha' Heq]]] ] ].
    + subst t2. subst f0. subst a0.
      exists (tm_abs T body k), v0, T, body, k.
      repeat split; auto using multi_refl.
    + subst t2.
      destruct (IHHm Hval f' a0 r0 eq_refl) as
        (fv & av & Ta & body & k & H1 & H2 & H3 & H4 & H5 & H6 & H7).
      exists fv, av, Ta, body, k. repeat split; auto.
      eapply multi_step; [exact Hf' | exact H1].
    + subst t2.
      destruct (IHHm Hval f0 a' r0 eq_refl) as
        (fv & av & Ta & body & k & H1 & H2 & H3 & H4 & H5 & H6 & H7).
      exists fv, av, Ta, body, k. repeat split; auto.
      eapply multi_step; [exact Ha' | exact H4].
Qed.

Lemma multi_pair_inv : forall s v,
  multi s v -> value v ->
  forall a b k, s = tm_pair a b k ->
    exists a' b', multi a a' /\ value a' /\ multi b b' /\ value b' /\
      v = tm_pair a' b' k.
Proof.
  intros s v Hm. induction Hm; intros Hval a0 b0 k0 Es.
  - rewrite Es in Hval. inversion Hval; subst.
    exists a0, b0. repeat split; auto using multi_refl.
  - rewrite Es in H.
    destruct (step_pair_inv a0 b0 k0 t2 H) as [[a' [Ha' Heq]] | [b' [Hva [Hb' Heq]]]].
    + subst t2. destruct (IHHm Hval a' b0 k0 eq_refl) as
        (a'' & b'' & H1 & H2 & H3 & H4 & H5).
      exists a'', b''. repeat split; auto. eapply multi_step; eauto.
    + subst t2. destruct (IHHm Hval a0 b' k0 eq_refl) as
        (a'' & b'' & H1 & H2 & H3 & H4 & H5).
      exists a'', b''. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_inl_inv : forall s v,
  multi s v -> value v -> forall t k, s = tm_inl t k ->
    exists w, multi t w /\ value w /\ v = tm_inl w k.
Proof.
  intros s v Hm. induction Hm; intros Hval t0 k0 Es.
  - rewrite Es in Hval. inversion Hval; subst. exists t0. repeat split; auto using multi_refl.
  - rewrite Es in H.
    destruct (step_inl_inv t0 k0 t2 H) as [t' [Hstep' Heq]]. subst t2.
    destruct (IHHm Hval t' k0 eq_refl) as [w [H1 [H2 H3]]].
    exists w. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_inr_inv : forall s v,
  multi s v -> value v -> forall t k, s = tm_inr t k ->
    exists w, multi t w /\ value w /\ v = tm_inr w k.
Proof.
  intros s v Hm. induction Hm; intros Hval t0 k0 Es.
  - rewrite Es in Hval. inversion Hval; subst. exists t0. repeat split; auto using multi_refl.
  - rewrite Es in H.
    destruct (step_inr_inv t0 k0 t2 H) as [t' [Hstep' Heq]]. subst t2.
    destruct (IHHm Hval t' k0 eq_refl) as [w [H1 [H2 H3]]].
    exists w. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_fst_inv : forall s v,
  multi s v -> value v -> forall t r, s = tm_fst t r ->
  exists w1 w2 k, multi t (tm_pair w1 w2 k) /\ value w1 /\ value w2 /\
    flows_to k.(reader) r /\ multi (tm_protect k.(indirect_reader) w1) v.
Proof.
  intros s v Hm. induction Hm; intros Hval t0 r0 Es.
  - rewrite Es in Hval. exfalso. exact (value_fst t0 r0 Hval).
  - rewrite Es in H.
    destruct (step_fst_inv t0 r0 t2 H) as
      [[v1 [v2 [k [Et [Hv1 [Hv2 [Hflow Heq]]]]]]] | [t' [Hstep' Heq]]].
    + subst t2. subst t0.
      exists v1, v2, k. repeat split; auto using multi_refl.
    + subst t2. destruct (IHHm Hval t' r0 eq_refl) as
        (w1 & w2 & k & H1 & H2 & H3 & H4 & H5).
      exists w1, w2, k. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_snd_inv : forall s v,
  multi s v -> value v -> forall t r, s = tm_snd t r ->
  exists w1 w2 k, multi t (tm_pair w1 w2 k) /\ value w1 /\ value w2 /\
    flows_to k.(reader) r /\ multi (tm_protect k.(indirect_reader) w2) v.
Proof.
  intros s v Hm. induction Hm; intros Hval t0 r0 Es.
  - rewrite Es in Hval. exfalso. exact (value_snd t0 r0 Hval).
  - rewrite Es in H.
    destruct (step_snd_inv t0 r0 t2 H) as
      [[v1 [v2 [k [Et [Hv1 [Hv2 [Hflow Heq]]]]]]] | [t' [Hstep' Heq]]].
    + subst t2. subst t0.
      exists v1, v2, k. repeat split; auto using multi_refl.
    + subst t2. destruct (IHHm Hval t' r0 eq_refl) as
        (w1 & w2 & k & H1 & H2 & H3 & H4 & H5).
      exists w1, w2, k. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_case_inv : forall s v,
  multi s v -> value v -> forall t b1 b2 r, s = tm_case t b1 b2 r ->
  (exists w k, multi t (tm_inl w k) /\ value w /\ flows_to k.(reader) r /\
     multi (tm_protect k.(indirect_reader) (open b1 w)) v)
  \/ (exists w k, multi t (tm_inr w k) /\ value w /\ flows_to k.(reader) r /\
     multi (tm_protect k.(indirect_reader) (open b2 w)) v).
Proof.
  intros s v Hm. induction Hm; intros Hval t0 b10 b20 r0 Es.
  - rewrite Es in Hval. exfalso. exact (value_case t0 b10 b20 r0 Hval).
  - rewrite Es in H.
    destruct (step_case_inv t0 b10 b20 r0 t2 H) as
      [ [v0 [k [Et [Hv0 [Hflow Heq]]]]]
      | [ [v0 [k [Et [Hv0 [Hflow Heq]]]]]
        | [t' [Hstep' Heq]] ] ].
    + subst t2. subst t0. left. exists v0, k. repeat split; auto using multi_refl.
    + subst t2. subst t0. right. exists v0, k. repeat split; auto using multi_refl.
    + subst t2. destruct (IHHm Hval t' b10 b20 r0 eq_refl) as [Hl | Hr].
      * destruct Hl as [w [k [H1 [H2 [H3 H4]]]]].
        left. exists w, k. repeat split; auto. eapply multi_step; eauto.
      * destruct Hr as [w [k [H1 [H2 [H3 H4]]]]].
        right. exists w, k. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_if_inv : forall s v,
  multi s v -> value v -> forall c y n r, s = tm_if c y n r ->
  (exists w k, multi c (tm_inl w k) /\ value w /\ flows_to k.(reader) r /\
     multi (tm_protect k.(indirect_reader) y) v)
  \/ (exists w k, multi c (tm_inr w k) /\ value w /\ flows_to k.(reader) r /\
     multi (tm_protect k.(indirect_reader) n) v).
Proof.
  intros s v Hm. induction Hm; intros Hval c0 y0 n0 r0 Es.
  - rewrite Es in Hval. exfalso. exact (value_if c0 y0 n0 r0 Hval).
  - rewrite Es in H.
    destruct (step_if_inv c0 y0 n0 r0 t2 H) as
      [ [v0 [k [Ec [Hv0 [Hflow Heq]]]]]
      | [ [v0 [k [Ec [Hv0 [Hflow Heq]]]]]
        | [c' [Hstep' Heq]] ] ].
    + subst t2. subst c0. left. exists v0, k. repeat split; auto using multi_refl.
    + subst t2. subst c0. right. exists v0, k. repeat split; auto using multi_refl.
    + subst t2. destruct (IHHm Hval c' y0 n0 r0 eq_refl) as [Hl | Hr].
      * destruct Hl as [w [k [H1 [H2 [H3 H4]]]]].
        left. exists w, k. repeat split; auto. eapply multi_step; eauto.
      * destruct Hr as [w [k [H1 [H2 [H3 H4]]]]].
        right. exists w, k. repeat split; auto. eapply multi_step; eauto.
Qed.

(* ================================================================== *)
(* Part 6b: Auxiliary lemmas for the fundamental theorem              *)
(* ================================================================== *)

Lemma flows_to_dec : forall a b : label, flows_to a b \/ ~ flows_to a b.
Proof. intros a b; destruct a, b; simpl; auto. Qed.

Lemma multi_unit_eq : forall k v, multi (tm_unit k) v -> v = tm_unit k.
Proof.
  intros k v Hm. remember (tm_unit k) as s eqn:Es.
  revert k Es. induction Hm; intros k0 Es.
  - reflexivity.
  - rewrite Es in H. inversion H.
Qed.

Lemma multi_abs_eq : forall T body k v,
  multi (tm_abs T body k) v -> v = tm_abs T body k.
Proof.
  intros T body k v Hm. remember (tm_abs T body k) as s eqn:Es.
  revert T body k Es. induction Hm; intros T0 body0 k0 Es.
  - reflexivity.
  - rewrite Es in H. inversion H.
Qed.

Lemma TR_vacuous : forall l T t1 t2,
  ~ flows_to (security_of T).(indirect_reader) l -> TR l T t1 t2.
Proof.
  intros l T t1 t2 H. unfold TR. intros v1 v2 E1 E2.
  apply VR_vacuous. exact H.
Qed.

Lemma not_flows_protect : forall j T l,
  ~ flows_to j l -> ~ flows_to (security_of (ty_protect j T)).(indirect_reader) l.
Proof.
  intros j T l Hnf.
  apply flows_to_false in Hnf. destruct Hnf as [Hj Hl]. subst.
  rewrite indirect_ty_protect. rewrite join_high_r. simpl. tauto.
Qed.

Lemma TR_protect : forall l T t1 t2 j j1 j2,
  TR l T t1 t2 ->
  TR l (ty_protect j T) (tm_protect j1 t1) (tm_protect j2 t2).
Proof.
  intros l T t1 t2 j j1 j2 H. unfold TR in *.
  intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
  destruct (multi_protect_inv _ _ Hm1 Hv1 j1 t1 eq_refl) as [w1 [Hmw1 [Hvw1 Heq1]]].
  destruct (multi_protect_inv _ _ Hm2 Hv2 j2 t2 eq_refl) as [w2 [Hmw2 [Hvw2 Heq2]]].
  subst v1. subst v2.
  apply VR_protect_value. apply H; split; assumption.
Qed.

(* Environment relations *)
Definition env_lc (s : atom -> tm) : Prop :=
  forall x, locally_closed (s x).

Definition env_rel (l : label) (Gamma : context) (s1 s2 : atom -> tm) : Prop :=
  forall (x : atom) (U : ty), lookup_context x Gamma = Some U -> TR l U (s1 x) (s2 x).

Lemma env_lc_id : env_lc tm_fvar.
Proof. intros x. simpl. exact I. Qed.

Lemma env_lc_extend : forall s x u,
  env_lc s -> locally_closed u -> env_lc (extend x u s).
Proof.
  intros s x u Hlc Hu y. unfold extend.
  destruct (Nat.eqb x y).
  - exact Hu.
  - apply Hlc.
Qed.

Lemma lookup_update_eq : forall x Gamma T,
  lookup_context x (update Gamma x T) = Some T.
Proof.
  intros x Gamma T. unfold update, lookup_context. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_update_neq : forall x y Gamma T,
  x <> y -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros x y Gamma T H. unfold update, lookup_context. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply H. symmetry. exact E.
  - reflexivity.
Qed.

Lemma env_rel_update : forall l Gamma s1 s2 x T u1 u2,
  env_rel l Gamma s1 s2 -> TR l T u1 u2 ->
  env_rel l (update Gamma x T) (extend x u1 s1) (extend x u2 s2).
Proof.
  intros l Gamma s1 s2 x T u1 u2 Henv HT y U Hlk.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    rewrite lookup_update_eq in Hlk. injection Hlk as ->.
    rewrite extend_eq. rewrite extend_eq. exact HT.
  - apply Nat.eqb_neq in E.
    rewrite lookup_update_neq in Hlk by exact E.
    rewrite (extend_neq x y u1 s1) by exact E.
    rewrite (extend_neq x y u2 s2) by exact E.
    apply Henv. exact Hlk.
Qed.

(* fresh atom helpers *)
Lemma fresh_atom_not_in_l : forall l1 l2, ~ In (fresh_atom (l1 ++ l2)) l1.
Proof.
  intros l1 l2 H. apply (fresh_atom_spec (l1 ++ l2)). apply in_app_iff. left. exact H.
Qed.

Lemma fresh_atom_not_in_r : forall l1 l2, ~ In (fresh_atom (l1 ++ l2)) l2.
Proof.
  intros l1 l2 H. apply (fresh_atom_spec (l1 ++ l2)). apply in_app_iff. right. exact H.
Qed.

Lemma subst_open_fvar : forall body x u s,
  ~ In x (fv body) -> env_lc s -> locally_closed u ->
  subst_atoms (extend x u s) (open body (tm_fvar x))
    = open (subst_atoms s body) u.
Proof.
  intros body x u s Hxfv Hlc Hu.
  unfold open.
  rewrite (subst_atoms_open_rec_lc body (extend x u s) 0 (tm_fvar x)).
  - change (open_rec 0 (extend x u s x) (subst_atoms (extend x u s) body)
            = open_rec 0 u (subst_atoms s body)).
    rewrite extend_eq. rewrite (subst_atoms_extend_fresh body x u s Hxfv). reflexivity.
  - apply env_lc_extend; assumption.
Qed.

Lemma VR_sum_inl : forall l T1 T2 kappa w1 w2 j1 j2,
  flows_to kappa.(indirect_reader) l ->
  VR l (Ty_Sum T1 T2 kappa) (tm_inl w1 j1) (tm_inl w2 j2) -> VR l T1 w1 w2.
Proof. intros; simpl in *; auto. Qed.

Lemma VR_sum_inr : forall l T1 T2 kappa w1 w2 j1 j2,
  flows_to kappa.(indirect_reader) l ->
  VR l (Ty_Sum T1 T2 kappa) (tm_inr w1 j1) (tm_inr w2 j2) -> VR l T2 w1 w2.
Proof. intros; simpl in *; auto. Qed.

Lemma VR_sum_lr : forall l T1 T2 kappa w1 w2 j1 j2,
  flows_to kappa.(indirect_reader) l ->
  VR l (Ty_Sum T1 T2 kappa) (tm_inl w1 j1) (tm_inr w2 j2) -> False.
Proof. intros; simpl in *; auto. Qed.

Lemma VR_sum_rl : forall l T1 T2 kappa w1 w2 j1 j2,
  flows_to kappa.(indirect_reader) l ->
  VR l (Ty_Sum T1 T2 kappa) (tm_inr w1 j1) (tm_inl w2 j2) -> False.
Proof. intros; simpl in *; auto. Qed.

Lemma VR_prod : forall l T1 T2 kappa a1 b1 a2 b2 j1 j2,
  flows_to kappa.(indirect_reader) l ->
  VR l (Ty_Prod T1 T2 kappa) (tm_pair a1 b1 j1) (tm_pair a2 b2 j2) ->
  VR l T1 a1 a2 /\ VR l T2 b1 b2.
Proof. intros; simpl in *; auto. Qed.


(* ================================================================== *)
(* Part 9: The fundamental theorem of the logical relation            *)
(* ================================================================== *)

Lemma fundamental : forall Gamma t T, has_type Gamma t T ->
  forall l s1 s2,
    env_lc s1 -> env_lc s2 -> env_rel l Gamma s1 s2 ->
    TR l T (subst_atoms s1 t) (subst_atoms s2 t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [ Gamma x T Hlk Hwf
    | Gamma kappa Hwf
    | L Gamma T1 body T2 kappa HwfT1 Hwfkappa Hbody IHbody
    | Gamma t1 t2 T1 T2 kappa r H1 IH1 H2 IH2 Hflow
    | Gamma t1 t2 T1 T2 kappa H1 IH1 H2 IH2 Hwf
    | Gamma t T1 T2 kappa r H1 IH1 Hflow
    | Gamma t T1 T2 kappa r H1 IH1 Hflow
    | Gamma t T1 T2 kappa H1 IH1 HwfT2 Hwf
    | Gamma t T1 T2 kappa HwfT1 H1 IH1 Hwf
    | L Gamma t body1 body2 T1 T2 T kappa r H1 IH1 Hflow H2 IH2 H3 IH3
    | Gamma t T lp H1 IH1
    | Gamma t T U H1 IH1 Hsub
    | Gamma c yes no k T r H1 IH1 H2 IH2 H3 IH3 Hflow ];
    intros l s1 s2 Hlc1 Hlc2 Henv.
  - (* T_Var *) simpl. eapply Henv. eassumption.
  - (* T_Unit *) simpl. unfold TR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    rewrite (multi_unit_eq kappa v1 Hm1). rewrite (multi_unit_eq kappa v2 Hm2).
    simpl. intro. reflexivity.
  - (* T_Abs *)
    simpl. unfold TR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    simpl in Hm1. simpl in Hm2.
    rewrite (multi_abs_eq T1 (subst_atoms s1 body) kappa v1 Hm1).
    rewrite (multi_abs_eq T1 (subst_atoms s2 body) kappa v2 Hm2).
    simpl. intro Hfl.
    intros u1 u2 Hvu1 Hvu2 Hvr w1 w2 E1 E2.
    set (x := fresh_atom (L ++ fv body)).
    assert (HxL : ~ In x L) by (unfold x; apply fresh_atom_not_in_l).
    assert (Hxfv : ~ In x (fv body)) by (unfold x; apply fresh_atom_not_in_r).
    assert (Henv' : env_rel l (update Gamma x T1) (extend x u1 s1) (extend x u2 s2)).
    { apply env_rel_update.
      - exact Henv.
      - apply VR_to_TR_value; [exact Hvu1 | exact Hvu2 | exact Hvr]. }
    pose proof (IHbody x HxL l _ _
      (env_lc_extend s1 x u1 Hlc1 (value_locally_closed u1 Hvu1))
      (env_lc_extend s2 x u2 Hlc2 (value_locally_closed u2 Hvu2))
      Henv') as Htr.
    rewrite (subst_open_fvar body x u1 s1 Hxfv Hlc1 (value_locally_closed u1 Hvu1)) in Htr.
    rewrite (subst_open_fvar body x u2 s2 Hxfv Hlc2 (value_locally_closed u2 Hvu2)) in Htr.
    apply Htr; assumption.
  - (* T_App *)
    simpl. unfold TR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct (multi_app_inv _ _ Hm1 Hv1 (subst_atoms s1 t1) (subst_atoms s1 t2) r eq_refl) as
      (fv1 & av1 & Ta1 & body1 & k1 & Hmf1 & Hvf1 & Heq1 & Hma1 & Hva1 & Hfl1 & Hrest1).
    destruct (multi_app_inv _ _ Hm2 Hv2 (subst_atoms s2 t1) (subst_atoms s2 t2) r eq_refl) as
      (fv2 & av2 & Ta2 & body2 & k2 & Hmf2 & Hvf2 & Heq2 & Hma2 & Hva2 & Hfl2 & Hrest2).
    destruct (flows_to_dec kappa.(indirect_reader) l) as [Hfl | Hnf].
    + assert (Hvrf : VR l (Ty_Arrow T1 T2 kappa) fv1 fv2).
      { apply (IH1 l s1 s2 Hlc1 Hlc2 Henv); [split; [exact Hmf1 | exact Hvf1] | split; [exact Hmf2 | exact Hvf2]]. }
      rewrite Heq1 in Hvrf. rewrite Heq2 in Hvrf. simpl in Hvrf.
      pose proof (Hvrf Hfl av1 av2 Hva1 Hva2) as Hbody.
      assert (Harg : VR l T1 av1 av2).
      { apply (IH2 l s1 s2 Hlc1 Hlc2 Henv); [split; [exact Hma1 | exact Hva1] | split; [exact Hma2 | exact Hva2]]. }
      pose proof (Hbody Harg) as Hbody'.
      pose proof (TR_protect l T2 (open body1 av1) (open body2 av2)
                    kappa.(indirect_reader) k1.(indirect_reader) k2.(indirect_reader) Hbody') as Hprot.
      unfold TR in Hprot.
      apply Hprot.
      * split; [exact Hrest1 | exact Hv1].
      * split; [exact Hrest2 | exact Hv2].
    + apply VR_vacuous. apply not_flows_protect. exact Hnf.
  - (* T_Pair *)
    simpl. unfold TR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct (multi_pair_inv _ _ Hm1 Hv1 (subst_atoms s1 t1) (subst_atoms s1 t2) kappa eq_refl) as
      (a1 & b1 & Hma1 & Hva1 & Hmb1 & Hvb1 & Heq1).
    destruct (multi_pair_inv _ _ Hm2 Hv2 (subst_atoms s2 t1) (subst_atoms s2 t2) kappa eq_refl) as
      (a2 & b2 & Hma2 & Hva2 & Hmb2 & Hvb2 & Heq2).
    rewrite Heq1. rewrite Heq2. simpl. intro Hfl. split.
    + apply (IH1 l s1 s2 Hlc1 Hlc2 Henv); [split; [exact Hma1 | exact Hva1] | split; [exact Hma2 | exact Hva2]].
    + apply (IH2 l s1 s2 Hlc1 Hlc2 Henv); [split; [exact Hmb1 | exact Hvb1] | split; [exact Hmb2 | exact Hvb2]].
  - (* T_Fst *)
    simpl. unfold TR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct (multi_fst_inv _ _ Hm1 Hv1 (subst_atoms s1 t) r eq_refl) as
      (w1 & w2 & k1 & Hm1' & Hvw1 & Hvw2 & Hfl1 & Hrest1).
    destruct (multi_fst_inv _ _ Hm2 Hv2 (subst_atoms s2 t) r eq_refl) as
      (w1' & w2' & k2 & Hm2' & Hvw1' & Hvw2' & Hfl2 & Hrest2).
    destruct (flows_to_dec kappa.(indirect_reader) l) as [Hfl | Hnf].
    + assert (Hvrf : VR l (Ty_Prod T1 T2 kappa) (tm_pair w1 w2 k1) (tm_pair w1' w2' k2)).
      { apply (IH1 l s1 s2 Hlc1 Hlc2 Henv); [split; [exact Hm1' | constructor; assumption] | split; [exact Hm2' | constructor; assumption]]. }
      pose proof (VR_prod l T1 T2 kappa w1 w2 w1' w2' k1 k2 Hfl Hvrf) as [Hc1 Hc2].
      assert (Htr1 : TR l T1 w1 w1') by (apply VR_to_TR_value; assumption).
      pose proof (TR_protect l T1 w1 w1' kappa.(indirect_reader) k1.(indirect_reader) k2.(indirect_reader) Htr1) as Hprot.
      exact (Hprot v1 v2 (conj Hrest1 Hv1) (conj Hrest2 Hv2)).
    + apply VR_vacuous. apply not_flows_protect. exact Hnf.
  - (* T_Snd *)
    simpl. unfold TR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct (multi_snd_inv _ _ Hm1 Hv1 (subst_atoms s1 t) r eq_refl) as
      (w1 & w2 & k1 & Hm1' & Hvw1 & Hvw2 & Hfl1 & Hrest1).
    destruct (multi_snd_inv _ _ Hm2 Hv2 (subst_atoms s2 t) r eq_refl) as
      (w1' & w2' & k2 & Hm2' & Hvw1' & Hvw2' & Hfl2 & Hrest2).
    destruct (flows_to_dec kappa.(indirect_reader) l) as [Hfl | Hnf].
    + assert (Hvrf : VR l (Ty_Prod T1 T2 kappa) (tm_pair w1 w2 k1) (tm_pair w1' w2' k2)).
      { apply (IH1 l s1 s2 Hlc1 Hlc2 Henv); [split; [exact Hm1' | constructor; assumption] | split; [exact Hm2' | constructor; assumption]]. }
      pose proof (VR_prod l T1 T2 kappa w1 w2 w1' w2' k1 k2 Hfl Hvrf) as [Hc1 Hc2].
      assert (Htr2 : TR l T2 w2 w2') by (apply VR_to_TR_value; assumption).
      pose proof (TR_protect l T2 w2 w2' kappa.(indirect_reader) k1.(indirect_reader) k2.(indirect_reader) Htr2) as Hprot.
      exact (Hprot v1 v2 (conj Hrest1 Hv1) (conj Hrest2 Hv2)).
    + apply VR_vacuous. apply not_flows_protect. exact Hnf.
  - (* T_Inl *)
    simpl. unfold TR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct (multi_inl_inv _ _ Hm1 Hv1 (subst_atoms s1 t) kappa eq_refl) as
      (w1 & Hm1' & Hvw1 & Heq1).
    destruct (multi_inl_inv _ _ Hm2 Hv2 (subst_atoms s2 t) kappa eq_refl) as
      (w2 & Hm2' & Hvw2 & Heq2).
    rewrite Heq1. rewrite Heq2. simpl. intro Hfl.
    apply (IH1 l s1 s2 Hlc1 Hlc2 Henv); [split; [exact Hm1' | exact Hvw1] | split; [exact Hm2' | exact Hvw2]].
  - (* T_Inr *)
    simpl. unfold TR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct (multi_inr_inv _ _ Hm1 Hv1 (subst_atoms s1 t) kappa eq_refl) as
      (w1 & Hm1' & Hvw1 & Heq1).
    destruct (multi_inr_inv _ _ Hm2 Hv2 (subst_atoms s2 t) kappa eq_refl) as
      (w2 & Hm2' & Hvw2 & Heq2).
    rewrite Heq1. rewrite Heq2. simpl. intro Hfl.
    apply (IH1 l s1 s2 Hlc1 Hlc2 Henv); [split; [exact Hm1' | exact Hvw1] | split; [exact Hm2' | exact Hvw2]].
  - (* T_Case *)
    simpl. unfold TR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct (multi_case_inv _ _ Hm1 Hv1 (subst_atoms s1 t) (subst_atoms s1 body1) (subst_atoms s1 body2) r eq_refl)
      as [[w1 [k1 [Hmc1 [Hvw1 [Hfl1 Hrest1]]]]] | [w1 [k1 [Hmc1 [Hvw1 [Hfl1 Hrest1]]]]]];
    destruct (multi_case_inv _ _ Hm2 Hv2 (subst_atoms s2 t) (subst_atoms s2 body1) (subst_atoms s2 body2) r eq_refl)
      as [[w2 [k2 [Hmc2 [Hvw2 [Hfl2 Hrest2]]]]] | [w2 [k2 [Hmc2 [Hvw2 [Hfl2 Hrest2]]]]]].
    all: destruct (flows_to_dec kappa.(indirect_reader) l) as [Hfl | Hnf].
    + (* inl / inl, flow *)
      assert (Hs : VR l (Ty_Sum T1 T2 kappa) (tm_inl w1 k1) (tm_inl w2 k2)).
      { apply (IH1 l s1 s2 Hlc1 Hlc2 Henv);
          [split; [exact Hmc1 | constructor; exact Hvw1]
          | split; [exact Hmc2 | constructor; exact Hvw2]]. }
      pose proof (VR_sum_inl l T1 T2 kappa w1 w2 k1 k2 Hfl Hs) as Hpayload.
      set (x := fresh_atom (L ++ fv body1)).
      assert (HxL : ~ In x L) by (unfold x; apply fresh_atom_not_in_l).
      assert (Hxfv : ~ In x (fv body1)) by (unfold x; apply fresh_atom_not_in_r).
      assert (Henv' : env_rel l (update Gamma x T1) (extend x w1 s1) (extend x w2 s2)).
      { apply env_rel_update.
        - exact Henv.
        - apply VR_to_TR_value; [exact Hvw1 | exact Hvw2 | exact Hpayload]. }
      pose proof (IH2 x HxL l _ _
        (env_lc_extend s1 x w1 Hlc1 (value_locally_closed w1 Hvw1))
        (env_lc_extend s2 x w2 Hlc2 (value_locally_closed w2 Hvw2)) Henv') as Htr.
      rewrite (subst_open_fvar body1 x w1 s1 Hxfv Hlc1 (value_locally_closed w1 Hvw1)) in Htr.
      rewrite (subst_open_fvar body1 x w2 s2 Hxfv Hlc2 (value_locally_closed w2 Hvw2)) in Htr.
      pose proof (TR_protect l T (open (subst_atoms s1 body1) w1) (open (subst_atoms s2 body1) w2)
                    kappa.(indirect_reader) k1.(indirect_reader) k2.(indirect_reader) Htr) as Hprot.
      unfold TR in Hprot.
      apply Hprot.
      * split; [exact Hrest1 | exact Hv1].
      * split; [exact Hrest2 | exact Hv2].

    + apply VR_vacuous. apply not_flows_protect. exact Hnf.
    + (* inl / inr, flow *)
      assert (Hs : VR l (Ty_Sum T1 T2 kappa) (tm_inl w1 k1) (tm_inr w2 k2)).
      { apply (IH1 l s1 s2 Hlc1 Hlc2 Henv);
          [split; [exact Hmc1 | constructor; exact Hvw1]
          | split; [exact Hmc2 | constructor; exact Hvw2]]. }
      exfalso. exact (VR_sum_lr l T1 T2 kappa w1 w2 k1 k2 Hfl Hs).

    + apply VR_vacuous. apply not_flows_protect. exact Hnf.
    + (* inr / inl, flow *)
      assert (Hs : VR l (Ty_Sum T1 T2 kappa) (tm_inr w1 k1) (tm_inl w2 k2)).
      { apply (IH1 l s1 s2 Hlc1 Hlc2 Henv);
          [split; [exact Hmc1 | constructor; exact Hvw1]
          | split; [exact Hmc2 | constructor; exact Hvw2]]. }
      exfalso. exact (VR_sum_rl l T1 T2 kappa w1 w2 k1 k2 Hfl Hs).

    + apply VR_vacuous. apply not_flows_protect. exact Hnf.
    + (* inr / inr, flow *)
      assert (Hs : VR l (Ty_Sum T1 T2 kappa) (tm_inr w1 k1) (tm_inr w2 k2)).
      { apply (IH1 l s1 s2 Hlc1 Hlc2 Henv);
          [split; [exact Hmc1 | constructor; exact Hvw1]
          | split; [exact Hmc2 | constructor; exact Hvw2]]. }
      pose proof (VR_sum_inr l T1 T2 kappa w1 w2 k1 k2 Hfl Hs) as Hpayload.
      set (x := fresh_atom (L ++ fv body2)).
      assert (HxL : ~ In x L) by (unfold x; apply fresh_atom_not_in_l).
      assert (Hxfv : ~ In x (fv body2)) by (unfold x; apply fresh_atom_not_in_r).
      assert (Henv' : env_rel l (update Gamma x T2) (extend x w1 s1) (extend x w2 s2)).
      { apply env_rel_update.
        - exact Henv.
        - apply VR_to_TR_value; [exact Hvw1 | exact Hvw2 | exact Hpayload]. }
      pose proof (IH3 x HxL l _ _
        (env_lc_extend s1 x w1 Hlc1 (value_locally_closed w1 Hvw1))
        (env_lc_extend s2 x w2 Hlc2 (value_locally_closed w2 Hvw2)) Henv') as Htr.
      rewrite (subst_open_fvar body2 x w1 s1 Hxfv Hlc1 (value_locally_closed w1 Hvw1)) in Htr.
      rewrite (subst_open_fvar body2 x w2 s2 Hxfv Hlc2 (value_locally_closed w2 Hvw2)) in Htr.
      pose proof (TR_protect l T (open (subst_atoms s1 body2) w1) (open (subst_atoms s2 body2) w2)
                    kappa.(indirect_reader) k1.(indirect_reader) k2.(indirect_reader) Htr) as Hprot.
      unfold TR in Hprot.
      apply Hprot.
      * split; [exact Hrest1 | exact Hv1].
      * split; [exact Hrest2 | exact Hv2].

    + apply VR_vacuous. apply not_flows_protect. exact Hnf.
  - (* T_Protect *)
    simpl. apply TR_protect. exact (IH1 l s1 s2 Hlc1 Hlc2 Henv).
  - (* T_Sub *)
    simpl. eapply TR_sub; [exact Hsub | exact (IH1 l s1 s2 Hlc1 Hlc2 Henv)].
  - (* T_If *)
    simpl. unfold TR. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct (multi_if_inv _ _ Hm1 Hv1 (subst_atoms s1 c) (subst_atoms s1 yes) (subst_atoms s1 no) r eq_refl)
      as [[w1 [k1 [Hmc1 [Hvw1 [Hfl1 Hrest1]]]]] | [w1 [k1 [Hmc1 [Hvw1 [Hfl1 Hrest1]]]]]];
    destruct (multi_if_inv _ _ Hm2 Hv2 (subst_atoms s2 c) (subst_atoms s2 yes) (subst_atoms s2 no) r eq_refl)
      as [[w2 [k2 [Hmc2 [Hvw2 [Hfl2 Hrest2]]]]] | [w2 [k2 [Hmc2 [Hvw2 [Hfl2 Hrest2]]]]]].
    all: destruct (flows_to_dec k.(indirect_reader) l) as [Hfl | Hnf].
    + (* inl / inl, flow *)
      assert (Hs : VR l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) (tm_inl w1 k1) (tm_inl w2 k2)).
      { apply (IH1 l s1 s2 Hlc1 Hlc2 Henv);
          [split; [exact Hmc1 | constructor; exact Hvw1]
          | split; [exact Hmc2 | constructor; exact Hvw2]]. }
      pose proof (TR_protect l T (subst_atoms s1 yes) (subst_atoms s2 yes)
                    k.(indirect_reader) k1.(indirect_reader) k2.(indirect_reader)
                    (IH2 l s1 s2 Hlc1 Hlc2 Henv)) as Hprot.
      unfold TR in Hprot.
      apply Hprot.
      * split; [exact Hrest1 | exact Hv1].
      * split; [exact Hrest2 | exact Hv2].

    + apply VR_vacuous. apply not_flows_protect. exact Hnf.
    + (* inl / inr, flow *)
      assert (Hs : VR l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) (tm_inl w1 k1) (tm_inr w2 k2)).
      { apply (IH1 l s1 s2 Hlc1 Hlc2 Henv);
          [split; [exact Hmc1 | constructor; exact Hvw1]
          | split; [exact Hmc2 | constructor; exact Hvw2]]. }
      exfalso. exact (VR_sum_lr l (Ty_Unit public) (Ty_Unit public) k w1 w2 k1 k2 Hfl Hs).

    + apply VR_vacuous. apply not_flows_protect. exact Hnf.
    + (* inr / inl, flow *)
      assert (Hs : VR l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) (tm_inr w1 k1) (tm_inl w2 k2)).
      { apply (IH1 l s1 s2 Hlc1 Hlc2 Henv);
          [split; [exact Hmc1 | constructor; exact Hvw1]
          | split; [exact Hmc2 | constructor; exact Hvw2]]. }
      exfalso. exact (VR_sum_rl l (Ty_Unit public) (Ty_Unit public) k w1 w2 k1 k2 Hfl Hs).

    + apply VR_vacuous. apply not_flows_protect. exact Hnf.
    + (* inr / inr, flow *)
      assert (Hs : VR l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) (tm_inr w1 k1) (tm_inr w2 k2)).
      { apply (IH1 l s1 s2 Hlc1 Hlc2 Henv);
          [split; [exact Hmc1 | constructor; exact Hvw1]
          | split; [exact Hmc2 | constructor; exact Hvw2]]. }
      pose proof (TR_protect l T (subst_atoms s1 no) (subst_atoms s2 no)
                    k.(indirect_reader) k1.(indirect_reader) k2.(indirect_reader)
                    (IH3 l s1 s2 Hlc1 Hlc2 Henv)) as Hprot.
      unfold TR in Hprot.
      apply Hprot.
      * split; [exact Hrest1 | exact Hv1].
      * split; [exact Hrest2 | exact Hv2].

    + apply VR_vacuous. apply not_flows_protect. exact Hnf.
Qed.


(* ================================================================== *)
(* Part 10: Free variables of a program context                       *)
(* ================================================================== *)

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
  | C_CaseLeft t0 C' b2 _ => fv t0 ++ fv_context C' ++ fv b2
  | C_CaseRight t0 b1 C' _ => fv t0 ++ fv b1 ++ fv_context C'
  | C_Protect _ C' => fv_context C'
  | C_IfCondition C' y n _ => fv_context C' ++ fv y ++ fv n
  | C_IfThen c C' n _ => fv c ++ fv_context C' ++ fv n
  | C_IfElse c y C' _ => fv c ++ fv y ++ fv_context C'
  end.

Lemma subst_atoms_extend_id : forall t x u,
  ~ In x (fv t) -> subst_atoms (extend x u tm_fvar) t = t.
Proof.
  intros t x u Hx.
  rewrite subst_atoms_extend_fresh by exact Hx.
  apply subst_atoms_id.
Qed.

Lemma not_in_app_l : forall (l1 l2 : list atom) (x : atom),
  ~ In x (l1 ++ l2) -> ~ In x l1.
Proof. intros l1 l2 x H Hin. apply H. apply in_app_iff. left. exact Hin. Qed.

Lemma not_in_app_r : forall (l1 l2 : list atom) (x : atom),
  ~ In x (l1 ++ l2) -> ~ In x l2.
Proof. intros l1 l2 x H Hin. apply H. apply in_app_iff. right. exact Hin. Qed.

Lemma subst_atoms_plug_fresh : forall C x u,
  ~ In x (fv_context C) ->
  subst_atoms (extend x u tm_fvar) (plug C (tm_fvar x)) = plug C u.
Proof.
  intros C. induction C as
    [ | T C IH | C IH t2 l | t1 C IH l | C IH t2 k | t1 C IH k
      | C IH lp | C IH lp | C IH kp | C IH kp
      | C IH b1 b2 lp | t0 C IH b2 lp | t0 b1 C IH lp
      | lp C IH
      | C IH y n lp | c C IH n lp | c y C IH lp ];
    intros x u Hx; simpl; repeat rewrite app_assoc in Hx.
  - (* Hole *) rewrite extend_eq. reflexivity.
  - (* Abs *) rewrite (IH x u Hx). reflexivity.
  - (* AppLeft *) rewrite (IH x u (not_in_app_l _ _ _ Hx)).
    rewrite (subst_atoms_extend_id t2 x u (not_in_app_r _ _ _ Hx)). reflexivity.
  - (* AppRight *) rewrite (subst_atoms_extend_id t1 x u (not_in_app_l _ _ _ Hx)).
    rewrite (IH x u (not_in_app_r _ _ _ Hx)). reflexivity.
  - (* PairLeft *) rewrite (IH x u (not_in_app_l _ _ _ Hx)).
    rewrite (subst_atoms_extend_id t2 x u (not_in_app_r _ _ _ Hx)). reflexivity.
  - (* PairRight *) rewrite (subst_atoms_extend_id t1 x u (not_in_app_l _ _ _ Hx)).
    rewrite (IH x u (not_in_app_r _ _ _ Hx)). reflexivity.
  - (* Fst *) rewrite (IH x u Hx). reflexivity.
  - (* Snd *) rewrite (IH x u Hx). reflexivity.
  - (* Inl *) rewrite (IH x u Hx). reflexivity.
  - (* Inr *) rewrite (IH x u Hx). reflexivity.
  - (* CaseScrutinee *) rewrite (IH x u (not_in_app_l _ _ _ Hx)).
    rewrite (subst_atoms_extend_id b1 x u (not_in_app_l _ _ _ (not_in_app_r _ _ _ Hx))).
    rewrite (subst_atoms_extend_id b2 x u (not_in_app_r _ _ _ (not_in_app_r _ _ _ Hx))).
    reflexivity.
  - (* CaseLeft *) rewrite (IH x u (not_in_app_l _ _ _ (not_in_app_r _ _ _ Hx))).
    rewrite (subst_atoms_extend_id t0 x u (not_in_app_l _ _ _ Hx)).
    rewrite (subst_atoms_extend_id b2 x u (not_in_app_r _ _ _ (not_in_app_r _ _ _ Hx))).
    reflexivity.
  - (* CaseRight *) rewrite (IH x u (not_in_app_r _ _ _ (not_in_app_r _ _ _ Hx))).
    rewrite (subst_atoms_extend_id t0 x u (not_in_app_l _ _ _ Hx)).
    rewrite (subst_atoms_extend_id b1 x u (not_in_app_l _ _ _ (not_in_app_r _ _ _ Hx))).
    reflexivity.
  - (* Protect *) rewrite (IH x u Hx). reflexivity.
  - (* IfCondition *) rewrite (IH x u (not_in_app_l _ _ _ Hx)).
    rewrite (subst_atoms_extend_id y x u (not_in_app_l _ _ _ (not_in_app_r _ _ _ Hx))).
    rewrite (subst_atoms_extend_id n x u (not_in_app_r _ _ _ (not_in_app_r _ _ _ Hx))).
    reflexivity.
  - (* IfThen *) rewrite (IH x u (not_in_app_l _ _ _ (not_in_app_r _ _ _ Hx))).
    rewrite (subst_atoms_extend_id c x u (not_in_app_l _ _ _ Hx)).
    rewrite (subst_atoms_extend_id n x u (not_in_app_r _ _ _ (not_in_app_r _ _ _ Hx))).
    reflexivity.
  - (* IfElse *) rewrite (IH x u (not_in_app_r _ _ _ (not_in_app_r _ _ _ Hx))).
    rewrite (subst_atoms_extend_id c x u (not_in_app_l _ _ _ Hx)).
    rewrite (subst_atoms_extend_id y x u (not_in_app_l _ _ _ (not_in_app_r _ _ _ Hx))).
    reflexivity.
Qed.

(* ================================================================== *)
(* Part 11: Erasing annotations of related ground values              *)
(* ================================================================== *)

Fixpoint nested_le (kappa : security) (T : ty) : Prop :=
  security_le (security_of T) kappa /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      nested_le kappa T1 /\ nested_le kappa T2
  end.

Lemma transparent_at_nested_le : forall kappa T,
  transparent_at kappa T -> nested_le kappa T.
Proof.
  intros kappa T. induction T; simpl; intros [Hle Hrec]; split; auto.
Qed.

Fixpoint all_indirect_flows (l : label) (T : ty) : Prop :=
  flows_to (security_of T).(indirect_reader) l /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      all_indirect_flows l T1 /\ all_indirect_flows l T2
  end.

Lemma nested_le_all_indirect : forall l kappa T,
  nested_le kappa T -> flows_to kappa.(indirect_reader) l ->
  all_indirect_flows l T.
Proof.
  intros l kappa T. induction T; simpl; intros [Hle Hrec] Hf; split.
  - (* Unit flow *) eapply flows_to_trans; [exact (proj2 Hle) | exact Hf].
  - (* Unit rest *) exact I.
  - (* Sum flow *) eapply flows_to_trans; [exact (proj2 Hle) | exact Hf].
  - (* Sum rest *) destruct Hrec as [H1 H2]. split; [apply IHT1 | apply IHT2]; auto.
  - (* Prod flow *) eapply flows_to_trans; [exact (proj2 Hle) | exact Hf].
  - (* Prod rest *) destruct Hrec as [H1 H2]. split; [apply IHT1 | apply IHT2]; auto.
  - (* Arrow flow *) eapply flows_to_trans; [exact (proj2 Hle) | exact Hf].
  - (* Arrow rest *) destruct Hrec as [H1 H2]. split; [apply IHT1 | apply IHT2]; auto.
Qed.

Lemma VR_erase : forall l T, ground T -> all_indirect_flows l T ->
  forall v1 v2, VR l T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  intros l T. induction T; intros Hg Hall v1 v2 Hv.
  - (* Unit *) simpl in *. destruct Hall as [Hf _]. apply Hv. exact Hf.
  - (* Sum *) simpl in *. destruct Hg as [Hg1 Hg2]. destruct Hall as [Hf [Ha1 Ha2]].
    apply Hv in Hf. destruct v1; destruct v2; simpl in *; try contradiction; try discriminate;
      try (rewrite (IHT1 Hg1 Ha1 _ _ Hf); reflexivity);
      try (rewrite (IHT2 Hg2 Ha2 _ _ Hf); reflexivity).
  - (* Prod *) simpl in *. destruct Hg as [Hg1 Hg2]. destruct Hall as [Hf [Ha1 Ha2]].
    apply Hv in Hf. destruct v1; destruct v2; simpl in *; try contradiction; try discriminate;
      try (destruct Hf as [Hc1 Hc2];
           rewrite (IHT1 Hg1 Ha1 _ _ Hc1); rewrite (IHT2 Hg2 Ha2 _ _ Hc2); reflexivity).
  - (* Arrow *) simpl in *. destruct Hg.
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 HC Hg Htr Hnflow.
  apply flows_to_false in Hnflow.
  destruct Hnflow as [Hsec Hres].
  destruct HC as [L Hplug].
  set (x := fresh_atom (L ++ fv_context C)).
  assert (HxL : ~ In x L) by (unfold x; apply fresh_atom_not_in_l).
  assert (HxC : ~ In x (fv_context C)) by (unfold x; apply fresh_atom_not_in_r).
  (* The two secret terms are related at the secret type. *)
  assert (HsecTR : TR Low T_secret t1 t2).
  { unfold TR. intros v1 v2 E1 E2. apply VR_vacuous.
    rewrite Hsec. simpl. tauto. }
  (* The substitutions are locally closed. *)
  assert (Hlc1 : env_lc (extend x t1 tm_fvar)).
  { apply env_lc_extend.
    - apply env_lc_id.
    - exact (has_type_locally_closed empty t1 T_secret Ht1). }
  assert (Hlc2 : env_lc (extend x t2 tm_fvar)).
  { apply env_lc_extend.
    - apply env_lc_id.
    - exact (has_type_locally_closed empty t2 T_secret Ht2). }
  (* The environments are related. *)
  assert (Henv : env_rel Low (update empty x T_secret)
                   (extend x t1 tm_fvar) (extend x t2 tm_fvar)).
  { intros y U Hlk. unfold update, lookup_context in Hlk. simpl in Hlk.
    destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. injection Hlk as ->.
      rewrite extend_eq. rewrite extend_eq. exact HsecTR.
    - discriminate Hlk. }
  (* Fundamental theorem. *)
  pose proof (fundamental (update empty x T_secret) (plug C (tm_fvar x)) T_result
                (Hplug x HxL) Low
                (extend x t1 tm_fvar) (extend x t2 tm_fvar) Hlc1 Hlc2 Henv) as HtrR.
  rewrite (subst_atoms_plug_fresh C x t1 HxC) in HtrR.
  rewrite (subst_atoms_plug_fresh C x t2 HxC) in HtrR.
  (* All nested annotations flow to Low. *)
  assert (Hall : all_indirect_flows Low T_result).
  { apply (nested_le_all_indirect Low (security_of T_result) T_result).
    - apply transparent_at_nested_le. exact Htr.
    - rewrite Hres. apply flows_to_refl. }
  (* Conclusion. *)
  intros v1 v2 E1 E2.
  unfold TR in HtrR.
  apply (VR_erase Low T_result Hg Hall).
  apply HtrR; assumption.
Qed.
