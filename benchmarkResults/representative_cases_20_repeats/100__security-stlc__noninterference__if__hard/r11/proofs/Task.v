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

(* ============================================================ *)
(* Basic lemmas about labels, security and types                *)
(* ============================================================ *)

Lemma flows_to_refl : forall l, flows_to l l.
Proof. intros l; destruct l; simpl; auto. Qed.

Lemma flows_to_trans : forall a b c,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. intros a b c; destruct a, b, c; simpl; auto; tauto. Qed.

Lemma flows_to_join_l : forall a b c,
  flows_to (join a b) c -> flows_to a c.
Proof. intros a b c; destruct a, b, c; simpl; auto. Qed.

Lemma flows_to_join_r : forall a b c,
  flows_to (join a b) c -> flows_to b c.
Proof. intros a b c; destruct a, b, c; simpl; auto. Qed.

Lemma join_mono_l : forall a b c,
  flows_to a b -> flows_to (join a c) (join b c).
Proof. intros a b c H; destruct a, b, c; simpl in *; auto. Qed.

Lemma join_mono_r : forall a b c,
  flows_to a b -> flows_to (join c a) (join c b).
Proof. intros a b c H; destruct a, b, c; simpl in *; auto. Qed.

Lemma join_assoc : forall a b c,
  join (join a b) c = join a (join b c).
Proof. intros a b c; destruct a, b, c; reflexivity. Qed.

Lemma join_comm : forall a b, join a b = join b a.
Proof. intros a b; destruct a, b; reflexivity. Qed.

Lemma join_absorb_l : forall a b, join a (join a b) = join a b.
Proof. intros a b; destruct a, b; reflexivity. Qed.

Lemma flows_to_to_low : forall a, flows_to a Low -> a = Low.
Proof. intros a H; destruct a; simpl in *; auto; tauto. Qed.

Lemma flows_to_any_high : forall b, b = High -> flows_to High b.
Proof. intros b H; subst b; simpl; auto. Qed.

Lemma not_flows_to_inv : forall a b,
  ~ flows_to a b -> a = High /\ b = Low.
Proof.
  intros a b H; destruct a, b; simpl in *;
    try (exfalso; apply H; exact I); auto.
Qed.

Lemma security_le_refl : forall k, security_le k k.
Proof. intros k; unfold security_le; split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros k1 k2 k3 [H1 H2] [H3 H4]; unfold security_le; split;
    eapply flows_to_trans; eauto.
Qed.

Lemma protect_security_mono : forall k1 k2,
  security_le k1 k2 ->
  forall l, security_le (protect_security k1 l) (protect_security k2 l).
Proof.
  intros k1 k2 [Hr Hi] l; unfold security_le, protect_security; simpl; split;
    apply join_mono_l; auto.
Qed.

Lemma protect_security_assoc : forall k l1 l2,
  protect_security (protect_security k l1) l2 =
  protect_security k (join l1 l2).
Proof.
  intros k l1 l2; unfold protect_security; destruct k as [r i]; simpl.
  f_equal; apply join_assoc.
Qed.

Lemma protect_security_ind : forall k l,
  (protect_security k l).(indirect_reader) = join k.(indirect_reader) l.
Proof. intros k l; reflexivity. Qed.

Lemma protect_security_reader : forall k l,
  (protect_security k l).(reader) = join k.(reader) l.
Proof. intros k l; reflexivity. Qed.

Lemma security_of_ty_protect : forall l T,
  security_of (ty_protect l T) = protect_security (security_of T) l.
Proof. intros l T; destruct T; simpl; reflexivity. Qed.

(* ============================================================ *)
(* The logical relation                                          *)
(* ============================================================ *)

(* [V l T kappa v1 v2] relates two values at type [T] whose top
   security level is [kappa], for an observer at level [l].
   [kappa] is kept separate from [T] so that protecting a type
   (which only changes the top annotation) is easy to handle.     *)

Fixpoint V (l : label) (T : ty) (kappa : security) (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_Unit _ =>
      flows_to kappa.(indirect_reader) l ->
      (exists (k1 k2 : security), v1 = tm_unit k1 /\ v2 = tm_unit k2)
  | Ty_Sum T1 T2 _ =>
      flows_to kappa.(indirect_reader) l ->
      ( (exists (u1 u2 : tm) (k1 k2 : security),
            v1 = tm_inl u1 k1 /\ v2 = tm_inl u2 k2 /\
            V l T1 (security_of T1) u1 u2)
        \/ (exists (u1 u2 : tm) (k1 k2 : security),
            v1 = tm_inr u1 k1 /\ v2 = tm_inr u2 k2 /\
            V l T2 (security_of T2) u1 u2) )
  | Ty_Prod T1 T2 _ =>
      flows_to kappa.(indirect_reader) l ->
      (exists (u1 w1 u2 w2 : tm) (k1 k2 : security),
          v1 = tm_pair u1 w1 k1 /\ v2 = tm_pair u2 w2 k2 /\
          V l T1 (security_of T1) u1 u2 /\
          V l T2 (security_of T2) w1 w2)
  | Ty_Arrow T1 T2 _ =>
      flows_to kappa.(indirect_reader) l ->
      (forall (a1 a2 : tm) (r : label),
          (forall (u1 u2 : tm),
              evaluates a1 u1 -> evaluates a2 u2 ->
              V l T1 (security_of T1) u1 u2) ->
          flows_to kappa.(reader) r ->
          (forall (w1 w2 : tm),
              evaluates (tm_app v1 a1 r) w1 ->
              evaluates (tm_app v2 a2 r) w2 ->
              V l T2 (protect_security (security_of T2) kappa.(indirect_reader))
                w1 w2))
  end.

Definition E (l : label) (T : ty) (kappa : security) (t1 t2 : tm) : Prop :=
  forall (v1 v2 : tm), evaluates t1 v1 -> evaluates t2 v2 -> V l T kappa v1 v2.

Lemma E_ty_protect : forall l l' T t1 t2,
  E l (ty_protect l' T) (security_of (ty_protect l' T)) t1 t2 <->
  E l T (protect_security (security_of T) l') t1 t2.
Proof.
  intros l l' T; destruct T; intros t1 t2; simpl; unfold E; simpl; reflexivity.
Qed.

(* ============================================================ *)
(* Basic lemmas about multi-step evaluation, values and protect *)
(* ============================================================ *)

Lemma multi_trans : forall a b c,
  multi a b -> multi b c -> multi a c.
Proof.
  intros a b c H; induction H; intros Hbc.
  - exact Hbc.
  - apply multi_step with t2; auto.
Qed.

Lemma value_no_step : forall t, value t -> forall t', ~ (t --> t').
Proof.
  intros t Hv. induction Hv; intros t' Hstep; inversion Hstep; subst; try firstorder.
Qed.

Lemma multi_value_inv : forall v v',
  value v -> multi v v' -> v' = v.
Proof.
  intros v v' Hv Hm; induction Hm.
  - reflexivity.
  - exfalso; eapply value_no_step; eauto.
Qed.

Lemma evaluates_value_inv : forall v v',
  value v -> evaluates v v' -> v' = v.
Proof.
  intros v v' Hv [Hm _]; apply multi_value_inv with (v := v); auto.
Qed.

Lemma protect_value_erase : forall v l,
  erase_security (protect_value v l) = erase_security v.
Proof. intros v l; destruct v; simpl; reflexivity. Qed.

Lemma protect_value_protect_value : forall v l1 l2,
  protect_value (protect_value v l1) l2 = protect_value v (join l1 l2).
Proof.
  intros v l1 l2; destruct v; simpl; try reflexivity;
    f_equal; apply protect_security_assoc.
Qed.

Lemma protect_value_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l Hv; induction Hv; simpl.
  - apply v_unit.
  - apply v_abs; assumption.
  - apply v_pair; assumption.
  - apply v_inl; assumption.
  - apply v_inr; assumption.
Qed.

Lemma value_locally_closed : forall v,
  value v -> locally_closed v.
Proof.
  intros v Hv; induction Hv; simpl.
  - exact I.
  - assumption.
  - split; assumption.
  - assumption.
  - assumption.
Qed.

Lemma multi_protect_inv : forall l t t',
  multi (tm_protect l t) t' -> value t' ->
  exists z, multi t z /\ value z /\ t' = protect_value z l.
Proof.
  intros l t t' Hm. remember (tm_protect l t) as tp eqn:E.
  revert t E. induction Hm as [| a b c Hs Hm' IH]; intros t0 E Hv.
  - subst t. inversion Hv.
  - subst a. inversion Hs; subst; clear Hs.
    + assert (Hc : c = protect_value t0 l)
        by (eapply multi_value_inv; eauto using protect_value_value).
      subst c. exists t0; split; [apply multi_refl | split; [assumption | reflexivity]].
    + destruct (IH t' eq_refl Hv) as [z [Hmz [Hvz Heq]]].
      exists z; split; [apply multi_step with t'; assumption | split; assumption].
Qed.

Lemma evaluates_protect_inv : forall l t v,
  evaluates (tm_protect l t) v ->
  exists z, evaluates t z /\ v = protect_value z l.
Proof.
  intros l t v [Hm Hv].
  destruct (multi_protect_inv l t v Hm Hv) as [z [Hmz [Hvz Heq]]].
  exists z; split; [split; assumption | assumption].
Qed.

Lemma multi_protect : forall t z l,
  multi t z -> value z -> multi (tm_protect l t) (protect_value z l).
Proof.
  intros t z l Hm; induction Hm as [| t1 t2 t3 Hs Hm' IH]; intros Hv.
  - eapply multi_step; [apply ST_ProtectValue; assumption | apply multi_refl].
  - eapply multi_step.
    + apply (ST_Protect l t1 t2 Hs).
    + apply IH; assumption.
Qed.

Lemma evaluates_protect_intro : forall l t z,
  evaluates t z -> evaluates (tm_protect l t) (protect_value z l).
Proof.
  intros l t z [Hm Hv]; split.
  - apply multi_protect; assumption.
  - apply protect_value_value; assumption.
Qed.

Lemma abs_no_step : forall (T : ty) (body : tm) (k : security) t',
  ~ (tm_abs T body k --> t').
Proof. intros; intro H; inversion H. Qed.

Lemma multi_abs_inv : forall T body k v,
  multi (tm_abs T body k) v -> v = tm_abs T body k.
Proof.
  intros T body k v Hm.
  remember (tm_abs T body k) as a eqn:E.
  revert T body k E.
  induction Hm as [| t1 t2 t3 Hs Hm' IH]; intros T0 body0 k0 E.
  - reflexivity.
  - subst t1. exfalso; exact (abs_no_step T0 body0 k0 t2 Hs).
Qed.

Lemma multi_app_inv : forall ta tb r v,
  multi (tm_app ta tb r) v -> value v ->
  exists va vb,
    multi ta va /\ value va /\ multi tb vb /\ value vb /\
    (exists (T : ty) (body : tm) (k : security),
        va = tm_abs T body k /\ flows_to k.(reader) r /\
        multi (tm_protect k.(indirect_reader) (open body vb)) v).
Proof.
  intros ta tb r v Hm. remember (tm_app ta tb r) as tp eqn:E.
  revert ta tb r E. induction Hm as [| a b c Hs Hm' IH]; intros ta tb r0 E Hv.
  - subst t. inversion Hv.
  - subst a. inversion Hs; subst; clear Hs.
    + exists (tm_abs T body kappa), tb.
      split; [apply multi_refl | split; [assumption | split; [apply multi_refl
        | split; [assumption | exists T, body, kappa; repeat split; assumption]]]].
    + destruct (IH t1' tb r0 eq_refl Hv) as [va [vb [Hma [Hva [Hmb [Hvb Hex]]]]]].
      exists va, vb; split; [apply multi_step with t1'; assumption | repeat split; assumption].
    + destruct (IH ta t2' r0 eq_refl Hv) as [va [vb [Hma [Hva [Hmb [Hvb Hex]]]]]].
      exists va, vb; repeat split; try assumption.
      apply multi_step with t2'; assumption.
Qed.

Lemma evaluates_app_inv : forall ta tb r v,
  evaluates (tm_app ta tb r) v ->
  exists va vb,
    evaluates ta va /\ value va /\ evaluates tb vb /\ value vb /\
    (exists (T : ty) (body : tm) (k : security),
        va = tm_abs T body k /\ flows_to k.(reader) r /\
        evaluates (tm_protect k.(indirect_reader) (open body vb)) v).
Proof.
  intros ta tb r v [Hm Hv].
  destruct (multi_app_inv ta tb r v Hm Hv) as [va [vb [Hma [Hva [Hmb [Hvb Hex]]]]]].
  exists va, vb. split.
  - split; assumption.
  - split; [assumption | split].
    + split; assumption.
    + split; [assumption |].
      destruct Hex as [T [body [k [Heq [Hflow Hmulti]]]]].
      exists T, body, k. repeat split; assumption.
Qed.

Lemma evaluates_app_abs_inv : forall T body k a r v,
  evaluates (tm_app (tm_abs T body k) a r) v ->
  exists u, evaluates a u /\ value u /\ flows_to k.(reader) r /\
    evaluates (tm_protect k.(indirect_reader) (open body u)) v.
Proof.
  intros T body k a r v Hev.
  destruct (evaluates_app_inv (tm_abs T body k) a r v Hev) as
    (va & vb & Heva & Hva & Hevb & Hvb & T' & body' & k' & Heq & Hflow & Hevprot).
  assert (Hva_eq : va = tm_abs T body k).
  { destruct Heva as [Hm _]. apply multi_abs_inv in Hm. exact Hm. }
  assert (Hva2 : tm_abs T body k = tm_abs T' body' k').
  { rewrite <- Hva_eq. exact Heq. }
  inversion Hva2; subst; clear Hva2.
  exists vb; split; [exact Hevb | split; [exact Hvb | split; [exact Hflow | exact Hevprot]]].
Qed.

Lemma evaluates_app_abs_intro : forall T body k a r u v,
  value (tm_abs T body k) -> value u -> flows_to k.(reader) r ->
  evaluates a u -> evaluates (tm_protect k.(indirect_reader) (open body u)) v ->
  evaluates (tm_app (tm_abs T body k) a r) v.
Proof.
  intros T body k a r u v Hvabs Hvu Hflow Heva Hevprot.
  split.
  - destruct Heva as [Hma _]; destruct Hevprot as [Hmp _].
    eapply multi_trans.
    + eapply multi_trans.
      * induction Hma as [| t1 t2 t3 Hs Hm IH].
        -- apply multi_refl.
        -- eapply multi_step.
           ++ exact (ST_App2 (tm_abs T body k) t1 t2 r Hvabs Hs).
           ++ apply IH; assumption.
      * eapply multi_step.
        -- exact (ST_AppAbs T body k u r Hvabs Hvu Hflow).
        -- apply multi_refl.
    + exact Hmp.
  - destruct Hevprot as [_ Hv]; exact Hv.
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
Admitted.
