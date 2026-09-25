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

Lemma erase_type_protect : forall l T,
  erase_type (ty_protect l T) = erase_type T.
Proof. intros l [k|A B k|A B k|A B k]; reflexivity. Qed.

Lemma protect_low_erase_type : forall T,
  ty_protect Low (erase_type T) = erase_type T.
Proof. intros [k|A B k|A B k|A B k]; reflexivity. Qed.

Lemma erase_security_open_rec : forall t k u,
  erase_security (open_rec k u t) =
  open_rec k (erase_security u) (erase_security t).
Proof.
  induction t; intros k u; simpl;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity).
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma erase_security_open : forall t u,
  erase_security (open t u) =
  open (erase_security t) (erase_security u).
Proof. intros; apply erase_security_open_rec. Qed.

Lemma erase_subtype : forall T U,
  subtype T U -> subtype (erase_type T) (erase_type U).
Proof.
  intros T U H; induction H; simpl.
  - apply S_Unit; simpl; repeat split; trivial.
  - apply S_Sum; auto; simpl; repeat split; trivial.
  - apply S_Prod; auto; simpl; repeat split; trivial.
  - apply S_Arrow; auto; simpl; repeat split; trivial.
  - eapply S_Trans; eauto.
Qed.

Definition erase_context (Gamma : context) : context :=
  map (fun p => (fst p, erase_type (snd p))) Gamma.

Lemma erase_context_update : forall Gamma x T,
  erase_context (update Gamma x T) =
  update (erase_context Gamma) x (erase_type T).
Proof. reflexivity. Qed.

Lemma erase_context_lookup : forall Gamma x T,
  lookup_context x Gamma = Some T ->
  lookup_context x (erase_context Gamma) = Some (erase_type T).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y); simpl in *; auto.
    inversion H; subst; reflexivity.
Qed.

Lemma wf_erase_type : forall T, wf_ty (erase_type T).
Proof.
  induction T; simpl; auto; repeat split; auto.
Qed.

Lemma erase_typing : forall Gamma t T,
  has_type Gamma t T ->
  has_type (erase_context Gamma) (erase_security t) (erase_type T).
Proof.
  intros Gamma t T H; induction H; simpl.
  - apply T_Var; auto using erase_context_lookup, wf_erase_type.
  - apply T_Unit. simpl. exact I.
  - eapply T_Abs with (L := L).
    + apply wf_erase_type.
    + simpl. exact I.
    + intros x Hx. specialize (H2 x Hx).
      rewrite erase_context_update in H2.
      rewrite erase_security_open in H2. simpl in H2. exact H2.
  - rewrite erase_type_protect.
    rewrite <- protect_low_erase_type.
    eapply T_App with (kappa := public); simpl; eauto.
  - eapply T_Pair; eauto. simpl. exact I.
  - rewrite erase_type_protect.
    rewrite <- protect_low_erase_type.
    eapply T_Fst with (kappa := public); simpl; eauto.
  - rewrite erase_type_protect.
    rewrite <- protect_low_erase_type.
    eapply T_Snd with (kappa := public); simpl; eauto.
  - eapply T_Inl; eauto using wf_erase_type. simpl. exact I.
  - eapply T_Inr; eauto using wf_erase_type. simpl. exact I.
  - rewrite erase_type_protect.
    rewrite <- protect_low_erase_type.
    eapply T_Case with (L := L) (kappa := public); simpl; eauto.
    + intros x Hx. specialize (H2 x Hx).
      rewrite erase_security_open in H2. simpl in H2. exact H2.
    + intros x Hx. specialize (H4 x Hx).
      rewrite erase_security_open in H4. simpl in H4. exact H4.
  - rewrite erase_type_protect. exact IHhas_type.
  - eapply T_Sub; eauto using erase_subtype.
Qed.

Lemma fv_open_rec : forall t k x z,
  In z (fv (open_rec k (tm_fvar x) t)) ->
  z = x \/ In z (fv t).
Proof.
  induction t; intros k x z Hz; simpl in *;
    try (apply IHt in Hz; tauto);
    try (apply in_app_or in Hz; destruct Hz as [Hz|Hz];
         [apply IHt1 in Hz|apply IHt2 in Hz];
         repeat rewrite in_app_iff; tauto).
  - destruct (Nat.eqb k n); simpl in Hz; try contradiction.
    destruct Hz as [Hz|[]]. left. symmetry. exact Hz.
  - right; exact Hz.
  - contradiction.
  - repeat rewrite in_app_iff in *.
    destruct Hz as [Hz|[Hz|Hz]].
    + apply IHt1 in Hz. tauto.
    + apply IHt2 in Hz. tauto.
    + apply IHt3 in Hz. tauto.
Qed.

Lemma typing_context_invariance : forall Gamma Delta t T,
  has_type Gamma t T ->
  (forall x, In x (fv t) ->
    lookup_context x Gamma = lookup_context x Delta) ->
  has_type Delta t T.
Proof.
  intros Gamma Delta t T H; revert Delta.
  induction H; intros Delta Heq; simpl in *.
  - apply T_Var; auto. rewrite <- (Heq x); auto.
  - apply T_Unit; auto.
  - eapply T_Abs with (L := L); eauto.
    intros y Hy. apply H2; auto.
    intros z Hz. apply fv_open_rec in Hz.
    destruct Hz as [->|Hz]; simpl.
    + rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eqb z y); auto.
  - eapply T_App; eauto.
    + apply IHhas_type1. intros x Hx. apply Heq.
      apply in_or_app. left; exact Hx.
    + apply IHhas_type2. intros x Hx. apply Heq.
      apply in_or_app. right; exact Hx.
  - eapply T_Pair; eauto.
    + apply IHhas_type1. intros x Hx. apply Heq.
      apply in_or_app. left; exact Hx.
    + apply IHhas_type2. intros x Hx. apply Heq.
      apply in_or_app. right; exact Hx.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
  - eapply T_Inl; eauto.
  - eapply T_Inr; eauto.
  - eapply T_Case with (L := L); eauto.
    + apply IHhas_type. intros x Hx. apply Heq.
      repeat rewrite in_app_iff. tauto.
    + intros y Hy. apply H2; auto.
      intros z Hz. apply fv_open_rec in Hz.
      destruct Hz as [->|Hz]; simpl.
      * rewrite Nat.eqb_refl. reflexivity.
      * destruct (Nat.eqb z y); auto. apply Heq.
        repeat rewrite in_app_iff. tauto.
    + intros y Hy. apply H4; auto.
      intros z Hz. apply fv_open_rec in Hz.
      destruct Hz as [->|Hz]; simpl.
      * rewrite Nat.eqb_refl. reflexivity.
      * destruct (Nat.eqb z y); auto. apply Heq.
        repeat rewrite in_app_iff. tauto.
  - eapply T_Protect; eauto.
  - eapply T_Sub; eauto.
Qed.

Lemma fv_open_contains : forall t k u x,
  In x (fv t) -> In x (fv (open_rec k u t)).
Proof.
  induction t; intros k u x Hx; simpl in *; try contradiction;
    try (apply IHt; exact Hx);
    try (apply in_app_or in Hx; apply in_or_app;
         destruct Hx as [Hx|Hx];
         [left; apply IHt1|right; apply IHt2]; exact Hx).
  - exact Hx.
  - repeat rewrite in_app_iff in *.
    destruct Hx as [Hx|[Hx|Hx]].
    + left. apply IHt1. exact Hx.
    + right; left. apply IHt2. exact Hx.
    + right; right. apply IHt3. exact Hx.
Qed.

Definition fresh (L : list atom) : atom :=
  S (fold_right Nat.max 0 L).

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L. unfold fresh.
  assert (Hmax : forall x, In x L -> x <= fold_right Nat.max 0 L).
  { induction L as [|a L IH]; intros x Hx; simpl in *.
    - contradiction.
    - destruct Hx as [<-|Hx]; [apply Nat.le_max_l|].
      eapply Nat.le_trans; [apply IH; exact Hx|apply Nat.le_max_r]. }
  intros Hin. specialize (Hmax _ Hin). lia.
Qed.

Lemma typing_fv : forall Gamma t T x,
  has_type Gamma t T -> In x (fv t) ->
  exists U, lookup_context x Gamma = Some U.
Proof.
  intros Gamma t T x H; induction H; simpl; intros Hx;
    try contradiction;
    try solve [eapply IHhas_type; eauto].
  - destruct Hx as [<-|[]]. eauto.
  - set (y := fresh (x :: L)).
    assert (Hfresh : ~ In y L /\ y <> x).
    { subst y. pose proof (fresh_not_in (x :: L)) as Hni.
      split; intro Hbad; apply Hni; simpl.
      - right; exact Hbad.
      - left; symmetry; exact Hbad. }
    destruct Hfresh as [HyL Hyx].
    specialize (H2 y HyL).
    specialize (H2 (fv_open_contains body 0 (tm_fvar y) x Hx)).
    destruct H2 as [U HU]. exists U.
    simpl in HU. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. congruence.
    + exact HU.
  - apply in_app_or in Hx. destruct Hx as [Hx|Hx].
    + eapply IHhas_type1; eauto.
    + eapply IHhas_type2; eauto.
  - apply in_app_or in Hx. destruct Hx as [Hx|Hx].
    + eapply IHhas_type1; eauto.
    + eapply IHhas_type2; eauto.
  - repeat rewrite in_app_iff in Hx.
    destruct Hx as [Hx|[Hx|Hx]].
    + eapply IHhas_type; eauto.
    + set (y := fresh (x :: L)).
      assert (Hfresh : ~ In y L /\ y <> x).
      { subst y. pose proof (fresh_not_in (x :: L)) as Hni.
        split; intro Hbad; apply Hni; simpl.
        - right; exact Hbad.
        - left; symmetry; exact Hbad. }
      destruct Hfresh as [HyL Hyx].
      specialize (H2 y HyL).
      specialize (H2 (fv_open_contains body1 0 (tm_fvar y) x Hx)).
      destruct H2 as [U HU]. exists U.
      simpl in HU. destruct (Nat.eqb x y) eqn:E.
      * apply Nat.eqb_eq in E. congruence.
      * exact HU.
    + set (y := fresh (x :: L)).
      assert (Hfresh : ~ In y L /\ y <> x).
      { subst y. pose proof (fresh_not_in (x :: L)) as Hni.
        split; intro Hbad; apply Hni; simpl.
        - right; exact Hbad.
        - left; symmetry; exact Hbad. }
      destruct Hfresh as [HyL Hyx].
      specialize (H4 y HyL).
      specialize (H4 (fv_open_contains body2 0 (tm_fvar y) x Hx)).
      destruct H4 as [U HU]. exists U.
      simpl in HU. destruct (Nat.eqb x y) eqn:E.
      * apply Nat.eqb_eq in E. congruence.
      * exact HU.
Qed.

Lemma lc_open_fvar_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x H; simpl in *;
    repeat match goal with
    | Hc : _ /\ _ |- _ => destruct Hc
    | |- _ /\ _ => split
    end;
    try exact I;
    try (eapply IHt; eauto);
    try (eapply IHt1; eauto);
    try (eapply IHt2; eauto);
    try (eapply IHt3; eauto).
  destruct (Nat.eqb k n) eqn:E; simpl in H.
  - apply Nat.eqb_eq in E. lia.
  - lia.
Qed.

Lemma lc_at_erase_reverse : forall t k,
  lc_at k (erase_security t) -> lc_at k t.
Proof.
  induction t; intros k H; simpl in *;
    repeat match goal with
    | Hc : _ /\ _ |- _ => destruct Hc
    | |- _ /\ _ => split
    end;
    try exact I; try assumption;
    try (eapply IHt; eauto);
    try (eapply IHt1; eauto);
    try (eapply IHt2; eauto);
    try (eapply IHt3; eauto).
Qed.

Lemma typing_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H; induction H; unfold locally_closed in *; simpl;
    try exact I; try tauto; try assumption.
  - set (x := fresh L).
    assert (Hx : ~ In x L) by (subst x; apply fresh_not_in).
    specialize (H2 x Hx). unfold open in H2.
    apply lc_open_fvar_inv in H2. exact H2.
  - set (x := fresh L).
    assert (Hx : ~ In x L) by (subst x; apply fresh_not_in).
    specialize (H2 x Hx). specialize (H4 x Hx).
    unfold open in H2, H4.
    apply lc_open_fvar_inv in H2.
    apply lc_open_fvar_inv in H4.
    tauto.
Qed.

Lemma underlying_typed_lc : forall T t,
  underlying_typed T t -> locally_closed t.
Proof.
  intros T t H. unfold underlying_typed in H.
  pose proof (typing_lc _ _ _ H) as Hlc.
  unfold locally_closed in *. eapply lc_at_erase_reverse; eauto.
Qed.

Lemma lc_open_rec_id : forall t k u,
  lc_at k t -> open_rec k u t = t.
Proof.
  induction t; intros k u H; simpl in *;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; auto;
         try tauto).
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma lc_at_weaken : forall t k j,
  lc_at k t -> k <= j -> lc_at j t.
Proof.
  induction t; intros k j H Hle; simpl in *;
    repeat match goal with
    | Hc : _ /\ _ |- _ => destruct Hc
    | |- _ /\ _ => split
    end;
    try exact I; try lia;
    try (eapply IHt; eauto; lia);
    try (eapply IHt1; eauto; lia);
    try (eapply IHt2; eauto; lia);
    try (eapply IHt3; eauto; lia).
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; induction H; unfold locally_closed in *; simpl in *; auto; tauto.
Qed.

Lemma subst_open_fvar : forall t k x y u,
  x <> y -> locally_closed u ->
  subst x u (open_rec k (tm_fvar y) t) =
  open_rec k (tm_fvar y) (subst x u t).
Proof.
  induction t; intros k x y u Hxy Hu; simpl;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; auto; reflexivity).
  - destruct (Nat.eqb k n); simpl; auto.
    destruct (Nat.eqb x y) eqn:E; auto.
    apply Nat.eqb_eq in E. contradiction.
  - destruct (Nat.eqb x a) eqn:E; simpl.
    + symmetry. apply lc_open_rec_id.
      eapply lc_at_weaken; eauto. lia.
    + reflexivity.
Qed.

Lemma typing_weaken_fresh : forall Gamma t T y U,
  has_type Gamma t T -> ~ In y (fv t) ->
  has_type (update Gamma y U) t T.
Proof.
  intros Gamma t T y U H Hfresh.
  eapply typing_context_invariance; eauto.
  intros z Hz. simpl.
  destruct (Nat.eqb z y) eqn:E; auto.
  apply Nat.eqb_eq in E. subst. contradiction.
Qed.

Definition substitution_context (Gamma Delta : context) (x : atom) (u : tm) : Prop :=
  forall z V, lookup_context z Gamma = Some V ->
    if Nat.eqb x z then has_type Delta u V
    else lookup_context z Delta = Some V.

Lemma substitution_context_extend : forall Gamma Delta x u y U,
  substitution_context Gamma Delta x u -> x <> y -> ~ In y (fv u) ->
  substitution_context (update Gamma y U) (update Delta y U) x u.
Proof.
  unfold substitution_context. intros Gamma Delta x u y U Hctx Hxy Hy z V Hlookup.
  simpl in Hlookup.
  destruct (Nat.eqb z y) eqn:Ezy.
  - inversion Hlookup; subst V.
    apply Nat.eqb_eq in Ezy. subst z.
    destruct (Nat.eqb x y) eqn:Exy.
    + apply Nat.eqb_eq in Exy. contradiction.
    + simpl. rewrite Nat.eqb_refl. reflexivity.
  - specialize (Hctx z V Hlookup).
    destruct (Nat.eqb x z) eqn:Exz.
    + eapply typing_weaken_fresh; eauto.
    + simpl. rewrite Ezy. exact Hctx.
Qed.

Lemma typing_subst : forall Gamma t T,
  has_type Gamma t T ->
  forall Delta x u,
    value u -> substitution_context Gamma Delta x u ->
    has_type Delta (subst x u t) T.
Proof.
  intros Gamma t T H; induction H; intros Delta a u Hu Hctx; simpl.
  - specialize (Hctx x T H).
    destruct (Nat.eqb a x); auto using T_Var.
  - apply T_Unit; auto.
  - eapply T_Abs with (L := a :: fv u ++ L); eauto.
    intros y Hy.
    assert (Hya : a <> y) by (intro E; subst; apply Hy; simpl; auto).
    assert (Hyfv : ~ In y (fv u)).
    { intro Hin. apply Hy. simpl. right. apply in_or_app. left. exact Hin. }
    assert (HyL : ~ In y L).
    { intro Hin. apply Hy. simpl. right. apply in_or_app. right. exact Hin. }
    unfold open. rewrite <- subst_open_fvar by (auto using value_lc).
    apply H2; auto.
    eapply substitution_context_extend; eauto.
  - eapply T_App; eauto.
  - eapply T_Pair; eauto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
  - eapply T_Inl; eauto.
  - eapply T_Inr; eauto.
  - eapply T_Case with (L := a :: fv u ++ L); eauto.
    + intros y Hy.
      assert (Hya : a <> y) by (intro E; subst; apply Hy; simpl; auto).
      assert (Hyfv : ~ In y (fv u)).
      { intro Hin. apply Hy. simpl. right. apply in_or_app. left. exact Hin. }
      assert (HyL : ~ In y L).
      { intro Hin. apply Hy. simpl. right. apply in_or_app. right. exact Hin. }
      unfold open. rewrite <- subst_open_fvar by (auto using value_lc).
      apply H2; auto.
      eapply substitution_context_extend; eauto.
    + intros y Hy.
      assert (Hya : a <> y) by (intro E; subst; apply Hy; simpl; auto).
      assert (Hyfv : ~ In y (fv u)).
      { intro Hin. apply Hy. simpl. right. apply in_or_app. left. exact Hin. }
      assert (HyL : ~ In y L).
      { intro Hin. apply Hy. simpl. right. apply in_or_app. right. exact Hin. }
      unfold open. rewrite <- subst_open_fvar by (auto using value_lc).
      apply H4; auto.
      eapply substitution_context_extend; eauto.
  - eapply T_Protect; eauto.
  - eapply T_Sub; eauto.
Qed.

Lemma flows_to_refl : forall l, flows_to l l.
Proof. destruct l; exact I. Qed.

Lemma flows_to_trans : forall a b c,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. destruct a, b, c; simpl; tauto. Qed.

Lemma value_relation_ground_erase : forall observer kappa T v1 v2,
  ground T -> transparent_at kappa T ->
  flows_to kappa.(indirect_reader) observer ->
  value_relation observer T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  intros observer kappa T; induction T; intros v1 v2 Hg Htr Hflow Hrel;
    simpl in Hg, Htr, Hrel.
  - destruct Htr as [Hle _].
    destruct Hrel as [_ [_ [_ [_ Hshape]]]].
    specialize (Hshape (flows_to_trans _ _ _ (proj2 Hle) Hflow)).
    destruct Hshape as [k1 [k2 [-> ->]]]. reflexivity.
  - destruct Hg as [Hg1 Hg2].
    destruct Htr as [Hle [Ht1 Ht2]].
    destruct Hrel as [_ [_ [_ [_ Hshape]]]].
    specialize (Hshape (flows_to_trans _ _ _ (proj2 Hle) Hflow)).
    destruct Hshape as [[u1 [u2 [k1 [k2 [-> [-> Hr]]]]]]|
                       [u1 [u2 [k1 [k2 [-> [-> Hr]]]]]]]; simpl;
      f_equal; [eapply IHT1|eapply IHT2]; eauto.
  - destruct Hg as [Hg1 Hg2].
    destruct Htr as [Hle [Ht1 Ht2]].
    destruct Hrel as [_ [_ [_ [_ Hshape]]]].
    specialize (Hshape (flows_to_trans _ _ _ (proj2 Hle) Hflow)).
    destruct Hshape as [a1 [b1 [a2 [b2 [k1 [k2
      [-> [-> [Ha Hb]]]]]]]]]. simpl. f_equal.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - contradiction.
Qed.

Lemma subtype_erase_eq : forall T U,
  subtype T U -> erase_type T = erase_type U.
Proof.
  intros T U H; induction H; simpl; try congruence.
Qed.

Lemma erase_type_idempotent : forall T,
  erase_type (erase_type T) = erase_type T.
Proof.
  induction T; simpl; try rewrite IHT1, IHT2; reflexivity.
Qed.

Inductive simple_type : context -> tm -> ty -> Prop :=
  | Simple_Var : forall Gamma x T,
      lookup_context x Gamma = Some T ->
      simple_type Gamma (tm_fvar x) T
  | Simple_Unit : forall Gamma kappa,
      simple_type Gamma (tm_unit kappa) (Ty_Unit public)
  | Simple_Abs : forall L Gamma T1 body T2 kappa,
      (forall x, ~ In x L ->
        simple_type (update Gamma x T1) (open body (tm_fvar x)) T2) ->
      simple_type Gamma (tm_abs T1 body kappa) (Ty_Arrow T1 T2 public)
  | Simple_App : forall Gamma f a T1 T2 r,
      simple_type Gamma f (Ty_Arrow T1 T2 public) ->
      simple_type Gamma a T1 ->
      simple_type Gamma (tm_app f a r) T2
  | Simple_Pair : forall Gamma a b T1 T2 kappa,
      simple_type Gamma a T1 -> simple_type Gamma b T2 ->
      simple_type Gamma (tm_pair a b kappa) (Ty_Prod T1 T2 public)
  | Simple_Fst : forall Gamma p T1 T2 r,
      simple_type Gamma p (Ty_Prod T1 T2 public) ->
      simple_type Gamma (tm_fst p r) T1
  | Simple_Snd : forall Gamma p T1 T2 r,
      simple_type Gamma p (Ty_Prod T1 T2 public) ->
      simple_type Gamma (tm_snd p r) T2
  | Simple_Inl : forall Gamma a T1 T2 kappa,
      simple_type Gamma a T1 ->
      simple_type Gamma (tm_inl a kappa) (Ty_Sum T1 T2 public)
  | Simple_Inr : forall Gamma b T1 T2 kappa,
      simple_type Gamma b T2 ->
      simple_type Gamma (tm_inr b kappa) (Ty_Sum T1 T2 public)
  | Simple_Case : forall L Gamma t body1 body2 T1 T2 T r,
      simple_type Gamma t (Ty_Sum T1 T2 public) ->
      (forall x, ~ In x L ->
        simple_type (update Gamma x T1) (open body1 (tm_fvar x)) T) ->
      (forall x, ~ In x L ->
        simple_type (update Gamma x T2) (open body2 (tm_fvar x)) T) ->
      simple_type Gamma (tm_case t body1 body2 r) T
  | Simple_Protect : forall Gamma l t T,
      simple_type Gamma t T -> simple_type Gamma (tm_protect l t) T.

Lemma erasure_simple_type : forall Gamma t T,
  has_type Gamma t T ->
  simple_type (erase_context Gamma) (erase_security t) (erase_type T).
Proof.
  intros Gamma t T H; induction H; simpl.
  - apply Simple_Var. eapply erase_context_lookup; eauto.
  - constructor.
  - eapply Simple_Abs with (L := L).
    intros x Hx. specialize (H2 x Hx).
    rewrite erase_context_update in H2.
    rewrite erase_security_open in H2. simpl in H2. exact H2.
  - rewrite erase_type_protect. eapply Simple_App; eauto.
  - eapply Simple_Pair; eauto.
  - rewrite erase_type_protect. eapply Simple_Fst; eauto.
  - rewrite erase_type_protect. eapply Simple_Snd; eauto.
  - eapply Simple_Inl; eauto.
  - eapply Simple_Inr; eauto.
  - rewrite erase_type_protect.
    eapply Simple_Case with (L := L); eauto.
    + intros x Hx. specialize (H2 x Hx).
      rewrite erase_security_open in H2. simpl in H2. exact H2.
    + intros x Hx. specialize (H4 x Hx).
      rewrite erase_security_open in H4. simpl in H4. exact H4.
  - rewrite erase_type_protect. exact IHhas_type.
  - rewrite <- (subtype_erase_eq _ _ H0). exact IHhas_type.
Qed.

Lemma simple_context_invariance : forall Gamma Delta t T,
  simple_type Gamma t T ->
  (forall x, In x (fv t) ->
    lookup_context x Gamma = lookup_context x Delta) ->
  simple_type Delta t T.
Proof.
  intros Gamma Delta t T H; revert Delta.
  induction H; intros Delta Heq; simpl in *.
  - apply Simple_Var. rewrite <- (Heq x); auto.
  - apply Simple_Unit.
  - eapply Simple_Abs with (L := L).
    intros y Hy. apply H0; auto.
    intros z Hz. apply fv_open_rec in Hz.
    destruct Hz as [->|Hz]; simpl.
    + rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eqb z y); auto.
  - eapply Simple_App.
    + apply IHsimple_type1. intros x Hx. apply Heq.
      apply in_or_app. left; exact Hx.
    + apply IHsimple_type2. intros x Hx. apply Heq.
      apply in_or_app. right; exact Hx.
  - eapply Simple_Pair.
    + apply IHsimple_type1. intros x Hx. apply Heq.
      apply in_or_app. left; exact Hx.
    + apply IHsimple_type2. intros x Hx. apply Heq.
      apply in_or_app. right; exact Hx.
  - eapply Simple_Fst; eauto.
  - eapply Simple_Snd; eauto.
  - eapply Simple_Inl; eauto.
  - eapply Simple_Inr; eauto.
  - eapply Simple_Case with (L := L).
    + apply IHsimple_type. intros x Hx. apply Heq.
      repeat rewrite in_app_iff. tauto.
    + intros y Hy. apply H1; auto.
      intros z Hz. apply fv_open_rec in Hz.
      destruct Hz as [->|Hz]; simpl.
      * rewrite Nat.eqb_refl. reflexivity.
      * destruct (Nat.eqb z y); auto. apply Heq.
        repeat rewrite in_app_iff. tauto.
    + intros y Hy. apply H3; auto.
      intros z Hz. apply fv_open_rec in Hz.
      destruct Hz as [->|Hz]; simpl.
      * rewrite Nat.eqb_refl. reflexivity.
      * destruct (Nat.eqb z y); auto. apply Heq.
        repeat rewrite in_app_iff. tauto.
  - eapply Simple_Protect; eauto.
Qed.

Definition simple_substitution_context
  (Gamma Delta : context) (x : atom) (u : tm) : Prop :=
  forall z V, lookup_context z Gamma = Some V ->
    if Nat.eqb x z then simple_type Delta u V
    else lookup_context z Delta = Some V.

Lemma simple_weaken_fresh : forall Gamma t T y U,
  simple_type Gamma t T -> ~ In y (fv t) ->
  simple_type (update Gamma y U) t T.
Proof.
  intros Gamma t T y U H Hfresh.
  eapply simple_context_invariance; eauto.
  intros z Hz. simpl.
  destruct (Nat.eqb z y) eqn:E; auto.
  apply Nat.eqb_eq in E. subst. contradiction.
Qed.

Lemma simple_substitution_context_extend : forall Gamma Delta x u y U,
  simple_substitution_context Gamma Delta x u ->
  x <> y -> ~ In y (fv u) ->
  simple_substitution_context (update Gamma y U) (update Delta y U) x u.
Proof.
  unfold simple_substitution_context.
  intros Gamma Delta x u y U Hctx Hxy Hy z V Hlookup.
  simpl in Hlookup.
  destruct (Nat.eqb z y) eqn:Ezy.
  - inversion Hlookup; subst V.
    apply Nat.eqb_eq in Ezy. subst z.
    destruct (Nat.eqb x y) eqn:Exy.
    + apply Nat.eqb_eq in Exy. contradiction.
    + simpl. rewrite Nat.eqb_refl. reflexivity.
  - specialize (Hctx z V Hlookup).
    destruct (Nat.eqb x z) eqn:Exz.
    + eapply simple_weaken_fresh; eauto.
    + simpl. rewrite Ezy. exact Hctx.
Qed.

Lemma simple_subst : forall Gamma t T,
  simple_type Gamma t T ->
  forall Delta x u,
    locally_closed u -> simple_substitution_context Gamma Delta x u ->
    simple_type Delta (subst x u t) T.
Proof.
  intros Gamma t T H; induction H; intros Delta q u Hu Hctx; simpl.
  - specialize (Hctx x T H).
    destruct (Nat.eqb q x); auto using Simple_Var.
  - apply Simple_Unit.
  - eapply Simple_Abs with (L := q :: fv u ++ L).
    intros y Hy.
    assert (Hya : q <> y) by (intro E; subst; apply Hy; simpl; auto).
    assert (Hyfv : ~ In y (fv u)).
    { intro Hin. apply Hy. simpl. right. apply in_or_app. left. exact Hin. }
    assert (HyL : ~ In y L).
    { intro Hin. apply Hy. simpl. right. apply in_or_app. right. exact Hin. }
    unfold open. rewrite <- subst_open_fvar by auto.
    apply H0; auto.
    eapply simple_substitution_context_extend; eauto.
  - eapply Simple_App; eauto.
  - eapply Simple_Pair; eauto.
  - eapply Simple_Fst; eauto.
  - eapply Simple_Snd; eauto.
  - eapply Simple_Inl; eauto.
  - eapply Simple_Inr; eauto.
  - eapply Simple_Case with (L := q :: fv u ++ L).
    + eauto.
    + intros y Hy.
      assert (Hya : q <> y) by (intro E; subst; apply Hy; simpl; auto).
      assert (Hyfv : ~ In y (fv u)).
      { intro Hin. apply Hy. simpl. right. apply in_or_app. left. exact Hin. }
      assert (HyL : ~ In y L).
      { intro Hin. apply Hy. simpl. right. apply in_or_app. right. exact Hin. }
      unfold open. rewrite <- subst_open_fvar by auto.
      apply H1; auto.
      eapply simple_substitution_context_extend; eauto.
    + intros y Hy.
      assert (Hya : q <> y) by (intro E; subst; apply Hy; simpl; auto).
      assert (Hyfv : ~ In y (fv u)).
      { intro Hin. apply Hy. simpl. right. apply in_or_app. left. exact Hin. }
      assert (HyL : ~ In y L).
      { intro Hin. apply Hy. simpl. right. apply in_or_app. right. exact Hin. }
      unfold open. rewrite <- subst_open_fvar by auto.
      apply H3; auto.
      eapply simple_substitution_context_extend; eauto.
  - eapply Simple_Protect; eauto.
Qed.

Lemma simple_subst_one : forall Gamma x U t T u,
  simple_type (update Gamma x U) t T ->
  simple_type Gamma u U -> value u ->
  simple_type Gamma (subst x u t) T.
Proof.
  intros Gamma x U t T u Ht Hu Hv.
  eapply simple_subst; eauto using value_lc.
  unfold simple_substitution_context.
  intros z V Hlookup. simpl in Hlookup.
  destruct (Nat.eqb x z) eqn:E.
  - rewrite Nat.eqb_sym in Hlookup. rewrite E in Hlookup.
    inversion Hlookup; subst. exact Hu.
  - rewrite Nat.eqb_sym in Hlookup. rewrite E in Hlookup. exact Hlookup.
Qed.

Lemma simple_subst_one_lc : forall Gamma x U t T u,
  simple_type (update Gamma x U) t T ->
  simple_type Gamma u U -> locally_closed u ->
  simple_type Gamma (subst x u t) T.
Proof.
  intros Gamma x U t T u Ht Hu Hlc.
  eapply simple_subst; eauto.
  unfold simple_substitution_context.
  intros z V Hlookup. simpl in Hlookup.
  destruct (Nat.eqb x z) eqn:E.
  - rewrite Nat.eqb_sym in Hlookup. rewrite E in Hlookup.
    inversion Hlookup; subst. exact Hu.
  - rewrite Nat.eqb_sym in Hlookup. rewrite E in Hlookup. exact Hlookup.
Qed.

Lemma subst_open_fresh : forall t k x u,
  ~ In x (fv t) ->
  subst x u (open_rec k (tm_fvar x) t) = open_rec k u t.
Proof.
  induction t; intros k x u Hfresh; simpl in *;
    try (rewrite IHt by exact Hfresh; reflexivity).
  - destruct (Nat.eqb k n); simpl; auto.
    rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb x a) eqn:E; auto.
    apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl; auto.
  - reflexivity.
  - assert (H1 : ~ In x (fv t1))
      by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv t2))
      by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
  - assert (H1 : ~ In x (fv t1))
      by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv t2))
      by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In x (fv t1)) by tauto.
    assert (H2 : ~ In x (fv t2)) by tauto.
    assert (H3 : ~ In x (fv t3)) by tauto.
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2.
    rewrite IHt3 by exact H3. reflexivity.
Qed.

Lemma lc_at_erase : forall t k,
  lc_at k t -> lc_at k (erase_security t).
Proof.
  induction t; intros k H; simpl in *;
    repeat match goal with
    | Hc : _ /\ _ |- _ => destruct Hc
    | |- _ /\ _ => split
    end;
    try exact I; try assumption;
    try (eapply IHt; eauto);
    try (eapply IHt1; eauto);
    try (eapply IHt2; eauto);
    try (eapply IHt3; eauto).
Qed.

Lemma value_erase : forall v,
  value v -> value (erase_security v).
Proof.
  intros v H; induction H; simpl; constructor; auto.
  unfold locally_closed in *; simpl in *.
  apply lc_at_erase. exact H.
Qed.

Lemma erase_protect_value : forall v l,
  value v ->
  erase_security (protect_value v l) = erase_security v.
Proof.
  intros v l H; inversion H; subst; simpl; reflexivity.
Qed.

Reserved Notation "t '==>' t'" (at level 40).

Inductive simple_step : tm -> tm -> Prop :=
  | SS_AppAbs : forall A body kappa v r,
      value (tm_abs A body kappa) -> value v ->
      tm_app (tm_abs A body kappa) v r ==> open body v
  | SS_App1 : forall f f' a r,
      f ==> f' -> tm_app f a r ==> tm_app f' a r
  | SS_App2 : forall f a a' r,
      value f -> a ==> a' -> tm_app f a r ==> tm_app f a' r
  | SS_Pair1 : forall a a' b kappa,
      a ==> a' -> tm_pair a b kappa ==> tm_pair a' b kappa
  | SS_Pair2 : forall a b b' kappa,
      value a -> b ==> b' -> tm_pair a b kappa ==> tm_pair a b' kappa
  | SS_FstPair : forall a b kappa r,
      value a -> value b ->
      tm_fst (tm_pair a b kappa) r ==> a
  | SS_Fst : forall p p' r,
      p ==> p' -> tm_fst p r ==> tm_fst p' r
  | SS_SndPair : forall a b kappa r,
      value a -> value b ->
      tm_snd (tm_pair a b kappa) r ==> b
  | SS_Snd : forall p p' r,
      p ==> p' -> tm_snd p r ==> tm_snd p' r
  | SS_Inl : forall t t' kappa,
      t ==> t' -> tm_inl t kappa ==> tm_inl t' kappa
  | SS_Inr : forall t t' kappa,
      t ==> t' -> tm_inr t kappa ==> tm_inr t' kappa
  | SS_CaseLeft : forall v kappa b1 b2 r,
      value v -> tm_case (tm_inl v kappa) b1 b2 r ==> open b1 v
  | SS_CaseRight : forall v kappa b1 b2 r,
      value v -> tm_case (tm_inr v kappa) b1 b2 r ==> open b2 v
  | SS_Case : forall t t' b1 b2 r,
      t ==> t' -> tm_case t b1 b2 r ==> tm_case t' b1 b2 r
  | SS_ProtectValue : forall l v,
      value v -> tm_protect l v ==> v
  | SS_Protect : forall l t t',
      t ==> t' -> tm_protect l t ==> tm_protect l t'
where "t '==>' t'" := (simple_step t t').

Lemma simple_preservation : forall Gamma t T t',
  simple_type Gamma t T -> t ==> t' -> simple_type Gamma t' T.
Proof.
  intros Gamma t T t' Hty; revert t'.
  induction Hty; intros t' Hstep; inversion Hstep; subst;
    try solve [eauto using simple_type].
  - inversion Hty1; subst.
    set (x := fresh (L ++ fv body)).
    assert (HxL : ~ In x L).
    { subst x. intro Hin. apply (fresh_not_in (L ++ fv body)).
      apply in_or_app. left; exact Hin. }
    assert (Hxfv : ~ In x (fv body)).
    { subst x. intro Hin. apply (fresh_not_in (L ++ fv body)).
      apply in_or_app. right; exact Hin. }
    specialize (H1 x HxL).
    pose proof (simple_subst_one Gamma x T1 (open body (tm_fvar x)) T2 a
      H1 Hty2 H4) as Hbeta.
    unfold open in *. rewrite subst_open_fresh in Hbeta by exact Hxfv.
    exact Hbeta.
  - inversion Hty; subst. assumption.
  - inversion Hty; subst. assumption.
  - inversion Hty; subst.
    set (x := fresh (L ++ fv body1)).
    assert (HxL : ~ In x L).
    { subst x. intro Hin. apply (fresh_not_in (L ++ fv body1)).
      apply in_or_app. left; exact Hin. }
    assert (Hxfv : ~ In x (fv body1)).
    { subst x. intro Hin. apply (fresh_not_in (L ++ fv body1)).
      apply in_or_app. right; exact Hin. }
    specialize (H x HxL).
    pose proof (simple_subst_one Gamma x T1 (open body1 (tm_fvar x)) T v
      H H5 H8) as Hbeta.
    unfold open in *. rewrite subst_open_fresh in Hbeta by exact Hxfv.
    exact Hbeta.
  - inversion Hty; subst.
    set (x := fresh (L ++ fv body2)).
    assert (HxL : ~ In x L).
    { subst x. intro Hin. apply (fresh_not_in (L ++ fv body2)).
      apply in_or_app. left; exact Hin. }
    assert (Hxfv : ~ In x (fv body2)).
    { subst x. intro Hin. apply (fresh_not_in (L ++ fv body2)).
      apply in_or_app. right; exact Hin. }
    specialize (H1 x HxL).
    pose proof (simple_subst_one Gamma x T2 (open body2 (tm_fvar x)) T v
      H1 H5 H8) as Hbeta.
    unfold open in *. rewrite subst_open_fresh in Hbeta by exact Hxfv.
    exact Hbeta.
Qed.

Lemma erase_step_simulation : forall t t',
  step t t' ->
  erase_security t = erase_security t' \/
  simple_step (erase_security t) (erase_security t').
Proof.
  intros t t' Hstep; induction Hstep; simpl.
  - right. rewrite erase_security_open.
    apply SS_AppAbs.
    + pose proof (value_erase _ H) as Hv. simpl in Hv. exact Hv.
    + apply value_erase. exact H0.
  - destruct IHHstep as [E|S].
    + left. rewrite E. reflexivity.
    + right. apply SS_App1. exact S.
  - destruct IHHstep as [E|S].
    + left. rewrite E. reflexivity.
    + right. apply SS_App2; auto using value_erase.
  - destruct IHHstep as [E|S].
    + left. rewrite E. reflexivity.
    + right. apply SS_Pair1. exact S.
  - destruct IHHstep as [E|S].
    + left. rewrite E. reflexivity.
    + right. apply SS_Pair2; auto using value_erase.
  - right. apply SS_FstPair; auto using value_erase.
  - destruct IHHstep as [E|S].
    + left. rewrite E. reflexivity.
    + right. apply SS_Fst. exact S.
  - right. apply SS_SndPair; auto using value_erase.
  - destruct IHHstep as [E|S].
    + left. rewrite E. reflexivity.
    + right. apply SS_Snd. exact S.
  - destruct IHHstep as [E|S].
    + left. rewrite E. reflexivity.
    + right. apply SS_Inl. exact S.
  - destruct IHHstep as [E|S].
    + left. rewrite E. reflexivity.
    + right. apply SS_Inr. exact S.
  - right. rewrite erase_security_open.
    apply SS_CaseLeft; auto using value_erase.
  - right. rewrite erase_security_open.
    apply SS_CaseRight; auto using value_erase.
  - destruct IHHstep as [E|S].
    + left. rewrite E. reflexivity.
    + right. apply SS_Case. exact S.
  - left. symmetry. apply erase_protect_value. assumption.
  - exact IHHstep.
Qed.

Lemma simple_preservation_multi : forall t v Gamma T,
  multi t v -> simple_type Gamma (erase_security t) T ->
  simple_type Gamma (erase_security v) T.
Proof.
  intros t v Gamma T Hmulti; induction Hmulti; intros Hty.
  - exact Hty.
  - apply IHHmulti.
    destruct (erase_step_simulation _ _ H) as [E|S].
    + rewrite <- E. exact Hty.
    + eapply simple_preservation; eauto.
Qed.

Lemma simple_to_erased_typing : forall Gamma t T,
  simple_type Gamma t T ->
  has_type (erase_context Gamma) (erase_security t) (erase_type T).
Proof.
  intros Gamma t T H; induction H; simpl.
  - apply T_Var; auto using erase_context_lookup, wf_erase_type.
  - apply T_Unit. simpl. exact I.
  - eapply T_Abs with (L := L).
    + apply wf_erase_type.
    + simpl. exact I.
    + intros x Hx. specialize (H0 x Hx).
      rewrite erase_context_update in H0.
      rewrite erase_security_open in H0. simpl in H0. exact H0.
  - rewrite <- protect_low_erase_type.
    eapply T_App with (kappa := public); simpl; eauto.
  - eapply T_Pair; eauto. simpl. exact I.
  - rewrite <- protect_low_erase_type.
    eapply T_Fst with (kappa := public); simpl; eauto.
  - rewrite <- protect_low_erase_type.
    eapply T_Snd with (kappa := public); simpl; eauto.
  - eapply T_Inl; eauto using wf_erase_type. simpl. exact I.
  - eapply T_Inr; eauto using wf_erase_type. simpl. exact I.
  - rewrite <- protect_low_erase_type.
    eapply T_Case with (L := L) (kappa := public); simpl; eauto.
    + intros x Hx. specialize (H1 x Hx).
      rewrite erase_security_open in H1. simpl in H1. exact H1.
    + intros x Hx. specialize (H3 x Hx).
      rewrite erase_security_open in H3. simpl in H3. exact H3.
  - exact IHsimple_type.
Qed.

Lemma erase_security_idempotent : forall t,
  erase_security (erase_security t) = erase_security t.
Proof.
  induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try rewrite erase_type_idempotent; reflexivity.
Qed.

Lemma evaluated_underlying_typed : forall t v T,
  has_type empty t T -> evaluates t v -> underlying_typed T v.
Proof.
  intros t v T Hty [Hmulti Hv]. unfold underlying_typed.
  pose proof (erasure_simple_type _ _ _ Hty) as Hsimple.
  pose proof (simple_preservation_multi _ _ _ _ Hmulti Hsimple) as Hvty.
  pose proof (simple_to_erased_typing _ _ _ Hvty) as Htarget.
  simpl in Htarget. rewrite erase_security_idempotent in Htarget.
  rewrite erase_type_idempotent in Htarget. exact Htarget.
Qed.

Lemma erase_security_subst : forall t x u,
  erase_security (subst x u t) =
  subst x (erase_security u) (erase_security t).
Proof.
  induction t; intros x u; simpl;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity).
  destruct (Nat.eqb x a); reflexivity.
Qed.

Lemma fv_erase_security : forall t,
  fv (erase_security t) = fv t.
Proof.
  induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    reflexivity.
Qed.

Lemma underlying_typed_closed : forall T v,
  underlying_typed T v -> fv v = [].
Proof.
  intros T v H. unfold underlying_typed in H.
  destruct (fv v) as [|x xs] eqn:E; auto.
  pose proof (typing_fv _ _ _ x H) as Hfv.
  rewrite fv_erase_security in Hfv. rewrite E in Hfv.
  specialize (Hfv (or_introl eq_refl)).
  destruct Hfv as [U HU]. discriminate.
Qed.

Lemma value_relation_closed : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  fv v1 = [] /\ fv v2 = [].
Proof.
  intros observer T v1 v2 H.
  destruct T; simpl in H;
    destruct H as [_ [_ [H1 [H2 _]]]];
    split; eapply underlying_typed_closed; eauto.
Qed.

Fixpoint instantiate (Gamma : context) (rho : atom -> tm) (t : tm) : tm :=
  match Gamma with
  | [] => t
  | (x, _) :: Gamma' => instantiate Gamma' rho (subst x (rho x) t)
  end.

Lemma erase_instantiate : forall Gamma rho t,
  erase_security (instantiate Gamma rho t) =
  instantiate Gamma (fun x => erase_security (rho x)) (erase_security t).
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho t; simpl; auto.
  rewrite IH. rewrite erase_security_subst. reflexivity.
Qed.

Definition environment_related (observer : label) (Gamma : context)
  (rho1 rho2 : atom -> tm) : Prop :=
  forall x T, In (x, T) Gamma ->
    expression_relation observer T (rho1 x) (rho2 x).

Lemma value_relation_left_typed : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  value v1 /\ underlying_typed T v1.
Proof.
  intros observer T v1 v2 H; destruct T; simpl in H; tauto.
Qed.

Lemma instantiate_simple_typed : forall observer Gamma rho1 rho2 s T,
  environment_related observer Gamma rho1 rho2 ->
  simple_type (erase_context Gamma) s (erase_type T) ->
  simple_type empty
    (instantiate Gamma (fun x => erase_security (rho1 x)) s)
    (erase_type T).
Proof.
  intros observer Gamma; induction Gamma as [|[x U] Gamma IH];
    intros rho1 rho2 s T Henv Hty; simpl in *.
  - exact Hty.
  - assert (Hrel : expression_relation observer U (rho1 x) (rho2 x)).
    { apply Henv. left. reflexivity. }
    destruct Hrel as [Hunder [_ _]].
    assert (Harg : simple_type (erase_context Gamma)
                      (erase_security (rho1 x)) (erase_type U)).
    { pose proof (erasure_simple_type _ _ _ Hunder) as Hsimple.
      simpl in Hsimple. rewrite erase_security_idempotent in Hsimple.
      rewrite erase_type_idempotent in Hsimple.
      eapply simple_context_invariance; eauto.
      intros z Hz. rewrite fv_erase_security in Hz.
      pose proof (underlying_typed_closed _ _ Hunder) as Hclosed.
      rewrite Hclosed in Hz. contradiction. }
    apply IH with (rho2 := rho2).
    + intros y V Hin. apply Henv. right. exact Hin.
    + eapply simple_subst_one_lc; eauto.
      unfold underlying_typed in Hunder.
      pose proof (typing_lc _ _ _ Hunder) as Hlc.
      unfold locally_closed in *. eapply lc_at_erase; eauto.
Qed.

Lemma instantiated_underlying_typed : forall observer Gamma rho1 rho2 t T,
  has_type Gamma t T ->
  environment_related observer Gamma rho1 rho2 ->
  underlying_typed T (instantiate Gamma rho1 t).
Proof.
  intros observer Gamma rho1 rho2 t T Hty Henv.
  unfold underlying_typed.
  pose proof (erasure_simple_type _ _ _ Hty) as Hsimple.
  pose proof (instantiate_simple_typed _ _ _ _ _ _ Henv Hsimple) as Hclosed.
  rewrite <- erase_instantiate in Hclosed.
  pose proof (simple_to_erased_typing _ _ _ Hclosed) as Hresult.
  simpl in Hresult. rewrite erase_security_idempotent in Hresult.
  rewrite erase_type_idempotent in Hresult. exact Hresult.
Qed.

Lemma subst_notin_fv : forall t x u,
  ~ In x (fv t) -> subst x u t = t.
Proof.
  induction t; intros x u H; simpl in *;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; auto;
         try (intro Hin; apply H; repeat rewrite in_app_iff; tauto);
         reflexivity).
  - destruct (Nat.eqb x a) eqn:E; auto.
    apply Nat.eqb_eq in E. subst. exfalso. apply H. simpl; auto.
Qed.

Lemma subst_open_closed : forall t k x u arg,
  locally_closed u -> fv arg = [] ->
  subst x u (open_rec k arg t) =
  open_rec k arg (subst x u t).
Proof.
  induction t; intros k x u arg Hu Harg; simpl;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; auto; reflexivity).
  - destruct (Nat.eqb k n); simpl; auto.
    apply subst_notin_fv. rewrite Harg. auto.
  - destruct (Nat.eqb x a); simpl; auto.
    symmetry. apply lc_open_rec_id.
    eapply lc_at_weaken; eauto. lia.
Qed.

Lemma instantiate_open_closed : forall Gamma rho body arg,
  (forall x, In x (map fst Gamma) -> locally_closed (rho x)) ->
  fv arg = [] ->
  instantiate Gamma rho (open body arg) =
  open (instantiate Gamma rho body) arg.
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho body arg Hlc Harg;
    simpl; auto.
  unfold open in *. rewrite subst_open_closed by (auto; apply Hlc; simpl; auto).
  apply IH; auto. intros y Hy. apply Hlc. simpl; auto.
Qed.

Lemma instantiate_extensional : forall Gamma rho sigma t,
  (forall x, In x (map fst Gamma) -> rho x = sigma x) ->
  instantiate Gamma rho t = instantiate Gamma sigma t.
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho sigma t Heq;
    simpl; auto.
  rewrite (Heq x) by (simpl; auto).
  apply IH. intros y Hy. apply Heq. simpl; auto.
Qed.

Lemma instantiate_abs : forall Gamma rho A body kappa,
  instantiate Gamma rho (tm_abs A body kappa) =
  tm_abs A (instantiate Gamma rho body) kappa.
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho A body kappa;
    simpl; auto.
Qed.

Lemma instantiate_app : forall Gamma rho f a r,
  instantiate Gamma rho (tm_app f a r) =
  tm_app (instantiate Gamma rho f) (instantiate Gamma rho a) r.
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho f a r;
    simpl; auto.
Qed.

Lemma instantiate_pair : forall Gamma rho a b kappa,
  instantiate Gamma rho (tm_pair a b kappa) =
  tm_pair (instantiate Gamma rho a) (instantiate Gamma rho b) kappa.
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho a b kappa;
    simpl; auto.
Qed.

Lemma instantiate_fst : forall Gamma rho p r,
  instantiate Gamma rho (tm_fst p r) =
  tm_fst (instantiate Gamma rho p) r.
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho p r;
    simpl; auto.
Qed.

Lemma instantiate_snd : forall Gamma rho p r,
  instantiate Gamma rho (tm_snd p r) =
  tm_snd (instantiate Gamma rho p) r.
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho p r;
    simpl; auto.
Qed.

Lemma instantiate_inl : forall Gamma rho p kappa,
  instantiate Gamma rho (tm_inl p kappa) =
  tm_inl (instantiate Gamma rho p) kappa.
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho p kappa;
    simpl; auto.
Qed.

Lemma instantiate_inr : forall Gamma rho p kappa,
  instantiate Gamma rho (tm_inr p kappa) =
  tm_inr (instantiate Gamma rho p) kappa.
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho p kappa;
    simpl; auto.
Qed.

Lemma instantiate_case : forall Gamma rho t b1 b2 r,
  instantiate Gamma rho (tm_case t b1 b2 r) =
  tm_case (instantiate Gamma rho t) (instantiate Gamma rho b1)
    (instantiate Gamma rho b2) r.
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho t b1 b2 r;
    simpl; auto.
Qed.

Lemma instantiate_protect : forall Gamma rho l t,
  instantiate Gamma rho (tm_protect l t) =
  tm_protect l (instantiate Gamma rho t).
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho l t;
    simpl; auto.
Qed.

Lemma in_map_fst_context : forall (Gamma : context) (x : atom),
  In x (map fst Gamma) -> exists T, In (x, T) Gamma.
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x H; simpl in H.
  - contradiction.
  - destruct H as [<-|H].
    + exists U. left. reflexivity.
    + destruct (IH _ H) as [T HT]. exists T. right. exact HT.
Qed.

Lemma environment_values_lc : forall observer Gamma rho1 rho2,
  environment_related observer Gamma rho1 rho2 ->
  forall x, In x (map fst Gamma) -> locally_closed (rho1 x).
Proof.
  intros observer Gamma rho1 rho2 Henv x Hin.
  destruct (in_map_fst_context _ _ Hin) as [T HT].
  destruct (Henv _ _ HT) as [Hunder _].
  eapply underlying_typed_lc; eauto.
Qed.

Definition env_extend (rho : atom -> tm) (y : atom) (v : tm) : atom -> tm :=
  fun x => if Nat.eqb x y then v else rho x.

Lemma instantiate_open_body : forall Gamma rho y U body arg,
  ~ In y (fv body) -> ~ In y (map fst Gamma) ->
  (forall x, In x (map fst Gamma) -> locally_closed (rho x)) ->
  fv arg = [] ->
  instantiate (update Gamma y U) (env_extend rho y arg)
    (open body (tm_fvar y)) =
  open (instantiate Gamma rho body) arg.
Proof.
  intros Gamma rho y U body arg Hybody Hydom Hlc Harg.
  simpl.
  replace (env_extend rho y arg y) with arg
    by (unfold env_extend; rewrite Nat.eqb_refl; reflexivity).
  unfold open at 1. rewrite subst_open_fresh by exact Hybody.
  fold (open body arg).
  rewrite (instantiate_extensional Gamma (env_extend rho y arg) rho).
  - apply instantiate_open_closed; auto.
  - intros x Hin. unfold env_extend.
    destruct (Nat.eqb x y) eqn:E; auto.
    apply Nat.eqb_eq in E. subst. contradiction.
Qed.

Lemma environment_related_extend : forall observer Gamma rho1 rho2 y U v1 v2,
  ~ In y (map fst Gamma) ->
  environment_related observer Gamma rho1 rho2 ->
  value_relation observer U v1 v2 ->
  environment_related observer (update Gamma y U)
    (env_extend rho1 y v1) (env_extend rho2 y v2).
Proof.
  intros observer Gamma rho1 rho2 y U v1 v2 Hy Henv Hv x T Hin.
  simpl in Hin. destruct Hin as [Hhead|Htail].
  - inversion Hhead; subst. unfold env_extend.
    rewrite Nat.eqb_refl. apply value_relation_expression. exact Hv.
  - assert (Hxy : x <> y).
    { intro E. subst x. apply Hy.
      apply (in_map fst) in Htail. simpl in Htail. exact Htail. }
    unfold env_extend. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + apply Henv. exact Htail.
Qed.

Lemma protect_value_is_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l H; inversion H; subst; simpl; constructor; auto.
Qed.

Inductive big_eval : tm -> tm -> Prop :=
  | BE_Value : forall v, value v -> big_eval v v
  | BE_App : forall f a A body kappa va w r,
      big_eval f (tm_abs A body kappa) ->
      big_eval a va -> flows_to kappa.(reader) r ->
      big_eval (open body va) w ->
      big_eval (tm_app f a r) (protect_value w kappa.(indirect_reader))
  | BE_Pair : forall a b va vb kappa,
      big_eval a va -> big_eval b vb ->
      big_eval (tm_pair a b kappa) (tm_pair va vb kappa)
  | BE_Fst : forall p va vb kappa r,
      big_eval p (tm_pair va vb kappa) ->
      flows_to kappa.(reader) r ->
      big_eval (tm_fst p r) (protect_value va kappa.(indirect_reader))
  | BE_Snd : forall p va vb kappa r,
      big_eval p (tm_pair va vb kappa) ->
      flows_to kappa.(reader) r ->
      big_eval (tm_snd p r) (protect_value vb kappa.(indirect_reader))
  | BE_Inl : forall t v kappa,
      big_eval t v -> big_eval (tm_inl t kappa) (tm_inl v kappa)
  | BE_Inr : forall t v kappa,
      big_eval t v -> big_eval (tm_inr t kappa) (tm_inr v kappa)
  | BE_CaseLeft : forall t b1 b2 v kappa w r,
      big_eval t (tm_inl v kappa) -> flows_to kappa.(reader) r ->
      big_eval (open b1 v) w ->
      big_eval (tm_case t b1 b2 r)
        (protect_value w kappa.(indirect_reader))
  | BE_CaseRight : forall t b1 b2 v kappa w r,
      big_eval t (tm_inr v kappa) -> flows_to kappa.(reader) r ->
      big_eval (open b2 v) w ->
      big_eval (tm_case t b1 b2 r)
        (protect_value w kappa.(indirect_reader))
  | BE_Protect : forall l t v,
      big_eval t v -> big_eval (tm_protect l t) (protect_value v l).

Lemma big_eval_result_value : forall t v,
  big_eval t v -> value v.
Proof.
  intros t v H; induction H;
    eauto using v_pair, v_inl, v_inr, protect_value_is_value.
  - inversion IHbig_eval; subst. apply protect_value_is_value; auto.
  - inversion IHbig_eval; subst. apply protect_value_is_value; auto.
Qed.

Lemma big_eval_value_inv : forall t v,
  value t -> big_eval t v -> v = t.
Proof.
  intros t v Hv He; revert Hv.
  induction He; intros Hv; auto;
    try (inversion Hv; subst; try (specialize (IHHe1 H2));
         try (specialize (IHHe H1)); subst; reflexivity).
  - inversion Hv; subst.
    specialize (IHHe1 H1). specialize (IHHe2 H3).
    subst. reflexivity.
  - inversion Hv; subst.
    specialize (IHHe H0). subst. reflexivity.
  - inversion Hv; subst.
    specialize (IHHe H0). subst. reflexivity.
Qed.

Lemma big_eval_pair_inv : forall a b kappa v,
  big_eval (tm_pair a b kappa) v ->
  exists va vb, v = tm_pair va vb kappa /\
    big_eval a va /\ big_eval b vb.
Proof.
  intros a b kappa v H; inversion H; subst.
  - inversion H0; subst.
    exists a, b. repeat split; auto using BE_Value.
  - eauto.
Qed.

Lemma big_eval_inl_inv : forall t kappa v,
  big_eval (tm_inl t kappa) v ->
  exists u, v = tm_inl u kappa /\ big_eval t u.
Proof.
  intros t kappa v H; inversion H; subst.
  - inversion H0; subst. exists t. split; auto using BE_Value.
  - eauto.
Qed.

Lemma big_eval_inr_inv : forall t kappa v,
  big_eval (tm_inr t kappa) v ->
  exists u, v = tm_inr u kappa /\ big_eval t u.
Proof.
  intros t kappa v H; inversion H; subst.
  - inversion H0; subst. exists t. split; auto using BE_Value.
  - eauto.
Qed.

Lemma big_eval_protect_inv : forall l t v,
  big_eval (tm_protect l t) v ->
  exists u, big_eval t u /\ v = protect_value u l.
Proof.
  intros l t v H; inversion H; subst; eauto.
  inversion H0.
Qed.

Lemma big_eval_step_back : forall t t' v,
  step t t' -> big_eval t' v -> big_eval t v.
Proof.
  intros t t' v Hstep; revert v.
  induction Hstep; intros w He.
  - destruct (big_eval_protect_inv _ _ _ He) as [z [Hz ->]].
    eapply BE_App; eauto using BE_Value.
  - inversion He; subst;
      try (match goal with Hv : value (tm_app _ _ _) |- _ => inversion Hv end).
    eapply BE_App; eauto.
  - inversion He; subst;
      try (match goal with Hv : value (tm_app _ _ _) |- _ => inversion Hv end).
    eapply BE_App; eauto.
  - destruct (big_eval_pair_inv _ _ _ _ He) as [a [b [-> [Ha Hb]]]].
    eapply BE_Pair; eauto.
  - destruct (big_eval_pair_inv _ _ _ _ He) as [a [b [-> [Ha Hb]]]].
    eapply BE_Pair; eauto.
  - destruct (big_eval_protect_inv _ _ _ He) as [z [Hz ->]].
    pose proof (big_eval_value_inv _ _ H Hz) as Ez. subst z.
    eapply BE_Fst; eauto using BE_Value, v_pair.
  - inversion He; subst;
      try (match goal with Hv : value (tm_fst _ _) |- _ => inversion Hv end).
    eapply BE_Fst; eauto.
  - destruct (big_eval_protect_inv _ _ _ He) as [z [Hz ->]].
    pose proof (big_eval_value_inv _ _ H0 Hz) as Ez. subst z.
    eapply BE_Snd; eauto using BE_Value, v_pair.
  - inversion He; subst;
      try (match goal with Hv : value (tm_snd _ _) |- _ => inversion Hv end).
    eapply BE_Snd; eauto.
  - destruct (big_eval_inl_inv _ _ _ He) as [u [-> Hu]].
    apply BE_Inl. eauto.
  - destruct (big_eval_inr_inv _ _ _ He) as [u [-> Hu]].
    apply BE_Inr. eauto.
  - destruct (big_eval_protect_inv _ _ _ He) as [z [Hz ->]].
    eapply BE_CaseLeft; eauto using BE_Value, v_inl.
  - destruct (big_eval_protect_inv _ _ _ He) as [z [Hz ->]].
    eapply BE_CaseRight; eauto using BE_Value, v_inr.
  - inversion He; subst;
      try (match goal with Hv : value (tm_case _ _ _ _) |- _ => inversion Hv end).
    + eapply BE_CaseLeft; eauto.
    + eapply BE_CaseRight; eauto.
  - pose proof (protect_value_is_value v l H) as Hv.
    pose proof (big_eval_value_inv _ _ Hv He) as E. subst w.
    apply BE_Protect. apply BE_Value. exact H.
  - destruct (big_eval_protect_inv _ _ _ He) as [z [Hz ->]].
    apply BE_Protect. eauto.
Qed.

Lemma evaluates_big_eval : forall t v,
  evaluates t v -> big_eval t v.
Proof.
  intros t v [Hmulti Hv]; induction Hmulti.
  - apply BE_Value. exact Hv.
  - eapply big_eval_step_back; eauto.
Qed.

Lemma multi_trans : forall a b c,
  multi a b -> multi b c -> multi a c.
Proof.
  intros a b c H; induction H; intros Hbc; auto.
  eapply multi_step; eauto.
Qed.

Lemma multi_one : forall a b, step a b -> multi a b.
Proof. intros a b H; eapply multi_step; eauto using multi_refl. Qed.

Lemma multi_app_left : forall f f' a r,
  multi f f' -> multi (tm_app f a r) (tm_app f' a r).
Proof.
  intros f f' a r H; induction H; eauto using multi_refl, multi_step, ST_App1.
Qed.

Lemma multi_app_right : forall f a a' r,
  value f -> multi a a' -> multi (tm_app f a r) (tm_app f a' r).
Proof.
  intros f a a' r Hv H; induction H;
    eauto using multi_refl, multi_step, ST_App2.
Qed.

Lemma multi_pair_left : forall a a' b kappa,
  multi a a' -> multi (tm_pair a b kappa) (tm_pair a' b kappa).
Proof.
  intros a a' b kappa H; induction H;
    eauto using multi_refl, multi_step, ST_Pair1.
Qed.

Lemma multi_pair_right : forall a b b' kappa,
  value a -> multi b b' ->
  multi (tm_pair a b kappa) (tm_pair a b' kappa).
Proof.
  intros a b b' kappa Hv H; induction H;
    eauto using multi_refl, multi_step, ST_Pair2.
Qed.

Lemma multi_fst : forall p p' r,
  multi p p' -> multi (tm_fst p r) (tm_fst p' r).
Proof.
  intros p p' r H; induction H;
    eauto using multi_refl, multi_step, ST_Fst.
Qed.

Lemma multi_snd : forall p p' r,
  multi p p' -> multi (tm_snd p r) (tm_snd p' r).
Proof.
  intros p p' r H; induction H;
    eauto using multi_refl, multi_step, ST_Snd.
Qed.

Lemma multi_inl : forall t t' kappa,
  multi t t' -> multi (tm_inl t kappa) (tm_inl t' kappa).
Proof.
  intros t t' kappa H; induction H;
    eauto using multi_refl, multi_step, ST_Inl.
Qed.

Lemma multi_inr : forall t t' kappa,
  multi t t' -> multi (tm_inr t kappa) (tm_inr t' kappa).
Proof.
  intros t t' kappa H; induction H;
    eauto using multi_refl, multi_step, ST_Inr.
Qed.

Lemma multi_case : forall t t' b1 b2 r,
  multi t t' -> multi (tm_case t b1 b2 r) (tm_case t' b1 b2 r).
Proof.
  intros t t' b1 b2 r H; induction H;
    eauto using multi_refl, multi_step, ST_Case.
Qed.

Lemma multi_protect : forall l t t',
  multi t t' -> multi (tm_protect l t) (tm_protect l t').
Proof.
  intros l t t' H; induction H;
    eauto using multi_refl, multi_step, ST_Protect.
Qed.

Lemma big_eval_evaluates : forall t v,
  big_eval t v -> evaluates t v.
Proof.
  intros t v H; induction H.
  - split; auto using multi_refl.
  - destruct IHbig_eval1 as [Hf Hvf].
    destruct IHbig_eval2 as [Ha Hva].
    destruct IHbig_eval3 as [Hb Hvb].
    split.
    + eapply multi_trans. apply multi_app_left. exact Hf.
      eapply multi_trans. apply multi_app_right; eauto.
      eapply multi_trans.
      * apply multi_one. eapply ST_AppAbs; eauto.
      * eapply multi_trans. apply multi_protect. exact Hb.
        apply multi_one. apply ST_ProtectValue. exact Hvb.
    + apply protect_value_is_value. exact Hvb.
  - destruct IHbig_eval1 as [Ha Hva].
    destruct IHbig_eval2 as [Hb Hvb]. split.
    + eapply multi_trans. apply multi_pair_left. exact Ha.
      apply multi_pair_right; auto.
    + constructor; auto.
  - destruct IHbig_eval as [Hp Hvp].
    inversion Hvp; subst. split.
    + eapply multi_trans. apply multi_fst. exact Hp.
      eapply multi_trans.
      * apply multi_one. eapply ST_FstPair; eauto.
      * apply multi_one. apply ST_ProtectValue. assumption.
    + apply protect_value_is_value. assumption.
  - destruct IHbig_eval as [Hp Hvp].
    inversion Hvp; subst. split.
    + eapply multi_trans. apply multi_snd. exact Hp.
      eapply multi_trans.
      * apply multi_one. eapply ST_SndPair; eauto.
      * apply multi_one. apply ST_ProtectValue. assumption.
    + apply protect_value_is_value. assumption.
  - destruct IHbig_eval as [Ht Hvt]. split.
    + apply multi_inl. exact Ht.
    + constructor. exact Hvt.
  - destruct IHbig_eval as [Ht Hvt]. split.
    + apply multi_inr. exact Ht.
    + constructor. exact Hvt.
  - destruct IHbig_eval1 as [Ht Hvt].
    destruct IHbig_eval2 as [Hb Hvb].
    inversion Hvt; subst. split.
    + eapply multi_trans. apply multi_case. exact Ht.
      eapply multi_trans.
      * apply multi_one. eapply ST_CaseLeft; eauto.
      * eapply multi_trans. apply multi_protect. exact Hb.
        apply multi_one. apply ST_ProtectValue. exact Hvb.
    + apply protect_value_is_value. exact Hvb.
  - destruct IHbig_eval1 as [Ht Hvt].
    destruct IHbig_eval2 as [Hb Hvb].
    inversion Hvt; subst. split.
    + eapply multi_trans. apply multi_case. exact Ht.
      eapply multi_trans.
      * apply multi_one. eapply ST_CaseRight; eauto.
      * eapply multi_trans. apply multi_protect. exact Hb.
        apply multi_one. apply ST_ProtectValue. exact Hvb.
    + apply protect_value_is_value. exact Hvb.
  - destruct IHbig_eval as [Ht Hvt]. split.
    + eapply multi_trans. apply multi_protect. exact Ht.
      apply multi_one. apply ST_ProtectValue. exact Hvt.
    + apply protect_value_is_value. exact Hvt.
Qed.

Lemma underlying_typed_erase_cast : forall T U v,
  erase_type T = erase_type U ->
  underlying_typed T v -> underlying_typed U v.
Proof.
  intros T U v E H. unfold underlying_typed in *. rewrite <- E. exact H.
Qed.

Lemma subtype_security_le : forall T U,
  subtype T U -> security_le (security_of T) (security_of U).
Proof.
  intros T U H; induction H; simpl in *; auto.
  destruct IHsubtype1 as [Hr1 Hi1].
  destruct IHsubtype2 as [Hr2 Hi2].
  split; eapply flows_to_trans; eauto.
Qed.

Lemma value_relation_subtype : forall observer T U v1 v2,
  subtype T U -> value_relation observer T v1 v2 ->
  value_relation observer U v1 v2.
Proof.
  intros observer T U v1 v2 Hsub; revert v1 v2.
  induction Hsub; intros v1 v2 Hrel; simpl in *.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; auto.
    intros Hvisible. apply Hshape.
    eapply flows_to_trans; [exact (proj2 H1)|exact Hvisible].
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    split; [exact Hv1|]. split; [exact Hv2|].
    split.
    { eapply underlying_typed_erase_cast; [|exact Ht1].
      simpl. f_equal; eapply subtype_erase_eq; eauto. }
    split.
    { eapply underlying_typed_erase_cast; [|exact Ht2].
      simpl. f_equal; eapply subtype_erase_eq; eauto. }
    intros Hvisible.
    specialize (Hshape (flows_to_trans _ _ _ (proj2 H1) Hvisible)).
    destruct Hshape as [[a1 [a2 [k1 [k2 [-> [-> Hr]]]]]]|
                       [a1 [a2 [k1 [k2 [-> [-> Hr]]]]]]].
    + left. exists a1, a2, k1, k2. repeat split; eauto.
    + right. exists a1, a2, k1, k2. repeat split; eauto.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    split; [exact Hv1|]. split; [exact Hv2|].
    split.
    { eapply underlying_typed_erase_cast; [|exact Ht1].
      simpl. f_equal; eapply subtype_erase_eq; eauto. }
    split.
    { eapply underlying_typed_erase_cast; [|exact Ht2].
      simpl. f_equal; eapply subtype_erase_eq; eauto. }
    intros Hvisible.
    specialize (Hshape (flows_to_trans _ _ _ (proj2 H1) Hvisible)).
    destruct Hshape as [a1 [b1 [a2 [b2 [k1 [k2
      [-> [-> [Ha Hb]]]]]]]]].
    exists a1, b1, a2, b2, k1, k2.
    repeat split; eauto.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    split; [exact Hv1|]. split; [exact Hv2|].
    split.
    { eapply underlying_typed_erase_cast; [|exact Ht1].
      simpl. f_equal.
      - symmetry. eapply subtype_erase_eq; eauto.
      - eapply subtype_erase_eq; eauto. }
    split.
    { eapply underlying_typed_erase_cast; [|exact Ht2].
      simpl. f_equal.
      - symmetry. eapply subtype_erase_eq; eauto.
      - eapply subtype_erase_eq; eauto. }
    intros Hvisible.
    specialize (Hshape (flows_to_trans _ _ _ (proj2 H1) Hvisible)).
    destruct Hshape as [A1 [A2 [b1 [b2 [k1 [k2
      [-> [-> Hfun]]]]]]]].
    exists A1, A2, b1, b2, k1, k2.
    repeat split; auto.
    intros arg1 arg2 Harg w1 w2 He1 He2.
    apply IHHsub2.
    eapply Hfun; eauto.
  - apply IHHsub2. apply IHHsub1. exact Hrel.
Qed.

Lemma underlying_typed_evaluation : forall T t v,
  underlying_typed T t -> evaluates t v -> underlying_typed T v.
Proof.
  intros T t v Hty [Hmulti Hv]. unfold underlying_typed in *.
  pose proof (erasure_simple_type _ _ _ Hty) as Hsimple.
  simpl in Hsimple.
  rewrite erase_security_idempotent in Hsimple.
  rewrite erase_type_idempotent in Hsimple.
  pose proof (simple_preservation_multi _ _ _ _ Hmulti Hsimple) as Hresult.
  pose proof (simple_to_erased_typing _ _ _ Hresult) as Hfinal.
  simpl in Hfinal.
  rewrite erase_security_idempotent in Hfinal.
  rewrite erase_type_idempotent in Hfinal. exact Hfinal.
Qed.

Lemma value_relation_intro_low : forall T v1 v2,
  value v1 -> value v2 ->
  underlying_typed T v1 -> underlying_typed T v2 ->
  (flows_to (security_of T).(indirect_reader) Low ->
   match T with
   | Ty_Unit _ => exists k1 k2, v1 = tm_unit k1 /\ v2 = tm_unit k2
   | Ty_Sum A B _ =>
       (exists a b k1 k2, v1 = tm_inl a k1 /\ v2 = tm_inl b k2 /\
          value_relation Low A a b) \/
       (exists a b k1 k2, v1 = tm_inr a k1 /\ v2 = tm_inr b k2 /\
          value_relation Low B a b)
   | Ty_Prod A B _ =>
       exists a1 b1 a2 b2 k1 k2,
         v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
         value_relation Low A a1 a2 /\ value_relation Low B b1 b2
   | Ty_Arrow A B _ =>
       exists A1 A2 b1 b2 k1 k2,
         v1 = tm_abs A1 b1 k1 /\ v2 = tm_abs A2 b2 k2 /\
         forall a1 a2,
           value_relation Low A a1 a2 ->
           expression_lifting (value_relation Low B)
             (tm_app v1 a1 High) (tm_app v2 a2 High)
   end) ->
  value_relation Low T v1 v2.
Proof.
  intros T v1 v2 Hv1 Hv2 Ht1 Ht2 Hshape.
  destruct T; simpl in *; repeat split; auto.
Qed.

Lemma protect_value_low : forall v,
  value v -> protect_value v Low = v.
Proof.
  intros v H; inversion H; subst; simpl;
    try (destruct kappa as [r i]; destruct r, i; reflexivity).
Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof.
  intros [k|A B k|A B k|A B k];
    destruct k as [r i]; destruct r, i; reflexivity.
Qed.

Lemma ty_protect_high_opaque : forall T,
  ~ flows_to (security_of (ty_protect High T)).(indirect_reader) Low.
Proof.
  intros [k|A B k|A B k|A B k];
    destruct k as [r i]; destruct r, i; simpl; tauto.
Qed.

Lemma instantiate_closed_id : forall Gamma rho t,
  fv t = [] -> instantiate Gamma rho t = t.
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho t Hfv; simpl; auto.
  rewrite subst_notin_fv by (rewrite Hfv; auto).
  apply IH. exact Hfv.
Qed.

Lemma lookup_in_context : forall Gamma x T,
  lookup_context x Gamma = Some T -> In (x, T) Gamma.
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      inversion H; subst. left. reflexivity.
    + right. apply IH. exact H.
Qed.

Lemma instantiate_var : forall observer Gamma rho1 rho2 x T,
  lookup_context x Gamma = Some T ->
  environment_related observer Gamma rho1 rho2 ->
  instantiate Gamma rho1 (tm_fvar x) = rho1 x.
Proof.
  intros observer Gamma; induction Gamma as [|[y U] Gamma IH];
    intros rho1 rho2 x T Hlookup Henv; simpl in *.
  - discriminate.
  - destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y.
      assert (Hrel : value_relation observer U (rho1 x) (rho2 x)).
      { apply Henv. left. reflexivity. }
      destruct (value_relation_closed _ _ _ _ Hrel) as [Hclosed _].
      apply instantiate_closed_id. exact Hclosed.
    + apply IH with (rho2 := rho2) (T := T).
      * rewrite Nat.eqb_sym in Hlookup. rewrite E in Hlookup. exact Hlookup.
      * intros z V Hin. apply Henv. right. exact Hin.
Qed.

Lemma evaluates_value_inv : forall v w,
  value v -> evaluates v w -> w = v.
Proof.
  intros v w Hv He. apply big_eval_value_inv with (t := v); auto.
  apply evaluates_big_eval. exact He.
Qed.

Lemma value_relation_fields : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  value v1 /\ value v2 /\
  underlying_typed T v1 /\ underlying_typed T v2.
Proof.
  intros observer T v1 v2 H; destruct T; simpl in H; tauto.
Qed.

Lemma value_relation_expression : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  expression_relation observer T v1 v2.
Proof.
  intros observer T v1 v2 Hrel.
  destruct (value_relation_fields _ _ _ _ Hrel)
    as [Hv1 [Hv2 [Ht1 Ht2]]].
  unfold expression_relation, expression_lifting.
  split; [exact Ht1|]. split; [exact Ht2|].
  intros w1 w2 He1 He2.
  pose proof (evaluates_value_inv _ _ Hv1 He1) as E1.
  pose proof (evaluates_value_inv _ _ Hv2 He2) as E2.
  subst. exact Hrel.
Qed.

Lemma value_relation_symmetric : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  value_relation observer T v2 v1.
Proof.
  intros observer T; induction T; intros v1 v2 Hrel;
    simpl in Hrel |- *;
    destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
  - repeat split; auto. intros Hvisible.
    destruct (Hshape Hvisible) as [k1 [k2 [-> ->]]].
    exists k2, k1. auto.
  - split; [exact Hv2|]. split; [exact Hv1|].
    split; [exact Ht2|]. split; [exact Ht1|].
    intros Hvisible.
    destruct (Hshape Hvisible) as
      [[a1 [a2 [k1 [k2 [-> [-> Hr]]]]]]|
       [a1 [a2 [k1 [k2 [-> [-> Hr]]]]]]].
    + left. exists a2, a1, k2, k1. repeat split; eauto.
    + right. exists a2, a1, k2, k1. repeat split; eauto.
  - split; [exact Hv2|]. split; [exact Hv1|].
    split; [exact Ht2|]. split; [exact Ht1|].
    intros Hvisible.
    destruct (Hshape Hvisible) as [a1 [b1 [a2 [b2 [k1 [k2
      [-> [-> [Ha Hb]]]]]]]]].
    exists a2, b2, a1, b1, k2, k1.
    repeat split; eauto.
  - split; [exact Hv2|]. split; [exact Hv1|].
    split; [exact Ht2|]. split; [exact Ht1|].
    intros Hvisible.
    destruct (Hshape Hvisible) as [A1 [A2 [b1 [b2 [k1 [k2
      [-> [-> Hfun]]]]]]]].
    exists A2, A1, b2, b1, k2, k1.
    repeat split; auto.
    intros a2 a1 Harg w2 w1 He2 He1.
    apply IHT2.
    exact (Hfun a1 a2 (IHT1 _ _ Harg) w1 w2 He1 He2).
Qed.

Lemma environment_related_symmetric : forall observer Gamma rho1 rho2,
  environment_related observer Gamma rho1 rho2 ->
  environment_related observer Gamma rho2 rho1.
Proof.
  intros observer Gamma rho1 rho2 Henv x T Hin.
  apply value_relation_symmetric. apply Henv. exact Hin.
Qed.

Lemma opaque_instantiate_related : forall Gamma t T rho1 rho2,
  has_type Gamma t T ->
  environment_related Low Gamma rho1 rho2 ->
  ~ flows_to (security_of T).(indirect_reader) Low ->
  expression_relation Low T
    (instantiate Gamma rho1 t) (instantiate Gamma rho2 t).
Proof.
  intros Gamma t T rho1 rho2 Hty Henv Hopaque.
  unfold expression_relation, expression_lifting.
  split.
  - eapply instantiated_underlying_typed; eauto.
  - split.
    + eapply instantiated_underlying_typed
        with (rho2 := rho1); eauto using environment_related_symmetric.
    + intros v1 v2 He1 He2.
      apply value_relation_intro_low.
      * exact (proj2 He1).
      * exact (proj2 He2).
      * eapply underlying_typed_evaluation; eauto.
        eapply instantiated_underlying_typed; eauto.
      * eapply underlying_typed_evaluation; eauto.
        eapply instantiated_underlying_typed
          with (rho2 := rho1); eauto using environment_related_symmetric.
      * intro Hvisible. contradiction.
Qed.

Lemma instantiated_underlying_typed_right : forall observer Gamma rho1 rho2 t T,
  has_type Gamma t T ->
  environment_related observer Gamma rho1 rho2 ->
  underlying_typed T (instantiate Gamma rho2 t).
Proof.
  intros observer Gamma rho1 rho2 t T Hty Henv.
  eapply instantiated_underlying_typed with (rho2 := rho1); eauto.
  apply environment_related_symmetric. exact Henv.
Qed.

Lemma instantiate_unit : forall Gamma rho kappa,
  instantiate Gamma rho (tm_unit kappa) = tm_unit kappa.
Proof.
  induction Gamma as [|[x U] Gamma IH]; intros rho kappa;
    simpl; auto.
Qed.

Lemma unit_value_related : forall kappa,
  value_relation Low (Ty_Unit kappa) (tm_unit kappa) (tm_unit kappa).
Proof.
  intros kappa. simpl.
  repeat split; auto using v_unit.
  - unfold underlying_typed. simpl. apply T_Unit. simpl. exact I.
  - unfold underlying_typed. simpl. apply T_Unit. simpl. exact I.
  - intros _. exists kappa, kappa. auto.
Qed.

Lemma big_eval_abs_source_inv : forall A body kappa v,
  big_eval (tm_abs A body kappa) v ->
  v = tm_abs A body kappa.
Proof.
  intros A body kappa v H; inversion H; subst; auto.
Qed.

Lemma big_eval_unit_source_inv : forall kappa v,
  big_eval (tm_unit kappa) v -> v = tm_unit kappa.
Proof.
  intros kappa v H; inversion H; subst; auto.
Qed.

Lemma big_eval_app_abs_inv : forall A body kappa arg r result,
  value arg ->
  big_eval (tm_app (tm_abs A body kappa) arg r) result ->
  exists w, big_eval (open body arg) w /\
    result = protect_value w kappa.(indirect_reader).
Proof.
  intros A body kappa arg r result Harg He.
  inversion He; subst.
  - match goal with Hv : value (tm_app _ _ _) |- _ => inversion Hv end.
  - match goal with
    Hf : big_eval (tm_abs _ _ _) (tm_abs _ _ _) |- _ =>
      pose proof (big_eval_abs_source_inv _ _ _ _ Hf) as Ef
    end.
    inversion Ef; subst.
    match goal with
    Ha : big_eval arg _ |- _ =>
      pose proof (big_eval_value_inv _ _ Harg Ha) as Ea
    end.
    subst. eauto.
Qed.

Lemma instantiated_expression_from_lifting : forall Gamma t T rho1 rho2,
  has_type Gamma t T ->
  environment_related Low Gamma rho1 rho2 ->
  expression_lifting (value_relation Low T)
    (instantiate Gamma rho1 t) (instantiate Gamma rho2 t) ->
  expression_relation Low T
    (instantiate Gamma rho1 t) (instantiate Gamma rho2 t).
Proof.
  intros Gamma t T rho1 rho2 Hty Henv Hlift.
  unfold expression_relation.
  split.
  - eapply instantiated_underlying_typed; eauto.
  - split.
    + eapply instantiated_underlying_typed_right; eauto.
    + exact Hlift.
Qed.

Lemma flows_to_high : forall l, flows_to l High.
Proof. destruct l; exact I. Qed.

Lemma big_eval_app_high : forall f a r v,
  big_eval (tm_app f a r) v ->
  exists vf va, big_eval f vf /\ big_eval a va /\
    big_eval (tm_app vf va High) v.
Proof.
  intros f a r v H; inversion H; subst.
  - match goal with Hv : value (tm_app _ _ _) |- _ => inversion Hv end.
  - exists (tm_abs A body kappa), va.
    repeat split; auto.
    eapply BE_App; eauto using BE_Value, big_eval_result_value, flows_to_high.
Qed.

Lemma protect_value_compose : forall v a b,
  value v ->
  protect_value (protect_value v a) b = protect_value v (join a b).
Proof.
  intros v a b Hv.
  inversion Hv; subst; simpl;
    destruct a, b, kappa as [r i]; destruct r, i; reflexivity.
Qed.

Lemma big_eval_relabelled_abs_inv : forall A body kappa l arg result,
  value arg ->
  big_eval (tm_app (protect_value (tm_abs A body kappa) l) arg High)
    result ->
  exists w, big_eval (open body arg) w /\
    result = protect_value (protect_value w kappa.(indirect_reader)) l.
Proof.
  intros A body kappa l arg result Harg He.
  simpl in He.
  destruct (big_eval_app_abs_inv _ _ _ _ _ _ Harg He)
    as [w [Hw ->]].
  exists w. split; auto.
  simpl. symmetry. apply protect_value_compose.
  apply big_eval_result_value with (t := open body arg). exact Hw.
Qed.

Lemma big_eval_original_abs_app : forall A body kappa arg w,
  value (tm_abs A body kappa) -> value arg ->
  big_eval (open body arg) w ->
  big_eval (tm_app (tm_abs A body kappa) arg High)
    (protect_value w kappa.(indirect_reader)).
Proof.
  intros A body kappa arg w Habs Harg Hbody.
  eapply BE_App; eauto using BE_Value, flows_to_high.
Qed.

Lemma value_relation_relabel : forall observer T v1 v2 l1 l2,
  value_relation observer T v1 v2 ->
  value_relation observer T
    (protect_value v1 l1) (protect_value v2 l2).
Proof.
  intros observer T; induction T; intros v1 v2 l1 l2 Hrel;
    simpl in Hrel |- *;
    destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
  - split; [apply protect_value_is_value; exact Hv1|].
    split; [apply protect_value_is_value; exact Hv2|].
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value; auto. }
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value; auto. }
    intro Hvisible.
    destruct (Hshape Hvisible) as [k1 [k2 [-> ->]]].
    exists (protect_security k1 l1), (protect_security k2 l2).
    simpl. auto.
  - split; [apply protect_value_is_value; exact Hv1|].
    split; [apply protect_value_is_value; exact Hv2|].
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value; auto. }
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value; auto. }
    intro Hvisible.
    destruct (Hshape Hvisible) as
      [[a1 [a2 [k1 [k2 [-> [-> Hr]]]]]]|
       [a1 [a2 [k1 [k2 [-> [-> Hr]]]]]]].
    + left. exists a1, a2, (protect_security k1 l1),
        (protect_security k2 l2). simpl. repeat split; auto.
    + right. exists a1, a2, (protect_security k1 l1),
        (protect_security k2 l2). simpl. repeat split; auto.
  - split; [apply protect_value_is_value; exact Hv1|].
    split; [apply protect_value_is_value; exact Hv2|].
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value; auto. }
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value; auto. }
    intro Hvisible.
    destruct (Hshape Hvisible) as [a1 [b1 [a2 [b2 [k1 [k2
      [-> [-> [Ha Hb]]]]]]]]].
    exists a1, b1, a2, b2,
      (protect_security k1 l1), (protect_security k2 l2).
    simpl. repeat split; auto.
  - split; [apply protect_value_is_value; exact Hv1|].
    split; [apply protect_value_is_value; exact Hv2|].
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value; auto. }
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value; auto. }
    intro Hvisible.
    destruct (Hshape Hvisible) as [A1 [A2 [body1 [body2 [k1 [k2
      [-> [-> Hfun]]]]]]]].
    exists A1, A2, body1, body2,
      (protect_security k1 l1), (protect_security k2 l2).
    simpl. repeat split; auto.
    intros arg1 arg2 Harg w1 w2 He1 He2.
    destruct (value_relation_fields _ _ _ _ Harg)
      as [HargV1 [HargV2 _]].
    destruct (big_eval_relabelled_abs_inv _ _ _ _ _ _ HargV1
      (evaluates_big_eval _ _ He1)) as [z1 [Hz1 Ew1]].
    destruct (big_eval_relabelled_abs_inv _ _ _ _ _ _ HargV2
      (evaluates_big_eval _ _ He2)) as [z2 [Hz2 Ew2]].
    subst w1 w2.
    apply IHT2.
    eapply Hfun; eauto;
      apply big_eval_evaluates;
      eapply big_eval_original_abs_app; eauto.
Qed.

Lemma big_eval_fst_inv : forall p r result,
  big_eval (tm_fst p r) result ->
  exists a b kappa, big_eval p (tm_pair a b kappa) /\
    result = protect_value a kappa.(indirect_reader).
Proof.
  intros p r result H; inversion H; subst.
  - match goal with Hv : value (tm_fst _ _) |- _ => inversion Hv end.
  - eauto.
Qed.

Lemma big_eval_snd_inv : forall p r result,
  big_eval (tm_snd p r) result ->
  exists a b kappa, big_eval p (tm_pair a b kappa) /\
    result = protect_value b kappa.(indirect_reader).
Proof.
  intros p r result H; inversion H; subst.
  - match goal with Hv : value (tm_snd _ _) |- _ => inversion Hv end.
  - eauto.
Qed.

Lemma big_eval_case_inv : forall t b1 b2 r result,
  big_eval (tm_case t b1 b2 r) result ->
  (exists v kappa w,
    big_eval t (tm_inl v kappa) /\
    big_eval (open b1 v) w /\
    result = protect_value w kappa.(indirect_reader)) \/
  (exists v kappa w,
    big_eval t (tm_inr v kappa) /\
    big_eval (open b2 v) w /\
    result = protect_value w kappa.(indirect_reader)).
Proof.
  intros t b1 b2 r result H; inversion H; subst.
  - match goal with Hv : value (tm_case _ _ _ _) |- _ => inversion Hv end.
  - left. exists v, kappa, w. repeat split; auto.
  - right. exists v, kappa, w. repeat split; auto.
Qed.

Lemma visible_sum_left : forall A B kappa a1 a2 k1 k2,
  indirect_reader kappa = Low ->
  value_relation Low (Ty_Sum A B kappa)
    (tm_inl a1 k1) (tm_inl a2 k2) ->
  value_relation Low A a1 a2.
Proof.
  intros A B kappa a1 a2 k1 k2 Eind Hrel.
  simpl in Hrel. destruct Hrel as [_ [_ [_ [_ Hshape]]]].
  rewrite Eind in Hshape.
  destruct (Hshape (flows_to_refl Low)) as
    [[u1 [u2 [s1 [s2 [E1 [E2 Hr]]]]]]|
     [u1 [u2 [s1 [s2 [E1 [E2 Hr]]]]]]].
  - inversion E1; inversion E2; subst; exact Hr.
  - discriminate.
Qed.

Lemma visible_sum_right : forall A B kappa a1 a2 k1 k2,
  indirect_reader kappa = Low ->
  value_relation Low (Ty_Sum A B kappa)
    (tm_inr a1 k1) (tm_inr a2 k2) ->
  value_relation Low B a1 a2.
Proof.
  intros A B kappa a1 a2 k1 k2 Eind Hrel.
  simpl in Hrel. destruct Hrel as [_ [_ [_ [_ Hshape]]]].
  rewrite Eind in Hshape.
  destruct (Hshape (flows_to_refl Low)) as
    [[u1 [u2 [s1 [s2 [E1 [E2 Hr]]]]]]|
     [u1 [u2 [s1 [s2 [E1 [E2 Hr]]]]]]].
  - discriminate.
  - inversion E1; inversion E2; subst; exact Hr.
Qed.

Lemma visible_sum_mixed : forall A B kappa a1 a2 k1 k2,
  indirect_reader kappa = Low ->
  value_relation Low (Ty_Sum A B kappa)
    (tm_inl a1 k1) (tm_inr a2 k2) -> False.
Proof.
  intros A B kappa a1 a2 k1 k2 Eind Hrel.
  simpl in Hrel. destruct Hrel as [_ [_ [_ [_ Hshape]]]].
  rewrite Eind in Hshape.
  destruct (Hshape (flows_to_refl Low)) as
    [[u1 [u2 [s1 [s2 [E1 [E2 Hr]]]]]]|
     [u1 [u2 [s1 [s2 [E1 [E2 Hr]]]]]]]; discriminate.
Qed.

Lemma case_lifting_low : forall A B T kappa
    scr1 scr2 left1 right1 left2 right2 r,
  indirect_reader kappa = Low ->
  expression_lifting (value_relation Low (Ty_Sum A B kappa)) scr1 scr2 ->
  (forall a1 a2,
    value_relation Low A a1 a2 ->
    expression_lifting (value_relation Low T)
      (open left1 a1) (open left2 a2)) ->
  (forall a1 a2,
    value_relation Low B a1 a2 ->
    expression_lifting (value_relation Low T)
      (open right1 a1) (open right2 a2)) ->
  expression_lifting (value_relation Low T)
    (tm_case scr1 left1 right1 r) (tm_case scr2 left2 right2 r).
Proof.
  intros A B T kappa scr1 scr2 left1 right1 left2 right2 r
    Eind Hscrut Hleft Hright v1 v2 Ev1 Ev2.
  destruct (big_eval_case_inv _ _ _ _ _ (evaluates_big_eval _ _ Ev1))
    as [[a1 [k1 [w1 [Hs1 [Hb1 Ew1]]]]]|
        [a1 [k1 [w1 [Hs1 [Hb1 Ew1]]]]]].
  - destruct (big_eval_case_inv _ _ _ _ _ (evaluates_big_eval _ _ Ev2))
      as [[a2 [k2 [w2 [Hs2 [Hb2 Ew2]]]]]|
          [a2 [k2 [w2 [Hs2 [Hb2 Ew2]]]]]].
    + subst v1 v2.
      pose proof (Hscrut _ _ (big_eval_evaluates _ _ Hs1)
        (big_eval_evaluates _ _ Hs2)) as Hsum.
      pose proof (visible_sum_left _ _ _ _ _ _ _ Eind Hsum) as Harg.
      pose proof (Hleft _ _ Harg _ _
        (big_eval_evaluates _ _ Hb1) (big_eval_evaluates _ _ Hb2)) as Hbody.
      apply value_relation_relabel. exact Hbody.
    + pose proof (Hscrut _ _ (big_eval_evaluates _ _ Hs1)
        (big_eval_evaluates _ _ Hs2)) as Hsum.
      exfalso. eapply visible_sum_mixed; eauto.
  - destruct (big_eval_case_inv _ _ _ _ _ (evaluates_big_eval _ _ Ev2))
      as [[a2 [k2 [w2 [Hs2 [Hb2 Ew2]]]]]|
          [a2 [k2 [w2 [Hs2 [Hb2 Ew2]]]]]].
    + pose proof (Hscrut _ _ (big_eval_evaluates _ _ Hs1)
        (big_eval_evaluates _ _ Hs2)) as Hsum.
      exfalso. eapply visible_sum_mixed; eauto.
      apply value_relation_symmetric. exact Hsum.
    + subst v1 v2.
      pose proof (Hscrut _ _ (big_eval_evaluates _ _ Hs1)
        (big_eval_evaluates _ _ Hs2)) as Hsum.
      pose proof (visible_sum_right _ _ _ _ _ _ _ Eind Hsum) as Harg.
      pose proof (Hright _ _ Harg _ _
        (big_eval_evaluates _ _ Hb1) (big_eval_evaluates _ _ Hb2)) as Hbody.
      apply value_relation_relabel. exact Hbody.
Qed.

Theorem fundamental_low : forall Gamma t T,
  has_type Gamma t T ->
  forall rho1 rho2,
    environment_related Low Gamma rho1 rho2 ->
    expression_relation Low T
      (instantiate Gamma rho1 t) (instantiate Gamma rho2 t).
Proof.
  intros Gamma t T Hty.
  pose proof Hty as Horig.
  induction Hty; intros rho1 rho2 Henv.
  - pose proof (Henv x T (lookup_in_context _ _ _ H)) as Hrel.
    rewrite (instantiate_var Low Gamma rho1 rho2 x T H Henv).
    rewrite (instantiate_var Low Gamma rho2 rho1 x T H)
      by (apply environment_related_symmetric; exact Henv).
    apply value_relation_expression. exact Hrel.
  - rewrite !instantiate_unit.
    apply value_relation_expression. apply unit_value_related.
  - destruct (indirect_reader kappa) eqn:Eind.
    + eapply instantiated_expression_from_lifting; eauto.
      unfold expression_lifting. intros v1 v2 Ev1 Ev2.
      apply value_relation_intro_low.
      * exact (proj2 Ev1).
      * exact (proj2 Ev2).
      * eapply underlying_typed_evaluation; eauto.
        eapply instantiated_underlying_typed; eauto.
      * eapply underlying_typed_evaluation; eauto.
        eapply instantiated_underlying_typed_right; eauto.
      * intros Hvisible.
        rewrite instantiate_abs in Ev1, Ev2.
        pose proof (big_eval_abs_source_inv _ _ _ _
          (evaluates_big_eval _ _ Ev1)) as E1.
        pose proof (big_eval_abs_source_inv _ _ _ _
          (evaluates_big_eval _ _ Ev2)) as E2.
        subst v1 v2.
        exists T1, T1, (instantiate Gamma rho1 body),
          (instantiate Gamma rho2 body), kappa, kappa.
        repeat split; try reflexivity.
        intros arg1 arg2 Harg w1 w2 Happ1 Happ2.
        set (y := fresh (L ++ fv body ++ map fst Gamma)).
        assert (HyL : ~ In y L).
        { subst y. intro Hin. apply (fresh_not_in (L ++ fv body ++ map fst Gamma)).
          repeat rewrite in_app_iff. tauto. }
        assert (Hybody : ~ In y (fv body)).
        { subst y. intro Hin. apply (fresh_not_in (L ++ fv body ++ map fst Gamma)).
          repeat rewrite in_app_iff. tauto. }
        assert (Hydom : ~ In y (map fst Gamma)).
        { subst y. intro Hin. apply (fresh_not_in (L ++ fv body ++ map fst Gamma)).
          repeat rewrite in_app_iff. tauto. }
        destruct (value_relation_closed _ _ _ _ Harg) as [Harg1 Harg2].
        pose proof (H2 y HyL (H1 y HyL) (env_extend rho1 y arg1)
          (env_extend rho2 y arg2)
          (environment_related_extend _ _ _ _ _ _ _ _ Hydom Henv Harg))
          as Hbody.
        destruct Hbody as [_ [_ Hbody]].
        rewrite (instantiate_open_body Gamma rho1 y T1 body arg1
          Hybody Hydom (environment_values_lc _ _ _ _ Henv) Harg1)
          in Hbody.
        rewrite (instantiate_open_body Gamma rho2 y T1 body arg2
          Hybody Hydom
          (environment_values_lc _ _ _ _
             (environment_related_symmetric _ _ _ _ Henv)) Harg2)
          in Hbody.
        destruct (value_relation_fields _ _ _ _ Harg)
          as [HargV1 [HargV2 _]].
        destruct (big_eval_app_abs_inv _ _ _ _ _ _ HargV1
          (evaluates_big_eval _ _ Happ1)) as [z1 [Hz1 Ew1]].
        destruct (big_eval_app_abs_inv _ _ _ _ _ _ HargV2
          (evaluates_big_eval _ _ Happ2)) as [z2 [Hz2 Ew2]].
        rewrite Eind in Ew1, Ew2.
        rewrite (protect_value_low _ (big_eval_result_value _ _ Hz1)) in Ew1.
        rewrite (protect_value_low _ (big_eval_result_value _ _ Hz2)) in Ew2.
        subst w1 w2.
        apply Hbody; apply big_eval_evaluates; assumption.
    + eapply opaque_instantiate_related; eauto.
      simpl. rewrite Eind. tauto.
  - destruct (indirect_reader kappa) eqn:Eind.
    + rewrite ty_protect_low in Horig |- *.
      eapply instantiated_expression_from_lifting; eauto.
      unfold expression_lifting. intros v1 v2 Ev1 Ev2.
      rewrite instantiate_app in Ev1, Ev2.
      destruct (big_eval_app_high _ _ _ _ (evaluates_big_eval _ _ Ev1))
        as [vf1 [va1 [Hf1 [Ha1 Hhigh1]]]].
      destruct (big_eval_app_high _ _ _ _ (evaluates_big_eval _ _ Ev2))
        as [vf2 [va2 [Hf2 [Ha2 Hhigh2]]]].
      destruct (IHHty1 Hty1 rho1 rho2 Henv) as [_ [_ Hfunlift]].
      destruct (IHHty2 Hty2 rho1 rho2 Henv) as [_ [_ Harglift]].
      pose proof (Hfunlift _ _ (big_eval_evaluates _ _ Hf1)
        (big_eval_evaluates _ _ Hf2)) as Hfunrel.
      pose proof (Harglift _ _ (big_eval_evaluates _ _ Ha1)
        (big_eval_evaluates _ _ Ha2)) as Hargrel.
      simpl in Hfunrel.
      destruct Hfunrel as [_ [_ [_ [_ Hshape]]]].
      rewrite Eind in Hshape.
      specialize (Hshape (flows_to_refl Low)).
      destruct Hshape as [A1 [A2 [b1 [b2 [k1 [k2
        [-> [-> Hfun]]]]]]]].
      exact (Hfun va1 va2 Hargrel v1 v2
        (big_eval_evaluates _ _ Hhigh1)
        (big_eval_evaluates _ _ Hhigh2)).
    + eapply opaque_instantiate_related; eauto.
      apply ty_protect_high_opaque.
  - destruct (indirect_reader kappa) eqn:Eind.
    + eapply instantiated_expression_from_lifting; eauto.
      unfold expression_lifting. intros v1 v2 Ev1 Ev2.
      rewrite instantiate_pair in Ev1, Ev2.
      destruct (big_eval_pair_inv _ _ _ _ (evaluates_big_eval _ _ Ev1))
        as [a1 [b1 [-> [Ha1 Hb1]]]].
      destruct (big_eval_pair_inv _ _ _ _ (evaluates_big_eval _ _ Ev2))
        as [a2 [b2 [-> [Ha2 Hb2]]]].
      destruct (IHHty1 Hty1 rho1 rho2 Henv) as [_ [_ Hlift1]].
      destruct (IHHty2 Hty2 rho1 rho2 Henv) as [_ [_ Hlift2]].
      pose proof (Hlift1 _ _ (big_eval_evaluates _ _ Ha1)
        (big_eval_evaluates _ _ Ha2)) as Hr1.
      pose proof (Hlift2 _ _ (big_eval_evaluates _ _ Hb1)
        (big_eval_evaluates _ _ Hb2)) as Hr2.
      apply value_relation_intro_low.
      * exact (proj2 Ev1).
      * exact (proj2 Ev2).
      * eapply underlying_typed_evaluation; eauto.
        pose proof (instantiated_underlying_typed Low Gamma rho1 rho2
          (tm_pair t1 t2 kappa) (Ty_Prod T1 T2 kappa) Horig Henv)
          as Hsrc. rewrite instantiate_pair in Hsrc. exact Hsrc.
      * eapply underlying_typed_evaluation; eauto.
        pose proof (instantiated_underlying_typed_right Low Gamma rho1 rho2
          (tm_pair t1 t2 kappa) (Ty_Prod T1 T2 kappa) Horig Henv)
          as Hsrc. rewrite instantiate_pair in Hsrc. exact Hsrc.
      * intros _. exists a1, b1, a2, b2, kappa, kappa.
        repeat split; auto.
    + eapply opaque_instantiate_related; eauto.
      simpl. rewrite Eind. tauto.
  - destruct (indirect_reader kappa) eqn:Eind.
    + rewrite ty_protect_low in Horig |- *.
      eapply instantiated_expression_from_lifting; eauto.
      unfold expression_lifting. intros v1 v2 Ev1 Ev2.
      rewrite instantiate_fst in Ev1, Ev2.
      destruct (big_eval_fst_inv _ _ _ (evaluates_big_eval _ _ Ev1))
        as [a1 [b1 [k1 [Hp1 ->]]]].
      destruct (big_eval_fst_inv _ _ _ (evaluates_big_eval _ _ Ev2))
        as [a2 [b2 [k2 [Hp2 ->]]]].
      destruct (IHHty Hty rho1 rho2 Henv) as [_ [_ Hlift]].
      pose proof (Hlift _ _ (big_eval_evaluates _ _ Hp1)
        (big_eval_evaluates _ _ Hp2)) as Hpair.
      simpl in Hpair.
      destruct Hpair as [_ [_ [_ [_ Hshape]]]].
      rewrite Eind in Hshape.
      specialize (Hshape (flows_to_refl Low)).
      destruct Hshape as [a1' [b1' [a2' [b2' [k1' [k2'
        [E1 [E2 [Ha Hb]]]]]]]]].
      inversion E1; inversion E2; subst.
      eapply value_relation_relabel. exact Ha.
    + eapply opaque_instantiate_related; eauto.
      apply ty_protect_high_opaque.
  - destruct (indirect_reader kappa) eqn:Eind.
    + rewrite ty_protect_low in Horig |- *.
      eapply instantiated_expression_from_lifting; eauto.
      unfold expression_lifting. intros v1 v2 Ev1 Ev2.
      rewrite instantiate_snd in Ev1, Ev2.
      destruct (big_eval_snd_inv _ _ _ (evaluates_big_eval _ _ Ev1))
        as [a1 [b1 [k1 [Hp1 ->]]]].
      destruct (big_eval_snd_inv _ _ _ (evaluates_big_eval _ _ Ev2))
        as [a2 [b2 [k2 [Hp2 ->]]]].
      destruct (IHHty Hty rho1 rho2 Henv) as [_ [_ Hlift]].
      pose proof (Hlift _ _ (big_eval_evaluates _ _ Hp1)
        (big_eval_evaluates _ _ Hp2)) as Hpair.
      simpl in Hpair.
      destruct Hpair as [_ [_ [_ [_ Hshape]]]].
      rewrite Eind in Hshape.
      specialize (Hshape (flows_to_refl Low)).
      destruct Hshape as [a1' [b1' [a2' [b2' [k1' [k2'
        [E1 [E2 [Ha Hb]]]]]]]]].
      inversion E1; inversion E2; subst.
      eapply value_relation_relabel. exact Hb.
    + eapply opaque_instantiate_related; eauto.
      apply ty_protect_high_opaque.
  - destruct (indirect_reader kappa) eqn:Eind.
    + eapply instantiated_expression_from_lifting; eauto.
      unfold expression_lifting. intros v1 v2 Ev1 Ev2.
      rewrite instantiate_inl in Ev1, Ev2.
      destruct (big_eval_inl_inv _ _ _ (evaluates_big_eval _ _ Ev1))
        as [a1 [-> Ha1]].
      destruct (big_eval_inl_inv _ _ _ (evaluates_big_eval _ _ Ev2))
        as [a2 [-> Ha2]].
      destruct (IHHty Hty rho1 rho2 Henv) as [_ [_ Hlift]].
      pose proof (Hlift _ _ (big_eval_evaluates _ _ Ha1)
        (big_eval_evaluates _ _ Ha2)) as Hr.
      apply value_relation_intro_low.
      * exact (proj2 Ev1).
      * exact (proj2 Ev2).
      * eapply underlying_typed_evaluation; eauto.
        pose proof (instantiated_underlying_typed Low Gamma rho1 rho2
          (tm_inl t kappa) (Ty_Sum T1 T2 kappa) Horig Henv)
          as Hsrc. rewrite instantiate_inl in Hsrc. exact Hsrc.
      * eapply underlying_typed_evaluation; eauto.
        pose proof (instantiated_underlying_typed_right Low Gamma rho1 rho2
          (tm_inl t kappa) (Ty_Sum T1 T2 kappa) Horig Henv)
          as Hsrc. rewrite instantiate_inl in Hsrc. exact Hsrc.
      * intros _. left. exists a1, a2, kappa, kappa.
        repeat split; auto.
    + eapply opaque_instantiate_related; eauto.
      simpl. rewrite Eind. tauto.
  - destruct (indirect_reader kappa) eqn:Eind.
    + eapply instantiated_expression_from_lifting; eauto.
      unfold expression_lifting. intros v1 v2 Ev1 Ev2.
      rewrite instantiate_inr in Ev1, Ev2.
      destruct (big_eval_inr_inv _ _ _ (evaluates_big_eval _ _ Ev1))
        as [a1 [-> Ha1]].
      destruct (big_eval_inr_inv _ _ _ (evaluates_big_eval _ _ Ev2))
        as [a2 [-> Ha2]].
      destruct (IHHty Hty rho1 rho2 Henv) as [_ [_ Hlift]].
      pose proof (Hlift _ _ (big_eval_evaluates _ _ Ha1)
        (big_eval_evaluates _ _ Ha2)) as Hr.
      apply value_relation_intro_low.
      * exact (proj2 Ev1).
      * exact (proj2 Ev2).
      * eapply underlying_typed_evaluation; eauto.
        pose proof (instantiated_underlying_typed Low Gamma rho1 rho2
          (tm_inr t kappa) (Ty_Sum T1 T2 kappa) Horig Henv)
          as Hsrc. rewrite instantiate_inr in Hsrc. exact Hsrc.
      * eapply underlying_typed_evaluation; eauto.
        pose proof (instantiated_underlying_typed_right Low Gamma rho1 rho2
          (tm_inr t kappa) (Ty_Sum T1 T2 kappa) Horig Henv)
          as Hsrc. rewrite instantiate_inr in Hsrc. exact Hsrc.
      * intros _. right. exists a1, a2, kappa, kappa.
        repeat split; auto.
    + eapply opaque_instantiate_related; eauto.
      simpl. rewrite Eind. tauto.
  - destruct (indirect_reader kappa) eqn:Eind.
    + rewrite ty_protect_low in Horig |- *.
      eapply instantiated_expression_from_lifting; eauto.
      rewrite !instantiate_case.
      eapply case_lifting_low.
      * exact Eind.
      * destruct (IHHty Hty rho1 rho2 Henv) as [_ [_ Hscrut]].
        exact Hscrut.
      * intros a1 a2 Harg.
        set (y := fresh (L ++ fv body1 ++ map fst Gamma)).
        assert (HyL : ~ In y L).
        { subst y. intro Hin. apply (fresh_not_in (L ++ fv body1 ++ map fst Gamma)).
          repeat rewrite in_app_iff. tauto. }
        assert (Hybody : ~ In y (fv body1)).
        { subst y. intro Hin. apply (fresh_not_in (L ++ fv body1 ++ map fst Gamma)).
          repeat rewrite in_app_iff. tauto. }
        assert (Hydom : ~ In y (map fst Gamma)).
        { subst y. intro Hin. apply (fresh_not_in (L ++ fv body1 ++ map fst Gamma)).
          repeat rewrite in_app_iff. tauto. }
        destruct (value_relation_closed _ _ _ _ Harg) as [Harg1 Harg2].
        pose proof (H1 y HyL (H0 y HyL) (env_extend rho1 y a1)
          (env_extend rho2 y a2)
          (environment_related_extend _ _ _ _ _ _ _ _ Hydom Henv Harg))
          as Hbranch.
        destruct Hbranch as [_ [_ Hbranch]].
        rewrite (instantiate_open_body Gamma rho1 y T1 body1 a1
          Hybody Hydom (environment_values_lc _ _ _ _ Henv) Harg1)
          in Hbranch.
        rewrite (instantiate_open_body Gamma rho2 y T1 body1 a2
          Hybody Hydom
          (environment_values_lc _ _ _ _
             (environment_related_symmetric _ _ _ _ Henv)) Harg2)
          in Hbranch.
        exact Hbranch.
      * intros a1 a2 Harg.
        set (y := fresh (L ++ fv body2 ++ map fst Gamma)).
        assert (HyL : ~ In y L).
        { subst y. intro Hin. apply (fresh_not_in (L ++ fv body2 ++ map fst Gamma)).
          repeat rewrite in_app_iff. tauto. }
        assert (Hybody : ~ In y (fv body2)).
        { subst y. intro Hin. apply (fresh_not_in (L ++ fv body2 ++ map fst Gamma)).
          repeat rewrite in_app_iff. tauto. }
        assert (Hydom : ~ In y (map fst Gamma)).
        { subst y. intro Hin. apply (fresh_not_in (L ++ fv body2 ++ map fst Gamma)).
          repeat rewrite in_app_iff. tauto. }
        destruct (value_relation_closed _ _ _ _ Harg) as [Harg1 Harg2].
        pose proof (H3 y HyL (H2 y HyL) (env_extend rho1 y a1)
          (env_extend rho2 y a2)
          (environment_related_extend _ _ _ _ _ _ _ _ Hydom Henv Harg))
          as Hbranch.
        destruct Hbranch as [_ [_ Hbranch]].
        rewrite (instantiate_open_body Gamma rho1 y T2 body2 a1
          Hybody Hydom (environment_values_lc _ _ _ _ Henv) Harg1)
          in Hbranch.
        rewrite (instantiate_open_body Gamma rho2 y T2 body2 a2
          Hybody Hydom
          (environment_values_lc _ _ _ _
             (environment_related_symmetric _ _ _ _ Henv)) Harg2)
          in Hbranch.
        exact Hbranch.
    + eapply opaque_instantiate_related; eauto.
      apply ty_protect_high_opaque.
  - destruct l.
    + rewrite ty_protect_low in Horig |- *.
      eapply instantiated_expression_from_lifting; eauto.
      unfold expression_lifting. intros v1 v2 Ev1 Ev2.
      rewrite instantiate_protect in Ev1, Ev2.
      destruct (big_eval_protect_inv _ _ _ (evaluates_big_eval _ _ Ev1))
        as [u1 [Hu1 Ew1]].
      destruct (big_eval_protect_inv _ _ _ (evaluates_big_eval _ _ Ev2))
        as [u2 [Hu2 Ew2]].
      rewrite (protect_value_low _ (big_eval_result_value _ _ Hu1)) in Ew1.
      rewrite (protect_value_low _ (big_eval_result_value _ _ Hu2)) in Ew2.
      subst v1 v2.
      destruct (IHHty Hty rho1 rho2 Henv) as [_ [_ Hlift]].
      apply Hlift; apply big_eval_evaluates; assumption.
    + eapply opaque_instantiate_related; eauto.
      apply ty_protect_high_opaque.
  - eapply instantiated_expression_from_lifting; eauto.
    unfold expression_lifting. intros v1 v2 Ev1 Ev2.
    destruct (IHHty Hty rho1 rho2 Henv) as [_ [_ Hlift]].
    eapply value_relation_subtype; eauto.
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
