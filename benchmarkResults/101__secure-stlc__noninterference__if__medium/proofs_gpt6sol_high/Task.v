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

Lemma flows_to_trans : forall a b c,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. destruct a, b, c; simpl; tauto. Qed.

Lemma related_ground_values_erase : forall T k observer v1 v2,
  ground T -> transparent_at k T ->
  flows_to k.(indirect_reader) observer ->
  value_relation observer T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  induction T; intros k observer v1 v2 Hg Ht Hflow Hr;
    destruct Hr as [_ [_ [_ [_ Hr]]]]; simpl in Hg, Ht, Hr.
  - destruct Ht as [Hle _].
    specialize (Hr (flows_to_trans _ _ _ (proj2 Hle) Hflow)).
    destruct Hr as [k1 [k2 [-> ->]]]. reflexivity.
  - destruct Ht as [Hle [Ht1 Ht2]].
    specialize (Hr (flows_to_trans _ _ _ (proj2 Hle) Hflow)).
    destruct Hg as [Hg1 Hg2].
    destruct Hr as [[u1 [u2 [k1 [k2 [-> [-> Hrel]]]]]] |
                    [u1 [u2 [k1 [k2 [-> [-> Hrel]]]]]]]; simpl;
      f_equal; eauto.
  - destruct Ht as [Hle [Ht1 Ht2]].
    specialize (Hr (flows_to_trans _ _ _ (proj2 Hle) Hflow)).
    destruct Hg as [Hg1 Hg2].
    destruct Hr as (a1 & b1 & a2 & b2 & k1 & k2 & -> & -> & Ha & Hb).
    simpl. f_equal; eauto.
  - contradiction.
Qed.

Definition erase_context (Gamma : context) : context :=
  map (fun p => (fst p, erase_type (snd p))) Gamma.

Lemma lookup_erase_context : forall Gamma x,
  lookup_context x (erase_context Gamma) =
  option_map erase_type (lookup_context x Gamma).
Proof.
  induction Gamma as [|[y T] Gamma IH]; intros x; simpl; auto.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma erase_context_update : forall Gamma x T,
  erase_context (update Gamma x T) =
  update (erase_context Gamma) x (erase_type T).
Proof. reflexivity. Qed.

Lemma erase_type_protect : forall l T,
  erase_type (ty_protect l T) = erase_type T.
Proof. intros l []; reflexivity. Qed.

Lemma protect_erased_type : forall T,
  ty_protect Low (erase_type T) = erase_type T.
Proof. intros []; reflexivity. Qed.

Lemma wf_erase_type : forall T, wf_ty (erase_type T).
Proof.
  induction T; simpl; auto; repeat split; auto.
Qed.

Lemma erase_type_subtype : forall T U,
  subtype T U -> subtype (erase_type T) (erase_type U).
Proof.
  intros T U H. induction H; simpl.
  - apply S_Unit; vm_compute; tauto.
  - apply S_Sum; auto; vm_compute; tauto.
  - apply S_Prod; auto; vm_compute; tauto.
  - apply S_Arrow; auto; vm_compute; tauto.
  - eapply S_Trans; eauto.
Qed.

Lemma erase_open_rec : forall t k u,
  erase_security (open_rec k u t) =
  open_rec k (erase_security u) (erase_security t).
Proof.
  induction t; intros k u; simpl; try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity).
  - destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma erase_open : forall body u,
  erase_security (open body u) =
  open (erase_security body) (erase_security u).
Proof. intros; unfold open; apply erase_open_rec. Qed.

Lemma erase_typing : forall Gamma t T,
  has_type Gamma t T ->
  has_type (erase_context Gamma) (erase_security t) (erase_type T).
Proof.
  intros Gamma t T Hty. induction Hty; simpl.
  - apply T_Var.
    + rewrite lookup_erase_context, H. reflexivity.
    + apply wf_erase_type.
  - apply T_Unit. vm_compute; exact I.
  - eapply T_Abs with (L := L); eauto using wf_erase_type.
    + vm_compute; exact I.
    + intros x Hfresh.
      specialize (H2 x Hfresh).
      rewrite erase_context_update in H2.
      rewrite erase_open in H2. simpl in H2. exact H2.
  - rewrite erase_type_protect.
    rewrite <- protect_erased_type.
    eapply T_App with (T1 := erase_type T1) (kappa := public).
    + exact IHHty1.
    + exact IHHty2.
    + vm_compute; exact I.
  - eapply T_Pair; eauto. vm_compute; exact I.
  - rewrite erase_type_protect.
    rewrite <- protect_erased_type.
    eapply T_Fst with (T2 := erase_type T2) (kappa := public).
    + exact IHHty.
    + vm_compute; exact I.
  - rewrite erase_type_protect.
    rewrite <- protect_erased_type.
    eapply T_Snd with (T1 := erase_type T1) (kappa := public).
    + exact IHHty.
    + vm_compute; exact I.
  - eapply T_Inl with (T2 := erase_type T2); eauto using wf_erase_type.
    vm_compute; exact I.
  - eapply T_Inr with (T1 := erase_type T1); eauto using wf_erase_type.
    vm_compute; exact I.
  - rewrite erase_type_protect.
    rewrite <- protect_erased_type.
    eapply T_Case with (L := L) (T1 := erase_type T1)
      (T2 := erase_type T2) (kappa := public).
    + exact IHHty.
    + vm_compute; exact I.
    + intros x Hfresh. specialize (H1 x Hfresh).
      rewrite erase_context_update in H1.
      rewrite erase_open in H1. simpl in H1. exact H1.
    + intros x Hfresh. specialize (H3 x Hfresh).
      rewrite erase_context_update in H3.
      rewrite erase_open in H3. simpl in H3. exact H3.
  - rewrite erase_type_protect. exact IHHty.
  - eapply T_Sub; eauto using erase_type_subtype.
  - rewrite erase_type_protect.
    rewrite <- protect_erased_type.
    eapply T_If with (k := public).
    + exact IHHty1.
    + exact IHHty2.
    + exact IHHty3.
    + vm_compute; exact I.
Qed.

Lemma lc_at_erase : forall t k,
  lc_at k t -> lc_at k (erase_security t).
Proof.
  induction t; intros k H; simpl in *; intuition eauto.
Qed.

Lemma value_erase : forall v,
  value v -> value (erase_security v).
Proof.
  intros v H. induction H; simpl; try constructor; auto.
  apply lc_at_erase. exact H.
Qed.

Lemma erase_protect_value : forall v l,
  value v -> erase_security (protect_value v l) = erase_security v.
Proof. intros v l Hv; inversion Hv; reflexivity. Qed.

Definition fresh_atom (L : list atom) : atom :=
  S (fold_right Nat.max 0 L).

Lemma in_bounded : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|y L IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + specialize (IH _ Hin). lia.
Qed.

Lemma fresh_atom_not_in : forall L, ~ In (fresh_atom L) L.
Proof.
  intros L Hin. unfold fresh_atom in Hin.
  pose proof (in_bounded L _ Hin). lia.
Qed.

Lemma lc_open_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x H; simpl in *;
    try solve [intuition eauto].
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + simpl in H. lia.
Qed.

Lemma typing_locally_closed : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty; unfold locally_closed in *; simpl in *;
    try solve [intuition eauto].
  - specialize (H2 (fresh_atom L) (fresh_atom_not_in L)).
    apply lc_open_inv with (x := fresh_atom L) in H2. exact H2.
  - specialize (H1 (fresh_atom L) (fresh_atom_not_in L)).
    specialize (H3 (fresh_atom L) (fresh_atom_not_in L)).
    split; [exact IHHty|].
    split.
    + exact (lc_open_inv body1 0 (fresh_atom L) H1).
    + exact (lc_open_inv body2 0 (fresh_atom L) H3).
Qed.

Lemma underlying_typed_from_type : forall t T,
  has_type empty t T -> underlying_typed T t.
Proof.
  intros t T H. unfold underlying_typed.
  pose proof (erase_typing _ _ _ H) as He.
  simpl in He. exact He.
Qed.

Lemma hidden_values_related : forall observer T v1 v2,
  ~ flows_to (security_of T).(indirect_reader) observer ->
  value v1 -> value v2 ->
  underlying_typed T v1 -> underlying_typed T v2 ->
  value_relation observer T v1 v2.
Proof.
  intros observer T v1 v2 Hhidden Hv1 Hv2 Hty1 Hty2.
  destruct T; simpl in *; repeat split; auto; contradiction.
Qed.

Definition context_extends (Gamma Delta : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    lookup_context x Delta = Some T.

Lemma typing_context_extends : forall Gamma t T,
  has_type Gamma t T ->
  forall Delta, context_extends Gamma Delta -> has_type Delta t T.
Proof.
  intros Gamma t T Hty. induction Hty; intros Delta Hext;
    try (econstructor; eauto; fail).
  - eapply T_Abs with (L := L); eauto.
    intros x Hfresh. apply H2; auto.
    intros y U Hlookup. simpl in *.
    destruct (Nat.eqb y x); auto.
  - eapply T_Case with (L := L) (T1 := T1) (T2 := T2)
      (kappa := kappa); eauto.
    + intros x Hfresh. apply H1; auto.
      intros y U Hlookup. simpl in *.
      destruct (Nat.eqb y x); auto.
    + intros x Hfresh. apply H3; auto.
      intros y U Hlookup. simpl in *.
      destruct (Nat.eqb y x); auto.
Qed.

Lemma open_rec_above_lc : forall t k j u,
  lc_at k t -> k <= j -> open_rec j u t = t.
Proof.
  induction t; intros k j u Hlc Hle; simpl in *;
    try solve [f_equal; eauto].
  - destruct (Nat.eqb j n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + reflexivity.
  - rewrite (IHt (S k) (S j) u Hlc); [reflexivity|lia].
  - destruct Hlc as [H1 H2].
    rewrite (IHt1 k j u H1 Hle), (IHt2 k j u H2 Hle). reflexivity.
  - destruct Hlc as [H1 H2].
    rewrite (IHt1 k j u H1 Hle), (IHt2 k j u H2 Hle). reflexivity.
  - destruct Hlc as [H1 [H2 H3]].
    rewrite (IHt1 k j u H1 Hle),
      (IHt2 (S k) (S j) u H2),
      (IHt3 (S k) (S j) u H3); auto; lia.
  - destruct Hlc as [H1 [H2 H3]].
    rewrite (IHt1 k j u H1 Hle),
      (IHt2 k j u H2 Hle),
      (IHt3 k j u H3 Hle); reflexivity.
Qed.

Lemma subst_open_rec_fvar : forall t k x y u,
  x <> y -> locally_closed u ->
  subst x u (open_rec k (tm_fvar y) t) =
  open_rec k (tm_fvar y) (subst x u t).
Proof.
  induction t; intros k x y u Hneq Hlc; simpl;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; auto; reflexivity).
  - destruct (Nat.eqb k n); simpl.
    + apply Nat.eqb_neq in Hneq.
      rewrite Hneq. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:Heq; simpl.
    + symmetry. apply open_rec_above_lc with (k := 0); auto. lia.
    + reflexivity.
Qed.

Lemma subst_open_fvar : forall body x y u,
  x <> y -> locally_closed u ->
  subst x u (open body (tm_fvar y)) =
  open (subst x u body) (tm_fvar y).
Proof. intros; unfold open; apply subst_open_rec_fvar; auto. Qed.

Definition context_replaces (Gamma Delta : context) (x : atom) (U : ty) : Prop :=
  lookup_context x Gamma = Some U /\
  forall y, y <> x -> lookup_context y Gamma = lookup_context y Delta.

Lemma lookup_not_in_domain : forall Gamma x,
  ~ In x (map fst Gamma) -> lookup_context x Gamma = None.
Proof.
  induction Gamma as [|[y T] Gamma IH]; intros x Hnot; simpl in *; auto.
  assert (x <> y) by (intro H; subst; apply Hnot; auto).
  assert (Nat.eqb x y = false) as Heq by (apply Nat.eqb_neq; exact H).
  rewrite Heq. apply IH.
  intro Hin. apply Hnot. right. exact Hin.
Qed.

Lemma context_extends_update_fresh : forall Gamma x T,
  lookup_context x Gamma = None ->
  context_extends Gamma (update Gamma x T).
Proof.
  intros Gamma x T Hnone y U Hlook.
  simpl. destruct (Nat.eqb y x) eqn:Heq; auto.
  apply Nat.eqb_eq in Heq. subst. congruence.
Qed.

Lemma context_replaces_update : forall Gamma Delta x y U T,
  x <> y -> context_replaces Gamma Delta x U ->
  context_replaces (update Gamma y T) (update Delta y T) x U.
Proof.
  intros Gamma Delta x y U T Hneq [Hx Hother]. split.
  - simpl. assert (Nat.eqb x y = false) as Heq
      by (apply Nat.eqb_neq; exact Hneq).
    rewrite Heq. exact Hx.
  - intros z Hz. simpl.
    destruct (Nat.eqb z y); [reflexivity|apply Hother; exact Hz].
Qed.

Lemma fresh_for_binder : forall L Delta x,
  let y := fresh_atom (x :: L ++ map fst Delta) in
  ~ In y L /\ y <> x /\ lookup_context y Delta = None.
Proof.
  intros L Delta x y. pose proof (fresh_atom_not_in (x :: L ++ map fst Delta)) as H.
  fold y in H. repeat split.
  - intro Hin. apply H. right. apply in_or_app. left. exact Hin.
  - intro Heq. apply H. left. symmetry. exact Heq.
  - apply lookup_not_in_domain. intro Hin. apply H. right.
    apply in_or_app. right. exact Hin.
Qed.

Lemma typing_substitution : forall Gamma t T,
  has_type Gamma t T ->
  forall Delta x U u,
    context_replaces Gamma Delta x U ->
    has_type Delta u U ->
    has_type Delta (subst x u t) T.
Proof.
  intros Gamma t T Hty. induction Hty; intros Delta z W u Hrep Hu;
    simpl; try (econstructor; eauto; fail).
  - destruct Hrep as [Hx Hother].
    destruct (Nat.eqb z x) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      rewrite H in Hx. inversion Hx; subst. exact Hu.
    + apply Nat.eqb_neq in Heq.
      apply T_Var; auto. rewrite <- (Hother x (fun E => Heq (eq_sym E))). exact H.
  - eapply T_Abs with (L := z :: L ++ map fst Delta); eauto.
    intros y Hfresh.
    assert (Hny : z <> y) by (intro Heq; subst; apply Hfresh; left; reflexivity).
    assert (HnL : ~ In y L) by
      (intro Hin; apply Hfresh; right; apply in_or_app; left; exact Hin).
    assert (HnD : lookup_context y Delta = None).
    { apply lookup_not_in_domain. intro Hin. apply Hfresh. right.
      apply in_or_app. right. exact Hin. }
    pose proof (typing_locally_closed _ _ _ Hu) as Hlc.
    rewrite <- (subst_open_fvar body z y u Hny Hlc).
    eapply H2; eauto using context_replaces_update.
    eapply typing_context_extends; eauto using context_extends_update_fresh.
  - eapply T_Case with (L := z :: L ++ map fst Delta)
      (T1 := T1) (T2 := T2) (kappa := kappa); eauto.
    + intros y Hfresh.
      assert (Hny : z <> y) by (intro Heq; subst; apply Hfresh; left; reflexivity).
      assert (HnL : ~ In y L) by
        (intro Hin; apply Hfresh; right; apply in_or_app; left; exact Hin).
      assert (HnD : lookup_context y Delta = None).
      { apply lookup_not_in_domain. intro Hin. apply Hfresh. right.
        apply in_or_app. right. exact Hin. }
      pose proof (typing_locally_closed _ _ _ Hu) as Hlc.
      rewrite <- (subst_open_fvar body1 z y u Hny Hlc).
      eapply H1; eauto using context_replaces_update.
      eapply typing_context_extends; eauto using context_extends_update_fresh.
    + intros y Hfresh.
      assert (Hny : z <> y) by (intro Heq; subst; apply Hfresh; left; reflexivity).
      assert (HnL : ~ In y L) by
        (intro Hin; apply Hfresh; right; apply in_or_app; left; exact Hin).
      assert (HnD : lookup_context y Delta = None).
      { apply lookup_not_in_domain. intro Hin. apply Hfresh. right.
        apply in_or_app. right. exact Hin. }
      pose proof (typing_locally_closed _ _ _ Hu) as Hlc.
      rewrite <- (subst_open_fvar body2 z y u Hny Hlc).
      eapply H3; eauto using context_replaces_update.
      eapply typing_context_extends; eauto using context_extends_update_fresh.
Qed.

Lemma not_in_app : forall (A B : list atom) x,
  ~ In x (A ++ B) -> ~ In x A /\ ~ In x B.
Proof.
  intros A B x H. split; intro Hin; apply H; apply in_or_app; auto.
Qed.

Lemma subst_open_fresh_rec : forall body k x u,
  ~ In x (fv body) ->
  subst x u (open_rec k (tm_fvar x) body) = open_rec k u body.
Proof.
  induction body; intros k x u Hfresh; simpl in *;
    try (rewrite ?IHbody, ?IHbody1, ?IHbody2, ?IHbody3;
      try (intro Hin; apply Hfresh; apply in_or_app; auto);
      auto; reflexivity).
  - destruct (Nat.eqb k n); simpl.
    + now rewrite Nat.eqb_refl.
    + reflexivity.
  - assert (x <> a) by (intro Heq; apply Hfresh; left; symmetry; exact Heq).
    apply Nat.eqb_neq in H. rewrite H. reflexivity.
  - apply not_in_app in Hfresh as [H1 H23].
    apply not_in_app in H23 as [H2 H3].
    rewrite (IHbody1 k x u H1),
      (IHbody2 (S k) x u H2),
      (IHbody3 (S k) x u H3). reflexivity.
  - apply not_in_app in Hfresh as [H1 H23].
    apply not_in_app in H23 as [H2 H3].
    rewrite (IHbody1 k x u H1),
      (IHbody2 k x u H2),
      (IHbody3 k x u H3). reflexivity.
Qed.

Lemma subst_open_fresh : forall body x u,
  ~ In x (fv body) ->
  subst x u (open body (tm_fvar x)) = open body u.
Proof. intros; unfold open; apply subst_open_fresh_rec; auto. Qed.

Lemma typing_open : forall L Gamma T1 body T2 u,
  (forall x, ~ In x L ->
    has_type (update Gamma x T1) (open body (tm_fvar x)) T2) ->
  has_type Gamma u T1 ->
  has_type Gamma (open body u) T2.
Proof.
  intros L Gamma T1 body T2 u Hbody Hu.
  set (x := fresh_atom (L ++ fv body)).
  assert (Hfresh : ~ In x (L ++ fv body)).
  { unfold x. apply fresh_atom_not_in. }
  apply not_in_app in Hfresh as [HnL HnFv].
  rewrite <- (subst_open_fresh body x u HnFv).
  eapply typing_substitution with (Gamma := update Gamma x T1)
    (Delta := Gamma) (U := T1); eauto.
  unfold context_replaces. split; simpl.
  - now rewrite Nat.eqb_refl.
  - intros y Hneq. assert (Nat.eqb y x = false) as Heq
      by (apply Nat.eqb_neq; exact Hneq).
    now rewrite Heq.
Qed.

Lemma security_le_trans : forall a b c,
  security_le a b -> security_le b c -> security_le a c.
Proof.
  intros a b c [Hr1 Hi1] [Hr2 Hi2]. split;
    eapply flows_to_trans; eauto.
Qed.

Lemma subtype_arrow_inv : forall S T,
  subtype S T -> forall A B kappa,
  T = Ty_Arrow A B kappa ->
  exists A0 B0 kappa0,
    S = Ty_Arrow A0 B0 kappa0 /\
    subtype A A0 /\ subtype B0 B /\ security_le kappa0 kappa.
Proof.
  intros S T H. induction H; intros A B kappa Heq;
    try discriminate.
  - inversion Heq; subst. exists T1, T2, kappa1.
    split; [reflexivity|]. split; [exact H|].
    split; [exact H0|exact H3].
  - destruct (IHsubtype2 _ _ _ Heq) as
      (A1 & B1 & k1 & HU & HA1 & HB1 & HK1).
    destruct (IHsubtype1 _ _ _ HU) as
      (A0 & B0 & k0 & HS & HA0 & HB0 & HK0).
    exists A0, B0, k0. split; [exact HS|].
    split; [eapply S_Trans; eauto|].
    split; [eapply S_Trans; eauto|].
    eapply security_le_trans; eauto.
Qed.

Lemma subtype_sum_inv : forall S T,
  subtype S T -> forall A B kappa,
  T = Ty_Sum A B kappa ->
  exists A0 B0 kappa0,
    S = Ty_Sum A0 B0 kappa0 /\
    subtype A0 A /\ subtype B0 B /\ security_le kappa0 kappa.
Proof.
  intros S T H. induction H; intros A B kappa Heq;
    try discriminate.
  - inversion Heq; subst. exists T1, T2, kappa1.
    split; [reflexivity|]. split; [exact H|].
    split; [exact H0|exact H3].
  - destruct (IHsubtype2 _ _ _ Heq) as
      (A1 & B1 & k1 & HU & HA1 & HB1 & HK1).
    destruct (IHsubtype1 _ _ _ HU) as
      (A0 & B0 & k0 & HS & HA0 & HB0 & HK0).
    exists A0, B0, k0. split; [exact HS|].
    split; [eapply S_Trans; eauto|].
    split; [eapply S_Trans; eauto|].
    eapply security_le_trans; eauto.
Qed.

Lemma subtype_prod_inv : forall S T,
  subtype S T -> forall A B kappa,
  T = Ty_Prod A B kappa ->
  exists A0 B0 kappa0,
    S = Ty_Prod A0 B0 kappa0 /\
    subtype A0 A /\ subtype B0 B /\ security_le kappa0 kappa.
Proof.
  intros S T H. induction H; intros A B kappa Heq;
    try discriminate.
  - inversion Heq; subst. exists T1, T2, kappa1.
    split; [reflexivity|]. split; [exact H|].
    split; [exact H0|exact H3].
  - destruct (IHsubtype2 _ _ _ Heq) as
      (A1 & B1 & k1 & HU & HA1 & HB1 & HK1).
    destruct (IHsubtype1 _ _ _ HU) as
      (A0 & B0 & k0 & HS & HA0 & HB0 & HK0).
    exists A0, B0, k0. split; [exact HS|].
    split; [eapply S_Trans; eauto|].
    split; [eapply S_Trans; eauto|].
    eapply security_le_trans; eauto.
Qed.

Lemma subtype_wf_both : forall T U,
  subtype T U -> wf_ty T /\ wf_ty U.
Proof.
  intros T U H. induction H; simpl in *; intuition.
Qed.

Lemma subtype_wf_right : forall T U,
  subtype T U -> wf_ty U.
Proof. intros T U H; exact (proj2 (subtype_wf_both _ _ H)). Qed.

Lemma wf_security_protect : forall kappa l,
  wf_security kappa -> wf_security (protect_security kappa l).
Proof.
  intros [r i] l H; destruct r, i, l; vm_compute in *; tauto.
Qed.

Lemma wf_ty_protect : forall T l,
  wf_ty T -> wf_ty (ty_protect l T).
Proof.
  intros [] l H; simpl in *; intuition eauto using wf_security_protect.
Qed.

Lemma typing_wf : forall Gamma t T,
  has_type Gamma t T -> wf_ty T.
Proof.
  intros Gamma t T Hty. induction Hty; simpl in *;
    try (repeat split; auto; fail).
  - pose proof (H2 (fresh_atom L) (fresh_atom_not_in L)) as HB.
    repeat split; auto.
  - apply wf_ty_protect. tauto.
  - apply wf_ty_protect. tauto.
  - apply wf_ty_protect. tauto.
  - apply wf_ty_protect.
    pose proof (H1 (fresh_atom L) (fresh_atom_not_in L)) as HB.
    exact HB.
  - apply wf_ty_protect. exact IHHty.
  - eapply subtype_wf_right; eauto.
  - apply wf_ty_protect. exact IHHty2.
Qed.

Lemma subtype_refl : forall T,
  wf_ty T -> subtype T T.
Proof.
  induction T; intros Hwf; simpl in Hwf.
  - apply S_Unit; auto. split; destruct s as [r i]; destruct r, i; vm_compute; tauto.
  - destruct Hwf as [H1 [H2 Hk]].
    apply S_Sum; auto. split; destruct s as [r i]; destruct r, i; vm_compute; tauto.
  - destruct Hwf as [H1 [H2 Hk]].
    apply S_Prod; auto. split; destruct s as [r i]; destruct r, i; vm_compute; tauto.
  - destruct Hwf as [H1 [H2 Hk]].
    apply S_Arrow; auto. split; destruct s as [r i]; destruct r, i; vm_compute; tauto.
Qed.

Lemma security_le_protect : forall a b l,
  security_le a b ->
  security_le (protect_security a l) (protect_security b l).
Proof.
  intros [ar ai] [br bi] l H.
  destruct ar, ai, br, bi, l; vm_compute in *; tauto.
Qed.

Lemma subtype_protect : forall T U l,
  subtype T U -> subtype (ty_protect l T) (ty_protect l U).
Proof.
  intros T U l H. induction H; simpl.
  - apply S_Unit; eauto using wf_security_protect, security_le_protect.
  - apply S_Sum; eauto using wf_security_protect, security_le_protect.
  - apply S_Prod; eauto using wf_security_protect, security_le_protect.
  - apply S_Arrow; eauto using wf_security_protect, security_le_protect.
  - eapply S_Trans; eauto.
Qed.

Lemma typing_abs_inv : forall Gamma t T,
  has_type Gamma t T ->
  forall A body kappa D R kappa',
    t = tm_abs A body kappa ->
    T = Ty_Arrow D R kappa' ->
    exists B L,
      (forall x, ~ In x L ->
        has_type (update Gamma x A) (open body (tm_fvar x)) B) /\
      subtype D A /\ subtype B R /\ security_le kappa kappa'.
Proof.
  intros Gamma t T Hty. induction Hty;
    intros A body0 kterm D R kout Htm HT;
    try discriminate.
  - inversion Htm; inversion HT; subst.
    exists R, L. split; [exact H1|].
    split; [apply subtype_refl; exact H|].
    split.
    + apply subtype_refl.
      pose proof (H1 (fresh_atom L) (fresh_atom_not_in L)) as HB.
      eapply typing_wf; eauto.
    + split; destruct kout as [r i]; destruct r, i; vm_compute; tauto.
  - destruct (subtype_arrow_inv _ _ H _ _ _ HT) as
      (D0 & R0 & k0 & Htype & HD & HR & Hk).
    destruct (IHHty _ _ _ _ _ _ Htm Htype) as
      (B & L & HB & HD0 & HR0 & Hk0).
    exists B, L. split; [exact HB|].
    split; [eapply S_Trans; eauto|].
    split; [eapply S_Trans; eauto|].
    eapply security_le_trans; eauto.
Qed.

Lemma typing_inl_inv : forall Gamma t T,
  has_type Gamma t T -> forall v kappa A B kappa',
  t = tm_inl v kappa -> T = Ty_Sum A B kappa' ->
  has_type Gamma v A /\ security_le kappa kappa'.
Proof.
  intros Gamma t T Hty. induction Hty;
    intros v kterm A B kout Htm HT; try discriminate.
  - inversion Htm; inversion HT; subst. split; auto.
    split; destruct kout as [r i]; destruct r, i; vm_compute; tauto.
  - destruct (subtype_sum_inv _ _ H _ _ _ HT) as
      (A0 & B0 & k0 & Htype & HA & HB & Hk).
    destruct (IHHty _ _ _ _ _ Htm Htype) as [Hv Hk0].
    split.
    + eapply T_Sub; eauto.
    + eapply security_le_trans; eauto.
Qed.

Lemma typing_inr_inv : forall Gamma t T,
  has_type Gamma t T -> forall v kappa A B kappa',
  t = tm_inr v kappa -> T = Ty_Sum A B kappa' ->
  has_type Gamma v B /\ security_le kappa kappa'.
Proof.
  intros Gamma t T Hty. induction Hty;
    intros v kterm A B kout Htm HT; try discriminate.
  - inversion Htm; inversion HT; subst. split; auto.
    split; destruct kout as [r i]; destruct r, i; vm_compute; tauto.
  - destruct (subtype_sum_inv _ _ H _ _ _ HT) as
      (A0 & B0 & k0 & Htype & HA & HB & Hk).
    destruct (IHHty _ _ _ _ _ Htm Htype) as [Hv Hk0].
    split.
    + eapply T_Sub; eauto.
    + eapply security_le_trans; eauto.
Qed.

Lemma typing_pair_inv : forall Gamma t T,
  has_type Gamma t T -> forall a b kappa A B kappa',
  t = tm_pair a b kappa -> T = Ty_Prod A B kappa' ->
  has_type Gamma a A /\ has_type Gamma b B /\
  security_le kappa kappa'.
Proof.
  intros Gamma t T Hty. induction Hty;
    intros a b kterm A B kout Htm HT; try discriminate.
  - inversion Htm; inversion HT; subst.
    split; [assumption|]. split; [assumption|].
    split; destruct kout as [r i]; destruct r, i; vm_compute; tauto.
  - destruct (subtype_prod_inv _ _ H _ _ _ HT) as
      (A0 & B0 & k0 & Htype & HA & HB & Hk).
    destruct (IHHty _ _ _ _ _ _ Htm Htype) as [Ha [Hb Hk0]].
    split; [eapply T_Sub; eauto|].
    split; [eapply T_Sub; eauto|].
    eapply security_le_trans; eauto.
Qed.

Lemma typing_protect_value : forall Gamma v T,
  has_type Gamma v T -> value v -> forall l,
  has_type Gamma (protect_value v l) (ty_protect l T).
Proof.
  intros Gamma v T Hty. induction Hty; intros Hv protect_l;
    try solve [inversion Hv].
  - simpl. apply T_Unit. eauto using wf_security_protect.
  - simpl. eapply T_Abs with (L := L); eauto using wf_security_protect.
  - simpl. eapply T_Pair; eauto using wf_security_protect.
  - simpl. eapply T_Inl; eauto using wf_security_protect.
  - simpl. eapply T_Inr; eauto using wf_security_protect.
  - eapply T_Sub.
    + exact (IHHty Hv protect_l).
    + apply subtype_protect. exact H.
Qed.

Lemma flows_to_refl : forall l, flows_to l l.
Proof. destruct l; exact I. Qed.

Lemma join_monotone : forall a b c d,
  flows_to a b -> flows_to c d ->
  flows_to (join a c) (join b d).
Proof. destruct a, b, c, d; vm_compute; tauto. Qed.

Lemma security_le_protect_levels : forall a b l1 l2,
  security_le a b -> flows_to l1 l2 ->
  security_le (protect_security a l1) (protect_security b l2).
Proof.
  intros a b l1 l2 [Hr Hi] Hl. split; simpl;
    apply join_monotone; auto.
Qed.

Lemma subtype_protect_levels : forall T U,
  subtype T U -> forall l1 l2,
  flows_to l1 l2 ->
  subtype (ty_protect l1 T) (ty_protect l2 U).
Proof.
  intros T U H. induction H; intros l1 l2 Hl; simpl.
  - apply S_Unit; eauto using wf_security_protect, security_le_protect_levels.
  - apply S_Sum; eauto using wf_security_protect, security_le_protect_levels.
  - apply S_Prod; eauto using wf_security_protect, security_le_protect_levels.
  - apply S_Arrow; eauto using wf_security_protect, security_le_protect_levels.
  - eapply S_Trans with (U := ty_protect l1 U).
    + apply IHsubtype1. apply flows_to_refl.
    + apply IHsubtype2. exact Hl.
Qed.

Lemma preservation : forall Gamma t T,
  has_type Gamma t T -> forall t',
  step t t' -> has_type Gamma t' T.
Proof.
  intros Gamma t T Hty. induction Hty; intros t' Hstep;
    inversion Hstep; subst; eauto using has_type.
  - destruct (typing_abs_inv _ _ _ Hty1 _ _ _ _ _ _ eq_refl eq_refl)
      as (B & L & HB & HD & HR & HK).
    assert (Harg : has_type Gamma t2 T).
    { eapply T_Sub; eauto. }
    assert (Hbody : has_type Gamma (open body t2) B).
    { eapply typing_open; eauto. }
    eapply T_Sub.
    + apply T_Protect. exact Hbody.
    + apply subtype_protect_levels; auto. exact (proj2 HK).
  - destruct (typing_pair_inv _ _ _ Hty _ _ _ _ _ _ eq_refl eq_refl)
      as [Hv1 [_ HK]].
    eapply T_Sub.
    + apply T_Protect. exact Hv1.
    + apply subtype_protect_levels.
      * apply subtype_refl. eapply typing_wf; eauto.
      * exact (proj2 HK).
  - destruct (typing_pair_inv _ _ _ Hty _ _ _ _ _ _ eq_refl eq_refl)
      as [_ [Hv2 HK]].
    eapply T_Sub.
    + apply T_Protect. exact Hv2.
    + apply subtype_protect_levels.
      * apply subtype_refl. eapply typing_wf; eauto.
      * exact (proj2 HK).
  - destruct (typing_inl_inv _ _ _ Hty _ _ _ _ _ eq_refl eq_refl)
      as [Hv HK].
    assert (Hbody : has_type Gamma (open body1 v) T).
    { eapply typing_open; eauto. }
    eapply T_Sub.
    + apply T_Protect. exact Hbody.
    + apply subtype_protect_levels.
      * apply subtype_refl. eapply typing_wf; eauto.
      * exact (proj2 HK).
  - destruct (typing_inr_inv _ _ _ Hty _ _ _ _ _ eq_refl eq_refl)
      as [Hv HK].
    assert (Hbody : has_type Gamma (open body2 v) T).
    { eapply typing_open; eauto. }
    eapply T_Sub.
    + apply T_Protect. exact Hbody.
    + apply subtype_protect_levels.
      * apply subtype_refl. eapply typing_wf; eauto.
      * exact (proj2 HK).
  - eapply typing_protect_value; eauto.
  - destruct (typing_inl_inv _ _ _ Hty1 _ _ _ _ _ eq_refl eq_refl)
      as [_ HK].
    eapply T_Sub.
    + apply T_Protect. exact Hty2.
    + apply subtype_protect_levels.
      * apply subtype_refl. eapply typing_wf; eauto.
      * exact (proj2 HK).
  - destruct (typing_inr_inv _ _ _ Hty1 _ _ _ _ _ eq_refl eq_refl)
      as [_ HK].
    eapply T_Sub.
    + apply T_Protect. exact Hty3.
    + apply subtype_protect_levels.
      * apply subtype_refl. eapply typing_wf; eauto.
      * exact (proj2 HK).
Qed.

Lemma multi_preservation : forall Gamma t T v,
  has_type Gamma t T -> multi t v -> has_type Gamma v T.
Proof.
  intros Gamma t T v Hty Hmulti. induction Hmulti; auto.
  apply IHHmulti. eapply preservation; eauto.
Qed.

Lemma hidden_expressions_related : forall observer T t1 t2,
  ~ flows_to (security_of T).(indirect_reader) observer ->
  has_type empty t1 T -> has_type empty t2 T ->
  expression_relation observer T t1 t2.
Proof.
  intros observer T t1 t2 Hhidden Hty1 Hty2.
  unfold expression_relation, expression_lifting.
  repeat split; eauto using underlying_typed_from_type.
  intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
  eapply hidden_values_related; eauto.
  - apply underlying_typed_from_type.
    exact (multi_preservation empty t1 T v1 Hty1 Hm1).
  - apply underlying_typed_from_type.
    exact (multi_preservation empty t2 T v2 Hty2 Hm2).
Qed.

Lemma subst_fresh : forall t x u,
  ~ In x (fv t) -> subst x u t = t.
Proof.
  induction t; intros x u Hfresh; simpl in *;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
      try (intro Hin; apply Hfresh; apply in_or_app; auto);
      auto; reflexivity).
  - assert (x <> a) by (intro Heq; apply Hfresh; left; symmetry; exact Heq).
    apply Nat.eqb_neq in H. now rewrite H.
  - apply not_in_app in Hfresh as [H1 H23].
    apply not_in_app in H23 as [H2 H3].
    rewrite (IHt1 _ _ H1), (IHt2 _ _ H2), (IHt3 _ _ H3). reflexivity.
  - apply not_in_app in Hfresh as [H1 H23].
    apply not_in_app in H23 as [H2 H3].
    rewrite (IHt1 _ _ H1), (IHt2 _ _ H2), (IHt3 _ _ H3). reflexivity.
Qed.

Fixpoint context_fv (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ => context_fv C'
  | C_AppLeft C' t _ | C_PairLeft C' t _ => context_fv C' ++ fv t
  | C_AppRight t C' _ | C_PairRight t C' _ => fv t ++ context_fv C'
  | C_Fst C' _ | C_Snd C' _ | C_Inl C' _ | C_Inr C' _
  | C_Protect _ C' => context_fv C'
  | C_CaseScrutinee C' b1 b2 _ => context_fv C' ++ fv b1 ++ fv b2
  | C_CaseLeft t C' b2 _ => fv t ++ context_fv C' ++ fv b2
  | C_CaseRight t b1 C' _ => fv t ++ fv b1 ++ context_fv C'
  | C_IfCondition C' y n _ => context_fv C' ++ fv y ++ fv n
  | C_IfThen c C' n _ => fv c ++ context_fv C' ++ fv n
  | C_IfElse c y C' _ => fv c ++ fv y ++ context_fv C'
  end.

Lemma subst_plug : forall C x u,
  ~ In x (context_fv C) ->
  subst x u (plug C (tm_fvar x)) = plug C u.
Proof.
  induction C; intros x u Hfresh; simpl in *;
    repeat match goal with
    | H : ~ In _ (_ ++ _) |- _ =>
        apply not_in_app in H as [? ?]
    end;
    simpl;
    try rewrite IHC by assumption;
    repeat rewrite subst_fresh by assumption;
    try rewrite Nat.eqb_refl;
    reflexivity.
Qed.

Lemma typed_plug : forall C T_hole T_result u,
  context_has_type C T_hole T_result ->
  has_type empty u T_hole ->
  has_type empty (plug C u) T_result.
Proof.
  intros C T_hole T_result u [L Hctx] Hu.
  set (x := fresh_atom (L ++ context_fv C)).
  assert (Hfresh : ~ In x (L ++ context_fv C)).
  { unfold x. apply fresh_atom_not_in. }
  apply not_in_app in Hfresh as [HnL HnC].
  rewrite <- (subst_plug C x u HnC).
  eapply typing_substitution with
    (Gamma := update empty x T_hole) (Delta := empty) (U := T_hole).
  - apply Hctx. exact HnL.
  - unfold context_replaces. split; simpl.
    + now rewrite Nat.eqb_refl.
    + intros y Hneq. simpl.
      assert (Nat.eqb y x = false) as Heq by (apply Nat.eqb_neq; exact Hneq).
      now rewrite Heq.
  - exact Hu.
Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof.
  intros T; destruct T as [k|A B k|A B k|A B k];
    destruct k as [r i]; destruct r, i; reflexivity.
Qed.

Lemma typing_protect_low_inv : forall Gamma s T,
  has_type Gamma s T -> forall t,
  s = tm_protect Low t -> has_type Gamma t T.
Proof.
  intros Gamma s T Hty. induction Hty; intros u Heq; try discriminate.
  - inversion Heq; subst. rewrite ty_protect_low. exact Hty.
  - eapply T_Sub; eauto.
Qed.

Inductive erased_step : tm -> tm -> Prop :=
  | E_AppAbs : forall A body v,
      value (tm_abs A body public) -> value v ->
      erased_step (tm_app (tm_abs A body public) v Low) (open body v)
  | E_App1 : forall t t' u,
      erased_step t t' -> erased_step (tm_app t u Low) (tm_app t' u Low)
  | E_App2 : forall v u u',
      value v -> erased_step u u' ->
      erased_step (tm_app v u Low) (tm_app v u' Low)
  | E_Pair1 : forall t t' u,
      erased_step t t' ->
      erased_step (tm_pair t u public) (tm_pair t' u public)
  | E_Pair2 : forall v u u',
      value v -> erased_step u u' ->
      erased_step (tm_pair v u public) (tm_pair v u' public)
  | E_FstPair : forall a b,
      value a -> value b ->
      erased_step (tm_fst (tm_pair a b public) Low) a
  | E_Fst : forall t t',
      erased_step t t' -> erased_step (tm_fst t Low) (tm_fst t' Low)
  | E_SndPair : forall a b,
      value a -> value b ->
      erased_step (tm_snd (tm_pair a b public) Low) b
  | E_Snd : forall t t',
      erased_step t t' -> erased_step (tm_snd t Low) (tm_snd t' Low)
  | E_Inl : forall t t',
      erased_step t t' ->
      erased_step (tm_inl t public) (tm_inl t' public)
  | E_Inr : forall t t',
      erased_step t t' ->
      erased_step (tm_inr t public) (tm_inr t' public)
  | E_CaseLeft : forall v yes no,
      value v ->
      erased_step (tm_case (tm_inl v public) yes no Low) (open yes v)
  | E_CaseRight : forall v yes no,
      value v ->
      erased_step (tm_case (tm_inr v public) yes no Low) (open no v)
  | E_Case : forall t t' yes no,
      erased_step t t' ->
      erased_step (tm_case t yes no Low) (tm_case t' yes no Low)
  | E_IfTrue : forall v yes no,
      value v -> erased_step (tm_if (tm_inl v public) yes no Low) yes
  | E_IfFalse : forall v yes no,
      value v -> erased_step (tm_if (tm_inr v public) yes no Low) no
  | E_If : forall c c' yes no,
      erased_step c c' ->
      erased_step (tm_if c yes no Low) (tm_if c' yes no Low).

Lemma typed_unprotect_low : forall Gamma t T u,
  has_type Gamma t T ->
  step t (tm_protect Low u) -> has_type Gamma u T.
Proof.
  intros Gamma t T u Hty Hstep.
  eapply typing_protect_low_inv.
  - eapply preservation; eauto.
  - reflexivity.
Qed.

Lemma erased_step_preservation : forall Gamma t T,
  has_type Gamma t T -> forall t',
  erased_step t t' -> has_type Gamma t' T.
Proof.
  intros Gamma t T Hty. induction Hty; intros t' He;
    inversion He; subst; eauto using has_type.
  - eapply typed_unprotect_low.
    + eapply T_App; eauto.
    + eapply ST_AppAbs; eauto. vm_compute; exact I.
  - eapply typed_unprotect_low.
    + eapply T_Fst; eauto.
    + eapply ST_FstPair; eauto. vm_compute; exact I.
  - eapply typed_unprotect_low.
    + eapply T_Snd; eauto.
    + eapply ST_SndPair; eauto. vm_compute; exact I.
  - eapply typed_unprotect_low.
    + eapply T_Case with (L := L) (T1 := T1)
        (T2 := T2) (kappa := kappa); eauto.
    + eapply ST_CaseLeft; eauto. vm_compute; exact I.
  - eapply typed_unprotect_low.
    + eapply T_Case with (L := L) (T1 := T1)
        (T2 := T2) (kappa := kappa); eauto.
    + eapply ST_CaseRight; eauto. vm_compute; exact I.
  - eapply typed_unprotect_low with
      (t := tm_if (tm_inl v public) t' no Low).
    + eapply T_If with (k := k); eauto.
    + eapply ST_IfTrue; eauto. vm_compute; exact I.
  - eapply typed_unprotect_low.
    + eapply T_If; eauto.
    + eapply ST_IfFalse; eauto. vm_compute; exact I.
Qed.

Lemma erase_step_simulation : forall t t',
  step t t' ->
  erase_security t = erase_security t' \/
  erased_step (erase_security t) (erase_security t').
Proof.
  intros t t' Hstep. induction Hstep; simpl;
    try solve [destruct IHHstep as [Heq|Hs];
      [left; now rewrite Heq|right; eauto using erased_step, value_erase]].
  - right. rewrite erase_open. apply E_AppAbs.
    + exact (value_erase _ H).
    + exact (value_erase _ H0).
  - right. apply E_FstPair; apply value_erase; assumption.
  - right. apply E_SndPair; apply value_erase; assumption.
  - right. rewrite erase_open. apply E_CaseLeft.
    apply value_erase. assumption.
  - right. rewrite erase_open. apply E_CaseRight.
    apply value_erase. assumption.
  - left. symmetry. now apply erase_protect_value.
  - right. apply E_IfTrue. apply value_erase. assumption.
  - right. apply E_IfFalse. apply value_erase. assumption.
Qed.

Lemma underlying_step_preservation : forall T t t',
  underlying_typed T t -> step t t' -> underlying_typed T t'.
Proof.
  intros T t t' Htyped Hstep.
  unfold underlying_typed in *.
  destruct (erase_step_simulation _ _ Hstep) as [Heq|Hs].
  - rewrite <- Heq. exact Htyped.
  - eapply erased_step_preservation; eauto.
Qed.

Lemma underlying_multi_preservation : forall T t v,
  underlying_typed T t -> multi t v -> underlying_typed T v.
Proof.
  intros T t v Htyped Hmulti. induction Hmulti; auto.
  apply IHHmulti. eapply underlying_step_preservation; eauto.
Qed.

Fixpoint instantiate (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit k => tm_unit k
  | tm_abs A body k => tm_abs A (instantiate rho body) k
  | tm_app a b r => tm_app (instantiate rho a) (instantiate rho b) r
  | tm_pair a b k => tm_pair (instantiate rho a) (instantiate rho b) k
  | tm_fst a r => tm_fst (instantiate rho a) r
  | tm_snd a r => tm_snd (instantiate rho a) r
  | tm_inl a k => tm_inl (instantiate rho a) k
  | tm_inr a k => tm_inr (instantiate rho a) k
  | tm_case c a b r => tm_case (instantiate rho c)
      (instantiate rho a) (instantiate rho b) r
  | tm_protect l a => tm_protect l (instantiate rho a)
  | tm_if c a b r => tm_if (instantiate rho c)
      (instantiate rho a) (instantiate rho b) r
  end.

Definition extend_env (rho : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else rho y.

Lemma instantiate_open_rec : forall body k rho x u,
  ~ In x (fv body) ->
  (forall y, locally_closed (rho y)) ->
  instantiate (extend_env rho x u) (open_rec k (tm_fvar x) body) =
  open_rec k u (instantiate rho body).
Proof.
  induction body; intros k rho x u Hfresh Hlc; simpl in *;
    try (rewrite ?IHbody, ?IHbody1, ?IHbody2, ?IHbody3;
      try (intro Hin; apply Hfresh; apply in_or_app; auto);
      auto; reflexivity).
  - destruct (Nat.eqb k n); simpl.
    + unfold extend_env. now rewrite Nat.eqb_refl.
    + reflexivity.
  - assert (x <> a) by (intro Heq; apply Hfresh; left; symmetry; exact Heq).
    assert (Nat.eqb x a = false) as Heq by (apply Nat.eqb_neq; exact H).
    unfold extend_env. rewrite Heq.
    symmetry. apply open_rec_above_lc with (k := 0).
    + exact (Hlc a).
    + lia.
  - apply not_in_app in Hfresh as [H1 H23].
    apply not_in_app in H23 as [H2 H3].
    rewrite (IHbody1 k rho x u H1 Hlc),
      (IHbody2 (S k) rho x u H2 Hlc),
      (IHbody3 (S k) rho x u H3 Hlc). reflexivity.
  - apply not_in_app in Hfresh as [H1 H23].
    apply not_in_app in H23 as [H2 H3].
    rewrite (IHbody1 k rho x u H1 Hlc),
      (IHbody2 k rho x u H2 Hlc),
      (IHbody3 k rho x u H3 Hlc). reflexivity.
Qed.

Lemma instantiate_open : forall body rho x u,
  ~ In x (fv body) ->
  (forall y, locally_closed (rho y)) ->
  instantiate (extend_env rho x u) (open body (tm_fvar x)) =
  open (instantiate rho body) u.
Proof. intros; unfold open; apply instantiate_open_rec; auto. Qed.

Definition env_erased_typed (Gamma Delta : context) (rho : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    has_type Delta (erase_security (rho x)) (erase_type T).

Definition env_locally_closed (rho : atom -> tm) : Prop :=
  forall x, locally_closed (rho x).

Lemma extend_env_lc : forall rho x u,
  env_locally_closed rho -> locally_closed u ->
  env_locally_closed (extend_env rho x u).
Proof.
  intros rho x u Hrho Hu y. unfold extend_env.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma extend_env_erased_typed : forall Gamma Delta rho x A,
  env_erased_typed Gamma Delta rho ->
  lookup_context x Delta = None ->
  env_erased_typed (update Gamma x A)
    (update Delta x (erase_type A))
    (extend_env rho x (tm_fvar x)).
Proof.
  intros Gamma Delta rho x A Henv Hfresh y T Hlook.
  unfold extend_env. simpl in Hlook.
  destruct (Nat.eqb y x) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst.
    inversion Hlook; subst. rewrite Nat.eqb_refl. simpl. apply T_Var.
    + simpl. now rewrite Nat.eqb_refl.
    + apply wf_erase_type.
  - assert (Nat.eqb x y = false) as Heq' by
      (rewrite Nat.eqb_sym; exact Heq).
    rewrite Heq'.
    eapply typing_context_extends.
    + apply Henv. exact Hlook.
    + apply context_extends_update_fresh. exact Hfresh.
Qed.

Lemma instantiate_erased_typing : forall Gamma t T,
  has_type Gamma t T -> forall Delta rho,
  env_erased_typed Gamma Delta rho -> env_locally_closed rho ->
  has_type Delta (erase_security (instantiate rho t)) (erase_type T).
Proof.
  intros Gamma t T Hty. induction Hty; intros Delta rho Henv Hlc; simpl.
  - apply Henv. exact H.
  - apply T_Unit. vm_compute; exact I.
  - eapply T_Abs with (L := L ++ fv body ++ map fst Delta);
      eauto using wf_erase_type.
    + vm_compute; exact I.
    + intros x Hfresh.
      apply not_in_app in Hfresh as [HnL Htail].
      apply not_in_app in Htail as [HnFv HnDom].
      specialize (H2 x HnL (update Delta x (erase_type T1))
        (extend_env rho x (tm_fvar x))).
      assert (Hen : env_erased_typed (update Gamma x T1)
        (update Delta x (erase_type T1))
        (extend_env rho x (tm_fvar x))).
      { apply extend_env_erased_typed; auto.
        apply lookup_not_in_domain. exact HnDom. }
      assert (Hlc' : env_locally_closed (extend_env rho x (tm_fvar x))).
      { apply extend_env_lc; auto. exact I. }
      specialize (H2 Hen Hlc').
      rewrite instantiate_open in H2 by (auto using Hlc).
      rewrite erase_open in H2. simpl in H2. exact H2.
  - rewrite erase_type_protect.
    rewrite <- protect_erased_type.
    eapply T_App with (T1 := erase_type T1) (kappa := public);
      eauto. vm_compute; exact I.
  - eapply T_Pair; eauto. vm_compute; exact I.
  - rewrite erase_type_protect.
    rewrite <- protect_erased_type.
    eapply T_Fst with (T2 := erase_type T2) (kappa := public);
      eauto. vm_compute; exact I.
  - rewrite erase_type_protect.
    rewrite <- protect_erased_type.
    eapply T_Snd with (T1 := erase_type T1) (kappa := public);
      eauto. vm_compute; exact I.
  - eapply T_Inl with (T2 := erase_type T2); eauto using wf_erase_type.
    vm_compute; exact I.
  - eapply T_Inr with (T1 := erase_type T1); eauto using wf_erase_type.
    vm_compute; exact I.
  - rewrite erase_type_protect.
    rewrite <- protect_erased_type.
    eapply T_Case with
      (L := L ++ fv body1 ++ fv body2 ++ map fst Delta)
      (T1 := erase_type T1) (T2 := erase_type T2) (kappa := public).
    + exact (IHHty Delta rho Henv Hlc).
    + vm_compute; exact I.
    + intros x Hfresh.
      apply not_in_app in Hfresh as [HnL Htail].
      apply not_in_app in Htail as [HnFv Htail].
      apply not_in_app in Htail as [_ HnDom].
      specialize (H1 x HnL (update Delta x (erase_type T1))
        (extend_env rho x (tm_fvar x))).
      assert (Hen : env_erased_typed (update Gamma x T1)
        (update Delta x (erase_type T1))
        (extend_env rho x (tm_fvar x))).
      { apply extend_env_erased_typed; auto.
        apply lookup_not_in_domain. exact HnDom. }
      assert (Hlc' : env_locally_closed (extend_env rho x (tm_fvar x))).
      { apply extend_env_lc; auto. exact I. }
      specialize (H1 Hen Hlc').
      rewrite instantiate_open in H1 by (auto using Hlc).
      rewrite erase_open in H1. simpl in H1. exact H1.
    + intros x Hfresh.
      apply not_in_app in Hfresh as [HnL Htail].
      apply not_in_app in Htail as [_ Htail].
      apply not_in_app in Htail as [HnFv HnDom].
      specialize (H3 x HnL (update Delta x (erase_type T2))
        (extend_env rho x (tm_fvar x))).
      assert (Hen : env_erased_typed (update Gamma x T2)
        (update Delta x (erase_type T2))
        (extend_env rho x (tm_fvar x))).
      { apply extend_env_erased_typed; auto.
        apply lookup_not_in_domain. exact HnDom. }
      assert (Hlc' : env_locally_closed (extend_env rho x (tm_fvar x))).
      { apply extend_env_lc; auto. exact I. }
      specialize (H3 Hen Hlc').
      rewrite instantiate_open in H3 by (auto using Hlc).
      rewrite erase_open in H3. simpl in H3. exact H3.
  - rewrite erase_type_protect. exact (IHHty Delta rho Henv Hlc).
  - eapply T_Sub; eauto using erase_type_subtype.
  - rewrite erase_type_protect.
    rewrite <- protect_erased_type.
    eapply T_If with (k := public); eauto.
    vm_compute; exact I.
Qed.

Lemma protect_value_is_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l Hv. inversion Hv; subst; simpl; eauto using value.
Qed.

Inductive big_eval : tm -> tm -> Prop :=
  | BE_Unit : forall k, big_eval (tm_unit k) (tm_unit k)
  | BE_Abs : forall A body k,
      locally_closed (tm_abs A body k) ->
      big_eval (tm_abs A body k) (tm_abs A body k)
  | BE_Pair : forall a b va vb k,
      big_eval a va -> big_eval b vb ->
      big_eval (tm_pair a b k) (tm_pair va vb k)
  | BE_Inl : forall t v k,
      big_eval t v -> big_eval (tm_inl t k) (tm_inl v k)
  | BE_Inr : forall t v k,
      big_eval t v -> big_eval (tm_inr t k) (tm_inr v k)
  | BE_App : forall f a A body k r va w,
      big_eval f (tm_abs A body k) ->
      big_eval a va -> big_eval (open body va) w ->
      flows_to k.(reader) r ->
      big_eval (tm_app f a r) (protect_value w k.(indirect_reader))
  | BE_Fst : forall t a b k r,
      big_eval t (tm_pair a b k) -> flows_to k.(reader) r ->
      big_eval (tm_fst t r) (protect_value a k.(indirect_reader))
  | BE_Snd : forall t a b k r,
      big_eval t (tm_pair a b k) -> flows_to k.(reader) r ->
      big_eval (tm_snd t r) (protect_value b k.(indirect_reader))
  | BE_CaseLeft : forall t v k yes no r w,
      big_eval t (tm_inl v k) -> big_eval (open yes v) w ->
      flows_to k.(reader) r ->
      big_eval (tm_case t yes no r) (protect_value w k.(indirect_reader))
  | BE_CaseRight : forall t v k yes no r w,
      big_eval t (tm_inr v k) -> big_eval (open no v) w ->
      flows_to k.(reader) r ->
      big_eval (tm_case t yes no r) (protect_value w k.(indirect_reader))
  | BE_Protect : forall t v l,
      big_eval t v ->
      big_eval (tm_protect l t) (protect_value v l)
  | BE_IfTrue : forall c v k yes no r w,
      big_eval c (tm_inl v k) -> big_eval yes w ->
      flows_to k.(reader) r ->
      big_eval (tm_if c yes no r) (protect_value w k.(indirect_reader))
  | BE_IfFalse : forall c v k yes no r w,
      big_eval c (tm_inr v k) -> big_eval no w ->
      flows_to k.(reader) r ->
      big_eval (tm_if c yes no r) (protect_value w k.(indirect_reader)).

Lemma big_eval_value : forall t v,
  big_eval t v -> value v.
Proof.
  intros t v H. induction H; eauto using value, protect_value_is_value.
  - apply protect_value_is_value.
    inversion IHbig_eval; assumption.
  - apply protect_value_is_value.
    inversion IHbig_eval; assumption.
Qed.

Lemma big_eval_value_refl : forall v,
  value v -> big_eval v v.
Proof.
  intros v Hv. induction Hv; eauto using big_eval.
Qed.

Lemma big_eval_of_value : forall v w,
  value v -> big_eval v w -> w = v.
Proof.
  intros v w Hv. revert w. induction Hv; intros w Hbig;
    inversion Hbig; subst; auto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma step_big_eval_backward : forall t t',
  step t t' -> forall w,
  big_eval t' w -> big_eval t w.
Proof.
  intros t t' Hstep. induction Hstep; intros w Hbig;
    try (assert (w = protect_value v l) as -> by
      (eapply big_eval_of_value; [apply protect_value_is_value; eauto|exact Hbig]);
      apply BE_Protect; apply big_eval_value_refl; assumption);
    inversion Hbig; subst; eauto using big_eval.
  - eapply BE_App; eauto using big_eval_value_refl.
  - pose proof (big_eval_of_value _ _ H H5) as ->.
    eapply BE_Fst; eauto using big_eval_value_refl, value.
  - pose proof (big_eval_of_value _ _ H0 H5) as ->.
    eapply BE_Snd; eauto using big_eval_value_refl, value.
  - eapply BE_CaseLeft; eauto using big_eval_value_refl, value.
  - eapply BE_CaseRight; eauto using big_eval_value_refl, value.
  - eapply BE_IfTrue; eauto using big_eval_value_refl, value.
  - eapply BE_IfFalse; eauto using big_eval_value_refl, value.
Qed.

Lemma evaluates_big_eval : forall t v,
  evaluates t v -> big_eval t v.
Proof.
  intros t v [Hm Hv]. induction Hm.
  - apply big_eval_value_refl. exact Hv.
  - eapply step_big_eval_backward; eauto.
Qed.

Lemma multi_trans : forall a b c,
  multi a b -> multi b c -> multi a c.
Proof.
  intros a b c Hab Hbc. induction Hab; eauto using multi.
Qed.

Lemma multi_lift : forall (F : tm -> tm) a b,
  (forall x y, step x y -> step (F x) (F y)) ->
  multi a b -> multi (F a) (F b).
Proof.
  intros F a b Hstep Hmulti. induction Hmulti;
    eauto using multi.
Qed.

Lemma multi_one : forall a b, step a b -> multi a b.
Proof. intros a b H; eapply multi_step; eauto using multi. Qed.

Lemma big_eval_multi : forall t v,
  big_eval t v -> multi t v.
Proof.
  intros t v Hbig. induction Hbig; eauto using multi.
  - eapply multi_trans.
    + eapply multi_lift with (F := fun x => tm_pair x b k);
        eauto using step.
    + eapply multi_lift with (F := fun x => tm_pair va x k).
      * intros x y Hs. apply ST_Pair2;
          eauto using big_eval_value.
      * exact IHHbig2.
  - eapply multi_lift with (F := fun x => tm_inl x k);
      eauto using step.
  - eapply multi_lift with (F := fun x => tm_inr x k);
      eauto using step.
  - eapply multi_trans with
      (b := tm_app (tm_abs A body k) a r).
    + eapply multi_lift with (F := fun x => tm_app x a r);
        eauto using step.
    + eapply multi_trans with
        (b := tm_app (tm_abs A body k) va r).
      * eapply multi_lift with
          (F := fun x => tm_app (tm_abs A body k) x r).
        -- intros x y Hs. apply ST_App2;
             eauto using big_eval_value.
        -- exact IHHbig2.
      * eapply multi_trans with
          (b := tm_protect k.(indirect_reader) (open body va)).
        -- apply multi_one. apply ST_AppAbs;
             eauto using big_eval_value.
        -- eapply multi_trans with
            (b := tm_protect k.(indirect_reader) w).
           ++ eapply multi_lift with
                (F := fun x => tm_protect k.(indirect_reader) x);
                eauto using step.
           ++ apply multi_one. apply ST_ProtectValue.
              eapply big_eval_value; eauto.
  - eapply multi_trans with (b := tm_fst (tm_pair a b k) r).
    + eapply multi_lift with (F := fun x => tm_fst x r);
        eauto using step.
    + eapply multi_trans with
        (b := tm_protect k.(indirect_reader) a).
      * apply multi_one. apply ST_FstPair.
        -- pose proof (big_eval_value _ _ Hbig) as Hv; inversion Hv; assumption.
        -- pose proof (big_eval_value _ _ Hbig) as Hv; inversion Hv; assumption.
        -- exact H.
      * apply multi_one. apply ST_ProtectValue.
        pose proof (big_eval_value _ _ Hbig) as Hv; inversion Hv; assumption.
  - eapply multi_trans with (b := tm_snd (tm_pair a b k) r).
    + eapply multi_lift with (F := fun x => tm_snd x r);
        eauto using step.
    + eapply multi_trans with
        (b := tm_protect k.(indirect_reader) b).
      * apply multi_one. apply ST_SndPair.
        -- pose proof (big_eval_value _ _ Hbig) as Hv; inversion Hv; assumption.
        -- pose proof (big_eval_value _ _ Hbig) as Hv; inversion Hv; assumption.
        -- exact H.
      * apply multi_one. apply ST_ProtectValue.
        pose proof (big_eval_value _ _ Hbig) as Hv; inversion Hv; assumption.
  - eapply multi_trans with
      (b := tm_case (tm_inl v k) yes no r).
    + eapply multi_lift with
        (F := fun x => tm_case x yes no r); eauto using step.
    + eapply multi_trans with
        (b := tm_protect k.(indirect_reader) (open yes v)).
      * apply multi_one. apply ST_CaseLeft.
        -- pose proof (big_eval_value _ _ Hbig1) as Hv; inversion Hv; assumption.
        -- exact H.
      * eapply multi_trans with
          (b := tm_protect k.(indirect_reader) w).
        -- eapply multi_lift with
             (F := fun x => tm_protect k.(indirect_reader) x);
             eauto using step.
        -- apply multi_one. apply ST_ProtectValue.
           eapply big_eval_value; eauto.
  - eapply multi_trans with
      (b := tm_case (tm_inr v k) yes no r).
    + eapply multi_lift with
        (F := fun x => tm_case x yes no r); eauto using step.
    + eapply multi_trans with
        (b := tm_protect k.(indirect_reader) (open no v)).
      * apply multi_one. apply ST_CaseRight.
        -- pose proof (big_eval_value _ _ Hbig1) as Hv; inversion Hv; assumption.
        -- exact H.
      * eapply multi_trans with
          (b := tm_protect k.(indirect_reader) w).
        -- eapply multi_lift with
             (F := fun x => tm_protect k.(indirect_reader) x);
             eauto using step.
        -- apply multi_one. apply ST_ProtectValue.
           eapply big_eval_value; eauto.
  - eapply multi_trans with (b := tm_protect l v).
    + eapply multi_lift with (F := fun x => tm_protect l x);
        eauto using step.
    + apply multi_one. apply ST_ProtectValue.
      eapply big_eval_value; eauto.
  - eapply multi_trans with
      (b := tm_if (tm_inl v k) yes no r).
    + eapply multi_lift with (F := fun x => tm_if x yes no r);
        eauto using step.
    + eapply multi_trans with (b := tm_protect k.(indirect_reader) yes).
      * apply multi_one. apply ST_IfTrue.
        -- pose proof (big_eval_value _ _ Hbig1) as Hv; inversion Hv; assumption.
        -- exact H.
      * eapply multi_trans with (b := tm_protect k.(indirect_reader) w).
        -- eapply multi_lift with
             (F := fun x => tm_protect k.(indirect_reader) x);
             eauto using step.
        -- apply multi_one. apply ST_ProtectValue.
           eapply big_eval_value; eauto.
  - eapply multi_trans with
      (b := tm_if (tm_inr v k) yes no r).
    + eapply multi_lift with (F := fun x => tm_if x yes no r);
        eauto using step.
    + eapply multi_trans with (b := tm_protect k.(indirect_reader) no).
      * apply multi_one. apply ST_IfFalse.
        -- pose proof (big_eval_value _ _ Hbig1) as Hv; inversion Hv; assumption.
        -- exact H.
      * eapply multi_trans with (b := tm_protect k.(indirect_reader) w).
        -- eapply multi_lift with
             (F := fun x => tm_protect k.(indirect_reader) x);
             eauto using step.
        -- apply multi_one. apply ST_ProtectValue.
           eapply big_eval_value; eauto.
Qed.

Lemma big_eval_evaluates : forall t v,
  big_eval t v -> evaluates t v.
Proof.
  intros t v H. split.
  - apply big_eval_multi. exact H.
  - apply big_eval_value with (t := t). exact H.
Qed.

Lemma underlying_subtype : forall T U v,
  subtype T U -> underlying_typed T v -> underlying_typed U v.
Proof.
  intros T U v Hsub Hty. unfold underlying_typed in *.
  eapply T_Sub; eauto using erase_type_subtype.
Qed.

Lemma value_relation_subtype : forall T U,
  subtype T U -> forall observer v1 v2,
  value_relation observer T v1 v2 ->
  value_relation observer U v1 v2.
Proof.
  intros T U Hsub. induction Hsub;
    intros observer v1 v2 Hrel.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    simpl in *. split; [exact Hv1|]. split; [exact Hv2|].
    split; [eapply underlying_subtype with (T := Ty_Unit kappa1);
      [apply S_Unit; assumption|exact Ht1]|].
    split; [eapply underlying_subtype with (T := Ty_Unit kappa1);
      [apply S_Unit; assumption|exact Ht2]|].
    intros Hvisible.
    apply Hshape. exact (flows_to_trans _ _ _ (proj2 H1) Hvisible).
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    simpl in *. split; [exact Hv1|]. split; [exact Hv2|].
    split; [eapply underlying_subtype with
      (T := Ty_Sum T1 T2 kappa1); [apply S_Sum; assumption|exact Ht1]|].
    split; [eapply underlying_subtype with
      (T := Ty_Sum T1 T2 kappa1); [apply S_Sum; assumption|exact Ht2]|].
    intros Hvisible.
    specialize (Hshape (flows_to_trans _ _ _ (proj2 H1) Hvisible)).
    destruct Hshape as [[a1 [a2 [k1 [k2 [-> [-> Hr]]]]]] |
                        [a1 [a2 [k1 [k2 [-> [-> Hr]]]]]]].
    + left. do 4 eexists. repeat split; eauto.
    + right. do 4 eexists. repeat split; eauto.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    simpl in *. split; [exact Hv1|]. split; [exact Hv2|].
    split; [eapply underlying_subtype with
      (T := Ty_Prod T1 T2 kappa1); [apply S_Prod; assumption|exact Ht1]|].
    split; [eapply underlying_subtype with
      (T := Ty_Prod T1 T2 kappa1); [apply S_Prod; assumption|exact Ht2]|].
    intros Hvisible.
    specialize (Hshape (flows_to_trans _ _ _ (proj2 H1) Hvisible)).
    destruct Hshape as (a1 & b1 & a2 & b2 & k1 & k2 & -> & -> & Ha & Hb).
    do 6 eexists. repeat split; eauto.
  - destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    simpl in *. split; [exact Hv1|]. split; [exact Hv2|].
    split; [eapply underlying_subtype with
      (T := Ty_Arrow T1 T2 kappa1); [apply S_Arrow; assumption|exact Ht1]|].
    split; [eapply underlying_subtype with
      (T := Ty_Arrow T1 T2 kappa1); [apply S_Arrow; assumption|exact Ht2]|].
    intros Hvisible.
    specialize (Hshape (flows_to_trans _ _ _ (proj2 H1) Hvisible)).
    destruct Hshape as (A1 & A2 & body1 & body2 & k1 & k2 & Heq1 & Heq2 & Hfn).
    do 6 eexists. repeat split; eauto.
    intros arg1 arg2 Harg w1 w2 Hew1 Hew2.
    eapply IHHsub2.
    eapply Hfn; eauto using IHHsub1.
  - eapply IHHsub2. eapply IHHsub1. exact Hrel.
Qed.

Lemma expression_relation_subtype : forall observer T U t1 t2,
  subtype T U ->
  expression_relation observer T t1 t2 ->
  expression_relation observer U t1 t2.
Proof.
  intros observer T U t1 t2 Hsub [Ht1 [Ht2 Hlift]].
  unfold expression_relation, expression_lifting in *.
  repeat split; eauto using underlying_subtype.
  intros v1 v2 He1 He2.
  eapply value_relation_subtype; eauto.
Qed.

Lemma protect_value_low : forall v,
  value v -> protect_value v Low = v.
Proof.
  intros v Hv. inversion Hv; subst; simpl;
    destruct kappa as [r i]; destruct r, i; reflexivity.
Qed.

Lemma protect_value_compose : forall v l1 l2,
  value v ->
  protect_value (protect_value v l1) l2 =
  protect_value v (join l1 l2).
Proof.
  intros v l1 l2 Hv.
  inversion Hv; subst; simpl;
    destruct l1, l2; destruct kappa as [r i];
    destruct r, i; reflexivity.
Qed.

Lemma erase_protect_any : forall v l,
  value v -> erase_security (protect_value v l) = erase_security v.
Proof. apply erase_protect_value. Qed.

Lemma big_eval_app_values_inv : forall A body k arg w,
  value (tm_abs A body k) -> value arg ->
  big_eval (tm_app (tm_abs A body k) arg High) w ->
  exists u, big_eval (open body arg) u /\
    w = protect_value u k.(indirect_reader).
Proof.
  intros A body k arg w Habs Harg Hbig.
  inversion Hbig; subst.
  assert (Hfun : tm_abs A0 body0 k0 = tm_abs A body k).
  { eapply big_eval_of_value; eauto. }
  inversion Hfun; subst.
  assert (Hva : va = arg).
  { eapply big_eval_of_value; eauto. }
  subst. eexists. split; eauto.
Qed.

Lemma related_values_are_values : forall observer T v1 v2,
  value_relation observer T v1 v2 -> value v1 /\ value v2.
Proof.
  intros observer [] v1 v2 H; simpl in H; tauto.
Qed.

Lemma value_relation_protect_same : forall T observer v1 v2 l1 l2,
  value_relation observer T v1 v2 ->
  value_relation observer T
    (protect_value v1 l1) (protect_value v2 l2).
Proof.
  induction T; intros observer v1 v2 l1 l2 Hrel;
    destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]]; simpl.
  - split; [apply protect_value_is_value; exact Hv1|].
    split; [apply protect_value_is_value; exact Hv2|].
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value by exact Hv1.
      exact Ht1. }
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value by exact Hv2.
      exact Ht2. }
    intros Hvisible. specialize (Hshape Hvisible).
    destruct Hshape as (k1 & k2 & -> & ->).
    exists (protect_security k1 l1), (protect_security k2 l2).
    auto.
  - split; [apply protect_value_is_value; exact Hv1|].
    split; [apply protect_value_is_value; exact Hv2|].
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value by exact Hv1.
      exact Ht1. }
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value by exact Hv2.
      exact Ht2. }
    intros Hvisible. specialize (Hshape Hvisible).
    destruct Hshape as [[a1 [a2 [k1 [k2 [-> [-> Hr]]]]]] |
                        [a1 [a2 [k1 [k2 [-> [-> Hr]]]]]]].
    + left. exists a1, a2, (protect_security k1 l1),
        (protect_security k2 l2). auto.
    + right. exists a1, a2, (protect_security k1 l1),
        (protect_security k2 l2). auto.
  - split; [apply protect_value_is_value; exact Hv1|].
    split; [apply protect_value_is_value; exact Hv2|].
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value by exact Hv1.
      exact Ht1. }
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value by exact Hv2.
      exact Ht2. }
    intros Hvisible. specialize (Hshape Hvisible).
    destruct Hshape as (a1 & b1 & a2 & b2 & k1 & k2 & -> & -> & Ha & Hb).
    exists a1, b1, a2, b2, (protect_security k1 l1),
      (protect_security k2 l2). auto.
  - split; [apply protect_value_is_value; exact Hv1|].
    split; [apply protect_value_is_value; exact Hv2|].
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value by exact Hv1.
      exact Ht1. }
    split.
    { unfold underlying_typed in *. rewrite erase_protect_value by exact Hv2.
      exact Ht2. }
    intros Hvisible. specialize (Hshape Hvisible).
    destruct Hshape as (A1 & A2 & body1 & body2 & k1 & k2 & -> & -> & Hfn).
    exists A1, A2, body1, body2,
      (protect_security k1 l1), (protect_security k2 l2).
    split; [reflexivity|]. split; [reflexivity|].
    intros arg1 arg2 Harg w1 w2 Hew1 Hew2.
    destruct (big_eval_app_values_inv _ _ _ _ _
      (protect_value_is_value _ l1 Hv1)
      (proj1 (related_values_are_values _ _ _ _ Harg))
      (evaluates_big_eval _ _ Hew1)) as (u1 & Hbody1 & Hw1).
    destruct (big_eval_app_values_inv _ _ _ _ _
      (protect_value_is_value _ l2 Hv2)
      (proj2 (related_values_are_values _ _ _ _ Harg))
      (evaluates_big_eval _ _ Hew2)) as (u2 & Hbody2 & Hw2).
    subst w1 w2.
    assert (Hu1 : value u1) by (eapply big_eval_value; eauto).
    assert (Hu2 : value u2) by (eapply big_eval_value; eauto).
    simpl. rewrite <- (protect_value_compose u1 k1.(indirect_reader) l1 Hu1).
    rewrite <- (protect_value_compose u2 k2.(indirect_reader) l2 Hu2).
    apply IHT2.
    eapply Hfn; eauto.
    + apply big_eval_evaluates.
      eapply BE_App with (va := arg1) (w := u1).
      * apply big_eval_value_refl. exact Hv1.
      * apply big_eval_value_refl.
        exact (proj1 (related_values_are_values _ _ _ _ Harg)).
      * exact Hbody1.
      * destruct (reader k1); exact I.
    + apply big_eval_evaluates.
      eapply BE_App with (va := arg2) (w := u2).
      * apply big_eval_value_refl. exact Hv2.
      * apply big_eval_value_refl.
        exact (proj2 (related_values_are_values _ _ _ _ Harg)).
      * exact Hbody2.
      * destruct (reader k2); exact I.
Qed.

Lemma flows_to_join_left : forall a b c,
  flows_to (join a b) c -> flows_to a c.
Proof. destruct a, b, c; vm_compute; tauto. Qed.

Lemma value_relation_ty_protect : forall T observer v1 v2 l,
  value_relation observer T v1 v2 ->
  value_relation observer (ty_protect l T) v1 v2.
Proof.
  intros T observer v1 v2 l Hrel.
  destruct T; simpl in *;
    destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
  all: split; [exact Hv1|].
  all: split; [exact Hv2|].
  all: split; [unfold underlying_typed in *; simpl in *; exact Ht1|].
  all: split; [unfold underlying_typed in *; simpl in *; exact Ht2|].
  all: intros Hvisible; apply Hshape;
    eapply flows_to_join_left; eauto.
Qed.

Lemma expression_relation_ty_protect : forall T observer t1 t2 l,
  expression_relation observer T t1 t2 ->
  expression_relation observer (ty_protect l T) t1 t2.
Proof.
  intros T observer t1 t2 l [Ht1 [Ht2 Hlift]].
  unfold expression_relation, expression_lifting in *.
  split.
  - unfold underlying_typed in *.
    rewrite erase_type_protect. exact Ht1.
  - split.
    + unfold underlying_typed in *.
      rewrite erase_type_protect. exact Ht2.
    + intros v1 v2 He1 He2.
      apply value_relation_ty_protect.
      eapply Hlift; eauto.
Qed.

Lemma value_relation_protected : forall T observer v1 v2 l l1 l2,
  value_relation observer T v1 v2 ->
  value_relation observer (ty_protect l T)
    (protect_value v1 l1) (protect_value v2 l2).
Proof.
  intros T observer v1 v2 l l1 l2 H.
  apply value_relation_ty_protect.
  apply value_relation_protect_same. exact H.
Qed.

Lemma value_locally_closed : forall v,
  value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv; unfold locally_closed in *; simpl in *;
    intuition.
Qed.

Lemma related_values_underlying : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  underlying_typed T v1 /\ underlying_typed T v2.
Proof. intros observer [] v1 v2 H; simpl in H; tauto. Qed.

Definition related_env (observer : label) (Gamma : context)
    (rho1 rho2 : atom -> tm) : Prop :=
  env_locally_closed rho1 /\ env_locally_closed rho2 /\
  forall x T, lookup_context x Gamma = Some T ->
    value_relation observer T (rho1 x) (rho2 x).

Lemma related_env_erased_left : forall observer Gamma rho1 rho2,
  related_env observer Gamma rho1 rho2 ->
  env_erased_typed Gamma empty rho1.
Proof.
  intros observer Gamma rho1 rho2 [_ [_ Hrel]] x T Hlook.
  exact (proj1 (related_values_underlying _ _ _ _ (Hrel x T Hlook))).
Qed.

Lemma related_env_erased_right : forall observer Gamma rho1 rho2,
  related_env observer Gamma rho1 rho2 ->
  env_erased_typed Gamma empty rho2.
Proof.
  intros observer Gamma rho1 rho2 [_ [_ Hrel]] x T Hlook.
  exact (proj2 (related_values_underlying _ _ _ _ (Hrel x T Hlook))).
Qed.

Lemma related_env_extend : forall observer Gamma rho1 rho2 x T a1 a2,
  related_env observer Gamma rho1 rho2 ->
  value_relation observer T a1 a2 ->
  related_env observer (update Gamma x T)
    (extend_env rho1 x a1) (extend_env rho2 x a2).
Proof.
  intros observer Gamma rho1 rho2 x T a1 a2 [Hlc1 [Hlc2 Hrel]] Harg.
  destruct (related_values_are_values _ _ _ _ Harg) as [Hv1 Hv2].
  split.
  - apply extend_env_lc; auto using value_locally_closed.
  - split.
    + apply extend_env_lc; auto using value_locally_closed.
    + intros y U Hlook. simpl in Hlook.
      destruct (Nat.eqb y x) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst.
        inversion Hlook; subst. unfold extend_env.
        now rewrite Nat.eqb_refl.
      * assert (Nat.eqb x y = false) as Heq' by
          (rewrite Nat.eqb_sym; exact Heq).
        unfold extend_env. rewrite Heq'.
        apply Hrel. exact Hlook.
Qed.

Lemma related_env_instantiate_typed : forall observer Gamma t T rho1 rho2,
  has_type Gamma t T ->
  related_env observer Gamma rho1 rho2 ->
  underlying_typed T (instantiate rho1 t) /\
  underlying_typed T (instantiate rho2 t).
Proof.
  intros observer Gamma t T rho1 rho2 Hty Henv.
  unfold underlying_typed. split.
  - eapply instantiate_erased_typing; eauto using related_env_erased_left.
    exact (proj1 Henv).
  - eapply instantiate_erased_typing; eauto using related_env_erased_right.
    exact (proj1 (proj2 Henv)).
Qed.

Definition visible_part (observer : label) (T : ty) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_Unit _ =>
      exists k1 k2, v1 = tm_unit k1 /\ v2 = tm_unit k2
  | Ty_Sum A B _ =>
      (exists a1 a2 k1 k2,
        v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\
        value_relation observer A a1 a2) \/
      (exists b1 b2 k1 k2,
        v1 = tm_inr b1 k1 /\ v2 = tm_inr b2 k2 /\
        value_relation observer B b1 b2)
  | Ty_Prod A B _ =>
      exists a1 b1 a2 b2 k1 k2,
        v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
        value_relation observer A a1 a2 /\
        value_relation observer B b1 b2
  | Ty_Arrow A B _ =>
      exists A1 A2 body1 body2 k1 k2,
        v1 = tm_abs A1 body1 k1 /\ v2 = tm_abs A2 body2 k2 /\
        forall a1 a2,
          value_relation observer A a1 a2 ->
          expression_lifting (value_relation observer B)
            (tm_app v1 a1 High) (tm_app v2 a2 High)
  end.

Lemma value_relation_intro : forall observer T v1 v2,
  value v1 -> value v2 ->
  underlying_typed T v1 -> underlying_typed T v2 ->
  (flows_to (security_of T).(indirect_reader) observer ->
    visible_part observer T v1 v2) ->
  value_relation observer T v1 v2.
Proof.
  intros observer [] v1 v2 Hv1 Hv2 Ht1 Ht2 Hshape;
    simpl in *; repeat split; auto.
Qed.

Lemma lc_at_erase_inv : forall t k,
  lc_at k (erase_security t) -> lc_at k t.
Proof.
  induction t; intros k H; simpl in *; intuition eauto.
Qed.

Lemma underlying_locally_closed : forall T t,
  underlying_typed T t -> locally_closed t.
Proof.
  intros T t H. unfold underlying_typed in H.
  apply lc_at_erase_inv.
  eapply typing_locally_closed; eauto.
Qed.

Lemma related_from_big_shape : forall observer T t1 t2 v1 v2,
  underlying_typed T t1 -> underlying_typed T t2 ->
  big_eval t1 v1 -> big_eval t2 v2 ->
  (flows_to (security_of T).(indirect_reader) observer ->
    visible_part observer T v1 v2) ->
  value_relation observer T v1 v2.
Proof.
  intros observer T t1 t2 v1 v2 Ht1 Ht2 Hb1 Hb2 Hshape.
  apply value_relation_intro.
  - exact (big_eval_value _ _ Hb1).
  - exact (big_eval_value _ _ Hb2).
  - exact (underlying_multi_preservation T t1 v1 Ht1
      (big_eval_multi _ _ Hb1)).
  - exact (underlying_multi_preservation T t2 v2 Ht2
      (big_eval_multi _ _ Hb2)).
  - exact Hshape.
Qed.

Lemma flows_to_join_right : forall a b c,
  flows_to (join a b) c -> flows_to b c.
Proof. destruct a, b, c; vm_compute; tauto. Qed.

Lemma flows_to_dec : forall a b,
  {flows_to a b} + {~ flows_to a b}.
Proof. destruct a, b; simpl; auto. Qed.

Lemma visible_protect_level : forall T l observer,
  flows_to (security_of (ty_protect l T)).(indirect_reader) observer ->
  flows_to l observer.
Proof.
  intros [] l observer H; simpl in H;
    eapply flows_to_join_right; eauto.
Qed.

Lemma hidden_from_big : forall observer T t1 t2 v1 v2,
  ~ flows_to (security_of T).(indirect_reader) observer ->
  underlying_typed T t1 -> underlying_typed T t2 ->
  big_eval t1 v1 -> big_eval t2 v2 ->
  value_relation observer T v1 v2.
Proof.
  intros observer T t1 t2 v1 v2 Hhidden Ht1 Ht2 Hb1 Hb2.
  eapply related_from_big_shape with (T := T) (t1 := t1) (t2 := t2);
    eauto.
  intro Hvisible. contradiction.
Qed.

Theorem fundamental_big_eval : forall Gamma t T,
  has_type Gamma t T -> forall observer rho1 rho2 v1 v2,
  related_env observer Gamma rho1 rho2 ->
  underlying_typed T (instantiate rho1 t) ->
  underlying_typed T (instantiate rho2 t) ->
  big_eval (instantiate rho1 t) v1 ->
  big_eval (instantiate rho2 t) v2 ->
  value_relation observer T v1 v2.
Proof.
  intros Gamma t T Hty. induction Hty;
    intros observer rho1 rho2 v1 v2 Henv Hinst1 Hinst2 Hb1 Hb2;
    simpl in *.
  - destruct Henv as [_ [_ Hrel]].
    pose proof (Hrel x T H) as Hvar.
    destruct (related_values_are_values _ _ _ _ Hvar) as [Hv1 Hv2].
    pose proof (big_eval_of_value _ _ Hv1 Hb1) as ->.
    pose proof (big_eval_of_value _ _ Hv2 Hb2) as ->.
    exact Hvar.
  - pose proof (big_eval_of_value _ _ (v_unit kappa) Hb1) as ->.
    pose proof (big_eval_of_value _ _ (v_unit kappa) Hb2) as ->.
    eapply related_from_big_shape with (T := Ty_Unit kappa)
      (t1 := tm_unit kappa) (t2 := tm_unit kappa); eauto.
    intros _. exists kappa, kappa. auto.
  - assert (Hva1 : value (tm_abs T1 (instantiate rho1 body) kappa)).
    { apply v_abs. eapply underlying_locally_closed; eauto. }
    assert (Hva2 : value (tm_abs T1 (instantiate rho2 body) kappa)).
    { apply v_abs. eapply underlying_locally_closed; eauto. }
    pose proof (big_eval_of_value _ _ Hva1 Hb1) as ->.
    pose proof (big_eval_of_value _ _ Hva2 Hb2) as ->.
    eapply related_from_big_shape with
      (T := Ty_Arrow T1 T2 kappa)
      (t1 := tm_abs T1 (instantiate rho1 body) kappa)
      (t2 := tm_abs T1 (instantiate rho2 body) kappa); eauto.
    intros _. simpl.
    exists T1, T1, (instantiate rho1 body), (instantiate rho2 body),
      kappa, kappa. split; [reflexivity|].
    split; [reflexivity|].
    intros arg1 arg2 Harg w1 w2 Hew1 Hew2.
    destruct (related_values_are_values _ _ _ _ Harg) as [Harg1 Harg2].
    destruct (big_eval_app_values_inv _ _ _ _ _ Hva1 Harg1
      (evaluates_big_eval _ _ Hew1)) as (u1 & Hbody1 & Hw1).
    destruct (big_eval_app_values_inv _ _ _ _ _ Hva2 Harg2
      (evaluates_big_eval _ _ Hew2)) as (u2 & Hbody2 & Hw2).
    subst w1 w2.
    apply value_relation_protect_same.
    set (x := fresh_atom (L ++ fv body)).
    assert (Hfresh : ~ In x (L ++ fv body)).
    { unfold x. apply fresh_atom_not_in. }
    apply not_in_app in Hfresh as [HnL HnFv].
    pose proof (related_env_extend observer Gamma rho1 rho2 x T1
      arg1 arg2 Henv Harg) as Henv'.
    pose proof (related_env_instantiate_typed observer
      (update Gamma x T1) (open body (tm_fvar x)) T2
      (extend_env rho1 x arg1) (extend_env rho2 x arg2)
      (H1 x HnL) Henv') as [HtB1 HtB2].
    pose proof (instantiate_open body rho1 x arg1 HnFv
      (proj1 Henv)) as E1.
    pose proof (instantiate_open body rho2 x arg2 HnFv
      (proj1 (proj2 Henv))) as E2.
    rewrite E1 in HtB1. rewrite E2 in HtB2.
    eapply (H2 x HnL); eauto; rewrite ?E1, ?E2; assumption.
  - inversion Hb1; inversion Hb2; subst.
    destruct (flows_to_dec kappa.(indirect_reader) observer) as [Hvis|Hhide].
    + pose proof (related_env_instantiate_typed observer Gamma t1
        (Ty_Arrow T1 T2 kappa) rho1 rho2 Hty1 Henv)
        as [Hft1 Hft2].
      pose proof (related_env_instantiate_typed observer Gamma t2
        T1 rho1 rho2 Hty2 Henv) as [Hat1 Hat2].
      pose proof (IHHty1 observer rho1 rho2
        (tm_abs A body k) (tm_abs A0 body0 k0)
        Henv Hft1 Hft2 H3 H11) as Hfunrel.
      pose proof (IHHty2 observer rho1 rho2 va va0
        Henv Hat1 Hat2 H4 H12) as Hargrel.
      destruct Hfunrel as [_ [_ [_ [_ Hfunshape]]]].
      specialize (Hfunshape Hvis).
      destruct Hfunshape as
        (F1 & F2 & b1 & b2 & fk1 & fk2 & _ & _ & Hfn).
      assert (Happ1 : evaluates (tm_app (tm_abs A body k) va High)
        (protect_value w k.(indirect_reader))).
      { apply big_eval_evaluates.
        eapply BE_App with (va := va) (w := w).
        - apply big_eval_value_refl. eapply big_eval_value; eauto.
        - apply big_eval_value_refl. eapply big_eval_value; eauto.
        - exact H6.
        - destruct (reader k); exact I. }
      assert (Happ2 : evaluates (tm_app (tm_abs A0 body0 k0) va0 High)
        (protect_value w0 k0.(indirect_reader))).
      { apply big_eval_evaluates.
        eapply BE_App with (va := va0) (w := w0).
        - apply big_eval_value_refl. eapply big_eval_value; eauto.
        - apply big_eval_value_refl. eapply big_eval_value; eauto.
        - exact H14.
        - destruct (reader k0); exact I. }
      apply value_relation_ty_protect.
      eapply Hfn; eauto.
    + eapply hidden_from_big with
        (T := ty_protect kappa.(indirect_reader) T2)
        (t1 := tm_app (instantiate rho1 t1) (instantiate rho1 t2) r)
        (t2 := tm_app (instantiate rho2 t1) (instantiate rho2 t2) r);
        eauto.
      intro Hvisible. apply Hhide.
      eapply visible_protect_level; eauto.
  - inversion Hb1; inversion Hb2; subst.
    pose proof (related_env_instantiate_typed observer Gamma t1 T1
      rho1 rho2 Hty1 Henv) as [HtA1 HtA2].
    pose proof (related_env_instantiate_typed observer Gamma t2 T2
      rho1 rho2 Hty2 Henv) as [HtB1 HtB2].
    pose proof (IHHty1 observer rho1 rho2 va va0
      Henv HtA1 HtA2 H4 H10) as Ha.
    pose proof (IHHty2 observer rho1 rho2 vb vb0
      Henv HtB1 HtB2 H5 H11) as Hb.
    eapply related_from_big_shape with
      (T := Ty_Prod T1 T2 kappa)
      (t1 := tm_pair (instantiate rho1 t1) (instantiate rho1 t2) kappa)
      (t2 := tm_pair (instantiate rho2 t1) (instantiate rho2 t2) kappa);
      eauto.
    intros _. exists va, vb, va0, vb0, kappa, kappa.
    repeat split; auto.
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
