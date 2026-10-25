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
(* Infrastructure for the noninterference proof.                    *)
(* ================================================================ *)

(* ---------------- Labels, joins, and security ---------------- *)

Lemma flows_to_refl : forall l : label, flows_to l l.
Proof. intros []; simpl; trivial. Qed.

Lemma flows_to_trans : forall l1 l2 l3 : label,
    flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof. intros [] [] [] H12 H23; simpl in *; trivial; contradiction. Qed.

Lemma flows_to_join_l : forall a b : label, flows_to a (join a b).
Proof. intros [] []; simpl; trivial. Qed.

Lemma flows_to_join_r : forall a b : label, flows_to b (join a b).
Proof. intros [] []; simpl; trivial. Qed.

Lemma join_mono : forall a b c d : label,
    flows_to a b -> flows_to c d -> flows_to (join a c) (join b d).
Proof. intros [] [] [] [] H1 H2; simpl in *; trivial; contradiction. Qed.

Lemma join_assoc : forall a b c : label, join (join a b) c = join a (join b c).
Proof. intros [] [] []; reflexivity. Qed.

Lemma join_comm : forall a b : label, join a b = join b a.
Proof. intros [] []; reflexivity. Qed.

Lemma join_idem : forall a : label, join a a = a.
Proof. intros []; reflexivity. Qed.

Lemma join_low_r : forall a : label, join a Low = a.
Proof. intros []; reflexivity. Qed.

Lemma join_high_r : forall a : label, join a High = High.
Proof. intros []; reflexivity. Qed.

Lemma join_absorb_r : forall a b : label, join a (join a b) = join a b.
Proof. intros a b; rewrite <- join_assoc; rewrite join_idem; reflexivity. Qed.

Lemma join_absorb_l : forall a b : label, join (join a b) b = join a b.
Proof. intros a b; rewrite join_assoc; rewrite join_idem; reflexivity. Qed.

Definition flowb (a b : label) : bool :=
  match a, b with
  | High, Low => false
  | _, _ => true
  end.

Lemma flowb_true : forall a b, flowb a b = true <-> flows_to a b.
Proof. intros [] []; simpl; intuition discriminate. Qed.

Lemma flowb_false : forall a b, flowb a b = false <-> ~ flows_to a b.
Proof. intros [] []; simpl; intuition discriminate. Qed.

Lemma flowb_join_high : forall a b l, flowb a l = false -> flowb (join b a) l = false.
Proof. intros [] [] []; simpl in *; try discriminate; reflexivity. Qed.

Lemma flowb_join_hidden : forall a b l, flowb a l = false -> flowb (join a b) l = false.
Proof. intros [] [] []; simpl in *; try discriminate; reflexivity. Qed.

Lemma security_le_refl : forall κ, security_le κ κ.
Proof. intros [r i]; simpl; split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall κ1 κ2 κ3,
    security_le κ1 κ2 -> security_le κ2 κ3 -> security_le κ1 κ3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3] [H1 H2] [H3 H4]; simpl in *.
  split; eapply flows_to_trans; eauto.
Qed.

Lemma protect_security_low : forall κ, protect_security κ Low = κ.
Proof. intros [r i]; unfold protect_security; cbn; rewrite !join_low_r; reflexivity. Qed.

Lemma protect_security_reader : forall κ l,
    (protect_security κ l).(reader) = join κ.(reader) l.
Proof. intros [r i] l; reflexivity. Qed.

Lemma protect_security_ind : forall κ l,
    (protect_security κ l).(indirect_reader) = join κ.(indirect_reader) l.
Proof. intros [r i] l; reflexivity. Qed.

Lemma protect_security_join : forall κ a b,
    protect_security (protect_security κ a) b = protect_security κ (join a b).
Proof. intros [r i] a b; unfold protect_security; cbn; rewrite !join_assoc; reflexivity. Qed.

Lemma security_le_protect : forall κ l, security_le κ (protect_security κ l).
Proof. intros [r i] l; unfold security_le, protect_security; cbn. split; apply flows_to_join_l. Qed.

Lemma security_le_protect_mono : forall κ1 κ2 a b,
    security_le κ1 κ2 -> flows_to a b ->
    security_le (protect_security κ1 a) (protect_security κ2 b).
Proof.
  intros [r1 i1] [r2 i2] a b [Hr Hi] Hab.
  unfold security_le, protect_security in *. cbn in *.
  split; apply join_mono; auto.
Qed.

Lemma wf_security_protect : forall κ l, wf_security κ -> wf_security (protect_security κ l).
Proof.
  intros [r i] l H. unfold wf_security, protect_security in *. cbn in *.
  apply join_mono; [exact H | apply flows_to_refl].
Qed.

Lemma security_of_ty_protect : forall l T,
    security_of (ty_protect l T) = protect_security (security_of T) l.
Proof. intros l [κ|T1 T2 κ|T1 T2 κ|T1 T2 κ]; reflexivity. Qed.

Definition set_security (T : ty) (κ : security) : ty :=
  match T with
  | Ty_Unit _ => Ty_Unit κ
  | Ty_Sum T1 T2 _ => Ty_Sum T1 T2 κ
  | Ty_Prod T1 T2 _ => Ty_Prod T1 T2 κ
  | Ty_Arrow T1 T2 _ => Ty_Arrow T1 T2 κ
  end.

Lemma ty_protect_as_set : forall l T,
    ty_protect l T = set_security T (protect_security (security_of T) l).
Proof. intros l [κ|T1 T2 κ|T1 T2 κ|T1 T2 κ]; reflexivity. Qed.

Lemma security_of_set_security : forall T κ, security_of (set_security T κ) = κ.
Proof. intros [κ0|T1 T2 κ0|T1 T2 κ0|T1 T2 κ0] κ; reflexivity. Qed.

Lemma set_security_security_of : forall T, set_security T (security_of T) = T.
Proof. intros [κ|T1 T2 κ|T1 T2 κ|T1 T2 κ]; reflexivity. Qed.

(* ---------------- protect_value ---------------- *)

Lemma protect_value_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l H; induction H; simpl.
  - apply v_unit.
  - apply v_abs. exact H.
  - apply v_pair; assumption.
  - apply v_inl; assumption.
  - apply v_inr; assumption.
Qed.

Lemma protect_value_protect : forall v a b,
    protect_value (protect_value v a) b = protect_value v (join a b).
Proof.
  intros v a b. destruct v; simpl; try reflexivity;
  rewrite protect_security_join; reflexivity.
Qed.

Lemma erase_security_protect_value : forall v l,
    erase_security (protect_value v l) = erase_security v.
Proof. intros v l; destruct v; simpl; reflexivity. Qed.

(* ---------------- Fresh atoms ---------------- *)

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Lemma max_list_spec : forall (l : list nat) (x : nat), In x l -> x <= max_list l.
Proof.
  induction l as [| y ys IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma exists_fresh : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (max_list L)). intro H.
  apply max_list_spec in H. lia.
Qed.

Lemma exists_fresh_two : forall L1 L2 : list atom,
    exists x, ~ In x L1 /\ ~ In x L2.
Proof.
  intros L1 L2. exists (S (Nat.max (max_list L1) (max_list L2))).
  split; intro H; apply max_list_spec in H; lia.
Qed.

(* ---------------- Local closure ---------------- *)

Lemma lc_at_weaken : forall t k1 k2, k1 <= k2 -> lc_at k1 t -> lc_at k2 t.
Proof.
  induction t; intros k1 k2 Hle H; simpl in *; auto.
  - lia.
  - (* abs *) apply IHt with (k1 := S k1) (k2 := S k2); [lia | exact H].
  - (* app *) destruct H as [H1 H2]; split.
    + apply IHt1 with (k1 := k1) (k2 := k2); assumption.
    + apply IHt2 with (k1 := k1) (k2 := k2); assumption.
  - (* pair *) destruct H as [H1 H2]; split.
    + apply IHt1 with (k1 := k1) (k2 := k2); assumption.
    + apply IHt2 with (k1 := k1) (k2 := k2); assumption.
  - (* fst *) apply IHt with (k1 := k1) (k2 := k2); assumption.
  - (* snd *) apply IHt with (k1 := k1) (k2 := k2); assumption.
  - (* inl *) apply IHt with (k1 := k1) (k2 := k2); assumption.
  - (* inr *) apply IHt with (k1 := k1) (k2 := k2); assumption.
  - (* case *)
    destruct H as [H1 [H2 H3]]. repeat split.
    + apply IHt1 with (k1 := k1) (k2 := k2); assumption.
    + apply IHt2 with (k1 := S k1) (k2 := S k2); [lia | exact H2].
    + apply IHt3 with (k1 := S k1) (k2 := S k2); [lia | exact H3].
  - (* protect *) apply IHt with (k1 := k1) (k2 := k2); assumption.
  - (* if *)
    destruct H as [H1 [H2 H3]]. repeat split.
    + apply IHt1 with (k1 := k1) (k2 := k2); assumption.
    + apply IHt2 with (k1 := k1) (k2 := k2); assumption.
    + apply IHt3 with (k1 := k1) (k2 := k2); assumption.
Qed.

Lemma lc_at_open_rec_fvar : forall body k x,
    lc_at k (open_rec k (tm_fvar x) body) <-> lc_at (S k) body.
Proof.
  induction body; intros k x; simpl.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst n. split; intros _; [lia | exact I].
    + apply Nat.eqb_neq in E. cbn. split; lia.
  - (* fvar *) reflexivity.
  - (* unit *) reflexivity.
  - (* abs *) apply IHbody.
  - (* app *) rewrite IHbody1, IHbody2. tauto.
  - (* pair *) rewrite IHbody1, IHbody2. tauto.
  - (* fst *) apply IHbody.
  - (* snd *) apply IHbody.
  - (* inl *) apply IHbody.
  - (* inr *) apply IHbody.
  - (* case *) rewrite IHbody1, IHbody2, IHbody3. tauto.
  - (* protect *) apply IHbody.
  - (* if *) rewrite IHbody1, IHbody2, IHbody3. tauto.
Qed.

Lemma open_rec_lc : forall t k u, lc_at k t -> open_rec k u t = t.
Proof.
  induction t; intros k u H; simpl in *; auto.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst n. lia.
    + reflexivity.
  - (* abs *) f_equal. apply IHt with (k := S k). exact H.
  - (* app *) destruct H as [H1 H2]. f_equal; [apply IHt1 | apply IHt2]; exact H1 || exact H2.
  - (* pair *) destruct H as [H1 H2]. f_equal; [apply IHt1 | apply IHt2]; exact H1 || exact H2.
  - (* fst *) f_equal. eapply IHt; eauto.
  - (* snd *) f_equal. eapply IHt; eauto.
  - (* inl *) f_equal. eapply IHt; eauto.
  - (* inr *) f_equal. eapply IHt; eauto.
  - (* case *)
    destruct H as [H1 [H2 H3]].
    f_equal; [apply IHt1 with (k := k) | apply IHt2 with (k := S k) | apply IHt3 with (k := S k)]; auto.
  - (* protect *) f_equal. eapply IHt; eauto.
  - (* if *)
    destruct H as [H1 [H2 H3]].
    f_equal; [apply IHt1 with (k := k) | apply IHt2 with (k := k) | apply IHt3 with (k := k)]; auto.
Qed.

Lemma value_lc : forall v, value v -> lc_at 0 v.
Proof.
  intros v H; induction H; simpl.
  - trivial.
  - exact H.
  - split; assumption.
  - assumption.
  - assumption.
Qed.

Lemma has_type_lc : forall Γ t T, has_type Γ t T -> lc_at 0 t.
Proof.
  intros Γ t T H.
  induction H as
    [ Γ x T Hlook Hwf
    | Γ κ Hwf
    | L Γ T1 body T2 κ HwfT1 Hwfκ Hbody IHbody
    | Γ t1 t2 T1 T2 κ r Ht1 IH1 Ht2 IH2 Hflow
    | Γ t1 t2 T1 T2 κ Ht1 IH1 Ht2 IH2 Hwfκ
    | Γ t T1 T2 κ r Ht IHt Hflow
    | Γ t T1 T2 κ r Ht IHt Hflow
    | Γ t T1 T2 κ Ht IHt HwfT2 Hwfκ
    | Γ t T1 T2 κ HwfT1 Ht IHt Hwfκ
    | L Γ t body1 body2 T1 T2 T κ r Ht IHt Hflow Hb1 IHb1 Hb2 IHb2
    | Γ t T l Ht IHt
    | Γ t T U Ht IHt Hsub
    | Γ c yes no k T r Hc IHc Hy IHy Hn IHn Hflow ]; simpl.
  - (* T_Var *) trivial.
  - (* T_Unit *) trivial.
  - (* T_Abs *)
    destruct (exists_fresh L) as (x & Hx).
    specialize (IHbody x Hx).
    exact (proj1 (lc_at_open_rec_fvar body 0 x) IHbody).
  - (* T_App *) split; assumption.
  - (* T_Pair *) split; assumption.
  - (* T_Fst *) assumption.
  - (* T_Snd *) assumption.
  - (* T_Inl *) assumption.
  - (* T_Inr *) assumption.
  - (* T_Case *)
    destruct (exists_fresh L) as (x & Hx).
    specialize (IHb1 x Hx). specialize (IHb2 x Hx).
    apply (proj1 (lc_at_open_rec_fvar body1 0 x)) in IHb1.
    apply (proj1 (lc_at_open_rec_fvar body2 0 x)) in IHb2.
    repeat split; assumption.
  - (* T_Protect *) assumption.
  - (* T_Sub *) assumption.
  - (* T_If *) repeat split; assumption.
Qed.

(* ---------------- Simultaneous substitution of free variables ---------------- *)

Fixpoint subst_env (σ : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => σ x
  | tm_unit κ => tm_unit κ
  | tm_abs T body κ => tm_abs T (subst_env σ body) κ
  | tm_app t1 t2 r => tm_app (subst_env σ t1) (subst_env σ t2) r
  | tm_pair t1 t2 κ => tm_pair (subst_env σ t1) (subst_env σ t2) κ
  | tm_fst t1 r => tm_fst (subst_env σ t1) r
  | tm_snd t1 r => tm_snd (subst_env σ t1) r
  | tm_inl t1 κ => tm_inl (subst_env σ t1) κ
  | tm_inr t1 κ => tm_inr (subst_env σ t1) κ
  | tm_case t0 body1 body2 r =>
      tm_case (subst_env σ t0) (subst_env σ body1) (subst_env σ body2) r
  | tm_protect l t1 => tm_protect l (subst_env σ t1)
  | tm_if c yes no r => tm_if (subst_env σ c) (subst_env σ yes) (subst_env σ no) r
  end.

Lemma subst_env_fvar_id : forall t, subst_env (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; congruence. Qed.

Lemma subst_env_open_rec : forall (σ : atom -> tm),
    (forall x, lc_at 0 (σ x)) ->
    forall body k u,
      subst_env σ (open_rec k u body) =
      open_rec k (subst_env σ u) (subst_env σ body).
Proof.
  intros σ Hlc body. induction body; intros k u; simpl.
  - (* bvar *) destruct (Nat.eqb k n); reflexivity.
  - (* fvar *)
    symmetry. apply open_rec_lc.
    apply lc_at_weaken with (k1 := 0); [lia | apply Hlc].
  - (* unit *) reflexivity.
  - (* abs *) rewrite IHbody. reflexivity.
  - (* app *) rewrite IHbody1, IHbody2. reflexivity.
  - (* pair *) rewrite IHbody1, IHbody2. reflexivity.
  - (* fst *) rewrite IHbody. reflexivity.
  - (* snd *) rewrite IHbody. reflexivity.
  - (* inl *) rewrite IHbody. reflexivity.
  - (* inr *) rewrite IHbody. reflexivity.
  - (* case *) rewrite IHbody1, IHbody2, IHbody3. reflexivity.
  - (* protect *) rewrite IHbody. reflexivity.
  - (* if *) rewrite IHbody1, IHbody2, IHbody3. reflexivity.
Qed.

Lemma In_app_l : forall (x : atom) l1 l2, In x l1 -> In x (l1 ++ l2).
Proof. intros; apply in_app_iff; auto. Qed.

Lemma In_app_r : forall (x : atom) l1 l2, In x l2 -> In x (l1 ++ l2).
Proof. intros; apply in_app_iff; auto. Qed.

Lemma subst_env_ext : forall (σ σ' : atom -> tm) t,
    (forall x, In x (fv t) -> σ x = σ' x) ->
    subst_env σ t = subst_env σ' t.
Proof.
  intros σ σ' t. induction t; simpl; intros H.
  - (* bvar *) reflexivity.
  - (* fvar *) apply H. simpl; auto.
  - (* unit *) reflexivity.
  - (* abs *) f_equal. apply IHt. intros x Hx. apply H. simpl in *; auto.
  - (* app *)
    f_equal.
    + apply IHt1. intros x Hx. apply H. apply In_app_l. exact Hx.
    + apply IHt2. intros x Hx. apply H. apply In_app_r. exact Hx.
  - (* pair *)
    f_equal.
    + apply IHt1. intros x Hx. apply H. apply In_app_l. exact Hx.
    + apply IHt2. intros x Hx. apply H. apply In_app_r. exact Hx.
  - (* fst *) f_equal. apply IHt. intros x Hx. apply H. simpl in *; auto.
  - (* snd *) f_equal. apply IHt. intros x Hx. apply H. simpl in *; auto.
  - (* inl *) f_equal. apply IHt. intros x Hx. apply H. simpl in *; auto.
  - (* inr *) f_equal. apply IHt. intros x Hx. apply H. simpl in *; auto.
  - (* case *)
    f_equal.
    + apply IHt1. intros x Hx. apply H. apply In_app_l. exact Hx.
    + apply IHt2. intros x Hx. apply H. apply In_app_r. apply In_app_l. exact Hx.
    + apply IHt3. intros x Hx. apply H. apply In_app_r. apply In_app_r. exact Hx.
  - (* protect *) f_equal. apply IHt. intros x Hx. apply H. simpl in *; auto.
  - (* if *)
    f_equal.
    + apply IHt1. intros x Hx. apply H. apply In_app_l. exact Hx.
    + apply IHt2. intros x Hx. apply H. apply In_app_r. apply In_app_l. exact Hx.
    + apply IHt3. intros x Hx. apply H. apply In_app_r. apply In_app_r. exact Hx.
Qed.

Lemma subst_env_notin : forall (σ : atom -> tm) x u t,
    ~ In x (fv t) ->
    subst_env (fun y => if Nat.eqb y x then u else σ y) t = subst_env σ t.
Proof.
  intros σ x u t Hx. apply subst_env_ext. intros y Hy.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. exfalso. apply Hx. exact Hy.
  - reflexivity.
Qed.

Lemma subst_env_open_fvar : forall (σ : atom -> tm),
    (forall x, lc_at 0 (σ x)) ->
    forall body x,
      subst_env σ (open body (tm_fvar x)) = open (subst_env σ body) (σ x).
Proof.
  intros σ Hlc body x. unfold open.
  rewrite (subst_env_open_rec σ Hlc body 0 (tm_fvar x)).
  cbn [subst_env]. reflexivity.
Qed.

(* ---------------- Small-step decomposition lemmas ---------------- *)

Lemma value_no_step : forall v, value v -> forall t, ~ step v t.
Proof.
  intros v Hv. induction Hv; intros t Hst; inversion Hst; subst.
  - (* v_pair, ST_Pair1 *) eapply IHHv1; eauto.
  - (* v_pair, ST_Pair2 *) eapply IHHv2; eauto.
  - (* v_inl *) eapply IHHv; eauto.
  - (* v_inr *) eapply IHHv; eauto.
Qed.

Lemma multi_value : forall v w, multi v w -> value v -> w = v.
Proof.
  intros v w Hm. induction Hm as [| t1 t2 t3 Hst Hm IH]; intro Hv.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma multi_trans : forall a b c, multi a b -> multi b c -> multi a c.
Proof.
  intros a b c Hm. induction Hm as [| t1 t2 t3 Hst Hm IH]; intro H2.
  - exact H2.
  - eapply multi_step; [exact Hst | apply IH; exact H2].
Qed.

Lemma multi_protect : forall e w l,
    multi e w -> value w -> multi (tm_protect l e) (protect_value w l).
Proof.
  intros e w l Hm. induction Hm as [| t1 t2 t3 Hst Hm IH]; intro Hw.
  - eapply multi_step.
    + apply ST_ProtectValue. exact Hw.
    + apply multi_refl.
  - eapply multi_step.
    + apply ST_Protect. exact Hst.
    + apply IH. exact Hw.
Qed.

Lemma step_app_inv : forall f a r t2, tm_app f a r --> t2 ->
  (exists f', f --> f' /\ t2 = tm_app f' a r) \/
  (exists a', value f /\ a --> a' /\ t2 = tm_app f a' r) \/
  (exists T body kappa v, f = tm_abs T body kappa /\ a = v /\
     value (tm_abs T body kappa) /\ value v /\ flows_to kappa.(reader) r /\
     t2 = tm_protect kappa.(indirect_reader) (open body v)).
Proof.
  intros f a r t2 H. inversion H; subst.
  - right. right. eexists _, _, _, _. repeat split; eassumption || reflexivity.
  - left. eexists. split; [eassumption | reflexivity].
  - right. left. eexists. repeat split; eassumption || reflexivity.
Qed.

Lemma step_pair_inv : forall t1 t2 κ u, tm_pair t1 t2 κ --> u ->
  (exists t1', t1 --> t1' /\ u = tm_pair t1' t2 κ) \/
  (exists t2', value t1 /\ t2 --> t2' /\ u = tm_pair t1 t2' κ).
Proof.
  intros t1 t2 κ u H. inversion H; subst.
  - left. eexists. split; [eassumption | reflexivity].
  - right. eexists. repeat split; eassumption || reflexivity.
Qed.

Lemma step_fst_inv : forall t r u, tm_fst t r --> u ->
  (exists t', t --> t' /\ u = tm_fst t' r) \/
  (exists v1 v2 κ, t = tm_pair v1 v2 κ /\ value v1 /\ value v2 /\
     flows_to κ.(reader) r /\ u = tm_protect κ.(indirect_reader) v1).
Proof.
  intros t r u H. inversion H; subst.
  - right. eexists _, _, _. repeat split; eassumption || reflexivity.
  - left. eexists. split; [eassumption | reflexivity].
Qed.

Lemma step_snd_inv : forall t r u, tm_snd t r --> u ->
  (exists t', t --> t' /\ u = tm_snd t' r) \/
  (exists v1 v2 κ, t = tm_pair v1 v2 κ /\ value v1 /\ value v2 /\
     flows_to κ.(reader) r /\ u = tm_protect κ.(indirect_reader) v2).
Proof.
  intros t r u H. inversion H; subst.
  - right. eexists _, _, _. repeat split; eassumption || reflexivity.
  - left. eexists. split; [eassumption | reflexivity].
Qed.

Lemma step_inl_inv : forall t κ u, tm_inl t κ --> u ->
  exists t', t --> t' /\ u = tm_inl t' κ.
Proof.
  intros t κ u H. inversion H; subst. eexists. split; [eassumption | reflexivity].
Qed.

Lemma step_inr_inv : forall t κ u, tm_inr t κ --> u ->
  exists t', t --> t' /\ u = tm_inr t' κ.
Proof.
  intros t κ u H. inversion H; subst. eexists. split; [eassumption | reflexivity].
Qed.

Lemma step_case_inv : forall t b1 b2 r u, tm_case t b1 b2 r --> u ->
  (exists t', t --> t' /\ u = tm_case t' b1 b2 r) \/
  (exists v κ, t = tm_inl v κ /\ value v /\ flows_to κ.(reader) r /\
     u = tm_protect κ.(indirect_reader) (open b1 v)) \/
  (exists v κ, t = tm_inr v κ /\ value v /\ flows_to κ.(reader) r /\
     u = tm_protect κ.(indirect_reader) (open b2 v)).
Proof.
  intros t b1 b2 r u H. inversion H; subst.
  - right. left. eexists _, _. repeat split; eassumption || reflexivity.
  - right. right. eexists _, _. repeat split; eassumption || reflexivity.
  - left. eexists. split; [eassumption | reflexivity].
Qed.

Lemma step_protect_inv : forall l e u, tm_protect l e --> u ->
  (exists v, e = v /\ u = protect_value v l /\ value v) \/
  (exists e', e --> e' /\ u = tm_protect l e').
Proof.
  intros l e u H. inversion H; subst.
  - left. eexists. repeat split; eassumption || reflexivity.
  - right. eexists. split; [eassumption | reflexivity].
Qed.

Lemma step_if_inv : forall c yes no r u, tm_if c yes no r --> u ->
  (exists c', c --> c' /\ u = tm_if c' yes no r) \/
  (exists v k, c = tm_inl v k /\ value v /\ flows_to k.(reader) r /\
     u = tm_protect k.(indirect_reader) yes) \/
  (exists v k, c = tm_inr v k /\ value v /\ flows_to k.(reader) r /\
     u = tm_protect k.(indirect_reader) no).
Proof.
  intros c yes no r u H. inversion H; subst.
  - left. eexists. split; [eassumption | reflexivity].
  - right. left. eexists _, _. repeat split; eassumption || reflexivity.
  - right. right. eexists _, _. repeat split; eassumption || reflexivity.
Qed.

Lemma multi_protect_inv : forall t w,
    multi t w -> value w ->
    forall e l, t = tm_protect l e ->
    exists v, value v /\ multi e v /\ w = protect_value v l.
Proof.
  intros t w Hm. induction Hm as [| t1 t2 t3 Hst Hm IH]; intros Hw e l E.
  - subst t. inversion Hw.
  - subst t1. destruct (step_protect_inv l e t2 Hst) as
      [(v & Heq & Hu & Hv) | (e' & Hstep & Hu)].
    + subst e. subst t2. exists v. split; [exact Hv | split].
      * apply multi_refl.
      * eapply multi_value.
        -- exact Hm.
        -- apply protect_value_value. exact Hv.
    + subst t2. destruct (IH Hw e' l eq_refl) as (v & Hv & Hmv & Heq).
      exists v. split; [exact Hv | split].
      * eapply multi_step; eauto.
      * exact Heq.
Qed.

Lemma abs_no_step : forall T body κ t, ~ step (tm_abs T body κ) t.
Proof. intros T body κ t H; inversion H. Qed.

Lemma multi_normal : forall (s : tm), (forall t, ~ step s t) ->
    forall t w, multi t w -> t = s -> w = s.
Proof.
  intros s Hns t w Hm. induction Hm as [| t1 t2 t3 Hst Hm IH]; intros E.
  - exact E.
  - subst t1. exfalso. eapply Hns. exact Hst.
Qed.

Lemma multi_abs_inv : forall T body κ w,
    multi (tm_abs T body κ) w -> w = tm_abs T body κ.
Proof.
  intros T body κ w Hm.
  eapply multi_normal.
  - apply abs_no_step.
  - exact Hm.
  - reflexivity.
Qed.

Lemma multi_app_inv : forall t w,
    multi t w -> value w ->
    forall f a r, t = tm_app f a r ->
    exists fv, value fv /\ multi f fv /\
      exists av, value av /\ multi a av /\ multi (tm_app fv av r) w.
Proof.
  intros t w Hm. induction Hm as [| t1 t2 t3 Hst Hm IH]; intros Hw f a r E.
  - subst t. inversion Hw.
  - subst t1. destruct (step_app_inv f a r t2 Hst) as
      [(f' & Hstep & Hu) |
       [(a' & Hvf & Hstep & Hu) |
        (T & body & kappa & v & Hf & Ha & Hvabs & Hv & Hflow & Hu)]].
    + (* ST_App1 *) subst t2.
      destruct (IH Hw f' a r eq_refl) as (fv & Hvfv & Hmf & av & Hvav & Hma & Happ).
      exists fv. split; [exact Hvfv | split].
      * eapply multi_step; eauto.
      * exists av. split; [exact Hvav | split; [exact Hma | exact Happ]].
    + (* ST_App2 *) subst t2.
      destruct (IH Hw f a' r eq_refl) as (fv & Hvfv & Hmf & av & Hvav & Hma & Happ).
      exists fv. split; [exact Hvfv | split; [exact Hmf | exists av]].
      split; [exact Hvav | split].
      * eapply multi_step; eauto.
      * exact Happ.
    + (* ST_AppAbs *) subst t2. subst f. subst a.
      exists (tm_abs T body kappa). split; [exact Hvabs | split].
      * apply multi_refl.
      * exists v. split; [exact Hv | split; [apply multi_refl | eapply multi_step; [exact Hst | exact Hm]]].
Qed.

Lemma multi_app_abs : forall t w, multi t w -> value w ->
    forall T body κ a r, t = tm_app (tm_abs T body κ) a r ->
    value a ->
    value (tm_abs T body κ) /\ flows_to κ.(reader) r /\
    exists w', multi (open body a) w' /\ value w' /\ w = protect_value w' κ.(indirect_reader).
Proof.
  intros t w Hm. induction Hm as [| t1 t2 t3 Hst Hm IH]; intros Hw T body κ a r E Hva.
  - subst t. inversion Hw.
  - subst t1. destruct (step_app_inv (tm_abs T body κ) a r t2 Hst) as
      [(f' & Hstep & Hu) |
       [(a' & Hvf' & Hstep & Hu) |
        (T' & body' & kappa' & v & Hf & Ha & Hvabs & Hv & Hflow & Hu)]].
    + (* the abstraction steps: impossible *)
      exfalso. exact (abs_no_step T body κ f' Hstep).
    + (* the argument steps: impossible *)
      exfalso. exact (value_no_step a Hva a' Hstep).
    + (* ST_AppAbs *) inversion Hf; subst.
      destruct (multi_protect_inv _ _ Hm Hw (open body' v) kappa'.(indirect_reader) eq_refl)
        as (w' & Hvw & Hmw & Heq).
      split; [exact Hvabs | split; [exact Hflow | exists w'; split; [exact Hmw | split; [exact Hvw | exact Heq]]]].
Qed.

Lemma multi_pair_inv : forall t w,
    multi t w -> value w ->
    forall t1 t2 κ, t = tm_pair t1 t2 κ ->
    exists v1 v2, value v1 /\ value v2 /\ multi t1 v1 /\ multi t2 v2 /\
      w = tm_pair v1 v2 κ.
Proof.
  intros t w Hm. induction Hm as [| u1 u2 u3 Hst Hm IH]; intros Hw t1 t2 κ E.
  - subst t. inversion Hw; subst. exists t1, t2. repeat split; auto; apply multi_refl.
  - subst u1. destruct (step_pair_inv t1 t2 κ u2 Hst) as
      [(t1' & Hstep & Hu) | (t2' & Hv1 & Hstep & Hu)].
    + (* ST_Pair1 *) subst u2.
      destruct (IH Hw t1' t2 κ eq_refl) as (v1 & v2 & Hv1 & Hv2 & Hm1 & Hm2 & Heq).
      exists v1, v2. repeat split; auto.
      eapply multi_step; eauto.
    + (* ST_Pair2 *) subst u2.
      destruct (IH Hw t1 t2' κ eq_refl) as (v1 & v2 & Hw1 & Hw2 & Hm1 & Hm2 & Heq).
      exists v1, v2. repeat split; auto.
      eapply multi_step; eauto.
Qed.

Lemma multi_fst_inv : forall t w,
    multi t w -> value w ->
    forall t0 r, t = tm_fst t0 r ->
    exists a b κ, value a /\ value b /\ multi t0 (tm_pair a b κ) /\
      multi (tm_protect κ.(indirect_reader) a) w.
Proof.
  intros t w Hm. induction Hm as [| u1 u2 u3 Hst Hm IH]; intros Hw t0 r E.
  - subst t. inversion Hw.
  - subst u1. destruct (step_fst_inv t0 r u2 Hst) as
      [(t' & Hstep & Hu) | (v1 & v2 & κ & Hpair & Hv1 & Hv2 & Hflow & Hu)].
    + (* ST_Fst *) subst u2.
      destruct (IH Hw t' r eq_refl) as (a & b & κ' & Hva & Hvb & Hm0 & Hmw).
      exists a, b, κ'. repeat split; auto. eapply multi_step; eauto.
    + (* ST_FstPair *) subst u2. subst t0.
      exists v1, v2, κ. repeat split; auto.
      apply multi_refl.
Qed.

Lemma multi_snd_inv : forall t w,
    multi t w -> value w ->
    forall t0 r, t = tm_snd t0 r ->
    exists a b κ, value a /\ value b /\ multi t0 (tm_pair a b κ) /\
      multi (tm_protect κ.(indirect_reader) b) w.
Proof.
  intros t w Hm. induction Hm as [| u1 u2 u3 Hst Hm IH]; intros Hw t0 r E.
  - subst t. inversion Hw.
  - subst u1. destruct (step_snd_inv t0 r u2 Hst) as
      [(t' & Hstep & Hu) | (v1 & v2 & κ & Hpair & Hv1 & Hv2 & Hflow & Hu)].
    + (* ST_Snd *) subst u2.
      destruct (IH Hw t' r eq_refl) as (a & b & κ' & Hva & Hvb & Hm0 & Hmw).
      exists a, b, κ'. repeat split; auto. eapply multi_step; eauto.
    + (* ST_SndPair *) subst u2. subst t0.
      exists v1, v2, κ. repeat split; auto.
      apply multi_refl.
Qed.

Lemma multi_inl_inv : forall t w,
    multi t w -> value w ->
    forall t0 κ, t = tm_inl t0 κ ->
    exists v, value v /\ multi t0 v /\ w = tm_inl v κ.
Proof.
  intros t w Hm. induction Hm as [| u1 u2 u3 Hst Hm IH]; intros Hw t0 κ E.
  - subst t. inversion Hw; subst. exists t0. repeat split; auto. apply multi_refl.
  - subst u1. destruct (step_inl_inv t0 κ u2 Hst) as (t' & Hstep & Hu).
    subst u2. destruct (IH Hw t' κ eq_refl) as (v & Hv & Hm0 & Heq).
    exists v. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_inr_inv : forall t w,
    multi t w -> value w ->
    forall t0 κ, t = tm_inr t0 κ ->
    exists v, value v /\ multi t0 v /\ w = tm_inr v κ.
Proof.
  intros t w Hm. induction Hm as [| u1 u2 u3 Hst Hm IH]; intros Hw t0 κ E.
  - subst t. inversion Hw; subst. exists t0. repeat split; auto. apply multi_refl.
  - subst u1. destruct (step_inr_inv t0 κ u2 Hst) as (t' & Hstep & Hu).
    subst u2. destruct (IH Hw t' κ eq_refl) as (v & Hv & Hm0 & Heq).
    exists v. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_case_inv : forall t w,
    multi t w -> value w ->
    forall t0 body1 body2 r, t = tm_case t0 body1 body2 r ->
    (exists v κ, value v /\ multi t0 (tm_inl v κ) /\
       multi (tm_protect κ.(indirect_reader) (open body1 v)) w) \/
    (exists v κ, value v /\ multi t0 (tm_inr v κ) /\
       multi (tm_protect κ.(indirect_reader) (open body2 v)) w).
Proof.
  intros t w Hm. induction Hm as [| u1 u2 u3 Hst Hm IH]; intros Hw t0 body1 body2 r E.
  - subst t. inversion Hw.
  - subst u1. destruct (step_case_inv t0 body1 body2 r u2 Hst) as
      [(t' & Hstep & Hu) |
       [(v & κ & Hinl & Hv & Hflow & Hu) |
        (v & κ & Hinr & Hv & Hflow & Hu)]].
    + (* ST_Case *) subst u2.
      destruct (IH Hw t' body1 body2 r eq_refl)
        as [(v & κ & Hv & Hm0 & Hmw) | (v & κ & Hv & Hm0 & Hmw)].
      * left. exists v, κ. repeat split; auto. eapply multi_step; eauto.
      * right. exists v, κ. repeat split; auto. eapply multi_step; eauto.
    + (* ST_CaseLeft *) subst u2. subst t0.
      left. exists v, κ. repeat split; auto.
      apply multi_refl.
    + (* ST_CaseRight *) subst u2. subst t0.
      right. exists v, κ. repeat split; auto.
      apply multi_refl.
Qed.

Lemma multi_if_inv : forall t w,
    multi t w -> value w ->
    forall c yes no r, t = tm_if c yes no r ->
    (exists v k, value v /\ multi c (tm_inl v k) /\ multi (tm_protect k.(indirect_reader) yes) w) \/
    (exists v k, value v /\ multi c (tm_inr v k) /\ multi (tm_protect k.(indirect_reader) no) w).
Proof.
  intros t w Hm. induction Hm as [| u1 u2 u3 Hst Hm IH]; intros Hw c yes no r E.
  - subst t. inversion Hw.
  - subst u1. destruct (step_if_inv c yes no r u2 Hst) as
      [(c' & Hstep & Hu) |
       [(v & k & Hinl & Hv & Hflow & Hu) |
        (v & k & Hinr & Hv & Hflow & Hu)]].
    + (* ST_If *) subst u2.
      destruct (IH Hw c' yes no r eq_refl)
        as [(v & k & Hv & Hm0 & Hmw) | (v & k & Hv & Hm0 & Hmw)].
      * left. exists v, k. repeat split; auto. eapply multi_step; eauto.
      * right. exists v, k. repeat split; auto. eapply multi_step; eauto.
    + (* ST_IfTrue *) subst u2. subst c.
      left. exists v, k. repeat split; auto.
      apply multi_refl.
    + (* ST_IfFalse *) subst u2. subst c.
      right. exists v, k. repeat split; auto.
      apply multi_refl.
Qed.

(* ---------------- The logical relation ---------------- *)

(* [VRp l T L] is the relation on values of type [ty_protect L T] observed
   at level [l].  [L] records an extra protection applied to the top-level
   security annotation of [T]. *)

Fixpoint VRp (l : label) (T : ty) (L : label) {struct T} : tm -> tm -> Prop :=
  match T with
  | Ty_Unit κ =>
      fun v1 v2 =>
        if flowb (join κ.(indirect_reader) L) l then
          match v1, v2 with
          | tm_unit _, tm_unit _ => True
          | _, _ => False
          end
        else True
  | Ty_Sum T1 T2 κ =>
      fun v1 v2 =>
        if flowb (join κ.(indirect_reader) L) l then
          match v1, v2 with
          | tm_inl u1 _, tm_inl u2 _ => VRp l T1 Low u1 u2
          | tm_inr u1 _, tm_inr u2 _ => VRp l T2 Low u1 u2
          | _, _ => False
          end
        else True
  | Ty_Prod T1 T2 κ =>
      fun v1 v2 =>
        if flowb (join κ.(indirect_reader) L) l then
          match v1, v2 with
          | tm_pair u1 w1 _, tm_pair u2 w2 _ => VRp l T1 Low u1 u2 /\ VRp l T2 Low w1 w2
          | _, _ => False
          end
        else True
  | Ty_Arrow T1 T2 κ =>
      fun v1 v2 =>
        if flowb (join κ.(indirect_reader) L) l then
          match v1, v2 with
          | tm_abs _ _ _, tm_abs _ _ _ =>
              forall (u1 u2 : tm) (r : label),
                value u1 -> value u2 ->
                flows_to (join κ.(reader) L) r ->
                VRp l T1 Low u1 u2 ->
                (forall w1 w2 : tm,
                  tm_app v1 u1 r -->* w1 -> value w1 ->
                  tm_app v2 u2 r -->* w2 -> value w2 ->
                  VRp l T2 (join κ.(indirect_reader) L) w1 w2)
          | _, _ => False
          end
        else True
  end.

Definition VR (l : label) (T : ty) : tm -> tm -> Prop := VRp l T Low.

Definition TR (l : label) (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, t1 -->* v1 -> value v1 -> t2 -->* v2 -> value v2 -> VR l T v1 v2.

Definition EnvRel (l : label) (Γ : context) (σ1 σ2 : atom -> tm) : Prop :=
  (forall x, lc_at 0 (σ1 x)) /\
  (forall x, lc_at 0 (σ2 x)) /\
  (forall x T, lookup_context x Γ = Some T -> TR l T (σ1 x) (σ2 x)).

(* Unfolding lemmas for the relation. *)

Lemma VRp_unit : forall l κ L v1 v2,
    VRp l (Ty_Unit κ) L v1 v2 =
    (if flowb (join κ.(indirect_reader) L) l then
       match v1, v2 with
       | tm_unit _, tm_unit _ => True
       | _, _ => False
       end
     else True).
Proof. reflexivity. Qed.

Lemma VRp_sum : forall l T1 T2 κ L v1 v2,
    VRp l (Ty_Sum T1 T2 κ) L v1 v2 =
    (if flowb (join κ.(indirect_reader) L) l then
       match v1, v2 with
       | tm_inl u1 _, tm_inl u2 _ => VRp l T1 Low u1 u2
       | tm_inr u1 _, tm_inr u2 _ => VRp l T2 Low u1 u2
       | _, _ => False
       end
     else True).
Proof. reflexivity. Qed.

Lemma VRp_prod : forall l T1 T2 κ L v1 v2,
    VRp l (Ty_Prod T1 T2 κ) L v1 v2 =
    (if flowb (join κ.(indirect_reader) L) l then
       match v1, v2 with
       | tm_pair u1 w1 _, tm_pair u2 w2 _ => VRp l T1 Low u1 u2 /\ VRp l T2 Low w1 w2
       | _, _ => False
       end
     else True).
Proof. reflexivity. Qed.

Lemma VRp_arrow : forall l T1 T2 κ L v1 v2,
    VRp l (Ty_Arrow T1 T2 κ) L v1 v2 =
    (if flowb (join κ.(indirect_reader) L) l then
       match v1, v2 with
       | tm_abs _ _ _, tm_abs _ _ _ =>
           forall (u1 u2 : tm) (r : label),
             value u1 -> value u2 ->
             flows_to (join κ.(reader) L) r ->
             VRp l T1 Low u1 u2 ->
             (forall w1 w2 : tm,
               tm_app v1 u1 r -->* w1 -> value w1 ->
               tm_app v2 u2 r -->* w2 -> value w2 ->
               VRp l T2 (join κ.(indirect_reader) L) w1 w2)
       | _, _ => False
       end
     else True).
Proof. reflexivity. Qed.

Lemma VR_ty_protect : forall l T L v1 v2,
    VRp l T L v1 v2 <-> VR l (ty_protect L T) v1 v2.
Proof.
  intros l [κ | T1 T2 κ | T1 T2 κ | T1 T2 κ] L v1 v2; cbn [VRp VR ty_protect];
  repeat rewrite join_low_r; split; intro H; exact H.
Qed.

Lemma VR_hidden : forall l T v1 v2,
    flowb (security_of T).(indirect_reader) l = false -> VR l T v1 v2.
Proof.
  intros l [κ | T1 T2 κ | T1 T2 κ | T1 T2 κ] v1 v2 E;
  cbn [security_of] in E; cbn [VR VRp];
  repeat rewrite join_low_r; rewrite E; trivial.
Qed.

(* ---------------- Introduction and elimination for the relation ---------------- *)

Lemma VR_unit_intro : forall l κ v1 v2 κ1 κ2,
    flowb κ.(indirect_reader) l = true ->
    v1 = tm_unit κ1 -> v2 = tm_unit κ2 ->
    VR l (Ty_Unit κ) v1 v2.
Proof.
  intros. subst v1. subst v2.
  cbn [VR VRp]. repeat rewrite join_low_r. rewrite H. trivial.
Qed.

Lemma VR_unit_inv : forall l κ v1 v2,
    VR l (Ty_Unit κ) v1 v2 -> flowb κ.(indirect_reader) l = true ->
    exists κ1 κ2, v1 = tm_unit κ1 /\ v2 = tm_unit κ2.
Proof.
  intros l κ v1 v2 H E.
  cbn [VR VRp] in H. repeat rewrite join_low_r in H. rewrite E in H.
  destruct v1; cbn in H; try contradiction; destruct v2; cbn in H; try contradiction;
  eauto.
Qed.

Lemma VR_sum_inv : forall l T1 T2 κ v1 v2,
    VR l (Ty_Sum T1 T2 κ) v1 v2 -> flowb κ.(indirect_reader) l = true ->
    (exists u1 u2 κ1 κ2, v1 = tm_inl u1 κ1 /\ v2 = tm_inl u2 κ2 /\ VR l T1 u1 u2) \/
    (exists u1 u2 κ1 κ2, v1 = tm_inr u1 κ1 /\ v2 = tm_inr u2 κ2 /\ VR l T2 u1 u2).
Proof.
  intros l T1 T2 κ v1 v2 H E.
  cbn [VR VRp] in H. repeat rewrite join_low_r in H. rewrite E in H.
  destruct v1; cbn in H; try contradiction; destruct v2; cbn in H; try contradiction.
  - left. eexists _, _, _, _. split; [reflexivity | split; [reflexivity | exact H]].
  - right. eexists _, _, _, _. split; [reflexivity | split; [reflexivity | exact H]].
Qed.

Lemma VR_prod_inv : forall l T1 T2 κ v1 v2,
    VR l (Ty_Prod T1 T2 κ) v1 v2 -> flowb κ.(indirect_reader) l = true ->
    exists u1 w1 u2 w2 κ1 κ2,
      v1 = tm_pair u1 w1 κ1 /\ v2 = tm_pair u2 w2 κ2 /\ VR l T1 u1 u2 /\ VR l T2 w1 w2.
Proof.
  intros l T1 T2 κ v1 v2 H E.
  cbn [VR VRp] in H. repeat rewrite join_low_r in H. rewrite E in H.
  destruct v1; cbn in H; try contradiction; destruct v2; cbn in H; try contradiction.
  destruct H as [H1 H2]. eexists _, _, _, _, _, _. repeat split; try reflexivity; auto.
Qed.

Lemma VR_sum_inl_intro : forall l T1 T2 κ v1 v2 κ1 κ2,
    flowb κ.(indirect_reader) l = true ->
    VR l T1 v1 v2 -> VR l (Ty_Sum T1 T2 κ) (tm_inl v1 κ1) (tm_inl v2 κ2).
Proof.
  intros. cbn [VR VRp]. repeat rewrite join_low_r. rewrite H. cbn. exact H0.
Qed.

Lemma VR_sum_inr_intro : forall l T1 T2 κ v1 v2 κ1 κ2,
    flowb κ.(indirect_reader) l = true ->
    VR l T2 v1 v2 -> VR l (Ty_Sum T1 T2 κ) (tm_inr v1 κ1) (tm_inr v2 κ2).
Proof.
  intros. cbn [VR VRp]. repeat rewrite join_low_r. rewrite H. cbn. exact H0.
Qed.

Lemma VR_prod_intro : forall l T1 T2 κ u1 w1 u2 w2 κ1 κ2,
    flowb κ.(indirect_reader) l = true ->
    VR l T1 u1 u2 -> VR l T2 w1 w2 ->
    VR l (Ty_Prod T1 T2 κ) (tm_pair u1 w1 κ1) (tm_pair u2 w2 κ2).
Proof.
  intros. cbn [VR VRp]. repeat rewrite join_low_r. rewrite H. cbn. split; assumption.
Qed.

Lemma VR_arrow_inv : forall l T1 T2 κ v1 v2,
    VR l (Ty_Arrow T1 T2 κ) v1 v2 -> flowb κ.(indirect_reader) l = true ->
    exists (T1' T2' : ty) (b1 b2 : tm) (κ1 κ2 : security),
      v1 = tm_abs T1' b1 κ1 /\ v2 = tm_abs T2' b2 κ2 /\
      (forall (u1 u2 : tm) (r : label),
         value u1 -> value u2 ->
         flows_to κ.(reader) r ->
         VR l T1 u1 u2 ->
         forall w1 w2,
           tm_app v1 u1 r -->* w1 -> value w1 ->
           tm_app v2 u2 r -->* w2 -> value w2 ->
           VR l (ty_protect κ.(indirect_reader) T2) w1 w2).
Proof.
  intros l T1 T2 κ v1 v2 H E.
  cbn [VR VRp] in H. repeat rewrite join_low_r in H. rewrite E in H.
  destruct v1; cbn in H; try contradiction; destruct v2; cbn in H; try contradiction.
  eexists _, _, _, _, _, _. split; [reflexivity | split; [reflexivity |]].
  intros u1 u2 r Hvu1 Hvu2 Hr Hrel w1 w2 Hm1 Hw1 Hm2 Hw2.
  apply (proj1 (VR_ty_protect l T2 κ.(indirect_reader) w1 w2)).
  apply (H u1 u2 r Hvu1 Hvu2 Hr Hrel w1 w2 Hm1 Hw1 Hm2 Hw2).
Qed.

Lemma VR_arrow_intro : forall l T1 T2 κ v1 v2 T1' T2' b1 b2 κ1 κ2,
    flowb κ.(indirect_reader) l = true ->
    v1 = tm_abs T1' b1 κ1 -> v2 = tm_abs T2' b2 κ2 ->
    (forall (u1 u2 : tm) (r : label),
       value u1 -> value u2 ->
       flows_to κ.(reader) r ->
       VR l T1 u1 u2 ->
       forall w1 w2,
         tm_app v1 u1 r -->* w1 -> value w1 ->
         tm_app v2 u2 r -->* w2 -> value w2 ->
         VR l (ty_protect κ.(indirect_reader) T2) w1 w2) ->
    VR l (Ty_Arrow T1 T2 κ) v1 v2.
Proof.
  intros l T1 T2 κ v1 v2 T1' T2' b1 b2 κ1 κ2 E E1 E2 Hcl.
  cbn [VR VRp]. repeat rewrite join_low_r. rewrite E. subst v1. subst v2. cbn.
  intros u1 u2 r Hvu1 Hvu2 Hr Hrel w1 w2 Hm1 Hw1 Hm2 Hw2.
  apply (proj2 (VR_ty_protect l T2 κ.(indirect_reader) w1 w2)).
  apply (Hcl u1 u2 r Hvu1 Hvu2 Hr Hrel w1 w2 Hm1 Hw1 Hm2 Hw2).
Qed.

(* ---------------- Annotation monotonicity ---------------- *)

Lemma join_flows_mono_reader : forall a L1 L2,
    flows_to L1 L2 -> flows_to (join a L1) (join a L2).
Proof. intros; apply join_mono; [apply flows_to_refl | assumption]. Qed.

Lemma VRp_ann_mono : forall T l L1 L2,
    flows_to L1 L2 ->
    forall v1 v2, VRp l T L1 v1 v2 -> VRp l T L2 v1 v2.
Proof.
  induction T as [κ | T1 IH1 T2 IH2 κ | T1 IH1 T2 IH2 κ | T1 IH1 T2 IH2 κ];
  intros l L1 L2 Hflow v1 v2 H; cbn [VRp] in *.
  - (* unit *)
    destruct (flowb (join κ.(indirect_reader) L2) l) eqn:E2.
    + assert (E1 : flowb (join κ.(indirect_reader) L1) l = true).
      { apply flowb_true. eapply flows_to_trans.
        - apply join_mono; [apply flows_to_refl | exact Hflow].
        - apply flowb_true. exact E2. }
      rewrite E1 in H. destruct v1; cbn in H; try contradiction;
      destruct v2; cbn in H; try contradiction; exact I.
    + exact I.
  - (* sum *)
    destruct (flowb (join κ.(indirect_reader) L2) l) eqn:E2.
    + assert (E1 : flowb (join κ.(indirect_reader) L1) l = true).
      { apply flowb_true. eapply flows_to_trans.
        - apply join_mono; [apply flows_to_refl | exact Hflow].
        - apply flowb_true. exact E2. }
      rewrite E1 in H. destruct v1; cbn in H; try contradiction;
      destruct v2; cbn in H; try contradiction; assumption.
    + exact I.
  - (* prod *)
    destruct (flowb (join κ.(indirect_reader) L2) l) eqn:E2.
    + assert (E1 : flowb (join κ.(indirect_reader) L1) l = true).
      { apply flowb_true. eapply flows_to_trans.
        - apply join_mono; [apply flows_to_refl | exact Hflow].
        - apply flowb_true. exact E2. }
      rewrite E1 in H. destruct v1; cbn in H; try contradiction;
      destruct v2; cbn in H; try contradiction; assumption.
    + exact I.
  - (* arrow *)
    destruct (flowb (join κ.(indirect_reader) L2) l) eqn:E2.
    + assert (E1 : flowb (join κ.(indirect_reader) L1) l = true).
      { apply flowb_true. eapply flows_to_trans.
        - apply join_mono; [apply flows_to_refl | exact Hflow].
        - apply flowb_true. exact E2. }
      rewrite E1 in H. destruct v1; cbn in H; try contradiction;
      destruct v2; cbn in H; try contradiction.
      intros u1 u2 r Hvu1 Hvu2 Hr Hrel w1 w2 Hm1 Hw1 Hm2 Hw2.
      apply (IH2 l (join κ.(indirect_reader) L1) (join κ.(indirect_reader) L2)).
      * apply join_mono; [apply flows_to_refl | exact Hflow].
      * apply (H u1 u2 r Hvu1 Hvu2).
        -- eapply flows_to_trans.
           ++ apply join_mono; [apply flows_to_refl | exact Hflow].
           ++ exact Hr.
        -- exact Hrel.
        -- exact Hm1. -- exact Hw1. -- exact Hm2. -- exact Hw2.
    + exact I.
Qed.

(* ---------------- Insensitivity of the relation to value annotations ---------------- *)

Lemma multi_protect_value : forall e w l,
    multi e w -> value w -> multi (tm_protect l e) (protect_value w l).
Proof. apply multi_protect. Qed.

Lemma value_abs_ann : forall T body κ κ',
    value (tm_abs T body κ) -> value (tm_abs T body κ').
Proof.
  intros T body κ κ' H. inversion H. apply v_abs. assumption.
Qed.

Lemma VRp_val_ann : forall T l L,
    forall v1 v2, VRp l T L v1 v2 ->
    forall M1 M2, VRp l T L (protect_value v1 M1) (protect_value v2 M2).
Proof.
  induction T as [κ | T1 IH1 T2 IH2 κ | T1 IH1 T2 IH2 κ | T1 IH1 T2 IH2 κ];
  intros l L v1 v2 H M1 M2; cbn [VRp] in *.
  - (* unit *)
    destruct (flowb (join κ.(indirect_reader) L) l) eqn:E.
    + destruct v1; cbn in H |- *; try contradiction;
      destruct v2; cbn in H |- *; try contradiction; exact I.
    + exact I.
  - (* sum *)
    destruct (flowb (join κ.(indirect_reader) L) l) eqn:E.
    + destruct v1; cbn in H |- *; try contradiction;
      destruct v2; cbn in H |- *; try contradiction; assumption.
    + exact I.
  - (* prod *)
    destruct (flowb (join κ.(indirect_reader) L) l) eqn:E.
    + destruct v1; cbn in H |- *; try contradiction;
      destruct v2; cbn in H |- *; try contradiction; assumption.
    + exact I.
  - (* arrow *)
    destruct (flowb (join κ.(indirect_reader) L) l) eqn:E.
    + destruct v1; cbn in H |- *; try contradiction;
      destruct v2; cbn in H |- *; try contradiction.
      intros u1 u2 r Hvu1 Hvu2 Hr Hrel w1 w2 Hm1 Hw1 Hm2 Hw2.
      (* decompose the protected applications *)
      destruct (multi_app_abs _ _ Hm1 Hw1 t v1 (protect_security s M1) u1 r eq_refl Hvu1)
        as (Hvabs1 & Hflow1 & w1' & Hm1' & Hw1' & Heq1).
      destruct (multi_app_abs _ _ Hm2 Hw2 t0 v2 (protect_security s0 M2) u2 r eq_refl Hvu2)
        as (Hvabs2 & Hflow2 & w2' & Hm2' & Hw2' & Heq2).
      assert (Hflow1' : flows_to s.(reader) r).
      { cbn [protect_security] in Hflow1. eapply flows_to_trans; [apply flows_to_join_l | exact Hflow1]. }
      assert (Hflow2' : flows_to s0.(reader) r).
      { cbn [protect_security] in Hflow2. eapply flows_to_trans; [apply flows_to_join_l | exact Hflow2]. }
      assert (Hvabs1' : value (tm_abs t v1 s)) by (eapply value_abs_ann; exact Hvabs1).
      assert (Hvabs2' : value (tm_abs t0 v2 s0)) by (eapply value_abs_ann; exact Hvabs2).
      (* the unprotected applications evaluate as well *)
      assert (Hsrc1 : multi (tm_app (tm_abs t v1 s) u1 r) (protect_value w1' s.(indirect_reader))).
      { eapply multi_trans.
        - apply multi_step with (t2 := tm_protect s.(indirect_reader) (open v1 u1)).
          + apply ST_AppAbs; [exact Hvabs1' | exact Hvu1 | exact Hflow1'].
          + apply multi_refl.
        - apply multi_protect. exact Hm1'. exact Hw1'. }
      assert (Hsrc2 : multi (tm_app (tm_abs t0 v2 s0) u2 r) (protect_value w2' s0.(indirect_reader))).
      { eapply multi_trans.
        - apply multi_step with (t2 := tm_protect s0.(indirect_reader) (open v2 u2)).
          + apply ST_AppAbs; [exact Hvabs2' | exact Hvu2 | exact Hflow2'].
          + apply multi_refl.
        - apply multi_protect. exact Hm2'. exact Hw2'. }
      assert (Hcl := H u1 u2 r Hvu1 Hvu2 Hr Hrel
                       (protect_value w1' s.(indirect_reader))
                       (protect_value w2' s0.(indirect_reader))
                       Hsrc1 (protect_value_value _ _ Hw1')
                       Hsrc2 (protect_value_value _ _ Hw2')).
      rewrite Heq1. rewrite Heq2.
      rewrite protect_security_ind. rewrite protect_security_ind.
      rewrite <- protect_value_protect. rewrite <- protect_value_protect.
      apply (IH2 l (join κ.(indirect_reader) L) _ _ Hcl M1 M2).
    + exact I.
Qed.

(* ---------------- Subtyping monotonicity ---------------- *)

Lemma flows_to_low_l : forall L : label, flows_to Low L.
Proof. intros []; simpl; trivial. Qed.

Lemma VRp_subtype : forall T U, subtype T U ->
    forall l L1 L2, flows_to L1 L2 ->
    forall v1 v2, VRp l T L1 v1 v2 -> VRp l U L2 v1 v2.
Proof.
  intros T U Hsub. induction Hsub as
    [ κ1 κ2 Hwf1 Hwf2 Hle
    | T1 T2 U1 U2 κ1 κ2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hle
    | T1 T2 U1 U2 κ1 κ2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hle
    | T1 T2 U1 U2 κ1 κ2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hle
    | T U V Hsub1 IH1 Hsub2 IH2 ];
  intros l L1 L2 Hflow v1 v2 H.
  - (* S_Unit *)
    unfold security_le in Hle. destruct Hle as [Hle_r Hle_i].
    cbn [VRp] in H |- *.
    destruct (flowb (join κ2.(indirect_reader) L2) l) eqn:E2.
    + assert (E1 : flowb (join κ1.(indirect_reader) L1) l = true).
      { apply flowb_true. eapply flows_to_trans.
        - apply join_mono; [exact Hle_i | exact Hflow].
        - apply flowb_true. exact E2. }
      rewrite E1 in H. destruct v1; cbn in H; try contradiction;
      destruct v2; cbn in H; try contradiction; exact I.
    + exact I.
  - (* S_Sum *)
    unfold security_le in Hle. destruct Hle as [Hle_r Hle_i].
    cbn [VRp] in H |- *.
    destruct (flowb (join κ2.(indirect_reader) L2) l) eqn:E2.
    + assert (E1 : flowb (join κ1.(indirect_reader) L1) l = true).
      { apply flowb_true. eapply flows_to_trans.
        - apply join_mono; [exact Hle_i | exact Hflow].
        - apply flowb_true. exact E2. }
      rewrite E1 in H.
      destruct v1; cbn in H; try contradiction; destruct v2; cbn in H; try contradiction;
      cbn.
      * apply (IH1 l Low Low (flows_to_refl Low) _ _ H).
      * apply (IH2 l Low Low (flows_to_refl Low) _ _ H).
    + exact I.
  - (* S_Prod *)
    unfold security_le in Hle. destruct Hle as [Hle_r Hle_i].
    cbn [VRp] in H |- *.
    destruct (flowb (join κ2.(indirect_reader) L2) l) eqn:E2.
    + assert (E1 : flowb (join κ1.(indirect_reader) L1) l = true).
      { apply flowb_true. eapply flows_to_trans.
        - apply join_mono; [exact Hle_i | exact Hflow].
        - apply flowb_true. exact E2. }
      rewrite E1 in H.
      destruct v1; cbn in H; try contradiction; destruct v2; cbn in H; try contradiction;
      cbn; destruct H as [H1 H2]; split.
      * apply (IH1 l Low Low (flows_to_refl Low) _ _ H1).
      * apply (IH2 l Low Low (flows_to_refl Low) _ _ H2).
    + exact I.
  - (* S_Arrow *)
    unfold security_le in Hle. destruct Hle as [Hle_r Hle_i].
    cbn [VRp] in H |- *.
    destruct (flowb (join κ2.(indirect_reader) L2) l) eqn:E2.
    + assert (E1 : flowb (join κ1.(indirect_reader) L1) l = true).
      { apply flowb_true. eapply flows_to_trans.
        - apply join_mono; [exact Hle_i | exact Hflow].
        - apply flowb_true. exact E2. }
      rewrite E1 in H.
      destruct v1; cbn in H; try contradiction; destruct v2; cbn in H; try contradiction.
      intros u1 u2 r Hvu1 Hvu2 Hr Hrel w1 w2 Hm1 Hw1 Hm2 Hw2.
      apply (IH2 l (join κ1.(indirect_reader) L1) (join κ2.(indirect_reader) L2)).
      * apply join_mono; [exact Hle_i | exact Hflow].
      * apply (H u1 u2 r Hvu1 Hvu2).
        -- eapply flows_to_trans.
           ++ apply join_mono; [exact Hle_r | exact Hflow].
           ++ exact Hr.
        -- apply (IH1 l Low Low (flows_to_refl Low) _ _ Hrel).
        -- exact Hm1. -- exact Hw1. -- exact Hm2. -- exact Hw2.
    + exact I.
  - (* S_Trans *)
    apply (IH2 l L2 L2 (flows_to_refl L2) v1 v2).
    apply (IH1 l L1 L2 Hflow v1 v2 H).
Qed.

(* ---------------- Basic TR lemmas ---------------- *)

Lemma TR_hidden : forall l T t1 t2,
    flowb (security_of T).(indirect_reader) l = false -> TR l T t1 t2.
Proof.
  intros l T t1 t2 E v1 v2 Hm1 Hv1 Hm2 Hv2. apply VR_hidden. exact E.
Qed.

Lemma TR_unit : forall l κ, TR l (Ty_Unit κ) (tm_unit κ) (tm_unit κ).
Proof.
  intros l κ w1 w2 Hm1 Hw1 Hm2 Hw2.
  rewrite (multi_value _ _ Hm1 (v_unit κ)). rewrite (multi_value _ _ Hm2 (v_unit κ)).
  cbn [VR VRp]. repeat rewrite join_low_r.
  destruct (flowb κ.(indirect_reader) l); cbn; exact I.
Qed.

Lemma TR_value : forall l T v1 v2,
    VR l T v1 v2 -> value v1 -> value v2 -> TR l T v1 v2.
Proof.
  intros l T v1 v2 H Hv1 Hv2 w1 w2 Hm1 Hw1 Hm2 Hw2.
  rewrite (multi_value _ _ Hm1 Hv1). rewrite (multi_value _ _ Hm2 Hv2). exact H.
Qed.

Lemma TR_ty_protect : forall l T L e1 e2,
    TR l T e1 e2 -> TR l (ty_protect L T) (tm_protect L e1) (tm_protect L e2).
Proof.
  intros l T L e1 e2 H w1 w2 Hm1 Hw1 Hm2 Hw2.
  destruct (multi_protect_inv _ _ Hm1 Hw1 e1 L eq_refl) as (v1 & Hv1 & Hm1' & Heq1).
  destruct (multi_protect_inv _ _ Hm2 Hw2 e2 L eq_refl) as (v2 & Hv2 & Hm2' & Heq2).
  rewrite Heq1. rewrite Heq2.
  apply (proj1 (VR_ty_protect l T L (protect_value v1 L) (protect_value v2 L))).
  apply (VRp_val_ann T l L v1 v2).
  apply (VRp_ann_mono T l Low L). apply flows_to_low_l.
  apply (H v1 v2 Hm1' Hv1 Hm2' Hv2).
Qed.

Lemma flowb_protect_hidden : forall T κ l,
    flowb κ.(indirect_reader) l = false ->
    flowb (security_of (ty_protect κ.(indirect_reader) T)).(indirect_reader) l = false.
Proof.
  intros T κ l E. rewrite security_of_ty_protect. rewrite protect_security_ind.
  apply flowb_join_high. exact E.
Qed.

Lemma TR_app : forall l T1 T2 κ r f1 f2 a1 a2,
    TR l (Ty_Arrow T1 T2 κ) f1 f2 ->
    TR l T1 a1 a2 ->
    flows_to κ.(reader) r ->
    TR l (ty_protect κ.(indirect_reader) T2) (tm_app f1 a1 r) (tm_app f2 a2 r).
Proof.
  intros l T1 T2 κ r f1 f2 a1 a2 Hf Ha Hflow w1 w2 Hm1 Hw1 Hm2 Hw2.
  destruct (multi_app_inv _ _ Hm1 Hw1 f1 a1 r eq_refl)
    as (fv1 & Hvfv1 & Hmf1 & av1 & Hvav1 & Hma1 & Happ1).
  destruct (multi_app_inv _ _ Hm2 Hw2 f2 a2 r eq_refl)
    as (fv2 & Hvfv2 & Hmf2 & av2 & Hvav2 & Hma2 & Happ2).
  assert (HVR := Hf fv1 fv2 Hmf1 Hvfv1 Hmf2 Hvfv2).
  unfold VR in HVR. rewrite VRp_arrow in HVR. repeat rewrite join_low_r in HVR.
  destruct (flowb κ.(indirect_reader) l) eqn:E.
  - destruct fv1; cbn in HVR; try contradiction; destruct fv2; cbn in HVR; try contradiction.
    assert (Hrel : VR l T1 av1 av2) by (apply (Ha av1 av2 Hma1 Hvav1 Hma2 Hvav2)).
    assert (Hcl := HVR av1 av2 r Hvav1 Hvav2 Hflow Hrel w1 w2 Happ1 Hw1 Happ2 Hw2).
    repeat rewrite join_low_r in Hcl.
    apply (proj1 (VR_ty_protect l T2 κ.(indirect_reader) w1 w2)). exact Hcl.
  - apply VR_hidden. apply flowb_protect_hidden. exact E.
Qed.

Lemma TR_pair : forall l T1 T2 κ u1 u2 v1 v2,
    TR l T1 u1 u2 -> TR l T2 v1 v2 ->
    TR l (Ty_Prod T1 T2 κ) (tm_pair u1 v1 κ) (tm_pair u2 v2 κ).
Proof.
  intros l T1 T2 κ u1 u2 v1 v2 Hu Hv w1 w2 Hm1 Hw1 Hm2 Hw2.
  destruct (multi_pair_inv _ _ Hm1 Hw1 u1 v1 κ eq_refl)
    as (a1 & b1 & Hva1 & Hvb1 & Hmu1 & Hmv1 & Heq1).
  destruct (multi_pair_inv _ _ Hm2 Hw2 u2 v2 κ eq_refl)
    as (a2 & b2 & Hva2 & Hvb2 & Hmu2 & Hmv2 & Heq2).
  rewrite Heq1. rewrite Heq2.
  unfold VR. rewrite VRp_prod. rewrite join_low_r.
  destruct (flowb κ.(indirect_reader) l) eqn:E.
  - cbn. split.
    + apply (Hu a1 a2 Hmu1 Hva1 Hmu2 Hva2).
    + apply (Hv b1 b2 Hmv1 Hvb1 Hmv2 Hvb2).
  - exact I.
Qed.

Lemma TR_inl : forall l T1 T2 κ t1 t2,
    TR l T1 t1 t2 -> TR l (Ty_Sum T1 T2 κ) (tm_inl t1 κ) (tm_inl t2 κ).
Proof.
  intros l T1 T2 κ t1 t2 H w1 w2 Hm1 Hw1 Hm2 Hw2.
  destruct (multi_inl_inv _ _ Hm1 Hw1 t1 κ eq_refl) as (v1 & Hv1 & Hm1' & Heq1).
  destruct (multi_inl_inv _ _ Hm2 Hw2 t2 κ eq_refl) as (v2 & Hv2 & Hm2' & Heq2).
  rewrite Heq1. rewrite Heq2.
  unfold VR. rewrite VRp_sum. rewrite join_low_r.
  destruct (flowb κ.(indirect_reader) l) eqn:E.
  - cbn. apply (H v1 v2 Hm1' Hv1 Hm2' Hv2).
  - exact I.
Qed.

Lemma TR_inr : forall l T1 T2 κ t1 t2,
    TR l T2 t1 t2 -> TR l (Ty_Sum T1 T2 κ) (tm_inr t1 κ) (tm_inr t2 κ).
Proof.
  intros l T1 T2 κ t1 t2 H w1 w2 Hm1 Hw1 Hm2 Hw2.
  destruct (multi_inr_inv _ _ Hm1 Hw1 t1 κ eq_refl) as (v1 & Hv1 & Hm1' & Heq1).
  destruct (multi_inr_inv _ _ Hm2 Hw2 t2 κ eq_refl) as (v2 & Hv2 & Hm2' & Heq2).
  rewrite Heq1. rewrite Heq2.
  unfold VR. rewrite VRp_sum. rewrite join_low_r.
  destruct (flowb κ.(indirect_reader) l) eqn:E.
  - cbn. apply (H v1 v2 Hm1' Hv1 Hm2' Hv2).
  - exact I.
Qed.

Lemma TR_fst : forall l T1 T2 κ r t1 t2,
    TR l (Ty_Prod T1 T2 κ) t1 t2 ->
    flows_to κ.(reader) r ->
    TR l (ty_protect κ.(indirect_reader) T1) (tm_fst t1 r) (tm_fst t2 r).
Proof.
  intros l T1 T2 κ r t1 t2 H Hflow w1 w2 Hm1 Hw1 Hm2 Hw2.
  destruct (multi_fst_inv _ _ Hm1 Hw1 t1 r eq_refl)
    as (a1 & b1 & κ1 & Hva1 & Hvb1 & Hm1p & Hmw1).
  destruct (multi_fst_inv _ _ Hm2 Hw2 t2 r eq_refl)
    as (a2 & b2 & κ2 & Hva2 & Hvb2 & Hm2p & Hmw2).
  assert (HVR := H _ _ Hm1p (v_pair _ _ _ Hva1 Hvb1) Hm2p (v_pair _ _ _ Hva2 Hvb2)).
  unfold VR in HVR. rewrite VRp_prod in HVR. repeat rewrite join_low_r in HVR.
  destruct (flowb κ.(indirect_reader) l) eqn:E.
  - cbn in HVR. destruct HVR as [Hrel _].
    destruct (multi_protect_inv _ _ Hmw1 Hw1 a1 κ1.(indirect_reader) eq_refl)
      as (a1' & Hva1' & Hma1' & Heq1).
    destruct (multi_protect_inv _ _ Hmw2 Hw2 a2 κ2.(indirect_reader) eq_refl)
      as (a2' & Hva2' & Hma2' & Heq2).
    assert (Ha1 : a1' = a1) by (eapply multi_value; eauto).
    assert (Ha2 : a2' = a2) by (eapply multi_value; eauto).
    subst a1'. subst a2'. rewrite Heq1. rewrite Heq2.
    apply (proj1 (VR_ty_protect l T1 κ.(indirect_reader) _ _)).
    apply (VRp_val_ann T1 l κ.(indirect_reader) a1 a2).
    apply (VRp_ann_mono T1 l Low κ.(indirect_reader)). apply flows_to_low_l.
    exact Hrel.
  - apply VR_hidden. apply flowb_protect_hidden. exact E.
Qed.

Lemma TR_snd : forall l T1 T2 κ r t1 t2,
    TR l (Ty_Prod T1 T2 κ) t1 t2 ->
    flows_to κ.(reader) r ->
    TR l (ty_protect κ.(indirect_reader) T2) (tm_snd t1 r) (tm_snd t2 r).
Proof.
  intros l T1 T2 κ r t1 t2 H Hflow w1 w2 Hm1 Hw1 Hm2 Hw2.
  destruct (multi_snd_inv _ _ Hm1 Hw1 t1 r eq_refl)
    as (a1 & b1 & κ1 & Hva1 & Hvb1 & Hm1p & Hmw1).
  destruct (multi_snd_inv _ _ Hm2 Hw2 t2 r eq_refl)
    as (a2 & b2 & κ2 & Hva2 & Hvb2 & Hm2p & Hmw2).
  assert (HVR := H _ _ Hm1p (v_pair _ _ _ Hva1 Hvb1) Hm2p (v_pair _ _ _ Hva2 Hvb2)).
  unfold VR in HVR. rewrite VRp_prod in HVR. repeat rewrite join_low_r in HVR.
  destruct (flowb κ.(indirect_reader) l) eqn:E.
  - cbn in HVR. destruct HVR as [_ Hrel].
    destruct (multi_protect_inv _ _ Hmw1 Hw1 b1 κ1.(indirect_reader) eq_refl)
      as (b1' & Hvb1' & Hmb1' & Heq1).
    destruct (multi_protect_inv _ _ Hmw2 Hw2 b2 κ2.(indirect_reader) eq_refl)
      as (b2' & Hvb2' & Hmb2' & Heq2).
    assert (Hb1 : b1' = b1) by (eapply multi_value; eauto).
    assert (Hb2 : b2' = b2) by (eapply multi_value; eauto).
    subst b1'. subst b2'. rewrite Heq1. rewrite Heq2.
    apply (proj1 (VR_ty_protect l T2 κ.(indirect_reader) _ _)).
    apply (VRp_val_ann T2 l κ.(indirect_reader) b1 b2).
    apply (VRp_ann_mono T2 l Low κ.(indirect_reader)). apply flows_to_low_l.
    exact Hrel.
  - apply VR_hidden. apply flowb_protect_hidden. exact E.
Qed.

Lemma TR_case : forall l T1 T2 T κ r t1 t2 b11 b12 b21 b22,
    TR l (Ty_Sum T1 T2 κ) t1 t2 ->
    (forall u1 u2, value u1 -> value u2 -> VR l T1 u1 u2 ->
       TR l T (open b11 u1) (open b12 u2)) ->
    (forall u1 u2, value u1 -> value u2 -> VR l T2 u1 u2 ->
       TR l T (open b21 u1) (open b22 u2)) ->
    flows_to κ.(reader) r ->
    TR l (ty_protect κ.(indirect_reader) T)
       (tm_case t1 b11 b21 r) (tm_case t2 b12 b22 r).
Proof.
  intros l T1 T2 T κ r t1 t2 b11 b12 b21 b22 Ht Hb1 Hb2 Hflow w1 w2 Hm1 Hw1 Hm2 Hw2.
  destruct (multi_case_inv _ _ Hm1 Hw1 t1 b11 b21 r eq_refl)
    as [(v1 & κ1 & Hv1 & Hm1s & Hmw1) | (v1 & κ1 & Hv1 & Hm1s & Hmw1)];
  destruct (multi_case_inv _ _ Hm2 Hw2 t2 b12 b22 r eq_refl)
    as [(v2 & κ2 & Hv2 & Hm2s & Hmw2) | (v2 & κ2 & Hv2 & Hm2s & Hmw2)].
  - (* inl / inl *)
    assert (HVR : VR l (Ty_Sum T1 T2 κ) (tm_inl v1 κ1) (tm_inl v2 κ2))
      by (apply (Ht _ _ Hm1s (v_inl _ _ Hv1) Hm2s (v_inl _ _ Hv2))).
    destruct (flowb κ.(indirect_reader) l) eqn:E.
    + cbn [VR VRp] in HVR. repeat repeat rewrite join_low_r in HVR. rewrite E in HVR. cbn in HVR.
      destruct (multi_protect_inv _ _ Hmw1 Hw1 (open b11 v1) κ1.(indirect_reader) eq_refl)
        as (u1 & Hu1 & Hmu1 & Heq1).
      destruct (multi_protect_inv _ _ Hmw2 Hw2 (open b12 v2) κ2.(indirect_reader) eq_refl)
        as (u2 & Hu2 & Hmu2 & Heq2).
      rewrite Heq1. rewrite Heq2.
      apply (proj1 (VR_ty_protect l T κ.(indirect_reader) _ _)).
      apply (VRp_val_ann T l κ.(indirect_reader) u1 u2).
      apply (VRp_ann_mono T l Low κ.(indirect_reader)). apply flows_to_low_l.
      apply (Hb1 v1 v2 Hv1 Hv2 HVR u1 u2 Hmu1 Hu1 Hmu2 Hu2).
    + apply VR_hidden. apply flowb_protect_hidden. exact E.
  - (* inl / inr *)
    assert (HVR : VR l (Ty_Sum T1 T2 κ) (tm_inl v1 κ1) (tm_inr v2 κ2))
      by (apply (Ht _ _ Hm1s (v_inl _ _ Hv1) Hm2s (v_inr _ _ Hv2))).
    destruct (flowb κ.(indirect_reader) l) eqn:E.
    + cbn [VR VRp] in HVR. repeat repeat rewrite join_low_r in HVR. rewrite E in HVR. cbn in HVR.
      contradiction.
    + apply VR_hidden. apply flowb_protect_hidden. exact E.
  - (* inr / inl *)
    assert (HVR : VR l (Ty_Sum T1 T2 κ) (tm_inr v1 κ1) (tm_inl v2 κ2))
      by (apply (Ht _ _ Hm1s (v_inr _ _ Hv1) Hm2s (v_inl _ _ Hv2))).
    destruct (flowb κ.(indirect_reader) l) eqn:E.
    + cbn [VR VRp] in HVR. repeat repeat rewrite join_low_r in HVR. rewrite E in HVR. cbn in HVR.
      contradiction.
    + apply VR_hidden. apply flowb_protect_hidden. exact E.
  - (* inr / inr *)
    assert (HVR : VR l (Ty_Sum T1 T2 κ) (tm_inr v1 κ1) (tm_inr v2 κ2))
      by (apply (Ht _ _ Hm1s (v_inr _ _ Hv1) Hm2s (v_inr _ _ Hv2))).
    destruct (flowb κ.(indirect_reader) l) eqn:E.
    + cbn [VR VRp] in HVR. repeat repeat rewrite join_low_r in HVR. rewrite E in HVR. cbn in HVR.
      destruct (multi_protect_inv _ _ Hmw1 Hw1 (open b21 v1) κ1.(indirect_reader) eq_refl)
        as (u1 & Hu1 & Hmu1 & Heq1).
      destruct (multi_protect_inv _ _ Hmw2 Hw2 (open b22 v2) κ2.(indirect_reader) eq_refl)
        as (u2 & Hu2 & Hmu2 & Heq2).
      rewrite Heq1. rewrite Heq2.
      apply (proj1 (VR_ty_protect l T κ.(indirect_reader) _ _)).
      apply (VRp_val_ann T l κ.(indirect_reader) u1 u2).
      apply (VRp_ann_mono T l Low κ.(indirect_reader)). apply flows_to_low_l.
      apply (Hb2 v1 v2 Hv1 Hv2 HVR u1 u2 Hmu1 Hu1 Hmu2 Hu2).
    + apply VR_hidden. apply flowb_protect_hidden. exact E.
Qed.

Lemma TR_if : forall l T k r c1 c2 y1 y2 n1 n2,
    TR l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) c1 c2 ->
    TR l T y1 y2 ->
    TR l T n1 n2 ->
    flows_to k.(reader) r ->
    TR l (ty_protect k.(indirect_reader) T) (tm_if c1 y1 n1 r) (tm_if c2 y2 n2 r).
Proof.
  intros l T k r c1 c2 y1 y2 n1 n2 Hc Hy Hn Hflow w1 w2 Hm1 Hw1 Hm2 Hw2.
  destruct (multi_if_inv _ _ Hm1 Hw1 c1 y1 n1 r eq_refl)
    as [(v1 & k1 & Hv1 & Hm1s & Hmw1) | (v1 & k1 & Hv1 & Hm1s & Hmw1)];
  destruct (multi_if_inv _ _ Hm2 Hw2 c2 y2 n2 r eq_refl)
    as [(v2 & k2 & Hv2 & Hm2s & Hmw2) | (v2 & k2 & Hv2 & Hm2s & Hmw2)].
  - (* inl / inl: both take the then-branch *)
    assert (HVR : VR l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                     (tm_inl v1 k1) (tm_inl v2 k2))
      by (apply (Hc _ _ Hm1s (v_inl _ _ Hv1) Hm2s (v_inl _ _ Hv2))).
    destruct (flowb k.(indirect_reader) l) eqn:E.
    + cbn [VR VRp] in HVR. repeat repeat rewrite join_low_r in HVR. rewrite E in HVR. cbn in HVR.
      destruct (multi_protect_inv _ _ Hmw1 Hw1 y1 k1.(indirect_reader) eq_refl)
        as (u1 & Hu1 & Hmu1 & Heq1).
      destruct (multi_protect_inv _ _ Hmw2 Hw2 y2 k2.(indirect_reader) eq_refl)
        as (u2 & Hu2 & Hmu2 & Heq2).
      rewrite Heq1. rewrite Heq2.
      apply (proj1 (VR_ty_protect l T k.(indirect_reader) _ _)).
      apply (VRp_val_ann T l k.(indirect_reader) u1 u2).
      apply (VRp_ann_mono T l Low k.(indirect_reader)). apply flows_to_low_l.
      apply (Hy u1 u2 Hmu1 Hu1 Hmu2 Hu2).
    + apply VR_hidden. apply flowb_protect_hidden. exact E.
  - (* inl / inr *)
    assert (HVR : VR l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                     (tm_inl v1 k1) (tm_inr v2 k2))
      by (apply (Hc _ _ Hm1s (v_inl _ _ Hv1) Hm2s (v_inr _ _ Hv2))).
    destruct (flowb k.(indirect_reader) l) eqn:E.
    + cbn [VR VRp] in HVR. repeat repeat rewrite join_low_r in HVR. rewrite E in HVR. cbn in HVR.
      contradiction.
    + apply VR_hidden. apply flowb_protect_hidden. exact E.
  - (* inr / inl *)
    assert (HVR : VR l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                     (tm_inr v1 k1) (tm_inl v2 k2))
      by (apply (Hc _ _ Hm1s (v_inr _ _ Hv1) Hm2s (v_inl _ _ Hv2))).
    destruct (flowb k.(indirect_reader) l) eqn:E.
    + cbn [VR VRp] in HVR. repeat repeat rewrite join_low_r in HVR. rewrite E in HVR. cbn in HVR.
      contradiction.
    + apply VR_hidden. apply flowb_protect_hidden. exact E.
  - (* inr / inr: both take the else-branch *)
    assert (HVR : VR l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                     (tm_inr v1 k1) (tm_inr v2 k2))
      by (apply (Hc _ _ Hm1s (v_inr _ _ Hv1) Hm2s (v_inr _ _ Hv2))).
    destruct (flowb k.(indirect_reader) l) eqn:E.
    + cbn [VR VRp] in HVR. repeat repeat rewrite join_low_r in HVR. rewrite E in HVR. cbn in HVR.
      destruct (multi_protect_inv _ _ Hmw1 Hw1 n1 k1.(indirect_reader) eq_refl)
        as (u1 & Hu1 & Hmu1 & Heq1).
      destruct (multi_protect_inv _ _ Hmw2 Hw2 n2 k2.(indirect_reader) eq_refl)
        as (u2 & Hu2 & Hmu2 & Heq2).
      rewrite Heq1. rewrite Heq2.
      apply (proj1 (VR_ty_protect l T k.(indirect_reader) _ _)).
      apply (VRp_val_ann T l k.(indirect_reader) u1 u2).
      apply (VRp_ann_mono T l Low k.(indirect_reader)). apply flows_to_low_l.
      apply (Hn u1 u2 Hmu1 Hu1 Hmu2 Hu2).
    + apply VR_hidden. apply flowb_protect_hidden. exact E.
Qed.

(* ---------------- Environments ---------------- *)

Definition extend_env (x : atom) (u : tm) (σ : atom -> tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else σ y.

Lemma extend_env_same : forall x u σ, extend_env x u σ x = u.
Proof. intros. unfold extend_env. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_env_other : forall x y u σ,
    y <> x -> extend_env x u σ y = σ y.
Proof.
  intros x y u σ Hxy. unfold extend_env.
  destruct (Nat.eqb y x) eqn:E; [| reflexivity].
  apply Nat.eqb_eq in E. contradiction.
Qed.

Lemma lookup_update_same : forall Γ x T,
    lookup_context x (update Γ x T) = Some T.
Proof.
  intros Γ x T. unfold update. cbn. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_update_other : forall Γ x y T,
    y <> x -> lookup_context y (update Γ x T) = lookup_context y Γ.
Proof.
  intros Γ x y T Hxy. unfold update. cbn.
  destruct (Nat.eqb y x) eqn:E; [| reflexivity].
  apply Nat.eqb_eq in E. contradiction.
Qed.

Lemma EnvRel_update : forall l Γ x T σ1 σ2 u1 u2,
    EnvRel l Γ σ1 σ2 ->
    value u1 -> value u2 -> VR l T u1 u2 ->
    EnvRel l (update Γ x T) (extend_env x u1 σ1) (extend_env x u2 σ2).
Proof.
  intros l Γ x T σ1 σ2 u1 u2 [Hlc1 [Hlc2 Hlook]] Hvu1 Hvu2 Hrel.
  split; [| split].
  - intro y. unfold extend_env. destruct (Nat.eqb y x); [apply value_lc; exact Hvu1 | apply Hlc1].
  - intro y. unfold extend_env. destruct (Nat.eqb y x); [apply value_lc; exact Hvu2 | apply Hlc2].
  - intros y U Hy.
    destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. rewrite lookup_update_same in Hy. injection Hy as Hy. subst U.
      rewrite (extend_env_same x u1 σ1). rewrite (extend_env_same x u2 σ2).
      apply TR_value; [exact Hrel | exact Hvu1 | exact Hvu2].
    + apply Nat.eqb_neq in E. rewrite lookup_update_other in Hy; [| exact E].
      rewrite (extend_env_other x y u1 σ1 E). rewrite (extend_env_other x y u2 σ2 E).
      apply Hlook. exact Hy.
Qed.

(* ---------------- Contexts and substitution ---------------- *)

Fixpoint context_atoms (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs T C' κ => context_atoms C'
  | C_AppLeft C' t2 r => context_atoms C' ++ fv t2
  | C_AppRight t1 C' r => fv t1 ++ context_atoms C'
  | C_PairLeft C' t2 κ => context_atoms C' ++ fv t2
  | C_PairRight t1 C' κ => fv t1 ++ context_atoms C'
  | C_Fst C' r => context_atoms C'
  | C_Snd C' r => context_atoms C'
  | C_Inl C' κ => context_atoms C'
  | C_Inr C' κ => context_atoms C'
  | C_CaseScrutinee C' b1 b2 r => context_atoms C' ++ fv b1 ++ fv b2
  | C_CaseLeft t0 C' b2 r => fv t0 ++ context_atoms C' ++ fv b2
  | C_CaseRight t0 b1 C' r => fv t0 ++ fv b1 ++ context_atoms C'
  | C_Protect l C' => context_atoms C'
  | C_IfCondition C' y n r => context_atoms C' ++ fv y ++ fv n
  | C_IfThen c C' n r => fv c ++ context_atoms C' ++ fv n
  | C_IfElse c y C' r => fv c ++ fv y ++ context_atoms C'
  end.

Lemma not_in_app_l : forall (x : atom) l1 l2,
    ~ In x (l1 ++ l2) -> ~ In x l1.
Proof. intros x l1 l2 H Hin. apply H. apply In_app_l. exact Hin. Qed.

Lemma not_in_app_r : forall (x : atom) l1 l2,
    ~ In x (l1 ++ l2) -> ~ In x l2.
Proof. intros x l1 l2 H Hin. apply H. apply In_app_r. exact Hin. Qed.

Lemma subst_env_extend_id : forall x t s,
    ~ In x (fv s) ->
    subst_env (extend_env x t (fun y => tm_fvar y)) s = s.
Proof.
  intros x t s Hx. rewrite <- subst_env_fvar_id.
  apply subst_env_ext. intros y Hy.
  unfold extend_env. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. exfalso. apply Hx. exact Hy.
  - reflexivity.
Qed.

Lemma plug_subst_env : forall C x u,
    ~ In x (context_atoms C) ->
    subst_env (extend_env x u (fun y => tm_fvar y)) (plug C (tm_fvar x)) = plug C u.
Proof.
  induction C; simpl; intros x u Hx.
  - (* C_Hole *) rewrite (extend_env_same x u (fun y => tm_fvar y)). reflexivity.
  - (* C_Abs *) f_equal. apply IHC. exact Hx.
  - (* C_AppLeft *) f_equal.
    + apply IHC. exact (not_in_app_l x (context_atoms C) (fv t) Hx).
    + apply subst_env_extend_id. exact (not_in_app_r x (context_atoms C) (fv t) Hx).
  - (* C_AppRight *) f_equal.
    + apply subst_env_extend_id. exact (not_in_app_l x (fv t) (context_atoms C) Hx).
    + apply IHC. exact (not_in_app_r x (fv t) (context_atoms C) Hx).
  - (* C_PairLeft *) f_equal.
    + apply IHC. exact (not_in_app_l x (context_atoms C) (fv t) Hx).
    + apply subst_env_extend_id. exact (not_in_app_r x (context_atoms C) (fv t) Hx).
  - (* C_PairRight *) f_equal.
    + apply subst_env_extend_id. exact (not_in_app_l x (fv t) (context_atoms C) Hx).
    + apply IHC. exact (not_in_app_r x (fv t) (context_atoms C) Hx).
  - (* C_Fst *) f_equal. apply IHC. exact Hx.
  - (* C_Snd *) f_equal. apply IHC. exact Hx.
  - (* C_Inl *) f_equal. apply IHC. exact Hx.
  - (* C_Inr *) f_equal. apply IHC. exact Hx.
  - (* C_CaseScrutinee *) f_equal.
    + apply IHC. exact (not_in_app_l x (context_atoms C) (fv t ++ fv t0) Hx).
    + apply subst_env_extend_id.
      exact (not_in_app_l x (fv t) (fv t0)
               (not_in_app_r x (context_atoms C) (fv t ++ fv t0) Hx)).
    + apply subst_env_extend_id.
      exact (not_in_app_r x (fv t) (fv t0)
               (not_in_app_r x (context_atoms C) (fv t ++ fv t0) Hx)).
  - (* C_CaseLeft *) f_equal.
    + apply subst_env_extend_id. exact (not_in_app_l x (fv t) (context_atoms C ++ fv t0) Hx).
    + apply IHC.
      exact (not_in_app_l x (context_atoms C) (fv t0)
               (not_in_app_r x (fv t) (context_atoms C ++ fv t0) Hx)).
    + apply subst_env_extend_id.
      exact (not_in_app_r x (context_atoms C) (fv t0)
               (not_in_app_r x (fv t) (context_atoms C ++ fv t0) Hx)).
  - (* C_CaseRight *) f_equal.
    + apply subst_env_extend_id. exact (not_in_app_l x (fv t) (fv t0 ++ context_atoms C) Hx).
    + apply subst_env_extend_id.
      exact (not_in_app_l x (fv t0) (context_atoms C)
               (not_in_app_r x (fv t) (fv t0 ++ context_atoms C) Hx)).
    + apply IHC.
      exact (not_in_app_r x (fv t0) (context_atoms C)
               (not_in_app_r x (fv t) (fv t0 ++ context_atoms C) Hx)).
  - (* C_Protect *) f_equal. apply IHC. exact Hx.
  - (* C_IfCondition *) f_equal.
    + apply IHC. exact (not_in_app_l x (context_atoms C) (fv t ++ fv t0) Hx).
    + apply subst_env_extend_id.
      exact (not_in_app_l x (fv t) (fv t0)
               (not_in_app_r x (context_atoms C) (fv t ++ fv t0) Hx)).
    + apply subst_env_extend_id.
      exact (not_in_app_r x (fv t) (fv t0)
               (not_in_app_r x (context_atoms C) (fv t ++ fv t0) Hx)).
  - (* C_IfThen *) f_equal.
    + apply subst_env_extend_id. exact (not_in_app_l x (fv t) (context_atoms C ++ fv t0) Hx).
    + apply IHC.
      exact (not_in_app_l x (context_atoms C) (fv t0)
               (not_in_app_r x (fv t) (context_atoms C ++ fv t0) Hx)).
    + apply subst_env_extend_id.
      exact (not_in_app_r x (context_atoms C) (fv t0)
               (not_in_app_r x (fv t) (context_atoms C ++ fv t0) Hx)).
  - (* C_IfElse *) f_equal.
    + apply subst_env_extend_id. exact (not_in_app_l x (fv t) (fv t0 ++ context_atoms C) Hx).
    + apply subst_env_extend_id.
      exact (not_in_app_l x (fv t0) (context_atoms C)
               (not_in_app_r x (fv t) (fv t0 ++ context_atoms C) Hx)).
    + apply IHC.
      exact (not_in_app_r x (fv t0) (context_atoms C)
               (not_in_app_r x (fv t) (fv t0 ++ context_atoms C) Hx)).
Qed.



(* ---------------- The fundamental theorem ---------------- *)

Lemma fundamental : forall l Γ t T,
    has_type Γ t T ->
    forall σ1 σ2, EnvRel l Γ σ1 σ2 ->
      TR l T (subst_env σ1 t) (subst_env σ2 t).
Proof.
  intros l Γ t T H.
  induction H as
    [ Γ x T0 Hlook Hwf
    | Γ κ Hwf
    | L Γ T1 body T2 κ HwfT1 Hwfκ Hbody IHbody
    | Γ t1 t2 T1 T2 κ r Ht1 IH1 Ht2 IH2 Hflow
    | Γ t1 t2 T1 T2 κ Ht1 IH1 Ht2 IH2 Hwfκ
    | Γ t T1 T2 κ r Ht IHt Hflow
    | Γ t T1 T2 κ r Ht IHt Hflow
    | Γ t T1 T2 κ Ht IHt HwfT2 Hwfκ
    | Γ t T1 T2 κ HwfT1 Ht IHt Hwfκ
    | L Γ t0 body1 body2 T1 T2 T κ r Ht IHt Hflow Hb1 IHb1 Hb2 IHb2
    | Γ t T l0 Ht IHt
    | Γ t T U Ht IHt Hsub
    | Γ c yes no k T r Hc IHc Hy IHy Hn IHn Hflow ];
  intros σ1 σ2 Henv.
  - (* T_Var *) apply (proj2 (proj2 Henv)). exact Hlook.
  - (* T_Unit *) apply TR_unit.
  - (* T_Abs *)
    cbn [subst_env].
    destruct (exists_fresh_two L (fv body)) as (x & HxL & Hxbody).
    intros w1 w2 Hm1 Hw1 Hm2 Hw2.
    rewrite (multi_abs_inv T1 (subst_env σ1 body) κ w1 Hm1).
    rewrite (multi_abs_inv T1 (subst_env σ2 body) κ w2 Hm2).
    destruct (flowb κ.(indirect_reader) l) eqn:E.
    + apply (VR_arrow_intro l T1 T2 κ
               (tm_abs T1 (subst_env σ1 body) κ) (tm_abs T1 (subst_env σ2 body) κ)
               T1 T1 (subst_env σ1 body) (subst_env σ2 body) κ κ E eq_refl eq_refl).
      intros u1 u2 r Hvu1 Hvu2 Hr Hrel w1' w2' Hm1' Hw1' Hm2' Hw2'.
      destruct (multi_app_abs _ _ Hm1' Hw1' T1 (subst_env σ1 body) κ u1 r eq_refl Hvu1)
        as (Hvabs1 & Hflow1 & v1' & Hmv1 & Hv1' & Heq1).
      destruct (multi_app_abs _ _ Hm2' Hw2' T1 (subst_env σ2 body) κ u2 r eq_refl Hvu2)
        as (Hvabs2 & Hflow2 & v2' & Hmv2 & Hv2' & Heq2).
      rewrite Heq1. rewrite Heq2.
      apply (proj1 (VR_ty_protect l T2 κ.(indirect_reader)
                     (protect_value v1' κ.(indirect_reader))
                     (protect_value v2' κ.(indirect_reader)))).
      apply (VRp_val_ann T2 l κ.(indirect_reader) v1' v2').
      * apply (VRp_ann_mono T2 l Low κ.(indirect_reader)). apply flows_to_low_l.
        assert (Henv' : EnvRel l (update Γ x T1)
                          (extend_env x u1 σ1) (extend_env x u2 σ2)).
        { apply EnvRel_update; [exact Henv | exact Hvu1 | exact Hvu2 | exact Hrel]. }
        assert (Hb := IHbody x HxL _ _ Henv').
        rewrite (subst_env_open_fvar (extend_env x u1 σ1) (proj1 Henv') body x) in Hb.
        rewrite (subst_env_open_fvar (extend_env x u2 σ2) (proj1 (proj2 Henv')) body x) in Hb.
        rewrite (extend_env_same x u1 σ1) in Hb.
        rewrite (extend_env_same x u2 σ2) in Hb.
        unfold extend_env in Hb.
        rewrite (subst_env_notin σ1 x u1 body Hxbody) in Hb.
        rewrite (subst_env_notin σ2 x u2 body Hxbody) in Hb.
        apply (Hb v1' v2' Hmv1 Hv1' Hmv2 Hv2').
    + apply VR_hidden. exact E.
  - (* T_App *)
    cbn [subst_env].
    exact (TR_app l T1 T2 κ r (subst_env σ1 t1) (subst_env σ2 t1)
             (subst_env σ1 t2) (subst_env σ2 t2)
             (IH1 σ1 σ2 Henv) (IH2 σ1 σ2 Henv) Hflow).
  - (* T_Pair *)
    cbn [subst_env].
    exact (TR_pair l T1 T2 κ (subst_env σ1 t1) (subst_env σ2 t1)
             (subst_env σ1 t2) (subst_env σ2 t2)
             (IH1 σ1 σ2 Henv) (IH2 σ1 σ2 Henv)).
  - (* T_Fst *)
    cbn [subst_env].
    exact (TR_fst l T1 T2 κ r (subst_env σ1 t) (subst_env σ2 t)
             (IHt σ1 σ2 Henv) Hflow).
  - (* T_Snd *)
    cbn [subst_env].
    exact (TR_snd l T1 T2 κ r (subst_env σ1 t) (subst_env σ2 t)
             (IHt σ1 σ2 Henv) Hflow).
  - (* T_Inl *)
    cbn [subst_env].
    exact (TR_inl l T1 T2 κ (subst_env σ1 t) (subst_env σ2 t) (IHt σ1 σ2 Henv)).
  - (* T_Inr *)
    cbn [subst_env].
    exact (TR_inr l T1 T2 κ (subst_env σ1 t) (subst_env σ2 t) (IHt σ1 σ2 Henv)).
  - (* T_Case *)
    cbn [subst_env].
    apply (TR_case l T1 T2 T κ r (subst_env σ1 t0) (subst_env σ2 t0)
             (subst_env σ1 body1) (subst_env σ2 body1)
             (subst_env σ1 body2) (subst_env σ2 body2)).
    + apply (IHt σ1 σ2 Henv).
    + (* first branch *)
      intros u1 u2 Hvu1 Hvu2 Hrel.
      destruct (exists_fresh_two L (fv body1)) as (x & HxL & Hxb).
      assert (Henv' : EnvRel l (update Γ x T1)
                        (extend_env x u1 σ1) (extend_env x u2 σ2)).
      { apply EnvRel_update; [exact Henv | exact Hvu1 | exact Hvu2 | exact Hrel]. }
      assert (Hb := IHb1 x HxL _ _ Henv').
      rewrite (subst_env_open_fvar (extend_env x u1 σ1) (proj1 Henv') body1 x) in Hb.
      rewrite (subst_env_open_fvar (extend_env x u2 σ2) (proj1 (proj2 Henv')) body1 x) in Hb.
      rewrite (extend_env_same x u1 σ1) in Hb.
      rewrite (extend_env_same x u2 σ2) in Hb.
      unfold extend_env in Hb.
      rewrite (subst_env_notin σ1 x u1 body1 Hxb) in Hb.
      rewrite (subst_env_notin σ2 x u2 body1 Hxb) in Hb.
      exact Hb.
    + (* second branch *)
      intros u1 u2 Hvu1 Hvu2 Hrel.
      destruct (exists_fresh_two L (fv body2)) as (x & HxL & Hxb).
      assert (Henv' : EnvRel l (update Γ x T2)
                        (extend_env x u1 σ1) (extend_env x u2 σ2)).
      { apply EnvRel_update; [exact Henv | exact Hvu1 | exact Hvu2 | exact Hrel]. }
      assert (Hb := IHb2 x HxL _ _ Henv').
      rewrite (subst_env_open_fvar (extend_env x u1 σ1) (proj1 Henv') body2 x) in Hb.
      rewrite (subst_env_open_fvar (extend_env x u2 σ2) (proj1 (proj2 Henv')) body2 x) in Hb.
      rewrite (extend_env_same x u1 σ1) in Hb.
      rewrite (extend_env_same x u2 σ2) in Hb.
      unfold extend_env in Hb.
      rewrite (subst_env_notin σ1 x u1 body2 Hxb) in Hb.
      rewrite (subst_env_notin σ2 x u2 body2 Hxb) in Hb.
      exact Hb.
    + exact Hflow.
  - (* T_Protect *)
    cbn [subst_env].
    exact (TR_ty_protect l T l0 (subst_env σ1 t) (subst_env σ2 t) (IHt σ1 σ2 Henv)).
  - (* T_Sub *)
    intros w1 w2 Hm1 Hw1 Hm2 Hw2.
    apply (VRp_subtype T U Hsub l Low Low (flows_to_refl Low) w1 w2).
    apply (IHt σ1 σ2 Henv w1 w2 Hm1 Hw1 Hm2 Hw2).
  - (* T_If *)
    cbn [subst_env].
    apply (TR_if l T k r (subst_env σ1 c) (subst_env σ2 c)
             (subst_env σ1 yes) (subst_env σ2 yes)
             (subst_env σ1 no) (subst_env σ2 no)).
    + apply (IHc σ1 σ2 Henv).
    + apply (IHy σ1 σ2 Henv).
    + apply (IHn σ1 σ2 Henv).
    + exact Hflow.
Qed.

(* ---------------- Erasing security annotations ---------------- *)

Fixpoint all_visible (l : label) (T : ty) : Prop :=
  flows_to (security_of T).(indirect_reader) l /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      all_visible l T1 /\ all_visible l T2
  end.

Lemma transparent_all_visible : forall T κ l,
    transparent_at κ T -> flows_to κ.(indirect_reader) l -> all_visible l T.
Proof.
  induction T; intros κ l Ht Hflow; simpl in Ht.
  - (* unit *) destruct Ht as [Hle _]. unfold security_le in Hle. destruct Hle as [_ Hi].
    split; [| trivial]. eapply flows_to_trans; [exact Hi | exact Hflow].
  - (* sum *) destruct Ht as [Hle [Ht1 Ht2]]. unfold security_le in Hle. destruct Hle as [_ Hi].
    split; [| split].
    + eapply flows_to_trans; [exact Hi | exact Hflow].
    + apply (IHT1 κ l); [exact Ht1 | exact Hflow].
    + apply (IHT2 κ l); [exact Ht2 | exact Hflow].
  - (* prod *) destruct Ht as [Hle [Ht1 Ht2]]. unfold security_le in Hle. destruct Hle as [_ Hi].
    split; [| split].
    + eapply flows_to_trans; [exact Hi | exact Hflow].
    + apply (IHT1 κ l); [exact Ht1 | exact Hflow].
    + apply (IHT2 κ l); [exact Ht2 | exact Hflow].
  - (* arrow *) destruct Ht as [Hle [Ht1 Ht2]]. unfold security_le in Hle. destruct Hle as [_ Hi].
    split; [| split].
    + eapply flows_to_trans; [exact Hi | exact Hflow].
    + apply (IHT1 κ l); [exact Ht1 | exact Hflow].
    + apply (IHT2 κ l); [exact Ht2 | exact Hflow].
Qed.

Lemma VR_erase : forall l T v1 v2,
    ground T -> all_visible l T -> VR l T v1 v2 ->
    erase_security v1 = erase_security v2.
Proof.
  induction T as [κ | T1 IH1 T2 IH2 κ | T1 IH1 T2 IH2 κ | T1 IH1 T2 IH2 κ];
  intros v1 v2 Hg Hv HVR; simpl in Hg, Hv.
  - (* unit *)
    destruct Hv as [Hflow _]. apply flowb_true in Hflow.
    cbn [VR VRp] in HVR. repeat rewrite join_low_r in HVR. rewrite Hflow in HVR.
    destruct v1; cbn in HVR; try contradiction; destruct v2; cbn in HVR; try contradiction;
    reflexivity.
  - (* sum *)
    destruct Hg as [Hg1 Hg2]. destruct Hv as [Hflow [Hv1 Hv2]]. apply flowb_true in Hflow.
    cbn [VR VRp] in HVR. repeat rewrite join_low_r in HVR. rewrite Hflow in HVR.
    destruct v1; cbn in HVR; try contradiction; destruct v2; cbn in HVR; try contradiction; simpl.
    + f_equal. apply IH1; [exact Hg1 | exact Hv1 | exact HVR].
    + f_equal. apply IH2; [exact Hg2 | exact Hv2 | exact HVR].
  - (* prod *)
    destruct Hg as [Hg1 Hg2]. destruct Hv as [Hflow [Hv1 Hv2]]. apply flowb_true in Hflow.
    cbn [VR VRp] in HVR. repeat rewrite join_low_r in HVR. rewrite Hflow in HVR.
    destruct v1; cbn in HVR; try contradiction; destruct v2; cbn in HVR; try contradiction; simpl.
    destruct HVR as [Hr1 Hr2]. f_equal.
    + apply IH1; [exact Hg1 | exact Hv1 | exact Hr1].
    + apply IH2; [exact Hg2 | exact Hv2 | exact Hr2].
  - (* arrow *) destruct Hg.
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 Hctx Hgnd Htr Hnflow.
  destruct Hctx as [L Hctx].
  destruct (exists_fresh (L ++ context_atoms C)) as (x & Hx).
  assert (HxL : ~ In x L) by (intro H; apply Hx; apply In_app_l; exact H).
  assert (HxC : ~ In x (context_atoms C)) by (intro H; apply Hx; apply In_app_r; exact H).
  set (l := (security_of T_result).(indirect_reader)).
  assert (Hplug1 : subst_env (extend_env x t1 (fun y => tm_fvar y)) (plug C (tm_fvar x)) = plug C t1).
  { apply plug_subst_env. exact HxC. }
  assert (Hplug2 : subst_env (extend_env x t2 (fun y => tm_fvar y)) (plug C (tm_fvar x)) = plug C t2).
  { apply plug_subst_env. exact HxC. }
  assert (Henv : EnvRel l (update empty x T_secret)
                   (extend_env x t1 (fun y => tm_fvar y))
                   (extend_env x t2 (fun y => tm_fvar y))).
  { split; [| split].
    - intro y. unfold extend_env. destruct (Nat.eqb y x); [exact (has_type_lc empty t1 T_secret Ht1) | simpl; trivial].
    - intro y. unfold extend_env. destruct (Nat.eqb y x); [exact (has_type_lc empty t2 T_secret Ht2) | simpl; trivial].
    - intros y T Hy.
      destruct (Nat.eqb y x) eqn:E.
      + apply Nat.eqb_eq in E. subst y. rewrite lookup_update_same in Hy.
        injection Hy as Hy. subst T.
        rewrite (extend_env_same x t1 (fun y => tm_fvar y)).
        rewrite (extend_env_same x t2 (fun y => tm_fvar y)).
        apply TR_hidden. apply flowb_false. unfold l. exact Hnflow.
      + apply Nat.eqb_neq in E. rewrite lookup_update_other in Hy; [| exact E].
        simpl in Hy. discriminate Hy. }
  assert (HTR := fundamental l (update empty x T_secret) (plug C (tm_fvar x)) T_result
                   (Hctx x HxL)
                   (extend_env x t1 (fun y => tm_fvar y))
                   (extend_env x t2 (fun y => tm_fvar y)) Henv).
  rewrite Hplug1 in HTR. rewrite Hplug2 in HTR.
  intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
  apply (VR_erase l T_result v1 v2 Hgnd).
  - apply (transparent_all_visible T_result (security_of T_result) l Htr).
    unfold l. apply flows_to_refl.
  - apply (HTR v1 v2 Hm1 Hv1 Hm2 Hv2).
Qed.

