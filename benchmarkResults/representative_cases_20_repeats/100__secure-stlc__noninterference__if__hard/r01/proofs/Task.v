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
(* Auxiliary lemmas about labels and security levels            *)
(* ============================================================ *)

Lemma flows_to_refl : forall l : label, flows_to l l.
Proof. destruct l; simpl; auto. Qed.

Lemma flows_to_trans : forall l1 l2 l3 : label,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof. intros l1 l2 l3 H1 H2. destruct l1, l2, l3; simpl in *; intuition. Qed.

Lemma flows_to_join_l : forall a b : label, flows_to a (join a b).
Proof. destruct a, b; simpl; auto. Qed.

Lemma flows_to_join_r : forall a b : label, flows_to b (join a b).
Proof. destruct a, b; simpl; auto. Qed.

Lemma join_lub : forall a b c : label,
  flows_to a c -> flows_to b c -> flows_to (join a b) c.
Proof. destruct a, b, c; simpl in *; intuition. Qed.

Lemma join_mono : forall a1 a2 b1 b2 : label,
  flows_to a1 a2 -> flows_to b1 b2 -> flows_to (join a1 b1) (join a2 b2).
Proof. destruct a1, a2, b1, b2; simpl in *; intuition. Qed.

Lemma join_idem : forall a : label, join a a = a.
Proof. destruct a; reflexivity. Qed.

Lemma join_comm : forall a b : label, join a b = join b a.
Proof. destruct a, b; reflexivity. Qed.

Lemma join_assoc : forall a b c : label, join (join a b) c = join a (join b c).
Proof. destruct a, b, c; reflexivity. Qed.

Lemma security_le_refl : forall k : security, security_le k k.
Proof. intros [r i]; simpl; split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3 : security,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3] [Hr1 Hi1] [Hr2 Hi2]; simpl in *.
  split; eapply flows_to_trans; eassumption.
Qed.

Lemma protect_security_le : forall k1 k2 : security, forall l1 l2 : label,
  security_le k1 k2 -> flows_to l1 l2 ->
  security_le (protect_security k1 l1) (protect_security k2 l2).
Proof.
  intros [r1 i1] [r2 i2] l1 l2 [Hr Hi] Hl; simpl in *.
  split; apply join_mono; assumption.
Qed.

Lemma protect_security_protect : forall k : security, forall l1 l2 : label,
  protect_security (protect_security k l1) l2 = protect_security k (join l1 l2).
Proof.
  intros [r i] l1 l2. unfold protect_security. simpl.
  f_equal; apply join_assoc.
Qed.

Lemma protect_security_idem : forall k : security, forall l : label,
  protect_security (protect_security k l) l = protect_security k l.
Proof.
  intros k l. rewrite protect_security_protect. rewrite join_idem. reflexivity.
Qed.

(* ============================================================ *)
(* Basic lemmas about values, steps, protection and multi-step  *)
(* ============================================================ *)

Lemma value_protect_value : forall v : tm, value v ->
  forall l : label, value (protect_value v l).
Proof.
  intros v Hv. induction Hv; intros l; simpl; try constructor; auto.
Qed.

Lemma protect_value_protect : forall v : tm, forall l1 l2 : label,
  protect_value (protect_value v l1) l2 = protect_value v (join l1 l2).
Proof.
  intros v l1 l2. destruct v; simpl; try reflexivity;
    try (rewrite protect_security_protect; reflexivity).
Qed.

Lemma value_no_step : forall v : tm, value v -> forall u : tm, ~ (v --> u).
Proof.
  intros v Hv. induction Hv; intros u Hstep; inversion Hstep; subst; firstorder.
Qed.

Lemma step_abs_false : forall T body kappa u,
  ~ (tm_abs T body kappa --> u).
Proof. intros. intro H. inversion H. Qed.

Lemma multi_value_eq : forall t u : tm, t -->* u -> value t -> u = t.
Proof.
  intros t u Hm. induction Hm; intros Hv.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma multi_trans : forall a b c : tm, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H1. induction H1; intros H2.
  - exact H2.
  - eapply multi_step; [ eassumption | apply IHmulti; exact H2 ].
Qed.

Lemma multi_step_or_refl : forall t u : tm, t -->* u ->
  t = u \/ (exists w, (t --> w) /\ (w -->* u)).
Proof.
  intros t u H. induction H.
  - left; reflexivity.
  - right; exists t2; split; assumption.
Qed.

Lemma multi_abs_eq : forall T body kappa u,
  tm_abs T body kappa -->* u -> u = tm_abs T body kappa.
Proof.
  intros T body kappa u H.
  destruct (multi_step_or_refl _ _ H) as [Heq | [w [Hs _]]].
  - symmetry; exact Heq.
  - exfalso. eapply step_abs_false; eauto.
Qed.

Lemma protect_multi : forall l : label, forall t v : tm,
  t -->* v -> value v -> tm_protect l t -->* protect_value v l.
Proof.
  intros l t v Hm. induction Hm; intros Hv.
  - eapply multi_step.
    + apply ST_ProtectValue. exact Hv.
    + apply multi_refl.
  - eapply multi_step.
    + apply ST_Protect. eassumption.
    + apply IHHm. exact Hv.
Qed.



Lemma eval_protect_decomp : forall (l : label) (t u : tm),
  multi (tm_protect l t) u -> value u ->
  exists v, multi t v /\ value v /\ u = protect_value v l.
Proof.
  intros l t u Hm Hv.
  remember (tm_protect l t) as s eqn:Es. revert t Es Hv.
  induction Hm; intros t0 Es Hv.
  - subst. inversion Hv.
  - subst. inversion H; subst.
    + assert (Hpv : value (protect_value t0 l)) by (apply value_protect_value; assumption).
      assert (Heq : t3 = protect_value t0 l) by (eapply multi_value_eq; eauto).
      exists t0. split; [ apply multi_refl | split; assumption ].
    + edestruct IHHm as (v & Hm' & Hval & Heq).
      * reflexivity.
      * exact Hv.
      * exists v. split; [ | split; assumption ].
        eapply multi_step; [ eassumption | exact Hm' ].
Qed.

Lemma eval_pair_decomp : forall (a b : tm) (k : security) (u : tm),
  multi (tm_pair a b k) u -> value u ->
  exists va vb, multi a va /\ value va /\ multi b vb /\ value vb /\
                u = tm_pair va vb k.
Proof.
  intros a b k u Hm Hv.
  remember (tm_pair a b k) as s eqn:Es. revert a b Es Hv.
  induction Hm; intros a0 b0 Es Hv.
  - subst. inversion Hv; subst.
    exists a0, b0. repeat split; try assumption; apply multi_refl.
  - subst. inversion H; subst.
    + edestruct IHHm as (va & vb & Hma & Hva & Hmb & Hvb & Heq).
      * reflexivity.
      * exact Hv.
      * exists va, vb. repeat split; try assumption.
        eapply multi_step; [ eassumption | exact Hma ].
    + edestruct IHHm as (va & vb & Hma & Hva & Hmb & Hvb & Heq).
      * reflexivity.
      * exact Hv.
      * exists va, vb. repeat split; try assumption.
        eapply multi_step; [ eassumption | exact Hmb ].
Qed.

Lemma eval_inl_decomp : forall (a : tm) (k : security) (u : tm),
  multi (tm_inl a k) u -> value u ->
  exists va, multi a va /\ value va /\ u = tm_inl va k.
Proof.
  intros a k u Hm Hv.
  remember (tm_inl a k) as s eqn:Es. revert a Es Hv.
  induction Hm; intros a0 Es Hv.
  - subst. inversion Hv; subst. exists a0. repeat split; try assumption; apply multi_refl.
  - subst. inversion H; subst.
    edestruct IHHm as (va & Hma & Hva & Heq).
    * reflexivity.
    * exact Hv.
    * exists va. repeat split; try assumption.
      eapply multi_step; [ eassumption | exact Hma ].
Qed.

Lemma eval_inr_decomp : forall (a : tm) (k : security) (u : tm),
  multi (tm_inr a k) u -> value u ->
  exists va, multi a va /\ value va /\ u = tm_inr va k.
Proof.
  intros a k u Hm Hv.
  remember (tm_inr a k) as s eqn:Es. revert a Es Hv.
  induction Hm; intros a0 Es Hv.
  - subst. inversion Hv; subst. exists a0. repeat split; try assumption; apply multi_refl.
  - subst. inversion H; subst.
    edestruct IHHm as (va & Hma & Hva & Heq).
    * reflexivity.
    * exact Hv.
    * exists va. repeat split; try assumption.
      eapply multi_step; [ eassumption | exact Hma ].
Qed.

Lemma eval_fst_decomp : forall (a : tm) (r : label) (u : tm),
  multi (tm_fst a r) u -> value u ->
  exists va vb k, multi a (tm_pair va vb k) /\ value va /\ value vb /\
                  flows_to k.(reader) r /\ u = protect_value va k.(indirect_reader).
Proof.
  intros a r u Hm Hv.
  remember (tm_fst a r) as s eqn:Es. revert a Es Hv.
  induction Hm; intros a0 Es Hv.
  - subst. inversion Hv.
  - subst. inversion H; subst.
    + destruct (eval_protect_decomp _ _ _ Hm Hv) as [v [Hmv [Hvv Heq]]].
      assert (Heqva : v = v1) by (eapply multi_value_eq; eauto).
      subst v.
      exists v1, v2, kappa. repeat split; try assumption; try apply multi_refl.
    + edestruct IHHm as (va & vb & k & Hma & Hva & Hvb & Hflow & Heq).
      * reflexivity.
      * exact Hv.
      * exists va, vb, k. repeat split; try assumption.
        eapply multi_step; [ eassumption | exact Hma ].
Qed.

Lemma eval_snd_decomp : forall (a : tm) (r : label) (u : tm),
  multi (tm_snd a r) u -> value u ->
  exists va vb k, multi a (tm_pair va vb k) /\ value va /\ value vb /\
                  flows_to k.(reader) r /\ u = protect_value vb k.(indirect_reader).
Proof.
  intros a r u Hm Hv.
  remember (tm_snd a r) as s eqn:Es. revert a Es Hv.
  induction Hm; intros a0 Es Hv.
  - subst. inversion Hv.
  - subst. inversion H; subst.
    + destruct (eval_protect_decomp _ _ _ Hm Hv) as [v [Hmv [Hvv Heq]]].
      assert (Heqvb : v = v2) by (eapply multi_value_eq; eauto).
      subst v.
      exists v1, v2, kappa. repeat split; try assumption; try apply multi_refl.
    + edestruct IHHm as (va & vb & k & Hma & Hva & Hvb & Hflow & Heq).
      * reflexivity.
      * exact Hv.
      * exists va, vb, k. repeat split; try assumption.
        eapply multi_step; [ eassumption | exact Hma ].
Qed.

Lemma eval_case_decomp : forall (a b1 b2 : tm) (r : label) (u : tm),
  multi (tm_case a b1 b2 r) u -> value u ->
  (exists v k w, multi a (tm_inl v k) /\ value v /\ flows_to k.(reader) r /\
                 multi (open b1 v) w /\ value w /\
                 u = protect_value w k.(indirect_reader))
  \/
  (exists v k w, multi a (tm_inr v k) /\ value v /\ flows_to k.(reader) r /\
                 multi (open b2 v) w /\ value w /\
                 u = protect_value w k.(indirect_reader)).
Proof.
  intros a b1 b2 r u Hm Hv.
  remember (tm_case a b1 b2 r) as s eqn:Es. revert a b1 b2 Es Hv.
  induction Hm; intros a0 c1 c2 Es Hv.
  - subst. inversion Hv.
  - subst. inversion H; subst.
    + destruct (eval_protect_decomp _ _ _ Hm Hv) as [w [Hmw [Hw Heq]]].
      left. exists v, kappa, w. repeat split; try assumption; try apply multi_refl.
    + destruct (eval_protect_decomp _ _ _ Hm Hv) as [w [Hmw [Hw Heq]]].
      right. exists v, kappa, w. repeat split; try assumption; try apply multi_refl.
    + edestruct IHHm as [[v [k [w [Hma [Hvv [Hflow [Hmw [Hw Heq]]]]]]]]
                        |[v [k [w [Hma [Hvv [Hflow [Hmw [Hw Heq]]]]]]]]].
      * reflexivity.
      * exact Hv.
      * left. exists v, k, w. repeat split; try assumption.
        eapply multi_step; [ eassumption | exact Hma ].
      * right. exists v, k, w. repeat split; try assumption.
        eapply multi_step; [ eassumption | exact Hma ].
Qed.

Lemma eval_if_decomp : forall (c y n : tm) (r : label) (u : tm),
  multi (tm_if c y n r) u -> value u ->
  (exists v k w, multi c (tm_inl v k) /\ value v /\ flows_to k.(reader) r /\
                 multi y w /\ value w /\ u = protect_value w k.(indirect_reader))
  \/
  (exists v k w, multi c (tm_inr v k) /\ value v /\ flows_to k.(reader) r /\
                 multi n w /\ value w /\ u = protect_value w k.(indirect_reader)).
Proof.
  intros c y n r u Hm Hv.
  remember (tm_if c y n r) as s eqn:Es. revert c y n Es Hv.
  induction Hm; intros c0 y0 n0 Es Hv.
  - subst. inversion Hv.
  - subst. inversion H; subst.
    + edestruct IHHm as [[v [k [w [Hma [Hvv [Hflow [Hmw [Hw Heq]]]]]]]]
                        |[v [k [w [Hma [Hvv [Hflow [Hmw [Hw Heq]]]]]]]]].
      * reflexivity.
      * exact Hv.
      * left. exists v, k, w. repeat split; try assumption.
        eapply multi_step; [ eassumption | exact Hma ].
      * right. exists v, k, w. repeat split; try assumption.
        eapply multi_step; [ eassumption | exact Hma ].
    + destruct (eval_protect_decomp _ _ _ Hm Hv) as [w [Hmw [Hw Heq]]].
      left. exists v, k, w. repeat split; try assumption; try apply multi_refl.
    + destruct (eval_protect_decomp _ _ _ Hm Hv) as [w [Hmw [Hw Heq]]].
      right. exists v, k, w. repeat split; try assumption; try apply multi_refl.
Qed.

Lemma eval_app_decomp : forall (a b : tm) (r : label) (u : tm),
  multi (tm_app a b r) u -> value u ->
  exists va vb, multi a va /\ value va /\ multi b vb /\ value vb /\
                multi (tm_app va vb r) u.
Proof.
  intros a b r u Hm Hv.
  remember (tm_app a b r) as s eqn:Es. revert a b Es Hv.
  induction Hm; intros a0 b0 Es Hv.
  - subst. inversion Hv.
  - subst. inversion H; subst.
    + exists (tm_abs T body kappa), b0. repeat split; try assumption; try apply multi_refl.
      eapply multi_step; [ eassumption | exact Hm ].
    + edestruct IHHm as (va & vb & Hma & Hva & Hmb & Hvb & Hcont).
      * reflexivity.
      * exact Hv.
      * exists va, vb. repeat split; try assumption.
        eapply multi_step; [ eassumption | exact Hma ].
    + edestruct IHHm as (va & vb & Hma & Hva & Hmb & Hvb & Hcont).
      * reflexivity.
      * exact Hv.
      * exists va, vb. repeat split; try assumption.
        eapply multi_step; [ eassumption | exact Hmb ].
Qed.

Lemma eval_app_abs_decomp : forall (T : ty) (body w : tm) (k : security)
  (r : label) (u : tm),
  value (tm_abs T body k) -> value w -> flows_to k.(reader) r ->
  multi (tm_app (tm_abs T body k) w r) u -> value u ->
  (exists v, multi (open body w) v /\ value v /\
             u = protect_value v k.(indirect_reader)).
Proof.
  intros T body w k r u Hva Hw Hflow Hm Hv.
  remember (tm_app (tm_abs T body k) w r) as s eqn:Es.
  revert body w Hva Hw Hflow Es Hv.
  induction Hm; intros body0 w0 Hva0 Hw0 Hflow0 Es Hv.
  - subst. inversion Hv.
  - subst. inversion H; subst.
    + destruct (eval_protect_decomp _ _ _ Hm Hv) as [v [Hmv [Hvv Heq]]].
      exists v. repeat split; assumption.
    + exfalso. eapply value_no_step; [ exact Hva0 | eassumption ].
    + exfalso. eapply value_no_step; [ exact Hw0 | eassumption ].
Qed.

Lemma eval_app_abs_complete : forall (T : ty) (body w v : tm) (k : security)
  (r : label),
  value (tm_abs T body k) -> value w -> flows_to k.(reader) r ->
  multi (open body w) v -> value v ->
  multi (tm_app (tm_abs T body k) w r) (protect_value v k.(indirect_reader)).
Proof.
  intros. eapply multi_step.
  - eapply ST_AppAbs; eassumption.
  - eapply protect_multi; eassumption.
Qed.

(* ============================================================ *)
(* The logical relation                                          *)
(* ============================================================ *)

Definition obs_sec (kappa : security) (l : label) : Prop :=
  flows_to kappa.(indirect_reader) l.

Fixpoint W (l : label) (T : ty) (kappa : security) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_Unit _ =>
      value v1 /\ value v2 /\
      (obs_sec kappa l ->
         exists k1 k2, v1 = tm_unit k1 /\ v2 = tm_unit k2 /\
           security_le k1 kappa /\ security_le k2 kappa)
  | Ty_Sum T1 T2 _ =>
      value v1 /\ value v2 /\
      (obs_sec kappa l ->
         (exists w1 w2 k1 k2,
            v1 = tm_inl w1 k1 /\ v2 = tm_inl w2 k2 /\
            security_le k1 kappa /\ security_le k2 kappa /\
            W l T1 (security_of T1) w1 w2)
         \/
         (exists w1 w2 k1 k2,
            v1 = tm_inr w1 k1 /\ v2 = tm_inr w2 k2 /\
            security_le k1 kappa /\ security_le k2 kappa /\
            W l T2 (security_of T2) w1 w2))
  | Ty_Prod T1 T2 _ =>
      value v1 /\ value v2 /\
      (obs_sec kappa l ->
         exists a1 b1 a2 b2 k1 k2,
            v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
            security_le k1 kappa /\ security_le k2 kappa /\
            W l T1 (security_of T1) a1 a2 /\
            W l T2 (security_of T2) b1 b2)
  | Ty_Arrow T1 T2 _ =>
      value v1 /\ value v2 /\
      (obs_sec kappa l ->
         (exists T1a b1 k1, v1 = tm_abs T1a b1 k1 /\ security_le k1 kappa /\
          exists T1b b2 k2, v2 = tm_abs T1b b2 k2 /\ security_le k2 kappa /\
          forall w1 w2 r,
            W l T1 (security_of T1) w1 w2 ->
            flows_to kappa.(reader) r ->
            forall u1 u2,
              multi (tm_app v1 w1 r) u1 -> value u1 ->
              multi (tm_app v2 w2 r) u2 -> value u2 ->
              W l T2 (protect_security (security_of T2) kappa.(indirect_reader))
                     u1 u2))
  end.

Lemma W_ty_protect : forall (l : label) (T : ty) (l' : label) (kappa : security)
  (v1 v2 : tm),
  W l (ty_protect l' T) kappa v1 v2 <-> W l T kappa v1 v2.
Proof. intros. destruct T; simpl; reflexivity. Qed.

Lemma security_of_ty_protect : forall (T : ty) (l : label),
  security_of (ty_protect l T) = protect_security (security_of T) l.
Proof. destruct T; reflexivity. Qed.

Lemma W_value_1 : forall (l : label) (T : ty) (kappa : security) (v1 v2 : tm),
  W l T kappa v1 v2 -> value v1.
Proof. intros. destruct T; simpl in H; tauto. Qed.

Lemma W_value_2 : forall (l : label) (T : ty) (kappa : security) (v1 v2 : tm),
  W l T kappa v1 v2 -> value v2.
Proof. intros. destruct T; simpl in H; tauto. Qed.

Lemma obs_sec_mono : forall (kappa1 kappa2 : security) (l : label),
  security_le kappa1 kappa2 -> obs_sec kappa2 l -> obs_sec kappa1 l.
Proof.
  intros [r1 i1] [r2 i2] l [Hr Hi] Hobs. simpl in *.
  eapply flows_to_trans; eassumption.
Qed.

Lemma security_le_protect : forall (kappa : security) (l : label),
  security_le kappa (protect_security kappa l).
Proof.
  intros [r i] l. simpl. split; apply flows_to_join_l.
Qed.

Ltac sec_trans k := apply security_le_trans with (k2 := k); assumption.

Lemma W_mono : forall (l : label) (T : ty) (kappa1 kappa2 : security),
  security_le kappa1 kappa2 ->
  forall v1 v2, W l T kappa1 v1 v2 -> W l T kappa2 v1 v2.
Proof.
  intros l T. induction T; intros kappa1 kappa2 Hle v1 v2 Hw; simpl in *.
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    split; [ exact Hv1 | split; [ exact Hv2 | intros Hobs ]].
    destruct (Hcl (obs_sec_mono _ _ _ Hle Hobs)) as (k1 & k2 & E1 & E2 & S1 & S2).
    exists k1, k2.
    split; [ exact E1 | split; [ exact E2 | split; [ sec_trans kappa1 | sec_trans kappa1 ] ] ].
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    split; [ exact Hv1 | split; [ exact Hv2 | intros Hobs ]].
    destruct (Hcl (obs_sec_mono _ _ _ Hle Hobs)) as
      [[w1 [w2 [k1 [k2 [E1 [E2 [S1 [S2 Hr]]]]]]]]
      |[w1 [w2 [k1 [k2 [E1 [E2 [S1 [S2 Hr]]]]]]]]].
    + left. exists w1, w2, k1, k2.
      split; [ exact E1 | split; [ exact E2 | split; [ sec_trans kappa1 |
        split; [ sec_trans kappa1 | exact Hr ] ] ] ].
    + right. exists w1, w2, k1, k2.
      split; [ exact E1 | split; [ exact E2 | split; [ sec_trans kappa1 |
        split; [ sec_trans kappa1 | exact Hr ] ] ] ].
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    split; [ exact Hv1 | split; [ exact Hv2 | intros Hobs ]].
    destruct (Hcl (obs_sec_mono _ _ _ Hle Hobs)) as
      (a1 & b1 & a2 & b2 & k1 & k2 & E1 & E2 & S1 & S2 & Ha & Hb).
    exists a1, b1, a2, b2, k1, k2.
    split; [ exact E1 | split; [ exact E2 | split; [ sec_trans kappa1 |
      split; [ sec_trans kappa1 | split; [ exact Ha | exact Hb ] ] ] ] ].
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    split; [ exact Hv1 | split; [ exact Hv2 | intros Hobs ]].
    destruct (Hcl (obs_sec_mono _ _ _ Hle Hobs)) as
      (T1a & b1 & k1 & E1 & S1 & T1b & b2 & k2 & E2 & S2 & Hclause).
    exists T1a, b1, k1.
    split; [ exact E1 | split; [ sec_trans kappa1 | exists T1b, b2, k2 ] ].
    split; [ exact E2 | split; [ sec_trans kappa1 | ] ].
    intros w1 w2 r Hw12 Hr u1 u2 Hm1 Hvv1 Hm2 Hvv2.
    eapply IHT2 with
      (kappa1 := protect_security (security_of T2) kappa1.(indirect_reader))
      (kappa2 := protect_security (security_of T2) kappa2.(indirect_reader)).
    + apply protect_security_le; [ apply security_le_refl | exact (proj2 Hle) ].
    + apply (Hclause w1 w2 r).
      * exact Hw12.
      * eapply flows_to_trans; [ exact (proj1 Hle) | exact Hr ].
      * exact Hm1.
      * exact Hvv1.
      * exact Hm2.
      * exact Hvv2.
Qed.

Lemma W_protect2 : forall (l : label) (T : ty) (kappa : security) (v1 v2 : tm),
  W l T kappa v1 v2 ->
  forall l1 l2 : label,
  W l T (protect_security kappa (join l1 l2))
        (protect_value v1 l1) (protect_value v2 l2).
Proof.
  intros l T. induction T; intros kappa v1 v2 Hw l1 l2; simpl in *.
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    split; [ apply value_protect_value; exact Hv1 |
      split; [ apply value_protect_value; exact Hv2 | intros Hobs ]].
    assert (Hobs1 : obs_sec kappa l)
      by (eapply obs_sec_mono; [ apply security_le_protect | exact Hobs ]).
    destruct (Hcl Hobs1) as (k1 & k2 & E1 & E2 & S1 & S2).
    exists (protect_security k1 l1), (protect_security k2 l2).
    rewrite E1, E2; simpl.
    split; [ reflexivity | split; [ reflexivity | split ] ].
    + apply protect_security_le; [ exact S1 | apply flows_to_join_l ].
    + apply protect_security_le; [ exact S2 | apply flows_to_join_r ].
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    split; [ apply value_protect_value; exact Hv1 |
      split; [ apply value_protect_value; exact Hv2 | intros Hobs ]].
    assert (Hobs1 : obs_sec kappa l)
      by (eapply obs_sec_mono; [ apply security_le_protect | exact Hobs ]).
    destruct (Hcl Hobs1) as
      [[w1 [w2 [k1 [k2 [E1 [E2 [S1 [S2 Hr]]]]]]]]
      |[w1 [w2 [k1 [k2 [E1 [E2 [S1 [S2 Hr]]]]]]]]].
    + left. exists w1, w2, (protect_security k1 l1), (protect_security k2 l2).
      rewrite E1, E2; simpl.
      split; [ reflexivity | split; [ reflexivity | split;
        [ apply protect_security_le; [ exact S1 | apply flows_to_join_l ] |
          split; [ apply protect_security_le; [ exact S2 | apply flows_to_join_r ] |
            exact Hr ] ] ] ].
    + right. exists w1, w2, (protect_security k1 l1), (protect_security k2 l2).
      rewrite E1, E2; simpl.
      split; [ reflexivity | split; [ reflexivity | split;
        [ apply protect_security_le; [ exact S1 | apply flows_to_join_l ] |
          split; [ apply protect_security_le; [ exact S2 | apply flows_to_join_r ] |
            exact Hr ] ] ] ].
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    split; [ apply value_protect_value; exact Hv1 |
      split; [ apply value_protect_value; exact Hv2 | intros Hobs ]].
    assert (Hobs1 : obs_sec kappa l)
      by (eapply obs_sec_mono; [ apply security_le_protect | exact Hobs ]).
    destruct (Hcl Hobs1) as
      (a1 & b1 & a2 & b2 & k1 & k2 & E1 & E2 & S1 & S2 & Ha & Hb).
    exists a1, b1, a2, b2, (protect_security k1 l1), (protect_security k2 l2).
    rewrite E1, E2; simpl.
    split; [ reflexivity | split; [ reflexivity | split;
      [ apply protect_security_le; [ exact S1 | apply flows_to_join_l ] |
        split; [ apply protect_security_le; [ exact S2 | apply flows_to_join_r ] |
          split; [ exact Ha | exact Hb ] ] ] ] ].
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    split; [ apply value_protect_value; exact Hv1 |
      split; [ apply value_protect_value; exact Hv2 | intros Hobs ]].
    assert (Hobs1 : obs_sec kappa l)
      by (eapply obs_sec_mono; [ apply security_le_protect | exact Hobs ]).
    destruct (Hcl Hobs1) as
      (T1a & b1 & k1 & E1 & S1 & T1b & b2 & k2 & E2 & S2 & Hclause).
    exists T1a, b1, (protect_security k1 l1).
    split.
    + rewrite E1; simpl; reflexivity.
    + split.
      * apply protect_security_le; [ exact S1 | apply flows_to_join_l ].
      * exists T1b, b2, (protect_security k2 l2).
        split.
        -- rewrite E2; simpl; reflexivity.
        -- split.
           ++ apply protect_security_le; [ exact S2 | apply flows_to_join_r ].
           ++ intros w1 w2 r Hw12 Hr u1 u2 Hm1 Hvv1 Hm2 Hvv2.
              assert (Hval1 : value (tm_abs T1a b1 (protect_security k1 l1))).
              { assert (Hvv : value (protect_value v1 l1)) by (apply value_protect_value; exact Hv1).
                rewrite E1 in Hvv. simpl in Hvv. exact Hvv. }
              assert (Hval2 : value (tm_abs T1b b2 (protect_security k2 l2))).
              { assert (Hvv : value (protect_value v2 l2)) by (apply value_protect_value; exact Hv2).
                rewrite E2 in Hvv. simpl in Hvv. exact Hvv. }
              assert (Hflow1 : flows_to (protect_security k1 l1).(reader) r).
              { eapply flows_to_trans.
                - apply (proj1 (protect_security_le k1 kappa l1 (join l1 l2) S1 (flows_to_join_l l1 l2))).
                - exact Hr. }
              assert (Hflow2 : flows_to (protect_security k2 l2).(reader) r).
              { eapply flows_to_trans.
                - apply (proj1 (protect_security_le k2 kappa l2 (join l1 l2) S2 (flows_to_join_r l1 l2))).
                - exact Hr. }
              rewrite E1 in Hm1; simpl in Hm1.
              rewrite E2 in Hm2; simpl in Hm2.
              destruct (eval_app_abs_decomp _ _ _ _ _ _ Hval1
                          (W_value_1 _ _ _ _ _ Hw12) Hflow1 Hm1 Hvv1)
                as (v1' & Hmv1 & Hvv1' & Heq1).
              destruct (eval_app_abs_decomp _ _ _ _ _ _ Hval2
                          (W_value_2 _ _ _ _ _ Hw12) Hflow2 Hm2 Hvv2)
                as (v2' & Hmv2 & Hvv2' & Heq2).
              assert (Hmineval1 : multi (tm_app v1 w1 r) (protect_value v1' k1.(indirect_reader))).
              { rewrite E1.
                eapply eval_app_abs_complete.
                - rewrite <- E1; exact Hv1.
                - exact (W_value_1 _ _ _ _ _ Hw12).
                - eapply flows_to_trans.
                  + exact (proj1 S1).
                  + eapply flows_to_trans.
                    * apply flows_to_join_l.
                    * exact Hr.
                - exact Hmv1.
                - exact Hvv1'. }
              assert (Hmineval2 : multi (tm_app v2 w2 r) (protect_value v2' k2.(indirect_reader))).
              { rewrite E2.
                eapply eval_app_abs_complete.
                - rewrite <- E2; exact Hv2.
                - exact (W_value_2 _ _ _ _ _ Hw12).
                - eapply flows_to_trans.
                  + exact (proj1 S2).
                  + eapply flows_to_trans.
                    * apply flows_to_join_l.
                    * exact Hr.
                - exact Hmv2.
                - exact Hvv2'. }
              assert (Hres : W l T2 (protect_security (security_of T2) kappa.(indirect_reader))
                                  (protect_value v1' k1.(indirect_reader))
                                  (protect_value v2' k2.(indirect_reader))).
              { apply (Hclause w1 w2 r).
                - exact Hw12.
                - eapply flows_to_trans.
                  + apply flows_to_join_l.
                  + exact Hr.
                - exact Hmineval1.
                - apply value_protect_value; exact Hvv1'.
                - exact Hmineval2.
                - apply value_protect_value; exact Hvv2'. }
              rewrite Heq1, Heq2. simpl.
              rewrite <- (protect_value_protect v1' k1.(indirect_reader) l1).
              rewrite <- (protect_value_protect v2' k2.(indirect_reader) l2).
              rewrite <- (protect_security_protect (security_of T2) kappa.(indirect_reader) (join l1 l2)).
              apply IHT2 with
                (kappa := protect_security (security_of T2) kappa.(indirect_reader))
                (v1 := protect_value v1' k1.(indirect_reader))
                (v2 := protect_value v2' k2.(indirect_reader)).
              exact Hres.
Qed.

Lemma subtype_security_le : forall (T U : ty), subtype T U ->
  security_le (security_of T) (security_of U).
Proof.
  intros T U Hsub. induction Hsub; simpl; eauto using security_le_trans, security_le_refl.
Qed.

Lemma W_subtype : forall (T U : ty), subtype T U ->
  forall (l : label) (kT kU : security) (v1 v2 : tm),
  security_le kT kU -> W l T kT v1 v2 -> W l U kU v1 v2.
Proof.
  intros T U Hsub. induction Hsub; intros l kT kU v1 v2 Hle Hw; simpl in *.
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    split; [ exact Hv1 | split; [ exact Hv2 | intros Hobs ]].
    destruct (Hcl (obs_sec_mono _ _ _ Hle Hobs)) as (k1 & k2 & E1 & E2 & S1 & S2).
    exists k1, k2.
    split; [ exact E1 | split; [ exact E2 | split; [ sec_trans kT | sec_trans kT ] ] ].
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    split; [ exact Hv1 | split; [ exact Hv2 | intros Hobs ]].
    destruct (Hcl (obs_sec_mono _ _ _ Hle Hobs)) as
      [[w1 [w2 [k1 [k2 [E1 [E2 [S1 [S2 Hr]]]]]]]]
      |[w1 [w2 [k1 [k2 [E1 [E2 [S1 [S2 Hr]]]]]]]]].
    + left. exists w1, w2, k1, k2.
      split; [ exact E1 | split; [ exact E2 | split; [ sec_trans kT |
        split; [ sec_trans kT | ] ] ] ].
      eapply IHHsub1; [ apply subtype_security_le; eassumption | exact Hr ].
    + right. exists w1, w2, k1, k2.
      split; [ exact E1 | split; [ exact E2 | split; [ sec_trans kT |
        split; [ sec_trans kT | ] ] ] ].
      eapply IHHsub2; [ apply subtype_security_le; eassumption | exact Hr ].
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    split; [ exact Hv1 | split; [ exact Hv2 | intros Hobs ]].
    destruct (Hcl (obs_sec_mono _ _ _ Hle Hobs)) as
      (a1 & b1 & a2 & b2 & k1 & k2 & E1 & E2 & S1 & S2 & Ha & Hb).
    exists a1, b1, a2, b2, k1, k2.
    split; [ exact E1 | split; [ exact E2 | split; [ sec_trans kT |
      split; [ sec_trans kT | split; [ | ] ] ] ] ].
    + eapply IHHsub1; [ apply subtype_security_le; eassumption | exact Ha ].
    + eapply IHHsub2; [ apply subtype_security_le; eassumption | exact Hb ].
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    split; [ exact Hv1 | split; [ exact Hv2 | intros Hobs ]].
    destruct (Hcl (obs_sec_mono _ _ _ Hle Hobs)) as
      (T1a & b1 & k1 & E1 & S1 & T1b & b2 & k2 & E2 & S2 & Hclause).
    exists T1a, b1, k1.
    split; [ exact E1 | split; [ sec_trans kT | exists T1b, b2, k2 ] ].
    split; [ exact E2 | split; [ sec_trans kT | ] ].
    intros w1 w2 r Hw12 Hr u1 u2 Hm1 Hvv1 Hm2 Hvv2.
    assert (Hw12' : W l T1 (security_of T1) w1 w2).
    { eapply IHHsub1; [ apply subtype_security_le; eassumption | exact Hw12 ]. }
    assert (Hres : W l T2 (protect_security (security_of T2) kT.(indirect_reader)) u1 u2).
    { apply (Hclause w1 w2 r).
      - exact Hw12'.
      - eapply flows_to_trans; [ exact (proj1 Hle) | exact Hr ].
      - exact Hm1.
      - exact Hvv1.
      - exact Hm2.
      - exact Hvv2. }
    eapply IHHsub2.
    + apply protect_security_le; [ apply subtype_security_le; eassumption | exact (proj2 Hle) ].
    + exact Hres.
  - eapply IHHsub2; [ | eapply IHHsub1; [ apply security_le_refl | exact Hw ] ].
    exact Hle.
Qed.

Definition LRterm (l : label) (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, multi t1 v1 -> value v1 -> multi t2 v2 -> value v2 ->
    W l T (security_of T) v1 v2.

Lemma LRterm_of_W : forall (l : label) (T : ty) (v1 v2 : tm),
  W l T (security_of T) v1 v2 -> LRterm l T v1 v2.
Proof.
  intros l T v1 v2 Hw. unfold LRterm.
  intros v1' v2' Hm1 Hval1 Hm2 Hval2.
  assert (Hv1 : value v1) by (eapply W_value_1; eassumption).
  assert (Hv2 : value v2) by (eapply W_value_2; eassumption).
  rewrite (multi_value_eq _ _ Hm1 Hv1).
  rewrite (multi_value_eq _ _ Hm2 Hv2).
  exact Hw.
Qed.

Lemma LRterm_any_not_obs : forall (l : label) (T : ty) (t1 t2 : tm),
  ~ obs_sec (security_of T) l -> LRterm l T t1 t2.
Proof.
  intros l T t1 t2 Hno. unfold LRterm.
  intros v1 v2 Hm1 Hval1 Hm2 Hval2.
  destruct T; simpl in *.
  - split; [ exact Hval1 | split; [ exact Hval2 | intros Hobs ]].
    exfalso. apply Hno. exact Hobs.
  - split; [ exact Hval1 | split; [ exact Hval2 | intros Hobs ]].
    exfalso. apply Hno. exact Hobs.
  - split; [ exact Hval1 | split; [ exact Hval2 | intros Hobs ]].
    exfalso. apply Hno. exact Hobs.
  - split; [ exact Hval1 | split; [ exact Hval2 | intros Hobs ]].
    exfalso. apply Hno. exact Hobs.
Qed.

(* ============================================================ *)
(* Fresh atoms and locally closed terms                          *)
(* ============================================================ *)

Fixpoint max_list (L : list nat) : nat :=
  match L with
  | [] => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Lemma In_max_list : forall (L : list nat) (x : nat), In x L -> x <= max_list L.
Proof.
  intros L x H. induction L as [| y ys IH].
  - inversion H.
  - simpl in H. destruct H as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [ apply IH; exact Hin | apply Nat.le_max_r ].
Qed.

Definition fresh_from (L : list atom) : atom := S (max_list L).

Lemma fresh_from_not_in : forall (L : list atom), ~ In (fresh_from L) L.
Proof.
  intros L H. unfold fresh_from in H.
  pose proof (In_max_list L (S (max_list L)) H). lia.
Qed.

Lemma fresh_from_app_not_in_l : forall (L1 L2 : list atom),
  ~ In (fresh_from (L1 ++ L2)) L1.
Proof.
  intros L1 L2 H. apply (fresh_from_not_in (L1 ++ L2)).
  apply in_or_app. left. exact H.
Qed.

Lemma fresh_from_app_not_in_r : forall (L1 L2 : list atom),
  ~ In (fresh_from (L1 ++ L2)) L2.
Proof.
  intros L1 L2 H. apply (fresh_from_not_in (L1 ++ L2)).
  apply in_or_app. right. exact H.
Qed.

(* ============================================================ *)
(* Locally closed terms                                          *)
(* ============================================================ *)

Lemma lc_at_open_rec_id : forall (t : tm) (k : nat), lc_at k t ->
  forall u : tm, open_rec k u t = t.
Proof.
  intros t. induction t as
    [ n | a | s | T body IHbody s0 | t1 IH1 t2 IH2 l | t1 IH1 t2 IH2 s
    | t IH l | t IH l | t IH s | t IH s | t1 IH1 t2 IH2 t3 IH3 l
    | l t IH | t1 IH1 t2 IH2 t3 IH3 l ];
    intros k Hlc u; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n) eqn:E; [ | reflexivity ].
    apply Nat.eqb_eq in E. subst n. lia.
  - f_equal. apply IHbody. exact Hlc.
  - f_equal.
    + apply IH1. tauto.
    + apply IH2. tauto.
  - f_equal.
    + apply IH1. tauto.
    + apply IH2. tauto.
  - f_equal. apply IH. exact Hlc.
  - f_equal. apply IH. exact Hlc.
  - f_equal. apply IH. exact Hlc.
  - f_equal. apply IH. exact Hlc.
  - f_equal.
    + apply IH1. tauto.
    + apply IH2. tauto.
    + apply IH3. tauto.
  - f_equal. apply IH. exact Hlc.
  - f_equal.
    + apply IH1. tauto.
    + apply IH2. tauto.
    + apply IH3. tauto.
Qed.

Lemma lc_open_fvar_inv : forall (body : tm) (k : nat) (x : atom),
  lc_at k (open_rec k (tm_fvar x) body) -> lc_at (S k) body.
Proof.
  intros body. induction body as
    [ n | a | s | T body IHbody s0 | t1 IH1 t2 IH2 l | t1 IH1 t2 IH2 s
    | t IH l | t IH l | t IH s | t IH s | t1 IH1 t2 IH2 t3 IH3 l
    | l t IH | t1 IH1 t2 IH2 t3 IH3 l ];
    intros k x Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl in *.
    + apply Nat.eqb_eq in E. subst n. lia.
    + lia.
  - exact I.
  - exact I.
  - apply (IHbody (S k) x). exact Hlc.
  - split; [ apply (IH1 k x); tauto | apply (IH2 k x); tauto ].
  - split; [ apply (IH1 k x); tauto | apply (IH2 k x); tauto ].
  - apply (IH k x). exact Hlc.
  - apply (IH k x). exact Hlc.
  - apply (IH k x). exact Hlc.
  - apply (IH k x). exact Hlc.
  - split; [ apply (IH1 k x); tauto | split;
      [ apply (IH2 (S k) x); tauto | apply (IH3 (S k) x); tauto ] ].
  - apply (IH k x). exact Hlc.
  - split; [ apply (IH1 k x); tauto | split;
      [ apply (IH2 k x); tauto | apply (IH3 k x); tauto ] ].
Qed.

Lemma value_lc : forall (v : tm), value v -> lc_at 0 v.
Proof.
  intros v Hv. induction Hv; simpl.
  - exact I.
  - unfold locally_closed in H. simpl in H. exact H.
  - split; assumption.
  - assumption.
  - assumption.
Qed.

(* ============================================================ *)
(* Environment substitution                                      *)
(* ============================================================ *)

Definition env := atom -> tm.

Fixpoint subst_env (gamma : env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_unit kappa => tm_unit kappa
  | tm_abs T body kappa => tm_abs T (subst_env gamma body) kappa
  | tm_app t1 t2 r => tm_app (subst_env gamma t1) (subst_env gamma t2) r
  | tm_pair t1 t2 kappa => tm_pair (subst_env gamma t1) (subst_env gamma t2) kappa
  | tm_fst t1 r => tm_fst (subst_env gamma t1) r
  | tm_snd t1 r => tm_snd (subst_env gamma t1) r
  | tm_inl t1 kappa => tm_inl (subst_env gamma t1) kappa
  | tm_inr t1 kappa => tm_inr (subst_env gamma t1) kappa
  | tm_case t0 body1 body2 r =>
      tm_case (subst_env gamma t0) (subst_env gamma body1)
              (subst_env gamma body2) r
  | tm_protect l t1 => tm_protect l (subst_env gamma t1)
  | tm_if c yes no r =>
      tm_if (subst_env gamma c) (subst_env gamma yes) (subst_env gamma no) r
  end.

Definition env_update (gamma : env) (x : atom) (u : tm) : env :=
  fun y => if Nat.eqb x y then u else gamma y.

Definition env_id : env := fun x => tm_fvar x.

Lemma lc_at_mono : forall (t : tm) (k k' : nat), k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros t. induction t as
    [ n | a | s | T body IHbody s0 | t1 IH1 t2 IH2 l | t1 IH1 t2 IH2 s
    | t IH l | t IH l | t IH s | t IH s | t1 IH1 t2 IH2 t3 IH3 l
    | l t IH | t1 IH1 t2 IH2 t3 IH3 l ];
    intros k k' Hle H; simpl in *; try exact I; try assumption.
  - lia.
  - apply (IHbody (S k) (S k')); [ lia | exact H ].
  - split; [ apply (IH1 k k'); [ lia | tauto ] | apply (IH2 k k'); [ lia | tauto ] ].
  - split; [ apply (IH1 k k'); [ lia | tauto ] | apply (IH2 k k'); [ lia | tauto ] ].
  - apply (IH k k'); [ lia | exact H ].
  - apply (IH k k'); [ lia | exact H ].
  - apply (IH k k'); [ lia | exact H ].
  - apply (IH k k'); [ lia | exact H ].
  - split; [ apply (IH1 k k'); [ lia | tauto ] | split;
      [ apply (IH2 (S k) (S k')); [ lia | tauto ] |
        apply (IH3 (S k) (S k')); [ lia | tauto ] ] ].
  - apply (IH k k'); [ lia | exact H ].
  - split; [ apply (IH1 k k'); [ lia | tauto ] | split;
      [ apply (IH2 k k'); [ lia | tauto ] | apply (IH3 k k'); [ lia | tauto ] ] ].
Qed.

Lemma subst_env_ext : forall (gamma1 gamma2 : env) (t : tm),
  (forall x, In x (fv t) -> gamma1 x = gamma2 x) ->
  subst_env gamma1 t = subst_env gamma2 t.
Proof.
  intros gamma1 gamma2 t. induction t as
    [ n | a | s | T body IHbody s0 | t1 IH1 t2 IH2 l | t1 IH1 t2 IH2 s
    | t IH l | t IH l | t IH s | t IH s | t1 IH1 t2 IH2 t3 IH3 l
    | l t IH | t1 IH1 t2 IH2 t3 IH3 l ];
    intros H; simpl.
  - reflexivity.
  - apply H. simpl. auto.
  - reflexivity.
  - f_equal. apply IHbody. intros z Hz. apply H. simpl. exact Hz.
  - f_equal.
    + apply IH1. intros z Hz. apply H. simpl. apply in_or_app. left. exact Hz.
    + apply IH2. intros z Hz. apply H. simpl. apply in_or_app. right. exact Hz.
  - f_equal.
    + apply IH1. intros z Hz. apply H. simpl. apply in_or_app. left. exact Hz.
    + apply IH2. intros z Hz. apply H. simpl. apply in_or_app. right. exact Hz.
  - f_equal. apply IH. intros z Hz. apply H. simpl. exact Hz.
  - f_equal. apply IH. intros z Hz. apply H. simpl. exact Hz.
  - f_equal. apply IH. intros z Hz. apply H. simpl. exact Hz.
  - f_equal. apply IH. intros z Hz. apply H. simpl. exact Hz.
  - f_equal.
    + apply IH1. intros z Hz. apply H. simpl. apply in_or_app. left. exact Hz.
    + apply IH2. intros z Hz. apply H. simpl. apply in_or_app. right.
      apply in_or_app. left. exact Hz.
    + apply IH3. intros z Hz. apply H. simpl. apply in_or_app. right.
      apply in_or_app. right. exact Hz.
  - f_equal. apply IH. intros z Hz. apply H. simpl. exact Hz.
  - f_equal.
    + apply IH1. intros z Hz. apply H. simpl. apply in_or_app. left. exact Hz.
    + apply IH2. intros z Hz. apply H. simpl. apply in_or_app. right.
      apply in_or_app. left. exact Hz.
    + apply IH3. intros z Hz. apply H. simpl. apply in_or_app. right.
      apply in_or_app. right. exact Hz.
Qed.

Lemma subst_env_id : forall (t : tm), subst_env env_id t = t.
Proof.
  induction t; simpl; try reflexivity; try (f_equal; auto).
Qed.

Lemma subst_env_open_rec : forall (gamma : env),
  (forall x, lc_at 0 (gamma x)) ->
  forall (t : tm) (k : nat) (u : tm),
  subst_env gamma (open_rec k u t) = open_rec k (subst_env gamma u) (subst_env gamma t).
Proof.
  intros gamma Hlcenv t. induction t as
    [ n | a | s | T body IHbody s0 | t1 IH1 t2 IH2 l | t1 IH1 t2 IH2 s
    | t IH l | t IH l | t IH s | t IH s | t1 IH1 t2 IH2 t3 IH3 l
    | l t IH | t1 IH1 t2 IH2 t3 IH3 l ];
    intros k u; simpl.
  - destruct (Nat.eqb k n); simpl; reflexivity.
  - rewrite lc_at_open_rec_id with (k := k) (u := subst_env gamma u).
    + reflexivity.
    + apply lc_at_mono with (k := 0); [ lia | apply Hlcenv ].
  - reflexivity.
  - f_equal. apply IHbody.
  - f_equal; [ apply IH1 | apply IH2 ].
  - f_equal; [ apply IH1 | apply IH2 ].
  - f_equal. apply IH.
  - f_equal. apply IH.
  - f_equal. apply IH.
  - f_equal. apply IH.
  - f_equal; [ apply IH1 | apply IH2 | apply IH3 ].
  - f_equal. apply IH.
  - f_equal; [ apply IH1 | apply IH2 | apply IH3 ].
Qed.

Lemma subst_env_open_fvar : forall (gamma : env),
  (forall x, lc_at 0 (gamma x)) ->
  forall (t : tm) (x : atom),
  subst_env gamma (open t (tm_fvar x)) = open (subst_env gamma t) (gamma x).
Proof.
  intros gamma Hlcenv t x. unfold open.
  rewrite subst_env_open_rec; [ reflexivity | exact Hlcenv ].
Qed.

Lemma subst_env_id_on : forall (gamma : env) (t : tm),
  (forall x, In x (fv t) -> gamma x = tm_fvar x) ->
  subst_env gamma t = t.
Proof.
  intros gamma t H.
  transitivity (subst_env env_id t).
  - apply subst_env_ext. intros x Hx. apply H. exact Hx.
  - apply subst_env_id.
Qed.

Lemma has_type_lc : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T H. induction H as
    [ Gamma0 x T0 Hlk Hwf
    | Gamma0 kappa Hwf
    | L Gamma0 T1 body T2 kappa HwfT1 Hwfkappa Hprem IHbody
    | Gamma0 t1 t2 T1 T2 kappa r Ht1 IH1 Ht2 IH2 Hflow
    | Gamma0 t1 t2 T1 T2 kappa Ht1 IH1 Ht2 IH2 Hwf
    | Gamma0 t T1 T2 kappa r Ht IH Hflow
    | Gamma0 t T1 T2 kappa r Ht IH Hflow
    | Gamma0 t T1 T2 kappa Ht IH HwfT2 Hwf
    | Gamma0 t T1 T2 kappa HwfT1 Ht IH Hwf
    | L Gamma0 t body1 body2 T1 T2 T0 kappa r Ht IHt Hflow
        Hprem1 IH1 Hprem2 IH2
    | Gamma0 t T0 l Ht IH
    | Gamma0 t T0 U Ht IH Hsub
    | Gamma0 c yes no k T0 r Hc IHc Hy IHy Hn IHn Hflow ]; simpl.
  - exact I.
  - exact I.
  - pose proof (IHbody (fresh_from L) (fresh_from_not_in L)) as Hlc.
    simpl in Hlc.
    apply (lc_open_fvar_inv body 0 (fresh_from L)). exact Hlc.
  - split; assumption.
  - split; assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - split; [ assumption | split ].
    + apply (lc_open_fvar_inv body1 0 (fresh_from L)).
      apply IH1. apply fresh_from_not_in.
    + apply (lc_open_fvar_inv body2 0 (fresh_from L)).
      apply IH2. apply fresh_from_not_in.
  - assumption.
  - assumption.
  - split; [ assumption | split; assumption ].
Qed.

(* ============================================================ *)
(* Environments and the fundamental theorem                      *)
(* ============================================================ *)

Definition env_lc (gamma : env) : Prop := forall x : atom, lc_at 0 (gamma x).

Definition env_related (l : label) (Gamma : context) (gamma1 gamma2 : env) : Prop :=
  env_lc gamma1 /\ env_lc gamma2 /\
  (forall (x : atom) (T : ty), lookup_context x Gamma = Some T ->
     LRterm l T (gamma1 x) (gamma2 x)).

Lemma obs_sec_dec : forall (kappa : security) (l : label),
  obs_sec kappa l \/ ~ obs_sec kappa l.
Proof. intros [r i] l. unfold obs_sec. destruct i, l; simpl; tauto. Qed.

Lemma obs_sec_protect_r : forall (kappa0 kappa : security) (l : label),
  obs_sec (protect_security kappa0 kappa.(indirect_reader)) l -> obs_sec kappa l.
Proof.
  intros [r0 i0] [r i] l H. simpl in *.
  eapply flows_to_trans; [ apply flows_to_join_r | exact H ].
Qed.

Lemma W_non_obs_intro : forall (l : label) (T : ty) (kappa : security) (v1 v2 : tm),
  ~ obs_sec kappa l -> value v1 -> value v2 -> W l T kappa v1 v2.
Proof.
  intros l T. destruct T; intros kappa v1 v2 Hn H1 H2; simpl.
  all: split; [ exact H1 | split; [ exact H2 | intros H; exfalso; apply Hn; exact H ] ].
Qed.

Lemma lookup_update_eq : forall (Gamma : context) (x : atom) (T : ty),
  lookup_context x (update Gamma x T) = Some T.
Proof.
  intros. unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_update_neq : forall (Gamma : context) (x y : atom) (T : ty),
  x <> y -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T Hne. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply Hne. symmetry. exact E.
  - reflexivity.
Qed.

Lemma env_related_update : forall (l : label) (Gamma : context)
  (gamma1 gamma2 : env) (x : atom) (T1 : ty) (w1 w2 : tm),
  env_related l Gamma gamma1 gamma2 ->
  W l T1 (security_of T1) w1 w2 ->
  env_related l (update Gamma x T1) (env_update gamma1 x w1) (env_update gamma2 x w2).
Proof.
  intros l Gamma gamma1 gamma2 x T1 w1 w2 [Hlc1 [Hlc2 Hrel]] Hw.
  split.
  - unfold env_lc. intros z. unfold env_update.
    destruct (Nat.eqb x z) eqn:E.
    + apply value_lc. eapply W_value_1; eassumption.
    + apply Hlc1.
  - split.
    + unfold env_lc. intros z. unfold env_update.
      destruct (Nat.eqb x z) eqn:E.
      * apply value_lc. eapply W_value_2; eassumption.
      * apply Hlc2.
    + intros z Tz Hz. unfold env_update.
      destruct (Nat.eqb x z) eqn:E.
      * apply Nat.eqb_eq in E. subst z.
        rewrite lookup_update_eq in Hz. injection Hz as HTz. subst Tz.
        apply LRterm_of_W. exact Hw.
      * apply Nat.eqb_neq in E.
        assert (Hz' : lookup_context z Gamma = Some Tz).
        { unfold update in Hz. simpl in Hz.
          destruct (Nat.eqb z x) eqn:E2.
          - apply Nat.eqb_eq in E2. exfalso. apply E. symmetry. exact E2.
          - exact Hz. }
        apply Hrel. exact Hz'.
Qed.

Lemma body_related_open : forall (l : label) (Gamma0 : context) (T_payload T_body : ty)
  (body : tm) (L : list atom)
  (IHbody : forall x : atom, ~ In x L ->
     forall (l' : label) (gamma1 gamma2 : env),
     env_related l' (update Gamma0 x T_payload) gamma1 gamma2 ->
     LRterm l' T_body (subst_env gamma1 (open body (tm_fvar x)))
                      (subst_env gamma2 (open body (tm_fvar x))))
  (gamma1 gamma2 : env) (v1 v2 w1 w2 : tm),
  env_related l Gamma0 gamma1 gamma2 ->
  W l T_payload (security_of T_payload) v1 v2 ->
  multi (open (subst_env gamma1 body) v1) w1 -> value w1 ->
  multi (open (subst_env gamma2 body) v2) w2 -> value w2 ->
  W l T_body (security_of T_body) w1 w2.
Proof.
  intros l Gamma0 T_payload T_body body L IHbody gamma1 gamma2 v1 v2 w1 w2
         Henv Hw Hm1 Hv1 Hm2 Hv2.
  destruct Henv as [Hlc1 [Hlc2 Hrel]].
  set (x := fresh_from (L ++ fv body)).
  assert (HxL : ~ In x L).
  { subst x. intro HIn. apply (fresh_from_not_in (L ++ fv body)).
    apply in_or_app. left. exact HIn. }
  assert (Hxfv : ~ In x (fv body)).
  { subst x. intro HIn. apply (fresh_from_not_in (L ++ fv body)).
    apply in_or_app. right. exact HIn. }
  assert (Henv' : env_related l (update Gamma0 x T_payload)
                    (env_update gamma1 x v1) (env_update gamma2 x v2)).
  { apply env_related_update.
    - split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ].
    - exact Hw. }
  pose proof (IHbody x HxL l (env_update gamma1 x v1) (env_update gamma2 x v2) Henv')
    as Hlr.
  assert (Hlc1' : env_lc (env_update gamma1 x v1)).
  { unfold env_lc. intros z. unfold env_update.
    destruct (Nat.eqb x z) eqn:E.
    - apply value_lc. eapply W_value_1; eassumption.
    - apply Hlc1. }
  assert (Hlc2' : env_lc (env_update gamma2 x v2)).
  { unfold env_lc. intros z. unfold env_update.
    destruct (Nat.eqb x z) eqn:E.
    - apply value_lc. eapply W_value_2; eassumption.
    - apply Hlc2. }
  assert (Hopen1 : subst_env (env_update gamma1 x v1) (open body (tm_fvar x))
                   = open (subst_env gamma1 body) v1).
  { assert (Hsub : subst_env (env_update gamma1 x v1) body = subst_env gamma1 body).
    { apply subst_env_ext. intros z Hz. unfold env_update.
      destruct (Nat.eqb x z) eqn:E.
      - apply Nat.eqb_eq in E. subst z. exfalso. apply Hxfv. exact Hz.
      - reflexivity. }
    rewrite (subst_env_open_fvar (env_update gamma1 x v1) Hlc1' body x).
    rewrite Hsub. unfold env_update. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hopen2 : subst_env (env_update gamma2 x v2) (open body (tm_fvar x))
                   = open (subst_env gamma2 body) v2).
  { assert (Hsub : subst_env (env_update gamma2 x v2) body = subst_env gamma2 body).
    { apply subst_env_ext. intros z Hz. unfold env_update.
      destruct (Nat.eqb x z) eqn:E.
      - apply Nat.eqb_eq in E. subst z. exfalso. apply Hxfv. exact Hz.
      - reflexivity. }
    rewrite (subst_env_open_fvar (env_update gamma2 x v2) Hlc2' body x).
    rewrite Hsub. unfold env_update. rewrite Nat.eqb_refl. reflexivity. }
  eapply Hlr.
  - rewrite Hopen1. exact Hm1.
  - exact Hv1.
  - rewrite Hopen2. exact Hm2.
  - exact Hv2.
Qed.

Lemma protect_result : forall (l : label) (T : ty) (kappa k1 k2 : security) (w1 w2 : tm),
  W l T (security_of T) w1 w2 ->
  security_le k1 kappa -> security_le k2 kappa ->
  W l T (protect_security (security_of T) kappa.(indirect_reader))
       (protect_value w1 k1.(indirect_reader))
       (protect_value w2 k2.(indirect_reader)).
Proof.
  intros l T kappa k1 k2 w1 w2 Hw S1 S2.
  assert (Hp : W l T (protect_security (security_of T)
                        (join k1.(indirect_reader) k2.(indirect_reader)))
                   (protect_value w1 k1.(indirect_reader))
                   (protect_value w2 k2.(indirect_reader)))
    by (eapply W_protect2; exact Hw).
  eapply W_mono with (kappa1 := protect_security (security_of T)
                        (join k1.(indirect_reader) k2.(indirect_reader))).
  - apply protect_security_le; [ apply security_le_refl | ].
    apply join_lub; [ exact (proj2 S1) | exact (proj2 S2) ].
  - exact Hp.
Qed.

Lemma W_sum_inv : forall (l : label) (T1 T2 : ty) (kappa0 k : security)
  (v1 v2 : tm),
  W l (Ty_Sum T1 T2 kappa0) k v1 v2 ->
  value v1 /\ value v2 /\
  (obs_sec k l ->
     (exists w1 w2 k1 k2, v1 = tm_inl w1 k1 /\ v2 = tm_inl w2 k2 /\
        security_le k1 k /\ security_le k2 k /\ W l T1 (security_of T1) w1 w2) \/
     (exists w1 w2 k1 k2, v1 = tm_inr w1 k1 /\ v2 = tm_inr w2 k2 /\
        security_le k1 k /\ security_le k2 k /\ W l T2 (security_of T2) w1 w2)).
Proof. intros. simpl in H. exact H. Qed.

Lemma fundamental : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T ->
  forall (l : label) (gamma1 gamma2 : env),
  env_related l Gamma gamma1 gamma2 ->
  LRterm l T (subst_env gamma1 t) (subst_env gamma2 t).
Proof.
  intros Gamma t T H. induction H as
    [ Gamma0 x T0 Hlk Hwf
    | Gamma0 kappa Hwf
    | L Gamma0 T1 body T2 kappa HwfT1 Hwfkappa Hprem IHbody
    | Gamma0 t1 t2 T1 T2 kappa r Ht1 IH1 Ht2 IH2 Hflow
    | Gamma0 t1 t2 T1 T2 kappa Ht1 IH1 Ht2 IH2 Hwf
    | Gamma0 t T1 T2 kappa r Ht IH Hflow
    | Gamma0 t T1 T2 kappa r Ht IH Hflow
    | Gamma0 t T1 T2 kappa Ht IH HwfT2 Hwf
    | Gamma0 t T1 T2 kappa HwfT1 Ht IH Hwf
    | L Gamma0 t body1 body2 T1 T2 T0 kappa r Ht IHt Hflow
        Hprem1 IH1 Hprem2 IH2
    | Gamma0 t T0 l0 Ht IH
    | Gamma0 t T0 U Ht IH Hsub
    | Gamma0 c yes no k T0 r Hc IHc Hy IHy Hn IHn Hflow ].
  - (* T_Var *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    apply Hrel. exact Hlk.
  - (* T_Unit *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    unfold LRterm. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
    assert (Hv : value (tm_unit kappa)) by constructor.
    rewrite (multi_value_eq _ _ Hm1 Hv).
    rewrite (multi_value_eq _ _ Hm2 Hv).
    simpl. split; [ constructor | split; [ constructor | intros _ ] ].
    exists kappa, kappa.
    split; [ reflexivity | split; [ reflexivity |
      split; [ apply security_le_refl | apply security_le_refl ] ] ].
  - (* T_Abs *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    unfold LRterm. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
    assert (E1 : v1 = tm_abs T1 (subst_env gamma1 body) kappa)
      by (eapply multi_abs_eq; exact Hm1).
    assert (E2 : v2 = tm_abs T1 (subst_env gamma2 body) kappa)
      by (eapply multi_abs_eq; exact Hm2).
    subst v1. subst v2.
    simpl.
    split; [ exact Hval1 | split; [ exact Hval2 | intros Hobs ] ].
    exists T1, (subst_env gamma1 body), kappa.
    split; [ reflexivity | split; [ apply security_le_refl | ] ].
    exists T1, (subst_env gamma2 body), kappa.
    split; [ reflexivity | split; [ apply security_le_refl | ] ].
    intros w1 w2 r Hw12 Hr u1 u2 Hmu1 Huv1 Hmu2 Huv2.
    assert (Hvw1 : value w1) by (eapply W_value_1; eassumption).
    assert (Hvw2 : value w2) by (eapply W_value_2; eassumption).
    destruct (eval_app_abs_decomp T1 (subst_env gamma1 body) w1 kappa r u1
                Hval1 Hvw1 Hr Hmu1 Huv1) as (v1' & Hmv1 & Hvv1' & Heq1).
    destruct (eval_app_abs_decomp T1 (subst_env gamma2 body) w2 kappa r u2
                Hval2 Hvw2 Hr Hmu2 Huv2) as (v2' & Hmv2 & Hvv2' & Heq2).
    set (x := fresh_from (L ++ fv body)).
    assert (HxL : ~ In x L).
    { subst x. intro HIn. apply (fresh_from_not_in (L ++ fv body)).
      apply in_or_app. left. exact HIn. }
    assert (Hxfv : ~ In x (fv body)).
    { subst x. intro HIn. apply (fresh_from_not_in (L ++ fv body)).
      apply in_or_app. right. exact HIn. }
    assert (Henv' : env_related l (update Gamma0 x T1)
                      (env_update gamma1 x w1) (env_update gamma2 x w2)).
    { apply env_related_update.
      - split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ].
      - exact Hw12. }
    pose proof (IHbody x HxL l (env_update gamma1 x w1) (env_update gamma2 x w2) Henv')
      as Hlr.
    assert (Hlc1' : env_lc (env_update gamma1 x w1)).
    { unfold env_lc. intros z. unfold env_update.
      destruct (Nat.eqb x z) eqn:E.
      - apply value_lc. exact Hvw1.
      - apply Hlc1. }
    assert (Hlc2' : env_lc (env_update gamma2 x w2)).
    { unfold env_lc. intros z. unfold env_update.
      destruct (Nat.eqb x z) eqn:E.
      - apply value_lc. exact Hvw2.
      - apply Hlc2. }
    assert (Hopen1 : subst_env (env_update gamma1 x w1) (open body (tm_fvar x))
                     = open (subst_env gamma1 body) w1).
    { assert (Hsub : subst_env (env_update gamma1 x w1) body = subst_env gamma1 body).
      { apply subst_env_ext. intros z Hz. unfold env_update.
        destruct (Nat.eqb x z) eqn:E.
        - apply Nat.eqb_eq in E. subst z. exfalso. apply Hxfv. exact Hz.
        - reflexivity. }
      rewrite (subst_env_open_fvar (env_update gamma1 x w1) Hlc1' body x).
      rewrite Hsub. unfold env_update. rewrite Nat.eqb_refl. reflexivity. }
    assert (Hopen2 : subst_env (env_update gamma2 x w2) (open body (tm_fvar x))
                     = open (subst_env gamma2 body) w2).
    { assert (Hsub : subst_env (env_update gamma2 x w2) body = subst_env gamma2 body).
      { apply subst_env_ext. intros z Hz. unfold env_update.
        destruct (Nat.eqb x z) eqn:E.
        - apply Nat.eqb_eq in E. subst z. exfalso. apply Hxfv. exact Hz.
        - reflexivity. }
      rewrite (subst_env_open_fvar (env_update gamma2 x w2) Hlc2' body x).
      rewrite Hsub. unfold env_update. rewrite Nat.eqb_refl. reflexivity. }
    assert (Hwbody : W l T2 (security_of T2) v1' v2').
    { eapply Hlr.
      - rewrite Hopen1. exact Hmv1.
      - exact Hvv1'.
      - rewrite Hopen2. exact Hmv2.
      - exact Hvv2'. }
    assert (Hprot : W l T2
                      (protect_security (security_of T2)
                         (join kappa.(indirect_reader) kappa.(indirect_reader)))
                      (protect_value v1' kappa.(indirect_reader))
                      (protect_value v2' kappa.(indirect_reader))).
    { eapply W_protect2. exact Hwbody. }
    rewrite join_idem in Hprot.
    rewrite Heq1, Heq2.
    exact Hprot.
  - (* T_App *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    unfold LRterm. intros u1 u2 Hm1 Hval1 Hm2 Hval2.
    rewrite security_of_ty_protect. rewrite W_ty_protect.
    destruct (eval_app_decomp (subst_env gamma1 t1) (subst_env gamma1 t2) r u1 Hm1 Hval1)
      as (va1 & vb1 & Hma1 & Hva1 & Hmb1 & Hvb1 & Hcont1).
    destruct (eval_app_decomp (subst_env gamma2 t1) (subst_env gamma2 t2) r u2 Hm2 Hval2)
      as (va2 & vb2 & Hma2 & Hva2 & Hmb2 & Hvb2 & Hcont2).
    assert (Hlr1 : LRterm l (Ty_Arrow T1 T2 kappa)
                     (subst_env gamma1 t1) (subst_env gamma2 t1))
      by (apply IH1; split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ]).
    assert (Hlr2 : LRterm l T1 (subst_env gamma1 t2) (subst_env gamma2 t2))
      by (apply IH2; split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ]).
    assert (Hwfun : W l (Ty_Arrow T1 T2 kappa)
                      (security_of (Ty_Arrow T1 T2 kappa)) va1 va2).
    { unfold LRterm in Hlr1. apply (Hlr1 va1 va2 Hma1 Hva1 Hma2 Hva2). }
    assert (Hwarg : W l T1 (security_of T1) vb1 vb2).
    { unfold LRterm in Hlr2. apply (Hlr2 vb1 vb2 Hmb1 Hvb1 Hmb2 Hvb2). }
    destruct (obs_sec_dec (protect_security (security_of T2) kappa.(indirect_reader)) l)
      as [HobsT | HnobsT].
    + assert (Hobs : obs_sec kappa l) by (eapply obs_sec_protect_r; eassumption).
      simpl in Hwfun.
      destruct Hwfun as [Hvva1 [Hvva2 Hcl]].
      destruct (Hcl Hobs) as
        (T1a & b1 & k1 & E1 & S1 & T1b & b2 & k2 & E2 & S2 & Hclause).
      apply (Hclause vb1 vb2 r).
      * exact Hwarg.
      * exact Hflow.
      * exact Hcont1.
      * exact Hval1.
      * exact Hcont2.
      * exact Hval2.
    + apply W_non_obs_intro; [ exact HnobsT | exact Hval1 | exact Hval2 ].
  - (* T_Pair *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    unfold LRterm. intros u1 u2 Hm1 Hval1 Hm2 Hval2.
    destruct (eval_pair_decomp (subst_env gamma1 t1) (subst_env gamma1 t2) kappa u1 Hm1 Hval1)
      as (va1 & vb1 & Hma1 & Hva1 & Hmb1 & Hvb1 & Heq1).
    destruct (eval_pair_decomp (subst_env gamma2 t1) (subst_env gamma2 t2) kappa u2 Hm2 Hval2)
      as (va2 & vb2 & Hma2 & Hva2 & Hmb2 & Hvb2 & Heq2).
    assert (Hlr1 : LRterm l T1 (subst_env gamma1 t1) (subst_env gamma2 t1))
      by (apply IH1; split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ]).
    assert (Hlr2 : LRterm l T2 (subst_env gamma1 t2) (subst_env gamma2 t2))
      by (apply IH2; split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ]).
    assert (Hw1 : W l T1 (security_of T1) va1 va2)
      by (unfold LRterm in Hlr1; apply (Hlr1 va1 va2 Hma1 Hva1 Hma2 Hva2)).
    assert (Hw2 : W l T2 (security_of T2) vb1 vb2)
      by (unfold LRterm in Hlr2; apply (Hlr2 vb1 vb2 Hmb1 Hvb1 Hmb2 Hvb2)).
    destruct (obs_sec_dec kappa l) as [Hobs | Hnobs].
    + rewrite Heq1, Heq2. simpl.
      split; [ apply v_pair; [ exact Hva1 | exact Hvb1 ] |
        split; [ apply v_pair; [ exact Hva2 | exact Hvb2 ] | intros _ ] ].
      exists va1, vb1, va2, vb2, kappa, kappa.
      split; [ reflexivity | split; [ reflexivity |
        split; [ apply security_le_refl | split; [ apply security_le_refl |
          split; [ exact Hw1 | exact Hw2 ] ] ] ] ].
    + apply W_non_obs_intro; [ exact Hnobs | exact Hval1 | exact Hval2 ].
  - (* T_Fst *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    unfold LRterm. intros u1 u2 Hm1 Hval1 Hm2 Hval2.
    rewrite security_of_ty_protect. rewrite W_ty_protect.
    destruct (eval_fst_decomp (subst_env gamma1 t) r u1 Hm1 Hval1)
      as (va1 & vb1 & k1 & Hma1 & Hva1 & Hvb1 & Hflow1 & Heq1).
    destruct (eval_fst_decomp (subst_env gamma2 t) r u2 Hm2 Hval2)
      as (va2 & vb2 & k2 & Hma2 & Hva2 & Hvb2 & Hflow2 & Heq2).
    assert (Hlr : LRterm l (Ty_Prod T1 T2 kappa)
                   (subst_env gamma1 t) (subst_env gamma2 t))
      by (apply IH; split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ]).
    assert (Hwpair : W l (Ty_Prod T1 T2 kappa) (security_of (Ty_Prod T1 T2 kappa))
                        (tm_pair va1 vb1 k1) (tm_pair va2 vb2 k2)).
    { unfold LRterm in Hlr.
      apply (Hlr (tm_pair va1 vb1 k1) (tm_pair va2 vb2 k2) Hma1
               (v_pair _ _ _ Hva1 Hvb1) Hma2 (v_pair _ _ _ Hva2 Hvb2)). }
    destruct (obs_sec_dec (protect_security (security_of T1) kappa.(indirect_reader)) l)
      as [HobsT | HnobsT].
    + assert (Hobs : obs_sec kappa l) by (eapply obs_sec_protect_r; eassumption).
      simpl in Hwpair.
      destruct Hwpair as [Hv1 [Hv2 Hcl]].
      destruct (Hcl Hobs) as
        (a1 & b1 & a2 & b2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HWa & HWb).
      injection E1 as Ha1 Hb1 Hk1. injection E2 as Ha2 Hb2 Hk2.
      subst a1. subst b1. subst kk1. subst a2. subst b2. subst kk2.
      assert (Hprot : W l T1
                        (protect_security (security_of T1)
                           (join k1.(indirect_reader) k2.(indirect_reader)))
                        (protect_value va1 k1.(indirect_reader))
                        (protect_value va2 k2.(indirect_reader)))
        by (eapply W_protect2; exact HWa).
      rewrite Heq1, Heq2.
      eapply W_mono with
        (kappa1 := protect_security (security_of T1)
                     (join k1.(indirect_reader) k2.(indirect_reader))).
      * apply protect_security_le; [ apply security_le_refl | ].
        apply join_lub; [ exact (proj2 S1) | exact (proj2 S2) ].
      * exact Hprot.
    + apply W_non_obs_intro; [ exact HnobsT | exact Hval1 | exact Hval2 ].
  - (* T_Snd *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    unfold LRterm. intros u1 u2 Hm1 Hval1 Hm2 Hval2.
    rewrite security_of_ty_protect. rewrite W_ty_protect.
    destruct (eval_snd_decomp (subst_env gamma1 t) r u1 Hm1 Hval1)
      as (va1 & vb1 & k1 & Hma1 & Hva1 & Hvb1 & Hflow1 & Heq1).
    destruct (eval_snd_decomp (subst_env gamma2 t) r u2 Hm2 Hval2)
      as (va2 & vb2 & k2 & Hma2 & Hva2 & Hvb2 & Hflow2 & Heq2).
    assert (Hlr : LRterm l (Ty_Prod T1 T2 kappa)
                   (subst_env gamma1 t) (subst_env gamma2 t))
      by (apply IH; split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ]).
    assert (Hwpair : W l (Ty_Prod T1 T2 kappa) (security_of (Ty_Prod T1 T2 kappa))
                        (tm_pair va1 vb1 k1) (tm_pair va2 vb2 k2)).
    { unfold LRterm in Hlr.
      apply (Hlr (tm_pair va1 vb1 k1) (tm_pair va2 vb2 k2) Hma1
               (v_pair _ _ _ Hva1 Hvb1) Hma2 (v_pair _ _ _ Hva2 Hvb2)). }
    destruct (obs_sec_dec (protect_security (security_of T2) kappa.(indirect_reader)) l)
      as [HobsT | HnobsT].
    + assert (Hobs : obs_sec kappa l) by (eapply obs_sec_protect_r; eassumption).
      simpl in Hwpair.
      destruct Hwpair as [Hv1 [Hv2 Hcl]].
      destruct (Hcl Hobs) as
        (a1 & b1 & a2 & b2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HWa & HWb).
      injection E1 as Ha1 Hb1 Hk1. injection E2 as Ha2 Hb2 Hk2.
      subst a1. subst b1. subst kk1. subst a2. subst b2. subst kk2.
      assert (Hprot : W l T2
                        (protect_security (security_of T2)
                           (join k1.(indirect_reader) k2.(indirect_reader)))
                        (protect_value vb1 k1.(indirect_reader))
                        (protect_value vb2 k2.(indirect_reader)))
        by (eapply W_protect2; exact HWb).
      rewrite Heq1, Heq2.
      eapply W_mono with
        (kappa1 := protect_security (security_of T2)
                     (join k1.(indirect_reader) k2.(indirect_reader))).
      * apply protect_security_le; [ apply security_le_refl | ].
        apply join_lub; [ exact (proj2 S1) | exact (proj2 S2) ].
      * exact Hprot.
    + apply W_non_obs_intro; [ exact HnobsT | exact Hval1 | exact Hval2 ].
  - (* T_Inl *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    unfold LRterm. intros u1 u2 Hm1 Hval1 Hm2 Hval2.
    destruct (eval_inl_decomp (subst_env gamma1 t) kappa u1 Hm1 Hval1)
      as (va1 & Hma1 & Hva1 & Heq1).
    destruct (eval_inl_decomp (subst_env gamma2 t) kappa u2 Hm2 Hval2)
      as (va2 & Hma2 & Hva2 & Heq2).
    assert (Hlr : LRterm l T1 (subst_env gamma1 t) (subst_env gamma2 t))
      by (apply IH; split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ]).
    assert (Hw : W l T1 (security_of T1) va1 va2)
      by (unfold LRterm in Hlr; apply (Hlr va1 va2 Hma1 Hva1 Hma2 Hva2)).
    destruct (obs_sec_dec kappa l) as [Hobs | Hnobs].
    + rewrite Heq1, Heq2. simpl.
      split; [ apply v_inl; exact Hva1 |
        split; [ apply v_inl; exact Hva2 | intros _ ] ].
      left. exists va1, va2, kappa, kappa.
      split; [ reflexivity | split; [ reflexivity |
        split; [ apply security_le_refl | split; [ apply security_le_refl |
          exact Hw ] ] ] ].
    + apply W_non_obs_intro; [ exact Hnobs | exact Hval1 | exact Hval2 ].
  - (* T_Inr *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    unfold LRterm. intros u1 u2 Hm1 Hval1 Hm2 Hval2.
    destruct (eval_inr_decomp (subst_env gamma1 t) kappa u1 Hm1 Hval1)
      as (va1 & Hma1 & Hva1 & Heq1).
    destruct (eval_inr_decomp (subst_env gamma2 t) kappa u2 Hm2 Hval2)
      as (va2 & Hma2 & Hva2 & Heq2).
    assert (Hlr : LRterm l T2 (subst_env gamma1 t) (subst_env gamma2 t))
      by (apply IH; split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ]).
    assert (Hw : W l T2 (security_of T2) va1 va2)
      by (unfold LRterm in Hlr; apply (Hlr va1 va2 Hma1 Hva1 Hma2 Hva2)).
    destruct (obs_sec_dec kappa l) as [Hobs | Hnobs].
    + rewrite Heq1, Heq2. simpl.
      split; [ apply v_inr; exact Hva1 |
        split; [ apply v_inr; exact Hva2 | intros _ ] ].
      right. exists va1, va2, kappa, kappa.
      split; [ reflexivity | split; [ reflexivity |
        split; [ apply security_le_refl | split; [ apply security_le_refl |
          exact Hw ] ] ] ].
    + apply W_non_obs_intro; [ exact Hnobs | exact Hval1 | exact Hval2 ].

  - (* T_Case *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    unfold LRterm. intros u1 u2 Hm1 Hval1 Hm2 Hval2.
    rewrite security_of_ty_protect. rewrite W_ty_protect.
    assert (Henv0 : env_related l Gamma0 gamma1 gamma2)
      by (split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ]).
    assert (Hlr : LRterm l (Ty_Sum T1 T2 kappa)
                   (subst_env gamma1 t) (subst_env gamma2 t))
      by (apply IHt; exact Henv0).
    destruct (obs_sec_dec (protect_security (security_of T0) kappa.(indirect_reader)) l)
      as [HobsT | HnobsT].
    + assert (Hobs : obs_sec kappa l) by (eapply obs_sec_protect_r; eassumption).
      destruct (eval_case_decomp (subst_env gamma1 t) (subst_env gamma1 body1)
                  (subst_env gamma1 body2) r u1 Hm1 Hval1)
        as [[v1 [k1 [w1 [Hma1 [Hv1 [Hflow1 [Hmb1 [Hwv1 Heq1]]]]]]]]
           |[v1 [k1 [w1 [Hma1 [Hv1 [Hflow1 [Hmb1 [Hwv1 Heq1]]]]]]]]];
      destruct (eval_case_decomp (subst_env gamma2 t) (subst_env gamma2 body1)
                  (subst_env gamma2 body2) r u2 Hm2 Hval2)
        as [[v2 [k2 [w2 [Hma2 [Hv2 [Hflow2 [Hmb2 [Hwv2 Heq2]]]]]]]]
           |[v2 [k2 [w2 [Hma2 [Hv2 [Hflow2 [Hmb2 [Hwv2 Heq2]]]]]]]]].
      * assert (Hwsum : W l (Ty_Sum T1 T2 kappa) (security_of (Ty_Sum T1 T2 kappa))
                           (tm_inl v1 k1) (tm_inl v2 k2)).
        { unfold LRterm in Hlr.
          apply (Hlr _ _ Hma1 (v_inl _ _ Hv1) Hma2 (v_inl _ _ Hv2)). }
        apply W_sum_inv in Hwsum.
        destruct Hwsum as [Hv1' [Hv2' Hcl]].
        destruct (Hcl Hobs) as
          [[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]
          |[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]].
        -- injection E1 as Ha1 Hk1. injection E2 as Ha2 Hk2.
           subst a1. subst kk1. subst a2. subst kk2.
           assert (Hwbody : W l T0 (security_of T0) w1 w2).
           { eapply body_related_open.
             - exact IH1.
             - exact Henv0.
             - exact HWa.
             - exact Hmb1.
             - exact Hwv1.
             - exact Hmb2.
             - exact Hwv2. }
           rewrite Heq1, Heq2.
           eapply protect_result.
           ++ exact Hwbody.
           ++ exact S1.
           ++ exact S2.
        -- discriminate E1.
      * assert (Hwsum : W l (Ty_Sum T1 T2 kappa) (security_of (Ty_Sum T1 T2 kappa))
                           (tm_inl v1 k1) (tm_inr v2 k2)).
        { unfold LRterm in Hlr.
          apply (Hlr _ _ Hma1 (v_inl _ _ Hv1) Hma2 (v_inr _ _ Hv2)). }
        apply W_sum_inv in Hwsum.
        destruct Hwsum as [Hv1' [Hv2' Hcl]].
        destruct (Hcl Hobs) as
          [[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]
          |[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]].
        -- discriminate E2.
        -- discriminate E1.
      * assert (Hwsum : W l (Ty_Sum T1 T2 kappa) (security_of (Ty_Sum T1 T2 kappa))
                           (tm_inr v1 k1) (tm_inl v2 k2)).
        { unfold LRterm in Hlr.
          apply (Hlr _ _ Hma1 (v_inr _ _ Hv1) Hma2 (v_inl _ _ Hv2)). }
        apply W_sum_inv in Hwsum.
        destruct Hwsum as [Hv1' [Hv2' Hcl]].
        destruct (Hcl Hobs) as
          [[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]
          |[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]].
        -- discriminate E1.
        -- discriminate E2.
      * assert (Hwsum : W l (Ty_Sum T1 T2 kappa) (security_of (Ty_Sum T1 T2 kappa))
                           (tm_inr v1 k1) (tm_inr v2 k2)).
        { unfold LRterm in Hlr.
          apply (Hlr _ _ Hma1 (v_inr _ _ Hv1) Hma2 (v_inr _ _ Hv2)). }
        apply W_sum_inv in Hwsum.
        destruct Hwsum as [Hv1' [Hv2' Hcl]].
        destruct (Hcl Hobs) as
          [[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]
          |[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]].
        -- discriminate E1.
        -- injection E1 as Ha1 Hk1. injection E2 as Ha2 Hk2.
           subst a1. subst kk1. subst a2. subst kk2.
           assert (Hwbody : W l T0 (security_of T0) w1 w2).
           { eapply body_related_open.
             - exact IH2.
             - exact Henv0.
             - exact HWa.
             - exact Hmb1.
             - exact Hwv1.
             - exact Hmb2.
             - exact Hwv2. }
           rewrite Heq1, Heq2.
           eapply protect_result.
           ++ exact Hwbody.
           ++ exact S1.
           ++ exact S2.
    + apply W_non_obs_intro; [ exact HnobsT | exact Hval1 | exact Hval2 ].
  - (* T_Protect *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    unfold LRterm. intros u1 u2 Hm1 Hval1 Hm2 Hval2.
    rewrite security_of_ty_protect. rewrite W_ty_protect.
    destruct (eval_protect_decomp l0 (subst_env gamma1 t) u1 Hm1 Hval1)
      as (v1 & Hm1' & Hv1 & Heq1).
    destruct (eval_protect_decomp l0 (subst_env gamma2 t) u2 Hm2 Hval2)
      as (v2 & Hm2' & Hv2 & Heq2).
    assert (Hlr : LRterm l T0 (subst_env gamma1 t) (subst_env gamma2 t))
      by (apply IH; split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ]).
    assert (Hw : W l T0 (security_of T0) v1 v2)
      by (unfold LRterm in Hlr; apply (Hlr v1 v2 Hm1' Hv1 Hm2' Hv2)).
    rewrite Heq1, Heq2.
    assert (Hp : W l T0 (protect_security (security_of T0) (join l0 l0))
                    (protect_value v1 l0) (protect_value v2 l0))
      by (eapply W_protect2; exact Hw).
    rewrite join_idem in Hp.
    exact Hp.
  - (* T_Sub *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    unfold LRterm. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
    assert (Hlr : LRterm l T0 (subst_env gamma1 t) (subst_env gamma2 t))
      by (apply IH; split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ]).
    assert (Hw : W l T0 (security_of T0) v1 v2)
      by (unfold LRterm in Hlr; apply (Hlr v1 v2 Hm1 Hval1 Hm2 Hval2)).
    eapply W_subtype; [ exact Hsub | apply subtype_security_le; exact Hsub | exact Hw ].
  - (* T_If *)
    intros l gamma1 gamma2 Henv. destruct Henv as [Hlc1 [Hlc2 Hrel]]. simpl.
    unfold LRterm. intros u1 u2 Hm1 Hval1 Hm2 Hval2.
    rewrite security_of_ty_protect. rewrite W_ty_protect.
    assert (Henv0 : env_related l Gamma0 gamma1 gamma2)
      by (split; [ exact Hlc1 | split; [ exact Hlc2 | exact Hrel ] ]).
    assert (Hlr : LRterm l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                   (subst_env gamma1 c) (subst_env gamma2 c))
      by (apply IHc; exact Henv0).
    destruct (obs_sec_dec (protect_security (security_of T0) k.(indirect_reader)) l)
      as [HobsT | HnobsT].
    + assert (Hobs : obs_sec k l) by (eapply obs_sec_protect_r; eassumption).
      destruct (eval_if_decomp (subst_env gamma1 c) (subst_env gamma1 yes)
                  (subst_env gamma1 no) r u1 Hm1 Hval1)
        as [[v1 [k1 [w1 [Hma1 [Hv1 [Hflow1 [Hmb1 [Hwv1 Heq1]]]]]]]]
           |[v1 [k1 [w1 [Hma1 [Hv1 [Hflow1 [Hmb1 [Hwv1 Heq1]]]]]]]]];
      destruct (eval_if_decomp (subst_env gamma2 c) (subst_env gamma2 yes)
                  (subst_env gamma2 no) r u2 Hm2 Hval2)
        as [[v2 [k2 [w2 [Hma2 [Hv2 [Hflow2 [Hmb2 [Hwv2 Heq2]]]]]]]]
           |[v2 [k2 [w2 [Hma2 [Hv2 [Hflow2 [Hmb2 [Hwv2 Heq2]]]]]]]]].
      * assert (Hwsum : W l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                           (security_of (Ty_Sum (Ty_Unit public) (Ty_Unit public) k))
                           (tm_inl v1 k1) (tm_inl v2 k2)).
        { unfold LRterm in Hlr.
          apply (Hlr _ _ Hma1 (v_inl _ _ Hv1) Hma2 (v_inl _ _ Hv2)). }
        apply W_sum_inv in Hwsum.
        destruct Hwsum as [Hv1' [Hv2' Hcl]].
        destruct (Hcl Hobs) as
          [[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]
          |[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]].
        -- injection E1 as Ha1 Hk1. injection E2 as Ha2 Hk2.
           subst a1. subst kk1. subst a2. subst kk2.
           assert (Hlr_y : LRterm l T0 (subst_env gamma1 yes) (subst_env gamma2 yes))
             by (apply IHy; exact Henv0).
           assert (Hwbody : W l T0 (security_of T0) w1 w2).
           { unfold LRterm in Hlr_y. apply (Hlr_y w1 w2 Hmb1 Hwv1 Hmb2 Hwv2). }
           rewrite Heq1, Heq2.
           eapply protect_result.
           ++ exact Hwbody.
           ++ exact S1.
           ++ exact S2.
        -- discriminate E1.
      * assert (Hwsum : W l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                           (security_of (Ty_Sum (Ty_Unit public) (Ty_Unit public) k))
                           (tm_inl v1 k1) (tm_inr v2 k2)).
        { unfold LRterm in Hlr.
          apply (Hlr _ _ Hma1 (v_inl _ _ Hv1) Hma2 (v_inr _ _ Hv2)). }
        apply W_sum_inv in Hwsum.
        destruct Hwsum as [Hv1' [Hv2' Hcl]].
        destruct (Hcl Hobs) as
          [[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]
          |[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]].
        -- discriminate E2.
        -- discriminate E1.
      * assert (Hwsum : W l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                           (security_of (Ty_Sum (Ty_Unit public) (Ty_Unit public) k))
                           (tm_inr v1 k1) (tm_inl v2 k2)).
        { unfold LRterm in Hlr.
          apply (Hlr _ _ Hma1 (v_inr _ _ Hv1) Hma2 (v_inl _ _ Hv2)). }
        apply W_sum_inv in Hwsum.
        destruct Hwsum as [Hv1' [Hv2' Hcl]].
        destruct (Hcl Hobs) as
          [[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]
          |[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]].
        -- discriminate E1.
        -- discriminate E2.
      * assert (Hwsum : W l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                           (security_of (Ty_Sum (Ty_Unit public) (Ty_Unit public) k))
                           (tm_inr v1 k1) (tm_inr v2 k2)).
        { unfold LRterm in Hlr.
          apply (Hlr _ _ Hma1 (v_inr _ _ Hv1) Hma2 (v_inr _ _ Hv2)). }
        apply W_sum_inv in Hwsum.
        destruct Hwsum as [Hv1' [Hv2' Hcl]].
        destruct (Hcl Hobs) as
          [[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]
          |[a1 [a2 [kk1 [kk2 [E1 [E2 [S1 [S2 HWa]]]]]]]]].
        -- discriminate E1.
        -- injection E1 as Ha1 Hk1. injection E2 as Ha2 Hk2.
           subst a1. subst kk1. subst a2. subst kk2.
           assert (Hlr_n : LRterm l T0 (subst_env gamma1 no) (subst_env gamma2 no))
             by (apply IHn; exact Henv0).
           assert (Hwbody : W l T0 (security_of T0) w1 w2).
           { unfold LRterm in Hlr_n. apply (Hlr_n w1 w2 Hmb1 Hwv1 Hmb2 Hwv2). }
           rewrite Heq1, Heq2.
           eapply protect_result.
           ++ exact Hwbody.
           ++ exact S1.
           ++ exact S2.
    + apply W_non_obs_intro; [ exact HnobsT | exact Hval1 | exact Hval2 ].
Qed.

(* ============================================================ *)
(* Plugging terms into program contexts                          *)
(* ============================================================ *)

Definition gamma_plug (x : atom) (u : tm) : env :=
  fun z => if Nat.eqb x z then u else tm_fvar z.

Lemma gamma_plug_lc : forall (x : atom) (u : tm),
  lc_at 0 u -> env_lc (gamma_plug x u).
Proof.
  intros x u Hu z. unfold gamma_plug.
  destruct (Nat.eqb x z); [ exact Hu | exact I ].
Qed.

Lemma subst_env_gamma_plug_id : forall (x : atom) (u t : tm),
  ~ In x (fv t) -> subst_env (gamma_plug x u) t = t.
Proof.
  intros x u t Hx. apply subst_env_id_on. intros z Hz. unfold gamma_plug.
  destruct (Nat.eqb x z) eqn:E.
  - apply Nat.eqb_eq in E. subst z. exfalso. apply Hx. exact Hz.
  - reflexivity.
Qed.

Lemma notin_app_l : forall (x : atom) (a b : list atom),
  ~ In x (a ++ b) -> ~ In x a.
Proof. intros x a b H Hin. apply H. apply in_or_app. left. exact Hin. Qed.

Lemma notin_app_r : forall (x : atom) (a b : list atom),
  ~ In x (a ++ b) -> ~ In x b.
Proof. intros x a b H Hin. apply H. apply in_or_app. right. exact Hin. Qed.

Lemma notin_app3_1 : forall (x : atom) (a b c : list atom),
  ~ In x (a ++ b ++ c) -> ~ In x a.
Proof. intros x a b c H. apply notin_app_l in H. exact H. Qed.

Lemma notin_app3_2 : forall (x : atom) (a b c : list atom),
  ~ In x (a ++ b ++ c) -> ~ In x b.
Proof. intros x a b c H. apply notin_app_r in H. apply notin_app_l in H. exact H. Qed.

Lemma notin_app3_3 : forall (x : atom) (a b c : list atom),
  ~ In x (a ++ b ++ c) -> ~ In x c.
Proof. intros x a b c H. apply notin_app_r in H. apply notin_app_r in H. exact H. Qed.

Fixpoint context_fv (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ => context_fv C'
  | C_AppLeft C' t2 _ => context_fv C' ++ fv t2
  | C_AppRight t1 C' _ => fv t1 ++ context_fv C'
  | C_PairLeft C' t2 _ => context_fv C' ++ fv t2
  | C_PairRight t1 C' _ => fv t1 ++ context_fv C'
  | C_Fst C' _ => context_fv C'
  | C_Snd C' _ => context_fv C'
  | C_Inl C' _ => context_fv C'
  | C_Inr C' _ => context_fv C'
  | C_CaseScrutinee C' body1 body2 _ => context_fv C' ++ fv body1 ++ fv body2
  | C_CaseLeft t0 C' body2 _ => fv t0 ++ context_fv C' ++ fv body2
  | C_CaseRight t0 body1 C' _ => fv t0 ++ fv body1 ++ context_fv C'
  | C_Protect _ C' => context_fv C'
  | C_IfCondition C' y n _ => context_fv C' ++ fv y ++ fv n
  | C_IfThen c C' n _ => fv c ++ context_fv C' ++ fv n
  | C_IfElse c y C' _ => fv c ++ fv y ++ context_fv C'
  end.

Lemma subst_env_plug : forall (C : program_context) (x : atom) (u : tm),
  ~ In x (context_fv C) ->
  subst_env (gamma_plug x u) (plug C (tm_fvar x)) = plug C u.
Proof.
  intros C. induction C as
    [ | T C' IHC k | C' IHC t2 r | t1 C' IHC r | C' IHC t2 k | t1 C' IHC k
    | C' IHC r | C' IHC r | C' IHC k | C' IHC k | C' IHC b1 b2 r
    | t0 C' IHC b2 r | t0 b1 C' IHC r | l0 C' IHC | C' IHC y n r
    | c C' IHC n r | c y C' IHC r ];
    intros x u H; simpl in *.
  - unfold gamma_plug. rewrite Nat.eqb_refl. reflexivity.
  - f_equal. apply IHC. exact H.
  - assert (H1 : ~ In x (context_fv C')) by (apply notin_app_l with (b := fv t2); exact H).
    assert (H2 : ~ In x (fv t2)) by (apply notin_app_r with (a := context_fv C'); exact H).
    rewrite (subst_env_gamma_plug_id x u t2 H2).
    rewrite (IHC x u H1). reflexivity.
  - assert (H1 : ~ In x (fv t1)) by (apply notin_app_l with (b := context_fv C'); exact H).
    assert (H2 : ~ In x (context_fv C')) by (apply notin_app_r with (a := fv t1); exact H).
    rewrite (subst_env_gamma_plug_id x u t1 H1).
    rewrite (IHC x u H2). reflexivity.
  - assert (H1 : ~ In x (context_fv C')) by (apply notin_app_l with (b := fv t2); exact H).
    assert (H2 : ~ In x (fv t2)) by (apply notin_app_r with (a := context_fv C'); exact H).
    rewrite (subst_env_gamma_plug_id x u t2 H2).
    rewrite (IHC x u H1). reflexivity.
  - assert (H1 : ~ In x (fv t1)) by (apply notin_app_l with (b := context_fv C'); exact H).
    assert (H2 : ~ In x (context_fv C')) by (apply notin_app_r with (a := fv t1); exact H).
    rewrite (subst_env_gamma_plug_id x u t1 H1).
    rewrite (IHC x u H2). reflexivity.
  - f_equal. apply IHC. exact H.
  - f_equal. apply IHC. exact H.
  - f_equal. apply IHC. exact H.
  - f_equal. apply IHC. exact H.
  - assert (H1 : ~ In x (context_fv C')) by (apply notin_app3_1 with (b := fv b1) (c := fv b2); exact H).
    assert (H2 : ~ In x (fv b1)) by (apply notin_app3_2 with (a := context_fv C') (c := fv b2); exact H).
    assert (H3 : ~ In x (fv b2)) by (apply notin_app3_3 with (a := context_fv C') (b := fv b1); exact H).
    rewrite (subst_env_gamma_plug_id x u b1 H2).
    rewrite (subst_env_gamma_plug_id x u b2 H3).
    rewrite (IHC x u H1). reflexivity.
  - assert (H1 : ~ In x (fv t0)) by (apply notin_app3_1 with (b := context_fv C') (c := fv b2); exact H).
    assert (H2 : ~ In x (context_fv C')) by (apply notin_app3_2 with (a := fv t0) (c := fv b2); exact H).
    assert (H3 : ~ In x (fv b2)) by (apply notin_app3_3 with (a := fv t0) (b := context_fv C'); exact H).
    rewrite (subst_env_gamma_plug_id x u t0 H1).
    rewrite (subst_env_gamma_plug_id x u b2 H3).
    rewrite (IHC x u H2). reflexivity.
  - assert (H1 : ~ In x (fv t0)) by (apply notin_app3_1 with (b := fv b1) (c := context_fv C'); exact H).
    assert (H2 : ~ In x (fv b1)) by (apply notin_app3_2 with (a := fv t0) (c := context_fv C'); exact H).
    assert (H3 : ~ In x (context_fv C')) by (apply notin_app3_3 with (a := fv t0) (b := fv b1); exact H).
    rewrite (subst_env_gamma_plug_id x u t0 H1).
    rewrite (subst_env_gamma_plug_id x u b1 H2).
    rewrite (IHC x u H3). reflexivity.
  - f_equal. apply IHC. exact H.
  - assert (H1 : ~ In x (context_fv C')) by (apply notin_app3_1 with (b := fv y) (c := fv n); exact H).
    assert (H2 : ~ In x (fv y)) by (apply notin_app3_2 with (a := context_fv C') (c := fv n); exact H).
    assert (H3 : ~ In x (fv n)) by (apply notin_app3_3 with (a := context_fv C') (b := fv y); exact H).
    rewrite (subst_env_gamma_plug_id x u y H2).
    rewrite (subst_env_gamma_plug_id x u n H3).
    rewrite (IHC x u H1). reflexivity.
  - assert (H1 : ~ In x (fv c)) by (apply notin_app3_1 with (b := context_fv C') (c := fv n); exact H).
    assert (H2 : ~ In x (context_fv C')) by (apply notin_app3_2 with (a := fv c) (c := fv n); exact H).
    assert (H3 : ~ In x (fv n)) by (apply notin_app3_3 with (a := fv c) (b := context_fv C'); exact H).
    rewrite (subst_env_gamma_plug_id x u c H1).
    rewrite (subst_env_gamma_plug_id x u n H3).
    rewrite (IHC x u H2). reflexivity.
  - assert (H1 : ~ In x (fv c)) by (apply notin_app3_1 with (b := fv y) (c := context_fv C'); exact H).
    assert (H2 : ~ In x (fv y)) by (apply notin_app3_2 with (a := fv c) (c := context_fv C'); exact H).
    assert (H3 : ~ In x (context_fv C')) by (apply notin_app3_3 with (a := fv c) (b := fv y); exact H).
    rewrite (subst_env_gamma_plug_id x u c H1).
    rewrite (subst_env_gamma_plug_id x u y H2).
    rewrite (IHC x u H3). reflexivity.
Qed.

(* ============================================================ *)
(* Low-annotated types and adequacy                              *)
(* ============================================================ *)

Fixpoint low_annotated (T : ty) : Prop :=
  flows_to (security_of T).(indirect_reader) Low /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      low_annotated T1 /\ low_annotated T2
  end.

Lemma transparent_at_low : forall (T : ty) (kappa : security),
  transparent_at kappa T -> flows_to kappa.(indirect_reader) Low -> low_annotated T.
Proof.
  intros T. induction T as
    [ k0 | T1 IHT1 T2 IHT2 k0 | T1 IHT1 T2 IHT2 k0 | T1 IHT1 T2 IHT2 k0 ];
    intros kappa Htr Hk; simpl in *.
  - destruct Htr as [Hle _]. split; [ | exact I ].
    eapply flows_to_trans; [ exact (proj2 Hle) | exact Hk ].
  - destruct Htr as [Hle [Htr1 Htr2]]. split; [ | split ].
    + eapply flows_to_trans; [ exact (proj2 Hle) | exact Hk ].
    + apply (IHT1 kappa); assumption.
    + apply (IHT2 kappa); assumption.
  - destruct Htr as [Hle [Htr1 Htr2]]. split; [ | split ].
    + eapply flows_to_trans; [ exact (proj2 Hle) | exact Hk ].
    + apply (IHT1 kappa); assumption.
    + apply (IHT2 kappa); assumption.
  - destruct Htr as [Hle [Htr1 Htr2]]. split; [ | split ].
    + eapply flows_to_trans; [ exact (proj2 Hle) | exact Hk ].
    + apply (IHT1 kappa); assumption.
    + apply (IHT2 kappa); assumption.
Qed.

Lemma transparent_low : forall (T : ty),
  transparent T -> flows_to (security_of T).(indirect_reader) Low -> low_annotated T.
Proof.
  intros T Htr Hk. apply (transparent_at_low T (security_of T)); assumption.
Qed.

Lemma low_adequacy : forall (T : ty) (v1 v2 : tm),
  ground T -> low_annotated T ->
  W Low T (security_of T) v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  intros T. induction T as
    [ k0 | T1 IHT1 T2 IHT2 k0 | T1 IHT1 T2 IHT2 k0 | T1 IHT1 T2 IHT2 k0 ];
    intros v1 v2 Hg Hlow Hw; simpl in *.
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    destruct (Hcl (proj1 Hlow)) as (k1 & k2 & E1 & E2 & _).
    rewrite E1, E2. reflexivity.
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    destruct (proj2 Hlow) as [Hlow1 Hlow2].
    destruct (Hcl (proj1 Hlow)) as
      [[w1 [w2 [k1 [k2 [E1 [E2 [S1 [S2 HWa]]]]]]]]
      |[w1 [w2 [k1 [k2 [E1 [E2 [S1 [S2 HWa]]]]]]]]].
    + rewrite E1, E2. simpl.
      rewrite (IHT1 w1 w2 (proj1 Hg) Hlow1 HWa). reflexivity.
    + rewrite E1, E2. simpl.
      rewrite (IHT2 w1 w2 (proj2 Hg) Hlow2 HWa). reflexivity.
  - destruct Hw as [Hv1 [Hv2 Hcl]].
    destruct (proj2 Hlow) as [Hlow1 Hlow2].
    destruct (Hcl (proj1 Hlow)) as
      (a1 & b1 & a2 & b2 & k1 & k2 & E1 & E2 & S1 & S2 & Ha & Hb).
    rewrite E1, E2. simpl.
    rewrite (IHT1 a1 a2 (proj1 Hg) Hlow1 Ha).
    rewrite (IHT2 b1 b2 (proj2 Hg) Hlow2 Hb).
    reflexivity.
  - destruct Hg.
Qed.

Lemma adequacy : forall (T : ty) (v1 v2 : tm),
  ground T -> transparent T ->
  flows_to (security_of T).(indirect_reader) Low ->
  W Low T (security_of T) v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  intros T v1 v2 Hg Htr Hflow Hw.
  apply (low_adequacy T v1 v2 Hg).
  - apply (transparent_low T); assumption.
  - exact Hw.
Qed.

Lemma not_flows_to_inv : forall (a b : label),
  ~ flows_to a b -> a = High /\ b = Low.
Proof.
  intros a b H. destruct a, b; simpl in *; tauto.
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 HC Hg Htr Hno.
  destruct (not_flows_to_inv _ _ Hno) as [HIRs HIRr].
  unfold context_has_type in HC.
  destruct HC as [L HCL].
  set (x := fresh_from (L ++ context_fv C)).
  assert (Hfresh : ~ In x (L ++ context_fv C))
    by (subst x; apply fresh_from_not_in).
  assert (HxL : ~ In x L)
    by (apply notin_app_l with (b := context_fv C); exact Hfresh).
  assert (HxC : ~ In x (context_fv C))
    by (apply notin_app_r with (a := L); exact Hfresh).
  pose proof (HCL x HxL) as Hty.
  set (gamma1 := gamma_plug x t1).
  set (gamma2 := gamma_plug x t2).
  assert (Henv : env_related Low (update empty x T_secret) gamma1 gamma2).
  { split.
    - apply gamma_plug_lc.
      apply has_type_lc with (Gamma := empty) (T := T_secret). exact Ht1.
    - split.
      + apply gamma_plug_lc.
        apply has_type_lc with (Gamma := empty) (T := T_secret). exact Ht2.
      + intros z Tz Hz. unfold gamma1, gamma2.
        destruct (Nat.eqb x z) eqn:E.
        * apply Nat.eqb_eq in E. subst z.
          assert (HTz : Tz = T_secret).
          { unfold update in Hz. simpl in Hz. rewrite Nat.eqb_refl in Hz.
            injection Hz as HT. symmetry. exact HT. }
          subst Tz.
          apply LRterm_any_not_obs.
          unfold obs_sec. rewrite HIRs. simpl. intro H. exact H.
        * assert (Hz' : lookup_context z empty = Some Tz).
          { unfold update in Hz. simpl in Hz.
            destruct (Nat.eqb z x) eqn:E2.
            - apply Nat.eqb_eq in E2. exfalso. apply Nat.eqb_neq in E.
              apply E. symmetry. exact E2.
            - exact Hz. }
          simpl in Hz'. discriminate Hz'. }
  pose proof (fundamental (update empty x T_secret) (plug C (tm_fvar x)) T_result
                Hty Low gamma1 gamma2 Henv) as Hlr.
  unfold gamma1, gamma2 in Hlr.
  rewrite (subst_env_plug C x t1 HxC) in Hlr.
  rewrite (subst_env_plug C x t2 HxC) in Hlr.
  unfold same_result. intros v1 v2 Hev1 Hev2.
  unfold evaluates in Hev1, Hev2.
  destruct Hev1 as [Hm1 Hv1]. destruct Hev2 as [Hm2 Hv2].
  unfold LRterm in Hlr.
  pose proof (Hlr v1 v2 Hm1 Hv1 Hm2 Hv2) as Hw.
  apply (adequacy T_result v1 v2 Hg Htr).
  - rewrite HIRr. simpl. auto.
  - exact Hw.
Qed.
