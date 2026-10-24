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
(* Auxiliary lemmas for the noninterference proof                *)
(* ============================================================ *)

(* ---------- The label order ---------- *)

Lemma flows_to_refl : forall l, flows_to l l.
Proof. destruct l; simpl; trivial. Qed.

Lemma flows_to_trans : forall l1 l2 l3,
    flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof. destruct l1, l2, l3; simpl; auto. Qed.

Lemma flows_to_low : forall l, flows_to Low l.
Proof. destruct l; simpl; trivial. Qed.

Lemma flows_to_high : forall l, flows_to l High.
Proof. destruct l; simpl; trivial. Qed.

Lemma security_le_refl : forall k, security_le k k.
Proof. intros [r i]; simpl; split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3,
    security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3] [H1 H2] [H3 H4]; simpl in *.
  split; eapply flows_to_trans; eauto.
Qed.

Lemma security_le_ir_low : forall k1 k2,
    security_le k1 k2 -> k2.(indirect_reader) = Low -> k1.(indirect_reader) = Low.
Proof.
  intros [r1 i1] [r2 i2] [H1 H2] E; simpl in *; subst i2.
  destruct i1; simpl in H2; [reflexivity | destruct H2].
Qed.

(* ---------- Protection ---------- *)

Lemma join_low_r : forall l, join l Low = l.
Proof. destruct l; reflexivity. Qed.

Lemma protect_security_low : forall k, protect_security k Low = k.
Proof. intros [r i]; destruct r, i; reflexivity. Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof.
  intros T; destruct T; simpl;
  destruct s as [r i]; destruct r, i; reflexivity.
Qed.

Lemma protect_value_low : forall v, protect_value v Low = v.
Proof.
  intros v; destruct v; simpl;
  try reflexivity;
  destruct s as [r i]; destruct r, i; reflexivity.
Qed.

(* ---------- Fresh atoms ---------- *)

Definition fresh (L : list atom) : atom := S (fold_right max 0 L).

Lemma in_le_fold_max : forall L a, In a L -> a <= fold_right max 0 L.
Proof.
  induction L as [| b L IH]; intros a Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eassumption | apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L Hin. unfold fresh in Hin.
  pose proof (in_le_fold_max L (S (fold_right max 0 L)) Hin). lia.
Qed.

(* ---------- Substitution of all free variables ---------- *)

Fixpoint subst_all (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_unit kappa => tm_unit kappa
  | tm_abs T body kappa => tm_abs T (subst_all sigma body) kappa
  | tm_app t1 t2 r => tm_app (subst_all sigma t1) (subst_all sigma t2) r
  | tm_pair t1 t2 kappa => tm_pair (subst_all sigma t1) (subst_all sigma t2) kappa
  | tm_fst t1 r => tm_fst (subst_all sigma t1) r
  | tm_snd t1 r => tm_snd (subst_all sigma t1) r
  | tm_inl t1 kappa => tm_inl (subst_all sigma t1) kappa
  | tm_inr t1 kappa => tm_inr (subst_all sigma t1) kappa
  | tm_case t0 body1 body2 r =>
      tm_case (subst_all sigma t0) (subst_all sigma body1)
        (subst_all sigma body2) r
  | tm_protect l t1 => tm_protect l (subst_all sigma t1)
  | tm_if c yes no r =>
      tm_if (subst_all sigma c) (subst_all sigma yes) (subst_all sigma no) r
  end.

(* ---------- Locally closed terms ---------- *)

Lemma lc_at_mono : forall t k k', k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  induction t as [ n | x | s | T body IHb s | t1 IH1 t2 IH2 l
                 | t1 IH1 t2 IH2 s | t1 IH1 l | t1 IH1 l | t1 IH1 s
                 | t1 IH1 s | t0 IH0 b1 IH1 b2 IH2 l | l t1 IH1
                 | c IH1 y IH2 n IH3 l ];
  intros k k' Hle H; simpl in *.
  - lia.
  - exact I.
  - exact I.
  - apply (IHb (S k)); [lia | exact H].
  - destruct H as [H1 H2]; split.
    + apply (IH1 k k'); [lia | assumption].
    + apply (IH2 k k'); [lia | assumption].
  - destruct H as [H1 H2]; split.
    + apply (IH1 k k'); [lia | assumption].
    + apply (IH2 k k'); [lia | assumption].
  - apply (IH1 k k'); [lia | assumption].
  - apply (IH1 k k'); [lia | assumption].
  - apply (IH1 k k'); [lia | assumption].
  - apply (IH1 k k'); [lia | assumption].
  - destruct H as [H1 [H2 H3]]; split; [| split].
    + apply (IH0 k k'); [lia | assumption].
    + apply (IH1 (S k)); [lia | assumption].
    + apply (IH2 (S k)); [lia | assumption].
  - apply (IH1 k k'); [lia | assumption].
  - destruct H as [H1 [H2 H3]]; split; [| split].
    + apply (IH1 k k'); [lia | assumption].
    + apply (IH2 k k'); [lia | assumption].
    + apply (IH3 k k'); [lia | assumption].
Qed.

Lemma open_rec_lc : forall t k u, lc_at k t -> open_rec k u t = t.
Proof.
  induction t as [ n | x | s | T body IHb s | t1 IH1 t2 IH2 l
                 | t1 IH1 t2 IH2 s | t1 IH1 l | t1 IH1 l | t1 IH1 s
                 | t1 IH1 s | t0 IH0 b1 IH1 b2 IH2 l | l t1 IH1
                 | c IH1 y IH2 n IH3 l ];
  intros k u H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
  - reflexivity.
  - reflexivity.
  - simpl. f_equal. apply IHb. exact H.
  - simpl. rewrite IH1 by tauto. rewrite IH2 by tauto. reflexivity.
  - simpl. rewrite IH1 by tauto. rewrite IH2 by tauto. reflexivity.
  - simpl. rewrite IH1 by tauto. reflexivity.
  - simpl. rewrite IH1 by tauto. reflexivity.
  - simpl. rewrite IH1 by tauto. reflexivity.
  - simpl. rewrite IH1 by tauto. reflexivity.
  - simpl. rewrite IH0 by tauto. rewrite IH1 by (simpl; tauto).
    rewrite IH2 by (simpl; tauto). reflexivity.
  - simpl. rewrite IH1 by tauto. reflexivity.
  - simpl. rewrite IH1 by tauto. rewrite IH2 by tauto.
    rewrite IH3 by tauto. reflexivity.
Qed.

Lemma lc_open_rec_fvar : forall t x k,
    lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t as [ n | y | s | T body IHb s | t1 IH1 t2 IH2 l
                 | t1 IH1 t2 IH2 s | t1 IH1 l | t1 IH1 l | t1 IH1 s
                 | t1 IH1 s | t0 IH0 b1 IH1 b2 IH2 l | l t1 IH1
                 | c IH1 y IH2 n IH3 l ];
  intros x k H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl in H.
    + apply Nat.eqb_eq in E. lia.
    + lia.
  - exact I.
  - exact I.
  - apply IHb with x. exact H.
  - destruct H as [H1 H2]; split.
    + apply IH1 with x; assumption.
    + apply IH2 with x; assumption.
  - destruct H as [H1 H2]; split.
    + apply IH1 with x; assumption.
    + apply IH2 with x; assumption.
  - apply IH1 with x; assumption.
  - apply IH1 with x; assumption.
  - apply IH1 with x; assumption.
  - apply IH1 with x; assumption.
  - destruct H as [H1 [H2 H3]]; split; [| split].
    + apply IH0 with x; assumption.
    + apply IH1 with x; assumption.
    + apply IH2 with x; assumption.
  - apply IH1 with x; assumption.
  - destruct H as [H1 [H2 H3]]; split; [| split].
    + apply IH1 with x; assumption.
    + apply IH2 with x; assumption.
    + apply IH3 with x; assumption.
Qed.

(* ---------- Commutation of substitution and opening ---------- *)

Lemma subst_all_open_rec : forall body k u sigma,
    (forall y, locally_closed (sigma y)) ->
    subst_all sigma (open_rec k u body) =
    open_rec k (subst_all sigma u) (subst_all sigma body).
Proof.
  induction body as [ n | y | s | T body IHb s | t1 IH1 t2 IH2 l
                 | t1 IH1 t2 IH2 s | t1 IH1 l | t1 IH1 l | t1 IH1 s
                 | t1 IH1 s | t0 IH0 b1 IH1 b2 IH2 l | l t1 IH1
                 | c IH1 y IH2 n IH3 l ];
  intros k u sigma Hlc; simpl.
  - destruct (Nat.eqb k n) eqn:E; reflexivity.
  - symmetry. apply open_rec_lc.
    apply lc_at_mono with (k := 0); [lia | apply Hlc].
  - reflexivity.
  - simpl. f_equal. apply IHb. exact Hlc.
  - simpl. rewrite IH1 by exact Hlc. rewrite IH2 by exact Hlc. reflexivity.
  - simpl. rewrite IH1 by exact Hlc. rewrite IH2 by exact Hlc. reflexivity.
  - simpl. rewrite IH1 by exact Hlc. reflexivity.
  - simpl. rewrite IH1 by exact Hlc. reflexivity.
  - simpl. rewrite IH1 by exact Hlc. reflexivity.
  - simpl. rewrite IH1 by exact Hlc. reflexivity.
  - simpl. rewrite IH0 by exact Hlc. rewrite IH1 by exact Hlc.
    rewrite IH2 by exact Hlc. reflexivity.
  - simpl. rewrite IH1 by exact Hlc. reflexivity.
  - simpl. rewrite IH1 by exact Hlc. rewrite IH2 by exact Hlc.
    rewrite IH3 by exact Hlc. reflexivity.
Qed.

Lemma subst_all_open : forall body x sigma,
    (forall y, locally_closed (sigma y)) ->
    subst_all sigma (open body (tm_fvar x)) =
    open (subst_all sigma body) (sigma x).
Proof.
  intros. unfold open. apply subst_all_open_rec. exact H.
Qed.

Lemma subst_all_agree : forall t sigma tau,
    (forall y, In y (fv t) -> sigma y = tau y) ->
    subst_all sigma t = subst_all tau t.
Proof.
  induction t as [ n | x | s | T body IHb s | t1 IH1 t2 IH2 l
                 | t1 IH1 t2 IH2 s | t1 IH1 l | t1 IH1 l | t1 IH1 s
                 | t1 IH1 s | t0 IH0 b1 IH1 b2 IH2 l | l t1 IH1
                 | c IH1 y IH2 n IH3 l ];
  intros sigma tau H; simpl.
  - reflexivity.
  - apply H. simpl; auto.
  - reflexivity.
  - f_equal. apply IHb. intros y Hy. apply H. simpl in *. exact Hy.
  - assert (E1 : subst_all sigma t1 = subst_all tau t1).
    { apply IH1. intros y Hy. apply H. simpl. rewrite !in_app_iff. auto. }
    assert (E2 : subst_all sigma t2 = subst_all tau t2).
    { apply IH2. intros y Hy. apply H. simpl. rewrite !in_app_iff. auto. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : subst_all sigma t1 = subst_all tau t1).
    { apply IH1. intros y Hy. apply H. simpl. rewrite !in_app_iff. auto. }
    assert (E2 : subst_all sigma t2 = subst_all tau t2).
    { apply IH2. intros y Hy. apply H. simpl. rewrite !in_app_iff. auto. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : subst_all sigma t1 = subst_all tau t1).
    { apply IH1. intros y Hy. apply H. simpl. exact Hy. }
    rewrite E1. reflexivity.
  - assert (E1 : subst_all sigma t1 = subst_all tau t1).
    { apply IH1. intros y Hy. apply H. simpl. exact Hy. }
    rewrite E1. reflexivity.
  - assert (E1 : subst_all sigma t1 = subst_all tau t1).
    { apply IH1. intros y Hy. apply H. simpl. exact Hy. }
    rewrite E1. reflexivity.
  - assert (E1 : subst_all sigma t1 = subst_all tau t1).
    { apply IH1. intros y Hy. apply H. simpl. exact Hy. }
    rewrite E1. reflexivity.
  - assert (E1 : subst_all sigma t0 = subst_all tau t0).
    { apply IH0. intros y Hy. apply H. simpl. rewrite !in_app_iff. auto. }
    assert (E2 : subst_all sigma b1 = subst_all tau b1).
    { apply IH1. intros y Hy. apply H. simpl. rewrite !in_app_iff. auto. }
    assert (E3 : subst_all sigma b2 = subst_all tau b2).
    { apply IH2. intros y Hy. apply H. simpl. rewrite !in_app_iff. auto. }
    rewrite E1, E2, E3. reflexivity.
  - assert (E1 : subst_all sigma t1 = subst_all tau t1).
    { apply IH1. intros y Hy. apply H. simpl. exact Hy. }
    rewrite E1. reflexivity.
  - assert (E1 : subst_all sigma c = subst_all tau c).
    { apply IH1. intros y0 Hy. apply H. simpl. rewrite !in_app_iff. auto. }
    assert (E2 : subst_all sigma y = subst_all tau y).
    { apply IH2. intros y0 Hy. apply H. simpl. rewrite !in_app_iff. auto. }
    assert (E3 : subst_all sigma n = subst_all tau n).
    { apply IH3. intros y0 Hy. apply H. simpl. rewrite !in_app_iff. auto. }
    rewrite E1, E2, E3. reflexivity.
Qed.

Lemma subst_all_fvar_self : forall t x u,
    ~ In x (fv t) ->
    subst_all (fun y => if Nat.eqb y x then u else tm_fvar y) t = t.
Proof.
  induction t as [ n | a | s | T body IHb s | t1 IH1 t2 IH2 l
                 | t1 IH1 t2 IH2 s | t1 IH1 l | t1 IH1 l | t1 IH1 s
                 | t1 IH1 s | t0 IH0 b1 IH1 b2 IH2 l | l t1 IH1
                 | c IH1 y IH2 n IH3 l ];
  intros x u Hx; simpl.
  - reflexivity.
  - destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hx. simpl; auto.
    + reflexivity.
  - reflexivity.
  - f_equal. apply IHb. simpl in Hx. exact Hx.
  - rewrite IH1 by (simpl in Hx; intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite IH2 by (simpl in Hx; intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
  - rewrite IH1 by (simpl in Hx; intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite IH2 by (simpl in Hx; intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
  - rewrite IH1 by (simpl in Hx; exact Hx). reflexivity.
  - rewrite IH1 by (simpl in Hx; exact Hx). reflexivity.
  - rewrite IH1 by (simpl in Hx; exact Hx). reflexivity.
  - rewrite IH1 by (simpl in Hx; exact Hx). reflexivity.
  - rewrite IH0 by (simpl in Hx; intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite IH1 by (simpl in Hx; intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite IH2 by (simpl in Hx; intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
  - rewrite IH1 by (simpl in Hx; exact Hx). reflexivity.
  - rewrite IH1 by (simpl in Hx; intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite IH2 by (simpl in Hx; intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite IH3 by (simpl in Hx; intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
Qed.

Lemma subst_all_unit : forall sigma, subst_all sigma (tm_unit public) = tm_unit public.
Proof. reflexivity. Qed.

(* ---------- Values ---------- *)

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv; simpl.
  - exact I.
  - assumption.
  - split; assumption.
  - assumption.
  - assumption.
Qed.

Lemma value_no_step : forall v, value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv. induction Hv; intros t' Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    + eapply IHHv1; eassumption.
    + eapply IHHv2; eassumption.
  - inversion Hstep; subst.
    eapply IHHv; eassumption.
  - inversion Hstep; subst.
    eapply IHHv; eassumption.
Qed.

Lemma multi_value_eq : forall t v, multi t v -> value t -> v = t.
Proof.
  intros t v Hm. induction Hm; intros Hv.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma evaluates_value_eq : forall v u, value v -> evaluates v u -> u = v.
Proof.
  intros v u Hv [Hm _]. apply multi_value_eq with (t := v); assumption.
Qed.

Lemma evaluates_value : forall v, value v -> evaluates v v.
Proof. intros v Hv; split; [apply multi_refl | exact Hv]. Qed.

(* ---------- Typing implies local closedness ---------- *)

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H. induction H; unfold locally_closed; simpl.
  - exact I.
  - exact I.
  - match goal with
    | Hpre : forall x : atom, ~ In x ?L -> _ |- _ =>
        pose proof (fresh_not_in L) as Hx;
        apply lc_open_rec_fvar with (x := fresh L) (k := 0);
        match goal with
        | IH : forall y : atom, ~ In y ?L2 -> locally_closed (open ?b (tm_fvar y)) |- _ =>
            unfold locally_closed, open in IH;
            unfold locally_closed, open;
            apply (IH (fresh L) Hx)
        end
    end.
  - split; assumption.
  - split; assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - split; [assumption | split].
    + match goal with
      | Hpre : forall x : atom, ~ In x ?L -> _ |- _ =>
          pose proof (fresh_not_in L) as Hx;
          apply lc_open_rec_fvar with (x := fresh L) (k := 0);
          match goal with
          | IH : forall y : atom, ~ In y ?L2 -> locally_closed (open ?b (tm_fvar y)) |- _ =>
              unfold locally_closed, open in IH;
              unfold locally_closed, open;
              apply (IH (fresh L) Hx)
          end
      end.
    + match goal with
      | Hpre : forall x : atom, ~ In x ?L -> _ |- _ =>
          pose proof (fresh_not_in L) as Hx;
          apply lc_open_rec_fvar with (x := fresh L) (k := 0);
          match goal with
          | IH : forall y : atom, ~ In y ?L2 -> locally_closed (open ?b (tm_fvar y)) |- _ =>
              unfold locally_closed, open in IH;
              unfold locally_closed, open;
              apply (IH (fresh L) Hx)
          end
      end.
  - assumption.
  - assumption.
  - split; [assumption | split; assumption].
Qed.

(* ---------- The logical relation ---------- *)

Fixpoint RV (T : ty) (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_Unit kappa =>
      match kappa.(indirect_reader) with
      | High => True
      | Low =>
          (exists ka1, v1 = tm_unit ka1) /\ (exists ka2, v2 = tm_unit ka2)
      end
  | Ty_Sum T1 T2 kappa =>
      match kappa.(indirect_reader) with
      | High => True
      | Low =>
          (exists a1 ka1 a2 ka2,
              v1 = tm_inl a1 ka1 /\ v2 = tm_inl a2 ka2 /\
              ka1.(indirect_reader) = Low /\ ka2.(indirect_reader) = Low /\
              RV T1 a1 a2)
          \/
          (exists a1 ka1 a2 ka2,
              v1 = tm_inr a1 ka1 /\ v2 = tm_inr a2 ka2 /\
              ka1.(indirect_reader) = Low /\ ka2.(indirect_reader) = Low /\
              RV T2 a1 a2)
      end
  | Ty_Prod T1 T2 kappa =>
      match kappa.(indirect_reader) with
      | High => True
      | Low =>
          exists a1 b1 ka1 a2 b2 ka2,
              v1 = tm_pair a1 b1 ka1 /\ v2 = tm_pair a2 b2 ka2 /\
              ka1.(indirect_reader) = Low /\ ka2.(indirect_reader) = Low /\
              RV T1 a1 a2 /\ RV T2 b1 b2
      end
  | Ty_Arrow T1 T2 kappa =>
      match kappa.(indirect_reader) with
      | High => True
      | Low =>
          exists T1a b1 ka1 T1b b2 ka2,
              v1 = tm_abs T1a b1 ka1 /\ v2 = tm_abs T1b b2 ka2 /\
              ka1.(indirect_reader) = Low /\ ka2.(indirect_reader) = Low /\
              (forall a1 a2, value a1 -> value a2 -> RV T1 a1 a2 ->
                  forall u1 u2, evaluates (open b1 a1) u1 ->
                                evaluates (open b2 a2) u2 -> RV T2 u1 u2)
      end
  end.

Definition R (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, evaluates t1 v1 -> evaluates t2 v2 -> RV T v1 v2.

Lemma RV_high : forall T v1 v2,
    (security_of T).(indirect_reader) = High -> RV T v1 v2.
Proof.
  intros T v1 v2 H.
  destruct T as [k | T1 T2 k | T1 T2 k | T1 T2 k]; simpl in H; simpl;
  destruct k as [r i]; simpl in *; subst i; simpl; exact I.
Qed.

Lemma R_weak : forall T,
    (security_of T).(indirect_reader) = High -> forall t1 t2, R T t1 t2.
Proof.
  intros T H t1 t2 v1 v2 E1 E2. apply RV_high. exact H.
Qed.

(* Subtyping is antitone with respect to observability: the subtype
   has lower security annotations, hence a stronger relation. *)

Lemma RV_subtype : forall T U, subtype T U -> forall v1 v2, RV T v1 v2 -> RV U v1 v2.
Proof.
  intros T U Hsub.
  induction Hsub as [ kappa1 kappa2 Hw1 Hw2 Hle
                   | T1 T2 U1 U2 kappa1 kappa2 Hp1 IH1 Hp2 IH2 Hw1 Hw2 Hle
                   | T1 T2 U1 U2 kappa1 kappa2 Hp1 IH1 Hp2 IH2 Hw1 Hw2 Hle
                   | T1 T2 U1 U2 kappa1 kappa2 Hp1 IH1 Hp2 IH2 Hw1 Hw2 Hle
                   | T U V Hp1 IH1 Hp2 IH2 ];
  intros v1 v2 H.
  - (* S_Unit *)
    destruct kappa2 as [r2 i2]; destruct i2; simpl.
    + assert (Hi : kappa1.(indirect_reader) = Low).
      { match goal with Hle' : security_le kappa1 _ |- _ =>
          apply (security_le_ir_low kappa1 _ Hle'); reflexivity end. }
      destruct kappa1 as [r1 i1]; simpl in Hi; subst i1; simpl in H.
      exact H.
    + exact I.
  - (* S_Sum *)
    destruct kappa2 as [r2 i2]; destruct i2; simpl.
    + assert (Hi : kappa1.(indirect_reader) = Low).
      { match goal with Hle' : security_le kappa1 _ |- _ =>
          apply (security_le_ir_low kappa1 _ Hle'); reflexivity end. }
      destruct kappa1 as [r1 i1]; simpl in Hi; subst i1; simpl in H.
      destruct H as [Hinl | Hinr].
      * destruct Hinl as (a1 & ka1 & a2 & ka2 & Eq1 & Eq2 & Hk1 & Hk2 & Hpay).
        left. exists a1, ka1, a2, ka2. repeat split; auto.
      * destruct Hinr as (a1 & ka1 & a2 & ka2 & Eq1 & Eq2 & Hk1 & Hk2 & Hpay).
        right. exists a1, ka1, a2, ka2. repeat split; auto.
    + exact I.
  - (* S_Prod *)
    destruct kappa2 as [r2 i2]; destruct i2; simpl.
    + assert (Hi : kappa1.(indirect_reader) = Low).
      { match goal with Hle' : security_le kappa1 _ |- _ =>
          apply (security_le_ir_low kappa1 _ Hle'); reflexivity end. }
      destruct kappa1 as [r1 i1]; simpl in Hi; subst i1; simpl in H.
      destruct H as (a1 & b1 & ka1 & a2 & b2 & ka2 & Eq1 & Eq2 & Hk1 & Hk2 & Hpay1 & Hpay2).
      exists a1, b1, ka1, a2, b2, ka2. repeat split; auto.
    + exact I.
  - (* S_Arrow *)
    destruct kappa2 as [r2 i2]; destruct i2; simpl.
    + assert (Hi : kappa1.(indirect_reader) = Low).
      { match goal with Hle' : security_le kappa1 _ |- _ =>
          apply (security_le_ir_low kappa1 _ Hle'); reflexivity end. }
      destruct kappa1 as [r1 i1]; simpl in Hi; subst i1; simpl in H.
      destruct H as (T1a & b1 & ka1 & T1b & b2 & ka2 & Eq1 & Eq2 & Hk1 & Hk2 & Hbeh).
      exists T1a, b1, ka1, T1b, b2, ka2. repeat split; try auto.
      intros a1 a2 Hv1 Hv2 Hrel u1 u2 Eu1 Eu2.
      apply IH2.
      apply (Hbeh a1 a2).
      * exact Hv1.
      * exact Hv2.
      * apply IH1. exact Hrel.
      * exact Eu1.
      * exact Eu2.
    + exact I.
  - (* S_Trans *)
    apply IH2. apply IH1. exact H.
Qed.

Lemma R_subtype : forall T U, subtype T U -> forall t1 t2, R T t1 t2 -> R U t1 t2.
Proof.
  intros T U Hsub t1 t2 H v1 v2 E1 E2.
  apply (RV_subtype T U Hsub v1 v2).
  exact (H v1 v2 E1 E2).
Qed.

(* ---------- Protection by Low ---------- *)

Lemma multi_trans : forall a b c, multi a b -> multi b c -> multi a c.
Proof.
  intros a b c Hab Hbc. induction Hab.
  - exact Hbc.
  - eapply multi_step; [eassumption | apply IHHab; exact Hbc].
Qed.

Lemma multi_protect : forall l t u, multi t u -> multi (tm_protect l t) (tm_protect l u).
Proof.
  intros l t u Hm. induction Hm.
  - apply multi_refl.
  - eapply multi_step; [apply ST_Protect; eassumption | exact IHHm].
Qed.

Lemma value_protect_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv. induction Hv; simpl.
  - apply v_unit.
  - apply v_abs. assumption.
  - apply v_pair; assumption.
  - apply v_inl. assumption.
  - apply v_inr. assumption.
Qed.

Lemma ev_protect : forall l t v,
    evaluates (tm_protect l t) v ->
    exists u, evaluates t u /\ v = protect_value u l.
Proof.
  intros l t v [Hm Hv].
  remember (tm_protect l t) as s eqn:E.
  revert l t E.
  induction Hm; intros l0 t0 E.
  - rewrite E in Hv. inversion Hv.
  - subst. inversion H; subst; clear H.
    + exists t0. split.
      * apply evaluates_value. assumption.
      * apply multi_value_eq with (t := protect_value t0 l0).
        -- assumption.
        -- apply value_protect_value. assumption.
    + destruct (IHHm Hv l0 t' eq_refl) as (u & Eu & Ev).
      exists u. split; [|exact Ev].
      destruct Eu as [Hmu Hvu]. split.
      * eapply multi_step; [exact H3 | exact Hmu].
      * exact Hvu.
Qed.

Lemma ev_protect_low_iff : forall t v,
    evaluates (tm_protect Low t) v <-> evaluates t v.
Proof.
  intros t v; split.
  - intros H. destruct (ev_protect Low t v H) as (u & Eu & Ev).
    rewrite protect_value_low in Ev. subst v. exact Eu.
  - intros [Hm Hv]. split; [|exact Hv].
    eapply multi_trans.
    + apply multi_protect. exact Hm.
    + eapply multi_step.
      * apply ST_ProtectValue. exact Hv.
      * rewrite protect_value_low. apply multi_refl.
Qed.

Lemma R_protect_low : forall T t1 t2,
    R T t1 t2 -> R T (tm_protect Low t1) (tm_protect Low t2).
Proof.
  intros T t1 t2 H v1 v2 E1 E2.
  apply (H v1 v2).
  - apply ev_protect_low_iff. exact E1.
  - apply ev_protect_low_iff. exact E2.
Qed.

Lemma R_protect_low_inv : forall T t1 t2,
    R T (tm_protect Low t1) (tm_protect Low t2) -> R T t1 t2.
Proof.
  intros T t1 t2 H v1 v2 E1 E2.
  apply H.
  - apply ev_protect_low_iff. exact E1.
  - apply ev_protect_low_iff. exact E2.
Qed.

(* ---------- Decomposition of evaluations ---------- *)

Lemma ev_app : forall t1 t2 r v,
    evaluates (tm_app t1 t2 r) v ->
    exists w1 a, evaluates t1 w1 /\ evaluates t2 a /\
      exists T1a body ka, w1 = tm_abs T1a body ka /\
        evaluates (tm_protect ka.(indirect_reader) (open body a)) v.
Proof.
  intros t1 t2 r v [Hm Hv].
  remember (tm_app t1 t2 r) as s eqn:E.
  revert t1 t2 r E.
  induction Hm; intros x1 x2 r0 E.
  - subst. inversion Hv.
  - subst. inversion H; subst; clear H.
    + exists (tm_abs T body kappa), x2. split.
      * apply evaluates_value. assumption.
      * split.
        -- apply evaluates_value. assumption.
        -- exists T, body, kappa. split; [reflexivity | split; assumption].
    + destruct (IHHm Hv t1' x2 r0 eq_refl)
        as (w1 & a & E1 & E2 & T1a & body & ka & Eq & E3).
      exists w1, a. split.
      * destruct E1 as [Hmu Hvu]. split.
        -- eapply multi_step; [exact H4 | exact Hmu].
        -- exact Hvu.
      * split; [exact E2 |].
        exists T1a, body, ka. split; [exact Eq | exact E3].
    + destruct (IHHm Hv x1 t2' r0 eq_refl)
        as (w1 & a & E1 & E2 & T1a & body & ka & Eq & E3).
      exists w1, a. split.
      * exact E1.
      * split.
        -- destruct E2 as [Hmu Hvu]. split.
           ++ eapply multi_step; [exact H5 | exact Hmu].
           ++ exact Hvu.
        -- exists T1a, body, ka. split; [exact Eq | exact E3].
Qed.

Lemma ev_pair : forall a b ka v,
    evaluates (tm_pair a b ka) v ->
    exists v1 v2, evaluates a v1 /\ evaluates b v2 /\ v = tm_pair v1 v2 ka.
Proof.
  intros a b ka v [Hm Hv].
  remember (tm_pair a b ka) as s eqn:E.
  revert a b ka E.
  induction Hm; intros a b ka E.
  - subst. inversion Hv; subst.
    exists a, b. split.
    + apply evaluates_value. exact H1.
    + split.
      * apply evaluates_value. exact H3.
      * reflexivity.
  - subst. inversion H; subst; clear H.
    + destruct (IHHm Hv t1' b ka eq_refl) as (v1 & v2 & E1 & E2 & Ev).
      exists v1, v2. split; [|split].
      * destruct E1 as [Hmu Hvu]. split.
        -- eapply multi_step; [exact H4 | exact Hmu].
        -- exact Hvu.
      * exact E2.
      * exact Ev.
    + destruct (IHHm Hv a t2' ka eq_refl) as (v1 & v2 & E1 & E2 & Ev).
      exists v1, v2. split; [|split].
      * exact E1.
      * destruct E2 as [Hmu Hvu]. split.
        -- eapply multi_step; [exact H5 | exact Hmu].
        -- exact Hvu.
      * exact Ev.
Qed.

Lemma ev_inl : forall a ka v,
    evaluates (tm_inl a ka) v ->
    exists v1, evaluates a v1 /\ v = tm_inl v1 ka.
Proof.
  intros a ka v [Hm Hv].
  remember (tm_inl a ka) as s eqn:E.
  revert a ka E.
  induction Hm; intros a ka E.
  - subst. inversion Hv; subst.
    exists a. split; [apply evaluates_value; assumption | reflexivity].
  - subst. inversion H; subst; clear H.
    destruct (IHHm Hv t' ka eq_refl) as (v1 & E1 & Ev).
    exists v1. split; [|exact Ev].
    destruct E1 as [Hmu Hvu]. split.
    * eapply multi_step; [exact H3 | exact Hmu].
    * exact Hvu.
Qed.

Lemma ev_inr : forall a ka v,
    evaluates (tm_inr a ka) v ->
    exists v1, evaluates a v1 /\ v = tm_inr v1 ka.
Proof.
  intros a ka v [Hm Hv].
  remember (tm_inr a ka) as s eqn:E.
  revert a ka E.
  induction Hm; intros a ka E.
  - subst. inversion Hv; subst.
    exists a. split; [apply evaluates_value; assumption | reflexivity].
  - subst. inversion H; subst; clear H.
    destruct (IHHm Hv t' ka eq_refl) as (v1 & E1 & Ev).
    exists v1. split; [|exact Ev].
    destruct E1 as [Hmu Hvu]. split.
    * eapply multi_step; [exact H3 | exact Hmu].
    * exact Hvu.
Qed.

Lemma ev_fst : forall a r v,
    evaluates (tm_fst a r) v ->
    exists v1 v2 ka, evaluates a (tm_pair v1 v2 ka) /\
      evaluates (tm_protect ka.(indirect_reader) v1) v.
Proof.
  intros a r v [Hm Hv].
  remember (tm_fst a r) as s eqn:E.
  revert a r E.
  induction Hm; intros a r E.
  - subst. inversion Hv.
  - subst. inversion H; subst; clear H.
    + exists v1, v2, kappa. split.
      * apply evaluates_value. apply v_pair; assumption.
      * split; assumption.
    + destruct (IHHm Hv t' r eq_refl) as (v1 & v2 & ka & E1 & E2).
      exists v1, v2, ka. split; [|exact E2].
      destruct E1 as [Hmu Hvu]. split.
      * eapply multi_step; [exact H3 | exact Hmu].
      * exact Hvu.
Qed.

Lemma ev_snd : forall a r v,
    evaluates (tm_snd a r) v ->
    exists v1 v2 ka, evaluates a (tm_pair v1 v2 ka) /\
      evaluates (tm_protect ka.(indirect_reader) v2) v.
Proof.
  intros a r v [Hm Hv].
  remember (tm_snd a r) as s eqn:E.
  revert a r E.
  induction Hm; intros a r E.
  - subst. inversion Hv.
  - subst. inversion H; subst; clear H.
    + exists v1, v2, kappa. split.
      * apply evaluates_value. apply v_pair; assumption.
      * split; assumption.
    + destruct (IHHm Hv t' r eq_refl) as (v1 & v2 & ka & E1 & E2).
      exists v1, v2, ka. split; [|exact E2].
      destruct E1 as [Hmu Hvu]. split.
      * eapply multi_step; [exact H3 | exact Hmu].
      * exact Hvu.
Qed.

Lemma ev_case : forall a b1 b2 r v,
    evaluates (tm_case a b1 b2 r) v ->
    (exists u ka, evaluates a (tm_inl u ka) /\
        evaluates (tm_protect ka.(indirect_reader) (open b1 u)) v) \/
    (exists u ka, evaluates a (tm_inr u ka) /\
        evaluates (tm_protect ka.(indirect_reader) (open b2 u)) v).
Proof.
  intros a b1 b2 r v [Hm Hv].
  remember (tm_case a b1 b2 r) as s eqn:E.
  revert a b1 b2 r E.
  induction Hm; intros a b1 b2 r E.
  - subst. inversion Hv.
  - subst. inversion H; subst; clear H.
    + left. exists v, kappa. split.
      * apply evaluates_value. apply v_inl. exact H5.
      * split; assumption.
    + right. exists v, kappa. split.
      * apply evaluates_value. apply v_inr. exact H5.
      * split; assumption.
    + destruct (IHHm Hv t' b1 b2 r eq_refl)
        as [(u & ka & E1 & E2) | (u & ka & E1 & E2)].
      * left. exists u, ka. split; [|exact E2].
        destruct E1 as [Hmu Hvu]. split.
        -- eapply multi_step; [exact H5 | exact Hmu].
        -- exact Hvu.
      * right. exists u, ka. split; [|exact E2].
        destruct E1 as [Hmu Hvu]. split.
        -- eapply multi_step; [exact H5 | exact Hmu].
        -- exact Hvu.
Qed.

Lemma ev_if : forall c y n r v,
    evaluates (tm_if c y n r) v ->
    (exists u ka, evaluates c (tm_inl u ka) /\
        evaluates (tm_protect ka.(indirect_reader) y) v) \/
    (exists u ka, evaluates c (tm_inr u ka) /\
        evaluates (tm_protect ka.(indirect_reader) n) v).
Proof.
  intros c y n r v [Hm Hv].
  remember (tm_if c y n r) as s eqn:E.
  revert c y n r E.
  induction Hm; intros c y n r E.
  - subst. inversion Hv.
  - subst. inversion H; subst; clear H.
    + destruct (IHHm Hv c' y n r eq_refl)
        as [(u & ka & E1 & E2) | (u & ka & E1 & E2)].
      * left. exists u, ka. split; [|exact E2].
        destruct E1 as [Hmu Hvu]. split.
        -- eapply multi_step; [exact H5 | exact Hmu].
        -- exact Hvu.
      * right. exists u, ka. split; [|exact E2].
        destruct E1 as [Hmu Hvu]. split.
        -- eapply multi_step; [exact H5 | exact Hmu].
        -- exact Hvu.
    + left. exists v, k. split.
      * apply evaluates_value. apply v_inl. assumption.
      * split; assumption.
    + right. exists v, k. split.
      * apply evaluates_value. apply v_inr. assumption.
      * split; assumption.
Qed.

(* ---------- Environment machinery for the fundamental theorem ---------- *)

Lemma lookup_context_update_eq : forall Gamma x T,
    lookup_context x (update Gamma x T) = Some T.
Proof.
  intros Gamma x T. unfold update. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_context_update_neq : forall Gamma x y T,
    y <> x -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T H. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma join_high_r : forall l, join l High = High.
Proof. destruct l; reflexivity. Qed.

Lemma security_of_ty_protect : forall l T,
    security_of (ty_protect l T) = protect_security (security_of T) l.
Proof. intros l T; destruct T; reflexivity. Qed.

Lemma protect_security_ir : forall kappa l,
    (protect_security kappa l).(indirect_reader) = join kappa.(indirect_reader) l.
Proof. intros [r i] l; reflexivity. Qed.

Lemma protect_security_reader : forall kappa l,
    (protect_security kappa l).(reader) = join kappa.(reader) l.
Proof. intros [r i] l; reflexivity. Qed.

Lemma abs_no_step : forall T body kappa t, ~ (tm_abs T body kappa --> t).
Proof. intros; inversion 1. Qed.

Lemma unit_no_step : forall kappa t, ~ (tm_unit kappa --> t).
Proof. intros; inversion 1. Qed.

Lemma multi_abs_eq : forall T body kappa v,
    multi (tm_abs T body kappa) v -> v = tm_abs T body kappa.
Proof.
  intros T body kappa v Hm.
  remember (tm_abs T body kappa) as s eqn:E.
  revert T body kappa E.
  induction Hm; intros T0 body0 kappa0 E.
  - subst. reflexivity.
  - subst. exfalso. eapply abs_no_step. eassumption.
Qed.

Lemma multi_unit_eq : forall kappa v,
    multi (tm_unit kappa) v -> v = tm_unit kappa.
Proof.
  intros kappa v Hm.
  remember (tm_unit kappa) as s eqn:E.
  revert kappa E.
  induction Hm; intros kappa0 E.
  - subst. reflexivity.
  - subst. exfalso. eapply unit_no_step. eassumption.
Qed.

Lemma R_of_RV : forall T v1 v2,
    value v1 -> value v2 -> RV T v1 v2 -> R T v1 v2.
Proof.
  intros T v1 v2 Hv1 Hv2 HRV w1 w2 E1 E2.
  destruct E1 as [Hm1 _]. destruct E2 as [Hm2 _].
  assert (H1 : w1 = v1) by (apply multi_value_eq with (t := v1); assumption).
  assert (H2 : w2 = v2) by (apply multi_value_eq with (t := v2); assumption).
  subst w1. subst w2. exact HRV.
Qed.

Definition extend (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else sigma y.

Lemma extend_eq : forall sigma x u, extend sigma x u x = u.
Proof. intros. unfold extend. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_neq : forall sigma x u y, y <> x -> extend sigma x u y = sigma y.
Proof.
  intros sigma x u y H. unfold extend.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma extend_lc : forall sigma x u,
    (forall y, locally_closed (sigma y)) -> locally_closed u ->
    forall y, locally_closed (extend sigma x u y).
Proof.
  intros sigma x u Hsig Hu y. unfold extend.
  destruct (Nat.eqb y x).
  - exact Hu.
  - apply Hsig.
Qed.

Lemma extend_agree : forall sigma x u t,
    ~ In x (fv t) -> subst_all (extend sigma x u) t = subst_all sigma t.
Proof.
  intros sigma x u t Hx. apply subst_all_agree.
  intros y Hy. apply extend_neq.
  intro E. subst y. apply Hx. exact Hy.
Qed.

Lemma subst_all_open_extend : forall body x sigma u,
    (forall y, locally_closed (sigma y)) ->
    locally_closed u ->
    ~ In x (fv body) ->
    subst_all (extend sigma x u) (open body (tm_fvar x)) =
    open (subst_all sigma body) u.
Proof.
  intros body x sigma u Hlc Hu Hx.
  rewrite subst_all_open.
  - rewrite extend_eq. rewrite extend_agree; [reflexivity | exact Hx].
  - apply extend_lc; assumption.
Qed.

Definition env_rel (Gamma : context) (sigma1 sigma2 : atom -> tm) : Prop :=
  (forall y, locally_closed (sigma1 y)) /\
  (forall y, locally_closed (sigma2 y)) /\
  (forall x T, lookup_context x Gamma = Some T -> R T (sigma1 x) (sigma2 x)).

Lemma env_rel_lc1 : forall Gamma sigma1 sigma2,
    env_rel Gamma sigma1 sigma2 -> forall y, locally_closed (sigma1 y).
Proof. intros Gamma s1 s2 [H1 _]; exact H1. Qed.

Lemma env_rel_lc2 : forall Gamma sigma1 sigma2,
    env_rel Gamma sigma1 sigma2 -> forall y, locally_closed (sigma2 y).
Proof. intros Gamma s1 s2 [_ [H2 _]]; exact H2. Qed.

Lemma env_rel_R : forall Gamma sigma1 sigma2 x T,
    env_rel Gamma sigma1 sigma2 -> lookup_context x Gamma = Some T ->
    R T (sigma1 x) (sigma2 x).
Proof. intros Gamma s1 s2 x T [_ [_ H]] Hlook. exact (H x T Hlook). Qed.

Lemma env_rel_extend : forall Gamma sigma1 sigma2 x T a1 a2,
    env_rel Gamma sigma1 sigma2 ->
    value a1 -> value a2 -> RV T a1 a2 ->
    env_rel (update Gamma x T) (extend sigma1 x a1) (extend sigma2 x a2).
Proof.
  intros Gamma sigma1 sigma2 x T a1 a2 [Hlc1 [Hlc2 Hrel]] Hv1 Hv2 HRV.
  split; [|split].
  - apply extend_lc; [exact Hlc1 | apply value_lc; exact Hv1].
  - apply extend_lc; [exact Hlc2 | apply value_lc; exact Hv2].
  - intros y U Hy. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y.
      assert (HU : U = T).
      { rewrite lookup_context_update_eq in Hy. injection Hy. auto. }
      subst U. rewrite extend_eq, extend_eq.
      apply R_of_RV; assumption.
    + apply Nat.eqb_neq in E.
      rewrite lookup_context_update_neq in Hy by exact E.
      rewrite extend_neq by exact E. rewrite extend_neq by exact E.
      apply Hrel. exact Hy.
Qed.

(* ---------- Fundamental theorem ---------- *)

Lemma value_pair_inv : forall a b k, value (tm_pair a b k) -> value a /\ value b.
Proof. intros; inversion H; auto. Qed.

Lemma value_inl_inv : forall a k, value (tm_inl a k) -> value a.
Proof. intros; inversion H; auto. Qed.

Lemma value_inr_inv : forall a k, value (tm_inr a k) -> value a.
Proof. intros; inversion H; auto. Qed.

Lemma fundamental : forall Gamma t T,
    has_type Gamma t T ->
    forall sigma1 sigma2, env_rel Gamma sigma1 sigma2 ->
    R T (subst_all sigma1 t) (subst_all sigma2 t).
Proof.
  intros Gamma t T H.
  induction H as [ Gamma x T0 Hlook Hwf
                 | Gamma kappa Hwf
                 | L Gamma T1 body T2 kappa HwfT Hwfk Hprem IHprem
                 | Gamma t1 t2 T1 T2 kappa r H1 IH1 H2 IH2 Hflow
                 | Gamma t1 t2 T1 T2 kappa H1 IH1 H2 IH2 Hwfk
                 | Gamma t T1 T2 kappa r H1 IH1 Hflow
                 | Gamma t T1 T2 kappa r H1 IH1 Hflow
                 | Gamma t T1 T2 kappa H1 IH1 HwfT2 Hwfk
                 | Gamma t T1 T2 kappa HwfT1 H2 IH2 Hwfk
                 | L Gamma t body1 body2 T1 T2 T0 kappa r Ht IHt Hflow Hp1 IHp1 Hp2 IHp2
                 | Gamma t T0 l H1 IH1
                 | Gamma t T0 U H1 IH1 Hsub
                 | Gamma c yes no k T0 r Hc IHc Hy IHy Hn IHn Hflow ];
  intros sigma1 sigma2 Henv.
  - (* T_Var *)
    simpl. apply (env_rel_R Gamma sigma1 sigma2 x T0 Henv Hlook).
  - (* T_Unit *)
    simpl. intros v1 v2 E1 E2.
    destruct E1 as [Hm1 Hval1]. destruct E2 as [Hm2 Hval2].
    assert (Ev1 : v1 = tm_unit kappa) by (apply multi_unit_eq; exact Hm1).
    assert (Ev2 : v2 = tm_unit kappa) by (apply multi_unit_eq; exact Hm2).
    subst v1. subst v2.
    destruct kappa as [rr ii]. destruct ii; simpl.
    + split; eexists; reflexivity.
    + exact I.
  - (* T_Abs *)
    simpl. intros v1 v2 E1 E2.
    destruct E1 as [Hm1 Hval1]. destruct E2 as [Hm2 Hval2].
    assert (Ev1 : v1 = tm_abs T1 (subst_all sigma1 body) kappa)
      by (apply multi_abs_eq; exact Hm1).
    assert (Ev2 : v2 = tm_abs T1 (subst_all sigma2 body) kappa)
      by (apply multi_abs_eq; exact Hm2).
    subst v1. subst v2.
    destruct kappa as [rr ii]. destruct ii; simpl.
    + exists T1, (subst_all sigma1 body), {| reader := rr; indirect_reader := Low |},
             T1, (subst_all sigma2 body), {| reader := rr; indirect_reader := Low |}.
      split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity |]]]].
      intros a1 a2 Hva1 Hva2 HRV u1 u2 Eu1 Eu2.
      set (Hlc1 := env_rel_lc1 Gamma sigma1 sigma2 Henv).
      set (Hlc2 := env_rel_lc2 Gamma sigma1 sigma2 Henv).
      set (xx := fresh (L ++ fv body)).
      assert (HxL : ~ In xx L).
      { intro Hc. apply (fresh_not_in (L ++ fv body)). apply in_or_app. left. exact Hc. }
      assert (HxB : ~ In xx (fv body)).
      { intro Hc. apply (fresh_not_in (L ++ fv body)). apply in_or_app. right. exact Hc. }
      assert (Henv' : env_rel (update Gamma xx T1)
                         (extend sigma1 xx a1) (extend sigma2 xx a2)).
      { apply env_rel_extend; [exact Henv | exact Hva1 | exact Hva2 | exact HRV]. }
      pose proof (IHprem xx HxL (extend sigma1 xx a1) (extend sigma2 xx a2) Henv')
        as Hbody.
      pose proof (subst_all_open_extend body xx sigma1 a1 Hlc1 (value_lc a1 Hva1) HxB) as Heq1.
      rewrite Heq1 in Hbody.
      pose proof (subst_all_open_extend body xx sigma2 a2 Hlc2 (value_lc a2 Hva2) HxB) as Heq2.
      rewrite Heq2 in Hbody.
      exact (Hbody u1 u2 Eu1 Eu2).
    + exact I.
  - (* T_App *)
    simpl. intros v1 v2 E1 E2.
    destruct kappa as [rr ii]. destruct ii; simpl.
    + rewrite ty_protect_low.
      destruct (ev_app (subst_all sigma1 t1) (subst_all sigma1 t2) r v1 E1)
        as (w1 & a1 & Ef1 & Ea1 & T1a & body1 & ka1 & Eq1 & Er1).
      destruct (ev_app (subst_all sigma2 t1) (subst_all sigma2 t2) r v2 E2)
        as (w2 & a2 & Ef2 & Ea2 & T1b & body2 & ka2 & Eq2 & Er2).
      destruct (IH1 sigma1 sigma2 Henv w1 w2 Ef1 Ef2)
        as (T1a' & b1 & ka1' & T1b' & b2 & ka2' & Eqw1 & Eqw2 & Hk1 & Hk2 & Hbeh).
      rewrite Eqw1 in Eq1. injection Eq1 as H_T1a H_b1 H_ka1.
      subst T1a'. subst b1. subst ka1'.
      rewrite Eqw2 in Eq2. injection Eq2 as H_T1b H_b2 H_ka2.
      subst T1b'. subst b2. subst ka2'.
      assert (HRVarg : RV T1 a1 a2) by (apply (IH2 sigma1 sigma2 Henv a1 a2 Ea1 Ea2)).
      assert (Eo1 : evaluates (open body1 a1) v1).
      { apply ev_protect_low_iff. rewrite <- Hk1. exact Er1. }
      assert (Eo2 : evaluates (open body2 a2) v2).
      { apply ev_protect_low_iff. rewrite <- Hk2. exact Er2. }
      exact (Hbeh a1 a2 (proj2 Ea1) (proj2 Ea2) HRVarg v1 v2 Eo1 Eo2).
    + apply RV_high. rewrite security_of_ty_protect, protect_security_ir, join_high_r.
      reflexivity.
  - (* T_Pair *)
    simpl. intros v1 v2 E1 E2.
    destruct kappa as [rr ii]. destruct ii; simpl.
    + destruct (ev_pair (subst_all sigma1 t1) (subst_all sigma1 t2) {| reader := rr; indirect_reader := Low |} v1 E1)
        as (a1 & b1 & E1a & E1b & Eq1).
      destruct (ev_pair (subst_all sigma2 t1) (subst_all sigma2 t2) {| reader := rr; indirect_reader := Low |} v2 E2)
        as (a2 & b2 & E2a & E2b & Eq2).
      assert (HRV1 : RV T1 a1 a2) by (apply (IH1 sigma1 sigma2 Henv a1 a2 E1a E2a)).
      assert (HRV2 : RV T2 b1 b2) by (apply (IH2 sigma1 sigma2 Henv b1 b2 E1b E2b)).
      subst v1. subst v2.
      exists a1, b1, {| reader := rr; indirect_reader := Low |},
             a2, b2, {| reader := rr; indirect_reader := Low |}.
      split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; assumption]]]].
    + exact I.
  - (* T_Fst *)
    simpl. intros v1 v2 E1 E2.
    destruct kappa as [rr ii]. destruct ii; simpl.
    + rewrite ty_protect_low.
      destruct (ev_fst (subst_all sigma1 t) r v1 E1) as (a1 & b1 & ka1 & Ep1 & Er1).
      destruct (ev_fst (subst_all sigma2 t) r v2 E2) as (a2 & b2 & ka2 & Ep2 & Er2).
      destruct (IH1 sigma1 sigma2 Henv (tm_pair a1 b1 ka1) (tm_pair a2 b2 ka2) Ep1 Ep2)
        as (x1 & y1 & kb1 & x2 & y2 & kb2 & Eq1 & Eq2 & Hk1 & Hk2 & HRV1 & HRV2).
      injection Eq1 as Ha1 Hb1 Hka1. subst x1. subst y1. subst kb1.
      injection Eq2 as Ha2 Hb2 Hka2. subst x2. subst y2. subst kb2.
      assert (Eo1 : evaluates a1 v1).
      { apply ev_protect_low_iff. rewrite <- Hk1. exact Er1. }
      assert (Eo2 : evaluates a2 v2).
      { apply ev_protect_low_iff. rewrite <- Hk2. exact Er2. }
      apply (R_of_RV T1 a1 a2).
      * exact (proj1 (value_pair_inv _ _ _ (proj2 Ep1))).
      * exact (proj1 (value_pair_inv _ _ _ (proj2 Ep2))).
      * exact HRV1.
      * exact Eo1.
      * exact Eo2.
    + apply RV_high. rewrite security_of_ty_protect, protect_security_ir, join_high_r.
      reflexivity.
  - (* T_Snd *)
    simpl. intros v1 v2 E1 E2.
    destruct kappa as [rr ii]. destruct ii; simpl.
    + rewrite ty_protect_low.
      destruct (ev_snd (subst_all sigma1 t) r v1 E1) as (a1 & b1 & ka1 & Ep1 & Er1).
      destruct (ev_snd (subst_all sigma2 t) r v2 E2) as (a2 & b2 & ka2 & Ep2 & Er2).
      destruct (IH1 sigma1 sigma2 Henv (tm_pair a1 b1 ka1) (tm_pair a2 b2 ka2) Ep1 Ep2)
        as (x1 & y1 & kb1 & x2 & y2 & kb2 & Eq1 & Eq2 & Hk1 & Hk2 & HRV1 & HRV2).
      injection Eq1 as Ha1 Hb1 Hka1. subst x1. subst y1. subst kb1.
      injection Eq2 as Ha2 Hb2 Hka2. subst x2. subst y2. subst kb2.
      assert (Eo1 : evaluates b1 v1).
      { apply ev_protect_low_iff. rewrite <- Hk1. exact Er1. }
      assert (Eo2 : evaluates b2 v2).
      { apply ev_protect_low_iff. rewrite <- Hk2. exact Er2. }
      apply (R_of_RV T2 b1 b2).
      * exact (proj2 (value_pair_inv _ _ _ (proj2 Ep1))).
      * exact (proj2 (value_pair_inv _ _ _ (proj2 Ep2))).
      * exact HRV2.
      * exact Eo1.
      * exact Eo2.
    + apply RV_high. rewrite security_of_ty_protect, protect_security_ir, join_high_r.
      reflexivity.
  - (* T_Inl *)
    simpl. intros v1 v2 E1 E2.
    destruct kappa as [rr ii]. destruct ii; simpl.
    + destruct (ev_inl (subst_all sigma1 t) {| reader := rr; indirect_reader := Low |} v1 E1)
        as (a1 & Ea1 & Eq1).
      destruct (ev_inl (subst_all sigma2 t) {| reader := rr; indirect_reader := Low |} v2 E2)
        as (a2 & Ea2 & Eq2).
      assert (HRV : RV T1 a1 a2) by (apply (IH1 sigma1 sigma2 Henv a1 a2 Ea1 Ea2)).
      subst v1. subst v2.
      left. exists a1, {| reader := rr; indirect_reader := Low |},
                    a2, {| reader := rr; indirect_reader := Low |}.
      split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | exact HRV]]]].
    + exact I.
  - (* T_Inr *)
    simpl. intros v1 v2 E1 E2.
    destruct kappa as [rr ii]. destruct ii; simpl.
    + destruct (ev_inr (subst_all sigma1 t) {| reader := rr; indirect_reader := Low |} v1 E1)
        as (a1 & Ea1 & Eq1).
      destruct (ev_inr (subst_all sigma2 t) {| reader := rr; indirect_reader := Low |} v2 E2)
        as (a2 & Ea2 & Eq2).
      assert (HRV : RV T2 a1 a2) by (apply (IH2 sigma1 sigma2 Henv a1 a2 Ea1 Ea2)).
      subst v1. subst v2.
      right. exists a1, {| reader := rr; indirect_reader := Low |},
                     a2, {| reader := rr; indirect_reader := Low |}.
      split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | exact HRV]]]].
    + exact I.
  - (* T_Case *)
    simpl. intros v1 v2 E1 E2.
    destruct kappa as [rr ii]. destruct ii; simpl.
    + rewrite ty_protect_low.
      destruct (ev_case (subst_all sigma1 t) (subst_all sigma1 body1) (subst_all sigma1 body2) r v1 E1)
        as [(u1 & ka1 & Es1 & Er1) | (u1 & ka1 & Es1 & Er1)];
      destruct (ev_case (subst_all sigma2 t) (subst_all sigma2 body1) (subst_all sigma2 body2) r v2 E2)
        as [(u2 & ka2 & Es2 & Er2) | (u2 & ka2 & Es2 & Er2)].
      * (* inl-inl *)
        destruct (IHt sigma1 sigma2 Henv (tm_inl u1 ka1) (tm_inl u2 ka2) Es1 Es2)
          as [(x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & Hk1 & Hk2 & Hpay) | (x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & _ & _ & _)].
        -- injection Eq1 as Hx1 Hkb1. injection Eq2 as Hx2 Hkb2.
        subst x1. subst kb1. subst x2. subst kb2.
        assert (Eo1 : evaluates (open (subst_all sigma1 body1) u1) v1).
        { apply ev_protect_low_iff. rewrite <- Hk1. exact Er1. }
        assert (Eo2 : evaluates (open (subst_all sigma2 body1) u2) v2).
        { apply ev_protect_low_iff. rewrite <- Hk2. exact Er2. }
        set (Hlc1 := env_rel_lc1 Gamma sigma1 sigma2 Henv).
        set (Hlc2 := env_rel_lc2 Gamma sigma1 sigma2 Henv).
        set (xx := fresh (L ++ fv body1)).
        assert (HxL : ~ In xx L).
        { intro Hc. apply (fresh_not_in (L ++ fv body1)). apply in_or_app. left. exact Hc. }
        assert (HxB : ~ In xx (fv body1)).
        { intro Hc. apply (fresh_not_in (L ++ fv body1)). apply in_or_app. right. exact Hc. }
        assert (Henv' : env_rel (update Gamma xx T1)
                           (extend sigma1 xx u1) (extend sigma2 xx u2)).
        { apply env_rel_extend.
          - exact Henv.
          - exact (value_inl_inv _ _ (proj2 Es1)).
          - exact (value_inl_inv _ _ (proj2 Es2)).
          - exact Hpay. }
        pose proof (IHp1 xx HxL (extend sigma1 xx u1) (extend sigma2 xx u2) Henv')
          as Hbody.
        rewrite (subst_all_open_extend body1 xx sigma1 u1 Hlc1
                   (value_lc u1 (value_inl_inv _ _ (proj2 Es1))) HxB) in Hbody.
        rewrite (subst_all_open_extend body1 xx sigma2 u2 Hlc2
                   (value_lc u2 (value_inl_inv _ _ (proj2 Es2))) HxB) in Hbody.
        exact (Hbody v1 v2 Eo1 Eo2).
        -- (* inr disjunct is impossible *) discriminate Eq1.
      * (* inl-inr : impossible *)
        destruct (IHt sigma1 sigma2 Henv (tm_inl u1 ka1) (tm_inr u2 ka2) Es1 Es2)
          as [(x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & _ & _ & _)
             | (x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & _ & _ & _)].
        -- discriminate Eq2.
        -- discriminate Eq1.
      * (* inr-inl : impossible *)
        destruct (IHt sigma1 sigma2 Henv (tm_inr u1 ka1) (tm_inl u2 ka2) Es1 Es2)
          as [(x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & _ & _ & _)
             | (x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & _ & _ & _)].
        -- discriminate Eq1.
        -- discriminate Eq2.
      * (* inr-inr *)
        destruct (IHt sigma1 sigma2 Henv (tm_inr u1 ka1) (tm_inr u2 ka2) Es1 Es2)
          as [(x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & _ & _ & _) | (x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & Hk1 & Hk2 & Hpay)].
        -- (* inl disjunct is impossible *) discriminate Eq2.
        -- injection Eq1 as Hx1 Hkb1. injection Eq2 as Hx2 Hkb2.
        subst x1. subst kb1. subst x2. subst kb2.
        assert (Eo1 : evaluates (open (subst_all sigma1 body2) u1) v1).
        { apply ev_protect_low_iff. rewrite <- Hk1. exact Er1. }
        assert (Eo2 : evaluates (open (subst_all sigma2 body2) u2) v2).
        { apply ev_protect_low_iff. rewrite <- Hk2. exact Er2. }
        set (Hlc1 := env_rel_lc1 Gamma sigma1 sigma2 Henv).
        set (Hlc2 := env_rel_lc2 Gamma sigma1 sigma2 Henv).
        set (xx := fresh (L ++ fv body2)).
        assert (HxL : ~ In xx L).
        { intro Hc. apply (fresh_not_in (L ++ fv body2)). apply in_or_app. left. exact Hc. }
        assert (HxB : ~ In xx (fv body2)).
        { intro Hc. apply (fresh_not_in (L ++ fv body2)). apply in_or_app. right. exact Hc. }
        assert (Henv' : env_rel (update Gamma xx T2)
                           (extend sigma1 xx u1) (extend sigma2 xx u2)).
        { apply env_rel_extend.
          - exact Henv.
          - exact (value_inr_inv _ _ (proj2 Es1)).
          - exact (value_inr_inv _ _ (proj2 Es2)).
          - exact Hpay. }
        pose proof (IHp2 xx HxL (extend sigma1 xx u1) (extend sigma2 xx u2) Henv')
          as Hbody.
        rewrite (subst_all_open_extend body2 xx sigma1 u1 Hlc1
                   (value_lc u1 (value_inr_inv _ _ (proj2 Es1))) HxB) in Hbody.
        rewrite (subst_all_open_extend body2 xx sigma2 u2 Hlc2
                   (value_lc u2 (value_inr_inv _ _ (proj2 Es2))) HxB) in Hbody.
        exact (Hbody v1 v2 Eo1 Eo2).
    + apply RV_high. rewrite security_of_ty_protect, protect_security_ir, join_high_r.
      reflexivity.
  - (* T_Protect *)
    simpl. destruct l; simpl.
    + rewrite ty_protect_low. apply R_protect_low. apply (IH1 sigma1 sigma2 Henv).
    + intros v1 v2 E1 E2. apply RV_high.
      rewrite security_of_ty_protect, protect_security_ir, join_high_r.
      reflexivity.
  - (* T_Sub *)
    simpl. apply (R_subtype T0 U Hsub). apply (IH1 sigma1 sigma2 Henv).
  - (* T_If *)
    simpl. intros v1 v2 E1 E2.
    destruct k as [r2 i2]. destruct i2; simpl.
    + rewrite ty_protect_low.
      destruct (ev_if (subst_all sigma1 c) (subst_all sigma1 yes) (subst_all sigma1 no) r v1 E1)
        as [(u1 & ka1 & Ec1 & Er1) | (u1 & ka1 & Ec1 & Er1)];
      destruct (ev_if (subst_all sigma2 c) (subst_all sigma2 yes) (subst_all sigma2 no) r v2 E2)
        as [(u2 & ka2 & Ec2 & Er2) | (u2 & ka2 & Ec2 & Er2)].
      * destruct (IHc sigma1 sigma2 Henv (tm_inl u1 ka1) (tm_inl u2 ka2) Ec1 Ec2)
          as [(x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & Hk1 & Hk2 & _) | (x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & _ & _ & _)].
        -- injection Eq1 as _ Hkb1. injection Eq2 as _ Hkb2.
           subst kb1. subst kb2.
           assert (Eo1 : evaluates (subst_all sigma1 yes) v1).
           { apply ev_protect_low_iff. rewrite <- Hk1. exact Er1. }
           assert (Eo2 : evaluates (subst_all sigma2 yes) v2).
           { apply ev_protect_low_iff. rewrite <- Hk2. exact Er2. }
           exact (IHy sigma1 sigma2 Henv v1 v2 Eo1 Eo2).
        -- discriminate Eq1.
      * destruct (IHc sigma1 sigma2 Henv (tm_inl u1 ka1) (tm_inr u2 ka2) Ec1 Ec2)
          as [(x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & _ & _ & _)
             | (x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & _ & _ & _)].
        -- discriminate Eq2.
        -- discriminate Eq1.
      * destruct (IHc sigma1 sigma2 Henv (tm_inr u1 ka1) (tm_inl u2 ka2) Ec1 Ec2)
          as [(x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & _ & _ & _)
             | (x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & _ & _ & _)].
        -- discriminate Eq1.
        -- discriminate Eq2.
      * destruct (IHc sigma1 sigma2 Henv (tm_inr u1 ka1) (tm_inr u2 ka2) Ec1 Ec2)
          as [(x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & _ & _ & _) | (x1 & kb1 & x2 & kb2 & Eq1 & Eq2 & Hk1 & Hk2 & _)].
        -- discriminate Eq2.
        -- injection Eq1 as _ Hkb1. injection Eq2 as _ Hkb2.
           subst kb1. subst kb2.
           assert (Eo1 : evaluates (subst_all sigma1 no) v1).
           { apply ev_protect_low_iff. rewrite <- Hk1. exact Er1. }
           assert (Eo2 : evaluates (subst_all sigma2 no) v2).
           { apply ev_protect_low_iff. rewrite <- Hk2. exact Er2. }
           exact (IHn sigma1 sigma2 Henv v1 v2 Eo1 Eo2).
    + apply RV_high. rewrite security_of_ty_protect, protect_security_ir, join_high_r.
      reflexivity.
Qed.

(* ---------- Plugging and substitution ---------- *)

Fixpoint fv_context (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs T C' kappa => fv_context C'
  | C_AppLeft C' t2 r => fv_context C' ++ fv t2
  | C_AppRight t1 C' r => fv t1 ++ fv_context C'
  | C_PairLeft C' t2 kappa => fv_context C' ++ fv t2
  | C_PairRight t1 C' kappa => fv t1 ++ fv_context C'
  | C_Fst C' r => fv_context C'
  | C_Snd C' r => fv_context C'
  | C_Inl C' kappa => fv_context C'
  | C_Inr C' kappa => fv_context C'
  | C_CaseScrutinee C' body1 body2 r => fv_context C' ++ fv body1 ++ fv body2
  | C_CaseLeft t0 C' body2 r => fv t0 ++ fv_context C' ++ fv body2
  | C_CaseRight t0 body1 C' r => fv t0 ++ fv body1 ++ fv_context C'
  | C_Protect l C' => fv_context C'
  | C_IfCondition C' y n r => fv_context C' ++ fv y ++ fv n
  | C_IfThen c C' n r => fv c ++ fv_context C' ++ fv n
  | C_IfElse c y C' r => fv c ++ fv y ++ fv_context C'
  end.

Lemma subst_all_plug : forall C x u,
    ~ In x (fv_context C) ->
    subst_all (fun y => if Nat.eqb y x then u else tm_fvar y)
      (plug C (tm_fvar x)) = plug C u.
Proof.
  induction C; intros x u Hx; simpl in *.
  - rewrite Nat.eqb_refl. reflexivity.
  - f_equal. apply IHC. exact Hx.
  - rewrite IHC by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
  - rewrite IHC by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
  - rewrite IHC by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
  - rewrite IHC by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
  - f_equal. apply IHC. exact Hx.
  - f_equal. apply IHC. exact Hx.
  - f_equal. apply IHC. exact Hx.
  - f_equal. apply IHC. exact Hx.
  - rewrite IHC by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
  - rewrite IHC by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
  - rewrite IHC by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
  - f_equal. apply IHC. exact Hx.
  - rewrite IHC by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
  - rewrite IHC by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
  - rewrite IHC by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    rewrite subst_all_fvar_self by (intro H; apply Hx; rewrite !in_app_iff; auto).
    reflexivity.
Qed.

(* ---------- Erasing ground, transparent values ---------- *)

Fixpoint all_ir_low (T : ty) : Prop :=
  (security_of T).(indirect_reader) = Low /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      all_ir_low T1 /\ all_ir_low T2
  end.

Lemma transparent_all_ir_low : forall kappa T,
    transparent_at kappa T -> kappa.(indirect_reader) = Low -> all_ir_low T.
Proof.
  intros kappa T.
  induction T as [k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k];
    intros Htr Hk; simpl in *.
  - destruct Htr as [Hle _]. split; [| exact I].
    apply (security_le_ir_low _ _ Hle Hk).
  - destruct Htr as [Hle [Htr1 Htr2]]. split; [| split].
    + apply (security_le_ir_low _ _ Hle Hk).
    + apply IH1; [exact Htr1 | exact Hk].
    + apply IH2; [exact Htr2 | exact Hk].
  - destruct Htr as [Hle [Htr1 Htr2]]. split; [| split].
    + apply (security_le_ir_low _ _ Hle Hk).
    + apply IH1; [exact Htr1 | exact Hk].
    + apply IH2; [exact Htr2 | exact Hk].
  - destruct Htr as [Hle [Htr1 Htr2]]. split; [| split].
    + apply (security_le_ir_low _ _ Hle Hk).
    + apply IH1; [exact Htr1 | exact Hk].
    + apply IH2; [exact Htr2 | exact Hk].
Qed.

Lemma RV_erase : forall kappa T v1 v2,
    ground T -> transparent_at kappa T -> kappa.(indirect_reader) = Low ->
    RV T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  intros kappa T.
  induction T as [k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k];
    intros v1 v2 Hg Htr Hk HRV.
  - (* Ty_Unit *)
    simpl in Hg.
    destruct (transparent_all_ir_low kappa (Ty_Unit k) Htr Hk) as [Hir _].
    simpl in Hir.
    destruct k as [rr ii]; simpl in *; subst ii; simpl in HRV.
    destruct HRV as [[ka1 Eq1] [ka2 Eq2]].
    subst v1. subst v2. reflexivity.
  - (* Ty_Sum *)
    simpl in Hg. destruct Hg as [Hg1 Hg2].
    destruct (transparent_all_ir_low kappa (Ty_Sum T1 T2 k) Htr Hk)
      as [Hir [Hl1 Hl2]].
    simpl in Hir.
    destruct k as [rr ii]; simpl in *; subst ii; simpl in HRV.
    destruct Htr as [_ [Htr1 Htr2]].
    destruct HRV as [Hinl | Hinr].
    + destruct Hinl as (a1 & ka1 & a2 & ka2 & Eq1 & Eq2 & _ & _ & Hpay).
      subst v1. subst v2. simpl. f_equal.
      exact (IH1 a1 a2 Hg1 Htr1 Hk Hpay).
    + destruct Hinr as (a1 & ka1 & a2 & ka2 & Eq1 & Eq2 & _ & _ & Hpay).
      subst v1. subst v2. simpl. f_equal.
      exact (IH2 a1 a2 Hg2 Htr2 Hk Hpay).
  - (* Ty_Prod *)
    simpl in Hg. destruct Hg as [Hg1 Hg2].
    destruct (transparent_all_ir_low kappa (Ty_Prod T1 T2 k) Htr Hk)
      as [Hir [Hl1 Hl2]].
    simpl in Hir.
    destruct k as [rr ii]; simpl in *; subst ii; simpl in HRV.
    destruct Htr as [_ [Htr1 Htr2]].
    destruct HRV as (a1 & b1 & ka1 & a2 & b2 & ka2 & Eq1 & Eq2 & _ & _ & Hp1 & Hp2).
    subst v1. subst v2. simpl. f_equal.
    + exact (IH1 a1 a2 Hg1 Htr1 Hk Hp1).
    + exact (IH2 b1 b2 Hg2 Htr2 Hk Hp2).
  - (* Ty_Arrow *)
    simpl in Hg. destruct Hg.
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 Hctx Hground Htrans Hnflow.
  (* The secret's indirect reader is High, the result's indirect reader is Low *)
  assert (Hsec : (security_of T_secret).(indirect_reader) = High).
  { destruct ((security_of T_secret).(indirect_reader)) eqn:E; auto.
    exfalso. apply Hnflow.
    destruct ((security_of T_result).(indirect_reader)) eqn:E2; simpl; exact I. }
  assert (Hres : (security_of T_result).(indirect_reader) = Low).
  { destruct ((security_of T_result).(indirect_reader)) eqn:E; auto.
    exfalso. apply Hnflow. rewrite Hsec. simpl. exact I. }
  (* Choose a fresh variable for the hole *)
  destruct Hctx as (L & Hty).
  set (L' := L ++ fv_context C).
  set (x := fresh L').
  assert (Hx' : ~ In x L') by apply fresh_not_in.
  assert (HxL : ~ In x L).
  { intro Hc. apply Hx'. unfold L'. apply in_or_app. left. exact Hc. }
  assert (HxC : ~ In x (fv_context C)).
  { intro Hc. apply Hx'. unfold L'. apply in_or_app. right. exact Hc. }
  assert (Htyx : has_type (update empty x T_secret)
                    (plug C (tm_fvar x)) T_result).
  { apply Hty. exact HxL. }
  (* Substitute t1 and t2 for the hole *)
  set (sigma1 := fun y => if Nat.eqb y x then t1 else tm_fvar y).
  set (sigma2 := fun y => if Nat.eqb y x then t2 else tm_fvar y).
  assert (Henv : env_rel (update empty x T_secret) sigma1 sigma2).
  { split; [| split].
    - intros y. unfold sigma1. destruct (Nat.eqb y x).
      + exact (has_type_lc empty t1 T_secret Ht1).
      + exact I.
    - intros y. unfold sigma2. destruct (Nat.eqb y x).
      + exact (has_type_lc empty t2 T_secret Ht2).
      + exact I.
    - intros y T Hy. unfold sigma1, sigma2.
      destruct (Nat.eqb y x) eqn:E.
      + apply Nat.eqb_eq in E. subst y.
        assert (HT : T = T_secret).
        { rewrite lookup_context_update_eq in Hy. injection Hy. auto. }
        subst T. apply R_weak. exact Hsec.
      + apply Nat.eqb_neq in E.
        rewrite lookup_context_update_neq in Hy by exact E.
        simpl in Hy. discriminate Hy. }
  assert (Hmain : R T_result
      (subst_all sigma1 (plug C (tm_fvar x)))
      (subst_all sigma2 (plug C (tm_fvar x)))).
  { exact (fundamental (update empty x T_secret) (plug C (tm_fvar x))
             T_result Htyx sigma1 sigma2 Henv). }
  assert (Hs1 : subst_all sigma1 (plug C (tm_fvar x)) = plug C t1).
  { unfold sigma1. apply subst_all_plug. exact HxC. }
  assert (Hs2 : subst_all sigma2 (plug C (tm_fvar x)) = plug C t2).
  { unfold sigma2. apply subst_all_plug. exact HxC. }
  rewrite Hs1 in Hmain. rewrite Hs2 in Hmain.
  unfold same_result. intros v1 v2 E1 E2.
  apply (RV_erase (security_of T_result) T_result v1 v2
           Hground Htrans Hres).
  exact (Hmain v1 v2 E1 E2).
Qed.
