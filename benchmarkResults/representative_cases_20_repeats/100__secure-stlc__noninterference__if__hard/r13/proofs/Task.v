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
(* Auxiliary definitions and lemmas added for the proof.        *)
(* ============================================================ *)

(* ---------- label and security lemmas ---------- *)

Lemma flows_to_refl : forall l : label, flows_to l l.
Proof. intros []; simpl; auto. Qed.

Lemma flows_to_trans : forall l1 l2 l3 : label,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof. intros [] [] [] H1 H2; simpl in *; auto. Qed.

Lemma flows_to_low : forall l : label, flows_to Low l.
Proof. intros []; simpl; auto. Qed.

Lemma flows_to_high : forall l : label, flows_to l High.
Proof. intros []; simpl; auto. Qed.

Lemma flows_to_low_inv : forall l : label, flows_to l Low -> l = Low.
Proof. intros [] H; simpl in *; [reflexivity | tauto]. Qed.

Lemma join_flows_to : forall l1 l2 l : label,
  flows_to (join l1 l2) l <-> flows_to l1 l /\ flows_to l2 l.
Proof. intros [] [] []; simpl; tauto. Qed.

Lemma flows_to_join_r : forall l1 l2 l : label,
  flows_to l l1 -> flows_to l (join l1 l2).
Proof. intros [] [] []; simpl in *; auto. Qed.

Lemma flows_to_join_l : forall l1 l2 l : label,
  flows_to l l2 -> flows_to l (join l1 l2).
Proof. intros [] [] []; simpl in *; auto. Qed.

Lemma join_comm : forall l1 l2 : label, join l1 l2 = join l2 l1.
Proof. intros [] []; simpl; auto. Qed.

Lemma join_assoc : forall l1 l2 l3 : label,
  join (join l1 l2) l3 = join l1 (join l2 l3).
Proof. intros [] [] []; simpl; auto. Qed.

Lemma security_le_refl : forall k : security, security_le k k.
Proof. intros [r i]; simpl; split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3 : security,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3] [H1 H2] [H3 H4]; simpl in *.
  split; eapply flows_to_trans; eauto.
Qed.

Lemma protect_security_assoc : forall k l1 l2,
  protect_security (protect_security k l1) l2 =
  protect_security k (join l1 l2).
Proof.
  intros [r i] l1 l2; simpl.
  destruct r, i, l1, l2; simpl; auto.
Qed.

Lemma protect_security_ge : forall k l, security_le k (protect_security k l).
Proof.
  intros [r i] l; simpl; split.
  - destruct r, l; simpl; auto.
  - destruct i, l; simpl; auto.
Qed.

Lemma protect_security_indirect : forall k l,
  (protect_security k l).(indirect_reader) = join k.(indirect_reader) l.
Proof. intros [r i] l; simpl; auto. Qed.

Lemma protect_security_reader : forall k l,
  (protect_security k l).(reader) = join k.(reader) l.
Proof. intros [r i] l; simpl; auto. Qed.

Lemma security_of_ty_protect : forall l T,
  security_of (ty_protect l T) = protect_security (security_of T) l.
Proof. intros l []; simpl; auto. Qed.

Lemma wf_security_protect : forall k l,
  wf_security k -> wf_security (protect_security k l).
Proof.
  intros [r i] l. unfold wf_security. simpl.
  intros H. destruct r, i, l; simpl in *; tauto.
Qed.

(* ---------- freshness of atoms ---------- *)

Definition max_atom (L : list atom) : atom := fold_right Nat.max 0 L.

Lemma max_atom_ge : forall (L : list atom) (x : atom), In x L -> x <= max_atom L.
Proof.
  induction L as [| a L IH].
  - simpl. intros x H. destruct H.
  - simpl. intros x H. destruct H as [<- | H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto | apply Nat.le_max_r].
Qed.

Definition fresh (L : list atom) : atom := S (max_atom L).

Lemma fresh_not_in : forall L : list atom, ~ In (fresh L) L.
Proof.
  intros L H. apply max_atom_ge in H. unfold fresh in H. lia.
Qed.

(* ---------- environment substitution ---------- *)

Fixpoint subst_env (g : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => g x
  | tm_unit kappa => tm_unit kappa
  | tm_abs T body kappa => tm_abs T (subst_env g body) kappa
  | tm_app t1 t2 r => tm_app (subst_env g t1) (subst_env g t2) r
  | tm_pair t1 t2 kappa => tm_pair (subst_env g t1) (subst_env g t2) kappa
  | tm_fst t1 r => tm_fst (subst_env g t1) r
  | tm_snd t1 r => tm_snd (subst_env g t1) r
  | tm_inl t1 kappa => tm_inl (subst_env g t1) kappa
  | tm_inr t1 kappa => tm_inr (subst_env g t1) kappa
  | tm_case t0 body1 body2 r =>
      tm_case (subst_env g t0) (subst_env g body1) (subst_env g body2) r
  | tm_protect l t1 => tm_protect l (subst_env g t1)
  | tm_if c yes no r => tm_if (subst_env g c) (subst_env g yes) (subst_env g no) r
  end.

Definition update_env (g : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else g y.

Definition env_lc (g : atom -> tm) : Prop :=
  forall y, locally_closed (g y).

Lemma env_lc_update : forall g x u,
  env_lc g -> locally_closed u -> env_lc (update_env g x u).
Proof.
  intros g x u Hg Hu y; unfold update_env.
  destruct (Nat.eqb y x); [exact Hu | apply Hg].
Qed.

(* ---------- locality lemmas ---------- *)

Lemma lc_at_mono : forall t k k', k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  induction t; simpl; intros k k' Hle H; auto; try lia.
  - (* abs *) apply (IHt (S k) (S k')); [lia | assumption].
  - (* app *) destruct H as [H1 H2]; split.
    + apply (IHt1 k k'); auto.
    + apply (IHt2 k k'); auto.
  - (* pair *) destruct H as [H1 H2]; split.
    + apply (IHt1 k k'); auto.
    + apply (IHt2 k k'); auto.
  - (* fst *) apply (IHt k k'); auto.
  - (* snd *) apply (IHt k k'); auto.
  - (* inl *) apply (IHt k k'); auto.
  - (* inr *) apply (IHt k k'); auto.
  - (* case *) destruct H as [H1 [H2 H3]]; repeat split.
    + apply (IHt1 k k'); auto.
    + apply (IHt2 (S k) (S k')); [lia | assumption].
    + apply (IHt3 (S k) (S k')); [lia | assumption].
  - (* protect *) apply (IHt k k'); auto.
  - (* if *) destruct H as [H1 [H2 H3]]; repeat split.
    + apply (IHt1 k k'); auto.
    + apply (IHt2 k k'); auto.
    + apply (IHt3 k k'); auto.
Qed.

Lemma lc_at_open_fvar : forall body k x,
  lc_at (S k) body <-> lc_at k (open_rec k (tm_fvar x) body).
Proof.
  induction body as [ n | x0 | kappa | T body IHbody kappa
                    | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 kappa
                    | t1 IH1 r | t1 IH1 r | t1 IH1 kappa | t1 IH1 kappa
                    | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1
                    | c IHc yes IHy no IHn r ];
  intros k x; simpl.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; simpl. split; intros; [exact I | lia].
    + apply Nat.eqb_neq in E; simpl. split; intros; lia.
  - (* fvar *) tauto.
  - (* unit *) tauto.
  - (* abs *) apply IHbody.
  - (* app *)
    split; intros [H1 H2]; split;
      [ apply (proj1 (IH1 k x)); exact H1
      | apply (proj1 (IH2 k x)); exact H2
      | apply (proj2 (IH1 k x)); exact H1
      | apply (proj2 (IH2 k x)); exact H2 ].
  - (* pair *)
    split; intros [H1 H2]; split;
      [ apply (proj1 (IH1 k x)); exact H1
      | apply (proj1 (IH2 k x)); exact H2
      | apply (proj2 (IH1 k x)); exact H1
      | apply (proj2 (IH2 k x)); exact H2 ].
  - (* fst *) apply IH1.
  - (* snd *) apply IH1.
  - (* inl *) apply IH1.
  - (* inr *) apply IH1.
  - (* case *)
    split; intros [H1 [H2 H3]]; repeat split;
      [ apply (proj1 (IH0 k x)); exact H1
      | apply (proj1 (IH1 (S k) x)); exact H2
      | apply (proj1 (IH2 (S k) x)); exact H3
      | apply (proj2 (IH0 k x)); exact H1
      | apply (proj2 (IH1 (S k) x)); exact H2
      | apply (proj2 (IH2 (S k) x)); exact H3 ].
  - (* protect *) apply IH1.
  - (* if *)
    split; intros [H1 [H2 H3]]; repeat split;
      [ apply (proj1 (IHc k x)); exact H1
      | apply (proj1 (IHy k x)); exact H2
      | apply (proj1 (IHn k x)); exact H3
      | apply (proj2 (IHc k x)); exact H1
      | apply (proj2 (IHy k x)); exact H2
      | apply (proj2 (IHn k x)); exact H3 ].
Qed.

Lemma lc_at_subst_env : forall g, env_lc g ->
  forall t k, lc_at k t -> lc_at k (subst_env g t).
Proof.
  intros g Hg t.
  induction t as [ n | x | kappa | T body IHbody kappa
                 | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 kappa
                 | t1 IH1 r | t1 IH1 r | t1 IH1 kappa | t1 IH1 kappa
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1
                 | c IHc yes IHy no IHn r ];
  simpl; intros k H.
  - (* bvar *) exact H.
  - (* fvar *) apply lc_at_mono with (k := 0); [lia | apply Hg].
  - (* unit *) exact I.
  - (* abs *) apply (IHbody (S k)); exact H.
  - (* app *) destruct H as [H1 H2]; split.
    + apply (IH1 k); exact H1.
    + apply (IH2 k); exact H2.
  - (* pair *) destruct H as [H1 H2]; split.
    + apply (IH1 k); exact H1.
    + apply (IH2 k); exact H2.
  - (* fst *) apply (IH1 k); exact H.
  - (* snd *) apply (IH1 k); exact H.
  - (* inl *) apply (IH1 k); exact H.
  - (* inr *) apply (IH1 k); exact H.
  - (* case *) destruct H as [H1 [H2 H3]]; repeat split.
    + apply (IH0 k); exact H1.
    + apply (IH1 (S k)); exact H2.
    + apply (IH2 (S k)); exact H3.
  - (* protect *) apply (IH1 k); exact H.
  - (* if *) destruct H as [H1 [H2 H3]]; repeat split.
    + apply (IHc k); exact H1.
    + apply (IHy k); exact H2.
    + apply (IHn k); exact H3.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H as
    [ Gamma x T Hlook Hwf
    | Gamma kappa Hwf
    | L Gamma T1 body T2 kappa Hwf1 Hwf2 Hty HIH
    | Gamma t1 t2 T1 T2 kappa r Hty1 IH1 Hty2 IH2 Hflow
    | Gamma t1 t2 T1 T2 kappa Hty1 IH1 Hty2 IH2 Hwf
    | Gamma t T1 T2 kappa r Hty IH Hflow
    | Gamma t T1 T2 kappa r Hty IH Hflow
    | Gamma t T1 T2 kappa Hty IH HwfT2 Hwfkappa
    | Gamma t T1 T2 kappa HwfT1 Hty IH Hwfkappa
    | L Gamma t body1 body2 T1 T2 T kappa r Hty0 IH0 Hflow Hty1 IH1 Hty2 IH2
    | Gamma t T l Hty IH
    | Gamma t T U Hty IH Hsub
    | Gamma c yes no k T r Htyc IHc Htyy IHy Htyn IHn Hflow
    ]; simpl.
  - (* T_Var *) exact I.
  - (* T_Unit *) exact I.
  - (* T_Abs *)
    apply (proj2 (lc_at_open_fvar body 0 (fresh L))).
    apply HIH. apply fresh_not_in.
  - (* T_App *) split; assumption.
  - (* T_Pair *) split; assumption.
  - (* T_Fst *) assumption.
  - (* T_Snd *) assumption.
  - (* T_Inl *) assumption.
  - (* T_Inr *) assumption.
  - (* T_Case *)
    split; [exact IH0 | split].
    + apply (proj2 (lc_at_open_fvar body1 0 (fresh L))).
      apply IH1. apply fresh_not_in.
    + apply (proj2 (lc_at_open_fvar body2 0 (fresh L))).
      apply IH2. apply fresh_not_in.
  - (* T_Protect *) assumption.
  - (* T_Sub *) assumption.
  - (* T_If *) repeat split; assumption.
Qed.

(* ---------- free variables of a program context ---------- *)

Fixpoint fv_ctx (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ => fv_ctx C'
  | C_AppLeft C' t2 _ => fv_ctx C' ++ fv t2
  | C_AppRight t1 C' _ => fv t1 ++ fv_ctx C'
  | C_PairLeft C' t2 _ => fv_ctx C' ++ fv t2
  | C_PairRight t1 C' _ => fv t1 ++ fv_ctx C'
  | C_Fst C' _ => fv_ctx C'
  | C_Snd C' _ => fv_ctx C'
  | C_Inl C' _ => fv_ctx C'
  | C_Inr C' _ => fv_ctx C'
  | C_CaseScrutinee C' b1 b2 _ => fv_ctx C' ++ fv b1 ++ fv b2
  | C_CaseLeft t0 C' b2 _ => fv t0 ++ fv_ctx C' ++ fv b2
  | C_CaseRight t0 b1 C' _ => fv t0 ++ fv b1 ++ fv_ctx C'
  | C_Protect _ C' => fv_ctx C'
  | C_IfCondition C' y n _ => fv_ctx C' ++ fv y ++ fv n
  | C_IfThen c C' n _ => fv c ++ fv_ctx C' ++ fv n
  | C_IfElse c y C' _ => fv c ++ fv y ++ fv_ctx C'
  end.

Lemma subst_env_fix : forall g s,
  (forall y, In y (fv s) -> g y = tm_fvar y) -> subst_env g s = s.
Proof.
  intros g s.
  induction s as [ n | a | kappa | T body IHbody kappa
                 | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 kappa
                 | t1 IH1 r | t1 IH1 r | t1 IH1 kappa | t1 IH1 kappa
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1
                 | c IHc yes IHy no IHn r ];
  simpl; intros Hfix.
  - (* bvar *) reflexivity.
  - (* fvar *) apply Hfix. simpl. auto.
  - (* unit *) reflexivity.
  - (* abs *) f_equal. apply IHbody. intros y Hy. apply Hfix. simpl. exact Hy.
  - (* app *)
    assert (E1 : subst_env g t1 = t1)
      by (apply IH1; intros y Hy; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g t2 = t2)
      by (apply IH2; intros y Hy; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E1, E2. reflexivity.
  - (* pair *)
    assert (E1 : subst_env g t1 = t1)
      by (apply IH1; intros y Hy; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g t2 = t2)
      by (apply IH2; intros y Hy; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E1, E2. reflexivity.
  - (* fst *) f_equal. apply IH1. intros y Hy. apply Hfix. simpl. exact Hy.
  - (* snd *) f_equal. apply IH1. intros y Hy. apply Hfix. simpl. exact Hy.
  - (* inl *) f_equal. apply IH1. intros y Hy. apply Hfix. simpl. exact Hy.
  - (* inr *) f_equal. apply IH1. intros y Hy. apply Hfix. simpl. exact Hy.
  - (* case *)
    assert (E0 : subst_env g t0 = t0)
      by (apply IH0; intros y Hy; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E1 : subst_env g b1 = b1)
      by (apply IH1; intros y Hy; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g b2 = b2)
      by (apply IH2; intros y Hy; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E0, E1, E2. reflexivity.
  - (* protect *) f_equal. apply IH1. intros y Hy. apply Hfix. simpl. exact Hy.
  - (* if *)
    assert (Ec : subst_env g c = c)
      by (apply IHc; intros y Hy; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (Ey : subst_env g yes = yes)
      by (apply IHy; intros y Hy; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (En : subst_env g no = no)
      by (apply IHn; intros y Hy; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite Ec, Ey, En. reflexivity.
Qed.

Lemma subst_env_plug : forall g C t,
  (forall y, In y (fv_ctx C) -> g y = tm_fvar y) ->
  subst_env g (plug C t) = plug C (subst_env g t).
Proof.
  intros g C.
  induction C as
    [ | T C' IH k | C' IH t2 r | t1 C' IH r | C' IH t2 k | t1 C' IH k
    | C' IH r | C' IH r | C' IH k | C' IH k
    | C' IH b1 b2 r | t0 C' IH b2 r | t0 b1 C' IH r
    | l C' IH | C' IH y n r | c C' IH n r | c y C' IH r ];
  simpl; intros t Hfix.
  - (* C_Hole *) reflexivity.
  - (* C_Abs *) f_equal. apply IH. intros z Hz. apply Hfix. simpl. exact Hz.
  - (* C_AppLeft *)
    assert (E1 : subst_env g (plug C' t) = plug C' (subst_env g t))
      by (apply IH; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g t2 = t2)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E1, E2. reflexivity.
  - (* C_AppRight *)
    assert (E1 : subst_env g t1 = t1)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g (plug C' t) = plug C' (subst_env g t))
      by (apply IH; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E1, E2. reflexivity.
  - (* C_PairLeft *)
    assert (E1 : subst_env g (plug C' t) = plug C' (subst_env g t))
      by (apply IH; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g t2 = t2)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E1, E2. reflexivity.
  - (* C_PairRight *)
    assert (E1 : subst_env g t1 = t1)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g (plug C' t) = plug C' (subst_env g t))
      by (apply IH; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E1, E2. reflexivity.
  - (* C_Fst *) f_equal. apply IH. intros z Hz. apply Hfix. simpl. exact Hz.
  - (* C_Snd *) f_equal. apply IH. intros z Hz. apply Hfix. simpl. exact Hz.
  - (* C_Inl *) f_equal. apply IH. intros z Hz. apply Hfix. simpl. exact Hz.
  - (* C_Inr *) f_equal. apply IH. intros z Hz. apply Hfix. simpl. exact Hz.
  - (* C_CaseScrutinee *)
    assert (E0 : subst_env g (plug C' t) = plug C' (subst_env g t))
      by (apply IH; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E1 : subst_env g b1 = b1)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g b2 = b2)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E0, E1, E2. reflexivity.
  - (* C_CaseLeft *)
    assert (E0 : subst_env g t0 = t0)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E1 : subst_env g (plug C' t) = plug C' (subst_env g t))
      by (apply IH; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g b2 = b2)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E0, E1, E2. reflexivity.
  - (* C_CaseRight *)
    assert (E0 : subst_env g t0 = t0)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E1 : subst_env g b1 = b1)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g (plug C' t) = plug C' (subst_env g t))
      by (apply IH; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E0, E1, E2. reflexivity.
  - (* C_Protect *) f_equal. apply IH. intros z Hz. apply Hfix. simpl. exact Hz.
  - (* C_IfCondition *)
    assert (E0 : subst_env g (plug C' t) = plug C' (subst_env g t))
      by (apply IH; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E1 : subst_env g y = y)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g n = n)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E0, E1, E2. reflexivity.
  - (* C_IfThen *)
    assert (E0 : subst_env g c = c)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E1 : subst_env g (plug C' t) = plug C' (subst_env g t))
      by (apply IH; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g n = n)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E0, E1, E2. reflexivity.
  - (* C_IfElse *)
    assert (E0 : subst_env g c = c)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E1 : subst_env g y = y)
      by (apply subst_env_fix; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    assert (E2 : subst_env g (plug C' t) = plug C' (subst_env g t))
      by (apply IH; intros z Hz; apply Hfix; simpl; repeat rewrite in_app_iff; tauto).
    rewrite E0, E1, E2. reflexivity.
Qed.

Lemma subst_env_plug_fresh : forall x t C,
  ~ In x (fv_ctx C) ->
  subst_env (update_env (fun y => tm_fvar y) x t) (plug C (tm_fvar x)) = plug C t.
Proof.
  intros x t C Hfresh.
  rewrite subst_env_plug.
  - simpl. unfold update_env. rewrite Nat.eqb_refl. reflexivity.
  - intros y Hy. unfold update_env. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst. contradiction.
    + reflexivity.
Qed.

(* ---------- value lemmas ---------- *)

Lemma value_locally_closed : forall v, value v -> locally_closed v.
Proof.
  intros v Hv.
  induction Hv as [kappa | T body kappa Hlc | v1 v2 kappa Hv1 IH1 Hv2 IH2
                 | v kappa Hv IH | v kappa Hv IH]; simpl.
  - (* v_unit *) exact I.
  - (* v_abs *) exact Hlc.
  - (* v_pair *) split; assumption.
  - (* v_inl *) assumption.
  - (* v_inr *) assumption.
Qed.

Lemma value_no_step : forall v, value v -> forall v', ~ (v --> v').
Proof.
  intros v Hv.
  induction Hv as [kappa | T body kappa Hlc | v1 v2 kappa Hv1 IH1 Hv2 IH2
                 | v kappa Hv IH | v kappa Hv IH];
  intros v' Hstep; inversion Hstep; subst.
  - (* v_pair, ST_Pair1 *) eapply IH1; eassumption.
  - (* v_pair, ST_Pair2 *) eapply IH2; eassumption.
  - (* v_inl *) eapply IH; eassumption.
  - (* v_inr *) eapply IH; eassumption.
Qed.

(* ---------- evaluation lemmas ---------- *)

Lemma multi_value_inv : forall v u, value v -> v -->* u -> u = v.
Proof.
  intros v u Hv Hm. induction Hm as [t | t1 t2 t3 Hs Hm IH].
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma multi_abs : forall s u, s -->* u -> forall T body k,
  s = tm_abs T body k -> u = tm_abs T body k.
Proof.
  intros s u Hm. induction Hm as [s0 | s0 s1 s2 Hs Hm IH].
  - intros T body k Heq. subst. reflexivity.
  - intros T body k Heq. subst. inversion Hs.
Qed.

Lemma multi_unit : forall s u, s -->* u -> forall k,
  s = tm_unit k -> u = tm_unit k.
Proof.
  intros s u Hm. induction Hm as [s0 | s0 s1 s2 Hs Hm IH].
  - intros k Heq. subst. reflexivity.
  - intros k Heq. subst. inversion Hs.
Qed.

Lemma value_protect_value : forall v, value v -> forall l, value (protect_value v l).
Proof.
  intros v Hv.
  induction Hv as [kappa | T body kappa Hlc | v1 v2 kappa Hv1 IH1 Hv2 IH2
                 | v kappa Hv IH | v kappa Hv IH]; intros l; simpl.
  - (* v_unit *) apply v_unit.
  - (* v_abs *) apply v_abs. exact Hlc.
  - (* v_pair *) apply v_pair; auto.
  - (* v_inl *) apply v_inl; auto.
  - (* v_inr *) apply v_inr; auto.
Qed.

Lemma multi_pair : forall s u, s -->* u -> value u ->
  forall t1 t2 k, s = tm_pair t1 t2 k ->
  exists v1 v2, t1 -->* v1 /\ t2 -->* v2 /\ value v1 /\ value v2 /\
               u = tm_pair v1 v2 k.
Proof.
  intros s u Hm. induction Hm as [s0 | s0 s1 s2 Hs Hm IH].
  - intros Hval a1 a2 k Heq. subst. inversion Hval; subst.
    exists a1, a2. repeat split; auto using multi_refl.
  - intros Hval a1 a2 k Heq. subst. inversion Hs; subst.
    + edestruct IH as (v1 & v2 & Hm1 & Hm2 & Hv1 & Hv2 & Hu);
        [exact Hval | reflexivity | ].
      exists v1, v2. repeat split; auto. eapply multi_step; eauto.
    + edestruct IH as (v1 & v2 & Hm1 & Hm2 & Hv1 & Hv2 & Hu);
        [exact Hval | reflexivity | ].
      exists v1, v2. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_inl : forall s u, s -->* u -> value u ->
  forall t kappa, s = tm_inl t kappa ->
  exists v, t -->* v /\ value v /\ u = tm_inl v kappa.
Proof.
  intros s u Hm. induction Hm as [s0 | s0 s1 s2 Hs Hm IH].
  - intros Hval a k Heq. subst. inversion Hval; subst.
    exists a. repeat split; auto using multi_refl.
  - intros Hval a k Heq. subst. inversion Hs; subst.
    edestruct IH as (v & Hm1 & Hv & Hu); [exact Hval | reflexivity | ].
    exists v. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_inr : forall s u, s -->* u -> value u ->
  forall t kappa, s = tm_inr t kappa ->
  exists v, t -->* v /\ value v /\ u = tm_inr v kappa.
Proof.
  intros s u Hm. induction Hm as [s0 | s0 s1 s2 Hs Hm IH].
  - intros Hval a k Heq. subst. inversion Hval; subst.
    exists a. repeat split; auto using multi_refl.
  - intros Hval a k Heq. subst. inversion Hs; subst.
    edestruct IH as (v & Hm1 & Hv & Hu); [exact Hval | reflexivity | ].
    exists v. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_app : forall s u, s -->* u -> value u ->
  forall t1 t2 r, s = tm_app t1 t2 r ->
  exists T body kappa v,
    t1 -->* tm_abs T body kappa /\ value (tm_abs T body kappa) /\
    t2 -->* v /\ value v /\
    flows_to kappa.(reader) r /\
    tm_protect kappa.(indirect_reader) (open body v) -->* u.
Proof.
  intros s u Hm. induction Hm as [s0 | s0 s1 s2 Hs Hm IH].
  - intros Hval a1 a2 r Heq. subst. inversion Hval.
  - intros Hval a1 a2 r Heq. subst. inversion Hs; subst.
    + (* ST_AppAbs *) exists T, body, kappa, a2. repeat split; auto using multi_refl.
    + (* ST_App1 *)
      edestruct IH as (Ta & ba & ka & va & Ha & Hva & Hb & Hvb & Hf & Hp);
        [exact Hval | reflexivity | ].
      exists Ta, ba, ka, va. repeat split; auto. eapply multi_step; eauto.
    + (* ST_App2 *)
      edestruct IH as (Ta & ba & ka & va & Ha & Hva & Hb & Hvb & Hf & Hp);
        [exact Hval | reflexivity | ].
      exists Ta, ba, ka, va. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_fst : forall s u, s -->* u -> value u ->
  forall t r, s = tm_fst t r ->
  exists v1 v2 kappa,
    t -->* tm_pair v1 v2 kappa /\ value v1 /\ value v2 /\
    tm_protect kappa.(indirect_reader) v1 -->* u.
Proof.
  intros s u Hm. induction Hm as [s0 | s0 s1 s2 Hs Hm IH].
  - intros Hval a r Heq. subst. inversion Hval.
  - intros Hval a r Heq. subst. inversion Hs; subst.
    + exists v1, v2, kappa. repeat split; auto using multi_refl.
    + edestruct IH as (v1 & v2 & kappa & Hm1 & Hv1 & Hv2 & Hp);
        [exact Hval | reflexivity | ].
      exists v1, v2, kappa. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_snd : forall s u, s -->* u -> value u ->
  forall t r, s = tm_snd t r ->
  exists v1 v2 kappa,
    t -->* tm_pair v1 v2 kappa /\ value v1 /\ value v2 /\
    tm_protect kappa.(indirect_reader) v2 -->* u.
Proof.
  intros s u Hm. induction Hm as [s0 | s0 s1 s2 Hs Hm IH].
  - intros Hval a r Heq. subst. inversion Hval.
  - intros Hval a r Heq. subst. inversion Hs; subst.
    + exists v1, v2, kappa. repeat split; auto using multi_refl.
    + edestruct IH as (v1 & v2 & kappa & Hm1 & Hv1 & Hv2 & Hp);
        [exact Hval | reflexivity | ].
      exists v1, v2, kappa. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_case : forall s u, s -->* u -> value u ->
  forall t b1 b2 r, s = tm_case t b1 b2 r ->
  (exists v kappa, t -->* tm_inl v kappa /\ value v /\
                   tm_protect kappa.(indirect_reader) (open b1 v) -->* u) \/
  (exists v kappa, t -->* tm_inr v kappa /\ value v /\
                   tm_protect kappa.(indirect_reader) (open b2 v) -->* u).
Proof.
  intros s u Hm. induction Hm as [s0 | s0 s1 s2 Hs Hm IH].
  - intros Hval a b1 b2 r Heq. subst. inversion Hval.
  - intros Hval a b1 b2 r Heq. subst. inversion Hs; subst.
    + left. exists v, kappa. repeat split; auto using multi_refl.
    + right. exists v, kappa. repeat split; auto using multi_refl.
    + destruct (IH Hval t' b1 b2 r eq_refl) as [(v & kappa & Hm1 & Hv & Hp) | (v & kappa & Hm1 & Hv & Hp)].
      * left. exists v, kappa. repeat split; auto. eapply multi_step; eauto.
      * right. exists v, kappa. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma multi_if : forall s u, s -->* u -> value u ->
  forall c yes no r, s = tm_if c yes no r ->
  (exists v k, c -->* tm_inl v k /\ value v /\
               tm_protect k.(indirect_reader) yes -->* u) \/
  (exists v k, c -->* tm_inr v k /\ value v /\
               tm_protect k.(indirect_reader) no -->* u).
Proof.
  intros s u Hm. induction Hm as [s0 | s0 s1 s2 Hs Hm IH].
  - intros Hval a yes no r Heq. subst. inversion Hval.
  - intros Hval a yes no r Heq. subst. inversion Hs; subst.
    + destruct (IH Hval c' yes no r eq_refl) as [(v & k & Hm1 & Hv & Hp) | (v & k & Hm1 & Hv & Hp)].
      * left. exists v, k. repeat split; auto. eapply multi_step; eauto.
      * right. exists v, k. repeat split; auto. eapply multi_step; eauto.
    + left. exists v, k. repeat split; auto using multi_refl.
    + right. exists v, k. repeat split; auto using multi_refl.
Qed.

Lemma multi_protect : forall s u, s -->* u -> value u ->
  forall l t, s = tm_protect l t ->
  exists v, t -->* v /\ value v /\ u = protect_value v l.
Proof.
  intros s u Hm. induction Hm as [s0 | s0 s1 s2 Hs Hm IH].
  - intros Hval a t Heq. subst. inversion Hval.
  - intros Hval a t Heq. subst. inversion Hs; subst.
    + exists t. split.
      * apply multi_refl.
      * split; [exact H2 | ].
        assert (Hpv : value (protect_value t a)) by (apply value_protect_value; auto).
        pose proof (multi_value_inv _ _ Hpv Hm) as E. subst. reflexivity.
    + edestruct IH as (v & Hm1 & Hv & Hu); [exact Hval | reflexivity | ].
      exists v. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma join_flows_to_inv_l : forall l1 l2 l : label,
  flows_to (join l1 l2) l -> flows_to l1 l.
Proof. intros l1 l2 l H. apply (proj1 (join_flows_to l1 l2 l)) in H; exact (proj1 H). Qed.

Lemma join_flows_to_inv_r : forall l1 l2 l : label,
  flows_to (join l1 l2) l -> flows_to l2 l.
Proof. intros l1 l2 l H. apply (proj1 (join_flows_to l1 l2 l)) in H; exact (proj2 H). Qed.

Lemma flows_to_join_self_l : forall l1 l2 : label, flows_to l1 (join l1 l2).
Proof. intros l1 l2. apply flows_to_join_r. apply flows_to_refl. Qed.

(* ---------- additional multi-step and value lemmas ---------- *)

Lemma multi_trans : forall t1 t2 t3, t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 Hm. induction Hm as [t | t0 s1 s2 Hs Hm IH]; intros Hm'.
  - exact Hm'.
  - eapply multi_step; [exact Hs | apply IH; exact Hm'].
Qed.

Lemma multi_protect_congr : forall t u l, t -->* u -> tm_protect l t -->* tm_protect l u.
Proof.
  intros t u l Hm. induction Hm as [t0 | t0 t1 t2 Hs Hm IH].
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_Protect; exact Hs.
    + exact IH.
Qed.

Lemma multi_protect_value : forall l v, value v -> tm_protect l v -->* protect_value v l.
Proof.
  intros l v Hv. eapply multi_step.
  - apply ST_ProtectValue; exact Hv.
  - apply multi_refl.
Qed.

Lemma protect_value_compose : forall v l1 l2,
  protect_value (protect_value v l1) l2 = protect_value v (join l1 l2).
Proof.
  intros v l1 l2. destruct v; simpl;
  try reflexivity;
  try (rewrite protect_security_assoc; reflexivity).
Qed.

Lemma protect_value_abs_inv : forall v l T body k,
  protect_value v l = tm_abs T body k ->
  exists T0 body0 k0, v = tm_abs T0 body0 k0 /\
                      T = T0 /\ body = body0 /\ k = protect_security k0 l.
Proof.
  intros v l T body k E. destruct v; simpl in E; try discriminate.
  injection E as ET Eb Ek. subst.
  eexists; eexists; eexists. repeat split; reflexivity.
Qed.

Lemma multi_app_abs_protect : forall s z, s -->* z -> value z ->
  forall T body kappa v r,
    s = tm_app (tm_abs T body kappa) v r ->
    value v -> value (tm_abs T body kappa) ->
    flows_to kappa.(reader) r /\
    tm_protect kappa.(indirect_reader) (open body v) -->* z.
Proof.
  intros s z Hm. induction Hm as [s0 | s0 s1 s2 Hs Hm IH];
  intros Hz T body kappa v r Heq Hv Habs.
  - subst. inversion Hz.
  - subst. inversion Hs; subst.
    + split; assumption.
    + exfalso.
      match goal with
      | Hst : tm_abs _ _ _ --> _ |- _ => exact (value_no_step _ Habs _ Hst)
      end.
    + exfalso.
      match goal with
      | Hst : ?vv --> _ |- _ => exact (value_no_step _ Hv _ Hst)
      end.
Qed.

(* ---------- opening and environment substitution ---------- *)

Lemma open_rec_lc_gen : forall s m, lc_at m s -> forall k u, m <= k -> open_rec k u s = s.
Proof.
  induction s as [ n | x | kappa | T body IHbody kappa
                 | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 kappa
                 | t1 IH1 r | t1 IH1 r | t1 IH1 kappa | t1 IH1 kappa
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1
                 | c IHc yes IHy no IHn r ];
  intros m Hm k u Hle; simpl in *.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. lia.
    + reflexivity.
  - (* fvar *) reflexivity.
  - (* unit *) reflexivity.
  - (* abs *) rewrite (IHbody (S m) Hm (S k) u). reflexivity. lia.
  - (* app *) destruct Hm as [H1 H2].
    rewrite (IH1 m H1 k u Hle), (IH2 m H2 k u Hle). reflexivity.
  - (* pair *) destruct Hm as [H1 H2].
    rewrite (IH1 m H1 k u Hle), (IH2 m H2 k u Hle). reflexivity.
  - (* fst *) rewrite (IH1 m Hm k u Hle). reflexivity.
  - (* snd *) rewrite (IH1 m Hm k u Hle). reflexivity.
  - (* inl *) rewrite (IH1 m Hm k u Hle). reflexivity.
  - (* inr *) rewrite (IH1 m Hm k u Hle). reflexivity.
  - (* case *) destruct Hm as [H0 [H1 H2]].
    rewrite (IH0 m H0 k u Hle), (IH1 (S m) H1 (S k) u), (IH2 (S m) H2 (S k) u).
    reflexivity. lia. lia.
  - (* protect *) rewrite (IH1 m Hm k u Hle). reflexivity.
  - (* if *) destruct Hm as [H0 [H1 H2]].
    rewrite (IHc m H0 k u Hle), (IHy m H1 k u Hle), (IHn m H2 k u Hle).
    reflexivity.
Qed.

Lemma open_rec_lc : forall s, lc_at 0 s -> forall k u, open_rec k u s = s.
Proof. intros s H k u. eapply open_rec_lc_gen; [exact H | lia]. Qed.

Lemma subst_env_open_rec : forall g x u body,
  env_lc g -> locally_closed u -> ~ In x (fv body) ->
  forall k,
  subst_env (update_env g x u) (open_rec k (tm_fvar x) body) =
  open_rec k u (subst_env g body).
Proof.
  intros g x u body.
  induction body as [ n | y | kappa | T body IHbody kappa
                    | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 kappa
                    | t1 IH1 r | t1 IH1 r | t1 IH1 kappa | t1 IH1 kappa
                    | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1
                    | c IHc yes IHy no IHn r ];
  intros Hlc Hu Hx k; simpl.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold update_env. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - (* fvar *) destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hx. simpl. auto.
    + unfold update_env. rewrite E. symmetry. apply open_rec_lc. apply Hlc.
  - (* unit *) reflexivity.
  - (* abs *) f_equal. apply (IHbody Hlc Hu). simpl in Hx. exact Hx.
  - (* app *)
    assert (Hx1 : ~ In x (fv t1)) by (intro H; apply Hx; simpl; repeat rewrite in_app_iff; auto).
    assert (Hx2 : ~ In x (fv t2)) by (intro H; apply Hx; simpl; repeat rewrite in_app_iff; auto).
    rewrite (IH1 Hlc Hu Hx1 k), (IH2 Hlc Hu Hx2 k). reflexivity.
  - (* pair *)
    assert (Hx1 : ~ In x (fv t1)) by (intro H; apply Hx; simpl; repeat rewrite in_app_iff; auto).
    assert (Hx2 : ~ In x (fv t2)) by (intro H; apply Hx; simpl; repeat rewrite in_app_iff; auto).
    rewrite (IH1 Hlc Hu Hx1 k), (IH2 Hlc Hu Hx2 k). reflexivity.
  - (* fst *) rewrite (IH1 Hlc Hu Hx k). reflexivity.
  - (* snd *) rewrite (IH1 Hlc Hu Hx k). reflexivity.
  - (* inl *) rewrite (IH1 Hlc Hu Hx k). reflexivity.
  - (* inr *) rewrite (IH1 Hlc Hu Hx k). reflexivity.
  - (* case *)
    assert (Hx0 : ~ In x (fv t0)) by (intro H; apply Hx; simpl; repeat rewrite in_app_iff; auto).
    assert (Hx1 : ~ In x (fv b1)) by (intro H; apply Hx; simpl; repeat rewrite in_app_iff; auto).
    assert (Hx2 : ~ In x (fv b2)) by (intro H; apply Hx; simpl; repeat rewrite in_app_iff; auto).
    rewrite (IH0 Hlc Hu Hx0 k), (IH1 Hlc Hu Hx1 (S k)), (IH2 Hlc Hu Hx2 (S k)).
    reflexivity.
  - (* protect *) rewrite (IH1 Hlc Hu Hx k). reflexivity.
  - (* if *)
    assert (Hx0 : ~ In x (fv c)) by (intro H; apply Hx; simpl; repeat rewrite in_app_iff; auto).
    assert (Hx1 : ~ In x (fv yes)) by (intro H; apply Hx; simpl; repeat rewrite in_app_iff; auto).
    assert (Hx2 : ~ In x (fv no)) by (intro H; apply Hx; simpl; repeat rewrite in_app_iff; auto).
    rewrite (IHc Hlc Hu Hx0 k), (IHy Hlc Hu Hx1 k), (IHn Hlc Hu Hx2 k).
    reflexivity.
Qed.

Lemma subst_env_open : forall g x u body,
  env_lc g -> locally_closed u -> ~ In x (fv body) ->
  subst_env (update_env g x u) (open body (tm_fvar x)) =
  open (subst_env g body) u.
Proof.
  intros g x u body Hlc Hu Hx. unfold open.
  apply subst_env_open_rec; auto.
Qed.

Lemma premise_lc : forall L Gamma T1 body T,
  (forall x, ~ In x L -> has_type (update Gamma x T1) (open body (tm_fvar x)) T) ->
  lc_at 1 body.
Proof.
  intros L Gamma T1 body T Hty.
  pose proof (typing_lc _ _ _ (Hty (fresh L) (fresh_not_in L))) as Hlc.
  unfold locally_closed, open in Hlc.
  apply (proj2 (lc_at_open_fvar body 0 (fresh L))). exact Hlc.
Qed.

(* ---------- the logical relation ---------- *)

Fixpoint VR (o : label) (T : ty) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_Unit s =>
      flows_to s.(indirect_reader) o ->
      exists k1 k2, v1 = tm_unit k1 /\ v2 = tm_unit k2
  | Ty_Sum T1 T2 s =>
      flows_to s.(indirect_reader) o ->
      ((exists u1 u2 k1 k2,
          v1 = tm_inl u1 k1 /\ v2 = tm_inl u2 k2 /\ VR o T1 u1 u2)
       \/ (exists u1 u2 k1 k2,
          v1 = tm_inr u1 k1 /\ v2 = tm_inr u2 k2 /\ VR o T2 u1 u2))
  | Ty_Prod T1 T2 s =>
      flows_to s.(indirect_reader) o ->
      exists a1 b1 a2 b2 k1 k2,
        v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
        VR o T1 a1 a2 /\ VR o T2 b1 b2
  | Ty_Arrow T1 T2 s =>
      flows_to s.(indirect_reader) o ->
      forall (w1 w2 : tm) (r : label),
        value w1 -> value w2 ->
        flows_to s.(reader) r ->
        VR o T1 w1 w2 ->
        forall (z1 z2 : tm),
          evaluates (tm_app v1 w1 r) z1 ->
          evaluates (tm_app v2 w2 r) z2 ->
          VR o T2 z1 z2
  end.

Definition ER (o : label) (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, evaluates t1 v1 -> evaluates t2 v2 -> VR o T v1 v2.

Definition env_rel (o : label) (Gamma : context) (g1 g2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> ER o T (g1 x) (g2 x).

Lemma VR_ty_protect : forall o l T v1 v2,
  VR o T v1 v2 -> VR o (ty_protect l T) v1 v2.
Proof.
  intros o l T. destruct T; simpl; intros v1 v2 H.
  - (* Ty_Unit *) intros Hgate. apply H. revert Hgate.
    apply join_flows_to_inv_l.
  - (* Ty_Sum *) intros Hgate. apply H. revert Hgate.
    apply join_flows_to_inv_l.
  - (* Ty_Prod *) intros Hgate. apply H. revert Hgate.
    apply join_flows_to_inv_l.
  - (* Ty_Arrow *) intros Hgate w1 w2 r Hv1 Hv2 Hflow HVR z1 z2 He1 He2.
    assert (Hgate' : flows_to s.(indirect_reader) o).
    { revert Hgate. apply join_flows_to_inv_l. }
    assert (Hflow' : flows_to s.(reader) r).
    { revert Hflow. apply join_flows_to_inv_l. }
    exact (H Hgate' w1 w2 r Hv1 Hv2 Hflow' HVR z1 z2 He1 He2).
Qed.

Lemma VR_ty_protect_gated : forall o l T v1 v2,
  (flows_to (join (security_of T).(indirect_reader) l) o -> VR o T v1 v2) ->
  VR o (ty_protect l T) v1 v2.
Proof.
  intros o l T. destruct T; simpl; intros v1 v2 H Hgate.
  - (* Unit *) apply (H Hgate). revert Hgate. apply join_flows_to_inv_l.
  - (* Sum *) apply (H Hgate). revert Hgate. apply join_flows_to_inv_l.
  - (* Prod *) apply (H Hgate). revert Hgate. apply join_flows_to_inv_l.
  - (* Arrow *)
    intros w1 w2 r Hw1 Hw2 Hflow HVR z1 z2 He1 He2.
    assert (Hind : flows_to s.(indirect_reader) o).
    { revert Hgate. apply join_flows_to_inv_l. }
    assert (Hflow' : flows_to s.(reader) r).
    { revert Hflow. apply join_flows_to_inv_l. }
    exact (H Hgate Hind w1 w2 r Hw1 Hw2 Hflow' HVR z1 z2 He1 He2).
Qed.

Lemma VR_protect_value : forall o T v1 v2,
  value v1 -> value v2 ->
  VR o T v1 v2 ->
  forall l1 l2, VR o T (protect_value v1 l1) (protect_value v2 l2).
Proof.
  intros o T.
  induction T as [s | T1 IH1 T2 IH2 s | T1 IH1 T2 IH2 s | T1 IH1 T2 IH2 s];
  intros v1 v2 Hval1 Hval2 H l1 l2; simpl in *.
  - (* Ty_Unit *) intros Hgate.
    destruct (H Hgate) as (k1 & k2 & E1 & E2). subst.
    simpl. exists (protect_security k1 l1), (protect_security k2 l2).
    split; reflexivity.
  - (* Ty_Sum *) intros Hgate.
    destruct (H Hgate) as
      [(u1 & u2 & k1 & k2 & E1 & E2 & HR) | (u1 & u2 & k1 & k2 & E1 & E2 & HR)];
    subst; simpl.
    + left. exists u1, u2, (protect_security k1 l1), (protect_security k2 l2).
      repeat split; auto.
    + right. exists u1, u2, (protect_security k1 l1), (protect_security k2 l2).
      repeat split; auto.
  - (* Ty_Prod *) intros Hgate.
    destruct (H Hgate) as (a1 & b1 & a2 & b2 & k1 & k2 & E1 & E2 & HR1 & HR2); subst; simpl.
    exists a1, b1, a2, b2, (protect_security k1 l1), (protect_security k2 l2).
    repeat split; auto.
  - (* Ty_Arrow *)
    intros Hgate w1 w2 r Hw1 Hw2 Hflow HVR z1 z2 He1 He2.
    (* ----- side 1 ----- *)
    destruct He1 as (Hm1 & Hz1).
    destruct (multi_app _ _ Hm1 Hz1 _ _ _ eq_refl)
      as (Ta1 & ba1 & ka1 & va1 & Hma1 & Hva1 & Hb1 & Hvb1 & Hp1).
    assert (E1 : protect_value v1 l1 = tm_abs Ta1 ba1 ka1).
    { symmetry. eapply multi_value_inv.
      - apply value_protect_value; exact Hval1.
      - exact Hma1. }
    destruct (protect_value_abs_inv _ _ _ _ _ E1) as (T10 & b10 & k10 & Ev1 & ETa1 & Eba1 & Eka1).
    subst v1. subst Ta1. subst ba1. subst ka1.
    assert (Eva1 : va1 = w1).
    { eapply multi_value_inv; [exact Hw1 | exact Hb1]. }
    subst va1.
    (* ----- side 2 ----- *)
    destruct He2 as (Hm2 & Hz2).
    destruct (multi_app _ _ Hm2 Hz2 _ _ _ eq_refl)
      as (Ta2 & ba2 & ka2 & va2 & Hma2 & Hva2 & Hb2 & Hvb2 & Hp2).
    assert (E2 : protect_value v2 l2 = tm_abs Ta2 ba2 ka2).
    { symmetry. eapply multi_value_inv.
      - apply value_protect_value; exact Hval2.
      - exact Hma2. }
    destruct (protect_value_abs_inv _ _ _ _ _ E2) as (T20 & b20 & k20 & Ev2 & ETa2 & Eba2 & Eka2).
    subst v2. subst Ta2. subst ba2. subst ka2.
    assert (Eva2 : va2 = w2).
    { eapply multi_value_inv; [exact Hw2 | exact Hb2]. }
    subst va2.
    (* ----- flows and protect decompositions ----- *)
    assert (Hval1' : value (tm_abs T10 b10 (protect_security k10 l1))).
    { exact (value_protect_value (tm_abs T10 b10 k10) Hval1 l1). }
    assert (Hval2' : value (tm_abs T20 b20 (protect_security k20 l2))).
    { exact (value_protect_value (tm_abs T20 b20 k20) Hval2 l2). }
    assert (Hflow1' : flows_to (protect_security k10 l1).(reader) r).
    { eapply (proj1 (multi_app_abs_protect _ _ Hm1 Hz1 _ _ _ _ _ eq_refl Hw1 Hval1')). }
    assert (Hflow2' : flows_to (protect_security k20 l2).(reader) r).
    { eapply (proj1 (multi_app_abs_protect _ _ Hm2 Hz2 _ _ _ _ _ eq_refl Hw2 Hval2')). }
    assert (Hp1' : tm_protect (protect_security k10 l1).(indirect_reader)
                     (open b10 w1) -->* z1).
    { eapply (proj2 (multi_app_abs_protect _ _ Hm1 Hz1 _ _ _ _ _ eq_refl Hw1 Hval1')). }
    assert (Hp2' : tm_protect (protect_security k20 l2).(indirect_reader)
                     (open b20 w2) -->* z2).
    { eapply (proj2 (multi_app_abs_protect _ _ Hm2 Hz2 _ _ _ _ _ eq_refl Hw2 Hval2')). }
    assert (Hflow1 : flows_to k10.(reader) r).
    { revert Hflow1'. apply join_flows_to_inv_l. }
    assert (Hflow2 : flows_to k20.(reader) r).
    { revert Hflow2'. apply join_flows_to_inv_l. }
    destruct (multi_protect _ _ Hp1' Hz1 _ _ eq_refl) as (u1 & Hu1 & Hvu1 & Hz1eq).
    destruct (multi_protect _ _ Hp2' Hz2 _ _ eq_refl) as (u2 & Hu2 & Hvu2 & Hz2eq).
    (* ----- evaluations of the original applications ----- *)
    assert (Hev1 : evaluates (tm_app (tm_abs T10 b10 k10) w1 r)
                            (protect_value u1 k10.(indirect_reader))).
    { split.
      - eapply multi_step.
        + apply ST_AppAbs; [exact Hval1 | exact Hw1 | exact Hflow1].
        + eapply multi_trans.
          * apply multi_protect_congr. exact Hu1.
          * apply multi_protect_value. exact Hvu1.
      - apply value_protect_value. exact Hvu1. }
    assert (Hev2 : evaluates (tm_app (tm_abs T20 b20 k20) w2 r)
                            (protect_value u2 k20.(indirect_reader))).
    { split.
      - eapply multi_step.
        + apply ST_AppAbs; [exact Hval2 | exact Hw2 | exact Hflow2].
        + eapply multi_trans.
          * apply multi_protect_congr. exact Hu2.
          * apply multi_protect_value. exact Hvu2.
      - apply value_protect_value. exact Hvu2. }
    pose proof (H Hgate w1 w2 r Hw1 Hw2 Hflow HVR
                  (protect_value u1 k10.(indirect_reader))
                  (protect_value u2 k20.(indirect_reader)) Hev1 Hev2) as HR.
    pose proof (IH2 (protect_value u1 k10.(indirect_reader))
                    (protect_value u2 k20.(indirect_reader))
                    (value_protect_value _ Hvu1 _)
                    (value_protect_value _ Hvu2 _) HR l1 l2) as HR2.
    rewrite protect_value_compose in HR2.
    rewrite protect_value_compose in HR2.
    rewrite Hz1eq, Hz2eq.
    rewrite protect_security_indirect.
    rewrite protect_security_indirect.
    exact HR2.
Qed.

Lemma subtype_interp : forall T U, subtype T U ->
  forall o v1 v2, VR o T v1 v2 -> VR o U v1 v2.
Proof.
  intros T U Hsub.
  induction Hsub as
    [ kappa1 kappa2 Hwf1 Hwf2 Hle
    | T1 T2 U1 U2 kappa1 kappa2 Hs1 IH1 Hs2 IH2 Hwf1 Hwf2 Hle
    | T1 T2 U1 U2 kappa1 kappa2 Hs1 IH1 Hs2 IH2 Hwf1 Hwf2 Hle
    | T1 T2 U1 U2 kappa1 kappa2 Hs1 IH1 Hs2 IH2 Hwf1 Hwf2 Hle
    | T0 U0 V Hs1 IH1 Hs2 IH2 ];
  intros o v1 v2 HVR; simpl in *.
  - (* S_Unit *) intros Hgate. apply HVR.
    eapply flows_to_trans; [exact (proj2 Hle) | exact Hgate].
  - (* S_Sum *) intros Hgate.
    assert (Hg : flows_to kappa1.(indirect_reader) o).
    { eapply flows_to_trans; [exact (proj2 Hle) | exact Hgate]. }
    destruct (HVR Hg) as [(u1 & u2 & k1 & k2 & E1 & E2 & HR) | (u1 & u2 & k1 & k2 & E1 & E2 & HR)].
    + left. exists u1, u2, k1, k2. repeat split; try assumption.
      apply IH1. exact HR.
    + right. exists u1, u2, k1, k2. repeat split; try assumption.
      apply IH2. exact HR.
  - (* S_Prod *) intros Hgate.
    assert (Hg : flows_to kappa1.(indirect_reader) o).
    { eapply flows_to_trans; [exact (proj2 Hle) | exact Hgate]. }
    destruct (HVR Hg) as (a1 & b1 & a2 & b2 & k1 & k2 & E1 & E2 & HR1 & HR2).
    exists a1, b1, a2, b2, k1, k2. repeat split; try assumption.
    + apply IH1. exact HR1.
    + apply IH2. exact HR2.
  - (* S_Arrow *) intros Hgate w1 w2 r Hw1 Hw2 Hflow HVRu z1 z2 He1 He2.
    assert (Hg : flows_to kappa1.(indirect_reader) o).
    { eapply flows_to_trans; [exact (proj2 Hle) | exact Hgate]. }
    assert (Hflow1 : flows_to kappa1.(reader) r).
    { eapply flows_to_trans; [exact (proj1 Hle) | exact Hflow]. }
    assert (HVRt : VR o T1 w1 w2) by (apply IH1; exact HVRu).
    pose proof (HVR Hg w1 w2 r Hw1 Hw2 Hflow1 HVRt z1 z2 He1 He2) as HR.
    apply IH2. exact HR.
  - (* S_Trans *) apply IH2. apply IH1. exact HVR.
Qed.

Lemma ER_sub : forall o T U, subtype T U ->
  forall t1 t2, ER o T t1 t2 -> ER o U t1 t2.
Proof.
  intros o T U Hsub t1 t2 HER v1 v2 He1 He2.
  apply (subtype_interp _ _ Hsub o v1 v2).
  apply (HER v1 v2); auto.
Qed.

Lemma VR_to_ER : forall o T v1 v2,
  value v1 -> value v2 -> VR o T v1 v2 -> ER o T v1 v2.
Proof.
  intros o T v1 v2 Hv1 Hv2 HVR u1 u2 [Hm1 Hval1] [Hm2 Hval2].
  assert (E1 : u1 = v1) by (eapply multi_value_inv; eauto).
  assert (E2 : u2 = v2) by (eapply multi_value_inv; eauto).
  subst. exact HVR.
Qed.

Lemma ER_opaque : forall o T t1 t2,
  ~ flows_to (security_of T).(indirect_reader) o -> ER o T t1 t2.
Proof.
  intros o T t1 t2 Hnot v1 v2 He1 He2. destruct T; simpl in *;
  intros Hcontra; exfalso; apply Hnot; exact Hcontra.
Qed.

(* ---------- context lookup lemmas ---------- *)

Lemma lookup_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros Gamma x T; simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_update_neq : forall Gamma x y T,
  x <> y -> lookup_context x (update Gamma y T) = lookup_context x Gamma.
Proof.
  intros Gamma x y T Hxy; simpl.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; contradiction.
  - reflexivity.
Qed.

Lemma lookup_update_some : forall Gamma x y T U,
  lookup_context x (update Gamma y T) = Some U ->
  (x = y /\ U = T) \/ (x <> y /\ lookup_context x Gamma = Some U).
Proof.
  intros Gamma x y T U H; simpl in H.
  destruct (Nat.eqb x y) eqn:E.
  - left. apply Nat.eqb_eq in E. inversion H; subst. auto.
  - right. apply Nat.eqb_neq in E. auto.
Qed.

Lemma env_rel_update : forall o Gamma g1 g2 x T w1 w2,
  env_rel o Gamma g1 g2 -> ER o T w1 w2 ->
  env_rel o (update Gamma x T) (update_env g1 x w1) (update_env g2 x w2).
Proof.
  intros o Gamma g1 g2 x T w1 w2 Hrel Hw y U Hlook.
  destruct (lookup_update_some Gamma y x T U Hlook) as [[E1 E2] | [E1 E2]].
  - subst. unfold update_env. rewrite Nat.eqb_refl. exact Hw.
  - unfold update_env. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + apply Hrel with (x := y) (T := U). exact E2.
Qed.

Theorem fundamental : forall Gamma t T, has_type Gamma t T ->
  forall o (g1 g2 : atom -> tm),
    env_rel o Gamma g1 g2 -> env_lc g1 -> env_lc g2 ->
    ER o T (subst_env g1 t) (subst_env g2 t).
Proof.
  intros Gamma t T H.
  induction H as
    [ Gamma0 x T0 Hlook Hwf
    | Gamma0 kappa0 Hwf
    | L Gamma0 T1 body T2 kappa0 Hwf1 Hwf2 Hty HIH
    | Gamma0 t1 t2 T1 T2 kappa0 r0 Hty1 IH1 Hty2 IH2 Hflow
    | Gamma0 t1 t2 T1 T2 kappa0 Hty1 IH1 Hty2 IH2 Hwf
    | Gamma0 t0 T1 T2 kappa0 r0 Hty IH Hflow
    | Gamma0 t0 T1 T2 kappa0 r0 Hty IH Hflow
    | Gamma0 t0 T1 T2 kappa0 Hty IH HwfT2 Hwfkappa
    | Gamma0 t0 T1 T2 kappa0 HwfT1 Hty IH Hwfkappa
    | L Gamma0 t0 body1 body2 T1 T2 TT kappa0 r0 Hty0 IH0 Hflow Hty1 IH1 Hty2 IH2
    | Gamma0 t0 TT l0 Hty IH
    | Gamma0 t0 TT UU Hty IH Hsub
    | Gamma0 c0 yes0 no0 k0 TT r0 Htyc IHc Htyy IHy Htyn IHn Hflow ];
  intros o g1 g2 Hrel Hlc1 Hlc2.
  - (* T_Var *) simpl. apply Hrel. exact Hlook.
  - (* T_Unit *)
    unfold ER. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    assert (E1 : v1 = tm_unit kappa0) by (eapply multi_unit; [exact Hm1 | reflexivity]).
    assert (E2 : v2 = tm_unit kappa0) by (eapply multi_unit; [exact Hm2 | reflexivity]).
    subst v1 v2. intros Hgate. exists kappa0, kappa0. split; reflexivity.
  - (* T_Abs *)
    unfold ER. intros z1 z2 [Hm1 Hz1] [Hm2 Hz2].
    assert (Hlcbody : lc_at 1 body) by (eapply premise_lc; eauto).
    assert (Hval1 : value (tm_abs T1 (subst_env g1 body) kappa0)).
    { apply v_abs. apply lc_at_subst_env; [exact Hlc1 | exact Hlcbody]. }
    assert (Hval2 : value (tm_abs T1 (subst_env g2 body) kappa0)).
    { apply v_abs. apply lc_at_subst_env; [exact Hlc2 | exact Hlcbody]. }
    assert (Ez1 : z1 = tm_abs T1 (subst_env g1 body) kappa0).
    { eapply multi_abs; [exact Hm1 | reflexivity]. }
    assert (Ez2 : z2 = tm_abs T1 (subst_env g2 body) kappa0).
    { eapply multi_abs; [exact Hm2 | reflexivity]. }
    subst z1 z2. simpl.
    intros Hgate w1 w2 r1 Hw1 Hw2 Hflow1 HVR u1 u2 He1 He2.
    set (x := fresh (L ++ fv body)).
    assert (HxL : ~ In x L).
    { intro Hc. apply fresh_not_in with (L ++ fv body). apply in_app_iff. auto. }
    assert (Hxb : ~ In x (fv body)).
    { intro Hc. apply fresh_not_in with (L ++ fv body). apply in_app_iff. auto. }
    assert (Hrel' : env_rel o (update Gamma0 x T1) (update_env g1 x w1) (update_env g2 x w2)).
    { apply env_rel_update; [exact Hrel | apply VR_to_ER; auto]. }
    assert (Hlc1' : env_lc (update_env g1 x w1)).
    { apply env_lc_update; [exact Hlc1 | apply value_locally_closed; exact Hw1]. }
    assert (Hlc2' : env_lc (update_env g2 x w2)).
    { apply env_lc_update; [exact Hlc2 | apply value_locally_closed; exact Hw2]. }
    pose proof (HIH x HxL o (update_env g1 x w1) (update_env g2 x w2) Hrel' Hlc1' Hlc2') as Hbody.
    rewrite subst_env_open in Hbody;
      [| exact Hlc1 | apply value_locally_closed; exact Hw1 | exact Hxb].
    rewrite subst_env_open in Hbody;
      [| exact Hlc2 | apply value_locally_closed; exact Hw2 | exact Hxb].
    destruct (multi_app_abs_protect _ _ (proj1 He1) (proj2 He1) T1 (subst_env g1 body) kappa0 w1 r1 eq_refl Hw1 Hval1)
      as (Hfl1 & Hp1).
    destruct (multi_app_abs_protect _ _ (proj1 He2) (proj2 He2) T1 (subst_env g2 body) kappa0 w2 r1 eq_refl Hw2 Hval2)
      as (Hfl2 & Hp2).
    destruct (multi_protect _ _ Hp1 (proj2 He1) _ _ eq_refl) as (a1 & Ha1 & Hva1 & Eu1).
    destruct (multi_protect _ _ Hp2 (proj2 He2) _ _ eq_refl) as (a2 & Ha2 & Hva2 & Eu2).
    rewrite Eu1, Eu2.
    apply VR_protect_value; auto.
    apply (Hbody _ _ (conj Ha1 Hva1) (conj Ha2 Hva2)).
  - (* T_App *)
    unfold ER. intros z1 z2 He1 He2.
    destruct He1 as [Hm1 Hz1]; destruct He2 as [Hm2 Hz2].
    destruct (multi_app _ _ Hm1 Hz1 _ _ _ eq_refl)
      as (Tabs1 & b1 & k1 & v1 & Hf1 & Hvf1 & Ha1 & Hva1 & Hfl1 & Hp1).
    destruct (multi_app _ _ Hm2 Hz2 _ _ _ eq_refl)
      as (Tabs2 & b2 & k2 & v2 & Hf2 & Hvf2 & Ha2 & Hva2 & Hfl2 & Hp2).
    pose proof (IH1 o g1 g2 Hrel Hlc1 Hlc2 _ _ (conj Hf1 Hvf1) (conj Hf2 Hvf2)) as HVRfun.
    pose proof (IH2 o g1 g2 Hrel Hlc1 Hlc2 _ _ (conj Ha1 Hva1) (conj Ha2 Hva2)) as HVRarg.
    assert (Hev1 : evaluates (tm_app (tm_abs Tabs1 b1 k1) v1 r0) z1).
    { split; [| exact Hz1]. eapply multi_step; [| exact Hp1].
      apply ST_AppAbs; auto. }
    assert (Hev2 : evaluates (tm_app (tm_abs Tabs2 b2 k2) v2 r0) z2).
    { split; [| exact Hz2]. eapply multi_step; [| exact Hp2].
      apply ST_AppAbs; auto. }
    apply VR_ty_protect_gated. intros Hgate.
    assert (Hk : flows_to kappa0.(indirect_reader) o).
    { revert Hgate. apply join_flows_to_inv_r. }
    exact (HVRfun Hk v1 v2 r0 Hva1 Hva2 Hflow HVRarg z1 z2 Hev1 Hev2).
  - (* T_Pair *)
    unfold ER. intros z1 z2 He1 He2.
    destruct He1 as [Hm1 Hz1]; destruct He2 as [Hm2 Hz2].
    destruct (multi_pair _ _ Hm1 Hz1 _ _ _ eq_refl) as (v1 & v2 & Hp1 & Hp2 & Hv1 & Hv2 & Ez1).
    destruct (multi_pair _ _ Hm2 Hz2 _ _ _ eq_refl) as (w1 & w2 & Hq1 & Hq2 & Hw1 & Hw2 & Ez2).
    subst z1 z2. intros Hgate.
    exists v1, v2, w1, w2, kappa0, kappa0. repeat split; try reflexivity.
    + apply (IH1 o g1 g2 Hrel Hlc1 Hlc2 _ _ (conj Hp1 Hv1) (conj Hq1 Hw1)).
    + apply (IH2 o g1 g2 Hrel Hlc1 Hlc2 _ _ (conj Hp2 Hv2) (conj Hq2 Hw2)).
  - (* T_Fst *)
    unfold ER. intros z1 z2 He1 He2.
    destruct He1 as [Hm1 Hz1]; destruct He2 as [Hm2 Hz2].
    destruct (multi_fst _ _ Hm1 Hz1 _ _ eq_refl) as (v1 & v2 & k1 & Hp1 & Hv1 & Hv2 & Hpr1).
    destruct (multi_fst _ _ Hm2 Hz2 _ _ eq_refl) as (w1 & w2 & k2 & Hp2 & Hw1 & Hw2 & Hpr2).
    pose proof (IH o g1 g2 Hrel Hlc1 Hlc2 _ _
                  (conj Hp1 (v_pair v1 v2 k1 Hv1 Hv2))
                  (conj Hp2 (v_pair w1 w2 k2 Hw1 Hw2))) as HVRpair.
    apply VR_ty_protect_gated. intros Hgate.
    assert (Hk : flows_to kappa0.(indirect_reader) o).
    { revert Hgate. apply join_flows_to_inv_r. }
    destruct (multi_protect _ _ Hpr1 Hz1 _ _ eq_refl) as (a1 & Ha1 & Hva1 & Ez1).
    destruct (multi_protect _ _ Hpr2 Hz2 _ _ eq_refl) as (a2 & Ha2 & Hva2 & Ez2).
    assert (Ea1 : a1 = v1) by (eapply multi_value_inv; eauto).
    assert (Ea2 : a2 = w1) by (eapply multi_value_inv; eauto).
    subst a1 a2. rewrite Ez1, Ez2.
    destruct (HVRpair Hk) as (p1 & q1 & p2 & q2 & ka & kb & Ep1 & Ep2 & HR1 & HR2).
    inversion Ep1; subst. inversion Ep2; subst.
    apply VR_protect_value; auto.
  - (* T_Snd *)
    unfold ER. intros z1 z2 He1 He2.
    destruct He1 as [Hm1 Hz1]; destruct He2 as [Hm2 Hz2].
    destruct (multi_snd _ _ Hm1 Hz1 _ _ eq_refl) as (v1 & v2 & k1 & Hp1 & Hv1 & Hv2 & Hpr1).
    destruct (multi_snd _ _ Hm2 Hz2 _ _ eq_refl) as (w1 & w2 & k2 & Hp2 & Hw1 & Hw2 & Hpr2).
    pose proof (IH o g1 g2 Hrel Hlc1 Hlc2 _ _
                  (conj Hp1 (v_pair v1 v2 k1 Hv1 Hv2))
                  (conj Hp2 (v_pair w1 w2 k2 Hw1 Hw2))) as HVRpair.
    apply VR_ty_protect_gated. intros Hgate.
    assert (Hk : flows_to kappa0.(indirect_reader) o).
    { revert Hgate. apply join_flows_to_inv_r. }
    destruct (multi_protect _ _ Hpr1 Hz1 _ _ eq_refl) as (a1 & Ha1 & Hva1 & Ez1).
    destruct (multi_protect _ _ Hpr2 Hz2 _ _ eq_refl) as (a2 & Ha2 & Hva2 & Ez2).
    assert (Ea1 : a1 = v2) by (eapply multi_value_inv; eauto).
    assert (Ea2 : a2 = w2) by (eapply multi_value_inv; eauto).
    subst a1 a2. rewrite Ez1, Ez2.
    destruct (HVRpair Hk) as (p1 & q1 & p2 & q2 & ka & kb & Ep1 & Ep2 & HR1 & HR2).
    inversion Ep1; subst. inversion Ep2; subst.
    apply VR_protect_value; auto.
  - (* T_Inl *)
    unfold ER. intros z1 z2 He1 He2.
    destruct He1 as [Hm1 Hz1]; destruct He2 as [Hm2 Hz2].
    destruct (multi_inl _ _ Hm1 Hz1 _ _ eq_refl) as (v1 & Hp1 & Hv1 & Ez1).
    destruct (multi_inl _ _ Hm2 Hz2 _ _ eq_refl) as (v2 & Hp2 & Hv2 & Ez2).
    subst z1 z2. intros Hgate. left.
    exists v1, v2, kappa0, kappa0. repeat split; try reflexivity.
    apply (IH o g1 g2 Hrel Hlc1 Hlc2 _ _ (conj Hp1 Hv1) (conj Hp2 Hv2)).
  - (* T_Inr *)
    unfold ER. intros z1 z2 He1 He2.
    destruct He1 as [Hm1 Hz1]; destruct He2 as [Hm2 Hz2].
    destruct (multi_inr _ _ Hm1 Hz1 _ _ eq_refl) as (v1 & Hp1 & Hv1 & Ez1).
    destruct (multi_inr _ _ Hm2 Hz2 _ _ eq_refl) as (v2 & Hp2 & Hv2 & Ez2).
    subst z1 z2. intros Hgate. right.
    exists v1, v2, kappa0, kappa0. repeat split; try reflexivity.
    apply (IH o g1 g2 Hrel Hlc1 Hlc2 _ _ (conj Hp1 Hv1) (conj Hp2 Hv2)).
  - (* T_Case *)
    unfold ER. intros z1 z2 He1 He2.
    destruct He1 as [Hm1 Hz1]; destruct He2 as [Hm2 Hz2].
    destruct (multi_case _ _ Hm1 Hz1 _ _ _ _ eq_refl) as
      [(v1 & k1 & Hc1 & Hv1 & Hp1) | (v1 & k1 & Hc1 & Hv1 & Hp1)];
    destruct (multi_case _ _ Hm2 Hz2 _ _ _ _ eq_refl) as
      [(v2 & k2 & Hc2 & Hv2 & Hp2) | (v2 & k2 & Hc2 & Hv2 & Hp2)].
    + (* left / left *)
      apply VR_ty_protect_gated. intros Hgate.
      assert (Hk : flows_to kappa0.(indirect_reader) o).
      { revert Hgate. apply join_flows_to_inv_r. }
      pose proof (IH0 o g1 g2 Hrel Hlc1 Hlc2 _ _
                    (conj Hc1 (v_inl v1 k1 Hv1)) (conj Hc2 (v_inl v2 k2 Hv2)) Hk) as Hs.
      destruct Hs as [(p1 & p2 & ka & kb & E1 & E2 & HRp) | (p1 & p2 & ka & kb & E1 & E2 & HRp)].
      * inversion E1; subst. inversion E2; subst.
        set (x := fresh (L ++ fv body1)).
        assert (HxL : ~ In x L).
        { intro Hc. apply fresh_not_in with (L ++ fv body1). apply in_app_iff. auto. }
        assert (Hxb : ~ In x (fv body1)).
        { intro Hc. apply fresh_not_in with (L ++ fv body1). apply in_app_iff. auto. }
        assert (Hrel' : env_rel o (update Gamma0 x T1) (update_env g1 x p1) (update_env g2 x p2)).
        { apply env_rel_update; [exact Hrel | apply VR_to_ER; auto]. }
        assert (Hlc1' : env_lc (update_env g1 x p1)).
        { apply env_lc_update; [exact Hlc1 | apply value_locally_closed; exact Hv1]. }
        assert (Hlc2' : env_lc (update_env g2 x p2)).
        { apply env_lc_update; [exact Hlc2 | apply value_locally_closed; exact Hv2]. }
        pose proof (IH1 x HxL o (update_env g1 x p1) (update_env g2 x p2) Hrel' Hlc1' Hlc2') as Hbody.
        rewrite subst_env_open in Hbody;
          [| exact Hlc1 | apply value_locally_closed; exact Hv1 | exact Hxb].
        rewrite subst_env_open in Hbody;
          [| exact Hlc2 | apply value_locally_closed; exact Hv2 | exact Hxb].
        destruct (multi_protect _ _ Hp1 Hz1 _ _ eq_refl) as (a1 & Ha1 & Hva1 & Ez1).
        destruct (multi_protect _ _ Hp2 Hz2 _ _ eq_refl) as (a2 & Ha2 & Hva2 & Ez2).
        rewrite Ez1, Ez2.
        apply VR_protect_value; auto.
        apply (Hbody _ _ (conj Ha1 Hva1) (conj Ha2 Hva2)).
      * exfalso. discriminate E1.
    + (* left / right *)
      apply VR_ty_protect_gated. intros Hgate.
      assert (Hk : flows_to kappa0.(indirect_reader) o).
      { revert Hgate. apply join_flows_to_inv_r. }
      pose proof (IH0 o g1 g2 Hrel Hlc1 Hlc2 _ _
                    (conj Hc1 (v_inl v1 k1 Hv1)) (conj Hc2 (v_inr v2 k2 Hv2)) Hk) as Hs.
      destruct Hs as [(p1 & p2 & ka & kb & E1 & E2 & HRp) | (p1 & p2 & ka & kb & E1 & E2 & HRp)].
      * exfalso. discriminate E2.
      * exfalso. discriminate E1.
    + (* right / left *)
      apply VR_ty_protect_gated. intros Hgate.
      assert (Hk : flows_to kappa0.(indirect_reader) o).
      { revert Hgate. apply join_flows_to_inv_r. }
      pose proof (IH0 o g1 g2 Hrel Hlc1 Hlc2 _ _
                    (conj Hc1 (v_inr v1 k1 Hv1)) (conj Hc2 (v_inl v2 k2 Hv2)) Hk) as Hs.
      destruct Hs as [(p1 & p2 & ka & kb & E1 & E2 & HRp) | (p1 & p2 & ka & kb & E1 & E2 & HRp)].
      * exfalso. discriminate E1.
      * exfalso. discriminate E2.
    + (* right / right *)
      apply VR_ty_protect_gated. intros Hgate.
      assert (Hk : flows_to kappa0.(indirect_reader) o).
      { revert Hgate. apply join_flows_to_inv_r. }
      pose proof (IH0 o g1 g2 Hrel Hlc1 Hlc2 _ _
                    (conj Hc1 (v_inr v1 k1 Hv1)) (conj Hc2 (v_inr v2 k2 Hv2)) Hk) as Hs.
      destruct Hs as [(p1 & p2 & ka & kb & E1 & E2 & HRp) | (p1 & p2 & ka & kb & E1 & E2 & HRp)].
      * exfalso. discriminate E1.
      * inversion E1; subst. inversion E2; subst.
        set (x := fresh (L ++ fv body2)).
        assert (HxL : ~ In x L).
        { intro Hc. apply fresh_not_in with (L ++ fv body2). apply in_app_iff. auto. }
        assert (Hxb : ~ In x (fv body2)).
        { intro Hc. apply fresh_not_in with (L ++ fv body2). apply in_app_iff. auto. }
        assert (Hrel' : env_rel o (update Gamma0 x T2) (update_env g1 x p1) (update_env g2 x p2)).
        { apply env_rel_update; [exact Hrel | apply VR_to_ER; auto]. }
        assert (Hlc1' : env_lc (update_env g1 x p1)).
        { apply env_lc_update; [exact Hlc1 | apply value_locally_closed; exact Hv1]. }
        assert (Hlc2' : env_lc (update_env g2 x p2)).
        { apply env_lc_update; [exact Hlc2 | apply value_locally_closed; exact Hv2]. }
        pose proof (IH2 x HxL o (update_env g1 x p1) (update_env g2 x p2) Hrel' Hlc1' Hlc2') as Hbody.
        rewrite subst_env_open in Hbody;
          [| exact Hlc1 | apply value_locally_closed; exact Hv1 | exact Hxb].
        rewrite subst_env_open in Hbody;
          [| exact Hlc2 | apply value_locally_closed; exact Hv2 | exact Hxb].
        destruct (multi_protect _ _ Hp1 Hz1 _ _ eq_refl) as (a1 & Ha1 & Hva1 & Ez1).
        destruct (multi_protect _ _ Hp2 Hz2 _ _ eq_refl) as (a2 & Ha2 & Hva2 & Ez2).
        rewrite Ez1, Ez2.
        apply VR_protect_value; auto.
        apply (Hbody _ _ (conj Ha1 Hva1) (conj Ha2 Hva2)).
  - (* T_Protect *)
    unfold ER. intros z1 z2 He1 He2.
    destruct He1 as [Hm1 Hz1]; destruct He2 as [Hm2 Hz2].
    destruct (multi_protect _ _ Hm1 Hz1 _ _ eq_refl) as (v1 & Hp1 & Hv1 & Ez1).
    destruct (multi_protect _ _ Hm2 Hz2 _ _ eq_refl) as (v2 & Hp2 & Hv2 & Ez2).
    rewrite Ez1, Ez2.
    apply VR_ty_protect.
    apply VR_protect_value; auto.
    apply (IH o g1 g2 Hrel Hlc1 Hlc2 _ _ (conj Hp1 Hv1) (conj Hp2 Hv2)).
  - (* T_Sub *)
    apply ER_sub with (T := TT). exact Hsub.
    apply IH; auto.
  - (* T_If *)
    unfold ER. intros z1 z2 He1 He2.
    destruct He1 as [Hm1 Hz1]; destruct He2 as [Hm2 Hz2].
    destruct (multi_if _ _ Hm1 Hz1 _ _ _ _ eq_refl) as
      [(v1 & k1 & Hc1 & Hv1 & Hp1) | (v1 & k1 & Hc1 & Hv1 & Hp1)];
    destruct (multi_if _ _ Hm2 Hz2 _ _ _ _ eq_refl) as
      [(v2 & k2 & Hc2 & Hv2 & Hp2) | (v2 & k2 & Hc2 & Hv2 & Hp2)].
    + (* both select yes *)
      apply VR_ty_protect_gated. intros Hgate.
      assert (Hk : flows_to k0.(indirect_reader) o).
      { revert Hgate. apply join_flows_to_inv_r. }
      pose proof (IHc o g1 g2 Hrel Hlc1 Hlc2 _ _
                    (conj Hc1 (v_inl v1 k1 Hv1)) (conj Hc2 (v_inl v2 k2 Hv2)) Hk) as Hs.
      destruct Hs as [(p1 & p2 & ka & kb & E1 & E2 & HRp) | (p1 & p2 & ka & kb & E1 & E2 & HRp)].
      * inversion E1. inversion E2.
        destruct (multi_protect _ _ Hp1 Hz1 _ _ eq_refl) as (a1 & Ha1 & Hva1 & Ez1).
        destruct (multi_protect _ _ Hp2 Hz2 _ _ eq_refl) as (a2 & Ha2 & Hva2 & Ez2).
        rewrite Ez1, Ez2.
        apply VR_protect_value; auto.
        apply (IHy o g1 g2 Hrel Hlc1 Hlc2 _ _ (conj Ha1 Hva1) (conj Ha2 Hva2)).
      * exfalso. discriminate E1.
    + (* yes / no *)
      apply VR_ty_protect_gated. intros Hgate.
      assert (Hk : flows_to k0.(indirect_reader) o).
      { revert Hgate. apply join_flows_to_inv_r. }
      pose proof (IHc o g1 g2 Hrel Hlc1 Hlc2 _ _
                    (conj Hc1 (v_inl v1 k1 Hv1)) (conj Hc2 (v_inr v2 k2 Hv2)) Hk) as Hs.
      destruct Hs as [(p1 & p2 & ka & kb & E1 & E2 & HRp) | (p1 & p2 & ka & kb & E1 & E2 & HRp)].
      * exfalso. discriminate E2.
      * exfalso. discriminate E1.
    + (* no / yes *)
      apply VR_ty_protect_gated. intros Hgate.
      assert (Hk : flows_to k0.(indirect_reader) o).
      { revert Hgate. apply join_flows_to_inv_r. }
      pose proof (IHc o g1 g2 Hrel Hlc1 Hlc2 _ _
                    (conj Hc1 (v_inr v1 k1 Hv1)) (conj Hc2 (v_inl v2 k2 Hv2)) Hk) as Hs.
      destruct Hs as [(p1 & p2 & ka & kb & E1 & E2 & HRp) | (p1 & p2 & ka & kb & E1 & E2 & HRp)].
      * exfalso. discriminate E1.
      * exfalso. discriminate E2.
    + (* both select no *)
      apply VR_ty_protect_gated. intros Hgate.
      assert (Hk : flows_to k0.(indirect_reader) o).
      { revert Hgate. apply join_flows_to_inv_r. }
      pose proof (IHc o g1 g2 Hrel Hlc1 Hlc2 _ _
                    (conj Hc1 (v_inr v1 k1 Hv1)) (conj Hc2 (v_inr v2 k2 Hv2)) Hk) as Hs.
      destruct Hs as [(p1 & p2 & ka & kb & E1 & E2 & HRp) | (p1 & p2 & ka & kb & E1 & E2 & HRp)].
      * exfalso. discriminate E1.
      * inversion E1. inversion E2.
        destruct (multi_protect _ _ Hp1 Hz1 _ _ eq_refl) as (a1 & Ha1 & Hva1 & Ez1).
        destruct (multi_protect _ _ Hp2 Hz2 _ _ eq_refl) as (a2 & Ha2 & Hva2 & Ez2).
        rewrite Ez1, Ez2.
        apply VR_protect_value; auto.
        apply (IHn o g1 g2 Hrel Hlc1 Hlc2 _ _ (conj Ha1 Hva1) (conj Ha2 Hva2)).
Qed.

(* ---------- the erasure lemma and the main theorem ---------- *)

Lemma VR_erase : forall (o : label) (kappa : security) T,
  transparent_at kappa T -> ground T ->
  flows_to kappa.(indirect_reader) o ->
  forall v1 v2, VR o T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  intros o kappa T.
  induction T as [s | T1 IH1 T2 IH2 s | T1 IH1 T2 IH2 s | T1 IH1 T2 IH2 s];
  intros Htr Hg Hgate v1 v2 HVR; simpl in *.
  - (* Unit *)
    destruct Htr as [Hle _].
    destruct (HVR (flows_to_trans _ _ _ (proj2 Hle) Hgate)) as (k1 & k2 & E1 & E2).
    subst. reflexivity.
  - (* Sum *)
    destruct Htr as [Hle [Htr1 Htr2]].
    destruct Hg as [Hg1 Hg2].
    destruct (HVR (flows_to_trans _ _ _ (proj2 Hle) Hgate)) as
      [(u1 & u2 & k1 & k2 & E1 & E2 & HR) | (u1 & u2 & k1 & k2 & E1 & E2 & HR)];
      subst; simpl; f_equal; eauto.
  - (* Prod *)
    destruct Htr as [Hle [Htr1 Htr2]].
    destruct Hg as [Hg1 Hg2].
    destruct (HVR (flows_to_trans _ _ _ (proj2 Hle) Hgate)) as
      (a1 & b1 & a2 & b2 & k1 & k2 & E1 & E2 & HR1 & HR2);
      subst; simpl; f_equal; eauto.
  - (* Arrow *) destruct Hg.
Qed.

Lemma same_result_of_ER : forall (o : label) T t1 t2,
  ground T -> transparent T -> flows_to (security_of T).(indirect_reader) o ->
  ER o T t1 t2 -> same_result t1 t2.
Proof.
  intros o T t1 t2 Hg Htr Hgate HER v1 v2 He1 He2.
  apply (VR_erase o (security_of T) T Htr Hg Hgate).
  apply (HER v1 v2); auto.
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 Hctx Hg Htr Hni.
  destruct Hctx as (L & Hctx).
  set (x := fresh (L ++ fv_ctx C ++ fv t1 ++ fv t2)).
  assert (HxL : ~ In x L).
  { intro Hc. apply fresh_not_in with (L ++ fv_ctx C ++ fv t1 ++ fv t2).
    repeat rewrite in_app_iff. tauto. }
  assert (HxC : ~ In x (fv_ctx C)).
  { intro Hc. apply fresh_not_in with (L ++ fv_ctx C ++ fv t1 ++ fv t2).
    repeat rewrite in_app_iff. tauto. }
  set (g1 := update_env (fun y => tm_fvar y) x t1).
  set (g2 := update_env (fun y => tm_fvar y) x t2).
  assert (Hrel : env_rel (security_of T_result).(indirect_reader)
                   (update empty x T_secret) g1 g2).
  { intros y U Hlook.
    destruct (lookup_update_some empty y x T_secret U Hlook) as [[E1 E2] | [E1 E2]].
    - subst y. subst U. unfold g1, g2, update_env.
      change (ER (indirect_reader (security_of T_result)) T_secret
                (if Nat.eqb x x then t1 else tm_fvar x)
                (if Nat.eqb x x then t2 else tm_fvar x)).
      rewrite Nat.eqb_refl.
      apply ER_opaque. exact Hni.
    - simpl in E2. discriminate E2. }
  assert (Hlc1 : env_lc g1).
  { intros y. unfold g1, update_env. destruct (Nat.eqb y x) eqn:E.
    - apply typing_lc in Ht1. exact Ht1.
    - simpl. exact I. }
  assert (Hlc2 : env_lc g2).
  { intros y. unfold g2, update_env. destruct (Nat.eqb y x) eqn:E.
    - apply typing_lc in Ht2. exact Ht2.
    - simpl. exact I. }
  pose proof (fundamental (update empty x T_secret) (plug C (tm_fvar x)) T_result
                (Hctx x HxL) (security_of T_result).(indirect_reader) g1 g2
                Hrel Hlc1 Hlc2) as HER.
  subst g1. subst g2.
  rewrite subst_env_plug_fresh in HER; [| exact HxC].
  rewrite subst_env_plug_fresh in HER; [| exact HxC].
  exact (same_result_of_ER (security_of T_result).(indirect_reader) T_result
           (plug C t1) (plug C t2) Hg Htr (flows_to_refl _) HER).
Qed.
