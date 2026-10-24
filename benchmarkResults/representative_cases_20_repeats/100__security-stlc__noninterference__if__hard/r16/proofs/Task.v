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

(* ============================================================== *)
(* Basic lemmas about labels and security levels                   *)
(* ============================================================== *)

Lemma flows_to_refl : forall l : label, flows_to l l.
Proof. destruct l; simpl; exact I. Qed.

Lemma flows_to_trans : forall l1 l2 l3 : label,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof. destruct l1, l2, l3; simpl in *; auto; contradiction. Qed.

Lemma security_le_refl : forall k : security, security_le k k.
Proof. intros [r i]; simpl; split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3 : security,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3]; simpl; intros [H1 H2] [H3 H4].
  split; eapply flows_to_trans; eauto.
Qed.

Lemma security_le_reader_flow : forall (ka kb : security) (r : label),
  security_le ka kb -> flows_to kb.(reader) r -> flows_to ka.(reader) r.
Proof.
  intros [ra ia] [rb ib] r [Hr Hi] Hf; simpl in *.
  eapply flows_to_trans; eauto.
Qed.

Lemma security_le_ind_low : forall ka kb : security,
  security_le ka kb -> flows_to kb.(indirect_reader) Low ->
  ka.(indirect_reader) = Low.
Proof.
  intros [ra ia] [rb ib] [Hr Hi] Hf; simpl in *.
  destruct ia; auto.
  exfalso. exact (flows_to_trans _ _ _ Hi Hf).
Qed.

Lemma join_low_r : forall l : label, join l Low = l.
Proof. destruct l; reflexivity. Qed.
Lemma join_low_l : forall l : label, join Low l = l.
Proof. destruct l; reflexivity. Qed.
Lemma join_high_r : forall l : label, join l High = High.
Proof. destruct l; reflexivity. Qed.
Lemma join_high_l : forall l : label, join High l = High.
Proof. destruct l; reflexivity. Qed.

Lemma protect_security_low : forall k : security, protect_security k Low = k.
Proof. intros [r i]; destruct r, i; reflexivity. Qed.

Lemma protect_security_high_ind : forall k : security,
  (protect_security k High).(indirect_reader) = High.
Proof. intros [r i]; destruct i; reflexivity. Qed.

Lemma ty_protect_low : forall T : ty, ty_protect Low T = T.
Proof.
  intros T; destruct T; simpl; rewrite protect_security_low; reflexivity.
Qed.

Lemma ty_protect_high_ind : forall T : ty,
  (security_of (ty_protect High T)).(indirect_reader) = High.
Proof.
  intros T; destruct T; simpl; rewrite join_high_r; reflexivity.
Qed.

(* ============================================================== *)
(* Lemmas about values                                             *)
(* ============================================================== *)

Lemma value_lc : forall v : tm, value v -> locally_closed v.
Proof.
  induction 1; simpl.
  - exact I.
  - assumption.
  - split; assumption.
  - assumption.
  - assumption.
Qed.

Lemma value_no_step : forall v : tm, value v -> forall u, ~ step v u.
Proof.
  intros v Hv.
  induction Hv as [kappa | T body kappa Hlc
                 | v1 v2 kappa Hv1 IH1 Hv2 IH2
                 | v kappa Hv IH | v kappa Hv IH]; intros u Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
  - inversion Hstep; subst. eapply IH; eauto.
  - inversion Hstep; subst. eapply IH; eauto.
Qed.

Lemma value_inv_pair : forall a b k, value (tm_pair a b k) -> value a /\ value b.
Proof. intros a b k H; inversion H; subst; auto. Qed.

Lemma value_inv_inl : forall a k, value (tm_inl a k) -> value a.
Proof. intros a k H; inversion H; subst; auto. Qed.

Lemma value_inv_inr : forall a k, value (tm_inr a k) -> value a.
Proof. intros a k H; inversion H; subst; auto. Qed.

Lemma value_inv_abs_lc : forall T body k,
  value (tm_abs T body k) -> locally_closed (tm_abs T body k).
Proof. intros T body k H; inversion H; subst; auto. Qed.

Lemma value_no_app : forall a b r, value (tm_app a b r) -> False.
Proof. intros; inversion H. Qed.

Lemma value_no_case : forall a b c r, value (tm_case a b c r) -> False.
Proof. intros; inversion H. Qed.

Lemma value_no_fst : forall a r, value (tm_fst a r) -> False.
Proof. intros; inversion H. Qed.

Lemma value_no_snd : forall a r, value (tm_snd a r) -> False.
Proof. intros; inversion H. Qed.

Lemma value_no_if : forall a b c r, value (tm_if a b c r) -> False.
Proof. intros; inversion H. Qed.

Lemma value_no_protect : forall l a, value (tm_protect l a) -> False.
Proof. intros; inversion H. Qed.

Lemma value_no_abs_step : forall T body k u, ~ step (tm_abs T body k) u.
Proof. intros T body k u Hstep; inversion Hstep. Qed.

Lemma value_protect_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv; induction Hv; simpl.
  - constructor.
  - constructor. simpl. assumption.
  - apply v_pair; assumption.
  - apply v_inl; assumption.
  - apply v_inr; assumption.
Qed.

Lemma protect_value_low : forall v : tm, protect_value v Low = v.
Proof.
  intros v; destruct v; simpl; try reflexivity;
    try (rewrite protect_security_low; reflexivity).
Qed.

(* ============================================================== *)
(* Multi-step evaluation lemmas                                    *)
(* ============================================================== *)

Lemma multi_unit_eq : forall k u, tm_unit k -->* u -> u = tm_unit k.
Proof.
  intros k u Hm.
  remember (tm_unit k) as x eqn:Hx.
  revert k Hx.
  induction Hm as [| t1 t2 t3 Hstep Hm IH]; intros k Hx.
  - reflexivity.
  - subst t1; inversion Hstep.
Qed.

Lemma multi_abs_eq : forall T body k u,
  tm_abs T body k -->* u -> u = tm_abs T body k.
Proof.
  intros T body k u Hm.
  remember (tm_abs T body k) as x eqn:Hx.
  revert T body k Hx.
  induction Hm as [| t1 t2 t3 Hstep Hm IH]; intros T body k Hx.
  - reflexivity.
  - subst t1; inversion Hstep.
Qed.

Lemma multi_value_eq : forall v u, multi v u -> value v -> value u -> u = v.
Proof.
  intros v u Hm. induction Hm as [| t1 t2 t3 Hstep Hm IH]; intros Hv Hval.
  - reflexivity.
  - exfalso. exact (value_no_step t1 Hv t2 Hstep).
Qed.

(* Inversion lemmas for single steps, phrased so that impossible
   constructors are discarded by inversion. *)

Lemma step_pair_inv : forall a b k x,
  step (tm_pair a b k) x ->
  (exists a', step a a' /\ x = tm_pair a' b k) \/
  (value a /\ exists b', step b b' /\ x = tm_pair a b' k).
Proof.
  intros a b k x H. inversion H; subst; eauto.
Qed.

Lemma step_inl_inv : forall a k x,
  step (tm_inl a k) x -> exists a', step a a' /\ x = tm_inl a' k.
Proof. intros a k x H; inversion H; subst; eauto. Qed.

Lemma step_inr_inv : forall a k x,
  step (tm_inr a k) x -> exists a', step a a' /\ x = tm_inr a' k.
Proof. intros a k x H; inversion H; subst; eauto. Qed.

Lemma step_app_inv : forall a b r x,
  step (tm_app a b r) x ->
  (exists T body k v,
      a = tm_abs T body k /\ value (tm_abs T body k) /\
      b = v /\ value v /\ flows_to k.(reader) r /\
      x = tm_protect k.(indirect_reader) (open body v))
  \/ (exists a', step a a' /\ x = tm_app a' b r)
  \/ (value a /\ exists b', step b b' /\ x = tm_app a b' r).
Proof.
  intros a b r x H. inversion H; subst.
  - left. eauto 10.
  - right; left. eauto.
  - right; right. eauto.
Qed.

Lemma step_fst_inv : forall t r x,
  step (tm_fst t r) x ->
  (exists v1 v2 k,
      t = tm_pair v1 v2 k /\ value v1 /\ value v2 /\
      flows_to k.(reader) r /\ x = tm_protect k.(indirect_reader) v1)
  \/ (exists t', step t t' /\ x = tm_fst t' r).
Proof.
  intros t r x H. inversion H; subst.
  - left. eauto 10.
  - right. eauto.
Qed.

Lemma step_snd_inv : forall t r x,
  step (tm_snd t r) x ->
  (exists v1 v2 k,
      t = tm_pair v1 v2 k /\ value v1 /\ value v2 /\
      flows_to k.(reader) r /\ x = tm_protect k.(indirect_reader) v2)
  \/ (exists t', step t t' /\ x = tm_snd t' r).
Proof.
  intros t r x H. inversion H; subst.
  - left. eauto 10.
  - right. eauto.
Qed.

Lemma step_case_inv : forall t b1 b2 r x,
  step (tm_case t b1 b2 r) x ->
  (exists v k,
      t = tm_inl v k /\ value v /\ flows_to k.(reader) r /\
      x = tm_protect k.(indirect_reader) (open b1 v))
  \/ (exists v k,
      t = tm_inr v k /\ value v /\ flows_to k.(reader) r /\
      x = tm_protect k.(indirect_reader) (open b2 v))
  \/ (exists t', step t t' /\ x = tm_case t' b1 b2 r).
Proof.
  intros t b1 b2 r x H. inversion H; subst.
  - left. eauto 10.
  - right; left. eauto 10.
  - right; right. eauto.
Qed.

Lemma step_if_inv : forall c y n r x,
  step (tm_if c y n r) x ->
  (exists c', step c c' /\ x = tm_if c' y n r)
  \/ (exists v k,
      c = tm_inl v k /\ value v /\ flows_to k.(reader) r /\
      x = tm_protect k.(indirect_reader) y)
  \/ (exists v k,
      c = tm_inr v k /\ value v /\ flows_to k.(reader) r /\
      x = tm_protect k.(indirect_reader) n).
Proof.
  intros c y n r x H. inversion H; subst.
  - left. eauto.
  - right; left. eauto 10.
  - right; right. eauto 10.
Qed.

Lemma step_protect_inv : forall l t x,
  step (tm_protect l t) x ->
  (value t /\ x = protect_value t l) \/
  (exists t', step t t' /\ x = tm_protect l t').
Proof.
  intros l t x H. inversion H; subst.
  - left. eauto.
  - right. eauto.
Qed.

Lemma pair_multi_decomp : forall x u,
  multi x u -> value u ->
  forall a b k, x = tm_pair a b k ->
  exists a' b', a -->* a' /\ value a' /\ b -->* b' /\ value b' /\
    u = tm_pair a' b' k.
Proof.
  intros x u Hm.
  induction Hm as [| x1 x2 x3 Hstep Hm IH]; intros Hval a b k Hx.
  - subst. destruct (value_inv_pair a b k Hval) as [Ha Hb].
    exists a, b. repeat split; auto using multi_refl.
  - subst x1.
    destruct (step_pair_inv a b k x2 Hstep) as
        [(a0' & Hstepa & Hx2) | (Hva & b0' & Hstepb & Hx2)].
    + destruct (IH Hval a0' b k Hx2) as (a'' & b'' & Ha & Hva' & Hb & Hvb' & Hu).
      exists a'', b''. repeat split; auto. eapply multi_step; eauto.
    + destruct (IH Hval a b0' k Hx2) as (a'' & b'' & Ha & Hva' & Hb & Hvb' & Hu).
      exists a'', b''. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma inl_multi_decomp : forall x u,
  multi x u -> value u ->
  forall a k, x = tm_inl a k ->
  exists a', a -->* a' /\ value a' /\ u = tm_inl a' k.
Proof.
  intros x u Hm.
  induction Hm as [| x1 x2 x3 Hstep Hm IH]; intros Hval a k Hx.
  - subst. exists a. repeat split; auto using multi_refl.
    apply value_inv_inl in Hval; auto.
  - subst x1. destruct (step_inl_inv a k x2 Hstep) as (a0' & Hstepa & Hx2).
    destruct (IH Hval a0' k Hx2) as (a'' & Ha & Hva' & Hu).
    exists a''. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma inr_multi_decomp : forall x u,
  multi x u -> value u ->
  forall a k, x = tm_inr a k ->
  exists a', a -->* a' /\ value a' /\ u = tm_inr a' k.
Proof.
  intros x u Hm.
  induction Hm as [| x1 x2 x3 Hstep Hm IH]; intros Hval a k Hx.
  - subst. exists a. repeat split; auto using multi_refl.
    apply value_inv_inr in Hval; auto.
  - subst x1. destruct (step_inr_inv a k x2 Hstep) as (a0' & Hstepa & Hx2).
    destruct (IH Hval a0' k Hx2) as (a'' & Ha & Hva' & Hu).
    exists a''. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma app_multi_decomp : forall x u,
  multi x u -> value u ->
  forall a b r, x = tm_app a b r ->
  exists a' b', a -->* a' /\ value a' /\ b -->* b' /\ value b' /\
    tm_app a' b' r -->* u.
Proof.
  intros x u Hm.
  induction Hm as [| x1 x2 x3 Hstep Hm IH]; intros Hval a b r Hx.
  - subst. exfalso. eapply value_no_app; eauto.
  - subst x1.
    destruct (step_app_inv a b r x2 Hstep) as
      [ (T0 & body0 & k0 & v0 & Ha & Hvabs & Hb & Hvv & Hfl & Hx2)
      | [ (a0' & Hstepa & Hx2) | (Hva & b0' & Hstepb & Hx2) ] ].
    + subst a; subst b; subst x2.
      exists (tm_abs T0 body0 k0), v0. repeat split; auto using multi_refl.
      eapply multi_step; [eapply ST_AppAbs; eauto | exact Hm].
    + destruct (IH Hval a0' b r Hx2) as (a'' & b'' & Ha & Hva' & Hb & Hvb' & Hu).
      exists a'', b''. repeat split; auto. eapply multi_step; eauto.
    + destruct (IH Hval a b0' r Hx2) as (a'' & b'' & Ha & Hva' & Hb & Hvb' & Hu).
      exists a'', b''. repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma fst_multi_decomp : forall x u,
  multi x u -> value u ->
  forall s r, x = tm_fst s r ->
  exists s', s -->* s' /\ value s' /\ tm_fst s' r -->* u.
Proof.
  intros x u Hm.
  induction Hm as [| x1 x2 x3 Hstep Hm IH]; intros Hval s r Hx.
  - subst. exfalso. eapply value_no_fst; eauto.
  - subst x1.
    destruct (step_fst_inv s r x2 Hstep) as
        [(v1 & v2 & k0 & Hs & Hv1 & Hv2 & Hfl & Hx2) | (s0' & Hsteps & Hx2)].
    + subst s; subst x2.
      exists (tm_pair v1 v2 k0). split.
      * apply multi_refl.
      * split.
        -- apply v_pair; auto.
        -- eapply multi_step; [eapply ST_FstPair; eauto | exact Hm].
    + destruct (IH Hval s0' r Hx2) as (s'' & Hs & Hvs & Hu).
      exists s''. split.
      * eapply multi_step; eauto.
      * split; [exact Hvs | exact Hu].
Qed.

Lemma snd_multi_decomp : forall x u,
  multi x u -> value u ->
  forall s r, x = tm_snd s r ->
  exists s', s -->* s' /\ value s' /\ tm_snd s' r -->* u.
Proof.
  intros x u Hm.
  induction Hm as [| x1 x2 x3 Hstep Hm IH]; intros Hval s r Hx.
  - subst. exfalso. eapply value_no_snd; eauto.
  - subst x1.
    destruct (step_snd_inv s r x2 Hstep) as
        [(v1 & v2 & k0 & Hs & Hv1 & Hv2 & Hfl & Hx2) | (s0' & Hsteps & Hx2)].
    + subst s; subst x2.
      exists (tm_pair v1 v2 k0). split.
      * apply multi_refl.
      * split.
        -- apply v_pair; auto.
        -- eapply multi_step; [eapply ST_SndPair; eauto | exact Hm].
    + destruct (IH Hval s0' r Hx2) as (s'' & Hs & Hvs & Hu).
      exists s''. split.
      * eapply multi_step; eauto.
      * split; [exact Hvs | exact Hu].
Qed.

Lemma case_multi_decomp : forall x u,
  multi x u -> value u ->
  forall s b1 b2 r, x = tm_case s b1 b2 r ->
  exists s', s -->* s' /\ value s' /\ tm_case s' b1 b2 r -->* u.
Proof.
  intros x u Hm.
  induction Hm as [| x1 x2 x3 Hstep Hm IH]; intros Hval s b1 b2 r Hx.
  - subst. exfalso. eapply value_no_case; eauto.
  - subst x1.
    destruct (step_case_inv s b1 b2 r x2 Hstep) as
      [ (v0 & k0 & Hs & Hv & Hfl & Hx2)
      | [ (v0 & k0 & Hs & Hv & Hfl & Hx2) | (s0' & Hsteps & Hx2) ] ].
    + subst s; subst x2.
      exists (tm_inl v0 k0). split.
      * apply multi_refl.
      * split.
        -- apply v_inl; auto.
        -- eapply multi_step; [eapply ST_CaseLeft; eauto | exact Hm].
    + subst s; subst x2.
      exists (tm_inr v0 k0). split.
      * apply multi_refl.
      * split.
        -- apply v_inr; auto.
        -- eapply multi_step; [eapply ST_CaseRight; eauto | exact Hm].
    + destruct (IH Hval s0' b1 b2 r Hx2) as (s'' & Hs & Hvs & Hu).
      exists s''. split.
      * eapply multi_step; eauto.
      * split; [exact Hvs | exact Hu].
Qed.

Lemma if_multi_decomp : forall x u,
  multi x u -> value u ->
  forall c y n r, x = tm_if c y n r ->
  exists c', c -->* c' /\ value c' /\ tm_if c' y n r -->* u.
Proof.
  intros x u Hm.
  induction Hm as [| x1 x2 x3 Hstep Hm IH]; intros Hval c y n r Hx.
  - subst. exfalso. eapply value_no_if; eauto.
  - subst x1.
    destruct (step_if_inv c y n r x2 Hstep) as
      [ (c0' & Hstepc & Hx2)
      | [ (v0 & k0 & Hc & Hv & Hfl & Hx2)
        | (v0 & k0 & Hc & Hv & Hfl & Hx2) ] ].
    + destruct (IH Hval c0' y n r Hx2) as (c'' & Hc & Hvc & Hu).
      exists c''. repeat split; auto. eapply multi_step; eauto.
    + subst c; subst x2.
      exists (tm_inl v0 k0). split.
      * apply multi_refl.
      * split.
        -- apply v_inl; auto.
        -- eapply multi_step; [eapply ST_IfTrue; eauto | exact Hm].
    + subst c; subst x2.
      exists (tm_inr v0 k0). split.
      * apply multi_refl.
      * split.
        -- apply v_inr; auto.
        -- eapply multi_step; [eapply ST_IfFalse; eauto | exact Hm].
Qed.

Lemma protect_multi_decomp : forall x u,
  multi x u -> value u ->
  forall l s, x = tm_protect l s ->
  exists v, s -->* v /\ value v /\ u = protect_value v l.
Proof.
  intros x u Hm.
  induction Hm as [| x1 x2 x3 Hstep Hm IH]; intros Hval l s Hx.
  - subst. exfalso. eapply value_no_protect; eauto.
  - subst x1.
    destruct (step_protect_inv l s x2 Hstep) as [(Hv & Hx2) | (s0' & Hsteps & Hx2)].
    + subst x2.
      assert (Hpv : value (protect_value s l)) by (apply value_protect_value; auto).
      assert (Heq : x3 = protect_value s l) by (eapply multi_value_eq; eauto).
      exists s. split.
      * apply multi_refl.
      * split; [exact Hv | exact Heq].
    + destruct (IH Hval l s0' Hx2) as (v & Hs & Hv & Hu).
      exists v. split.
      * eapply multi_step; eauto.
      * split; [exact Hv | exact Hu].
Qed.

(* Head-step lemmas: when the start is a redex with values, the first step
   is necessarily the corresponding rule. *)

Lemma app_abs_multi : forall T body k w r u,
  value (tm_abs T body k) -> value w -> flows_to k.(reader) r ->
  tm_app (tm_abs T body k) w r -->* u -> value u ->
  tm_protect k.(indirect_reader) (open body w) -->* u.
Proof.
  intros T body k w r u Hvabs Hvw Hflow Hmulti Hval.
  inversion Hmulti as [| t1 t2 t3 Hstep Hm]; subst.
  - exfalso. eapply value_no_app; eauto.
  - destruct (step_app_inv (tm_abs T body k) w r t2 Hstep) as
      [ (T0 & body0 & k0 & v0 & Ha & Hva & Hb & Hvv & Hfl & Hx2)
      | [ (a0' & Hstepa & Hx2) | (Hva & b0' & Hstepb & Hx2) ] ].
    + injection Ha as HT Hbody Hk. subst. exact Hm.
    + exfalso. exact (value_no_step (tm_abs T body k) Hvabs a0' Hstepa).
    + exfalso. exact (value_no_step w Hvw b0' Hstepb).
Qed.

Lemma fst_pair_multi : forall v1 v2 k r u,
  value v1 -> value v2 -> flows_to k.(reader) r ->
  tm_fst (tm_pair v1 v2 k) r -->* u -> value u ->
  tm_protect k.(indirect_reader) v1 -->* u.
Proof.
  intros v1 v2 k r u Hv1 Hv2 Hflow Hmulti Hval.
  inversion Hmulti as [| t1 t2 t3 Hstep Hm]; subst.
  - exfalso. eapply value_no_fst; eauto.
  - destruct (step_fst_inv (tm_pair v1 v2 k) r t2 Hstep) as
        [(w1 & w2 & k0 & Ht & Hw1 & Hw2 & Hfl & Hx2) | (s0' & Hsteps & Hx2)].
    + injection Ht as H1 H2 H3. subst. exact Hm.
    + exfalso. exact (value_no_step (tm_pair v1 v2 k) (v_pair v1 v2 k Hv1 Hv2) s0' Hsteps).
Qed.

Lemma snd_pair_multi : forall v1 v2 k r u,
  value v1 -> value v2 -> flows_to k.(reader) r ->
  tm_snd (tm_pair v1 v2 k) r -->* u -> value u ->
  tm_protect k.(indirect_reader) v2 -->* u.
Proof.
  intros v1 v2 k r u Hv1 Hv2 Hflow Hmulti Hval.
  inversion Hmulti as [| t1 t2 t3 Hstep Hm]; subst.
  - exfalso. eapply value_no_snd; eauto.
  - destruct (step_snd_inv (tm_pair v1 v2 k) r t2 Hstep) as
        [(w1 & w2 & k0 & Ht & Hw1 & Hw2 & Hfl & Hx2) | (s0' & Hsteps & Hx2)].
    + injection Ht as H1 H2 H3. subst. exact Hm.
    + exfalso. exact (value_no_step (tm_pair v1 v2 k) (v_pair v1 v2 k Hv1 Hv2) s0' Hsteps).
Qed.

Lemma case_inl_multi : forall a k b1 b2 r u,
  value a -> flows_to k.(reader) r ->
  tm_case (tm_inl a k) b1 b2 r -->* u -> value u ->
  tm_protect k.(indirect_reader) (open b1 a) -->* u.
Proof.
  intros a k b1 b2 r u Hva Hflow Hmulti Hval.
  inversion Hmulti as [| t1 t2 t3 Hstep Hm]; subst.
  - exfalso. eapply value_no_case; eauto.
  - destruct (step_case_inv (tm_inl a k) b1 b2 r t2 Hstep) as
      [ (v0 & k0 & Ht & Hv & Hfl & Hx2)
      | [ (v0 & k0 & Ht & Hv & Hfl & Hx2) | (s0' & Hsteps & Hx2) ] ].
    + injection Ht as Ha Hk. subst. exact Hm.
    + exfalso. discriminate Ht.
    + exfalso. exact (value_no_step (tm_inl a k) (v_inl a k Hva) s0' Hsteps).
Qed.

Lemma case_inr_multi : forall a k b1 b2 r u,
  value a -> flows_to k.(reader) r ->
  tm_case (tm_inr a k) b1 b2 r -->* u -> value u ->
  tm_protect k.(indirect_reader) (open b2 a) -->* u.
Proof.
  intros a k b1 b2 r u Hva Hflow Hmulti Hval.
  inversion Hmulti as [| t1 t2 t3 Hstep Hm]; subst.
  - exfalso. eapply value_no_case; eauto.
  - destruct (step_case_inv (tm_inr a k) b1 b2 r t2 Hstep) as
      [ (v0 & k0 & Ht & Hv & Hfl & Hx2)
      | [ (v0 & k0 & Ht & Hv & Hfl & Hx2) | (s0' & Hsteps & Hx2) ] ].
    + exfalso. discriminate Ht.
    + injection Ht as Ha Hk. subst. exact Hm.
    + exfalso. exact (value_no_step (tm_inr a k) (v_inr a k Hva) s0' Hsteps).
Qed.

Lemma if_inl_multi : forall a k y n r u,
  value a -> flows_to k.(reader) r ->
  tm_if (tm_inl a k) y n r -->* u -> value u ->
  tm_protect k.(indirect_reader) y -->* u.
Proof.
  intros a k y n r u Hva Hflow Hmulti Hval.
  inversion Hmulti as [| t1 t2 t3 Hstep Hm]; subst.
  - exfalso. eapply value_no_if; eauto.
  - destruct (step_if_inv (tm_inl a k) y n r t2 Hstep) as
      [ (c0' & Hstepc & Hx2)
      | [ (v0 & k0 & Hc & Hv & Hfl & Hx2)
        | (v0 & k0 & Hc & Hv & Hfl & Hx2) ] ].
    + exfalso. exact (value_no_step (tm_inl a k) (v_inl a k Hva) c0' Hstepc).
    + injection Hc as Ha Hk. subst. exact Hm.
    + exfalso. discriminate Hc.
Qed.

Lemma if_inr_multi : forall a k y n r u,
  value a -> flows_to k.(reader) r ->
  tm_if (tm_inr a k) y n r -->* u -> value u ->
  tm_protect k.(indirect_reader) n -->* u.
Proof.
  intros a k y n r u Hva Hflow Hmulti Hval.
  inversion Hmulti as [| t1 t2 t3 Hstep Hm]; subst.
  - exfalso. eapply value_no_if; eauto.
  - destruct (step_if_inv (tm_inr a k) y n r t2 Hstep) as
      [ (c0' & Hstepc & Hx2)
      | [ (v0 & k0 & Hc & Hv & Hfl & Hx2)
        | (v0 & k0 & Hc & Hv & Hfl & Hx2) ] ].
    + exfalso. exact (value_no_step (tm_inr a k) (v_inr a k Hva) c0' Hstepc).
    + exfalso. discriminate Hc.
    + injection Hc as Ha Hk. subst. exact Hm.
Qed.

(* ============================================================== *)
(* Substitutions and environments                                  *)
(* ============================================================== *)

Definition env := atom -> tm.

Definition env_update (sigma : env) (x : atom) (v : tm) : env :=
  fun y => if Nat.eqb y x then v else sigma y.

Lemma env_update_same : forall sigma x v, env_update sigma x v x = v.
Proof. intros; unfold env_update; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma env_update_other : forall sigma x y v, y <> x -> env_update sigma x v y = sigma y.
Proof.
  intros sigma x y v Hneq. unfold env_update.
  destruct (Nat.eqb y x) eqn:E; auto.
  apply Nat.eqb_eq in E; contradiction.
Qed.

Fixpoint subst_env (sigma : env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => sigma y
  | tm_unit k => tm_unit k
  | tm_abs T body k => tm_abs T (subst_env sigma body) k
  | tm_app t1 t2 r => tm_app (subst_env sigma t1) (subst_env sigma t2) r
  | tm_pair t1 t2 k => tm_pair (subst_env sigma t1) (subst_env sigma t2) k
  | tm_fst t1 r => tm_fst (subst_env sigma t1) r
  | tm_snd t1 r => tm_snd (subst_env sigma t1) r
  | tm_inl t1 k => tm_inl (subst_env sigma t1) k
  | tm_inr t1 k => tm_inr (subst_env sigma t1) k
  | tm_case t0 b1 b2 r =>
      tm_case (subst_env sigma t0) (subst_env sigma b1) (subst_env sigma b2) r
  | tm_protect l t1 => tm_protect l (subst_env sigma t1)
  | tm_if c y n r =>
      tm_if (subst_env sigma c) (subst_env sigma y) (subst_env sigma n) r
  end.

Fixpoint fv_context (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ => fv_context C'
  | C_AppLeft C' s _ => fv_context C' ++ fv s
  | C_AppRight s C' _ => fv s ++ fv_context C'
  | C_PairLeft C' s _ => fv_context C' ++ fv s
  | C_PairRight s C' _ => fv s ++ fv_context C'
  | C_Fst C' _ => fv_context C'
  | C_Snd C' _ => fv_context C'
  | C_Inl C' _ => fv_context C'
  | C_Inr C' _ => fv_context C'
  | C_CaseScrutinee C' s1 s2 _ => fv_context C' ++ fv s1 ++ fv s2
  | C_CaseLeft s0 C' s2 _ => fv s0 ++ fv_context C' ++ fv s2
  | C_CaseRight s0 s1 C' _ => fv s0 ++ fv s1 ++ fv_context C'
  | C_Protect _ C' => fv_context C'
  | C_IfCondition C' s1 s2 _ => fv_context C' ++ fv s1 ++ fv s2
  | C_IfThen s0 C' s2 _ => fv s0 ++ fv_context C' ++ fv s2
  | C_IfElse s0 s1 C' _ => fv s0 ++ fv s1 ++ fv_context C'
  end.

Lemma notin_app_inv_l : forall (x : atom) l1 l2, ~ In x (l1 ++ l2) -> ~ In x l1.
Proof. intros x l1 l2 H Hin; apply H; apply in_or_app; auto. Qed.

Lemma notin_app_inv_r : forall (x : atom) l1 l2, ~ In x (l1 ++ l2) -> ~ In x l2.
Proof. intros x l1 l2 H Hin; apply H; apply in_or_app; auto. Qed.

Lemma notin_app3_l : forall (x : atom) a b c, ~ In x (a ++ b ++ c) -> ~ In x a.
Proof. intros x a b c H. apply notin_app_inv_l in H. exact H. Qed.

Lemma notin_app3_m : forall (x : atom) a b c, ~ In x (a ++ b ++ c) -> ~ In x b.
Proof. intros x a b c H. apply notin_app_inv_r in H. apply notin_app_inv_l in H. exact H. Qed.

Lemma notin_app3_r : forall (x : atom) a b c, ~ In x (a ++ b ++ c) -> ~ In x c.
Proof. intros x a b c H. apply notin_app_inv_r in H. apply notin_app_inv_r in H. exact H. Qed.

#[local] Hint Resolve notin_app_inv_l notin_app_inv_r
  notin_app3_l notin_app3_m notin_app3_r : core.

Lemma subst_env_id : forall t, subst_env (fun y => tm_fvar y) t = t.
Proof.
  induction t as [ti | tf | ku | T body IHbody ka | t1 IH1 t2 IH2 ra
                 | t1 IH1 t2 IH2 kp | t1 IH1 rf | t1 IH1 rs | t1 IH1 kl
                 | t1 IH1 kr | t0 IH0 b1 IH1 b2 IH2 rc | lp t1 IH1
                 | c IHc v IHy n IHn ri]; simpl; try reflexivity;
    try (f_equal; assumption).
Qed.

Lemma subst_env_ext : forall sigma sigma' t,
  (forall y, In y (fv t) -> sigma' y = sigma y) ->
  subst_env sigma' t = subst_env sigma t.
Proof.
  intros sigma sigma' t Hagree.
  induction t as [ti | tf | ku | T body IHbody ka | t1 IH1 t2 IH2 ra
                 | t1 IH1 t2 IH2 kp | t1 IH1 rf | t1 IH1 rs | t1 IH1 kl
                 | t1 IH1 kr | t0 IH0 b1 IH1 b2 IH2 rc | lp t1 IH1
                 | c IHc v IHy n IHn ri]; simpl in *; try reflexivity.
  - apply Hagree; auto.
  - f_equal. apply IHbody. intros z Hz. apply Hagree. simpl. exact Hz.
  - f_equal; [apply IH1 | apply IH2]; intros z Hz; apply Hagree;
      simpl; apply in_or_app; auto.
  - f_equal; [apply IH1 | apply IH2]; intros z Hz; apply Hagree;
      simpl; apply in_or_app; auto.
  - f_equal. apply IH1. intros z Hz. apply Hagree. simpl. exact Hz.
  - f_equal. apply IH1. intros z Hz. apply Hagree. simpl. exact Hz.
  - f_equal. apply IH1. intros z Hz. apply Hagree. simpl. exact Hz.
  - f_equal. apply IH1. intros z Hz. apply Hagree. simpl. exact Hz.
  - f_equal.
    + apply IH0. intros z Hz. apply Hagree. apply in_or_app. left. exact Hz.
    + apply IH1. intros z Hz. apply Hagree.
      apply in_or_app. right. apply in_or_app. left. exact Hz.
    + apply IH2. intros z Hz. apply Hagree.
      apply in_or_app. right. apply in_or_app. right. exact Hz.
  - f_equal. apply IH1. intros z Hz. apply Hagree. exact Hz.
  - f_equal.
    + apply IHc. intros z Hz. apply Hagree. apply in_or_app. left. exact Hz.
    + apply IHy. intros z Hz. apply Hagree.
      apply in_or_app. right. apply in_or_app. left. exact Hz.
    + apply IHn. intros z Hz. apply Hagree.
      apply in_or_app. right. apply in_or_app. right. exact Hz.
Qed.

Lemma subst_env_id_on_fv : forall sigma s,
  (forall y, In y (fv s) -> sigma y = tm_fvar y) ->
  subst_env sigma s = s.
Proof.
  intros sigma s H.
  transitivity (subst_env (fun y => tm_fvar y) s).
  - apply subst_env_ext. intros y Hy. apply H; auto.
  - apply subst_env_id.
Qed.

Lemma subst_env_stored : forall sigma x s,
  (forall y, y <> x -> sigma y = tm_fvar y) ->
  ~ In x (fv s) -> subst_env sigma s = s.
Proof.
  intros sigma x s Hident Hfresh.
  apply subst_env_id_on_fv. intros y Hy.
  apply Hident. intro Hyx; subst y; exact (Hfresh Hy).
Qed.

Lemma open_rec_lc_gen : forall t m, lc_at m t ->
  forall k u, m <= k -> open_rec k u t = t.
Proof.
  induction t as [ti | tf | ku | T body IHbody ka | t1 IH1 t2 IH2 ra
                 | t1 IH1 t2 IH2 kp | t1 IH1 rf | t1 IH1 rs | t1 IH1 kl
                 | t1 IH1 kr | t0 IH0 b1 IH1 b2 IH2 rc | lp t1 IH1
                 | c IHc v IHy n IHn ri]; intros m Hm k u Hle; simpl in *.
  - destruct (Nat.eqb k ti) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E. exfalso. lia.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHbody with (m := S m) (k := S k).
    + exact Hm.
    + lia.
  - destruct Hm as [H1 H2]. f_equal; [apply IH1 with (m:=m)(k:=k) | apply IH2 with (m:=m)(k:=k)]; auto.
  - destruct Hm as [H1 H2]. f_equal; [apply IH1 with (m:=m)(k:=k) | apply IH2 with (m:=m)(k:=k)]; auto.
  - f_equal. apply IH1 with (m:=m)(k:=k); auto.
  - f_equal. apply IH1 with (m:=m)(k:=k); auto.
  - f_equal. apply IH1 with (m:=m)(k:=k); auto.
  - f_equal. apply IH1 with (m:=m)(k:=k); auto.
  - destruct Hm as [H0 [H1 H2]]. f_equal.
    + apply IH0 with (m:=m)(k:=k); auto.
    + apply IH1 with (m:=S m)(k:=S k); auto; lia.
    + apply IH2 with (m:=S m)(k:=S k); auto; lia.
  - f_equal. apply IH1 with (m:=m)(k:=k); auto.
  - destruct Hm as [Hc [Hy Hn]]. f_equal.
    + apply IHc with (m:=m)(k:=k); auto.
    + apply IHy with (m:=m)(k:=k); auto.
    + apply IHn with (m:=m)(k:=k); auto.
Qed.

Lemma subst_env_open : forall sigma,
  (forall y, locally_closed (sigma y)) ->
  forall t k x,
    subst_env sigma (open_rec k (tm_fvar x) t) =
    open_rec k (sigma x) (subst_env sigma t).
Proof.
  intros sigma Hlc t.
  induction t as [ti | tf | ku | T body IHbody ka | t1 IH1 t2 IH2 ra
                 | t1 IH1 t2 IH2 kp | t1 IH1 rf | t1 IH1 rs | t1 IH1 kl
                 | t1 IH1 kr | t0 IH0 b1 IH1 b2 IH2 rc | lp t1 IH1
                 | c IHc v IHy n IHn ri]; intros k x; simpl.
  - destruct (Nat.eqb k ti); reflexivity.
  - symmetry. exact (open_rec_lc_gen (sigma tf) 0 (Hlc tf) k (sigma x) (Nat.le_0_l k)).
  - reflexivity.
  - f_equal; apply IHbody.
  - f_equal; [apply IH1 | apply IH2].
  - f_equal; [apply IH1 | apply IH2].
  - f_equal; apply IH1.
  - f_equal; apply IH1.
  - f_equal; apply IH1.
  - f_equal; apply IH1.
  - f_equal; [apply IH0 | apply IH1 | apply IH2].
  - f_equal; apply IH1.
  - f_equal; [apply IHc | apply IHy | apply IHn].
Qed.

Lemma subst_env_plug_x : forall sigma C x t,
  sigma x = t ->
  (forall y, y <> x -> sigma y = tm_fvar y) ->
  ~ In x (fv_context C) ->
  subst_env sigma (plug C (tm_fvar x)) = plug C t.
Proof.
  intros sigma C.
  induction C as [ | T C' IHC ka | C' IHC s r | s C' IHC r
                 | C' IHC s r | s C' IHC r | C' IHC r | C' IHC r
                 | C' IHC s | C' IHC s | C' IHC s1 s2 r
                 | s0 C' IHC s2 r | s0 s1 C' IHC r | l C' IHC
                 | C' IHC s1 s2 r | s0 C' IHC s2 r | s0 s1 C' IHC r];
    intros x t Hx Hident Hfresh; simpl in *.
  - rewrite Hx. reflexivity.
  - f_equal. apply IHC; [exact Hx | exact Hident |exact Hfresh].
  - f_equal.
    + apply IHC; [exact Hx | exact Hident |apply notin_app_inv_l with (l2 := fv s); exact Hfresh].
    + apply (subst_env_stored sigma x s); [exact Hident |].
      apply notin_app_inv_r with (l1 := fv_context C'). exact Hfresh.
  - f_equal.
    + apply (subst_env_stored sigma x s); [exact Hident |].
      apply notin_app_inv_l with (l2 := fv_context C'). exact Hfresh.
    + apply IHC; [exact Hx | exact Hident |apply notin_app_inv_r with (l1 := fv s); exact Hfresh].
  - f_equal.
    + apply IHC; [exact Hx | exact Hident |apply notin_app_inv_l with (l2 := fv s); exact Hfresh].
    + apply (subst_env_stored sigma x s); [exact Hident |].
      apply notin_app_inv_r with (l1 := fv_context C'). exact Hfresh.
  - f_equal.
    + apply (subst_env_stored sigma x s); [exact Hident |].
      apply notin_app_inv_l with (l2 := fv_context C'). exact Hfresh.
    + apply IHC; [exact Hx | exact Hident |apply notin_app_inv_r with (l1 := fv s); exact Hfresh].
  - f_equal. apply IHC; [exact Hx | exact Hident |exact Hfresh].
  - f_equal. apply IHC; [exact Hx | exact Hident |exact Hfresh].
  - f_equal. apply IHC; [exact Hx | exact Hident |exact Hfresh].
  - f_equal. apply IHC; [exact Hx | exact Hident |exact Hfresh].
  - f_equal.
    + apply IHC; [exact Hx | exact Hident |apply notin_app3_l with (b := fv s1) (c := fv s2); exact Hfresh].
    + apply (subst_env_stored sigma x s1); [exact Hident |].
      apply notin_app3_m with (a := fv_context C') (c := fv s2). exact Hfresh.
    + apply (subst_env_stored sigma x s2); [exact Hident |].
      apply notin_app3_r with (a := fv_context C') (b := fv s1). exact Hfresh.
  - f_equal.
    + apply (subst_env_stored sigma x s0); [exact Hident |].
      apply notin_app3_l with (b := fv_context C') (c := fv s2). exact Hfresh.
    + apply IHC; [exact Hx | exact Hident |apply notin_app3_m with (a := fv s0) (c := fv s2); exact Hfresh].
    + apply (subst_env_stored sigma x s2); [exact Hident |].
      apply notin_app3_r with (a := fv s0) (b := fv_context C'). exact Hfresh.
  - f_equal.
    + apply (subst_env_stored sigma x s0); [exact Hident |].
      apply notin_app3_l with (b := fv s1) (c := fv_context C'). exact Hfresh.
    + apply (subst_env_stored sigma x s1); [exact Hident |].
      apply notin_app3_m with (a := fv s0) (c := fv_context C'). exact Hfresh.
    + apply IHC; [exact Hx | exact Hident |apply notin_app3_r with (a := fv s0) (b := fv s1); exact Hfresh].
  - f_equal. apply IHC; [exact Hx | exact Hident |exact Hfresh].
  - f_equal.
    + apply IHC; [exact Hx | exact Hident |apply notin_app3_l with (b := fv s1) (c := fv s2); exact Hfresh].
    + apply (subst_env_stored sigma x s1); [exact Hident |].
      apply notin_app3_m with (a := fv_context C') (c := fv s2). exact Hfresh.
    + apply (subst_env_stored sigma x s2); [exact Hident |].
      apply notin_app3_r with (a := fv_context C') (b := fv s1). exact Hfresh.
  - f_equal.
    + apply (subst_env_stored sigma x s0); [exact Hident |].
      apply notin_app3_l with (b := fv_context C') (c := fv s2). exact Hfresh.
    + apply IHC; [exact Hx | exact Hident |apply notin_app3_m with (a := fv s0) (c := fv s2); exact Hfresh].
    + apply (subst_env_stored sigma x s2); [exact Hident |].
      apply notin_app3_r with (a := fv s0) (b := fv_context C'). exact Hfresh.
  - f_equal.
    + apply (subst_env_stored sigma x s0); [exact Hident |].
      apply notin_app3_l with (b := fv s1) (c := fv_context C'). exact Hfresh.
    + apply (subst_env_stored sigma x s1); [exact Hident |].
      apply notin_app3_m with (a := fv s0) (c := fv_context C'). exact Hfresh.
    + apply IHC; [exact Hx | exact Hident |apply notin_app3_r with (a := fv s0) (b := fv s1); exact Hfresh].
Qed.

(* ============================================================== *)
(* Lookup lemmas                                                   *)
(* ============================================================== *)

Lemma lookup_update_same : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros; unfold update, lookup_context; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma lookup_update_other : forall Gamma x y T,
  y <> x -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T Hneq; unfold update, lookup_context.
  destruct (Nat.eqb y x) eqn:E; auto.
  apply Nat.eqb_eq in E; contradiction.
Qed.

Lemma lookup_single : forall x T y U,
  lookup_context y [(x, T)] = Some U -> y = x /\ U = T.
Proof.
  intros x T y U H. unfold lookup_context in H. simpl in H.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. split; auto. injection H; auto.
  - discriminate H.
Qed.

(* ============================================================== *)
(* Fresh atoms                                                     *)
(* ============================================================== *)

Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | y :: ys => y + sum_list ys
  end.

Definition fresh_atom (l : list atom) : atom := S (sum_list l).

Lemma fresh_atom_notin : forall l x, In x l -> x < fresh_atom l.
Proof.
  induction l as [| z zs IH]; intros x Hx; [contradiction|].
  destruct Hx as [Heq | Hx].
  - subst x. unfold fresh_atom. simpl. lia.
  - specialize (IH x Hx). unfold fresh_atom in *. simpl in *. lia.
Qed.

Lemma fresh_atom_fresh : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l H. exact (Nat.lt_irrefl (fresh_atom l) (fresh_atom_notin l _ H)).
Qed.

(* ============================================================== *)
(* The logical relation                                            *)
(* ============================================================== *)

Fixpoint V (T : ty) (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_Unit k =>
      match k.(indirect_reader) with
      | High => True
      | Low => exists k1 k2,
          v1 = tm_unit k1 /\ v2 = tm_unit k2 /\
          security_le k1 k /\ security_le k2 k
      end
  | Ty_Sum T1 T2 k =>
      match k.(indirect_reader) with
      | High => True
      | Low =>
          (exists a1 a2 ka1 ka2,
             v1 = tm_inl a1 ka1 /\ v2 = tm_inl a2 ka2 /\
             security_le ka1 k /\ security_le ka2 k /\ V T1 a1 a2)
          \/
          (exists a1 a2 ka1 ka2,
             v1 = tm_inr a1 ka1 /\ v2 = tm_inr a2 ka2 /\
             security_le ka1 k /\ security_le ka2 k /\ V T2 a1 a2)
      end
  | Ty_Prod T1 T2 k =>
      match k.(indirect_reader) with
      | High => True
      | Low => exists a1 a2 b1 b2 ka1 ka2,
          v1 = tm_pair a1 b1 ka1 /\ v2 = tm_pair a2 b2 ka2 /\
          security_le ka1 k /\ security_le ka2 k /\
          V T1 a1 a2 /\ V T2 b1 b2
      end
  | Ty_Arrow T1 T2 k =>
      match k.(indirect_reader) with
      | High => True
      | Low => exists Ta1 body1 ka1 Ta2 body2 ka2,
          v1 = tm_abs Ta1 body1 ka1 /\ v2 = tm_abs Ta2 body2 ka2 /\
          security_le ka1 k /\ security_le ka2 k /\
          (forall w1 w2 r,
             value w1 -> value w2 -> V T1 w1 w2 ->
             flows_to k.(reader) r ->
             forall u1 u2,
               tm_app v1 w1 r -->* u1 -> value u1 ->
               tm_app v2 w2 r -->* u2 -> value u2 ->
               V T2 u1 u2)
      end
  end.

Definition E (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, t1 -->* v1 -> value v1 -> t2 -->* v2 -> value v2 -> V T v1 v2.

Lemma V_high : forall T v1 v2,
  (security_of T).(indirect_reader) = High -> V T v1 v2.
Proof.
  intros T v1 v2 H.
  destruct T; simpl in H |- *; rewrite H; exact I.
Qed.

Lemma V_to_E_value : forall T v1 v2,
  value v1 -> value v2 -> V T v1 v2 -> E T v1 v2.
Proof.
  intros T v1 v2 Hv1 Hv2 HV u1 u2 Hm1 Hval1 Hm2 Hval2.
  assert (Hu1 : u1 = v1) by (eapply multi_value_eq; eauto).
  assert (Hu2 : u2 = v2) by (eapply multi_value_eq; eauto).
  subst u1; subst u2. exact HV.
Qed.

Definition env_rel (Gamma : context) (sigma1 sigma2 : env) : Prop :=
  (forall y, locally_closed (sigma1 y)) /\
  (forall y, locally_closed (sigma2 y)) /\
  (forall y T, lookup_context y Gamma = Some T -> E T (sigma1 y) (sigma2 y)).

Lemma env_rel_update : forall Gamma sigma1 sigma2 x T w1 w2,
  env_rel Gamma sigma1 sigma2 ->
  value w1 -> value w2 -> V T w1 w2 ->
  env_rel (update Gamma x T) (env_update sigma1 x w1) (env_update sigma2 x w2).
Proof.
  intros Gamma sigma1 sigma2 x T w1 w2 (Hlc1 & Hlc2 & HE) Hv1 Hv2 HV.
  split.
  - intros y. unfold env_update. destruct (Nat.eqb y x); [apply value_lc; auto | apply Hlc1].
  - split.
    + intros y. unfold env_update. destruct (Nat.eqb y x); [apply value_lc; auto | apply Hlc2].
    + intros y U Hlook. unfold update in Hlook; simpl in Hlook.
      destruct (Nat.eqb y x) eqn:Ey.
      * apply Nat.eqb_eq in Ey. subst y.
        injection Hlook as HU. subst U.
        unfold env_update. rewrite Nat.eqb_refl.
        apply V_to_E_value; auto.
      * unfold env_update. rewrite Ey.
        apply HE. exact Hlook.
Qed.

Lemma subst_env_open_env_update : forall sigma x w body,
  locally_closed w ->
  (forall y, locally_closed (sigma y)) ->
  ~ In x (fv body) ->
  subst_env (env_update sigma x w) (open_rec 0 (tm_fvar x) body) =
  open (subst_env sigma body) w.
Proof.
  intros sigma x w body Hw Hlc Hfresh.
  assert (Hlc' : forall y, locally_closed (env_update sigma x w y)).
  { intros y; unfold env_update; destruct (Nat.eqb y x); auto. }
  rewrite (subst_env_open (env_update sigma x w) Hlc' body 0 x).
  rewrite env_update_same.
  assert (Hext : forall y, In y (fv body) -> env_update sigma x w y = sigma y).
  { intros y Hy. apply env_update_other. intro Hyx; subst y; exact (Hfresh Hy). }
  rewrite (subst_env_ext _ _ _ Hext).
  unfold open. reflexivity.
Qed.

(* ============================================================== *)
(* Typing implies local closure                                    *)
(* ============================================================== *)

Lemma lc_open_S : forall t k x, lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros t.
  induction t as [ti | tf | ku | T body IHbody ka | t1 IH1 t2 IH2 ra
                 | t1 IH1 t2 IH2 kp | t1 IH1 rf | t1 IH1 rs | t1 IH1 kl
                 | t1 IH1 kr | t0 IH0 b1 IH1 b2 IH2 rc | lp t1 IH1
                 | c IHc v IHy n IHn ri]; intros k x H; simpl in *.
  - destruct (Nat.eqb k ti) eqn:E; simpl in H; [apply Nat.eqb_eq in E; lia | lia].
  - exact I.
  - exact I.
  - apply IHbody with (k := S k) (x := x). exact H.
  - destruct H as [H1 H2]; split; [apply IH1 with (x := x) | apply IH2 with (x := x)]; auto.
  - destruct H as [H1 H2]; split; [apply IH1 with (x := x) | apply IH2 with (x := x)]; auto.
  - apply IH1 with (x := x); auto.
  - apply IH1 with (x := x); auto.
  - apply IH1 with (x := x); auto.
  - apply IH1 with (x := x); auto.
  - destruct H as [H0 [H1 H2]]; split; [apply IH0 with (x := x); auto | split].
    + apply IH1 with (k := S k) (x := x); auto.
    + apply IH2 with (k := S k) (x := x); auto.
  - apply IH1 with (x := x); auto.
  - destruct H as [Hc [Hy Hn]]; split; [apply IHc with (x := x); auto | split].
    + apply IHy with (x := x); auto.
    + apply IHn with (x := x); auto.
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [ Gamma x T0 Hlook Hwf
    | Gamma kappa Hwf
    | L Gamma T1 body T2 kappa HwfT1 Hwfkappa Hbody IHbody
    | Gamma t1 t2 T1 T2 kappa r Ht1 IH1 Ht2 IH2 Hflow
    | Gamma t1 t2 T1 T2 kappa Ht1 IH1 Ht2 IH2 Hwf
    | Gamma t T1 T2 kappa r Ht IH Hflow
    | Gamma t T1 T2 kappa r Ht IH Hflow
    | Gamma t T1 T2 kappa Ht IH HwfT2 Hwfkappa
    | Gamma t T1 T2 kappa HwfT1 Ht IH Hwfkappa
    | L Gamma t b1 b2 T1 T2 T0 kappa r Ht IHt Hflow Hb1 IH1 Hb2 IH2
    | Gamma t T0 l Ht IH
    | Gamma t T0 U Ht IH Hsub
    | Gamma c yes no k T0 r Hc IHc Hyes IHyes Hno IHno Hflow ];
    simpl.
  - exact I.
  - exact I.
  - set (x := fresh_atom L).
    assert (Hx : ~ In x L) by (intro H; apply (fresh_atom_fresh L); exact H).
    apply (lc_open_S body 0 x). exact (IHbody x Hx).
  - split; [exact IH1 | exact IH2].
  - split; [exact IH1 | exact IH2].
  - exact IH.
  - exact IH.
  - exact IH.
  - exact IH.
  - split; [exact IHt | split].
    + set (x := fresh_atom L).
      assert (Hx : ~ In x L) by (intro H; apply (fresh_atom_fresh L); exact H).
      apply (lc_open_S b1 0 x). exact (IH1 x Hx).
    + set (x := fresh_atom L).
      assert (Hx : ~ In x L) by (intro H; apply (fresh_atom_fresh L); exact H).
      apply (lc_open_S b2 0 x). exact (IH2 x Hx).
  - exact IH.
  - exact IH.
  - split; [exact IHc | split; [exact IHyes | exact IHno]].
Qed.

(* ============================================================== *)
(* Monotonicity of V along subtyping                               *)
(* ============================================================== *)

Lemma V_subtype : forall T U, subtype T U -> forall v1 v2, V T v1 v2 -> V U v1 v2.
Proof.
  intros T U Hsub.
  induction Hsub as
    [ k1 k2 Hw1 Hw2 Hle
    | T1 T2 U1 U2 k1 k2 Hs1 IH1 Hs2 IH2 Hw1 Hw2 Hle
    | T1 T2 U1 U2 k1 k2 Hs1 IH1 Hs2 IH2 Hw1 Hw2 Hle
    | T1 T2 U1 U2 k1 k2 Hs1 IH1 Hs2 IH2 Hw1 Hw2 Hle
    | T0 U0 V0 Hs1 IH1 Hs2 IH2 ];
    intros v1 v2 HV.
  - destruct (k2.(indirect_reader)) eqn:E2.
    + destruct (k1.(indirect_reader)) eqn:E1.
      * simpl in HV. rewrite E1 in HV. simpl in HV.
        simpl. rewrite E2. simpl.
        destruct HV as (k1' & k2' & Hv1 & Hv2 & Hb1 & Hb2).
        exists k1', k2'. split; [exact Hv1 | split; [exact Hv2 | split]].
        -- exact (security_le_trans _ _ _ Hb1 Hle).
        -- exact (security_le_trans _ _ _ Hb2 Hle).
      * exfalso. destruct Hle as [_ Hf]. simpl in Hf. rewrite E1, E2 in Hf. exact Hf.
    + apply V_high. simpl. exact E2.
  - destruct (k2.(indirect_reader)) eqn:E2.
    + destruct (k1.(indirect_reader)) eqn:E1.
      * simpl in HV. rewrite E1 in HV. simpl in HV.
        simpl. rewrite E2. simpl.
        destruct HV as [(a1 & a2 & ka1 & ka2 & Hv1 & Hv2 & Hb1 & Hb2 & HVp) |
                       (a1 & a2 & ka1 & ka2 & Hv1 & Hv2 & Hb1 & Hb2 & HVp)].
        -- left. exists a1, a2, ka1, ka2. split; [exact Hv1 | split; [exact Hv2 | split]].
           ++ exact (security_le_trans _ _ _ Hb1 Hle).
           ++ split; [exact (security_le_trans _ _ _ Hb2 Hle) | exact (IH1 _ _ HVp)].
        -- right. exists a1, a2, ka1, ka2. split; [exact Hv1 | split; [exact Hv2 | split]].
           ++ exact (security_le_trans _ _ _ Hb1 Hle).
           ++ split; [exact (security_le_trans _ _ _ Hb2 Hle) | exact (IH2 _ _ HVp)].
      * exfalso. destruct Hle as [_ Hf]. simpl in Hf. rewrite E1, E2 in Hf. exact Hf.
    + apply V_high. simpl. exact E2.
  - destruct (k2.(indirect_reader)) eqn:E2.
    + destruct (k1.(indirect_reader)) eqn:E1.
      * simpl in HV. rewrite E1 in HV. simpl in HV.
        simpl. rewrite E2. simpl.
        destruct HV as (a1 & a2 & b1 & b2 & ka1 & ka2 & Hv1 & Hv2 & Hb1 & Hb2 & HV1 & HV2).
        exists a1, a2, b1, b2, ka1, ka2. split; [exact Hv1 | split; [exact Hv2 | split]].
        -- exact (security_le_trans _ _ _ Hb1 Hle).
        -- split.
           ++ exact (security_le_trans _ _ _ Hb2 Hle).
           ++ split; [exact (IH1 _ _ HV1) | exact (IH2 _ _ HV2)].
      * exfalso. destruct Hle as [_ Hf]. simpl in Hf. rewrite E1, E2 in Hf. exact Hf.
    + apply V_high. simpl. exact E2.
  - destruct (k2.(indirect_reader)) eqn:E2.
    + destruct (k1.(indirect_reader)) eqn:E1.
      * simpl in HV. rewrite E1 in HV. simpl in HV.
        simpl. rewrite E2. simpl.
        destruct HV as (Ta1 & body1 & ka1 & Ta2 & body2 & ka2 &
                        Hv1 & Hv2 & Hb1 & Hb2 & Hbeh).
        exists Ta1, body1, ka1, Ta2, body2, ka2. split; [exact Hv1 | split; [exact Hv2 | split]].
        -- exact (security_le_trans _ _ _ Hb1 Hle).
        -- split.
           ++ exact (security_le_trans _ _ _ Hb2 Hle).
           ++ intros w1 w2 r Hvw1 Hvw2 HVw Hflow u1 u2 Hu1 Hvu1 Hu2 Hvu2.
              exact (IH2 u1 u2 (Hbeh w1 w2 r Hvw1 Hvw2 (IH1 w1 w2 HVw)
                     (security_le_reader_flow k1 k2 r Hle Hflow)
                     u1 u2 Hu1 Hvu1 Hu2 Hvu2)).
      * exfalso. destruct Hle as [_ Hf]. simpl in Hf. rewrite E1, E2 in Hf. exact Hf.
    + apply V_high. simpl. exact E2.
  - exact (IH2 _ _ (IH1 _ _ HV)).
Qed.

Lemma security_le_ind_low_flow : forall ka kb,
  security_le ka kb -> kb.(indirect_reader) = Low -> ka.(indirect_reader) = Low.
Proof.
  intros ka kb Hle Hk. apply security_le_ind_low with (kb := kb); [exact Hle |].
  rewrite Hk. simpl. exact I.
Qed.

Lemma transparent_ground_erase : forall kappa T v1 v2,
  transparent_at kappa T -> ground T ->
  flows_to kappa.(indirect_reader) Low ->
  V T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  intros kappa T.
  induction T as [k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k];
    intros v1 v2 Htr Hg Hflow HV.
  - simpl in Hg. destruct Htr as [Hle _].
    assert (Hk : k.(indirect_reader) = Low).
    { apply security_le_ind_low with (kb := kappa); [exact Hle | exact Hflow]. }
    simpl in HV. rewrite Hk in HV. simpl in HV.
    destruct HV as (k1 & k2 & Hv1 & Hv2 & _ & _).
    rewrite Hv1, Hv2. simpl. reflexivity.
  - simpl in Hg. destruct Hg as [Hg1 Hg2].
    destruct Htr as [Hle [Htr1 Htr2]].
    assert (Hk : k.(indirect_reader) = Low).
    { apply security_le_ind_low with (kb := kappa); [exact Hle | exact Hflow]. }
    simpl in HV. rewrite Hk in HV. simpl in HV.
    destruct HV as [(a1 & a2 & ka1 & ka2 & Hv1 & Hv2 & _ & _ & HVp) |
                   (a1 & a2 & ka1 & ka2 & Hv1 & Hv2 & _ & _ & HVp)].
    + rewrite Hv1, Hv2. simpl. f_equal. apply IH1; auto.
    + rewrite Hv1, Hv2. simpl. f_equal. apply IH2; auto.
  - simpl in Hg. destruct Hg as [Hg1 Hg2].
    destruct Htr as [Hle [Htr1 Htr2]].
    assert (Hk : k.(indirect_reader) = Low).
    { apply security_le_ind_low with (kb := kappa); [exact Hle | exact Hflow]. }
    simpl in HV. rewrite Hk in HV. simpl in HV.
    destruct HV as (a1 & a2 & b1 & b2 & ka1 & ka2 & Hv1 & Hv2 & _ & _ & HV1 & HV2).
    rewrite Hv1, Hv2. simpl. f_equal.
    + apply IH1; auto.
    + apply IH2; auto.
  - simpl in Hg. destruct Hg.
Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma1 sigma2, env_rel Gamma sigma1 sigma2 ->
  E T (subst_env sigma1 t) (subst_env sigma2 t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [ Gamma x T0 Hlook Hwf
    | Gamma kappa Hwf
    | L Gamma T1 body T2 kappa HwfT1 Hwfkappa Hbody IHbody
    | Gamma t1 t2 T1 T2 kappa r Ht1 IH1 Ht2 IH2 Hflow
    | Gamma t1 t2 T1 T2 kappa Ht1 IH1 Ht2 IH2 Hwf
    | Gamma t T1 T2 kappa r Ht IH Hflow
    | Gamma t T1 T2 kappa r Ht IH Hflow
    | Gamma t T1 T2 kappa Ht IH HwfT2 Hwfkappa
    | Gamma t T1 T2 kappa HwfT1 Ht IH Hwfkappa
    | L Gamma t b1 b2 T1 T2 T0 kappa r Ht IHt Hflow Hb1 IH1 Hb2 IH2
    | Gamma t T0 l Ht IH
    | Gamma t T0 U Ht IH Hsub
    | Gamma c yes no k T0 r Hc IHc Hyes IHyes Hno IHno Hflow ];
    intros sigma1 sigma2 Henv.
  - (* T_Var *)
    destruct Henv as (Hlc1 & Hlc2 & HE).
    unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
    eapply HE; eauto.
  - (* T_Unit *)
    destruct (kappa.(indirect_reader)) eqn:Ek.
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      simpl. rewrite Ek. simpl.
      exists kappa, kappa. split.
      * exact (multi_unit_eq kappa v1 Hm1).
      * split; [exact (multi_unit_eq kappa v2 Hm2) | split; apply security_le_refl].
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      apply V_high. simpl. exact Ek.
  - (* T_Abs *)
    unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
    pose proof (multi_abs_eq T1 (subst_env sigma1 body) kappa v1 Hm1) as Hv1eq.
    pose proof (multi_abs_eq T1 (subst_env sigma2 body) kappa v2 Hm2) as Hv2eq.
    destruct (kappa.(indirect_reader)) eqn:Ek.
    + simpl. rewrite Ek. simpl.
      exists T1, (subst_env sigma1 body), kappa, T1, (subst_env sigma2 body), kappa.
      split; [exact Hv1eq | split; [exact Hv2eq | split]].
      * apply security_le_refl.
      * split.
        -- apply security_le_refl.
        -- intros w1 w2 r Hvalw1 Hvalw2 HVw Hflow u1 u2 Happ1 Hvalu1 Happ2 Hvalu2.
           rewrite Hv1eq in Happ1, Hval1.
           rewrite Hv2eq in Happ2, Hval2.
           pose proof (app_abs_multi T1 (subst_env sigma1 body) kappa w1 r u1
                         Hval1 Hvalw1 Hflow Happ1 Hvalu1) as Hprot1.
           pose proof (app_abs_multi T1 (subst_env sigma2 body) kappa w2 r u2
                         Hval2 Hvalw2 Hflow Happ2 Hvalu2) as Hprot2.
           rewrite Ek in Hprot1, Hprot2.
           destruct (protect_multi_decomp (tm_protect Low (open (subst_env sigma1 body) w1))
                       u1 Hprot1 Hvalu1 Low (open (subst_env sigma1 body) w1) eq_refl)
             as (u1' & Hmu1 & Hvu1 & Hu1).
           destruct (protect_multi_decomp (tm_protect Low (open (subst_env sigma2 body) w2))
                       u2 Hprot2 Hvalu2 Low (open (subst_env sigma2 body) w2) eq_refl)
             as (u2' & Hmu2 & Hvu2 & Hu2).
           assert (Hu1eq : u1 = u1') by (rewrite Hu1; apply protect_value_low).
           assert (Hu2eq : u2 = u2') by (rewrite Hu2; apply protect_value_low).
           rewrite Hu1eq, Hu2eq.
           destruct Henv as (Hlc1 & Hlc2 & HE).
           set (x := fresh_atom (L ++ fv body)).
           assert (HxL : ~ In x L).
           { intro Hx. apply (fresh_atom_fresh (L ++ fv body)). apply in_or_app; auto. }
           assert (Hxbody : ~ In x (fv body)).
           { intro Hx. apply (fresh_atom_fresh (L ++ fv body)). apply in_or_app; auto. }
           pose proof (IHbody x HxL (env_update sigma1 x w1) (env_update sigma2 x w2)
                         (env_rel_update Gamma sigma1 sigma2 x T1 w1 w2
                            (conj Hlc1 (conj Hlc2 HE)) Hvalw1 Hvalw2 HVw)) as HEbody.
           assert (Hrew1 : subst_env (env_update sigma1 x w1) (open body (tm_fvar x)) =
                           open (subst_env sigma1 body) w1).
           { apply (subst_env_open_env_update sigma1 x w1 body).
             - apply value_lc. exact Hvalw1.
             - exact Hlc1.
             - exact Hxbody. }
           assert (Hrew2 : subst_env (env_update sigma2 x w2) (open body (tm_fvar x)) =
                           open (subst_env sigma2 body) w2).
           { apply (subst_env_open_env_update sigma2 x w2 body).
             - apply value_lc. exact Hvalw2.
             - exact Hlc2.
             - exact Hxbody. }
           rewrite Hrew1 in HEbody. rewrite Hrew2 in HEbody.
           eapply HEbody; eauto.
    + apply V_high. simpl. exact Ek.
  - (* T_App *)
    destruct (kappa.(indirect_reader)) eqn:Ek.
    + assert (Hty : ty_protect Low T2 = T2) by apply ty_protect_low.
      rewrite Hty. unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      destruct (app_multi_decomp _ _ Hm1 Hval1
                  (subst_env sigma1 t1) (subst_env sigma1 t2) r eq_refl)
        as (a1' & b1' & Ha1 & Hva1 & Hb1 & Hvb1 & Hr1).
      destruct (app_multi_decomp _ _ Hm2 Hval2
                  (subst_env sigma2 t1) (subst_env sigma2 t2) r eq_refl)
        as (a2' & b2' & Ha2 & Hva2 & Hb2 & Hvb2 & Hr2).
      destruct Henv as (Hlc1 & Hlc2 & HE).
      pose proof (IH1 sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                    a1' a2' Ha1 Hva1 Ha2 Hva2) as HVf.
      pose proof (IH2 sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                    b1' b2' Hb1 Hvb1 Hb2 Hvb2) as HVa.
      simpl in HVf. rewrite Ek in HVf. simpl in HVf.
      destruct HVf as (Ta1 & body1 & ka1 & Ta2 & body2 & ka2 &
                       Hv1 & Hv2 & _ & _ & Hbeh).
      exact (Hbeh b1' b2' r Hvb1 Hvb2 HVa Hflow v1 v2 Hr1 Hval1 Hr2 Hval2).
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      apply V_high. apply ty_protect_high_ind.
  - (* T_Pair *)
    destruct (kappa.(indirect_reader)) eqn:Ek.
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      simpl. rewrite Ek. simpl.
      destruct (pair_multi_decomp _ _ Hm1 Hval1
                  (subst_env sigma1 t1) (subst_env sigma1 t2) kappa eq_refl)
        as (a1' & b1' & Ha1 & Hva1 & Hb1 & Hvb1 & Hu1).
      destruct (pair_multi_decomp _ _ Hm2 Hval2
                  (subst_env sigma2 t1) (subst_env sigma2 t2) kappa eq_refl)
        as (a2' & b2' & Ha2 & Hva2 & Hb2 & Hvb2 & Hu2).
      destruct Henv as (Hlc1 & Hlc2 & HE).
      pose proof (IH1 sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                    a1' a2' Ha1 Hva1 Ha2 Hva2) as HV1.
      pose proof (IH2 sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                    b1' b2' Hb1 Hvb1 Hb2 Hvb2) as HV2.
      exists a1', a2', b1', b2', kappa, kappa.
      split; [exact Hu1 | split; [exact Hu2 | split]].
      * apply security_le_refl.
      * split; [apply security_le_refl | split; assumption].
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      apply V_high. simpl. exact Ek.
  - (* T_Fst *)
    destruct (kappa.(indirect_reader)) eqn:Ek.
    + assert (Hty : ty_protect Low T1 = T1) by apply ty_protect_low.
      rewrite Hty. unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      destruct (fst_multi_decomp _ _ Hm1 Hval1 (subst_env sigma1 t) r eq_refl)
        as (s1' & Hs1 & Hvs1 & Hr1).
      destruct (fst_multi_decomp _ _ Hm2 Hval2 (subst_env sigma2 t) r eq_refl)
        as (s2' & Hs2 & Hvs2 & Hr2).
      destruct Henv as (Hlc1 & Hlc2 & HE).
      pose proof (IH sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                    s1' s2' Hs1 Hvs1 Hs2 Hvs2) as HVp.
      simpl in HVp. rewrite Ek in HVp. simpl in HVp.
      destruct HVp as (w1 & w2 & z1 & z2 & ka1 & ka2 &
                       Hs1eq & Hs2eq & Hb1 & Hb2 & HVw1 & HVw2).
      rewrite Hs1eq in Hr1, Hvs1. rewrite Hs2eq in Hr2, Hvs2.
      destruct (value_inv_pair w1 z1 ka1 Hvs1) as [Hvw1 Hvz1].
      destruct (value_inv_pair w2 z2 ka2 Hvs2) as [Hvw2 Hvz2].
      assert (Hk1 : ka1.(indirect_reader) = Low)
        by (apply security_le_ind_low_flow with (kb := kappa); auto).
      assert (Hk2 : ka2.(indirect_reader) = Low)
        by (apply security_le_ind_low_flow with (kb := kappa); auto).
      pose proof (fst_pair_multi w1 z1 ka1 r v1 Hvw1 Hvz1
                    (security_le_reader_flow ka1 kappa r Hb1 Hflow) Hr1 Hval1) as Hp1.
      pose proof (fst_pair_multi w2 z2 ka2 r v2 Hvw2 Hvz2
                    (security_le_reader_flow ka2 kappa r Hb2 Hflow) Hr2 Hval2) as Hp2.
      rewrite Hk1 in Hp1. rewrite Hk2 in Hp2.
      destruct (protect_multi_decomp (tm_protect Low w1) v1 Hp1 Hval1 Low w1 eq_refl)
        as (u1' & Hmu1 & Hvu1 & Hu1).
      destruct (protect_multi_decomp (tm_protect Low w2) v2 Hp2 Hval2 Low w2 eq_refl)
        as (u2' & Hmu2 & Hvu2 & Hu2).
      assert (Hu1eq : v1 = u1') by (rewrite Hu1; apply protect_value_low).
      assert (Hu2eq : v2 = u2') by (rewrite Hu2; apply protect_value_low).
      assert (Hw1eq : u1' = w1) by (eapply multi_value_eq; eauto).
      assert (Hw2eq : u2' = w2) by (eapply multi_value_eq; eauto).
      rewrite Hu1eq, Hu2eq, Hw1eq, Hw2eq. exact HVw1.
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      apply V_high. apply ty_protect_high_ind.
  - (* T_Snd *)
    destruct (kappa.(indirect_reader)) eqn:Ek.
    + assert (Hty : ty_protect Low T2 = T2) by apply ty_protect_low.
      rewrite Hty. unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      destruct (snd_multi_decomp _ _ Hm1 Hval1 (subst_env sigma1 t) r eq_refl)
        as (s1' & Hs1 & Hvs1 & Hr1).
      destruct (snd_multi_decomp _ _ Hm2 Hval2 (subst_env sigma2 t) r eq_refl)
        as (s2' & Hs2 & Hvs2 & Hr2).
      destruct Henv as (Hlc1 & Hlc2 & HE).
      pose proof (IH sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                    s1' s2' Hs1 Hvs1 Hs2 Hvs2) as HVp.
      simpl in HVp. rewrite Ek in HVp. simpl in HVp.
      destruct HVp as (w1 & w2 & z1 & z2 & ka1 & ka2 &
                       Hs1eq & Hs2eq & Hb1 & Hb2 & HVw1 & HVw2).
      rewrite Hs1eq in Hr1, Hvs1. rewrite Hs2eq in Hr2, Hvs2.
      destruct (value_inv_pair w1 z1 ka1 Hvs1) as [Hvw1 Hvz1].
      destruct (value_inv_pair w2 z2 ka2 Hvs2) as [Hvw2 Hvz2].
      assert (Hk1 : ka1.(indirect_reader) = Low)
        by (apply security_le_ind_low_flow with (kb := kappa); auto).
      assert (Hk2 : ka2.(indirect_reader) = Low)
        by (apply security_le_ind_low_flow with (kb := kappa); auto).
      pose proof (snd_pair_multi w1 z1 ka1 r v1 Hvw1 Hvz1
                    (security_le_reader_flow ka1 kappa r Hb1 Hflow) Hr1 Hval1) as Hp1.
      pose proof (snd_pair_multi w2 z2 ka2 r v2 Hvw2 Hvz2
                    (security_le_reader_flow ka2 kappa r Hb2 Hflow) Hr2 Hval2) as Hp2.
      rewrite Hk1 in Hp1. rewrite Hk2 in Hp2.
      destruct (protect_multi_decomp (tm_protect Low z1) v1 Hp1 Hval1 Low z1 eq_refl)
        as (u1' & Hmu1 & Hvu1 & Hu1).
      destruct (protect_multi_decomp (tm_protect Low z2) v2 Hp2 Hval2 Low z2 eq_refl)
        as (u2' & Hmu2 & Hvu2 & Hu2).
      assert (Hu1eq : v1 = u1') by (rewrite Hu1; apply protect_value_low).
      assert (Hu2eq : v2 = u2') by (rewrite Hu2; apply protect_value_low).
      assert (Hw1eq : u1' = z1) by (eapply multi_value_eq; eauto).
      assert (Hw2eq : u2' = z2) by (eapply multi_value_eq; eauto).
      rewrite Hu1eq, Hu2eq, Hw1eq, Hw2eq. exact HVw2.
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      apply V_high. apply ty_protect_high_ind.
  - (* T_Inl *)
    destruct (kappa.(indirect_reader)) eqn:Ek.
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      simpl. rewrite Ek. simpl.
      destruct (inl_multi_decomp _ _ Hm1 Hval1 (subst_env sigma1 t) kappa eq_refl)
        as (a1' & Ha1 & Hva1 & Hu1).
      destruct (inl_multi_decomp _ _ Hm2 Hval2 (subst_env sigma2 t) kappa eq_refl)
        as (a2' & Ha2 & Hva2 & Hu2).
      destruct Henv as (Hlc1 & Hlc2 & HE).
      pose proof (IH sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                    a1' a2' Ha1 Hva1 Ha2 Hva2) as HVa.
      left. exists a1', a2', kappa, kappa.
      split; [exact Hu1 | split; [exact Hu2 | split]].
      * apply security_le_refl.
      * split; [apply security_le_refl | exact HVa].
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      apply V_high. simpl. exact Ek.
  - (* T_Inr *)
    destruct (kappa.(indirect_reader)) eqn:Ek.
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      simpl. rewrite Ek. simpl.
      destruct (inr_multi_decomp _ _ Hm1 Hval1 (subst_env sigma1 t) kappa eq_refl)
        as (a1' & Ha1 & Hva1 & Hu1).
      destruct (inr_multi_decomp _ _ Hm2 Hval2 (subst_env sigma2 t) kappa eq_refl)
        as (a2' & Ha2 & Hva2 & Hu2).
      destruct Henv as (Hlc1 & Hlc2 & HE).
      pose proof (IH sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                    a1' a2' Ha1 Hva1 Ha2 Hva2) as HVa.
      right. exists a1', a2', kappa, kappa.
      split; [exact Hu1 | split; [exact Hu2 | split]].
      * apply security_le_refl.
      * split; [apply security_le_refl | exact HVa].
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      apply V_high. simpl. exact Ek.
  - (* T_Case *)
    destruct (kappa.(indirect_reader)) eqn:Ek.
    + assert (Hty : ty_protect Low T0 = T0) by apply ty_protect_low.
      rewrite Hty. unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      destruct (case_multi_decomp _ _ Hm1 Hval1 (subst_env sigma1 t)
                  (subst_env sigma1 b1) (subst_env sigma1 b2) r eq_refl)
        as (s1' & Hs1 & Hvs1 & Hr1).
      destruct (case_multi_decomp _ _ Hm2 Hval2 (subst_env sigma2 t)
                  (subst_env sigma2 b1) (subst_env sigma2 b2) r eq_refl)
        as (s2' & Hs2 & Hvs2 & Hr2).
      destruct Henv as (Hlc1 & Hlc2 & HE).
      pose proof (IHt sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                    s1' s2' Hs1 Hvs1 Hs2 Hvs2) as HVs.
      simpl in HVs. rewrite Ek in HVs. simpl in HVs.
      destruct HVs as [(a1 & a2 & ka1 & ka2 & Hs1eq & Hs2eq & Hka1 & Hka2 & HVa) |
                       (a1 & a2 & ka1 & ka2 & Hs1eq & Hs2eq & Hka1 & Hka2 & HVa)].
      * (* inl *)
        rewrite Hs1eq in Hr1, Hvs1. rewrite Hs2eq in Hr2, Hvs2.
        pose proof (value_inv_inl a1 ka1 Hvs1) as Hva1.
        pose proof (value_inv_inl a2 ka2 Hvs2) as Hva2.
        assert (Hk1 : ka1.(indirect_reader) = Low)
          by (apply security_le_ind_low_flow with (kb := kappa); auto).
        assert (Hk2 : ka2.(indirect_reader) = Low)
          by (apply security_le_ind_low_flow with (kb := kappa); auto).
        pose proof (case_inl_multi a1 ka1 (subst_env sigma1 b1) (subst_env sigma1 b2) r v1
                      Hva1 (security_le_reader_flow ka1 kappa r Hka1 Hflow) Hr1 Hval1) as Hp1.
        pose proof (case_inl_multi a2 ka2 (subst_env sigma2 b1) (subst_env sigma2 b2) r v2
                      Hva2 (security_le_reader_flow ka2 kappa r Hka2 Hflow) Hr2 Hval2) as Hp2.
        rewrite Hk1 in Hp1. rewrite Hk2 in Hp2.
        destruct (protect_multi_decomp
                    (tm_protect Low (open (subst_env sigma1 b1) a1)) v1 Hp1 Hval1
                    Low (open (subst_env sigma1 b1) a1) eq_refl) as (u1' & Hmu1 & Hvu1 & Hu1).
        destruct (protect_multi_decomp
                    (tm_protect Low (open (subst_env sigma2 b1) a2)) v2 Hp2 Hval2
                    Low (open (subst_env sigma2 b1) a2) eq_refl) as (u2' & Hmu2 & Hvu2 & Hu2).
        assert (Hu1eq : v1 = u1') by (rewrite Hu1; apply protect_value_low).
        assert (Hu2eq : v2 = u2') by (rewrite Hu2; apply protect_value_low).
        rewrite Hu1eq, Hu2eq.
        set (x := fresh_atom (L ++ fv b1)).
        assert (HxL : ~ In x L).
        { intro Hx. apply (fresh_atom_fresh (L ++ fv b1)). apply in_or_app; auto. }
        assert (Hxb : ~ In x (fv b1)).
        { intro Hx. apply (fresh_atom_fresh (L ++ fv b1)). apply in_or_app; auto. }
        pose proof (IH1 x HxL (env_update sigma1 x a1) (env_update sigma2 x a2)
                      (env_rel_update Gamma sigma1 sigma2 x T1 a1 a2
                         (conj Hlc1 (conj Hlc2 HE)) Hva1 Hva2 HVa)) as HEbody.
        assert (Hrew1 : subst_env (env_update sigma1 x a1) (open b1 (tm_fvar x)) =
                        open (subst_env sigma1 b1) a1).
        { apply (subst_env_open_env_update sigma1 x a1 b1).
          - apply value_lc. exact Hva1.
          - exact Hlc1.
          - exact Hxb. }
        assert (Hrew2 : subst_env (env_update sigma2 x a2) (open b1 (tm_fvar x)) =
                        open (subst_env sigma2 b1) a2).
        { apply (subst_env_open_env_update sigma2 x a2 b1).
          - apply value_lc. exact Hva2.
          - exact Hlc2.
          - exact Hxb. }
        rewrite Hrew1 in HEbody. rewrite Hrew2 in HEbody.
        eapply HEbody; eauto.
      * (* inr *)
        rewrite Hs1eq in Hr1, Hvs1. rewrite Hs2eq in Hr2, Hvs2.
        pose proof (value_inv_inr a1 ka1 Hvs1) as Hva1.
        pose proof (value_inv_inr a2 ka2 Hvs2) as Hva2.
        assert (Hk1 : ka1.(indirect_reader) = Low)
          by (apply security_le_ind_low_flow with (kb := kappa); auto).
        assert (Hk2 : ka2.(indirect_reader) = Low)
          by (apply security_le_ind_low_flow with (kb := kappa); auto).
        pose proof (case_inr_multi a1 ka1 (subst_env sigma1 b1) (subst_env sigma1 b2) r v1
                      Hva1 (security_le_reader_flow ka1 kappa r Hka1 Hflow) Hr1 Hval1) as Hp1.
        pose proof (case_inr_multi a2 ka2 (subst_env sigma2 b1) (subst_env sigma2 b2) r v2
                      Hva2 (security_le_reader_flow ka2 kappa r Hka2 Hflow) Hr2 Hval2) as Hp2.
        rewrite Hk1 in Hp1. rewrite Hk2 in Hp2.
        destruct (protect_multi_decomp
                    (tm_protect Low (open (subst_env sigma1 b2) a1)) v1 Hp1 Hval1
                    Low (open (subst_env sigma1 b2) a1) eq_refl) as (u1' & Hmu1 & Hvu1 & Hu1).
        destruct (protect_multi_decomp
                    (tm_protect Low (open (subst_env sigma2 b2) a2)) v2 Hp2 Hval2
                    Low (open (subst_env sigma2 b2) a2) eq_refl) as (u2' & Hmu2 & Hvu2 & Hu2).
        assert (Hu1eq : v1 = u1') by (rewrite Hu1; apply protect_value_low).
        assert (Hu2eq : v2 = u2') by (rewrite Hu2; apply protect_value_low).
        rewrite Hu1eq, Hu2eq.
        set (x := fresh_atom (L ++ fv b2)).
        assert (HxL : ~ In x L).
        { intro Hx. apply (fresh_atom_fresh (L ++ fv b2)). apply in_or_app; auto. }
        assert (Hxb : ~ In x (fv b2)).
        { intro Hx. apply (fresh_atom_fresh (L ++ fv b2)). apply in_or_app; auto. }
        pose proof (IH2 x HxL (env_update sigma1 x a1) (env_update sigma2 x a2)
                      (env_rel_update Gamma sigma1 sigma2 x T2 a1 a2
                         (conj Hlc1 (conj Hlc2 HE)) Hva1 Hva2 HVa)) as HEbody.
        assert (Hrew1 : subst_env (env_update sigma1 x a1) (open b2 (tm_fvar x)) =
                        open (subst_env sigma1 b2) a1).
        { apply (subst_env_open_env_update sigma1 x a1 b2).
          - apply value_lc. exact Hva1.
          - exact Hlc1.
          - exact Hxb. }
        assert (Hrew2 : subst_env (env_update sigma2 x a2) (open b2 (tm_fvar x)) =
                        open (subst_env sigma2 b2) a2).
        { apply (subst_env_open_env_update sigma2 x a2 b2).
          - apply value_lc. exact Hva2.
          - exact Hlc2.
          - exact Hxb. }
        rewrite Hrew1 in HEbody. rewrite Hrew2 in HEbody.
        eapply HEbody; eauto.
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      apply V_high. apply ty_protect_high_ind.
  - (* T_Protect *)
    destruct l eqn:El.
    + assert (Hty : ty_protect Low T0 = T0) by (apply ty_protect_low).
      rewrite Hty. unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      destruct (protect_multi_decomp _ _ Hm1 Hval1 Low (subst_env sigma1 t) eq_refl)
        as (u1' & Hmu1 & Hvu1 & Hu1).
      destruct (protect_multi_decomp _ _ Hm2 Hval2 Low (subst_env sigma2 t) eq_refl)
        as (u2' & Hmu2 & Hvu2 & Hu2).
      assert (Hu1eq : v1 = u1') by (rewrite Hu1; apply protect_value_low).
      assert (Hu2eq : v2 = u2') by (rewrite Hu2; apply protect_value_low).
      rewrite Hu1eq, Hu2eq.
      destruct Henv as (Hlc1 & Hlc2 & HE).
      pose proof (IH sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                    u1' u2' Hmu1 Hvu1 Hmu2 Hvu2) as HV.
      exact HV.
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      apply V_high. apply ty_protect_high_ind.
  - (* T_Sub *)
    unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
    destruct Henv as (Hlc1 & Hlc2 & HE).
    pose proof (IH sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                  v1 v2 Hm1 Hval1 Hm2 Hval2) as HV.
    exact (V_subtype T0 U Hsub v1 v2 HV).
  - (* T_If *)
    destruct (k.(indirect_reader)) eqn:Ek.
    + assert (Hty : ty_protect Low T0 = T0) by apply ty_protect_low.
      rewrite Hty. unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      destruct (if_multi_decomp _ _ Hm1 Hval1 (subst_env sigma1 c)
                  (subst_env sigma1 yes) (subst_env sigma1 no) r eq_refl)
        as (c1' & Hc1 & Hvc1 & Hr1).
      destruct (if_multi_decomp _ _ Hm2 Hval2 (subst_env sigma2 c)
                  (subst_env sigma2 yes) (subst_env sigma2 no) r eq_refl)
        as (c2' & Hc2 & Hvc2 & Hr2).
      destruct Henv as (Hlc1 & Hlc2 & HE).
      pose proof (IHc sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                    c1' c2' Hc1 Hvc1 Hc2 Hvc2) as HVs.
      simpl in HVs. rewrite Ek in HVs. simpl in HVs.
      destruct HVs as [(a1 & a2 & ka1 & ka2 & Hc1eq & Hc2eq & Hb1 & Hb2 & HVa) |
                       (a1 & a2 & ka1 & ka2 & Hc1eq & Hc2eq & Hb1 & Hb2 & HVa)].
      * (* true *)
        rewrite Hc1eq in Hr1, Hvc1. rewrite Hc2eq in Hr2, Hvc2.
        pose proof (value_inv_inl a1 ka1 Hvc1) as Hva1.
        pose proof (value_inv_inl a2 ka2 Hvc2) as Hva2.
        assert (Hk1 : ka1.(indirect_reader) = Low)
          by (apply security_le_ind_low_flow with (kb := k); auto).
        assert (Hk2 : ka2.(indirect_reader) = Low)
          by (apply security_le_ind_low_flow with (kb := k); auto).
        pose proof (if_inl_multi a1 ka1 (subst_env sigma1 yes) (subst_env sigma1 no) r v1
                      Hva1 (security_le_reader_flow ka1 k r Hb1 Hflow) Hr1 Hval1) as Hp1.
        pose proof (if_inl_multi a2 ka2 (subst_env sigma2 yes) (subst_env sigma2 no) r v2
                      Hva2 (security_le_reader_flow ka2 k r Hb2 Hflow) Hr2 Hval2) as Hp2.
        rewrite Hk1 in Hp1. rewrite Hk2 in Hp2.
        destruct (protect_multi_decomp (tm_protect Low (subst_env sigma1 yes)) v1
                    Hp1 Hval1 Low (subst_env sigma1 yes) eq_refl) as (u1' & Hmu1 & Hvu1 & Hu1).
        destruct (protect_multi_decomp (tm_protect Low (subst_env sigma2 yes)) v2
                    Hp2 Hval2 Low (subst_env sigma2 yes) eq_refl) as (u2' & Hmu2 & Hvu2 & Hu2).
        assert (Hu1eq : v1 = u1') by (rewrite Hu1; apply protect_value_low).
        assert (Hu2eq : v2 = u2') by (rewrite Hu2; apply protect_value_low).
        rewrite Hu1eq, Hu2eq.
        pose proof (IHyes sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                      u1' u2' Hmu1 Hvu1 Hmu2 Hvu2) as HV.
        exact HV.
      * (* false *)
        rewrite Hc1eq in Hr1, Hvc1. rewrite Hc2eq in Hr2, Hvc2.
        pose proof (value_inv_inr a1 ka1 Hvc1) as Hva1.
        pose proof (value_inv_inr a2 ka2 Hvc2) as Hva2.
        assert (Hk1 : ka1.(indirect_reader) = Low)
          by (apply security_le_ind_low_flow with (kb := k); auto).
        assert (Hk2 : ka2.(indirect_reader) = Low)
          by (apply security_le_ind_low_flow with (kb := k); auto).
        pose proof (if_inr_multi a1 ka1 (subst_env sigma1 yes) (subst_env sigma1 no) r v1
                      Hva1 (security_le_reader_flow ka1 k r Hb1 Hflow) Hr1 Hval1) as Hp1.
        pose proof (if_inr_multi a2 ka2 (subst_env sigma2 yes) (subst_env sigma2 no) r v2
                      Hva2 (security_le_reader_flow ka2 k r Hb2 Hflow) Hr2 Hval2) as Hp2.
        rewrite Hk1 in Hp1. rewrite Hk2 in Hp2.
        destruct (protect_multi_decomp (tm_protect Low (subst_env sigma1 no)) v1
                    Hp1 Hval1 Low (subst_env sigma1 no) eq_refl) as (u1' & Hmu1 & Hvu1 & Hu1).
        destruct (protect_multi_decomp (tm_protect Low (subst_env sigma2 no)) v2
                    Hp2 Hval2 Low (subst_env sigma2 no) eq_refl) as (u2' & Hmu2 & Hvu2 & Hu2).
        assert (Hu1eq : v1 = u1') by (rewrite Hu1; apply protect_value_low).
        assert (Hu2eq : v2 = u2') by (rewrite Hu2; apply protect_value_low).
        rewrite Hu1eq, Hu2eq.
        pose proof (IHno sigma1 sigma2 (conj Hlc1 (conj Hlc2 HE))
                      u1' u2' Hmu1 Hvu1 Hmu2 Hvu2) as HV.
        exact HV.
    + unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      apply V_high. apply ty_protect_high_ind.
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
  intros C t1 t2 T_secret T_result Hty1 Hty2 Hctx Hg Htr Hnof.
  destruct Hctx as (L & Hctx).
  assert (Hres : (security_of T_result).(indirect_reader) = Low).
  { destruct ((security_of T_result).(indirect_reader)) eqn:E.
    - reflexivity.
    - exfalso. apply Hnof.
      destruct ((security_of T_secret).(indirect_reader)); simpl; reflexivity. }
  assert (Hsec : (security_of T_secret).(indirect_reader) = High).
  { destruct ((security_of T_secret).(indirect_reader)) eqn:E.
    - exfalso. apply Hnof.
      destruct ((security_of T_result).(indirect_reader)); simpl; reflexivity.
    - reflexivity. }
  set (x := fresh_atom (L ++ fv_context C)).
  assert (HxL : ~ In x L).
  { intro Hx. apply (fresh_atom_fresh (L ++ fv_context C)). apply in_or_app; auto. }
  assert (HxC : ~ In x (fv_context C)).
  { intro Hx. apply (fresh_atom_fresh (L ++ fv_context C)). apply in_or_app; auto. }
  assert (Htyx : has_type (update empty x T_secret) (plug C (tm_fvar x)) T_result)
    by (apply Hctx; exact HxL).
  set (sigma1 := env_update (fun y : atom => tm_fvar y) x t1).
  set (sigma2 := env_update (fun y : atom => tm_fvar y) x t2).
  assert (Hsigma1x : sigma1 x = t1) by (unfold sigma1; apply env_update_same).
  assert (Hsigma2x : sigma2 x = t2) by (unfold sigma2; apply env_update_same).
  assert (Hident1 : forall y, y <> x -> sigma1 y = tm_fvar y).
  { intros y Hy. unfold sigma1. apply env_update_other. exact Hy. }
  assert (Hident2 : forall y, y <> x -> sigma2 y = tm_fvar y).
  { intros y Hy. unfold sigma2. apply env_update_other. exact Hy. }
  assert (Hlc1 : forall y, locally_closed (sigma1 y)).
  { intro y. unfold sigma1, env_update.
    destruct (Nat.eqb y x) eqn:E.
    - exact (has_type_lc empty t1 T_secret Hty1).
    - simpl. exact I. }
  assert (Hlc2 : forall y, locally_closed (sigma2 y)).
  { intro y. unfold sigma2, env_update.
    destruct (Nat.eqb y x) eqn:E.
    - exact (has_type_lc empty t2 T_secret Hty2).
    - simpl. exact I. }
  assert (Henv : env_rel (update empty x T_secret) sigma1 sigma2).
  { split; [exact Hlc1 | split; [exact Hlc2 |]].
    intros y T Hlook.
    destruct (Nat.eqb y x) eqn:Ey.
    - apply Nat.eqb_eq in Ey. subst y.
      rewrite lookup_update_same in Hlook. injection Hlook as HT. subst T.
      simpl. unfold E. intros v1 v2 Hm1 Hval1 Hm2 Hval2.
      apply V_high. exact Hsec.
    - apply Nat.eqb_neq in Ey.
      rewrite (lookup_update_other empty x y T_secret Ey) in Hlook.
      simpl in Hlook. discriminate Hlook. }
  pose proof (fundamental (update empty x T_secret) (plug C (tm_fvar x)) T_result Htyx
                sigma1 sigma2 Henv) as HE.
  rewrite (subst_env_plug_x sigma1 C x t1 Hsigma1x Hident1 HxC) in HE.
  rewrite (subst_env_plug_x sigma2 C x t2 Hsigma2x Hident2 HxC) in HE.
  intros v1 v2 Hev1 Hev2.
  destruct Hev1 as [Hm1 Hval1]. destruct Hev2 as [Hm2 Hval2].
  pose proof (HE v1 v2 Hm1 Hval1 Hm2 Hval2) as HV.
  apply (transparent_ground_erase (security_of T_result) T_result v1 v2 Htr Hg).
  - rewrite Hres. simpl. exact I.
  - exact HV.
Qed.
