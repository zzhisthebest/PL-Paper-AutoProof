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
(* Basic lemmas about labels, joins and securities               *)
(* ============================================================ *)

Lemma flows_to_refl : forall l : label, flows_to l l.
Proof. destruct l; simpl; auto. Qed.

Lemma flows_to_trans : forall a b c : label,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. destruct a, b, c; simpl in *; auto. Qed.

Lemma flows_to_join_r : forall a b : label, flows_to a (join a b).
Proof. destruct a, b; simpl; auto. Qed.

Lemma flows_to_join_l : forall a b : label, flows_to b (join a b).
Proof. destruct a, b; simpl; auto. Qed.

Lemma join_low_l : forall a : label, join Low a = a.
Proof. destruct a; reflexivity. Qed.

Lemma join_low_r : forall a : label, join a Low = a.
Proof. destruct a; reflexivity. Qed.

Lemma join_assoc : forall a b c : label,
  join (join a b) c = join a (join b c).
Proof. destruct a, b, c; reflexivity. Qed.

Lemma join_idem : forall a b : label, join (join a b) b = join a b.
Proof. destruct a, b; reflexivity. Qed.

Lemma join_comm : forall a b : label, join a b = join b a.
Proof. destruct a, b; reflexivity. Qed.

Lemma flows_to_join_iff : forall a b c : label,
  flows_to (join a b) c <-> flows_to a c /\ flows_to b c.
Proof. destruct a, b, c; simpl; intuition. Qed.

Lemma join_mono : forall a a' b b' : label,
  flows_to a a' -> flows_to b b' -> flows_to (join a b) (join a' b').
Proof.
  intros a a' b b' Ha Hb.
  apply flows_to_join_iff. split.
  - eapply flows_to_trans; [exact Ha | apply flows_to_join_r].
  - eapply flows_to_trans; [exact Hb | apply flows_to_join_l].
Qed.

Lemma not_flows_to : forall a b : label,
  ~ flows_to a b -> a = High /\ b = Low.
Proof.
  destruct a, b; simpl; auto; tauto.
Qed.

Lemma security_le_refl : forall kappa : security, security_le kappa kappa.
Proof.
  intros [r i]; simpl. split; apply flows_to_refl.
Qed.

Lemma security_le_trans : forall k1 k2 k3 : security,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros k1 k2 k3 [H1 H2] [H3 H4]. simpl in *.
  split; eapply flows_to_trans; eauto.
Qed.

Lemma protect_security_mono : forall (p q : label) (k1 k2 : security),
  flows_to p q -> security_le k1 k2 ->
  security_le (protect_security k1 p) (protect_security k2 q).
Proof.
  intros p q [r1 i1] [r2 i2] Hpq Hle.
  destruct Hle as [Hr Hi].
  change (flows_to (join r1 p) (join r2 q) /\
          flows_to (join i1 p) (join i2 q)).
  split; apply join_mono; assumption.
Qed.

Lemma protect_security_twice : forall (kappa : security) (p q : label),
  protect_security (protect_security kappa p) q =
  protect_security kappa (join p q).
Proof.
  intros [r i] p q; destruct r, i, p, q; reflexivity.
Qed.

Lemma protect_security_low : forall kappa : security,
  protect_security kappa Low = kappa.
Proof.
  intros [r i]; destruct r, i; reflexivity.
Qed.

Lemma protect_security_join_low_l : forall (kappa : security) (p : label),
  protect_security (protect_security kappa p) Low = protect_security kappa p.
Proof.
  intros. rewrite protect_security_twice, join_low_r. reflexivity.
Qed.

Lemma security_of_ty_protect : forall (l : label) (T : ty),
  security_of (ty_protect l T) = protect_security (security_of T) l.
Proof. destruct T; reflexivity. Qed.

(* ============================================================ *)
(* Fresh atoms                                                   *)
(* ============================================================ *)

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Lemma max_list_bound : forall (l : list nat) (x : nat),
  In x l -> x <= max_list l.
Proof.
  induction l as [| a l IH]; simpl; intros x Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Definition fresh_from (L : list atom) : atom := S (max_list L).

Lemma fresh_from_notin : forall L : list atom, ~ In (fresh_from L) L.
Proof.
  intros L Hin. apply max_list_bound in Hin. unfold fresh_from in Hin. lia.
Qed.

(* ============================================================ *)
(* Value lemmas                                                  *)
(* ============================================================ *)

Lemma value_step_false : forall (v t : tm), value v -> step v t -> False.
Proof.
  intros v t Hv. revert t. induction Hv; intros t Hs; inversion Hs; subst; eauto.
Qed.

Lemma value_protect_value : forall (v : tm) (l : label),
  value v -> value (protect_value v l).
Proof.
  intros v l Hv. destruct v; simpl.
  - inversion Hv.
  - inversion Hv.
  - constructor.
  - constructor; inversion Hv; assumption.
  - inversion Hv.
  - constructor; inversion Hv; assumption.
  - inversion Hv.
  - inversion Hv.
  - constructor; inversion Hv; assumption.
  - constructor; inversion Hv; assumption.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
Qed.

Lemma value_abs_annot : forall (T : ty) (body : tm) (k1 k2 : security),
  value (tm_abs T body k1) -> value (tm_abs T body k2).
Proof.
  intros T body k1 k2 H. inversion H. constructor. assumption.
Qed.

Lemma value_pair_inv : forall (v1 v2 : tm) (k : security),
  value (tm_pair v1 v2 k) -> value v1 /\ value v2.
Proof. intros. inversion H. auto. Qed.

Lemma value_inl_inv : forall (v : tm) (k : security), value (tm_inl v k) -> value v.
Proof. intros. inversion H. auto. Qed.

Lemma value_inr_inv : forall (v : tm) (k : security), value (tm_inr v k) -> value v.
Proof. intros. inversion H. auto. Qed.

Lemma value_protect_value_inv : forall (v : tm) (l : label),
  value (protect_value v l) -> value v.
Proof.
  intros v l. destruct v; simpl; intro H.
  - inversion H.
  - inversion H.
  - constructor.
  - constructor; inversion H; assumption.
  - inversion H.
  - constructor; inversion H; assumption.
  - inversion H.
  - inversion H.
  - constructor; inversion H; assumption.
  - constructor; inversion H; assumption.
  - inversion H.
  - inversion H.
  - inversion H.
Qed.

(* ============================================================ *)
(* Small-step and multi-step lemmas                              *)
(* ============================================================ *)

Lemma multi_value : forall (v u : tm), multi v u -> value v -> u = v.
Proof.
  intros v u H. induction H; intros Hv.
  - reflexivity.
  - exfalso. match goal with Hs' : ?x --> ?y, Hv' : value ?x |- _ => exact (value_step_false x y Hv' Hs') end.
Qed.

(* ============================================================ *)
(* Locally closed terms                                          *)
(* ============================================================ *)

Lemma value_lc : forall (v : tm), value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv; simpl; auto; try (split; assumption).
Qed.

Lemma lc_at_S : forall (t : tm) (k : nat), lc_at k t -> lc_at (S k) t.
Proof.
  induction t; intros k H; simpl in *.
  - lia.
  - exact I.
  - exact I.
  - apply IHt. exact H.
  - destruct H as [H1 H2]. split; [apply IHt1; exact H1 | apply IHt2; exact H2].
  - destruct H as [H1 H2]. split; [apply IHt1; exact H1 | apply IHt2; exact H2].
  - apply IHt. exact H.
  - apply IHt. exact H.
  - apply IHt. exact H.
  - apply IHt. exact H.
  - destruct H as [H0 [H1 H2]].
    split; [apply IHt1; exact H0 | split; [apply IHt2; exact H1 | apply IHt3; exact H2]].
  - apply IHt. exact H.
  - destruct H as [H0 [H1 H2]].
    split; [apply IHt1; exact H0 | split; [apply IHt2; exact H1 | apply IHt3; exact H2]].
Qed.

Lemma lc_at_mono : forall (k k' : nat) (t : tm),
  k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t Hle. induction Hle; intros H.
  - exact H.
  - apply lc_at_S. apply IHHle. exact H.
Qed.

Lemma open_rec_closed : forall (t : tm) (k j : nat) (u : tm),
  k <= j -> lc_at k t -> open_rec j u t = t.
Proof.
  induction t; intros k j u Hkj Hlc; simpl in *.
  - destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHt with (k := S k); [lia | exact Hlc].
  - destruct Hlc as [H1 H2]. f_equal; [apply IHt1 with (k:=k)(j:=j) | apply IHt2 with (k:=k)(j:=j)]; auto.
  - destruct Hlc as [H1 H2]. f_equal; [apply IHt1 with (k:=k)(j:=j) | apply IHt2 with (k:=k)(j:=j)]; auto.
  - f_equal. apply IHt with (k:=k)(j:=j); assumption.
  - f_equal. apply IHt with (k:=k)(j:=j); assumption.
  - f_equal. apply IHt with (k:=k)(j:=j); assumption.
  - f_equal. apply IHt with (k:=k)(j:=j); assumption.
  - destruct Hlc as [H0 [H1 H2]]. f_equal.
    + apply IHt1 with (k:=k)(j:=j); assumption.
    + apply IHt2 with (k:=S k)(j:=S j); [lia | exact H1].
    + apply IHt3 with (k:=S k)(j:=S j); [lia | exact H2].
  - f_equal. apply IHt with (k:=k)(j:=j); assumption.
  - destruct Hlc as [H0 [H1 H2]]. f_equal.
    + apply IHt1 with (k:=k)(j:=j); assumption.
    + apply IHt2 with (k:=k)(j:=j); assumption.
    + apply IHt3 with (k:=k)(j:=j); assumption.
Qed.

Lemma open_lc : forall (t : tm) (k : nat) (x : atom),
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x0 H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + simpl in H. apply Nat.eqb_neq in E. lia.
  - exact I.
  - exact I.
  - apply (IHt (S k) x0). exact H.
  - destruct H as [H1 H2].
    split; [apply (IHt1 k x0); exact H1 | apply (IHt2 k x0); exact H2].
  - destruct H as [H1 H2].
    split; [apply (IHt1 k x0); exact H1 | apply (IHt2 k x0); exact H2].
  - apply (IHt k x0). exact H.
  - apply (IHt k x0). exact H.
  - apply (IHt k x0). exact H.
  - apply (IHt k x0). exact H.
  - destruct H as [H0 [H1 H2]].
    split; [apply (IHt1 k x0); exact H0
           | split; [apply (IHt2 (S k) x0); exact H1 | apply (IHt3 (S k) x0); exact H2]].
  - apply (IHt k x0). exact H.
  - destruct H as [H0 [H1 H2]].
    split; [apply (IHt1 k x0); exact H0
           | split; [apply (IHt2 k x0); exact H1 | apply (IHt3 k x0); exact H2]].
Qed.

(* ============================================================ *)
(* Functional substitution                                       *)
(* ============================================================ *)

Fixpoint subst_fn (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => sigma y
  | tm_unit kappa => tm_unit kappa
  | tm_abs T body kappa => tm_abs T (subst_fn sigma body) kappa
  | tm_app t1 t2 r => tm_app (subst_fn sigma t1) (subst_fn sigma t2) r
  | tm_pair t1 t2 kappa => tm_pair (subst_fn sigma t1) (subst_fn sigma t2) kappa
  | tm_fst t1 r => tm_fst (subst_fn sigma t1) r
  | tm_snd t1 r => tm_snd (subst_fn sigma t1) r
  | tm_inl t1 kappa => tm_inl (subst_fn sigma t1) kappa
  | tm_inr t1 kappa => tm_inr (subst_fn sigma t1) kappa
  | tm_case t0 body1 body2 r =>
      tm_case (subst_fn sigma t0) (subst_fn sigma body1) (subst_fn sigma body2) r
  | tm_protect l t1 => tm_protect l (subst_fn sigma t1)
  | tm_if c yes no r =>
      tm_if (subst_fn sigma c) (subst_fn sigma yes) (subst_fn sigma no) r
  end.

Lemma subst_fn_id : forall (t : tm), subst_fn (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try reflexivity; try (f_equal; assumption).
Qed.

Lemma subst_fn_ext : forall (sigma1 sigma2 : atom -> tm) (t : tm),
  (forall y : atom, In y (fv t) -> sigma1 y = sigma2 y) ->
  subst_fn sigma1 t = subst_fn sigma2 t.
Proof.
  intros sigma1 sigma2 t H. induction t; simpl; try reflexivity;
    try (f_equal; apply H; simpl; auto).
  - apply H. simpl. auto.
  - f_equal. apply IHt. intros y Hy. apply H. simpl. exact Hy.
  - f_equal; [apply IHt1 | apply IHt2]; intros y Hy; apply H; simpl; apply in_or_app; auto.
  - f_equal; [apply IHt1 | apply IHt2]; intros y Hy; apply H; simpl; apply in_or_app; auto.
  - f_equal. apply IHt. intros y Hy. apply H. simpl. exact Hy.
  - f_equal. apply IHt. intros y Hy. apply H. simpl. exact Hy.
  - f_equal. apply IHt. intros y Hy. apply H. simpl. exact Hy.
  - f_equal. apply IHt. intros y Hy. apply H. simpl. exact Hy.
  - f_equal.
    + apply IHt1. intros y Hy. apply H. simpl. apply in_or_app; left; exact Hy.
    + apply IHt2. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; left; exact Hy.
    + apply IHt3. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; right; exact Hy.
  - f_equal. apply IHt. intros y Hy. apply H. simpl. exact Hy.
  - f_equal.
    + apply IHt1. intros y Hy. apply H. simpl. apply in_or_app; left; exact Hy.
    + apply IHt2. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; left; exact Hy.
    + apply IHt3. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; right; exact Hy.
Qed.

Lemma subst_fn_lc : forall (sigma : atom -> tm) (t : tm) (k : nat),
  (forall y : atom, lc_at 0 (sigma y)) ->
  lc_at k t -> lc_at k (subst_fn sigma t).
Proof.
  intros sigma t. induction t; intros k Hc Hlc; simpl in *.
  - exact Hlc.
  - apply lc_at_mono with (k := 0); [lia | apply Hc].
  - exact I.
  - apply (IHt (S k) Hc). exact Hlc.
  - destruct Hlc as [H1 H2].
    split; [apply (IHt1 k Hc); exact H1 | apply (IHt2 k Hc); exact H2].
  - destruct Hlc as [H1 H2].
    split; [apply (IHt1 k Hc); exact H1 | apply (IHt2 k Hc); exact H2].
  - apply (IHt k Hc). exact Hlc.
  - apply (IHt k Hc). exact Hlc.
  - apply (IHt k Hc). exact Hlc.
  - apply (IHt k Hc). exact Hlc.
  - destruct Hlc as [H0 [H1 H2]].
    split; [apply (IHt1 k Hc); exact H0
           | split; [apply (IHt2 (S k) Hc); exact H1 | apply (IHt3 (S k) Hc); exact H2]].
  - apply (IHt k Hc). exact Hlc.
  - destruct Hlc as [H0 [H1 H2]].
    split; [apply (IHt1 k Hc); exact H0
           | split; [apply (IHt2 k Hc); exact H1 | apply (IHt3 k Hc); exact H2]].
Qed.

Lemma subst_fn_open_rec : forall (sigma : atom -> tm),
  (forall y : atom, lc_at 0 (sigma y)) ->
  forall (j : nat) (u t : tm),
    subst_fn sigma (open_rec j u t) =
    open_rec j (subst_fn sigma u) (subst_fn sigma t).
Proof.
  intros sigma Hc j u t. revert j u.
  induction t; intros j0 u0; simpl.
  - destruct (Nat.eqb j0 n); reflexivity.
  - rewrite (open_rec_closed (sigma a) 0 j0 (subst_fn sigma u0)).
    + reflexivity.
    + apply Nat.le_0_l.
    + apply Hc.
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal.
    + apply IHt1.
    + apply IHt2.
    + apply IHt3.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3].
Qed.

(* ============================================================ *)
(* Typing implies local closure                                 *)
(* ============================================================ *)

Lemma has_type_lc : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T H. induction H; simpl in *.
  - exact I.
  - exact I.
  - apply (open_lc body 0 (fresh_from L)). apply H2. apply fresh_from_notin.
  - split; assumption.
  - split; assumption.
  - exact IHhas_type.
  - exact IHhas_type.
  - exact IHhas_type.
  - exact IHhas_type.
  - split. { exact IHhas_type. }
    split.
    + apply (open_lc body1 0 (fresh_from L)). apply H2. apply fresh_from_notin.
    + apply (open_lc body2 0 (fresh_from L)). apply H4. apply fresh_from_notin.
  - exact IHhas_type.
  - exact IHhas_type.
  - split; [exact IHhas_type1 | split; [exact IHhas_type2 | exact IHhas_type3]].
Qed.

(* ============================================================ *)
(* Free variables of a program context and plug commutation      *)
(* ============================================================ *)

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
  | C_CaseScrutinee C' t1 t2 _ => fv_context C' ++ fv t1 ++ fv t2
  | C_CaseLeft t0 C' t2 _ => fv t0 ++ fv_context C' ++ fv t2
  | C_CaseRight t0 t1 C' _ => fv t0 ++ fv t1 ++ fv_context C'
  | C_Protect _ C' => fv_context C'
  | C_IfCondition C' t1 t2 _ => fv_context C' ++ fv t1 ++ fv t2
  | C_IfThen t0 C' t2 _ => fv t0 ++ fv_context C' ++ fv t2
  | C_IfElse t0 t1 C' _ => fv t0 ++ fv t1 ++ fv_context C'
  end.

Lemma subst_fn_fix_on : forall (sigma : atom -> tm) (t : tm),
  (forall y : atom, In y (fv t) -> sigma y = tm_fvar y) ->
  subst_fn sigma t = t.
Proof.
  intros sigma t H.
  transitivity (subst_fn (fun x => tm_fvar x) t).
  - apply subst_fn_ext. exact H.
  - apply subst_fn_id.
Qed.

Lemma subst_fn_plug : forall (C : program_context) (t : tm) (sigma : atom -> tm),
  (forall y : atom, In y (fv_context C) -> sigma y = tm_fvar y) ->
  subst_fn sigma (plug C t) = plug C (subst_fn sigma t).
Proof.
  induction C as [ | T c IHc s | c IHc t l | t c IHc l | c IHc t s | t c IHc s
                  | c IHc l | c IHc l | c IHc s | c IHc s
                  | c IHc t t0 l | t c IHc t0 l | t t0 c IHc l
                  | l c IHc | c IHc t t0 l | t c IHc t0 l | t t0 c IHc l ];
    simpl; intros tt sg H.
  - reflexivity.
  - f_equal. apply IHc. intros y Hy. apply H. simpl. exact Hy.
  - f_equal.
    + apply IHc. intros y Hy. apply H. simpl. apply in_or_app; left. exact Hy.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; right. exact Hy.
  - f_equal.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; left. exact Hy.
    + apply IHc. intros y Hy. apply H. simpl. apply in_or_app; right. exact Hy.
  - f_equal.
    + apply IHc. intros y Hy. apply H. simpl. apply in_or_app; left. exact Hy.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; right. exact Hy.
  - f_equal.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; left. exact Hy.
    + apply IHc. intros y Hy. apply H. simpl. apply in_or_app; right. exact Hy.
  - f_equal. apply IHc. intros y Hy. apply H. simpl. exact Hy.
  - f_equal. apply IHc. intros y Hy. apply H. simpl. exact Hy.
  - f_equal. apply IHc. intros y Hy. apply H. simpl. exact Hy.
  - f_equal. apply IHc. intros y Hy. apply H. simpl. exact Hy.
  - f_equal.
    + apply IHc. intros y Hy. apply H. simpl. apply in_or_app; left. exact Hy.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; left. exact Hy.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; right. exact Hy.
  - f_equal.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; left. exact Hy.
    + apply IHc. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; left. exact Hy.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; right. exact Hy.
  - f_equal.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; left. exact Hy.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; left. exact Hy.
    + apply IHc. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; right. exact Hy.
  - f_equal. apply IHc. intros y Hy. apply H. simpl. exact Hy.
  - f_equal.
    + apply IHc. intros y Hy. apply H. simpl. apply in_or_app; left. exact Hy.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; left. exact Hy.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; right. exact Hy.
  - f_equal.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; left. exact Hy.
    + apply IHc. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; left. exact Hy.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; right. exact Hy.
  - f_equal.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; left. exact Hy.
    + apply subst_fn_fix_on. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; left. exact Hy.
    + apply IHc. intros y Hy. apply H. simpl. apply in_or_app; right; apply in_or_app; right. exact Hy.
Qed.

(* ============================================================ *)
(* The logical relation                                          *)
(* ============================================================ *)

Definition vsec (v : tm) : security :=
  match v with
  | tm_unit s => s
  | tm_abs _ _ s => s
  | tm_pair _ _ s => s
  | tm_inl _ s => s
  | tm_inr _ s => s
  | _ => public
  end.

Fixpoint val_rel (l p : label) (T : ty) (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_Unit s =>
      flows_to (join s.(indirect_reader) p) l ->
      security_le (vsec v1) (protect_security s p) /\
      security_le (vsec v2) (protect_security s p) /\
      match v1, v2 with tm_unit _, tm_unit _ => True | _, _ => False end
  | Ty_Sum T1 T2 s =>
      flows_to (join s.(indirect_reader) p) l ->
      security_le (vsec v1) (protect_security s p) /\
      security_le (vsec v2) (protect_security s p) /\
      match v1, v2 with
      | tm_inl a1 _, tm_inl a2 _ => val_rel l Low T1 a1 a2
      | tm_inr b1 _, tm_inr b2 _ => val_rel l Low T2 b1 b2
      | _, _ => False
      end
  | Ty_Prod T1 T2 s =>
      flows_to (join s.(indirect_reader) p) l ->
      security_le (vsec v1) (protect_security s p) /\
      security_le (vsec v2) (protect_security s p) /\
      match v1, v2 with
      | tm_pair a1 b1 _, tm_pair a2 b2 _ =>
          val_rel l Low T1 a1 a2 /\ val_rel l Low T2 b1 b2
      | _, _ => False
      end
  | Ty_Arrow T1 T2 s =>
      flows_to (join s.(indirect_reader) p) l ->
      security_le (vsec v1) (protect_security s p) /\
      security_le (vsec v2) (protect_security s p) /\
      (value v1 -> value v2 ->
       forall (a1 a2 : tm) (r : label),
         value a1 -> value a2 -> val_rel l Low T1 a1 a2 ->
         flows_to (join s.(reader) p) r ->
         forall u1 u2 : tm,
           evaluates (tm_app v1 a1 r) u1 ->
           evaluates (tm_app v2 a2 r) u2 ->
           val_rel l (join s.(indirect_reader) p) T2 u1 u2)
  end.

Definition interp (l p : label) (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, evaluates t1 v1 -> evaluates t2 v2 -> val_rel l p T v1 v2.

(* ============================================================ *)
(* Security inequality helpers                                   *)
(* ============================================================ *)

Lemma security_le_public : forall k : security, security_le public k.
Proof. intros [r i]; destruct r, i; unfold security_le, public; simpl; auto. Qed.

Lemma sec_le_raise : forall (k s : security) (p q : label),
  flows_to p q -> security_le k (protect_security s p) ->
  security_le k (protect_security s q).
Proof.
  intros k s p q Hpq Hk.
  eapply security_le_trans; [exact Hk |].
  apply protect_security_mono; [exact Hpq | apply security_le_refl].
Qed.

Lemma sec_le_protect_r : forall (k s : security) (p L : label),
  security_le k (protect_security s p) ->
  security_le (protect_security k L) (protect_security s (join p L)).
Proof.
  intros k s p L Hk.
  eapply security_le_trans.
  - apply protect_security_mono; [apply flows_to_refl | exact Hk].
  - rewrite protect_security_twice. apply security_le_refl.
Qed.

Lemma sec_le_vsec_protect : forall (v : tm) (L : label) (s : security) (p : label),
  security_le (vsec v) (protect_security s p) ->
  security_le (vsec (protect_value v L)) (protect_security s (join p L)).
Proof.
  intros v L s p H. destruct v; simpl; try (apply security_le_public); apply sec_le_protect_r; exact H.
Qed.

Lemma protect_value_protect_value : forall (v : tm) (L1 L2 : label),
  protect_value (protect_value v L1) L2 = protect_value v (join L1 L2).
Proof.
  intros v L1 L2. destruct v; simpl; try reflexivity;
    rewrite protect_security_twice; reflexivity.
Qed.

(* ============================================================ *)
(* Basic properties of the relation                              *)
(* ============================================================ *)

Lemma val_rel_ty_protect : forall (l p : label) (T : ty) (v1 v2 : tm),
  val_rel l p T v1 v2 <-> val_rel l Low (ty_protect p T) v1 v2.
Proof.
  intros l p T v1 v2. destruct T as [s | T1 T2 s | T1 T2 s | T1 T2 s];
    simpl; repeat rewrite join_low_r; repeat rewrite protect_security_twice;
    repeat rewrite join_low_r; reflexivity.
Qed.

Lemma val_rel_interp : forall (l p : label) (T : ty) (v1 v2 : tm),
  value v1 -> value v2 -> val_rel l p T v1 v2 -> interp l p T v1 v2.
Proof.
  intros l p T v1 v2 Hv1 Hv2 Hvr u1 u2 [Hm1 Hval1] [Hm2 Hval2].
  assert (u1 = v1) as E1 by (eapply multi_value; eauto).
  assert (u2 = v2) as E2 by (eapply multi_value; eauto).
  subst. exact Hvr.
Qed.

Lemma val_rel_mono : forall (T : ty) (l p q : label) (v1 v2 : tm),
  flows_to p q -> val_rel l p T v1 v2 -> val_rel l q T v1 v2.
Proof.
  intros T. induction T as [s | T1 IHT1 T2 IHT2 s | T1 IHT1 T2 IHT2 s | T1 IHT1 T2 IHT2 s];
    intros l p q v1 v2 Hpq Hvr Hobs; simpl in *.
  - assert (Hp : flows_to (join (indirect_reader s) p) l)
      by (eapply flows_to_trans;
          [apply join_mono; [apply flows_to_refl | exact Hpq] | exact Hobs]).
    destruct (Hvr Hp) as [Hs1 [Hs2 Hst]].
    split; [| split; [| exact Hst]].
    + eapply sec_le_raise; [exact Hpq | exact Hs1].
    + eapply sec_le_raise; [exact Hpq | exact Hs2].
  - assert (Hp : flows_to (join (indirect_reader s) p) l)
      by (eapply flows_to_trans;
          [apply join_mono; [apply flows_to_refl | exact Hpq] | exact Hobs]).
    destruct (Hvr Hp) as [Hs1 [Hs2 Hst]].
    split; [| split; [| exact Hst]].
    + eapply sec_le_raise; [exact Hpq | exact Hs1].
    + eapply sec_le_raise; [exact Hpq | exact Hs2].
  - assert (Hp : flows_to (join (indirect_reader s) p) l)
      by (eapply flows_to_trans;
          [apply join_mono; [apply flows_to_refl | exact Hpq] | exact Hobs]).
    destruct (Hvr Hp) as [Hs1 [Hs2 Hst]].
    split; [| split; [| exact Hst]].
    + eapply sec_le_raise; [exact Hpq | exact Hs1].
    + eapply sec_le_raise; [exact Hpq | exact Hs2].
  - assert (Hp : flows_to (join (indirect_reader s) p) l)
      by (eapply flows_to_trans;
          [apply join_mono; [apply flows_to_refl | exact Hpq] | exact Hobs]).
    destruct (Hvr Hp) as [Hs1 [Hs2 Hst]].
    split; [| split; [|]].
    + eapply sec_le_raise; [exact Hpq | exact Hs1].
    + eapply sec_le_raise; [exact Hpq | exact Hs2].
    + intros Hv1 Hv2 a1 a2 r Ha1 Ha2 Harg Hflow u1 u2 He1 He2.
      eapply IHT2.
      * apply join_mono; [apply flows_to_refl | exact Hpq].
      * apply (Hst Hv1 Hv2 a1 a2 r Ha1 Ha2 Harg).
        -- eapply flows_to_trans;
             [apply join_mono; [apply flows_to_refl | exact Hpq] | exact Hflow].
        -- exact He1.
        -- exact He2.
Qed.

Lemma val_rel_sym : forall (T : ty) (l p : label) (v1 v2 : tm),
  val_rel l p T v1 v2 -> val_rel l p T v2 v1.
Proof.
  intros T. induction T as [s | T1 IHT1 T2 IHT2 s | T1 IHT1 T2 IHT2 s | T1 IHT1 T2 IHT2 s];
    intros l p v1 v2 Hvr Hobs; simpl in *.
  - destruct (Hvr Hobs) as [Hs1 [Hs2 Hst]].
    split; [exact Hs2 | split; [exact Hs1 |]].
    destruct v1, v2; simpl in *; intuition.
  - destruct (Hvr Hobs) as [Hs1 [Hs2 Hst]].
    split; [exact Hs2 | split; [exact Hs1 |]].
    destruct v1, v2; simpl in *; try tauto;
      try (apply IHT1; assumption); try (apply IHT2; assumption).
  - destruct (Hvr Hobs) as [Hs1 [Hs2 Hst]].
    split; [exact Hs2 | split; [exact Hs1 |]].
    destruct v1, v2; simpl in *; try tauto.
    destruct Hst as [H1 H2]. split; [apply IHT1; exact H1 | apply IHT2; exact H2].
  - destruct (Hvr Hobs) as [Hs1 [Hs2 Hst]].
    split; [exact Hs2 | split; [exact Hs1 |]].
    intros Hv2 Hv1 a1 a2 r Ha1 Ha2 Harg Hflow u1 u2 He1 He2.
    apply IHT2.
    apply (Hst Hv1 Hv2 a2 a1 r Ha2 Ha1 (IHT1 l Low a1 a2 Harg) Hflow u2 u1 He2 He1).
Qed.

(* ============================================================ *)
(* Inversion lemmas for multi-step evaluation                    *)
(* ============================================================ *)

Lemma multi_stuck : forall (t u : tm),
  (forall t', ~ step t t') -> multi t u -> u = t.
Proof.
  intros t u Hst Hm. induction Hm as [| u1 u2 u3 Hstep Hmulti IH].
  - reflexivity.
  - exfalso. apply (Hst u2). exact Hstep.
Qed.

Lemma multi_not_value_step : forall (t u : tm),
  multi t u -> value u -> ~ value t -> exists t', step t t' /\ multi t' u.
Proof.
  intros t u Hm. induction Hm as [| u1 u2 u3 Hstep Hmulti IH]; intros Hv Hnv.
  - exfalso. apply Hnv. exact Hv.
  - exists u2. split; [exact Hstep | exact Hmulti].
Qed.

Lemma multi_protect_value : forall (L : label) (t w : tm),
  multi t w -> value w -> multi (tm_protect L t) (protect_value w L).
Proof.
  intros L t w Hm. induction Hm as [| u1 u2 u3 Hstep Hmulti IH]; intros Hw.
  - eapply multi_step; [apply ST_ProtectValue; exact Hw | apply multi_refl].
  - eapply multi_step; [apply ST_Protect; exact Hstep | apply IH; exact Hw].
Qed.

Lemma multi_protect_inv : forall (L : label) (t v : tm),
  value v -> multi (tm_protect L t) v ->
  exists w, multi t w /\ value w /\ v = protect_value w L.
Proof.
  intros L t v Hv Hm. remember (tm_protect L t) as s eqn:E.
  revert L t E. induction Hm as [| u1 u2 u3 Hstep Hmulti IH]; intros L0 t0 E.
  - rewrite E in Hv. inversion Hv.
  - rewrite E in Hstep. inversion Hstep; subst.
    + exists t0. split; [apply multi_refl | split; [assumption |]].
      eapply multi_value.
      * exact Hmulti.
      * eapply value_protect_value. assumption.
    + destruct (IH Hv L0 t' eq_refl) as [w [Hm1 [Hw Ev]]].
      exists w. split; [| split; [assumption | assumption]].
      eapply multi_step; eauto.
Qed.

Lemma multi_app_abs_shape : forall (f a : tm) (r : label) (v : tm),
  value f -> value a -> value v -> multi (tm_app f a r) v ->
  exists (T : ty) (body : tm) (k : security), f = tm_abs T body k.
Proof.
  intros f a r v Hvf Hva Hv Hm.
  assert (Hnv : ~ value (tm_app f a r)) by (intro H; inversion H).
  destruct (multi_not_value_step _ _ Hm Hv Hnv) as [u [Hs Hu]].
  inversion Hs; subst.
  - exists T, body, kappa. reflexivity.
  - exfalso. match goal with Hs' : ?x --> ?y, Hv' : value ?x |- _ => exact (value_step_false x y Hv' Hs') end.
  - exfalso. match goal with Hs' : ?x --> ?y, Hv' : value ?x |- _ => exact (value_step_false x y Hv' Hs') end.
Qed.

Lemma multi_app_abs_decomp : forall (T : ty) (body a : tm) (k : security)
    (r : label) (v : tm),
  value (tm_abs T body k) -> value a -> value v ->
  multi (tm_app (tm_abs T body k) a r) v ->
  flows_to k.(reader) r /\ multi (tm_protect k.(indirect_reader) (open body a)) v.
Proof.
  intros T body a k r v Hvf Hva Hv Hm.
  assert (Hnv : ~ value (tm_app (tm_abs T body k) a r)) by (intro H; inversion H).
  destruct (multi_not_value_step _ _ Hm Hv Hnv) as [u [Hs Hu]].
  inversion Hs; subst.
  - split; [assumption | exact Hu].
  - exfalso. match goal with Hs' : ?x --> ?y, Hv' : value ?x |- _ => exact (value_step_false x y Hv' Hs') end.
  - exfalso. match goal with Hs' : ?x --> ?y, Hv' : value ?x |- _ => exact (value_step_false x y Hv' Hs') end.
Qed.

Lemma multi_app_inv : forall (t1 t2 : tm) (r : label) (v : tm),
  value v -> multi (tm_app t1 t2 r) v ->
  exists f w, multi t1 f /\ value f /\ multi t2 w /\ value w /\
              multi (tm_app f w r) v.
Proof.
  intros t1 t2 r v Hv Hm. remember (tm_app t1 t2 r) as s eqn:E.
  revert t1 t2 r E. induction Hm as [| u1 u2 u3 Hstep Hmulti IH]; intros t1' t2' r0 E.
  - rewrite E in Hv. inversion Hv.
  - rewrite E in Hstep. inversion Hstep; subst.
    + exists (tm_abs T body kappa), t2'.
      split; [apply multi_refl | split; [assumption | split; [apply multi_refl | split; [assumption |]]]].
      eapply multi_step; eauto.
    + destruct (IH Hv t1'0 t2' r0 eq_refl) as [f [w [Hm1 [Hvf [Hm2 [Hvw Happ]]]]]].
      exists f, w. split; [| split; [| split; [| split]]].
      * eapply multi_step; eauto.
      * exact Hvf.
      * exact Hm2.
      * exact Hvw.
      * exact Happ.
    + destruct (IH Hv t1' t2'0 r0 eq_refl) as [f [w [Hm1 [Hvf [Hm2 [Hvw Happ]]]]]].
      exists f, w. split; [| split; [| split; [| split]]].
      * exact Hm1.
      * exact Hvf.
      * eapply multi_step; eauto.
      * exact Hvw.
      * exact Happ.
Qed.

Lemma multi_fst_inv : forall (t : tm) (r : label) (v : tm),
  value v -> multi (tm_fst t r) v ->
  exists v1 v2 kappa, multi t (tm_pair v1 v2 kappa) /\ value v1 /\ value v2 /\
                      multi (tm_protect kappa.(indirect_reader) v1) v.
Proof.
  intros t r v Hv Hm. remember (tm_fst t r) as s eqn:E.
  revert t r E. induction Hm as [| u1 u2 u3 Hstep Hmulti IH]; intros t0 r0 E.
  - rewrite E in Hv. inversion Hv.
  - rewrite E in Hstep. inversion Hstep; subst.
    + exists v1, v2, kappa.
      split; [apply multi_refl | split; [assumption | split; [assumption | exact Hmulti]]].
    + destruct (IH Hv t' r0 eq_refl) as [v1 [v2 [k [Hm1 [Hvv1 [Hvv2 Hmf]]]]]].
      exists v1, v2, k. split; [| split; [| split]]; auto.
      eapply multi_step; eauto.
Qed.

Lemma multi_snd_inv : forall (t : tm) (r : label) (v : tm),
  value v -> multi (tm_snd t r) v ->
  exists v1 v2 kappa, multi t (tm_pair v1 v2 kappa) /\ value v1 /\ value v2 /\
                      multi (tm_protect kappa.(indirect_reader) v2) v.
Proof.
  intros t r v Hv Hm. remember (tm_snd t r) as s eqn:E.
  revert t r E. induction Hm as [| u1 u2 u3 Hstep Hmulti IH]; intros t0 r0 E.
  - rewrite E in Hv. inversion Hv.
  - rewrite E in Hstep. inversion Hstep; subst.
    + exists v1, v2, kappa.
      split; [apply multi_refl | split; [assumption | split; [assumption | exact Hmulti]]].
    + destruct (IH Hv t' r0 eq_refl) as [v1 [v2 [k [Hm1 [Hvv1 [Hvv2 Hmf]]]]]].
      exists v1, v2, k. split; [| split; [| split]]; auto.
      eapply multi_step; eauto.
Qed.

Lemma multi_pair_inv : forall (t1 t2 : tm) (k : security) (v : tm),
  value v -> multi (tm_pair t1 t2 k) v ->
  exists v1 v2, multi t1 v1 /\ value v1 /\ multi t2 v2 /\ value v2 /\
                v = tm_pair v1 v2 k.
Proof.
  intros t1 t2 k v Hv Hm. remember (tm_pair t1 t2 k) as s eqn:E.
  revert t1 t2 k E. induction Hm as [| u1 u2 u3 Hstep Hmulti IH]; intros t1' t2' k0 E.
  - rewrite E in Hv. inversion Hv; subst.
    exists t1', t2'. split; [apply multi_refl | split; [assumption | split; [apply multi_refl | split; [assumption | reflexivity]]]].
  - rewrite E in Hstep. inversion Hstep; subst.
    + destruct (IH Hv t1'0 t2' k0 eq_refl) as [v1 [v2 [Hm1 [Hvv1 [Hm2 [Hvv2 Ev]]]]]].
      exists v1, v2. split; [| split; [| split; [| split]]]; auto.
      eapply multi_step; eauto.
    + destruct (IH Hv t1' t2'0 k0 eq_refl) as [v1 [v2 [Hm1 [Hvv1 [Hm2 [Hvv2 Ev]]]]]].
      exists v1, v2. split; [| split; [| split; [| split]]]; auto.
      eapply multi_step; eauto.
Qed.

Lemma multi_inl_inv : forall (t : tm) (k : security) (v : tm),
  value v -> multi (tm_inl t k) v -> exists w, multi t w /\ value w /\ v = tm_inl w k.
Proof.
  intros t k v Hv Hm. remember (tm_inl t k) as s eqn:E.
  revert t k E. induction Hm as [| u1 u2 u3 Hstep Hmulti IH]; intros t0 k0 E.
  - rewrite E in Hv. inversion Hv; subst. exists t0.
    split; [apply multi_refl | split; [assumption | reflexivity]].
  - rewrite E in Hstep. inversion Hstep; subst.
    destruct (IH Hv t' k0 eq_refl) as [w [Hm1 [Hw Ev]]].
    exists w. split; [| split]; auto. eapply multi_step; eauto.
Qed.

Lemma multi_inr_inv : forall (t : tm) (k : security) (v : tm),
  value v -> multi (tm_inr t k) v -> exists w, multi t w /\ value w /\ v = tm_inr w k.
Proof.
  intros t k v Hv Hm. remember (tm_inr t k) as s eqn:E.
  revert t k E. induction Hm as [| u1 u2 u3 Hstep Hmulti IH]; intros t0 k0 E.
  - rewrite E in Hv. inversion Hv; subst. exists t0.
    split; [apply multi_refl | split; [assumption | reflexivity]].
  - rewrite E in Hstep. inversion Hstep; subst.
    destruct (IH Hv t' k0 eq_refl) as [w [Hm1 [Hw Ev]]].
    exists w. split; [| split]; auto. eapply multi_step; eauto.
Qed.

Lemma multi_case_inv : forall (t b1 b2 : tm) (r : label) (v : tm),
  value v -> multi (tm_case t b1 b2 r) v ->
  (exists w kappa, multi t (tm_inl w kappa) /\ value w /\ flows_to kappa.(reader) r /\
                   multi (tm_protect kappa.(indirect_reader) (open b1 w)) v) \/
  (exists w kappa, multi t (tm_inr w kappa) /\ value w /\ flows_to kappa.(reader) r /\
                   multi (tm_protect kappa.(indirect_reader) (open b2 w)) v).
Proof.
  intros t b1 b2 r v Hv Hm. remember (tm_case t b1 b2 r) as s eqn:E.
  revert t b1 b2 r E. induction Hm as [| u1 u2 u3 Hstep Hmulti IH]; intros t0 b10 b20 r0 E.
  - rewrite E in Hv. inversion Hv.
  - rewrite E in Hstep. inversion Hstep; subst.
    + (* ST_CaseLeft *) left. exists v, kappa.
      split; [apply multi_refl | split; [assumption | split; [assumption | exact Hmulti]]].
    + (* ST_CaseRight *) right. exists v, kappa.
      split; [apply multi_refl | split; [assumption | split; [assumption | exact Hmulti]]].
    + (* ST_Case *) destruct (IH Hv t' b10 b20 r0 eq_refl) as [L | R].
      * left. destruct L as [w [k [Hm1 [Hw [Hfl Hmf]]]]].
        exists w, k. split; [| split; [| split]]; auto. eapply multi_step; eauto.
      * right. destruct R as [w [k [Hm1 [Hw [Hfl Hmf]]]]].
        exists w, k. split; [| split; [| split]]; auto. eapply multi_step; eauto.
Qed.

Lemma multi_if_inv : forall (c y n : tm) (r : label) (v : tm),
  value v -> multi (tm_if c y n r) v ->
  (exists w kappa, multi c (tm_inl w kappa) /\ value w /\ flows_to kappa.(reader) r /\
                   multi (tm_protect kappa.(indirect_reader) y) v) \/
  (exists w kappa, multi c (tm_inr w kappa) /\ value w /\ flows_to kappa.(reader) r /\
                   multi (tm_protect kappa.(indirect_reader) n) v).
Proof.
  intros c y n r v Hv Hm. remember (tm_if c y n r) as s eqn:E.
  revert c y n r E. induction Hm as [| u1 u2 u3 Hstep Hmulti IH]; intros c0 y0 n0 r0 E.
  - rewrite E in Hv. inversion Hv.
  - rewrite E in Hstep. inversion Hstep; subst.
    + (* ST_If *) destruct (IH Hv c' y0 n0 r0 eq_refl) as [L | R].
      * left. destruct L as [w [k [Hm1 [Hw [Hfl Hmf]]]]].
        exists w, k. split; [| split; [| split]]; auto. eapply multi_step; eauto.
      * right. destruct R as [w [k [Hm1 [Hw [Hfl Hmf]]]]].
        exists w, k. split; [| split; [| split]]; auto. eapply multi_step; eauto.
    + (* ST_IfTrue *) left. exists v, k.
      split; [apply multi_refl | split; [assumption | split; [assumption | exact Hmulti]]].
    + (* ST_IfFalse *) right. exists v, k.
      split; [apply multi_refl | split; [assumption | split; [assumption | exact Hmulti]]].
Qed.

Lemma protect_value_abs : forall (v : tm) (L : label) (T : ty) (body : tm) (k : security),
  protect_value v L = tm_abs T body k ->
  exists (T' : ty) (body' : tm) (k' : security),
    v = tm_abs T' body' k' /\ T = T' /\ body = body' /\ k = protect_security k' L.
Proof.
  intros v L T body k E.
  destruct v as [ i | x | sU | TA bodyA kA | a0 b0 r0 | a0 b0 sU | a0 r0 | a0 r0
                | a0 sU | a0 sU | a0 b0 c0 r0 | l0 a0 | a0 b0 c0 r0 ];
    simpl in E; try discriminate E.
  injection E as ET Eb Ek.
  exists T, body, kA.
  split; [| split; [| split]].
  - rewrite <- ET, <- Eb. reflexivity.
  - reflexivity.
  - reflexivity.
  - symmetry. exact Ek.
Qed.

Lemma val_rel_protect1 : forall (T : ty) (l p L : label) (v1 v2 : tm),
  val_rel l p T v1 v2 ->
  val_rel l (join p L) T (protect_value v1 L) v2.
Proof.
  intros T. induction T as [s | T1 IHT1 T2 IHT2 s | T1 IHT1 T2 IHT2 s | T1 IHT1 T2 IHT2 s];
    intros l p L v1 v2 Hvr Hobs; simpl in *.
  - assert (Hp : flows_to (join (indirect_reader s) p) l)
      by (eapply flows_to_trans;
          [apply join_mono; [apply flows_to_refl | apply flows_to_join_r] | exact Hobs]).
    destruct (Hvr Hp) as [Hs1 [Hs2 Hst]].
    split; [| split; [|]].
    + apply sec_le_vsec_protect. exact Hs1.
    + eapply sec_le_raise; [apply flows_to_join_r | exact Hs2].
    + destruct v1, v2; simpl in *; intuition.
  - assert (Hp : flows_to (join (indirect_reader s) p) l)
      by (eapply flows_to_trans;
          [apply join_mono; [apply flows_to_refl | apply flows_to_join_r] | exact Hobs]).
    destruct (Hvr Hp) as [Hs1 [Hs2 Hst]].
    split; [| split; [|]].
    + apply sec_le_vsec_protect. exact Hs1.
    + eapply sec_le_raise; [apply flows_to_join_r | exact Hs2].
    + destruct v1, v2; simpl in *; try tauto; try assumption.
  - assert (Hp : flows_to (join (indirect_reader s) p) l)
      by (eapply flows_to_trans;
          [apply join_mono; [apply flows_to_refl | apply flows_to_join_r] | exact Hobs]).
    destruct (Hvr Hp) as [Hs1 [Hs2 Hst]].
    split; [| split; [|]].
    + apply sec_le_vsec_protect. exact Hs1.
    + eapply sec_le_raise; [apply flows_to_join_r | exact Hs2].
    + destruct v1, v2; simpl in *; try tauto; try assumption.
  - assert (Hp : flows_to (join (indirect_reader s) p) l)
      by (eapply flows_to_trans;
          [apply join_mono; [apply flows_to_refl | apply flows_to_join_r] | exact Hobs]).
    destruct (Hvr Hp) as [Hs1 [Hs2 Hst]].
    split; [| split; [|]].
    + apply sec_le_vsec_protect. exact Hs1.
    + eapply sec_le_raise; [apply flows_to_join_r | exact Hs2].
    + intros Hv1' Hv2 a1 a2 r0 Ha1 Ha2 Harg Hflow u1 u2 He1 He2.
      assert (Hv1 : value v1) by (apply value_protect_value_inv in Hv1'; exact Hv1').
      destruct He1 as [Hm1 Hu1].
      destruct (multi_app_abs_shape (protect_value v1 L) a1 r0 u1 Hv1' Ha1 Hu1 Hm1)
        as [T0 [body0 [k0 Ev]]].
      destruct (protect_value_abs v1 L T0 body0 k0 Ev)
        as [TA [bodyA [kA [Ev1 [ET [Eb Ek]]]]]].
      subst T0. subst body0. subst k0. subst v1.
      simpl in Hv1'.
      destruct (multi_app_abs_decomp TA bodyA a1 (protect_security kA L) r0 u1
                  Hv1' Ha1 Hu1 Hm1) as [Hflow1 Hmprot].
      destruct (multi_protect_inv (protect_security kA L).(indirect_reader)
                  (open bodyA a1) u1 Hu1 Hmprot) as [w1 [Hmb1 [Hw1 Eu1]]].
      assert (Hflow0 : flows_to kA.(reader) r0).
      { eapply flows_to_trans; [| exact Hflow1]. apply flows_to_join_r. }
      assert (He1' : evaluates (tm_app (tm_abs TA bodyA kA) a1 r0)
                              (protect_value w1 kA.(indirect_reader))).
      { split.
        - eapply multi_step.
          + apply ST_AppAbs; [exact Hv1 | exact Ha1 | exact Hflow0].
          + apply multi_protect_value; assumption.
        - apply value_protect_value; exact Hw1. }
      assert (Hres : val_rel l (join (indirect_reader s) p) T2
                       (protect_value w1 kA.(indirect_reader)) u2).
      { apply (Hst Hv1 Hv2 a1 a2 r0 Ha1 Ha2 Harg).
        - eapply flows_to_trans;
            [apply join_mono; [apply flows_to_refl | apply flows_to_join_r] | exact Hflow].
        - exact He1'.
        - exact He2. }
      simpl in Eu1.
      rewrite Eu1.
      pose proof (IHT2 l (join (indirect_reader s) p) L
                    (protect_value w1 kA.(indirect_reader)) u2 Hres) as Hres2.
      rewrite protect_value_protect_value in Hres2.
      rewrite join_assoc in Hres2.
      exact Hres2.
Qed.

Lemma val_rel_protect2 : forall (T : ty) (l p L1 L2 : label) (v1 v2 : tm),
  val_rel l p T v1 v2 ->
  val_rel l (join (join p L1) L2) T (protect_value v1 L1) (protect_value v2 L2).
Proof.
  intros T l p L1 L2 v1 v2 Hvr.
  pose proof (val_rel_protect1 T l p L1 v1 v2 Hvr) as H1.
  pose proof (val_rel_sym T l (join p L1) (protect_value v1 L1) v2 H1) as H2.
  pose proof (val_rel_protect1 T l (join p L1) L2 v2 (protect_value v1 L1) H2) as H3.
  apply (val_rel_sym T l (join (join p L1) L2)
           (protect_value v2 L2) (protect_value v1 L1)).
  exact H3.
Qed.

Lemma subtype_val_rel : forall (T U : ty), subtype T U ->
  forall (l p q : label) (v1 v2 : tm),
    flows_to p q -> val_rel l p T v1 v2 -> val_rel l q U v1 v2.
Proof.
  intros T U Hsub. induction Hsub; intros l p q v1 v2 Hpq Hvr.
  - (* S_Unit *)
    intro Hobs.
    assert (Hle' : security_le (protect_security kappa1 p) (protect_security kappa2 q))
      by (apply protect_security_mono; assumption).
    destruct H1 as [_ Hir].
    assert (Hobs1 : flows_to (join (indirect_reader kappa1) p) l).
    { eapply flows_to_trans.
      - apply join_mono; [exact Hir | exact Hpq].
      - exact Hobs. }
    destruct (Hvr Hobs1) as [Hs1 [Hs2 Hst]].
    split; [| split; [| exact Hst]].
    + eapply security_le_trans; [exact Hs1 | exact Hle'].
    + eapply security_le_trans; [exact Hs2 | exact Hle'].
  - (* S_Sum *)
    intro Hobs.
    assert (Hle' : security_le (protect_security kappa1 p) (protect_security kappa2 q))
      by (apply protect_security_mono; assumption).
    destruct H1 as [_ Hir].
    assert (Hobs1 : flows_to (join (indirect_reader kappa1) p) l).
    { eapply flows_to_trans.
      - apply join_mono; [exact Hir | exact Hpq].
      - exact Hobs. }
    destruct (Hvr Hobs1) as [Hs1 [Hs2 Hst]].
    split; [| split; [|]].
    + eapply security_le_trans; [exact Hs1 | exact Hle'].
    + eapply security_le_trans; [exact Hs2 | exact Hle'].
    + destruct v1, v2; simpl in *; try tauto.
      * apply (IHHsub1 l Low Low v1 v2 (flows_to_refl Low) Hst).
      * apply (IHHsub2 l Low Low v1 v2 (flows_to_refl Low) Hst).
  - (* S_Prod *)
    intro Hobs.
    assert (Hle' : security_le (protect_security kappa1 p) (protect_security kappa2 q))
      by (apply protect_security_mono; assumption).
    destruct H1 as [_ Hir].
    assert (Hobs1 : flows_to (join (indirect_reader kappa1) p) l).
    { eapply flows_to_trans.
      - apply join_mono; [exact Hir | exact Hpq].
      - exact Hobs. }
    destruct (Hvr Hobs1) as [Hs1 [Hs2 Hst]].
    split; [| split; [|]].
    + eapply security_le_trans; [exact Hs1 | exact Hle'].
    + eapply security_le_trans; [exact Hs2 | exact Hle'].
    + destruct v1, v2; simpl in *; try tauto.
      destruct Hst as [Hst1 Hst2]. split.
      * apply (IHHsub1 l Low Low); [apply flows_to_refl | exact Hst1].
      * apply (IHHsub2 l Low Low); [apply flows_to_refl | exact Hst2].
  - (* S_Arrow *)
    intro Hobs.
    assert (Hle' : security_le (protect_security kappa1 p) (protect_security kappa2 q))
      by (apply protect_security_mono; assumption).
    destruct H1 as [Hr Hi].
    assert (Hobs1 : flows_to (join (indirect_reader kappa1) p) l).
    { eapply flows_to_trans.
      - apply join_mono; [exact Hi | exact Hpq].
      - exact Hobs. }
    destruct (Hvr Hobs1) as [Hs1 [Hs2 Hst]].
    split; [| split; [|]].
    + eapply security_le_trans; [exact Hs1 | exact Hle'].
    + eapply security_le_trans; [exact Hs2 | exact Hle'].
    + intros Hv1 Hv2 a1 a2 r0 Ha1 Ha2 Harg Hflow u1 u2 He1 He2.
      assert (Hflow1 : flows_to (join (reader kappa1) p) r0).
      { eapply flows_to_trans; [| exact Hflow].
        apply join_mono; [exact Hr | exact Hpq]. }
      pose proof (Hst Hv1 Hv2 a1 a2 r0 Ha1 Ha2
                    (IHHsub1 l Low Low a1 a2 (flows_to_refl Low) Harg)
                    Hflow1 u1 u2 He1 He2) as Hst3.
      assert (Hlev : flows_to (join (indirect_reader kappa1) p)
                             (join (indirect_reader kappa2) q)).
      { apply join_mono; [exact Hi | exact Hpq]. }
      exact (IHHsub2 l (join (indirect_reader kappa1) p)
               (join (indirect_reader kappa2) q) u1 u2 Hlev Hst3).
  - (* S_Trans *)
    apply (IHHsub2 l q q v1 v2 (flows_to_refl q)).
    apply (IHHsub1 l p q v1 v2 Hpq Hvr).
Qed.

(* ============================================================ *)
(* Context lookup lemmas                                        *)
(* ============================================================ *)

Lemma lookup_update_eq : forall (Gamma : context) (x : atom) (T : ty),
  lookup_context x (update Gamma x T) = Some T.
Proof.
  intros Gamma x T. unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_update_neq : forall (Gamma : context) (x y : atom) (T : ty),
  x <> y -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T Hne. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply Hne. symmetry. exact E.
  - reflexivity.
Qed.

Lemma lookup_update_some : forall (Gamma : context) (x y : atom) (T U : ty),
  lookup_context y (update Gamma x T) = Some U ->
  (y = x /\ U = T) \/ (y <> x /\ lookup_context y Gamma = Some U).
Proof.
  intros Gamma x y T U H. unfold update in H. simpl in H.
  destruct (Nat.eqb y x) eqn:E.
  - left. apply Nat.eqb_eq in E. split; [exact E | inversion H; reflexivity].
  - right. apply Nat.eqb_neq in E. split; [exact E | exact H].
Qed.

(* ============================================================ *)
(* Related substitution environments                            *)
(* ============================================================ *)

Definition env_rel (l : label) (Gamma : context)
    (sigma1 sigma2 : atom -> tm) : Prop :=
  (forall y : atom, lc_at 0 (sigma1 y) /\ lc_at 0 (sigma2 y)) /\
  (forall (y : atom) (T : ty), lookup_context y Gamma = Some T ->
    interp l Low T (sigma1 y) (sigma2 y)).

Lemma env_rel_lc1 : forall (l : label) (Gamma : context)
    (sigma1 sigma2 : atom -> tm),
  env_rel l Gamma sigma1 sigma2 -> forall y, lc_at 0 (sigma1 y).
Proof. intros l Gamma sigma1 sigma2 [Hlc _] y. apply Hlc. Qed.

Lemma env_rel_lc2 : forall (l : label) (Gamma : context)
    (sigma1 sigma2 : atom -> tm),
  env_rel l Gamma sigma1 sigma2 -> forall y, lc_at 0 (sigma2 y).
Proof. intros l Gamma sigma1 sigma2 [Hlc _] y. apply Hlc. Qed.

Lemma env_rel_extend : forall (l : label) (Gamma : context) (x : atom) (T1 : ty)
    (sigma1 sigma2 : atom -> tm) (w1 w2 : tm),
  env_rel l Gamma sigma1 sigma2 ->
  val_rel l Low T1 w1 w2 ->
  value w1 -> value w2 ->
  env_rel l (update Gamma x T1)
    (fun y => if Nat.eqb y x then w1 else sigma1 y)
    (fun y => if Nat.eqb y x then w2 else sigma2 y).
Proof.
  intros l Gamma x T1 sigma1 sigma2 w1 w2 [Hlc Henv] Hvr Hw1 Hw2.
  split.
  - intros y. destruct (Nat.eqb y x) eqn:E.
    + split; apply value_lc; assumption.
    + apply Hlc.
  - intros y T Hlook. apply lookup_update_some in Hlook.
    destruct Hlook as [[E1 E2] | [Hne Hlook]].
    + subst y. subst T. rewrite Nat.eqb_refl. simpl.
      apply val_rel_interp; assumption.
    + destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E. exfalso. apply Hne. exact E.
      * apply Henv. exact Hlook.
Qed.

Lemma interp_protect : forall (l p L : label) (T : ty) (t1 t2 : tm),
  interp l p T t1 t2 ->
  interp l (join p L) T (tm_protect L t1) (tm_protect L t2).
Proof.
  intros l p L T t1 t2 Hi v1 v2 He1 He2.
  destruct He1 as [Hm1 Hv1]. destruct He2 as [Hm2 Hv2].
  destruct (multi_protect_inv L t1 v1 Hv1 Hm1) as [w1 [Hmw1 [Hvalw1 Ev1]]].
  destruct (multi_protect_inv L t2 v2 Hv2 Hm2) as [w2 [Hmw2 [Hvalw2 Ev2]]].
  pose proof (Hi w1 w2 (conj Hmw1 Hvalw1) (conj Hmw2 Hvalw2)) as Hvr.
  pose proof (val_rel_protect2 T l p L L w1 w2 Hvr) as Hp2.
  rewrite join_idem in Hp2.
  rewrite Ev1, Ev2. exact Hp2.
Qed.

(* ============================================================ *)
(* Additional helpers for the fundamental theorem                *)
(* ============================================================ *)

Lemma join_self : forall a : label, join a a = a.
Proof. destruct a; reflexivity. Qed.

Lemma interp_ty_protect : forall (l p : label) (T : ty) (t1 t2 : tm),
  interp l Low (ty_protect p T) t1 t2 <-> interp l p T t1 t2.
Proof.
  intros l p T t1 t2. unfold interp. split.
  - intros H v1 v2 He1 He2. apply (val_rel_ty_protect l p T v1 v2).
    apply H; assumption.
  - intros H v1 v2 He1 He2. apply (val_rel_ty_protect l p T v1 v2).
    apply H; assumption.
Qed.

Lemma subst_open_extend : forall (sigma : atom -> tm) (x : atom) (body w : tm),
  (forall y : atom, lc_at 0 (sigma y)) ->
  ~ In x (fv body) ->
  lc_at 0 w ->
  subst_fn (fun y => if Nat.eqb y x then w else sigma y) (open body (tm_fvar x))
  = open (subst_fn sigma body) w.
Proof.
  intros sigma x body w Hc Hnotin Hw.
  assert (Hc' : forall y : atom, lc_at 0 ((fun y => if Nat.eqb y x then w else sigma y) y)).
  { intros y. destruct (Nat.eqb y x). apply Hw. apply Hc. }
  unfold open.
  rewrite (subst_fn_open_rec (fun y => if Nat.eqb y x then w else sigma y) Hc'
             0 (tm_fvar x) body).
  simpl. rewrite Nat.eqb_refl. simpl.
  assert (E : subst_fn (fun y => if Nat.eqb y x then w else sigma y) body
              = subst_fn sigma body).
  { apply subst_fn_ext. intros y Hy.
    destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. exfalso. apply Hnotin. exact Hy.
    - reflexivity. }
  rewrite E. reflexivity.
Qed.

Lemma flows_to_dec : forall a b : label, {flows_to a b} + {~ flows_to a b}.
Proof.
  intros a b. destruct a, b; simpl.
  - left; trivial.
  - left; trivial.
  - right; intro H; exact H.
  - left; trivial.
Qed.

Lemma val_rel_vacuous : forall (l p : label) (T : ty) (v1 v2 : tm),
  ~ flows_to p l -> val_rel l p T v1 v2.
Proof.
  intros l p T v1 v2 Hnp. destruct T as [s | T1 T2 s | T1 T2 s | T1 T2 s]; simpl.
  - intro Hobs. exfalso. apply Hnp.
    eapply flows_to_trans; [apply flows_to_join_l | exact Hobs].
  - intro Hobs. exfalso. apply Hnp.
    eapply flows_to_trans; [apply flows_to_join_l | exact Hobs].
  - intro Hobs. exfalso. apply Hnp.
    eapply flows_to_trans; [apply flows_to_join_l | exact Hobs].
  - intro Hobs. exfalso. apply Hnp.
    eapply flows_to_trans; [apply flows_to_join_l | exact Hobs].
Qed.

Lemma val_rel_vacuous_gen : forall (lv p : label) (T : ty) (v1 v2 : tm),
  ~ flows_to (join (security_of T).(indirect_reader) p) lv ->
  val_rel lv p T v1 v2.
Proof.
  intros lv p T v1 v2 H.
  destruct T as [s | T1 T2 s | T1 T2 s | T1 T2 s]; simpl;
    intro Hobs; exfalso; exact (H Hobs).
Qed.

Lemma rel_protected : forall (T : ty) (l p L1 L2 : label) (v1 v2 w1 w2 : tm),
  val_rel l p T w1 w2 ->
  v1 = protect_value w1 L1 ->
  v2 = protect_value w2 L2 ->
  val_rel l (join (join p L1) L2) T v1 v2.
Proof.
  intros T l p L1 L2 v1 v2 w1 w2 Hvr Ev1 Ev2.
  subst v1. subst v2. apply val_rel_protect2. exact Hvr.
Qed.

(* ============================================================ *)
(* The fundamental theorem                                       *)
(* ============================================================ *)

Lemma fundamental : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T ->
  forall (lv : label) (sigma1 sigma2 : atom -> tm),
    env_rel lv Gamma sigma1 sigma2 ->
    interp lv Low T (subst_fn sigma1 t) (subst_fn sigma2 t).
Proof.
  intros Gamma t T Hty. induction Hty; intros lv sigma1 sigma2 Henv.
  - (* T_Var *) simpl. apply (proj2 Henv). exact H.
  - (* T_Unit *) simpl. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    assert (E1 : v1 = tm_unit kappa) by (eapply multi_value; [exact Hm1 | constructor]).
    assert (E2 : v2 = tm_unit kappa) by (eapply multi_value; [exact Hm2 | constructor]).
    subst v1. subst v2. simpl. intro Hobs.
    rewrite protect_security_low.
    split; [| split; [| exact I]]; apply security_le_refl.
  - (* T_Abs *)
    pose (x := fresh_from (L ++ fv body)).
    assert (HxL : ~ In x L).
    { unfold x. intro Hin. apply (fresh_from_notin (L ++ fv body)).
      apply in_or_app. left. exact Hin. }
    assert (Hxfv : ~ In x (fv body)).
    { unfold x. intro Hin. apply (fresh_from_notin (L ++ fv body)).
      apply in_or_app. right. exact Hin. }
    assert (Hlcbody : lc_at 1 body).
    { apply (open_lc body 0 x). apply (has_type_lc _ _ _ (H1 x HxL)). }
    assert (Hlc1 : lc_at 1 (subst_fn sigma1 body)).
    { apply (subst_fn_lc sigma1 body 1 (env_rel_lc1 lv Gamma sigma1 sigma2 Henv) Hlcbody). }
    assert (Hlc2 : lc_at 1 (subst_fn sigma2 body)).
    { apply (subst_fn_lc sigma2 body 1 (env_rel_lc2 lv Gamma sigma1 sigma2 Henv) Hlcbody). }
    assert (Hva1 : value (tm_abs T1 (subst_fn sigma1 body) kappa)) by (constructor; exact Hlc1).
    assert (Hva2 : value (tm_abs T1 (subst_fn sigma2 body) kappa)) by (constructor; exact Hlc2).
    simpl. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    assert (E1 : v1 = tm_abs T1 (subst_fn sigma1 body) kappa)
      by (eapply multi_value; eauto).
    assert (E2 : v2 = tm_abs T1 (subst_fn sigma2 body) kappa)
      by (eapply multi_value; eauto).
    subst v1. subst v2. simpl. intro Hobs.
    split; [| split; [|]].
    + rewrite protect_security_low. apply security_le_refl.
    + rewrite protect_security_low. apply security_le_refl.
    + intros Hvf1 Hvf2 a1 a2 r0 Ha1 Ha2 Harg Hflow u1 u2 He1 He2.
      destruct He1 as [Hmapp1 Hu1]. destruct He2 as [Hmapp2 Hu2].
      destruct (multi_app_abs_decomp T1 (subst_fn sigma1 body) a1 kappa r0 u1
                  Hvf1 Ha1 Hu1 Hmapp1) as [Hfl1 Hprot1].
      destruct (multi_app_abs_decomp T1 (subst_fn sigma2 body) a2 kappa r0 u2
                  Hvf2 Ha2 Hu2 Hmapp2) as [Hfl2 Hprot2].
      destruct (multi_protect_inv kappa.(indirect_reader)
                  (open (subst_fn sigma1 body) a1) u1 Hu1 Hprot1)
        as [w1 [Hmw1 [Hvalw1 Ev1]]].
      destruct (multi_protect_inv kappa.(indirect_reader)
                  (open (subst_fn sigma2 body) a2) u2 Hu2 Hprot2)
        as [w2 [Hmw2 [Hvalw2 Ev2]]].
      assert (Henv' : env_rel lv (update Gamma x T1)
                       (fun y => if Nat.eqb y x then a1 else sigma1 y)
                       (fun y => if Nat.eqb y x then a2 else sigma2 y)).
      { apply env_rel_extend; assumption. }
      pose proof (H2 x HxL lv _ _ Henv') as Hbodyi.
      assert (Esub1 : subst_fn (fun y => if Nat.eqb y x then a1 else sigma1 y)
                         (open body (tm_fvar x)) = open (subst_fn sigma1 body) a1).
      { apply subst_open_extend.
        - apply (env_rel_lc1 lv Gamma sigma1 sigma2 Henv).
        - exact Hxfv.
        - apply value_lc. exact Ha1. }
      assert (Esub2 : subst_fn (fun y => if Nat.eqb y x then a2 else sigma2 y)
                         (open body (tm_fvar x)) = open (subst_fn sigma2 body) a2).
      { apply subst_open_extend.
        - apply (env_rel_lc2 lv Gamma sigma1 sigma2 Henv).
        - exact Hxfv.
        - apply value_lc. exact Ha2. }
      rewrite Esub1, Esub2 in Hbodyi.
      assert (Hvr : val_rel lv Low T2 w1 w2).
      { apply Hbodyi. split; [exact Hmw1 | exact Hvalw1].
        split; [exact Hmw2 | exact Hvalw2]. }
      pose proof (rel_protected T2 lv Low kappa.(indirect_reader)
                    kappa.(indirect_reader) u1 u2 w1 w2 Hvr Ev1 Ev2) as Hp2.
      rewrite join_low_l in Hp2. rewrite join_self in Hp2.
      rewrite join_low_r. exact Hp2.
  - (* T_App *)
    simpl. intros v1 v2 He1 He2.
    destruct He1 as [Hm1 Hv1]. destruct He2 as [Hm2 Hv2].
    destruct (multi_app_inv (subst_fn sigma1 t1) (subst_fn sigma1 t2) r v1 Hv1 Hm1)
      as [f1 [w1 [Hmf1 [Hvf1 [Hmw1 [Hvw1 Happ1]]]]]].
    destruct (multi_app_inv (subst_fn sigma2 t1) (subst_fn sigma2 t2) r v2 Hv2 Hm2)
      as [f2 [w2 [Hmf2 [Hvf2 [Hmw2 [Hvw2 Happ2]]]]]].
    assert (Hrel1 : val_rel lv Low (Ty_Arrow T1 T2 kappa) f1 f2).
    { apply (IHHty1 lv sigma1 sigma2 Henv).
      split; assumption. split; assumption. }
    assert (Hrel2 : val_rel lv Low T1 w1 w2).
    { apply (IHHty2 lv sigma1 sigma2 Henv).
      split; assumption. split; assumption. }
    apply (val_rel_ty_protect lv kappa.(indirect_reader) T2 v1 v2).
    destruct (flows_to_dec kappa.(indirect_reader) lv) as [Hobs | Hnv].
    + assert (Hobsk : flows_to (join kappa.(indirect_reader) Low) lv).
      { rewrite join_low_r. exact Hobs. }
      assert (Hflow' : flows_to (join kappa.(reader) Low) r).
      { rewrite join_low_r. exact H. }
      destruct (Hrel1 Hobsk) as [Hs1 [Hs2 Hst]].
      pose proof (Hst Hvf1 Hvf2 w1 w2 r Hvw1 Hvw2 Hrel2 Hflow'
                    v1 v2 (conj Happ1 Hv1) (conj Happ2 Hv2)) as Hres.
      rewrite join_low_r in Hres. exact Hres.
    + apply val_rel_vacuous. exact Hnv.
  - (* T_Pair *)
    simpl. intros v1 v2 He1 He2.
    destruct He1 as [Hm1 Hv1]. destruct He2 as [Hm2 Hv2].
    destruct (multi_pair_inv (subst_fn sigma1 t1) (subst_fn sigma1 t2) kappa v1 Hv1 Hm1)
      as [a1 [b1 [Hma1 [Hva1 [Hmb1 [Hvb1 Ev1]]]]]].
    destruct (multi_pair_inv (subst_fn sigma2 t1) (subst_fn sigma2 t2) kappa v2 Hv2 Hm2)
      as [a2 [b2 [Hma2 [Hva2 [Hmb2 [Hvb2 Ev2]]]]]].
    subst v1. subst v2. simpl. intro Hobs.
    split; [| split; [|]].
    + rewrite protect_security_low. apply security_le_refl.
    + rewrite protect_security_low. apply security_le_refl.
    + split.
      * apply (IHHty1 lv sigma1 sigma2 Henv); split; assumption.
      * apply (IHHty2 lv sigma1 sigma2 Henv); split; assumption.
  - (* T_Fst *)
    simpl. intros v1 v2 He1 He2.
    destruct He1 as [Hm1 Hv1]. destruct He2 as [Hm2 Hv2].
    destruct (multi_fst_inv (subst_fn sigma1 t) r v1 Hv1 Hm1)
      as [a1 [b1 [k1 [Hma1 [Hva1 [Hvb1 Hprot1]]]]]].
    destruct (multi_fst_inv (subst_fn sigma2 t) r v2 Hv2 Hm2)
      as [a2 [b2 [k2 [Hma2 [Hva2 [Hvb2 Hprot2]]]]]].
    assert (Hrel : val_rel lv Low (Ty_Prod T1 T2 kappa)
                     (tm_pair a1 b1 k1) (tm_pair a2 b2 k2)).
    { apply (IHHty lv sigma1 sigma2 Henv).
      split; [exact Hma1 | constructor; assumption].
      split; [exact Hma2 | constructor; assumption]. }
    destruct (multi_protect_inv k1.(indirect_reader) a1 v1 Hv1 Hprot1)
      as [w1 [Hmw1 [Hvalw1 Ev1]]].
    destruct (multi_protect_inv k2.(indirect_reader) a2 v2 Hv2 Hprot2)
      as [w2 [Hmw2 [Hvalw2 Ev2]]].
    assert (Ew1 : w1 = a1) by (eapply multi_value; eauto).
    assert (Ew2 : w2 = a2) by (eapply multi_value; eauto).
    subst w1. subst w2.
    apply (val_rel_ty_protect lv kappa.(indirect_reader) T1 v1 v2).
    destruct (flows_to_dec kappa.(indirect_reader) lv) as [Hobs | Hnv].
    + assert (Hobsk : flows_to (join kappa.(indirect_reader) Low) lv).
      { rewrite join_low_r. exact Hobs. }
      destruct (Hrel Hobsk) as [Hs1 [Hs2 Hst]]. simpl in Hst.
      destruct Hst as [Hc1 Hc2].
      destruct Hs1 as [_ Hir1]. destruct Hs2 as [_ Hir2].
      rewrite protect_security_low in Hir1. rewrite protect_security_low in Hir2.
      assert (Hle : flows_to (join k1.(indirect_reader) k2.(indirect_reader))
                            kappa.(indirect_reader)).
      { apply flows_to_join_iff. split; assumption. }
      pose proof (rel_protected T1 lv Low k1.(indirect_reader) k2.(indirect_reader)
                    v1 v2 a1 a2 Hc1 Ev1 Ev2) as Hp2.
      rewrite join_low_l in Hp2.
      exact (val_rel_mono T1 lv (join k1.(indirect_reader) k2.(indirect_reader))
               kappa.(indirect_reader) v1 v2 Hle Hp2).
    + apply val_rel_vacuous. exact Hnv.
  - (* T_Snd *)
    simpl. intros v1 v2 He1 He2.
    destruct He1 as [Hm1 Hv1]. destruct He2 as [Hm2 Hv2].
    destruct (multi_snd_inv (subst_fn sigma1 t) r v1 Hv1 Hm1)
      as [a1 [b1 [k1 [Hma1 [Hva1 [Hvb1 Hprot1]]]]]].
    destruct (multi_snd_inv (subst_fn sigma2 t) r v2 Hv2 Hm2)
      as [a2 [b2 [k2 [Hma2 [Hva2 [Hvb2 Hprot2]]]]]].
    assert (Hrel : val_rel lv Low (Ty_Prod T1 T2 kappa)
                     (tm_pair a1 b1 k1) (tm_pair a2 b2 k2)).
    { apply (IHHty lv sigma1 sigma2 Henv).
      split; [exact Hma1 | constructor; assumption].
      split; [exact Hma2 | constructor; assumption]. }
    destruct (multi_protect_inv k1.(indirect_reader) b1 v1 Hv1 Hprot1)
      as [w1 [Hmw1 [Hvalw1 Ev1]]].
    destruct (multi_protect_inv k2.(indirect_reader) b2 v2 Hv2 Hprot2)
      as [w2 [Hmw2 [Hvalw2 Ev2]]].
    assert (Ew1 : w1 = b1) by (eapply multi_value; eauto).
    assert (Ew2 : w2 = b2) by (eapply multi_value; eauto).
    subst w1. subst w2.
    apply (val_rel_ty_protect lv kappa.(indirect_reader) T2 v1 v2).
    destruct (flows_to_dec kappa.(indirect_reader) lv) as [Hobs | Hnv].
    + assert (Hobsk : flows_to (join kappa.(indirect_reader) Low) lv).
      { rewrite join_low_r. exact Hobs. }
      destruct (Hrel Hobsk) as [Hs1 [Hs2 Hst]]. simpl in Hst.
      destruct Hst as [Hc1 Hc2].
      destruct Hs1 as [_ Hir1]. destruct Hs2 as [_ Hir2].
      rewrite protect_security_low in Hir1. rewrite protect_security_low in Hir2.
      assert (Hle : flows_to (join k1.(indirect_reader) k2.(indirect_reader))
                            kappa.(indirect_reader)).
      { apply flows_to_join_iff. split; assumption. }
      pose proof (rel_protected T2 lv Low k1.(indirect_reader) k2.(indirect_reader)
                    v1 v2 b1 b2 Hc2 Ev1 Ev2) as Hp2.
      rewrite join_low_l in Hp2.
      exact (val_rel_mono T2 lv (join k1.(indirect_reader) k2.(indirect_reader))
               kappa.(indirect_reader) v1 v2 Hle Hp2).
    + apply val_rel_vacuous. exact Hnv.
  - (* T_Inl *)
    simpl. intros v1 v2 He1 He2.
    destruct He1 as [Hm1 Hv1]. destruct He2 as [Hm2 Hv2].
    destruct (multi_inl_inv (subst_fn sigma1 t) kappa v1 Hv1 Hm1)
      as [w1 [Hmw1 [Hvalw1 Ev1]]].
    destruct (multi_inl_inv (subst_fn sigma2 t) kappa v2 Hv2 Hm2)
      as [w2 [Hmw2 [Hvalw2 Ev2]]].
    subst v1. subst v2. simpl. intro Hobs.
    split; [| split; [|]].
    + rewrite protect_security_low. apply security_le_refl.
    + rewrite protect_security_low. apply security_le_refl.
    + apply (IHHty lv sigma1 sigma2 Henv); split; assumption.
  - (* T_Inr *)
    simpl. intros v1 v2 He1 He2.
    destruct He1 as [Hm1 Hv1]. destruct He2 as [Hm2 Hv2].
    destruct (multi_inr_inv (subst_fn sigma1 t) kappa v1 Hv1 Hm1)
      as [w1 [Hmw1 [Hvalw1 Ev1]]].
    destruct (multi_inr_inv (subst_fn sigma2 t) kappa v2 Hv2 Hm2)
      as [w2 [Hmw2 [Hvalw2 Ev2]]].
    subst v1. subst v2. simpl. intro Hobs.
    split; [| split; [|]].
    + rewrite protect_security_low. apply security_le_refl.
    + rewrite protect_security_low. apply security_le_refl.
    + apply (IHHty lv sigma1 sigma2 Henv); split; assumption.
  - (* T_Case *)
    pose (x := fresh_from (L ++ fv body1 ++ fv body2)).
    assert (HxL : ~ In x L).
    { unfold x. intro Hin. apply (fresh_from_notin (L ++ fv body1 ++ fv body2)).
      apply in_or_app. left. exact Hin. }
    assert (Hxfv1 : ~ In x (fv body1)).
    { unfold x. intro Hin. apply (fresh_from_notin (L ++ fv body1 ++ fv body2)).
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (Hxfv2 : ~ In x (fv body2)).
    { unfold x. intro Hin. apply (fresh_from_notin (L ++ fv body1 ++ fv body2)).
      apply in_or_app. right. apply in_or_app. right. exact Hin. }
    simpl. intros v1 v2 He1 He2.
    destruct He1 as [Hm1 Hv1]. destruct He2 as [Hm2 Hv2].
    apply (val_rel_ty_protect lv kappa.(indirect_reader) T v1 v2).
    destruct (flows_to_dec kappa.(indirect_reader) lv) as [Hobs | Hnv].
    + assert (Hobsk : flows_to (join kappa.(indirect_reader) Low) lv).
      { rewrite join_low_r. exact Hobs. }
      destruct (multi_case_inv (subst_fn sigma1 t) (subst_fn sigma1 body1)
                  (subst_fn sigma1 body2) r v1 Hv1 Hm1) as [L1 | R1];
      destruct (multi_case_inv (subst_fn sigma2 t) (subst_fn sigma2 body1)
                  (subst_fn sigma2 body2) r v2 Hv2 Hm2) as [L2 | R2].
      * (* inl / inl *) destruct L1 as [w1 [k1 [Hmc1 [Hvw1 [Hfl1 Hmprot1]]]]].
      destruct L2 as [w2 [k2 [Hmc2 [Hvw2 [Hfl2 Hmprot2]]]]].
      assert (Hsum : val_rel lv Low (Ty_Sum T1 T2 kappa)
                       (tm_inl w1 k1) (tm_inl w2 k2)).
      { apply (IHHty lv sigma1 sigma2 Henv).
        - split; [exact Hmc1 | constructor; assumption].
        - split; [exact Hmc2 | constructor; assumption]. }
      destruct (Hsum Hobsk) as [Hs1 [Hs2 Hst]]. simpl in Hst.
      destruct (multi_protect_inv k1.(indirect_reader) (open (subst_fn sigma1 body1) w1)
                  v1 Hv1 Hmprot1) as [u1' [Hmu1 [Hvalu1 Ev1]]].
      destruct (multi_protect_inv k2.(indirect_reader) (open (subst_fn sigma2 body1) w2)
                  v2 Hv2 Hmprot2) as [u2' [Hmu2 [Hvalu2 Ev2]]].
      assert (Henv' : env_rel lv (update Gamma x T1)
                       (fun y => if Nat.eqb y x then w1 else sigma1 y)
                       (fun y => if Nat.eqb y x then w2 else sigma2 y)).
      { apply env_rel_extend; assumption. }
      pose proof (H1 x HxL lv _ _ Henv') as Hbodyi.
      assert (Esub1 : subst_fn (fun y => if Nat.eqb y x then w1 else sigma1 y)
                         (open body1 (tm_fvar x)) = open (subst_fn sigma1 body1) w1).
      { apply subst_open_extend.
        - apply (env_rel_lc1 lv Gamma sigma1 sigma2 Henv).
        - exact Hxfv1.
        - apply value_lc. exact Hvw1. }
      assert (Esub2 : subst_fn (fun y => if Nat.eqb y x then w2 else sigma2 y)
                         (open body1 (tm_fvar x)) = open (subst_fn sigma2 body1) w2).
      { apply subst_open_extend.
        - apply (env_rel_lc2 lv Gamma sigma1 sigma2 Henv).
        - exact Hxfv1.
        - apply value_lc. exact Hvw2. }
      rewrite Esub1, Esub2 in Hbodyi.
      assert (Hvr : val_rel lv Low T u1' u2').
      { apply Hbodyi. split; [exact Hmu1 | exact Hvalu1].
        split; [exact Hmu2 | exact Hvalu2]. }
      destruct Hs1 as [_ Hir1]. destruct Hs2 as [_ Hir2].
      rewrite protect_security_low in Hir1. rewrite protect_security_low in Hir2.
      assert (Hle : flows_to (join k1.(indirect_reader) k2.(indirect_reader))
                            kappa.(indirect_reader)).
      { apply flows_to_join_iff. split; assumption. }
      pose proof (rel_protected T lv Low k1.(indirect_reader) k2.(indirect_reader)
                    v1 v2 u1' u2' Hvr Ev1 Ev2) as Hp2.
      rewrite join_low_l in Hp2.
      exact (val_rel_mono T lv (join k1.(indirect_reader) k2.(indirect_reader))
               kappa.(indirect_reader) v1 v2 Hle Hp2).
      * (* inl / inr *) destruct L1 as [w1 [k1 [Hmc1 [Hvw1 [Hfl1 Hmprot1]]]]].
      destruct R2 as [w2 [k2 [Hmc2 [Hvw2 [Hfl2 Hmprot2]]]]].
      exfalso.
      assert (Hsum : val_rel lv Low (Ty_Sum T1 T2 kappa)
                       (tm_inl w1 k1) (tm_inr w2 k2)).
      { apply (IHHty lv sigma1 sigma2 Henv).
        - split; [exact Hmc1 | constructor; assumption].
        - split; [exact Hmc2 | constructor; assumption]. }
      destruct (Hsum Hobsk) as [Hs1 [Hs2 Hst]]. simpl in Hst. exact Hst.
      * (* inr / inl *) destruct R1 as [w1 [k1 [Hmc1 [Hvw1 [Hfl1 Hmprot1]]]]].
      destruct L2 as [w2 [k2 [Hmc2 [Hvw2 [Hfl2 Hmprot2]]]]].
      exfalso.
      assert (Hsum : val_rel lv Low (Ty_Sum T1 T2 kappa)
                       (tm_inr w1 k1) (tm_inl w2 k2)).
      { apply (IHHty lv sigma1 sigma2 Henv).
        - split; [exact Hmc1 | constructor; assumption].
        - split; [exact Hmc2 | constructor; assumption]. }
      destruct (Hsum Hobsk) as [Hs1 [Hs2 Hst]]. simpl in Hst. exact Hst.
      * (* inr / inr *) destruct R1 as [w1 [k1 [Hmc1 [Hvw1 [Hfl1 Hmprot1]]]]].
      destruct R2 as [w2 [k2 [Hmc2 [Hvw2 [Hfl2 Hmprot2]]]]].
      assert (Hsum : val_rel lv Low (Ty_Sum T1 T2 kappa)
                       (tm_inr w1 k1) (tm_inr w2 k2)).
      { apply (IHHty lv sigma1 sigma2 Henv).
        - split; [exact Hmc1 | constructor; assumption].
        - split; [exact Hmc2 | constructor; assumption]. }
      destruct (Hsum Hobsk) as [Hs1 [Hs2 Hst]]. simpl in Hst.
      destruct (multi_protect_inv k1.(indirect_reader) (open (subst_fn sigma1 body2) w1)
                  v1 Hv1 Hmprot1) as [u1' [Hmu1 [Hvalu1 Ev1]]].
      destruct (multi_protect_inv k2.(indirect_reader) (open (subst_fn sigma2 body2) w2)
                  v2 Hv2 Hmprot2) as [u2' [Hmu2 [Hvalu2 Ev2]]].
      assert (Henv' : env_rel lv (update Gamma x T2)
                       (fun y => if Nat.eqb y x then w1 else sigma1 y)
                       (fun y => if Nat.eqb y x then w2 else sigma2 y)).
      { apply env_rel_extend; assumption. }
      pose proof (H3 x HxL lv _ _ Henv') as Hbodyi.
      assert (Esub1 : subst_fn (fun y => if Nat.eqb y x then w1 else sigma1 y)
                         (open body2 (tm_fvar x)) = open (subst_fn sigma1 body2) w1).
      { apply subst_open_extend.
        - apply (env_rel_lc1 lv Gamma sigma1 sigma2 Henv).
        - exact Hxfv2.
        - apply value_lc. exact Hvw1. }
      assert (Esub2 : subst_fn (fun y => if Nat.eqb y x then w2 else sigma2 y)
                         (open body2 (tm_fvar x)) = open (subst_fn sigma2 body2) w2).
      { apply subst_open_extend.
        - apply (env_rel_lc2 lv Gamma sigma1 sigma2 Henv).
        - exact Hxfv2.
        - apply value_lc. exact Hvw2. }
      rewrite Esub1, Esub2 in Hbodyi.
      assert (Hvr : val_rel lv Low T u1' u2').
      { apply Hbodyi. split; [exact Hmu1 | exact Hvalu1].
        split; [exact Hmu2 | exact Hvalu2]. }
      destruct Hs1 as [_ Hir1]. destruct Hs2 as [_ Hir2].
      rewrite protect_security_low in Hir1. rewrite protect_security_low in Hir2.
      assert (Hle : flows_to (join k1.(indirect_reader) k2.(indirect_reader))
                            kappa.(indirect_reader)).
      { apply flows_to_join_iff. split; assumption. }
      pose proof (rel_protected T lv Low k1.(indirect_reader) k2.(indirect_reader)
                    v1 v2 u1' u2' Hvr Ev1 Ev2) as Hp2.
      rewrite join_low_l in Hp2.
      exact (val_rel_mono T lv (join k1.(indirect_reader) k2.(indirect_reader))
               kappa.(indirect_reader) v1 v2 Hle Hp2).
    + apply val_rel_vacuous. exact Hnv.
  - (* T_Protect *)
    simpl. apply interp_ty_protect.
    assert (E : interp lv (join Low l) T (tm_protect l (subst_fn sigma1 t))
                                  (tm_protect l (subst_fn sigma2 t))).
    { apply interp_protect. apply (IHHty lv sigma1 sigma2 Henv). }
    rewrite join_low_l in E. exact E.
  - (* T_Sub *)
    simpl. intros v1 v2 He1 He2.
    apply (subtype_val_rel T U H lv Low Low v1 v2 (flows_to_refl Low)).
    apply (IHHty lv sigma1 sigma2 Henv); assumption.
  - (* T_If *)
    simpl. intros v1 v2 He1 He2.
    destruct He1 as [Hm1 Hv1]. destruct He2 as [Hm2 Hv2].
    apply (val_rel_ty_protect lv k.(indirect_reader) T v1 v2).
    destruct (flows_to_dec k.(indirect_reader) lv) as [Hobs | Hnv].
    + assert (Hobsk : flows_to (join k.(indirect_reader) Low) lv).
      { rewrite join_low_r. exact Hobs. }
      destruct (multi_if_inv (subst_fn sigma1 c) (subst_fn sigma1 yes) (subst_fn sigma1 no)
                  r v1 Hv1 Hm1) as [L1 | R1];
      destruct (multi_if_inv (subst_fn sigma2 c) (subst_fn sigma2 yes) (subst_fn sigma2 no)
                  r v2 Hv2 Hm2) as [L2 | R2].
      * destruct L1 as [w1 [k1 [Hmc1 [Hvw1 [Hfl1 Hmprot1]]]]].
      destruct L2 as [w2 [k2 [Hmc2 [Hvw2 [Hfl2 Hmprot2]]]]].
      assert (Hsum : val_rel lv Low (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                       (tm_inl w1 k1) (tm_inl w2 k2)).
      { apply (IHHty1 lv sigma1 sigma2 Henv).
        - split; [exact Hmc1 | constructor; assumption].
        - split; [exact Hmc2 | constructor; assumption]. }
      destruct (Hsum Hobsk) as [Hs1 [Hs2 Hst]]. simpl in Hst.
      destruct (multi_protect_inv k1.(indirect_reader) (subst_fn sigma1 yes)
                  v1 Hv1 Hmprot1) as [u1' [Hmu1 [Hvalu1 Ev1]]].
      destruct (multi_protect_inv k2.(indirect_reader) (subst_fn sigma2 yes)
                  v2 Hv2 Hmprot2) as [u2' [Hmu2 [Hvalu2 Ev2]]].
      assert (Hvr : val_rel lv Low T u1' u2').
      { apply (IHHty2 lv sigma1 sigma2 Henv).
        - split; [exact Hmu1 | exact Hvalu1].
        - split; [exact Hmu2 | exact Hvalu2]. }
      destruct Hs1 as [_ Hir1]. destruct Hs2 as [_ Hir2].
      rewrite protect_security_low in Hir1. rewrite protect_security_low in Hir2.
      assert (Hle : flows_to (join k1.(indirect_reader) k2.(indirect_reader))
                            k.(indirect_reader)).
      { apply flows_to_join_iff. split; assumption. }
      pose proof (rel_protected T lv Low k1.(indirect_reader) k2.(indirect_reader)
                    v1 v2 u1' u2' Hvr Ev1 Ev2) as Hp2.
      rewrite join_low_l in Hp2.
      exact (val_rel_mono T lv (join k1.(indirect_reader) k2.(indirect_reader))
               k.(indirect_reader) v1 v2 Hle Hp2).
      * destruct L1 as [w1 [k1 [Hmc1 [Hvw1 [Hfl1 Hmprot1]]]]].
      destruct R2 as [w2 [k2 [Hmc2 [Hvw2 [Hfl2 Hmprot2]]]]].
      exfalso.
      assert (Hsum : val_rel lv Low (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                       (tm_inl w1 k1) (tm_inr w2 k2)).
      { apply (IHHty1 lv sigma1 sigma2 Henv).
        - split; [exact Hmc1 | constructor; assumption].
        - split; [exact Hmc2 | constructor; assumption]. }
      destruct (Hsum Hobsk) as [Hs1 [Hs2 Hst]]. simpl in Hst. exact Hst.
      * destruct R1 as [w1 [k1 [Hmc1 [Hvw1 [Hfl1 Hmprot1]]]]].
      destruct L2 as [w2 [k2 [Hmc2 [Hvw2 [Hfl2 Hmprot2]]]]].
      exfalso.
      assert (Hsum : val_rel lv Low (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                       (tm_inr w1 k1) (tm_inl w2 k2)).
      { apply (IHHty1 lv sigma1 sigma2 Henv).
        - split; [exact Hmc1 | constructor; assumption].
        - split; [exact Hmc2 | constructor; assumption]. }
      destruct (Hsum Hobsk) as [Hs1 [Hs2 Hst]]. simpl in Hst. exact Hst.
      * destruct R1 as [w1 [k1 [Hmc1 [Hvw1 [Hfl1 Hmprot1]]]]].
      destruct R2 as [w2 [k2 [Hmc2 [Hvw2 [Hfl2 Hmprot2]]]]].
      assert (Hsum : val_rel lv Low (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                       (tm_inr w1 k1) (tm_inr w2 k2)).
      { apply (IHHty1 lv sigma1 sigma2 Henv).
        - split; [exact Hmc1 | constructor; assumption].
        - split; [exact Hmc2 | constructor; assumption]. }
      destruct (Hsum Hobsk) as [Hs1 [Hs2 Hst]]. simpl in Hst.
      destruct (multi_protect_inv k1.(indirect_reader) (subst_fn sigma1 no)
                  v1 Hv1 Hmprot1) as [u1' [Hmu1 [Hvalu1 Ev1]]].
      destruct (multi_protect_inv k2.(indirect_reader) (subst_fn sigma2 no)
                  v2 Hv2 Hmprot2) as [u2' [Hmu2 [Hvalu2 Ev2]]].
      assert (Hvr : val_rel lv Low T u1' u2').
      { apply (IHHty3 lv sigma1 sigma2 Henv).
        - split; [exact Hmu1 | exact Hvalu1].
        - split; [exact Hmu2 | exact Hvalu2]. }
      destruct Hs1 as [_ Hir1]. destruct Hs2 as [_ Hir2].
      rewrite protect_security_low in Hir1. rewrite protect_security_low in Hir2.
      assert (Hle : flows_to (join k1.(indirect_reader) k2.(indirect_reader))
                            k.(indirect_reader)).
      { apply flows_to_join_iff. split; assumption. }
      pose proof (rel_protected T lv Low k1.(indirect_reader) k2.(indirect_reader)
                    v1 v2 u1' u2' Hvr Ev1 Ev2) as Hp2.
      rewrite join_low_l in Hp2.
      exact (val_rel_mono T lv (join k1.(indirect_reader) k2.(indirect_reader))
               k.(indirect_reader) v1 v2 Hle Hp2).
    + apply val_rel_vacuous. exact Hnv.
Qed.

(* ============================================================ *)
(* Erasing values at public ground types                        *)
(* ============================================================ *)

Fixpoint all_sec_below (l : label) (T : ty) : Prop :=
  flows_to (security_of T).(indirect_reader) l /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      all_sec_below l T1 /\ all_sec_below l T2
  end.

Lemma transparent_all_below : forall (kappa : security) (T : ty) (l : label),
  transparent_at kappa T -> flows_to kappa.(indirect_reader) l ->
  all_sec_below l T.
Proof.
  intros kappa T. induction T as [s | T1 IHT1 T2 IHT2 s | T1 IHT1 T2 IHT2 s
                              | T1 IHT1 T2 IHT2 s];
    intros l Htr Hfl; simpl in *.
  - destruct Htr as [Hle _]. split; [| exact I].
    destruct Hle as [_ Hi]. eapply flows_to_trans; [exact Hi | exact Hfl].
  - destruct Htr as [Hle [Ht1 Ht2]]. split.
    + destruct Hle as [_ Hi]. eapply flows_to_trans; [exact Hi | exact Hfl].
    + split; [apply IHT1 | apply IHT2]; assumption.
  - destruct Htr as [Hle [Ht1 Ht2]]. split.
    + destruct Hle as [_ Hi]. eapply flows_to_trans; [exact Hi | exact Hfl].
    + split; [apply IHT1 | apply IHT2]; assumption.
  - destruct Htr as [Hle [Ht1 Ht2]]. split.
    + destruct Hle as [_ Hi]. eapply flows_to_trans; [exact Hi | exact Hfl].
    + split; [apply IHT1 | apply IHT2]; assumption.
Qed.

Lemma val_rel_erase : forall (l : label) (T : ty) (v1 v2 : tm),
  ground T -> all_sec_below l T -> val_rel l Low T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  intros l T. induction T as [s | T1 IHT1 T2 IHT2 s | T1 IHT1 T2 IHT2 s
                              | T1 IHT1 T2 IHT2 s];
    intros v1 v2 Hg Hall Hvr; simpl in *.
  - destruct Hall as [Hfl _].
    assert (Hobs : flows_to (join (indirect_reader s) Low) l)
      by (rewrite join_low_r; exact Hfl).
    destruct (Hvr Hobs) as [Hs1 [Hs2 Hst]]. simpl in Hst.
    destruct v1, v2; simpl in *; try contradiction; reflexivity.
  - destruct Hg as [Hg1 Hg2]. destruct Hall as [Hfl [Hall1 Hall2]].
    assert (Hobs : flows_to (join (indirect_reader s) Low) l)
      by (rewrite join_low_r; exact Hfl).
    destruct (Hvr Hobs) as [Hs1 [Hs2 Hst]]. simpl in Hst.
    destruct v1, v2; simpl in *; try contradiction.
    + f_equal. apply (IHT1 v1 v2 Hg1 Hall1 Hst).
    + f_equal. apply (IHT2 v1 v2 Hg2 Hall2 Hst).
  - destruct Hg as [Hg1 Hg2]. destruct Hall as [Hfl [Hall1 Hall2]].
    assert (Hobs : flows_to (join (indirect_reader s) Low) l)
      by (rewrite join_low_r; exact Hfl).
    destruct (Hvr Hobs) as [Hs1 [Hs2 Hst]]. simpl in Hst.
    destruct v1, v2; simpl in *; try contradiction.
    destruct Hst as [Hc1 Hc2].
    f_equal.
    + apply (IHT1 v1_1 v2_1 Hg1 Hall1 Hc1).
    + apply (IHT2 v1_2 v2_2 Hg2 Hall2 Hc2).
  - destruct Hg.
Qed.

(* ============================================================ *)
(* Noninterference                                               *)
(* ============================================================ *)

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
  intros C t1 t2 T_secret T_result Ht1 Ht2 Hctx Hgr Htr Hni.
  destruct (not_flows_to _ _ Hni) as [Hsec Hres].
  rewrite Hres in Hni.
  destruct Hctx as [L Hctx].
  pose (x := fresh_from (L ++ fv_context C)).
  assert (HxL : ~ In x L).
  { unfold x. intro Hin. apply (fresh_from_notin (L ++ fv_context C)).
    apply in_or_app. left. exact Hin. }
  assert (Hxfv : ~ In x (fv_context C)).
  { unfold x. intro Hin. apply (fresh_from_notin (L ++ fv_context C)).
    apply in_or_app. right. exact Hin. }
  assert (HtyC : has_type (update empty x T_secret) (plug C (tm_fvar x)) T_result)
    by exact (Hctx x HxL).
  pose (s1 := fun y => if Nat.eqb y x then t1 else tm_fvar y).
  pose (s2 := fun y => if Nat.eqb y x then t2 else tm_fvar y).
  assert (Henv : env_rel Low (update empty x T_secret) s1 s2).
  { split.
    - intros y. unfold s1, s2. destruct (Nat.eqb y x).
      + split.
        * apply (has_type_lc empty t1 T_secret). exact Ht1.
        * apply (has_type_lc empty t2 T_secret). exact Ht2.
      + split; exact I.
    - intros y T Hlook. apply lookup_update_some in Hlook.
      destruct Hlook as [[E1 E2] | [Hne Hlook]].
      + subst y. subst T. unfold s1, s2. rewrite Nat.eqb_refl. simpl.
        intros v1 v2 He1 He2.
        apply val_rel_vacuous_gen. rewrite join_low_r. exact Hni.
      + exfalso. unfold empty in Hlook. simpl in Hlook. discriminate Hlook. }
  pose proof (fundamental (update empty x T_secret) (plug C (tm_fvar x)) T_result
                HtyC Low s1 s2 Henv) as Hfin.
  assert (Hid1 : forall y : atom, In y (fv_context C) -> s1 y = tm_fvar y).
  { intros y Hy. unfold s1. destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. exfalso. apply Hxfv. exact Hy.
    - reflexivity. }
  assert (Hid2 : forall y : atom, In y (fv_context C) -> s2 y = tm_fvar y).
  { intros y Hy. unfold s2. destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. exfalso. apply Hxfv. exact Hy.
    - reflexivity. }
  assert (Eplug1 : subst_fn s1 (plug C (tm_fvar x)) = plug C t1).
  { rewrite (subst_fn_plug C (tm_fvar x) s1 Hid1).
    unfold s1. simpl. rewrite Nat.eqb_refl. reflexivity. }
  assert (Eplug2 : subst_fn s2 (plug C (tm_fvar x)) = plug C t2).
  { rewrite (subst_fn_plug C (tm_fvar x) s2 Hid2).
    unfold s2. simpl. rewrite Nat.eqb_refl. reflexivity. }
  rewrite Eplug1, Eplug2 in Hfin.
  unfold same_result. intros v1 v2 He1 He2.
  apply (val_rel_erase Low T_result v1 v2 Hgr).
  - apply (transparent_all_below (security_of T_result) T_result Low Htr).
    rewrite Hres. apply flows_to_refl.
  - apply Hfin; assumption.
Qed.
