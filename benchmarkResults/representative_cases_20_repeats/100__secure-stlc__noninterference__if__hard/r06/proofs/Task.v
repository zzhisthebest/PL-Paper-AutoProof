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
(* Auxiliary lemmas about labels and security annotations         *)
(* ============================================================ *)

Lemma flows_to_refl : forall l, flows_to l l.
Proof. intros []; simpl; auto. Qed.

Lemma flows_to_trans : forall l1 l2 l3,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof. intros [] [] [] H1 H2; simpl in *; auto. Qed.

Lemma flows_to_join_l : forall l1 l2 l,
  flows_to (join l1 l2) l <-> flows_to l1 l /\ flows_to l2 l.
Proof. intros [] [] []; simpl; tauto. Qed.

Lemma flows_to_join_r1 : forall l1 l2, flows_to l1 (join l1 l2).
Proof. intros l1 l2; destruct l1, l2; simpl; auto. Qed.

Lemma flows_to_join_r2 : forall l1 l2, flows_to l2 (join l1 l2).
Proof. intros l1 l2; destruct l1, l2; simpl; auto. Qed.

Lemma join_assoc : forall a b c, join (join a b) c = join a (join b c).
Proof. intros [] [] []; reflexivity. Qed.

Lemma join_idem : forall a, join a a = a.
Proof. intros []; reflexivity. Qed.

Lemma flows_to_join_both : forall a b c,
  flows_to a c -> flows_to b c -> flows_to (join a b) c.
Proof. intros a b c H1 H2; apply flows_to_join_l; auto. Qed.

Lemma not_flows_to_inv : forall a b, ~ flows_to a b -> a = High /\ b = Low.
Proof. intros [] [] H; simpl in *; try (exfalso; apply H; exact I); auto. Qed.

Lemma security_le_refl : forall k, security_le k k.
Proof. intros [r i]; unfold security_le; simpl; split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3] [H1 H2] [H3 H4];
    unfold security_le in *; simpl in *.
  split; eapply flows_to_trans; eauto.
Qed.

Lemma security_le_ind : forall k1 k2, security_le k1 k2 ->
  flows_to k1.(indirect_reader) k2.(indirect_reader).
Proof. intros k1 k2 [H1 H2]; exact H2. Qed.

Lemma security_le_reader : forall k1 k2, security_le k1 k2 ->
  flows_to k1.(reader) k2.(reader).
Proof. intros k1 k2 [H1 H2]; exact H1. Qed.

Lemma security_le_protect_join : forall a1 a2 l1 l2,
  security_le a1 a2 -> flows_to l1 l2 ->
  security_le (protect_security a1 l1) (protect_security a2 l2).
Proof.
  intros [r1 i1] [r2 i2] l1 l2 [Hr Hi] Hl.
  unfold security_le, protect_security; simpl in *.
  split; apply flows_to_join_l; split.
  - eapply flows_to_trans; [exact Hr | apply flows_to_join_r1].
  - eapply flows_to_trans; [exact Hl | apply flows_to_join_r2].
  - eapply flows_to_trans; [exact Hi | apply flows_to_join_r1].
  - eapply flows_to_trans; [exact Hl | apply flows_to_join_r2].
Qed.

Lemma protect_security_compose : forall k l1 l2,
  protect_security (protect_security k l1) l2 = protect_security k (join l1 l2).
Proof.
  intros [r i] l1 l2. unfold protect_security. simpl.
  repeat rewrite join_assoc. reflexivity.
Qed.

Lemma security_of_ty_protect : forall l T,
  security_of (ty_protect l T) = protect_security (security_of T) l.
Proof. intros l T; destruct T; reflexivity. Qed.

(* ============================================================ *)
(* Big-step evaluation, equivalent to the small-step semantics   *)
(* ============================================================ *)

Inductive eval : tm -> tm -> Prop :=
  | ev_unit : forall k, eval (tm_unit k) (tm_unit k)
  | ev_abs : forall T body k, value (tm_abs T body k) -> eval (tm_abs T body k) (tm_abs T body k)
  | ev_pair : forall t1 t2 v1 v2 k,
      eval t1 v1 -> eval t2 v2 -> eval (tm_pair t1 t2 k) (tm_pair v1 v2 k)
  | ev_inl : forall t v k, eval t v -> eval (tm_inl t k) (tm_inl v k)
  | ev_inr : forall t v k, eval t v -> eval (tm_inr t k) (tm_inr v k)
  | ev_app : forall t1 t2 v2 r T body k v,
      eval t1 (tm_abs T body k) -> eval t2 v2 -> flows_to k.(reader) r ->
      eval (tm_protect k.(indirect_reader) (open body v2)) v ->
      eval (tm_app t1 t2 r) v
  | ev_fst : forall t v1 v2 k r v,
      eval t (tm_pair v1 v2 k) -> flows_to k.(reader) r ->
      eval (tm_protect k.(indirect_reader) v1) v -> eval (tm_fst t r) v
  | ev_snd : forall t v1 v2 k r v,
      eval t (tm_pair v1 v2 k) -> flows_to k.(reader) r ->
      eval (tm_protect k.(indirect_reader) v2) v -> eval (tm_snd t r) v
  | ev_case_l : forall t v k body1 body2 r v',
      eval t (tm_inl v k) -> flows_to k.(reader) r ->
      eval (tm_protect k.(indirect_reader) (open body1 v)) v' ->
      eval (tm_case t body1 body2 r) v'
  | ev_case_r : forall t v k body1 body2 r v',
      eval t (tm_inr v k) -> flows_to k.(reader) r ->
      eval (tm_protect k.(indirect_reader) (open body2 v)) v' ->
      eval (tm_case t body1 body2 r) v'
  | ev_protect : forall t v l,
      eval t v -> eval (tm_protect l t) (protect_value v l)
  | ev_if_l : forall c v k yes no r v',
      eval c (tm_inl v k) -> flows_to k.(reader) r ->
      eval (tm_protect k.(indirect_reader) yes) v' ->
      eval (tm_if c yes no r) v'
  | ev_if_r : forall c v k yes no r v',
      eval c (tm_inr v k) -> flows_to k.(reader) r ->
      eval (tm_protect k.(indirect_reader) no) v' ->
      eval (tm_if c yes no r) v'.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; induction H; unfold locally_closed; simpl.
  - trivial.
  - exact H.
  - split; assumption.
  - assumption.
  - assumption.
Qed.

Lemma protect_value_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l H; induction H; simpl.
  - apply v_unit.
  - apply v_abs; exact H.
  - apply v_pair; assumption.
  - apply v_inl; assumption.
  - apply v_inr; assumption.
Qed.

Lemma value_eval : forall v, value v -> eval v v.
Proof.
  intros v H; induction H.
  - apply ev_unit.
  - apply ev_abs. apply v_abs. exact H.
  - apply ev_pair; assumption.
  - apply ev_inl; assumption.
  - apply ev_inr; assumption.
Qed.

Lemma eval_value : forall t v, eval t v -> value v.
Proof.
  intros t v H; induction H.
  - apply v_unit.
  - assumption.
  - apply v_pair; assumption.
  - apply v_inl; assumption.
  - apply v_inr; assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - apply protect_value_value; assumption.
  - assumption.
  - assumption.
Qed.

Lemma eval_value_inv : forall v w, value v -> eval v w -> w = v.
Proof.
  intros v w Hv He. revert w He. induction Hv; intros w He; inversion He; subst.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma eval_unit_inv : forall k v, eval (tm_unit k) v -> v = tm_unit k.
Proof. intros. inversion H; subst; reflexivity. Qed.

Lemma eval_abs_inv : forall T body k v, eval (tm_abs T body k) v -> v = tm_abs T body k.
Proof. intros. inversion H; subst; reflexivity. Qed.

Lemma eval_pair_inv : forall t1 t2 k v, eval (tm_pair t1 t2 k) v ->
  exists v1 v2, v = tm_pair v1 v2 k /\ eval t1 v1 /\ eval t2 v2.
Proof.
  intros. inversion H; subst.
  match goal with
  | H1 : eval t1 ?v1, H2 : eval t2 ?v2 |- _ => exists v1, v2; eauto
  end.
Qed.

Lemma eval_inl_inv : forall t k v, eval (tm_inl t k) v ->
  exists w, v = tm_inl w k /\ eval t w.
Proof.
  intros. inversion H; subst.
  match goal with H1 : eval t ?w |- _ => exists w; eauto end.
Qed.

Lemma eval_inr_inv : forall t k v, eval (tm_inr t k) v ->
  exists w, v = tm_inr w k /\ eval t w.
Proof.
  intros. inversion H; subst.
  match goal with H1 : eval t ?w |- _ => exists w; eauto end.
Qed.

Lemma eval_app_inv : forall t1 t2 r v, eval (tm_app t1 t2 r) v ->
  exists T body k v2,
    eval t1 (tm_abs T body k) /\ eval t2 v2 /\
    flows_to k.(reader) r /\ eval (tm_protect k.(indirect_reader) (open body v2)) v.
Proof.
  intros. inversion H; subst.
  match goal with
  | H1 : eval t1 (tm_abs ?T ?body ?k), H2 : eval t2 ?v2,
    H3 : flows_to _ _, H4 : eval (tm_protect _ (open ?body ?v2)) _ |- _ =>
      exists T, body, k, v2; eauto
  end.
Qed.

Lemma eval_protect_inv : forall l t v, eval (tm_protect l t) v ->
  exists w, eval t w /\ v = protect_value w l.
Proof. intros. inversion H; subst. eauto. Qed.

Lemma eval_fst_inv : forall t r v, eval (tm_fst t r) v ->
  exists v1 v2 k, eval t (tm_pair v1 v2 k) /\ flows_to k.(reader) r /\
    eval (tm_protect k.(indirect_reader) v1) v.
Proof.
  intros. inversion H; subst.
  match goal with
  | H1 : eval t (tm_pair ?v1 ?v2 ?k), H2 : flows_to _ _,
    H3 : eval (tm_protect _ ?v1) _ |- _ => exists v1, v2, k; eauto
  end.
Qed.

Lemma eval_snd_inv : forall t r v, eval (tm_snd t r) v ->
  exists v1 v2 k, eval t (tm_pair v1 v2 k) /\ flows_to k.(reader) r /\
    eval (tm_protect k.(indirect_reader) v2) v.
Proof.
  intros. inversion H; subst.
  match goal with
  | H1 : eval t (tm_pair ?v1 ?v2 ?k), H2 : flows_to _ _,
    H3 : eval (tm_protect _ ?v2) _ |- _ => exists v1, v2, k; eauto
  end.
Qed.

Lemma eval_case_inv : forall t b1 b2 r v, eval (tm_case t b1 b2 r) v ->
  (exists x k, eval t (tm_inl x k) /\ flows_to k.(reader) r /\
     eval (tm_protect k.(indirect_reader) (open b1 x)) v)
  \/ (exists x k, eval t (tm_inr x k) /\ flows_to k.(reader) r /\
     eval (tm_protect k.(indirect_reader) (open b2 x)) v).
Proof. intros. inversion H; subst; [left | right]; eauto. Qed.

Lemma eval_if_inv : forall c y n r v, eval (tm_if c y n r) v ->
  (exists x k, eval c (tm_inl x k) /\ flows_to k.(reader) r /\
     eval (tm_protect k.(indirect_reader) y) v)
  \/ (exists x k, eval c (tm_inr x k) /\ flows_to k.(reader) r /\
     eval (tm_protect k.(indirect_reader) n) v).
Proof. intros. inversion H; subst; [left | right]; eauto. Qed.

(* ============================================================ *)
(* Environment substitution                                      *)
(* ============================================================ *)

Fixpoint subst_env (g : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => g x
  | tm_unit k => tm_unit k
  | tm_abs T body k => tm_abs T (subst_env g body) k
  | tm_app t1 t2 r => tm_app (subst_env g t1) (subst_env g t2) r
  | tm_pair t1 t2 k => tm_pair (subst_env g t1) (subst_env g t2) k
  | tm_fst t1 r => tm_fst (subst_env g t1) r
  | tm_snd t1 r => tm_snd (subst_env g t1) r
  | tm_inl t1 k => tm_inl (subst_env g t1) k
  | tm_inr t1 k => tm_inr (subst_env g t1) k
  | tm_case t0 body1 body2 r =>
      tm_case (subst_env g t0) (subst_env g body1) (subst_env g body2) r
  | tm_protect l t1 => tm_protect l (subst_env g t1)
  | tm_if c yes no r => tm_if (subst_env g c) (subst_env g yes) (subst_env g no) r
  end.

Definition env_lc (g : atom -> tm) : Prop := forall x, locally_closed (g x).

Lemma subst_env_agree : forall g1 g2 t,
  (forall x, In x (fv t) -> g1 x = g2 x) ->
  subst_env g1 t = subst_env g2 t.
Proof.
  intros g1 g2 t; induction t; simpl; intros H.
  - reflexivity.
  - apply H. simpl. auto.
  - reflexivity.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl. apply in_app_iff. left. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl. apply in_app_iff. right. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl. apply in_app_iff. left. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl. apply in_app_iff. right. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl.
      repeat rewrite in_app_iff in *. tauto.
    + apply IHt2. intros x Hx. apply H. simpl.
      repeat rewrite in_app_iff in *. tauto.
    + apply IHt3. intros x Hx. apply H. simpl.
      repeat rewrite in_app_iff in *. tauto.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl.
      repeat rewrite in_app_iff in *. tauto.
    + apply IHt2. intros x Hx. apply H. simpl.
      repeat rewrite in_app_iff in *. tauto.
    + apply IHt3. intros x Hx. apply H. simpl.
      repeat rewrite in_app_iff in *. tauto.
Qed.

Lemma subst_env_id : forall g t,
  (forall x, In x (fv t) -> g x = tm_fvar x) -> subst_env g t = t.
Proof.
  intros g t; induction t; simpl; intros H.
  - reflexivity.
  - apply H. simpl. auto.
  - reflexivity.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl. apply in_app_iff. left. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl. apply in_app_iff. right. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl. apply in_app_iff. left. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl. apply in_app_iff. right. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl.
      repeat rewrite in_app_iff in *. tauto.
    + apply IHt2. intros x Hx. apply H. simpl.
      repeat rewrite in_app_iff in *. tauto.
    + apply IHt3. intros x Hx. apply H. simpl.
      repeat rewrite in_app_iff in *. tauto.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl.
      repeat rewrite in_app_iff in *. tauto.
    + apply IHt2. intros x Hx. apply H. simpl.
      repeat rewrite in_app_iff in *. tauto.
    + apply IHt3. intros x Hx. apply H. simpl.
      repeat rewrite in_app_iff in *. tauto.
Qed.

Lemma le_S_S : forall a b : nat, a <= b -> S a <= S b.
Proof. intros; lia. Qed.

Lemma open_rec_lc : forall t j, lc_at j t -> forall k u, j <= k -> open_rec k u t = t.
Proof.
  intros t; induction t; intros j Hlc k u Hjk; simpl in *.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. lia.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - (* abs *) f_equal. eauto using le_S_S.
  - (* app *) destruct Hlc as [H1 H2]. f_equal; eauto.
  - (* pair *) destruct Hlc as [H1 H2]. f_equal; eauto.
  - (* fst *) f_equal. eauto.
  - (* snd *) f_equal. eauto.
  - (* inl *) f_equal. eauto.
  - (* inr *) f_equal. eauto.
  - (* case *) destruct Hlc as [H0 [H1 H2]]. f_equal; eauto using le_S_S.
  - (* protect *) f_equal. eauto.
  - (* if *) destruct Hlc as [H0 [H1 H2]]. f_equal; eauto.
Qed.

Lemma lc_open_rec_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros t; induction t; intros k x H; simpl in *.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E; simpl in H.
    + apply Nat.eqb_eq in E. subst. lia.
    + apply Nat.eqb_neq in E. lia.
  - auto.
  - auto.
  - (* abs *) eauto.
  - (* app *) destruct H as [H1 H2]. split; eauto.
  - (* pair *) destruct H as [H1 H2]. split; eauto.
  - (* fst *) eauto.
  - (* snd *) eauto.
  - (* inl *) eauto.
  - (* inr *) eauto.
  - (* case *) destruct H as [H0 [H1 H2]]. split; [eauto | split]; eauto.
  - (* protect *) eauto.
  - (* if *) destruct H as [H0 [H1 H2]]. split; [eauto | split]; eauto.
Qed.

Lemma subst_env_open_rec : forall g t u k,
  env_lc g ->
  subst_env g (open_rec k u t) = open_rec k (subst_env g u) (subst_env g t).
Proof.
  intros g t; induction t; intros u k Hlc; simpl.
  - (* bvar *) destruct (Nat.eqb k n); reflexivity.
  - (* fvar *) symmetry. apply (open_rec_lc (g a) 0). apply Hlc. lia.
  - (* unit *) reflexivity.
  - (* abs *) f_equal. apply IHt. exact Hlc.
  - (* app *) f_equal; [apply IHt1 | apply IHt2]; exact Hlc.
  - (* pair *) f_equal; [apply IHt1 | apply IHt2]; exact Hlc.
  - (* fst *) f_equal. apply IHt. exact Hlc.
  - (* snd *) f_equal. apply IHt. exact Hlc.
  - (* inl *) f_equal. apply IHt. exact Hlc.
  - (* inr *) f_equal. apply IHt. exact Hlc.
  - (* case *) f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; exact Hlc.
  - (* protect *) f_equal. apply IHt. exact Hlc.
  - (* if *) f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; exact Hlc.
Qed.

Lemma subst_env_open : forall g body x v,
  env_lc g -> g x = v ->
  subst_env g (open body (tm_fvar x)) = open (subst_env g body) v.
Proof.
  intros g body x v Hlc Hgx. unfold open.
  rewrite subst_env_open_rec; auto.
  simpl. rewrite Hgx. reflexivity.
Qed.

Lemma subst_env_update_agree : forall g x v t,
  ~ In x (fv t) ->
  subst_env (fun y => if Nat.eqb y x then v else g y) t = subst_env g t.
Proof.
  intros g x v t Hx. apply subst_env_agree.
  intros y Hy. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst. exfalso. apply Hx. exact Hy.
  - reflexivity.
Qed.

(* ============================================================ *)
(* Free variables of program contexts                            *)
(* ============================================================ *)

Fixpoint fvsC (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs T C' k => fvsC C'
  | C_AppLeft C' t r => fvsC C' ++ fv t
  | C_AppRight t C' r => fv t ++ fvsC C'
  | C_PairLeft C' t k => fvsC C' ++ fv t
  | C_PairRight t C' k => fv t ++ fvsC C'
  | C_Fst C' r => fvsC C'
  | C_Snd C' r => fvsC C'
  | C_Inl C' k => fvsC C'
  | C_Inr C' k => fvsC C'
  | C_CaseScrutinee C' b1 b2 r => fvsC C' ++ fv b1 ++ fv b2
  | C_CaseLeft t0 C' b2 r => fv t0 ++ fvsC C' ++ fv b2
  | C_CaseRight t0 b1 C' r => fv t0 ++ fv b1 ++ fvsC C'
  | C_Protect l C' => fvsC C'
  | C_IfCondition C' y n r => fvsC C' ++ fv y ++ fv n
  | C_IfThen c C' n r => fv c ++ fvsC C' ++ fv n
  | C_IfElse c y C' r => fv c ++ fv y ++ fvsC C'
  end.

Lemma in_app_l : forall (A : Type) (l1 l2 : list A) (x : A),
  In x l1 -> In x (l1 ++ l2).
Proof. intros; apply in_app_iff; auto. Qed.

Lemma in_app_r : forall (A : Type) (l1 l2 : list A) (x : A),
  In x l2 -> In x (l1 ++ l2).
Proof. intros; apply in_app_iff; auto. Qed.

Lemma subst_env_plug : forall C u g,
  (forall x, In x (fvsC C) -> g x = tm_fvar x) ->
  subst_env g (plug C u) = plug C (subst_env g u).
Proof.
  intros C; induction C; simpl; intros u g H.
  - (* C_Hole *) reflexivity.
  - (* C_Abs *) f_equal. apply IHC. exact H.
  - (* C_AppLeft *) f_equal.
    + apply IHC. intros x Hx. apply H. simpl. apply in_app_l. exact Hx.
    + apply subst_env_id. intros x Hx. apply H. simpl. apply in_app_r. exact Hx.
  - (* C_AppRight *) f_equal.
    + apply subst_env_id. intros x Hx. apply H. simpl. apply in_app_l. exact Hx.
    + apply IHC. intros x Hx. apply H. simpl. apply in_app_r. exact Hx.
  - (* C_PairLeft *) f_equal.
    + apply IHC. intros x Hx. apply H. simpl. apply in_app_l. exact Hx.
    + apply subst_env_id. intros x Hx. apply H. simpl. apply in_app_r. exact Hx.
  - (* C_PairRight *) f_equal.
    + apply subst_env_id. intros x Hx. apply H. simpl. apply in_app_l. exact Hx.
    + apply IHC. intros x Hx. apply H. simpl. apply in_app_r. exact Hx.
  - (* C_Fst *) f_equal. apply IHC. exact H.
  - (* C_Snd *) f_equal. apply IHC. exact H.
  - (* C_Inl *) f_equal. apply IHC. exact H.
  - (* C_Inr *) f_equal. apply IHC. exact H.
  - (* C_CaseScrutinee *) f_equal.
    + apply IHC. intros x Hx. apply H. simpl. apply in_app_l. exact Hx.
    + apply subst_env_id. intros x Hx. apply H. simpl.
      apply in_app_r. apply in_app_l. exact Hx.
    + apply subst_env_id. intros x Hx. apply H. simpl.
      apply in_app_r. apply in_app_r. exact Hx.
  - (* C_CaseLeft *) f_equal.
    + apply subst_env_id. intros x Hx. apply H. simpl. apply in_app_l. exact Hx.
    + apply IHC. intros x Hx. apply H. simpl.
      apply in_app_r. apply in_app_l. exact Hx.
    + apply subst_env_id. intros x Hx. apply H. simpl.
      apply in_app_r. apply in_app_r. exact Hx.
  - (* C_CaseRight *) f_equal.
    + apply subst_env_id. intros x Hx. apply H. simpl. apply in_app_l. exact Hx.
    + apply subst_env_id. intros x Hx. apply H. simpl.
      apply in_app_r. apply in_app_l. exact Hx.
    + apply IHC. intros x Hx. apply H. simpl.
      apply in_app_r. apply in_app_r. exact Hx.
  - (* C_Protect *) f_equal. apply IHC. exact H.
  - (* C_IfCondition *) f_equal.
    + apply IHC. intros x Hx. apply H. simpl. apply in_app_l. exact Hx.
    + apply subst_env_id. intros x Hx. apply H. simpl.
      apply in_app_r. apply in_app_l. exact Hx.
    + apply subst_env_id. intros x Hx. apply H. simpl.
      apply in_app_r. apply in_app_r. exact Hx.
  - (* C_IfThen *) f_equal.
    + apply subst_env_id. intros x Hx. apply H. simpl. apply in_app_l. exact Hx.
    + apply IHC. intros x Hx. apply H. simpl.
      apply in_app_r. apply in_app_l. exact Hx.
    + apply subst_env_id. intros x Hx. apply H. simpl.
      apply in_app_r. apply in_app_r. exact Hx.
  - (* C_IfElse *) f_equal.
    + apply subst_env_id. intros x Hx. apply H. simpl. apply in_app_l. exact Hx.
    + apply subst_env_id. intros x Hx. apply H. simpl.
      apply in_app_r. apply in_app_l. exact Hx.
    + apply IHC. intros x Hx. apply H. simpl.
      apply in_app_r. apply in_app_r. exact Hx.
Qed.

(* ============================================================ *)
(* Fresh atoms                                                   *)
(* ============================================================ *)

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (max_list l')
  end.

Lemma max_list_ge : forall l x, In x l -> x <= max_list l.
Proof.
  induction l; simpl; intros x H.
  - contradiction.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IHl; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (max_list L)). intros H.
  pose proof (max_list_ge L _ H). lia.
Qed.

(* ============================================================ *)
(* Typing implies local closure                                  *)
(* ============================================================ *)

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H; induction H; simpl.
  - (* T_Var *) exact I.
  - (* T_Unit *) exact I.
  - (* T_Abs *)
    match goal with
    | IH : forall x : atom, ~ In x ?L -> locally_closed (open ?body (tm_fvar x)) |- _ =>
        destruct (fresh_atom L) as [x Hx];
        specialize (IH x Hx); simpl in IH;
        exact (lc_open_rec_inv body 0 x IH)
    end.
  - (* T_App *) split; assumption.
  - (* T_Pair *) split; assumption.
  - (* T_Fst *) assumption.
  - (* T_Snd *) assumption.
  - (* T_Inl *) assumption.
  - (* T_Inr *) assumption.
  - (* T_Case *)
    match goal with
    | IH1 : forall x : atom, ~ In x ?L -> locally_closed (open ?b1 (tm_fvar x)),
      IH2 : forall x : atom, ~ In x ?L -> locally_closed (open ?b2 (tm_fvar x)) |- _ =>
        destruct (fresh_atom L) as [x Hx];
        specialize (IH1 x Hx); specialize (IH2 x Hx);
        simpl in IH1, IH2;
        split; [assumption | split];
        [ exact (lc_open_rec_inv b1 0 x IH1) | exact (lc_open_rec_inv b2 0 x IH2) ]
    end.
  - (* T_Protect *) assumption.
  - (* T_Sub *) assumption.
  - (* T_If *) split; [assumption | split; assumption].
Qed.

(* ============================================================ *)
(* Small-step to big-step evaluation                             *)
(* ============================================================ *)

Lemma step_eval : forall t1 t2, step t1 t2 -> forall v, eval t2 v -> eval t1 v.
Proof.
  intros t1 t2 H. induction H; intros w He.
  - (* ST_AppAbs *) inversion He; subst. eapply ev_app.
    + apply ev_abs. assumption.
    + apply value_eval. assumption.
    + assumption.
    + eapply ev_protect. eassumption.
  - (* ST_App1 *) inversion He; subst. eapply ev_app.
    + apply IHstep. eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
  - (* ST_App2 *) inversion He; subst. eapply ev_app.
    + eassumption.
    + apply IHstep. eassumption.
    + eassumption.
    + eassumption.
  - (* ST_Pair1 *) inversion He; subst. eapply ev_pair.
    + apply IHstep. eassumption.
    + eassumption.
  - (* ST_Pair2 *) inversion He; subst. eapply ev_pair.
    + eassumption.
    + apply IHstep. eassumption.
  - (* ST_FstPair *) inversion He; subst. eapply ev_fst.
    + eapply ev_pair; apply value_eval; assumption.
    + assumption.
    + eapply ev_protect. eassumption.
  - (* ST_Fst *) inversion He; subst. eapply ev_fst.
    + apply IHstep. eassumption.
    + eassumption.
    + eassumption.
  - (* ST_SndPair *) inversion He; subst. eapply ev_snd.
    + eapply ev_pair; apply value_eval; assumption.
    + assumption.
    + eapply ev_protect. eassumption.
  - (* ST_Snd *) inversion He; subst. eapply ev_snd.
    + apply IHstep. eassumption.
    + eassumption.
    + eassumption.
  - (* ST_Inl *) inversion He; subst. eapply ev_inl. apply IHstep. eassumption.
  - (* ST_Inr *) inversion He; subst. eapply ev_inr. apply IHstep. eassumption.
  - (* ST_CaseLeft *) inversion He; subst. eapply ev_case_l.
    + eapply ev_inl. apply value_eval. assumption.
    + assumption.
    + eapply ev_protect. eassumption.
  - (* ST_CaseRight *) inversion He; subst. eapply ev_case_r.
    + eapply ev_inr. apply value_eval. assumption.
    + assumption.
    + eapply ev_protect. eassumption.
  - (* ST_Case *) inversion He; subst.
    + eapply ev_case_l.
      * apply IHstep. eassumption.
      * eassumption.
      * eassumption.
    + eapply ev_case_r.
      * apply IHstep. eassumption.
      * eassumption.
      * eassumption.
  - (* ST_ProtectValue *)
    pose proof (eval_value_inv (protect_value v l) w (protect_value_value v l H) He) as E.
    subst w. apply ev_protect. apply value_eval. assumption.
  - (* ST_Protect *) inversion He; subst. eapply ev_protect. apply IHstep. eassumption.
  - (* ST_If *) inversion He; subst.
    + eapply ev_if_l.
      * apply IHstep. eassumption.
      * eassumption.
      * eassumption.
    + eapply ev_if_r.
      * apply IHstep. eassumption.
      * eassumption.
      * eassumption.
  - (* ST_IfTrue *) inversion He; subst. eapply ev_if_l.
    + eapply ev_inl. apply value_eval. assumption.
    + assumption.
    + eapply ev_protect. eassumption.
  - (* ST_IfFalse *) inversion He; subst. eapply ev_if_r.
    + eapply ev_inr. apply value_eval. assumption.
    + assumption.
    + eapply ev_protect. eassumption.
Qed.

Lemma multi_eval : forall t v, multi t v -> value v -> eval t v.
Proof.
  intros t v H. induction H; intros Hv.
  - apply value_eval. exact Hv.
  - eapply step_eval.
    + eassumption.
    + apply IHmulti. exact Hv.
Qed.

(* ============================================================ *)
(* The logical relation                                          *)
(* ============================================================ *)

Lemma protect_value_compose : forall v l1 l2,
  protect_value (protect_value v l1) l2 = protect_value v (join l1 l2).
Proof.
  intros v l1 l2. destruct v; cbn [protect_value];
    try reflexivity;
    try (rewrite protect_security_compose; reflexivity).
Qed.

Fixpoint Vp (l : label) (T : ty) (kappa : security) (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_Unit _ =>
      flows_to kappa.(indirect_reader) l ->
        (exists k1 k2 : security,
           v1 = tm_unit k1 /\ v2 = tm_unit k2 /\
           security_le k1 kappa /\ security_le k2 kappa)
  | Ty_Sum A B _ =>
      flows_to kappa.(indirect_reader) l ->
        ((exists (a1 a2 : tm) (k1 k2 : security),
            v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\
            security_le k1 kappa /\ security_le k2 kappa /\
            Vp l A (security_of A) a1 a2)
         \/
         (exists (b1 b2 : tm) (k1 k2 : security),
            v1 = tm_inr b1 k1 /\ v2 = tm_inr b2 k2 /\
            security_le k1 kappa /\ security_le k2 kappa /\
            Vp l B (security_of B) b1 b2))
  | Ty_Prod A B _ =>
      flows_to kappa.(indirect_reader) l ->
        (exists (a1 b1 a2 b2 : tm) (k1 k2 : security),
            v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
            security_le k1 kappa /\ security_le k2 kappa /\
            Vp l A (security_of A) a1 a2 /\
            Vp l B (security_of B) b1 b2)
  | Ty_Arrow A B _ =>
      flows_to kappa.(indirect_reader) l ->
        (exists (A1 : ty) (body1 : tm) (k1 : security)
                (A2 : ty) (body2 : tm) (k2 : security),
            v1 = tm_abs A1 body1 k1 /\ v2 = tm_abs A2 body2 k2 /\
            security_le k1 kappa /\ security_le k2 kappa /\
            forall (r : label) (t1 t2 : tm),
              (forall (u1 u2 : tm), eval t1 u1 -> eval t2 u2 ->
                 Vp l A (security_of A) u1 u2) ->
              forall (u1 u2 : tm),
                eval (tm_app v1 t1 r) u1 -> eval (tm_app v2 t2 r) u2 ->
                Vp l B (protect_security (security_of B) kappa.(indirect_reader)) u1 u2)
  end.

Definition E (l : label) (T : ty) (t1 t2 : tm) : Prop :=
  forall (v1 v2 : tm), eval t1 v1 -> eval t2 v2 -> Vp l T (security_of T) v1 v2.

Lemma Vp_ty_protect : forall l l' T kappa v1 v2,
  Vp l (ty_protect l' T) kappa v1 v2 = Vp l T kappa v1 v2.
Proof. intros l l' T; destruct T; reflexivity. Qed.

Lemma value_abs_sec_irrel : forall A body k1 k2,
  value (tm_abs A body k1) -> value (tm_abs A body k2).
Proof.
  intros A body k1 k2 H. inversion H; subst. apply v_abs. assumption.
Qed.

Lemma eval_app_protect_abs : forall (A : ty) (body t : tm) (kv : security) (l r : label) (w : tm),
  eval (tm_app (protect_value (tm_abs A body kv) l) t r) w ->
  exists w', eval (tm_app (tm_abs A body kv) t r) w' /\ w = protect_value w' l.
Proof.
  intros A body t kv l r w H. simpl in H.
  inversion H; subst.
  inversion H7; subst.
  inversion H3; subst.
  exists (protect_value v kv.(indirect_reader)). split.
  - eapply ev_app with (v2 := v2).
    + apply ev_abs. apply value_abs_sec_irrel with (k1 := protect_security kv l).
      exact (eval_value _ _ H3).
    + exact H4.
    + apply flows_to_join_l in H6. apply (proj1 H6).
    + apply ev_protect. exact H5.
  - cbn [indirect_reader]. symmetry. apply protect_value_compose.
Qed.

Lemma Vp_protect2 : forall l T kappa v1 v2 l1 l2,
  Vp l T kappa v1 v2 ->
  Vp l T (protect_security kappa (join l1 l2))
       (protect_value v1 l1) (protect_value v2 l2).
Proof.
  intros l T; induction T; intros kappa v1 v2 l1 l2 HV.
  - (* Ty_Unit *) simpl. intro Hvis.
    apply flows_to_join_l in Hvis. destruct Hvis as [Hk Hl].
    destruct (HV Hk) as [k1 [k2 [E1 [E2 [B1 B2]]]]].
    subst v1 v2. simpl.
    exists (protect_security k1 l1), (protect_security k2 l2).
    split; [reflexivity | split; [reflexivity | split]].
    + apply security_le_protect_join.
      * exact B1.
      * apply flows_to_join_r1.
    + apply security_le_protect_join.
      * exact B2.
      * apply flows_to_join_r2.
  - (* Ty_Sum *) simpl. intro Hvis.
    apply flows_to_join_l in Hvis. destruct Hvis as [Hk Hl].
    destruct (HV Hk) as
      [[a1 [a2 [k1 [k2 [E1 [E2 [B1 [B2 HP]]]]]]]]
      |[b1 [b2 [k1 [k2 [E1 [E2 [B1 [B2 HP]]]]]]]]].
    + subst v1 v2. simpl. left.
      exists a1, a2, (protect_security k1 l1), (protect_security k2 l2).
      split; [reflexivity | split; [reflexivity | split]].
      * apply security_le_protect_join.
        -- exact B1.
        -- apply flows_to_join_r1.
      * split.
        -- apply security_le_protect_join.
           ++ exact B2.
           ++ apply flows_to_join_r2.
        -- exact HP.
    + subst v1 v2. simpl. right.
      exists b1, b2, (protect_security k1 l1), (protect_security k2 l2).
      split; [reflexivity | split; [reflexivity | split]].
      * apply security_le_protect_join.
        -- exact B1.
        -- apply flows_to_join_r1.
      * split.
        -- apply security_le_protect_join.
           ++ exact B2.
           ++ apply flows_to_join_r2.
        -- exact HP.
  - (* Ty_Prod *) simpl. intro Hvis.
    apply flows_to_join_l in Hvis. destruct Hvis as [Hk Hl].
    destruct (HV Hk) as
      [a1 [b1 [a2 [b2 [k1 [k2 [E1 [E2 [B1 [B2 [HP1 HP2]]]]]]]]]]].
    subst v1 v2. simpl.
    exists a1, b1, a2, b2, (protect_security k1 l1), (protect_security k2 l2).
    split; [reflexivity | split; [reflexivity | split]].
    + apply security_le_protect_join.
      * exact B1.
      * apply flows_to_join_r1.
    + split.
      * apply security_le_protect_join.
        -- exact B2.
        -- apply flows_to_join_r2.
      * split; assumption.
  - (* Ty_Arrow *) simpl. intro Hvis.
    apply flows_to_join_l in Hvis. destruct Hvis as [Hk Hl].
    destruct (HV Hk) as
      [A1 [body1 [k1 [A2 [body2 [k2 [E1 [E2 [B1 [B2 HCl]]]]]]]]]].
    subst v1 v2. simpl.
    exists A1, body1, (protect_security k1 l1), A2, body2, (protect_security k2 l2).
    split; [reflexivity | split; [reflexivity | split]].
    + apply security_le_protect_join.
      * exact B1.
      * apply flows_to_join_r1.
    + split.
      * apply security_le_protect_join.
        -- exact B2.
        -- apply flows_to_join_r2.
      * intros r t1 t2 HE u1 u2 Hev1 Hev2.
        destruct (eval_app_protect_abs A1 body1 t1 k1 l1 r u1 Hev1)
          as [u1' [Hev1' Eq1]].
        destruct (eval_app_protect_abs A2 body2 t2 k2 l2 r u2 Hev2)
          as [u2' [Hev2' Eq2]].
        specialize (HCl r t1 t2 HE u1' u2' Hev1' Hev2').
        match goal with
        | IHT2 : forall (kappa0 : security) (v1' v2' : tm) (m1 m2 : label),
              Vp l T2 kappa0 v1' v2' ->
              Vp l T2 (protect_security kappa0 (join m1 m2))
                   (protect_value v1' m1) (protect_value v2' m2) |- _ =>
            specialize (IHT2 (protect_security (security_of T2) kappa.(indirect_reader))
                            u1' u2' l1 l2 HCl);
            rewrite protect_security_compose in IHT2;
            rewrite Eq1, Eq2; exact IHT2
        end.
Qed.

Lemma Vp_security_le : forall l T kappa1 kappa2 v1 v2,
  security_le kappa1 kappa2 ->
  Vp l T kappa1 v1 v2 ->
  Vp l T kappa2 v1 v2.
Proof.
  intros l T; induction T; intros kappa1 kappa2 v1 v2 Hle HV.
  - (* Ty_Unit *) simpl. intro Hvis.
    assert (Hvis1 : flows_to (indirect_reader kappa1) l).
    { eapply flows_to_trans; [apply security_le_ind; exact Hle | exact Hvis]. }
    destruct (HV Hvis1) as [k1 [k2 [E1 [E2 [B1 B2]]]]].
    exists k1, k2. split; [exact E1 | split; [exact E2 | split]].
    + eapply security_le_trans; eassumption.
    + eapply security_le_trans; eassumption.
  - (* Ty_Sum *) simpl. intro Hvis.
    assert (Hvis1 : flows_to (indirect_reader kappa1) l).
    { eapply flows_to_trans; [apply security_le_ind; exact Hle | exact Hvis]. }
    destruct (HV Hvis1) as
      [[a1 [a2 [k1 [k2 [E1 [E2 [B1 [B2 HP]]]]]]]]
      |[b1 [b2 [k1 [k2 [E1 [E2 [B1 [B2 HP]]]]]]]]].
    + left. exists a1, a2, k1, k2.
      split; [exact E1 | split; [exact E2 | split]].
      * eapply security_le_trans; eassumption.
      * split; [eapply security_le_trans; eassumption | exact HP].
    + right. exists b1, b2, k1, k2.
      split; [exact E1 | split; [exact E2 | split]].
      * eapply security_le_trans; eassumption.
      * split; [eapply security_le_trans; eassumption | exact HP].
  - (* Ty_Prod *) simpl. intro Hvis.
    assert (Hvis1 : flows_to (indirect_reader kappa1) l).
    { eapply flows_to_trans; [apply security_le_ind; exact Hle | exact Hvis]. }
    destruct (HV Hvis1) as
      [a1 [b1 [a2 [b2 [k1 [k2 [E1 [E2 [B1 [B2 [HP1 HP2]]]]]]]]]]].
    exists a1, b1, a2, b2, k1, k2.
    split; [exact E1 | split; [exact E2 | split]].
    + eapply security_le_trans; eassumption.
    + split.
      * eapply security_le_trans; eassumption.
      * split; assumption.
  - (* Ty_Arrow *) simpl. intro Hvis.
    assert (Hvis1 : flows_to (indirect_reader kappa1) l).
    { eapply flows_to_trans; [apply security_le_ind; exact Hle | exact Hvis]. }
    destruct (HV Hvis1) as
      [A1 [body1 [k1 [A2 [body2 [k2 [E1 [E2 [B1 [B2 HCl]]]]]]]]]].
    exists A1, body1, k1, A2, body2, k2.
    split; [exact E1 | split; [exact E2 | split]].
    + eapply security_le_trans; eassumption.
    + split.
      * eapply security_le_trans; eassumption.
      * intros r t1 t2 HE u1 u2 Hev1 Hev2.
        specialize (HCl r t1 t2 HE u1 u2 Hev1 Hev2).
        eapply IHT2.
        -- apply security_le_protect_join.
           ++ apply security_le_refl.
           ++ apply security_le_ind; exact Hle.
        -- exact HCl.
Qed.

Lemma subtype_security_le : forall T U, subtype T U ->
  security_le (security_of T) (security_of U).
Proof.
  intros T U H; induction H; simpl.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - eapply security_le_trans; eassumption.
Qed.

Lemma Vp_sub : forall T U, subtype T U ->
  forall l kappaT kappaU v1 v2,
    security_le kappaT kappaU ->
    Vp l T kappaT v1 v2 ->
    Vp l U kappaU v1 v2.
Proof.
  intros T U H; induction H; intros l kT kU v1 v2 Hle HV.
  - (* S_Unit *) simpl. intro Hvis.
    assert (Hvis1 : flows_to (indirect_reader kT) l).
    { eapply flows_to_trans; [apply security_le_ind; exact Hle | exact Hvis]. }
    destruct (HV Hvis1) as [k1 [k2 [E1 [E2 [B1 B2]]]]].
    exists k1, k2. split; [exact E1 | split; [exact E2 | split]].
    + eapply security_le_trans; eassumption.
    + eapply security_le_trans; eassumption.
  - (* S_Sum *) simpl. intro Hvis.
    assert (Hvis1 : flows_to (indirect_reader kT) l).
    { eapply flows_to_trans; [apply security_le_ind; exact Hle | exact Hvis]. }
    destruct (HV Hvis1) as
      [[a1 [a2 [k1 [k2 [E1 [E2 [B1 [B2 HP]]]]]]]]
      |[b1 [b2 [k1 [k2 [E1 [E2 [B1 [B2 HP]]]]]]]]].
    + left. exists a1, a2, k1, k2.
      split; [exact E1 | split; [exact E2 | split]].
      * eapply security_le_trans; eassumption.
      * split.
        -- eapply security_le_trans; eassumption.
        -- eauto using subtype_security_le.
    + right. exists b1, b2, k1, k2.
      split; [exact E1 | split; [exact E2 | split]].
      * eapply security_le_trans; eassumption.
      * split.
        -- eapply security_le_trans; eassumption.
        -- eauto using subtype_security_le.
  - (* S_Prod *) simpl. intro Hvis.
    assert (Hvis1 : flows_to (indirect_reader kT) l).
    { eapply flows_to_trans; [apply security_le_ind; exact Hle | exact Hvis]. }
    destruct (HV Hvis1) as
      [a1 [b1 [a2 [b2 [k1 [k2 [E1 [E2 [B1 [B2 [HP1 HP2]]]]]]]]]]].
    exists a1, b1, a2, b2, k1, k2.
    split; [exact E1 | split; [exact E2 | split]].
    + eapply security_le_trans; eassumption.
    + split.
      * eapply security_le_trans; eassumption.
      * split; eauto using subtype_security_le.
  - (* S_Arrow *) simpl. intro Hvis.
    assert (Hvis1 : flows_to (indirect_reader kT) l).
    { eapply flows_to_trans; [apply security_le_ind; exact Hle | exact Hvis]. }
    destruct (HV Hvis1) as
      [A1 [body1 [k1 [A2 [body2 [k2 [E1 [E2 [B1 [B2 HCl]]]]]]]]]].
    exists A1, body1, k1, A2, body2, k2.
    split; [exact E1 | split; [exact E2 | split]].
    + eapply security_le_trans; eassumption.
    + split.
      * eapply security_le_trans; eassumption.
      * intros r t1 t2 HE u1 u2 Hev1 Hev2.
        assert (HE' : forall u1 u2, eval t1 u1 -> eval t2 u2 ->
                       Vp l T1 (security_of T1) u1 u2).
        { intros w1 w2 Ev1 Ev2. eauto using subtype_security_le. }
        specialize (HCl r t1 t2 HE' u1 u2 Hev1 Hev2).
        eauto using subtype_security_le, security_le_protect_join,
                    security_le_ind, security_le_refl.
  - (* S_Trans *)
    match goal with
    | IH1 : forall (l0 : label) (a b : security) (x1 x2 : tm),
          security_le a b -> Vp l0 T a x1 x2 -> Vp l0 U b x1 x2,
      IH2 : forall (l0 : label) (a b : security) (x1 x2 : tm),
          security_le a b -> Vp l0 U a x1 x2 -> Vp l0 V b x1 x2 |- _ =>
        eapply IH2;
        [ exact Hle
        | eapply IH1;
          [ apply security_le_refl
          | exact HV ] ]
    end.
Qed.

Fixpoint all_ind_flows (l : label) (T : ty) : Prop :=
  flows_to (security_of T).(indirect_reader) l /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum A B _ | Ty_Prod A B _ | Ty_Arrow A B _ =>
      all_ind_flows l A /\ all_ind_flows l B
  end.

Lemma transparent_all_ind : forall T kappa l,
  transparent_at kappa T -> flows_to kappa.(indirect_reader) l ->
  all_ind_flows l T.
Proof.
  intros T; induction T; intros kappa l Htr Hf; simpl in Htr |- *.
  - destruct Htr as [Hle _]. split; [| trivial].
    eapply flows_to_trans; [apply security_le_ind; exact Hle | exact Hf].
  - destruct Htr as [Hle [H1 H2]]. split; [| split].
    + eapply flows_to_trans; [apply security_le_ind; exact Hle | exact Hf].
    + apply (IHT1 kappa l); assumption.
    + apply (IHT2 kappa l); assumption.
  - destruct Htr as [Hle [H1 H2]]. split; [| split].
    + eapply flows_to_trans; [apply security_le_ind; exact Hle | exact Hf].
    + apply (IHT1 kappa l); assumption.
    + apply (IHT2 kappa l); assumption.
  - destruct Htr as [Hle [H1 H2]]. split; [| split].
    + eapply flows_to_trans; [apply security_le_ind; exact Hle | exact Hf].
    + apply (IHT1 kappa l); assumption.
    + apply (IHT2 kappa l); assumption.
Qed.

Lemma Vp_ground_erase : forall T l v1 v2,
  ground T -> all_ind_flows l T ->
  Vp l T (security_of T) v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  intros T; induction T; intros l v1 v2 Hg Hall HV.
  - (* Ty_Unit *) simpl in Hg. simpl in Hall.
    destruct Hall as [Hf _].
    destruct (HV Hf) as [k1 [k2 [E1 [E2 _]]]]. subst v1 v2. reflexivity.
  - (* Ty_Sum *) simpl in Hg. simpl in Hall.
    destruct Hg as [Hg1 Hg2]. destruct Hall as [Hf [HA HB]].
    destruct (HV Hf) as
      [[a1 [a2 [k1 [k2 [E1 [E2 [B1 [B2 HP]]]]]]]]
      |[b1 [b2 [k1 [k2 [E1 [E2 [B1 [B2 HP]]]]]]]]].
    + subst v1 v2. simpl. rewrite (IHT1 l a1 a2 Hg1 HA HP). reflexivity.
    + subst v1 v2. simpl. rewrite (IHT2 l b1 b2 Hg2 HB HP). reflexivity.
  - (* Ty_Prod *) simpl in Hg. simpl in Hall.
    destruct Hg as [Hg1 Hg2]. destruct Hall as [Hf [HA HB]].
    destruct (HV Hf) as
      [a1 [b1 [a2 [b2 [k1 [k2 [E1 [E2 [B1 [B2 [HP1 HP2]]]]]]]]]]].
    subst v1 v2. simpl.
    rewrite (IHT1 l a1 a2 Hg1 HA HP1).
    rewrite (IHT2 l b1 b2 Hg2 HB HP2). reflexivity.
  - (* Ty_Arrow *) simpl in Hg. destruct Hg.
Qed.

Lemma Vp_E_values : forall l T v1 v2,
  Vp l T (security_of T) v1 v2 -> value v1 -> value v2 -> E l T v1 v2.
Proof.
  intros l T v1 v2 HV Hv1 Hv2. unfold E.
  intros u1 u2 He1 He2.
  rewrite (eval_value_inv v1 u1 Hv1 He1).
  rewrite (eval_value_inv v2 u2 Hv2 He2).
  exact HV.
Qed.



Definition flowb (a b : label) : bool :=
  match a, b with
  | High, Low => false
  | _, _ => true
  end.

Lemma flowb_true : forall a b, flowb a b = true <-> flows_to a b.
Proof.
  intros [] []; simpl; try tauto.
  split.
  - discriminate.
  - intros H; destruct H.
Qed.

Lemma flowb_false : forall a b, flowb a b = false <-> ~ flows_to a b.
Proof.
  intros [] []; simpl; try tauto.
  all: split; [discriminate | intros H; exfalso; apply H; exact I].
Qed.

Lemma Vp_invisible : forall ell T kappa v1 v2,
  ~ flows_to kappa.(indirect_reader) ell -> Vp ell T kappa v1 v2.
Proof.
  intros ell T; destruct T; intros kappa v1 v2 H; simpl; intro Hvis;
    exfalso; apply H; exact Hvis.
Qed.

(* ============================================================ *)
(* The fundamental theorem                                       *)
(* ============================================================ *)

Definition env_rel (l : label) (Gamma : context) (g1 g2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> E l T (g1 x) (g2 x).

Definition upd (g : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then v else g y.

Lemma upd_same : forall g x v, upd g x v x = v.
Proof. intros. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_neq : forall g x v y, y <> x -> upd g x v y = g y.
Proof. intros. unfold upd. destruct (Nat.eqb y x) eqn:E; auto.
  apply Nat.eqb_eq in E. contradiction. Qed.

Lemma env_lc_upd : forall g x v,
  env_lc g -> locally_closed v -> env_lc (upd g x v).
Proof.
  intros g x v Hg Hv y. unfold upd. destruct (Nat.eqb y x); [exact Hv | apply Hg].
Qed.

Lemma subst_env_upd_agree : forall g x v t,
  ~ In x (fv t) -> subst_env (upd g x v) t = subst_env g t.
Proof.
  intros g x v t Hx. apply subst_env_agree.
  intros y Hy. unfold upd. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. exfalso. apply Hx. exact Hy.
  - reflexivity.
Qed.

Lemma value_pair_left : forall v1 v2 k, value (tm_pair v1 v2 k) -> value v1.
Proof. intros. inversion H; subst. assumption. Qed.

Lemma value_pair_right : forall v1 v2 k, value (tm_pair v1 v2 k) -> value v2.
Proof. intros. inversion H; subst. assumption. Qed.

Lemma value_inl_payload : forall v k, value (tm_inl v k) -> value v.
Proof. intros. inversion H; subst. assumption. Qed.

Lemma value_inr_payload : forall v k, value (tm_inr v k) -> value v.
Proof. intros. inversion H; subst. assumption. Qed.

Lemma Vp_protect_transfer : forall l T kappa l1 l2 v1 v2,
  flows_to l1 kappa.(indirect_reader) ->
  flows_to l2 kappa.(indirect_reader) ->
  Vp l T (security_of T) v1 v2 ->
  Vp l T (protect_security (security_of T) kappa.(indirect_reader))
       (protect_value v1 l1) (protect_value v2 l2).
Proof.
  intros l T kappa l1 l2 v1 v2 Hf1 Hf2 HV.
  pose proof (Vp_protect2 l T (security_of T) v1 v2 l1 l2 HV) as H2.
  eapply Vp_security_le.
  - apply security_le_protect_join. apply security_le_refl.
    apply (flows_to_join_both l1 l2 kappa.(indirect_reader)); [exact Hf1 | exact Hf2].
  - exact H2.
Qed.

Lemma case_branch_E : forall ell Gamma T1 Tbody L
  (g1 g2 : atom -> tm) (body : tm) (p1 p2 : tm) (k1 k2 : security)
  (kappa : security) (v1 v2 w1 w2 : tm),
  (forall (x : atom), ~ In x L -> forall (ell' : label) (h1 h2 : atom -> tm),
     env_lc h1 -> env_lc h2 ->
     env_rel ell' (update Gamma x T1) h1 h2 ->
     E ell' Tbody (subst_env h1 (open body (tm_fvar x)))
                  (subst_env h2 (open body (tm_fvar x)))) ->
  env_lc g1 -> env_lc g2 -> env_rel ell Gamma g1 g2 ->
  Vp ell T1 (security_of T1) p1 p2 ->
  value p1 -> value p2 ->
  security_le k1 kappa -> security_le k2 kappa ->
  eval (open (subst_env g1 body) p1) w1 ->
  eval (open (subst_env g2 body) p2) w2 ->
  v1 = protect_value w1 k1.(indirect_reader) ->
  v2 = protect_value w2 k2.(indirect_reader) ->
  Vp ell Tbody (protect_security (security_of Tbody) kappa.(indirect_reader)) v1 v2.
Proof.
  intros ell Gamma T1 Tbody L g1 g2 body p1 p2 k1 k2 kappa v1 v2 w1 w2
         IH Hlc1 Hlc2 Henv HV Hv1 Hv2 Hle1 Hle2 Hev1 Hev2 Eq1 Eq2.
  destruct (fresh_atom (L ++ fv body)) as [x Hx].
  assert (HxL : ~ In x L).
  { intro Hc. apply Hx. apply in_app_iff. left. exact Hc. }
  assert (Hxb : ~ In x (fv body)).
  { intro Hc. apply Hx. apply in_app_iff. right. exact Hc. }
  assert (HenvU : env_rel ell (update Gamma x T1) (upd g1 x p1) (upd g2 x p2)).
  { intros y U Hy. unfold update in Hy. simpl in Hy.
    destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. injection Hy as Eq. subst U.
      rewrite upd_same, upd_same.
      apply Vp_E_values; assumption.
    - assert (Hyx : y <> x) by (intro Hc; subst y; rewrite Nat.eqb_refl in E; discriminate).
      rewrite (upd_neq g1 x p1 y Hyx), (upd_neq g2 x p2 y Hyx).
      apply Henv. exact Hy. }
  specialize (IH x HxL ell (upd g1 x p1) (upd g2 x p2)
    (env_lc_upd g1 x p1 Hlc1 (value_lc _ Hv1))
    (env_lc_upd g2 x p2 Hlc2 (value_lc _ Hv2)) HenvU).
  assert (Hs1 : subst_env (upd g1 x p1) (open body (tm_fvar x)) =
                open (subst_env (upd g1 x p1) body) p1).
  { apply subst_env_open.
    - apply env_lc_upd; [exact Hlc1 | apply value_lc; exact Hv1].
    - apply upd_same. }
  assert (Hu1 : subst_env (upd g1 x p1) body = subst_env g1 body).
  { apply subst_env_update_agree. exact Hxb. }
  assert (Hs2 : subst_env (upd g2 x p2) (open body (tm_fvar x)) =
                open (subst_env (upd g2 x p2) body) p2).
  { apply subst_env_open.
    - apply env_lc_upd; [exact Hlc2 | apply value_lc; exact Hv2].
    - apply upd_same. }
  assert (Hu2 : subst_env (upd g2 x p2) body = subst_env g2 body).
  { apply subst_env_update_agree. exact Hxb. }
  rewrite Hs1, Hu1, Hs2, Hu2 in IH.
  pose proof (IH w1 w2 Hev1 Hev2) as HVres.
  rewrite Eq1, Eq2.
  eapply Vp_protect_transfer.
  - apply security_le_ind; exact Hle1.
  - apply security_le_ind; exact Hle2.
  - exact HVres.
Qed.

Lemma if_branch_E : forall ell T kappa (g1 g2 : atom -> tm) (branch1 branch2 : tm)
  (k1 k2 : security) (v1 v2 w1 w2 : tm),
  E ell T (subst_env g1 branch1) (subst_env g2 branch2) ->
  security_le k1 kappa -> security_le k2 kappa ->
  eval (subst_env g1 branch1) w1 -> eval (subst_env g2 branch2) w2 ->
  v1 = protect_value w1 k1.(indirect_reader) ->
  v2 = protect_value w2 k2.(indirect_reader) ->
  Vp ell T (protect_security (security_of T) kappa.(indirect_reader)) v1 v2.
Proof.
  intros ell T kappa g1 g2 branch1 branch2 k1 k2 v1 v2 w1 w2
         IHb Hle1 Hle2 Hev1 Hev2 Eq1 Eq2.
  pose proof (IHb w1 w2 Hev1 Hev2) as HVres.
  rewrite Eq1, Eq2.
  eapply Vp_protect_transfer.
  - apply security_le_ind; exact Hle1.
  - apply security_le_ind; exact Hle2.
  - exact HVres.
Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall ell g1 g2,
    env_lc g1 -> env_lc g2 -> env_rel ell Gamma g1 g2 ->
    E ell T (subst_env g1 t) (subst_env g2 t).
Proof.
  intros Gamma t T H. induction H; intros ell g1 g2 Hlc1 Hlc2 Henv.
  - (* T_Var *) simpl. apply Henv. exact H.
  - (* T_Unit *) simpl. unfold E. intros v1 v2 He1 He2.
    rewrite (eval_unit_inv _ _ He1). rewrite (eval_unit_inv _ _ He2).
    simpl. intro Hvis. exists kappa, kappa.
    split; [reflexivity | split; [reflexivity | split]];
      apply security_le_refl.
  - (* T_Abs *) simpl. unfold E. intros v1 v2 He1 He2.
    rewrite (eval_abs_inv _ _ _ _ He1). rewrite (eval_abs_inv _ _ _ _ He2).
    simpl. intro Hvis.
    exists T1, (subst_env g1 body), kappa, T1, (subst_env g2 body), kappa.
    split; [reflexivity | split; [reflexivity | split]].
    + apply security_le_refl.
    + split.
      * apply security_le_refl.
      * intros r s1 s2 HE u1 u2 Hev1 Hev2.
        destruct (eval_app_inv _ _ _ _ Hev1) as
          [Ta [ba [ka [a2 [HEa [HEb [Hfl Hpr]]]]]]].
        destruct (eval_app_inv _ _ _ _ Hev2) as
          [Tb [bb [kb [b2 [HEa' [HEb' [Hfl' Hpr']]]]]]].
        assert (Eqa : tm_abs Ta ba ka = tm_abs T1 (subst_env g1 body) kappa).
        { apply eval_abs_inv. exact HEa. }
        assert (Eqb : tm_abs Tb bb kb = tm_abs T1 (subst_env g2 body) kappa).
        { apply eval_abs_inv. exact HEa'. }
        inversion Eqa; subst. inversion Eqb; subst.
        destruct (eval_protect_inv _ _ _ Hpr) as [w1 [Hw1 Eqv1]].
        destruct (eval_protect_inv _ _ _ Hpr') as [w2 [Hw2 Eqv2]].
        pose proof (HE a2 b2 HEb HEb') as HVarg.
        assert (Earg : E ell T1 a2 b2).
        { apply Vp_E_values; [exact HVarg | exact (eval_value _ _ HEb)
                             | exact (eval_value _ _ HEb')]. }
        destruct (fresh_atom (L ++ fv body)) as [x Hx].
        assert (HxL : ~ In x L).
        { intro Hc. apply Hx. apply in_app_iff. left. exact Hc. }
        assert (Hxb : ~ In x (fv body)).
        { intro Hc. apply Hx. apply in_app_iff. right. exact Hc. }
        specialize (H2 x HxL ell
          (fun y => if Nat.eqb y x then a2 else g1 y)
          (fun y => if Nat.eqb y x then b2 else g2 y)).
        assert (HenvU : env_rel ell (update Gamma x T1)
                  (upd g1 x a2) (upd g2 x b2)).
        { intros y U Hy. unfold update in Hy. simpl in Hy.
          destruct (Nat.eqb y x) eqn:E.
          - apply Nat.eqb_eq in E. subst y. injection Hy as Eq. subst U.
            rewrite upd_same, upd_same.
            apply Vp_E_values; [exact HVarg | exact (eval_value _ _ HEb)
                                | exact (eval_value _ _ HEb')].
          - assert (Hyx : y <> x) by (intro Hc; subst y; rewrite Nat.eqb_refl in E; discriminate).
            rewrite (upd_neq g1 x a2 y Hyx), (upd_neq g2 x b2 y Hyx).
            apply Henv. exact Hy. }
        specialize (H2 (env_lc_upd g1 x a2 Hlc1 (value_lc _ (eval_value _ _ HEb)))
                       (env_lc_upd g2 x b2 Hlc2 (value_lc _ (eval_value _ _ HEb')))
                       HenvU).
        assert (Hs1 : subst_env (fun y => if Nat.eqb y x then a2 else g1 y)
                      (open body (tm_fvar x)) =
                    open (subst_env (fun y => if Nat.eqb y x then a2 else g1 y)
                            body) a2).
        { apply subst_env_open.
          - apply env_lc_upd; [exact Hlc1 | exact (value_lc _ (eval_value _ _ HEb))].
          - simpl. rewrite Nat.eqb_refl. reflexivity. }
        assert (Hu1 : subst_env (fun y => if Nat.eqb y x then a2 else g1 y) body
                     = subst_env g1 body).
        { apply subst_env_update_agree. exact Hxb. }
        assert (Hs2 : subst_env (fun y => if Nat.eqb y x then b2 else g2 y)
                      (open body (tm_fvar x)) =
                    open (subst_env (fun y => if Nat.eqb y x then b2 else g2 y)
                            body) b2).
        { apply subst_env_open.
          - apply env_lc_upd; [exact Hlc2 | exact (value_lc _ (eval_value _ _ HEb'))].
          - simpl. rewrite Nat.eqb_refl. reflexivity. }
        assert (Hu2 : subst_env (fun y => if Nat.eqb y x then b2 else g2 y) body
                     = subst_env g2 body).
        { apply subst_env_update_agree. exact Hxb. }
        rewrite Hs1, Hu1, Hs2, Hu2 in H2.
        pose proof H2 as Hbody.
        pose proof (Hbody w1 w2 Hw1 Hw2) as HVres.
        pose proof (Vp_protect2 ell T2 (security_of T2) w1 w2
                      kappa.(indirect_reader) kappa.(indirect_reader) HVres) as Hprot.
        rewrite join_idem in Hprot.
        rewrite Eqv1, Eqv2. exact Hprot.
  - (* T_App *) simpl. unfold E. intros v1 v2 He1 He2.
    destruct (eval_app_inv _ _ _ _ He1) as
      [Ta [ba [ka [a2 [HEa [HEb [Hfl Hpr]]]]]]].
    destruct (eval_app_inv _ _ _ _ He2) as
      [Tb [bb [kb [b2 [HEa' [HEb' [Hfl' Hpr']]]]]]].
    pose proof (IHhas_type1 ell g1 g2 Hlc1 Hlc2 Henv _ _ HEa HEa') as HVfun.
    rewrite security_of_ty_protect. rewrite Vp_ty_protect.
    destruct (flowb kappa.(indirect_reader) ell) eqn:Ef.
    + apply flowb_true in Ef.
      destruct (HVfun Ef) as
        [A1 [body1 [k1 [A2 [body2 [k2 [E1 [E2 [B1 [B2 HCl]]]]]]]]]].
      inversion E1; subst. inversion E2; subst.
      eapply HCl.
      * exact (IHhas_type2 ell g1 g2 Hlc1 Hlc2 Henv).
      * eapply ev_app with (v2 := a2).
        -- apply ev_abs. exact (eval_value _ _ HEa).
        -- exact HEb.
        -- exact Hfl.
        -- exact Hpr.
      * eapply ev_app with (v2 := b2).
        -- apply ev_abs. exact (eval_value _ _ HEa').
        -- exact HEb'.
        -- exact Hfl'.
        -- exact Hpr'.
    + apply flowb_false in Ef.
      apply Vp_invisible.
      intro Hc. apply Ef.
      simpl in Hc. apply flows_to_join_l in Hc. exact (proj2 Hc).
  - (* T_Pair *) simpl. unfold E. intros v1 v2 He1 He2.
    destruct (eval_pair_inv _ _ _ _ He1) as [a1 [b1 [Eq1 [Ea1 Eb1]]]].
    destruct (eval_pair_inv _ _ _ _ He2) as [a2 [b2 [Eq2 [Ea2 Eb2]]]].
    subst v1 v2. simpl. intro Hvis.
    exists a1, b1, a2, b2, kappa, kappa.
    split; [reflexivity | split; [reflexivity | split]].
    + apply security_le_refl.
    + split.
      * apply security_le_refl.
      * split.
        -- exact (IHhas_type1 ell g1 g2 Hlc1 Hlc2 Henv _ _ Ea1 Ea2).
        -- exact (IHhas_type2 ell g1 g2 Hlc1 Hlc2 Henv _ _ Eb1 Eb2).
  - (* T_Fst *) simpl. unfold E. intros v1 v2 He1 He2.
    destruct (eval_fst_inv _ _ _ He1) as [a1 [b1 [k1 [Ep1 [Hfl1 Hpr1]]]]].
    destruct (eval_fst_inv _ _ _ He2) as [a2 [b2 [k2 [Ep2 [Hfl2 Hpr2]]]]].
    assert (Hva1 : value a1).
    { apply (value_pair_left a1 b1 k1). exact (eval_value _ _ Ep1). }
    assert (Hva2 : value a2).
    { apply (value_pair_left a2 b2 k2). exact (eval_value _ _ Ep2). }
    pose proof (IHhas_type ell g1 g2 Hlc1 Hlc2 Henv _ _ Ep1 Ep2) as HVprod.
    rewrite security_of_ty_protect. rewrite Vp_ty_protect.
    destruct (flowb kappa.(indirect_reader) ell) eqn:Ef.
    + apply flowb_true in Ef.
      destruct (HVprod Ef) as
        [x1 [y1 [x2 [y2 [kv1 [kv2 [E1 [E2 [B1 [B2 [HP1 HP2]]]]]]]]]]].
      inversion E1; subst. inversion E2; subst.
      destruct (eval_protect_inv _ _ _ Hpr1) as [w1 [Hw1 Eqv1]].
      destruct (eval_protect_inv _ _ _ Hpr2) as [w2 [Hw2 Eqv2]].
      rewrite (eval_value_inv _ _ Hva1 Hw1) in Eqv1.
      rewrite (eval_value_inv _ _ Hva2 Hw2) in Eqv2.
      rewrite Eqv1, Eqv2.
      eapply Vp_protect_transfer.
      * apply security_le_ind. exact B1.
      * apply security_le_ind. exact B2.
      * exact HP1.
    + apply flowb_false in Ef.
      apply Vp_invisible.
      intro Hc. apply Ef.
      simpl in Hc. apply flows_to_join_l in Hc. exact (proj2 Hc).
  - (* T_Snd *) simpl. unfold E. intros v1 v2 He1 He2.
    destruct (eval_snd_inv _ _ _ He1) as [a1 [b1 [k1 [Ep1 [Hfl1 Hpr1]]]]].
    destruct (eval_snd_inv _ _ _ He2) as [a2 [b2 [k2 [Ep2 [Hfl2 Hpr2]]]]].
    assert (Hvb1 : value b1).
    { apply (value_pair_right a1 b1 k1). exact (eval_value _ _ Ep1). }
    assert (Hvb2 : value b2).
    { apply (value_pair_right a2 b2 k2). exact (eval_value _ _ Ep2). }
    pose proof (IHhas_type ell g1 g2 Hlc1 Hlc2 Henv _ _ Ep1 Ep2) as HVprod.
    rewrite security_of_ty_protect. rewrite Vp_ty_protect.
    destruct (flowb kappa.(indirect_reader) ell) eqn:Ef.
    + apply flowb_true in Ef.
      destruct (HVprod Ef) as
        [x1 [y1 [x2 [y2 [kv1 [kv2 [E1 [E2 [B1 [B2 [HP1 HP2]]]]]]]]]]].
      inversion E1; subst. inversion E2; subst.
      destruct (eval_protect_inv _ _ _ Hpr1) as [w1 [Hw1 Eqv1]].
      destruct (eval_protect_inv _ _ _ Hpr2) as [w2 [Hw2 Eqv2]].
      rewrite (eval_value_inv _ _ Hvb1 Hw1) in Eqv1.
      rewrite (eval_value_inv _ _ Hvb2 Hw2) in Eqv2.
      rewrite Eqv1, Eqv2.
      eapply Vp_protect_transfer.
      * apply security_le_ind. exact B1.
      * apply security_le_ind. exact B2.
      * exact HP2.
    + apply flowb_false in Ef.
      apply Vp_invisible.
      intro Hc. apply Ef.
      simpl in Hc. apply flows_to_join_l in Hc. exact (proj2 Hc).
  - (* T_Inl *) simpl. unfold E. intros v1 v2 He1 He2.
    destruct (eval_inl_inv _ _ _ He1) as [w1 [Eq1 Ew1]].
    destruct (eval_inl_inv _ _ _ He2) as [w2 [Eq2 Ew2]].
    subst v1 v2. simpl. intro Hvis.
    left. exists w1, w2, kappa, kappa.
    split; [reflexivity | split; [reflexivity | split]].
    + apply security_le_refl.
    + split.
      * apply security_le_refl.
      * exact (IHhas_type ell g1 g2 Hlc1 Hlc2 Henv _ _ Ew1 Ew2).
  - (* T_Inr *) simpl. unfold E. intros v1 v2 He1 He2.
    destruct (eval_inr_inv _ _ _ He1) as [w1 [Eq1 Ew1]].
    destruct (eval_inr_inv _ _ _ He2) as [w2 [Eq2 Ew2]].
    subst v1 v2. simpl. intro Hvis.
    right. exists w1, w2, kappa, kappa.
    split; [reflexivity | split; [reflexivity | split]].
    + apply security_le_refl.
    + split.
      * apply security_le_refl.
      * exact (IHhas_type ell g1 g2 Hlc1 Hlc2 Henv _ _ Ew1 Ew2).
  - (* T_Case *) simpl. unfold E. intros v1 v2 He1 He2.
    rewrite security_of_ty_protect. rewrite Vp_ty_protect.
    destruct (flowb kappa.(indirect_reader) ell) eqn:Ef.
    + apply flowb_true in Ef.
      destruct (eval_case_inv _ _ _ _ _ He1) as
        [[x1 [kv1 [Ec1 [Hf1 Hp1]]]] | [x1 [kv1 [Ec1 [Hf1 Hp1]]]]].
      * destruct (eval_case_inv _ _ _ _ _ He2) as
          [[x2 [kv2 [Ec2 [Hf2 Hp2]]]] | [x2 [kv2 [Ec2 [Hf2 Hp2]]]]].
        -- (* inl / inl *)
           pose proof (IHhas_type ell g1 g2 Hlc1 Hlc2 Henv _ _ Ec1 Ec2) as HVsum.
           destruct (HVsum Ef) as
             [[sa1 [sa2 [sk1 [sk2 [SE1 [SE2 [SB1 [SB2 SHP]]]]]]]]
             |[sb1 [sb2 [sk1 [sk2 [SE1 [SE2 [SB1 [SB2 SHP]]]]]]]]].
           ++ inversion SE1; subst. inversion SE2; subst.
              destruct (eval_protect_inv _ _ _ Hp1) as [w1 [Hw1 Eqv1]].
              destruct (eval_protect_inv _ _ _ Hp2) as [w2 [Hw2 Eqv2]].
              assert (Hvsa1 : value sa1)
                by (apply (value_inl_payload sa1 sk1); apply (eval_value _ _ Ec1)).
              assert (Hvsa2 : value sa2)
                by (apply (value_inl_payload sa2 sk2); apply (eval_value _ _ Ec2)).
              eapply case_branch_E with (Gamma := Gamma) (T1 := T1) (Tbody := T)
                (L := L) (body := body1) (p1 := sa1) (p2 := sa2)
                (k1 := sk1) (k2 := sk2) (kappa := kappa) (w1 := w1) (w2 := w2).
              ** exact H2.
              ** exact Hlc1.
              ** exact Hlc2.
              ** exact Henv.
              ** exact SHP.
              ** exact Hvsa1.
              ** exact Hvsa2.
              ** exact SB1.
              ** exact SB2.
              ** exact Hw1.
              ** exact Hw2.
              ** exact Eqv1.
              ** exact Eqv2.
           ++ inversion SE1.
        -- (* inl / inr *)
           pose proof (IHhas_type ell g1 g2 Hlc1 Hlc2 Henv _ _ Ec1 Ec2) as HVsum.
           destruct (HVsum Ef) as
             [[sa1 [sa2 [sk1 [sk2 [SE1 [SE2 [SB1 [SB2 SHP]]]]]]]]
             |[sb1 [sb2 [sk1 [sk2 [SE1 [SE2 [SB1 [SB2 SHP]]]]]]]]].
           ++ inversion SE2.
           ++ inversion SE1.
      * destruct (eval_case_inv _ _ _ _ _ He2) as
          [[x2 [kv2 [Ec2 [Hf2 Hp2]]]] | [x2 [kv2 [Ec2 [Hf2 Hp2]]]]].
        -- (* inr / inl *)
           pose proof (IHhas_type ell g1 g2 Hlc1 Hlc2 Henv _ _ Ec1 Ec2) as HVsum.
           destruct (HVsum Ef) as
             [[sa1 [sa2 [sk1 [sk2 [SE1 [SE2 [SB1 [SB2 SHP]]]]]]]]
             |[sb1 [sb2 [sk1 [sk2 [SE1 [SE2 [SB1 [SB2 SHP]]]]]]]]].
           ++ inversion SE1.
           ++ inversion SE2.
        -- (* inr / inr *)
           pose proof (IHhas_type ell g1 g2 Hlc1 Hlc2 Henv _ _ Ec1 Ec2) as HVsum.
           destruct (HVsum Ef) as
             [[sa1 [sa2 [sk1 [sk2 [SE1 [SE2 [SB1 [SB2 SHP]]]]]]]]
             |[sb1 [sb2 [sk1 [sk2 [SE1 [SE2 [SB1 [SB2 SHP]]]]]]]]].
           ++ inversion SE1.
           ++ inversion SE1; subst. inversion SE2; subst.
              destruct (eval_protect_inv _ _ _ Hp1) as [w1 [Hw1 Eqv1]].
              destruct (eval_protect_inv _ _ _ Hp2) as [w2 [Hw2 Eqv2]].
              assert (Hvsb1 : value sb1)
                by (apply (value_inr_payload sb1 sk1); apply (eval_value _ _ Ec1)).
              assert (Hvsb2 : value sb2)
                by (apply (value_inr_payload sb2 sk2); apply (eval_value _ _ Ec2)).
              eapply case_branch_E with (Gamma := Gamma) (T1 := T2) (Tbody := T)
                (L := L) (body := body2) (p1 := sb1) (p2 := sb2)
                (k1 := sk1) (k2 := sk2) (kappa := kappa) (w1 := w1) (w2 := w2).
              ** exact H4.
              ** exact Hlc1.
              ** exact Hlc2.
              ** exact Henv.
              ** exact SHP.
              ** exact Hvsb1.
              ** exact Hvsb2.
              ** exact SB1.
              ** exact SB2.
              ** exact Hw1.
              ** exact Hw2.
              ** exact Eqv1.
              ** exact Eqv2.
    + apply flowb_false in Ef.
      apply Vp_invisible.
      intro Hc. apply Ef.
      simpl in Hc. apply flows_to_join_l in Hc. exact (proj2 Hc).
  - (* T_Protect *) simpl. unfold E. intros v1 v2 He1 He2.
    destruct (eval_protect_inv _ _ _ He1) as [w1 [Hw1 Eqv1]].
    destruct (eval_protect_inv _ _ _ He2) as [w2 [Hw2 Eqv2]].
    pose proof (IHhas_type ell g1 g2 Hlc1 Hlc2 Henv _ _ Hw1 Hw2) as HV.
    rewrite security_of_ty_protect. rewrite Vp_ty_protect.
    rewrite Eqv1, Eqv2.
    pose proof (Vp_protect2 ell T (security_of T) w1 w2 l l HV) as H2.
    rewrite join_idem in H2. exact H2.
  - (* T_Sub *) simpl. unfold E. intros v1 v2 He1 He2.
    pose proof (IHhas_type ell g1 g2 Hlc1 Hlc2 Henv _ _ He1 He2) as HV.
    eapply Vp_sub.
    + exact H0.
    + apply subtype_security_le. exact H0.
    + exact HV.
  - (* T_If *) simpl. unfold E. intros v1 v2 He1 He2.
    rewrite security_of_ty_protect. rewrite Vp_ty_protect.
    destruct (flowb k.(indirect_reader) ell) eqn:Ef.
    + apply flowb_true in Ef.
      destruct (eval_if_inv _ _ _ _ _ He1) as
        [[x1 [kv1 [Ec1 [Hf1 Hp1]]]] | [x1 [kv1 [Ec1 [Hf1 Hp1]]]]].
      * destruct (eval_if_inv _ _ _ _ _ He2) as
          [[x2 [kv2 [Ec2 [Hf2 Hp2]]]] | [x2 [kv2 [Ec2 [Hf2 Hp2]]]]].
        -- (* inl / inl *)
           pose proof (IHhas_type1 ell g1 g2 Hlc1 Hlc2 Henv _ _ Ec1 Ec2) as HVcond.
           destruct (HVcond Ef) as
             [[ca1 [ca2 [ck1 [ck2 [CE1 [CE2 [CB1 [CB2 CHP]]]]]]]]
             |[cb1 [cb2 [ck1 [ck2 [CE1 [CE2 [CB1 [CB2 CHP]]]]]]]]].
           ++ inversion CE1; subst. inversion CE2; subst.
              destruct (eval_protect_inv _ _ _ Hp1) as [w1 [Hw1 Eqv1]].
              destruct (eval_protect_inv _ _ _ Hp2) as [w2 [Hw2 Eqv2]].
              eapply if_branch_E with (T := T) (kappa := k)
                (branch1 := yes) (branch2 := yes)
                (k1 := ck1) (k2 := ck2) (w1 := w1) (w2 := w2).
              ** exact (IHhas_type2 ell g1 g2 Hlc1 Hlc2 Henv).
              ** exact CB1.
              ** exact CB2.
              ** exact Hw1.
              ** exact Hw2.
              ** exact Eqv1.
              ** exact Eqv2.
           ++ inversion CE1.
        -- (* inl / inr *)
           pose proof (IHhas_type1 ell g1 g2 Hlc1 Hlc2 Henv _ _ Ec1 Ec2) as HVcond.
           destruct (HVcond Ef) as
             [[ca1 [ca2 [ck1 [ck2 [CE1 [CE2 [CB1 [CB2 CHP]]]]]]]]
             |[cb1 [cb2 [ck1 [ck2 [CE1 [CE2 [CB1 [CB2 CHP]]]]]]]]].
           ++ inversion CE2.
           ++ inversion CE1.
      * destruct (eval_if_inv _ _ _ _ _ He2) as
          [[x2 [kv2 [Ec2 [Hf2 Hp2]]]] | [x2 [kv2 [Ec2 [Hf2 Hp2]]]]].
        -- (* inr / inl *)
           pose proof (IHhas_type1 ell g1 g2 Hlc1 Hlc2 Henv _ _ Ec1 Ec2) as HVcond.
           destruct (HVcond Ef) as
             [[ca1 [ca2 [ck1 [ck2 [CE1 [CE2 [CB1 [CB2 CHP]]]]]]]]
             |[cb1 [cb2 [ck1 [ck2 [CE1 [CE2 [CB1 [CB2 CHP]]]]]]]]].
           ++ inversion CE1.
           ++ inversion CE2.
        -- (* inr / inr *)
           pose proof (IHhas_type1 ell g1 g2 Hlc1 Hlc2 Henv _ _ Ec1 Ec2) as HVcond.
           destruct (HVcond Ef) as
             [[ca1 [ca2 [ck1 [ck2 [CE1 [CE2 [CB1 [CB2 CHP]]]]]]]]
             |[cb1 [cb2 [ck1 [ck2 [CE1 [CE2 [CB1 [CB2 CHP]]]]]]]]].
           ++ inversion CE1.
           ++ inversion CE1; subst. inversion CE2; subst.
              destruct (eval_protect_inv _ _ _ Hp1) as [w1 [Hw1 Eqv1]].
              destruct (eval_protect_inv _ _ _ Hp2) as [w2 [Hw2 Eqv2]].
              eapply if_branch_E with (T := T) (kappa := k)
                (branch1 := no) (branch2 := no)
                (k1 := ck1) (k2 := ck2) (w1 := w1) (w2 := w2).
              ** exact (IHhas_type3 ell g1 g2 Hlc1 Hlc2 Henv).
              ** exact CB1.
              ** exact CB2.
              ** exact Hw1.
              ** exact Hw2.
              ** exact Eqv1.
              ** exact Eqv2.
    + apply flowb_false in Ef.
      apply Vp_invisible.
      intro Hc. apply Ef.
      simpl in Hc. apply flows_to_join_l in Hc. exact (proj2 Hc).
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 HC Hg Htr Hnf.
  unfold same_result.
  intros v1 v2 Hev1 Hev2.
  destruct (not_flows_to_inv _ _ Hnf) as [HindS HindR].
  destruct HC as [L HC].
  set (x := S (max_list (L ++ fvsC C))).
  assert (Hxf : ~ In x (L ++ fvsC C)).
  { intro Hc. subst x. pose proof (max_list_ge (L ++ fvsC C) _ Hc). lia. }
  assert (HxL : ~ In x L).
  { intro Hc. apply Hxf. apply in_app_iff. left. exact Hc. }
  assert (HxC : ~ In x (fvsC C)).
  { intro Hc. apply Hxf. apply in_app_iff. right. exact Hc. }
  set (g1 := fun y => if Nat.eqb y x then t1 else tm_fvar y).
  set (g2 := fun y => if Nat.eqb y x then t2 else tm_fvar y).
  assert (Hlc1 : env_lc g1).
  { intros y. unfold g1. cbn beta. destruct (Nat.eqb y x).
    - exact (has_type_lc _ _ _ Ht1).
    - unfold locally_closed. simpl. trivial. }
  assert (Hlc2 : env_lc g2).
  { intros y. unfold g2. cbn beta. destruct (Nat.eqb y x).
    - exact (has_type_lc _ _ _ Ht2).
    - unfold locally_closed. simpl. trivial. }
  assert (Henv : env_rel Low (update empty x T_secret) g1 g2).
  { intros y U Hy. unfold update in Hy. simpl in Hy.
    destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. injection Hy as Eq. subst U.
      unfold g1, g2. cbn beta. rewrite Nat.eqb_refl. simpl.
      unfold E. intros u1 u2 _ _.
      apply Vp_invisible. intro Hc. rewrite HindS in Hc. simpl in Hc. exact Hc.
    - simpl in Hy. discriminate Hy. }
  pose proof (fundamental (update empty x T_secret) (plug C (tm_fvar x)) T_result
                (HC x HxL) Low g1 g2 Hlc1 Hlc2 Henv) as HE.
  assert (Hfix1 : forall y, In y (fvsC C) -> g1 y = tm_fvar y).
  { intros y Hy. unfold g1. cbn beta. destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. exfalso. exact (HxC Hy).
    - reflexivity. }
  assert (Hfix2 : forall y, In y (fvsC C) -> g2 y = tm_fvar y).
  { intros y Hy. unfold g2. cbn beta. destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. exfalso. exact (HxC Hy).
    - reflexivity. }
  assert (Hs1 : subst_env g1 (plug C (tm_fvar x)) = plug C t1).
  { rewrite (subst_env_plug C (tm_fvar x) g1 Hfix1).
    simpl. unfold g1. cbn beta. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hs2 : subst_env g2 (plug C (tm_fvar x)) = plug C t2).
  { rewrite (subst_env_plug C (tm_fvar x) g2 Hfix2).
    simpl. unfold g2. cbn beta. rewrite Nat.eqb_refl. reflexivity. }
  rewrite Hs1, Hs2 in HE.
  unfold evaluates in Hev1, Hev2.
  destruct Hev1 as [Hm1 Hval1]. destruct Hev2 as [Hm2 Hval2].
  assert (Hev1' : eval (plug C t1) v1) by (apply multi_eval; assumption).
  assert (Hev2' : eval (plug C t2) v2) by (apply multi_eval; assumption).
  pose proof (HE v1 v2 Hev1' Hev2') as HV.
  apply (Vp_ground_erase T_result Low v1 v2 Hg).
  - apply (transparent_all_ind T_result (security_of T_result) Low Htr).
    rewrite HindR. apply flows_to_refl.
  - exact HV.
Qed.