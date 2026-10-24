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

(* ================= label and security lemmas ================= *)
Lemma flows_to_refl : forall l : label, flows_to l l.
Proof. intros l; destruct l; simpl; auto. Qed.

Lemma flows_to_trans : forall a b c : label,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. intros a b c; destruct a, b, c; simpl; auto. Qed.

Lemma security_le_refl : forall sigma : security, security_le sigma sigma.
Proof. intros [r ir]; simpl; split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall s1 s2 s3 : security,
  security_le s1 s2 -> security_le s2 s3 -> security_le s1 s3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3] [H1 H2] [H3 H4]; simpl in *; split;
  eapply flows_to_trans; eauto.
Qed.

Lemma join_assoc : forall a b c : label, join (join a b) c = join a (join b c).
Proof. intros a b c; destruct a, b, c; reflexivity. Qed.

Lemma join_comm : forall a b : label, join a b = join b a.
Proof. intros a b; destruct a, b; reflexivity. Qed.

Lemma join_idem : forall a : label, join a a = a.
Proof. intros a; destruct a; reflexivity. Qed.

Lemma flows_to_join : forall a b c : label,
  flows_to a c -> flows_to b c -> flows_to (join a b) c.
Proof. intros a b c; destruct a, b, c; simpl; auto. Qed.

Lemma flows_to_join_l : forall a b c : label,
  flows_to (join a b) c -> flows_to a c.
Proof. intros a b c; destruct a, b, c; simpl; auto. Qed.

Lemma flows_to_join_r : forall a b c : label,
  flows_to (join a b) c -> flows_to b c.
Proof. intros a b c; destruct a, b, c; simpl; auto. Qed.

Lemma flows_to_join_join : forall a b c d : label,
  flows_to a c -> flows_to b d -> flows_to (join a b) (join c d).
Proof. intros a b c d; destruct a, b, c, d; simpl; auto. Qed.

Lemma protect_security_le : forall (s1 s2 : security) (a b : label),
  security_le s1 s2 -> flows_to a b ->
  security_le (protect_security s1 a) (protect_security s2 b).
Proof.
  intros [r1 i1] [r2 i2] a b [Hr Hi] Hab.
  unfold protect_security, security_le in *. simpl in *.
  split; eapply flows_to_join_join; eauto.
Qed.

Lemma protect_security_le_label : forall (s : security) (a b : label),
  flows_to a b -> security_le (protect_security s a) (protect_security s b).
Proof.
  intros s a b Hab; apply protect_security_le; [apply security_le_refl | exact Hab].
Qed.

Lemma protect_security_assoc : forall (s : security) (a b : label),
  protect_security (protect_security s a) b = protect_security s (join a b).
Proof.
  intros [r i] a b; destruct r, i, a, b; reflexivity.
Qed.

Lemma protect_security_join_idem : forall (s : security) (a : label),
  protect_security s (join a a) = protect_security s a.
Proof. intros s a; rewrite join_idem; reflexivity. Qed.

(* ================= logical relation ================= *)
Fixpoint V (l : label) (T : ty) (sigma : security) (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_Unit _ =>
      flows_to sigma.(indirect_reader) l ->
      (exists k1 k2 : security, v1 = tm_unit k1 /\ v2 = tm_unit k2)
  | Ty_Sum T1 T2 _ =>
      flows_to sigma.(indirect_reader) l ->
      ( (exists v1' (k1 : security) v2' (k2 : security),
           v1 = tm_inl v1' k1 /\ v2 = tm_inl v2' k2 /\
           security_le k1 sigma /\ security_le k2 sigma /\
           V l T1 (security_of T1) v1' v2')
        \/ (exists v1' (k1 : security) v2' (k2 : security),
           v1 = tm_inr v1' k1 /\ v2 = tm_inr v2' k2 /\
           security_le k1 sigma /\ security_le k2 sigma /\
           V l T2 (security_of T2) v1' v2') )
  | Ty_Prod T1 T2 _ =>
      flows_to sigma.(indirect_reader) l ->
      (exists a1 b1 (k1 : security) a2 b2 (k2 : security),
         v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
         security_le k1 sigma /\ security_le k2 sigma /\
         V l T1 (security_of T1) a1 a2 /\
         V l T2 (security_of T2) b1 b2)
  | Ty_Arrow T1 T2 _ =>
      flows_to sigma.(indirect_reader) l ->
      (exists Ta1 b1 (k1 : security), v1 = tm_abs Ta1 b1 k1 /\ security_le k1 sigma) /\
      (exists Ta2 b2 (k2 : security), v2 = tm_abs Ta2 b2 k2 /\ security_le k2 sigma) /\
      (forall a1 a2 : tm,
         (forall w1 w2 : tm, multi a1 w1 -> multi a2 w2 ->
            value w1 -> value w2 -> V l T1 (security_of T1) w1 w2) ->
         forall r : label,
         flows_to sigma.(reader) r ->
         forall w1 w2 : tm,
           multi (tm_app v1 a1 r) w1 ->
           multi (tm_app v2 a2 r) w2 ->
           value w1 -> value w2 ->
           V l T2 (protect_security (security_of T2) sigma.(indirect_reader)) w1 w2)
  end.

Definition E (l : label) (T : ty) (sigma : security) (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm,
    multi t1 v1 -> multi t2 v2 -> value v1 -> value v2 -> V l T sigma v1 v2.

Lemma V_opaque : forall (l : label) (T : ty) (sigma : security) (v1 v2 : tm),
  ~ flows_to sigma.(indirect_reader) l -> V l T sigma v1 v2.
Proof.
  intros l T; destruct T; intros sigma v1 v2 H; simpl; intros Hf; exfalso; apply H; exact Hf.
Qed.

Lemma V_ty_protect : forall (l : label) (T : ty) (sigma : security) (l0 : label) (v1 v2 : tm),
  V l (ty_protect l0 T) sigma v1 v2 <-> V l T sigma v1 v2.
Proof. intros; destruct T; simpl; reflexivity. Qed.

Lemma E_ty_protect : forall (l : label) (T : ty) (sigma : security) (l0 : label) (t1 t2 : tm),
  E l (ty_protect l0 T) sigma t1 t2 <-> E l T sigma t1 t2.
Proof.
  intros; unfold E; split; intros H v1 v2 Hm1 Hm2 Hv1 Hv2;
  [apply (proj1 (V_ty_protect l T sigma l0 v1 v2)) | apply (proj2 (V_ty_protect l T sigma l0 v1 v2))];
  apply H; assumption.
Qed.

(* ================= monotonicity in the security parameter ================= *)
Lemma V_mono : forall (T : ty) (l : label) (sigma sigma' : security) (v1 v2 : tm),
  security_le sigma sigma' -> V l T sigma v1 v2 -> V l T sigma' v1 v2.
Proof.
  induction T; intros l sigma sigma' v1 v2 Hle HV; simpl in HV |- *.
  - (* unit *) intros Hf. apply HV. destruct Hle as [Hr Hi].
    exact (flows_to_trans _ _ _ Hi Hf).
  - (* sum *) intros Hf. destruct Hle as [Hr Hi].
    assert (Hle' : security_le sigma sigma') by (split; assumption).
    destruct (HV (flows_to_trans _ _ _ Hi Hf)) as [Hleft | Hright].
    + destruct Hleft as (v1' & k1 & v2' & k2 & E1 & E2 & L1 & L2 & HV1).
      left. exists v1', k1, v2', k2.
      split; [exact E1 | split; [exact E2 | split;
        [apply security_le_trans with (s2 := sigma); assumption |
         split; [apply security_le_trans with (s2 := sigma); assumption | exact HV1]]]].
    + destruct Hright as (v1' & k1 & v2' & k2 & E1 & E2 & L1 & L2 & HV1).
      right. exists v1', k1, v2', k2.
      split; [exact E1 | split; [exact E2 | split;
        [apply security_le_trans with (s2 := sigma); assumption |
         split; [apply security_le_trans with (s2 := sigma); assumption | exact HV1]]]].
  - (* prod *) intros Hf. destruct Hle as [Hr Hi].
    assert (Hle' : security_le sigma sigma') by (split; assumption).
    destruct (HV (flows_to_trans _ _ _ Hi Hf)) as
      (a1 & b1 & k1 & a2 & b2 & k2 & E1 & E2 & L1 & L2 & HV1 & HV2).
    exists a1, b1, k1, a2, b2, k2.
    split; [exact E1 | split; [exact E2 | split;
      [apply security_le_trans with (s2 := sigma); assumption |
       split; [apply security_le_trans with (s2 := sigma); assumption |
       split; [exact HV1 | exact HV2]]]]].
  - (* arrow *) intros Hf. destruct Hle as [Hr Hi].
    assert (Hle' : security_le sigma sigma') by (split; assumption).
    destruct (HV (flows_to_trans _ _ _ Hi Hf)) as [Habs1 [Habs2 Hbody]].
    split.
    + destruct Habs1 as (Ta1 & b1 & k1 & E1 & L1).
      exists Ta1, b1, k1. split; auto.
      apply security_le_trans with (s2 := sigma); assumption.
    + split.
      * destruct Habs2 as (Ta2 & b2 & k2 & E2 & L2).
        exists Ta2, b2, k2. split; auto.
        apply security_le_trans with (s2 := sigma); assumption.
      * intros a1 a2 Ha r Hflow w1 w2 Hm1 Hm2 Hv1 Hv2.
        apply IHT2 with (sigma := protect_security (security_of T2) sigma.(indirect_reader)).
        { apply protect_security_le; [apply security_le_refl | exact Hi]. }
        { eapply Hbody with (a1 := a1) (a2 := a2) (r := r).
          - exact Ha.
          - exact (flows_to_trans _ _ _ Hr Hflow).
          - exact Hm1. - exact Hm2. - exact Hv1. - exact Hv2. }
Qed.

(* ================= subtyping ================= *)
Lemma subtype_security_le : forall (T U : ty),
  subtype T U -> security_le (security_of T) (security_of U).
Proof.
  intros T U Hsub. induction Hsub; simpl; eauto using security_le_trans.
Qed.

Lemma V_sub : forall (T U : ty), subtype T U ->
  forall (l : label) (sigma sigma' : security) (v1 v2 : tm),
    security_le sigma sigma' -> V l T sigma v1 v2 -> V l U sigma' v1 v2.
Proof.
  intros T U Hsub. induction Hsub;
  intros l sigma sigma' v1 v2 Hle HV; simpl in HV |- *.
  - (* S_Unit *) intros Hf. destruct Hle as [Hr Hi].
    apply HV. exact (flows_to_trans _ _ _ Hi Hf).
  - (* S_Sum *) intros Hf. destruct Hle as [Hr Hi].
    assert (Hle' : security_le sigma sigma') by (split; assumption).
    destruct (HV (flows_to_trans _ _ _ Hi Hf)) as [Hleft | Hright].
    + destruct Hleft as (v1' & k1 & v2' & k2 & E1 & E2 & L1 & L2 & HV1).
      left. exists v1', k1, v2', k2.
      split; [exact E1 | split; [exact E2 | split;
        [apply security_le_trans with (s2 := sigma); assumption |
         split; [apply security_le_trans with (s2 := sigma); assumption |
         apply IHHsub1 with (sigma := security_of T1) (sigma' := security_of U1);
           [apply subtype_security_le; assumption | exact HV1]]]]].
    + destruct Hright as (v1' & k1 & v2' & k2 & E1 & E2 & L1 & L2 & HV1).
      right. exists v1', k1, v2', k2.
      split; [exact E1 | split; [exact E2 | split;
        [apply security_le_trans with (s2 := sigma); assumption |
         split; [apply security_le_trans with (s2 := sigma); assumption |
         apply IHHsub2 with (sigma := security_of T2) (sigma' := security_of U2);
           [apply subtype_security_le; assumption | exact HV1]]]]].
  - (* S_Prod *) intros Hf. destruct Hle as [Hr Hi].
    assert (Hle' : security_le sigma sigma') by (split; assumption).
    destruct (HV (flows_to_trans _ _ _ Hi Hf)) as
      (a1 & b1 & k1 & a2 & b2 & k2 & E1 & E2 & L1 & L2 & HV1 & HV2).
    exists a1, b1, k1, a2, b2, k2.
    split; [exact E1 | split; [exact E2 | split;
      [apply security_le_trans with (s2 := sigma); assumption |
       split; [apply security_le_trans with (s2 := sigma); assumption | split;
       [apply IHHsub1 with (sigma := security_of T1) (sigma' := security_of U1);
          [apply subtype_security_le; assumption | exact HV1] |
        apply IHHsub2 with (sigma := security_of T2) (sigma' := security_of U2);
          [apply subtype_security_le; assumption | exact HV2]]]]]].
  - (* S_Arrow *) intros Hf. destruct Hle as [Hr Hi].
    assert (Hle' : security_le sigma sigma') by (split; assumption).
    destruct (HV (flows_to_trans _ _ _ Hi Hf)) as [Habs1 [Habs2 Hbody]].
    split.
    + destruct Habs1 as (Ta1 & b1 & k1 & E1 & L1).
      exists Ta1, b1, k1. split; auto.
      apply security_le_trans with (s2 := sigma); assumption.
    + split.
      * destruct Habs2 as (Ta2 & b2 & k2 & E2 & L2).
        exists Ta2, b2, k2. split; auto.
        apply security_le_trans with (s2 := sigma); assumption.
      * intros a1 a2 Ha r Hflow w1 w2 Hm1 Hm2 Hv1 Hv2.
        assert (Ha' : forall w1 w2 : tm, multi a1 w1 -> multi a2 w2 ->
                        value w1 -> value w2 -> V l T1 (security_of T1) w1 w2).
        { intros. apply IHHsub1 with (sigma := security_of U1) (sigma' := security_of T1).
          - apply subtype_security_le; assumption.
          - apply Ha; assumption. }
        assert (Hres : V l T2 (protect_security (security_of T2) sigma.(indirect_reader)) w1 w2).
        { eapply Hbody with (a1 := a1) (a2 := a2) (r := r).
          - exact Ha'.
          - exact (flows_to_trans _ _ _ Hr Hflow).
          - exact Hm1. - exact Hm2. - exact Hv1. - exact Hv2. }
        apply IHHsub2 with (sigma := protect_security (security_of T2) sigma.(indirect_reader))
                            (sigma' := protect_security (security_of U2) sigma'.(indirect_reader)).
        { apply protect_security_le; [apply subtype_security_le; assumption | exact Hi]. }
        { exact Hres. }
  - (* S_Trans *)
    apply IHHsub2 with (sigma := sigma') (sigma' := sigma').
    + apply security_le_refl.
    + apply IHHsub1 with (sigma := sigma) (sigma' := sigma'); assumption.
Qed.

(* ================= basic term lemmas ================= *)
Lemma abs_no_step : forall (T : ty) (b : tm) (k : security) (t : tm),
  ~ step (tm_abs T b k) t.
Proof. intros; intro H; inversion H. Qed.

Lemma unit_no_step : forall (k : security) (t : tm), ~ step (tm_unit k) t.
Proof. intros; intro H; inversion H. Qed.

Lemma app_not_value : forall f a r, ~ value (tm_app f a r).
Proof. intros; intro H; inversion H. Qed.

Lemma case_not_value : forall t b1 b2 r, ~ value (tm_case t b1 b2 r).
Proof. intros; intro H; inversion H. Qed.

Lemma if_not_value : forall c y n r, ~ value (tm_if c y n r).
Proof. intros; intro H; inversion H. Qed.

Lemma fst_not_value : forall t r, ~ value (tm_fst t r).
Proof. intros; intro H; inversion H. Qed.

Lemma snd_not_value : forall t r, ~ value (tm_snd t r).
Proof. intros; intro H; inversion H. Qed.

Lemma protect_not_value : forall l t, ~ value (tm_protect l t).
Proof. intros; intro H; inversion H. Qed.

Lemma bvar_not_value : forall i, ~ value (tm_bvar i).
Proof. intros; intro H; inversion H. Qed.

Lemma fvar_not_value : forall x, ~ value (tm_fvar x).
Proof. intros; intro H; inversion H. Qed.

Lemma value_no_step : forall t t', step t t' -> value t -> False.
Proof.
  intros t t' Hst. induction Hst; intros Hv; try (inversion Hv);
  try match goal with
      | IH : ?P -> False, H : ?P |- False => exact (IH H)
      end.
Qed.

Lemma multi_step_inv : forall (t1 t3 : tm),
  multi t1 t3 -> t1 = t3 \/ exists t2, step t1 t2 /\ multi t2 t3.
Proof.
  intros t1 t3 Hm. destruct Hm.
  - left; reflexivity.
  - right. exists t2. split; assumption.
Qed.

Lemma multi_value_inv : forall t v, multi t v -> value t -> value v -> v = t.
Proof.
  intros t v Hm Hvt Hvv.
  destruct (multi_step_inv _ _ Hm) as [Heq | [t2 [Hstep _]]].
  - symmetry; exact Heq.
  - exfalso; exact (value_no_step _ _ Hstep Hvt).
Qed.

Lemma multi_abs_inv : forall (T : ty) (b : tm) (k : security) (v : tm),
  multi (tm_abs T b k) v -> v = tm_abs T b k.
Proof.
  intros T b k v Hm.
  destruct (multi_step_inv _ _ Hm) as [Heq | [t2 [Hstep _]]].
  - symmetry; exact Heq.
  - exfalso; exact (abs_no_step _ _ _ _ Hstep).
Qed.

Lemma multi_unit_inv : forall (k : security) (v : tm),
  multi (tm_unit k) v -> v = tm_unit k.
Proof.
  intros k v Hm.
  destruct (multi_step_inv _ _ Hm) as [Heq | [t2 [Hstep _]]].
  - symmetry; exact Heq.
  - exfalso; exact (unit_no_step _ _ Hstep).
Qed.

Lemma value_protect_value : forall (v : tm) (l : label),
  value v -> value (protect_value v l).
Proof.
  intros v l Hv. induction Hv; simpl.
  - constructor.
  - apply v_abs. unfold locally_closed in *. simpl in *. exact H.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma value_protect_value_inv : forall (v : tm) (l : label),
  value (protect_value v l) -> value v.
Proof.
  intros v l H; destruct v; simpl in *.
  - exact H.
  - exact H.
  - constructor.
  - inversion H; subst. apply v_abs. unfold locally_closed in *. simpl in *. assumption.
  - exact H.
  - inversion H; subst. constructor; assumption.
  - exact H.
  - exact H.
  - inversion H; subst. constructor; assumption.
  - inversion H; subst. constructor; assumption.
  - exact H.
  - exact H.
  - exact H.
Qed.

Lemma value_abs_ann : forall (T : ty) (b : tm) (k1 k2 : security),
  value (tm_abs T b k1) -> value (tm_abs T b k2).
Proof. intros. inversion H; subst. apply v_abs. assumption. Qed.

Lemma protect_value_protect : forall (v : tm) (a b : label),
  protect_value (protect_value v a) b = protect_value v (join a b).
Proof.
  intros v a b; destruct v; simpl; try reflexivity;
  rewrite protect_security_assoc; reflexivity.
Qed.

(* ================= evaluation factorizations ================= *)
Lemma multi_app_inv : forall (f a : tm) (r : label) (v : tm),
  multi (tm_app f a r) v -> value v ->
  exists (T : ty) (body va : tm) (k : security),
    multi f (tm_abs T body k) /\ value (tm_abs T body k) /\
    multi a va /\ value va /\ flows_to k.(reader) r /\
    multi (tm_protect k.(indirect_reader) (open body va)) v.
Proof.
  intros f a r v Hm. remember (tm_app f a r) as t eqn:Et.
  revert f a r Et. induction Hm; intros f a r Et Hv.
  - subst t. exfalso. exact (app_not_value f a r Hv).
  - subst t1. inversion H; subst.
    + (* ST_AppAbs *) eexists T, body, a, kappa. repeat split; eauto using multi_refl.
    + (* ST_App1 *)
      destruct (IHHm t1' a r eq_refl Hv) as
        (T & body & va & k & Hf & Hvf & Ha & Hva & Hfl & Hmres).
      eexists T, body, va, k. repeat split; eauto using multi_step.
    + (* ST_App2 *)
      destruct (IHHm f t2' r eq_refl Hv) as
        (T & body & va & k & Hf & Hvf & Ha & Hva & Hfl & Hmres).
      eexists T, body, va, k. repeat split; eauto using multi_step.
Qed.

Lemma multi_trans : forall (t1 t2 t3 : tm),
  multi t1 t2 -> multi t2 t3 -> multi t1 t3.
Proof.
  intros t1 t2 t3 H12 H23. induction H12 in t3, H23 |- *.
  - exact H23.
  - eapply multi_step; eauto.
Qed.

Lemma multi_case_inv : forall (t b1 b2 : tm) (r : label) (v : tm),
  multi (tm_case t b1 b2 r) v -> value v ->
  exists vt,
    multi t vt /\ value vt /\
    ( (exists (u : tm) (k : security),
         vt = tm_inl u k /\ value u /\ flows_to k.(reader) r /\
         multi (tm_protect k.(indirect_reader) (open b1 u)) v)
      \/ (exists (u : tm) (k : security),
         vt = tm_inr u k /\ value u /\ flows_to k.(reader) r /\
         multi (tm_protect k.(indirect_reader) (open b2 u)) v) ).
Proof.
  intros t b1 b2 r v Hm. remember (tm_case t b1 b2 r) as s eqn:Es.
  revert t b1 b2 r Es. induction Hm; intros tt bb1 bb2 rr Eeq Hval.
  - subst t. exfalso. exact (case_not_value tt bb1 bb2 rr Hval).
  - subst t1. inversion H; subst.
    + (* ST_CaseLeft *)
      eexists (tm_inl v kappa). split.
      { apply multi_refl. }
      split.
      { apply v_inl. assumption. }
      left. exists v, kappa. repeat split; eauto using multi_refl.
    + (* ST_CaseRight *)
      eexists (tm_inr v kappa). split.
      { apply multi_refl. }
      split.
      { apply v_inr. assumption. }
      right. exists v, kappa. repeat split; eauto using multi_refl.
    + (* ST_Case *)
      destruct (IHHm _ _ _ _ eq_refl Hval) as (vt & Hmt & Hvt & Hdisj).
      exists vt. split.
      { eapply multi_step; eauto. }
      split; assumption.
Qed.

Lemma multi_if_inv : forall (c yes no : tm) (r : label) (v : tm),
  multi (tm_if c yes no r) v -> value v ->
  exists vc,
    multi c vc /\ value vc /\
    ( (exists (u : tm) (k : security),
         vc = tm_inl u k /\ value u /\ flows_to k.(reader) r /\
         multi (tm_protect k.(indirect_reader) yes) v)
      \/ (exists (u : tm) (k : security),
         vc = tm_inr u k /\ value u /\ flows_to k.(reader) r /\
         multi (tm_protect k.(indirect_reader) no) v) ).
Proof.
  intros c yes no r v Hm. remember (tm_if c yes no r) as s eqn:Es.
  revert c yes no r Es. induction Hm; intros cc yy nn rr Eeq Hval.
  - subst t. exfalso. exact (if_not_value cc yy nn rr Hval).
  - subst t1. inversion H; subst.
    + (* ST_If *)
      destruct (IHHm _ _ _ _ eq_refl Hval) as (vc & Hmc & Hvc & Hdisj).
      exists vc. split.
      { eapply multi_step; eauto. }
      split; assumption.
    + (* ST_IfTrue *)
      eexists (tm_inl v k). split.
      { apply multi_refl. }
      split.
      { apply v_inl. assumption. }
      left. exists v, k. repeat split; eauto using multi_refl.
    + (* ST_IfFalse *)
      eexists (tm_inr v k). split.
      { apply multi_refl. }
      split.
      { apply v_inr. assumption. }
      right. exists v, k. repeat split; eauto using multi_refl.
Qed.

Lemma multi_fst_inv : forall (t : tm) (r : label) (v : tm),
  multi (tm_fst t r) v -> value v ->
  exists vp,
    multi t vp /\ value vp /\
    exists (v1 v2 : tm) (k : security),
      vp = tm_pair v1 v2 k /\ value v1 /\ value v2 /\
      flows_to k.(reader) r /\
      multi (tm_protect k.(indirect_reader) v1) v.
Proof.
  intros t r v Hm. remember (tm_fst t r) as s eqn:Es.
  revert t r Es. induction Hm; intros tt rr Eeq Hval.
  - subst t. exfalso. exact (fst_not_value tt rr Hval).
  - subst t1. inversion H; subst.
    + (* ST_FstPair *)
      eexists (tm_pair v1 v2 kappa). split.
      { apply multi_refl. }
      split.
      { apply v_pair; assumption. }
      eexists v1, v2, kappa. repeat split; eauto using multi_refl.
    + (* ST_Fst *)
      destruct (IHHm _ _ eq_refl Hval) as (vp & Hmt & Hvp & Hrest).
      exists vp. split.
      { eapply multi_step; eauto. }
      split; assumption.
Qed.

Lemma multi_snd_inv : forall (t : tm) (r : label) (v : tm),
  multi (tm_snd t r) v -> value v ->
  exists vp,
    multi t vp /\ value vp /\
    exists (v1 v2 : tm) (k : security),
      vp = tm_pair v1 v2 k /\ value v1 /\ value v2 /\
      flows_to k.(reader) r /\
      multi (tm_protect k.(indirect_reader) v2) v.
Proof.
  intros t r v Hm. remember (tm_snd t r) as s eqn:Es.
  revert t r Es. induction Hm; intros tt rr Eeq Hval.
  - subst t. exfalso. exact (snd_not_value tt rr Hval).
  - subst t1. inversion H; subst.
    + (* ST_SndPair *)
      eexists (tm_pair v1 v2 kappa). split.
      { apply multi_refl. }
      split.
      { apply v_pair; assumption. }
      eexists v1, v2, kappa. repeat split; eauto using multi_refl.
    + (* ST_Snd *)
      destruct (IHHm _ _ eq_refl Hval) as (vp & Hmt & Hvp & Hrest).
      exists vp. split.
      { eapply multi_step; eauto. }
      split; assumption.
Qed.

Lemma multi_pair_inv : forall (a b : tm) (k : security) (v : tm),
  multi (tm_pair a b k) v -> value v ->
  exists va vb, multi a va /\ value va /\ multi b vb /\ value vb /\
                v = tm_pair va vb k.
Proof.
  intros a b k v Hm. remember (tm_pair a b k) as s eqn:Es.
  revert a b k Es. induction Hm; intros aa bb kk Eeq Hval.
  - subst t. inversion Hval; subst. exists aa, bb. repeat split; eauto using multi_refl.
  - subst t1. inversion H; subst.
    + (* ST_Pair1 *)
      destruct (IHHm _ _ _ eq_refl Hval) as (va & vb & Ha & Hva & Hb & Hvb & Heq).
      exists va, vb. repeat split; eauto using multi_step.
    + (* ST_Pair2 *)
      destruct (IHHm _ _ _ eq_refl Hval) as (va & vb & Ha & Hva & Hb & Hvb & Heq).
      exists va, vb. repeat split; eauto using multi_step.
Qed.

Lemma multi_inl_inv : forall (t : tm) (k : security) (v : tm),
  multi (tm_inl t k) v -> value v ->
  exists vt, multi t vt /\ value vt /\ v = tm_inl vt k.
Proof.
  intros t k v Hm. remember (tm_inl t k) as s eqn:Es.
  revert t k Es. induction Hm; intros tt kk Eeq Hval.
  - subst t. inversion Hval; subst. exists tt. repeat split; eauto using multi_refl.
  - subst t1. inversion H; subst.
    destruct (IHHm _ _ eq_refl Hval) as (vt & Hmt & Hvt & Heq).
    exists vt. repeat split; eauto using multi_step.
Qed.

Lemma multi_inr_inv : forall (t : tm) (k : security) (v : tm),
  multi (tm_inr t k) v -> value v ->
  exists vt, multi t vt /\ value vt /\ v = tm_inr vt k.
Proof.
  intros t k v Hm. remember (tm_inr t k) as s eqn:Es.
  revert t k Es. induction Hm; intros tt kk Eeq Hval.
  - subst t. inversion Hval; subst. exists tt. repeat split; eauto using multi_refl.
  - subst t1. inversion H; subst.
    destruct (IHHm _ _ eq_refl Hval) as (vt & Hmt & Hvt & Heq).
    exists vt. repeat split; eauto using multi_step.
Qed.

Lemma multi_protect_result : forall (l : label) (t v : tm),
  multi t v -> value v -> multi (tm_protect l t) (protect_value v l).
Proof.
  intros l t v Hm. induction Hm; intros Hv.
  - eapply multi_step.
    + apply ST_ProtectValue. exact Hv.
    + apply multi_refl.
  - eapply multi_trans with (t2 := tm_protect l t2).
    + eapply multi_step.
      * apply ST_Protect. exact H.
      * apply multi_refl.
    + apply IHHm. exact Hv.
Qed.

Lemma multi_protect_inv : forall (l : label) (t v : tm),
  multi (tm_protect l t) v -> value v ->
  exists w, multi t w /\ value w /\ v = protect_value w l.
Proof.
  intros l t v Hm. remember (tm_protect l t) as s eqn:Es.
  revert t Es. induction Hm; intros tt Eeq Hval.
  - subst t. exfalso. exact (protect_not_value l tt Hval).
  - subst t1. inversion H; subst.
    + (* ST_ProtectValue *)
      eexists tt. split.
      { apply multi_refl. }
      split.
      { exact H3. }
      apply (multi_value_inv (protect_value tt l) t3 Hm).
      { apply value_protect_value. exact H3. }
      { exact Hval. }
    + (* ST_Protect *)
      destruct (IHHm _ eq_refl Hval) as (w & Hmw & Hvw & Heq).
      exists w. split.
      { eapply multi_step; eauto. }
      split; assumption.
Qed.

(* ================= protection value lemma ================= *)
Lemma flows_to_join_left : forall a b : label, flows_to a (join a b).
Proof. intros a b; destruct a, b; simpl; auto. Qed.

Lemma flows_to_join_right : forall a b : label, flows_to b (join a b).
Proof. intros a b; destruct a, b; simpl; auto. Qed.

Lemma protect_security_reader : forall (s : security) (a : label),
  (protect_security s a).(reader) = join s.(reader) a.
Proof. intros; unfold protect_security; reflexivity. Qed.

Lemma protect_security_ir : forall (s : security) (a : label),
  (protect_security s a).(indirect_reader) = join s.(indirect_reader) a.
Proof. intros; unfold protect_security; reflexivity. Qed.

Lemma multi_app_arg : forall (f a a' : tm) (r : label),
  value f -> multi a a' -> multi (tm_app f a r) (tm_app f a' r).
Proof.
  intros f a a' r Hvf Hm. induction Hm.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; [exact Hvf | exact H].
    + exact IHHm.
Qed.

Lemma E_of_V_values : forall (l : label) (T : ty) (sigma : security) (v1 v2 : tm),
  value v1 -> value v2 -> V l T sigma v1 v2 -> E l T sigma v1 v2.
Proof.
  intros l T sigma v1 v2 Hv1 Hv2 HV. unfold E.
  intros w1 w2 Hm1 Hm2 Hw1 Hw2.
  assert (w1 = v1) by (eapply multi_value_inv; eauto).
  assert (w2 = v2) by (eapply multi_value_inv; eauto).
  subst w1; subst w2. exact HV.
Qed.

Lemma V_protect : forall (T : ty) (l : label) (sigma : security) (a1 a2 : label) (v1 v2 : tm),
  V l T sigma v1 v2 ->
  V l T (protect_security sigma (join a1 a2))
        (protect_value v1 a1) (protect_value v2 a2).
Proof.
  induction T; intros l sigma a1 a2 v1 v2 HV; simpl in HV |- *.
  - (* unit *) intros Hf.
    destruct (HV (flows_to_join_l _ _ _ Hf)) as (k1 & k2 & E1 & E2).
    subst v1; subst v2.
    exists (protect_security k1 a1), (protect_security k2 a2).
    simpl; split; reflexivity.
  - (* sum *) intros Hf.
    destruct (HV (flows_to_join_l _ _ _ Hf)) as [Hleft | Hright].
    + destruct Hleft as (v1' & k1 & v2' & k2 & E1 & E2 & L1 & L2 & HV1).
      left. exists v1', (protect_security k1 a1), v2', (protect_security k2 a2).
      split; [simpl; rewrite E1; reflexivity | split; [simpl; rewrite E2; reflexivity | split]].
      * apply protect_security_le; [exact L1 | apply flows_to_join_left].
      * split.
        { apply protect_security_le; [exact L2 | apply flows_to_join_right]. }
        { exact HV1. }
    + destruct Hright as (v1' & k1 & v2' & k2 & E1 & E2 & L1 & L2 & HV1).
      right. exists v1', (protect_security k1 a1), v2', (protect_security k2 a2).
      split; [simpl; rewrite E1; reflexivity | split; [simpl; rewrite E2; reflexivity | split]].
      * apply protect_security_le; [exact L1 | apply flows_to_join_left].
      * split.
        { apply protect_security_le; [exact L2 | apply flows_to_join_right]. }
        { exact HV1. }
  - (* prod *) intros Hf.
    destruct (HV (flows_to_join_l _ _ _ Hf)) as (a1' & b1' & k1 & a2' & b2' & k2 & E1 & E2 & L1 & L2 & HV1 & HV2).
    exists a1', b1', (protect_security k1 a1), a2', b2', (protect_security k2 a2).
    split; [simpl; rewrite E1; reflexivity | split; [simpl; rewrite E2; reflexivity | split]].
    + apply protect_security_le; [exact L1 | apply flows_to_join_left].
    + split.
      * apply protect_security_le; [exact L2 | apply flows_to_join_right].
      * split; assumption.
  - (* arrow *) intros Hf.
    assert (Hfs : flows_to sigma.(indirect_reader) l) by exact (flows_to_join_l _ _ _ Hf).
    destruct (HV Hfs) as [Habs1 [Habs2 Hbody]].
    destruct Habs1 as (Ta1 & b1 & k1 & E1 & L1). subst v1.
    destruct Habs2 as (Ta2 & b2 & k2 & E2 & L2). subst v2.
    split.
    + exists Ta1, b1, (protect_security k1 a1). split; [reflexivity |].
      apply protect_security_le; [exact L1 | apply flows_to_join_left].
    + split.
      * exists Ta2, b2, (protect_security k2 a2). split; [reflexivity |].
        apply protect_security_le; [exact L2 | apply flows_to_join_right].
      * intros u1 u2 Hu r Hflow w1 w2 Hm1 Hm2 Hw1 Hw2.
        assert (Hflow_s : flows_to sigma.(reader) r) by exact (flows_to_join_l _ _ _ Hflow).
        (* factorize target applications *)
        destruct (multi_app_inv _ _ _ _ Hm1 Hw1) as
          (T1x & bodyx & va1 & kx & Hf1 & Hvf1 & Hu1 & Hva1 & Hfl1 & Hres1).
        simpl in Hf1.
        assert (Hf1eq : tm_abs T1x bodyx kx = tm_abs Ta1 b1 (protect_security k1 a1))
          by (apply (multi_abs_inv _ _ _ _ Hf1)).
        inversion Hf1eq; subst.
        destruct (multi_protect_inv _ _ _ Hres1 Hw1) as (y1 & Hy1 & Hvy1 & Hw1eq).
        destruct (multi_app_inv _ _ _ _ Hm2 Hw2) as
          (T2x & bodyx2 & va2 & kx2 & Hf2 & Hvf2 & Hu2 & Hva2 & Hfl2 & Hres2).
        simpl in Hf2.
        assert (Hf2eq : tm_abs T2x bodyx2 kx2 = tm_abs Ta2 b2 (protect_security k2 a2))
          by (apply (multi_abs_inv _ _ _ _ Hf2)).
        inversion Hf2eq; subst.
        destruct (multi_protect_inv _ _ _ Hres2 Hw2) as (y2 & Hy2 & Hvy2 & Hw2eq).
        (* source abs values *)
        assert (Hvabs1 : value (tm_abs Ta1 b1 k1)).
        { apply value_protect_value_inv with (l := a1). simpl. exact Hvf1. }
        assert (Hvabs2 : value (tm_abs Ta2 b2 k2)).
        { apply value_protect_value_inv with (l := a2). simpl. exact Hvf2. }
        (* source multi evaluations *)
        assert (Hfl1s : flows_to k1.(reader) r).
        { apply flows_to_join_l with (a := k1.(reader)) (b := a1). exact Hfl1. }
        assert (Hfl2s : flows_to k2.(reader) r).
        { apply flows_to_join_l with (a := k2.(reader)) (b := a2). exact Hfl2. }
        assert (Hsrc1 : multi (tm_app (tm_abs Ta1 b1 k1) u1 r) (protect_value y1 k1.(indirect_reader))).
        { eapply multi_trans with (t2 := tm_app (tm_abs Ta1 b1 k1) va1 r).
          - apply multi_app_arg; assumption.
          - eapply multi_trans with (t2 := tm_protect k1.(indirect_reader) (open b1 va1)).
            + eapply multi_step.
              * apply ST_AppAbs; assumption.
              * apply multi_refl.
            + apply multi_protect_result; assumption. }
        assert (Hsrc2 : multi (tm_app (tm_abs Ta2 b2 k2) u2 r) (protect_value y2 k2.(indirect_reader))).
        { eapply multi_trans with (t2 := tm_app (tm_abs Ta2 b2 k2) va2 r).
          - apply multi_app_arg; assumption.
          - eapply multi_trans with (t2 := tm_protect k2.(indirect_reader) (open b2 va2)).
            + eapply multi_step.
              * apply ST_AppAbs; assumption.
              * apply multi_refl.
            + apply multi_protect_result; assumption. }
        assert (Hres : V l T2 (protect_security (security_of T2) sigma.(indirect_reader))
                         (protect_value y1 k1.(indirect_reader))
                         (protect_value y2 k2.(indirect_reader))).
        { eapply Hbody with (a1 := u1) (a2 := u2) (r := r).
          - exact Hu.
          - exact Hflow_s.
          - exact Hsrc1. - exact Hsrc2.
          - apply value_protect_value; exact Hvy1.
          - apply value_protect_value; exact Hvy2. }
        (* apply induction hypothesis at T2 and rewrite *)
        pose proof (IHT2 l (protect_security (security_of T2) sigma.(indirect_reader)) a1 a2
                      (protect_value y1 k1.(indirect_reader))
                      (protect_value y2 k2.(indirect_reader)) Hres) as Hfin.
        rewrite protect_value_protect in Hfin.
        rewrite protect_value_protect in Hfin.
        rewrite protect_security_assoc in Hfin.
        rewrite protect_security_ir.
        rewrite Hw2eq.
        rewrite protect_security_ir.
        exact Hfin.
Qed.

Lemma E_protect : forall (l : label) (T : ty) (sigma : security) (l0 : label) (t1 t2 : tm),
  E l T sigma t1 t2 ->
  E l T (protect_security sigma l0) (tm_protect l0 t1) (tm_protect l0 t2).
Proof.
  intros l T sigma l0 t1 t2 HE. unfold E.
  intros w1 w2 Hm1 Hm2 Hw1 Hw2.
  destruct (multi_protect_inv _ _ _ Hm1 Hw1) as (v1 & Hmv1 & Hv1 & Heq1).
  destruct (multi_protect_inv _ _ _ Hm2 Hw2) as (v2 & Hmv2 & Hv2 & Heq2).
  assert (HV : V l T sigma v1 v2) by (apply HE; assumption).
  pose proof (V_protect T l sigma l0 l0 v1 v2 HV) as Hv.
  rewrite protect_security_join_idem in Hv.
  rewrite Heq1, Heq2.
  exact Hv.
Qed.

Lemma E_protect2 : forall (l : label) (T : ty) (sigma : security) (a1 a2 : label) (t1 t2 : tm),
  E l T sigma t1 t2 ->
  E l T (protect_security sigma (join a1 a2)) (tm_protect a1 t1) (tm_protect a2 t2).
Proof.
  intros l T sigma a1 a2 t1 t2 HE. unfold E.
  intros w1 w2 Hm1 Hm2 Hw1 Hw2.
  destruct (multi_protect_inv _ _ _ Hm1 Hw1) as (v1 & Hmv1 & Hv1 & Heq1).
  destruct (multi_protect_inv _ _ _ Hm2 Hw2) as (v2 & Hmv2 & Hv2 & Heq2).
  assert (HV : V l T sigma v1 v2) by (apply HE; assumption).
  pose proof (V_protect T l sigma a1 a2 v1 v2 HV) as Hv.
  rewrite Heq1, Heq2.
  exact Hv.
Qed.

(* ================= erasure of related ground values ================= *)
Fixpoint all_ir_flows (l : label) (T : ty) : Prop :=
  flows_to (security_of T).(indirect_reader) l /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      all_ir_flows l T1 /\ all_ir_flows l T2
  end.

Lemma transparent_at_all_ir : forall (T : ty) (l : label) (sigma : security),
  flows_to sigma.(indirect_reader) l -> transparent_at sigma T -> all_ir_flows l T.
Proof.
  induction T; intros l sigma Hf Htr; simpl in Htr |- *.
  - destruct Htr as [Hle _]. split; [|trivial].
    unfold security_le in Hle; destruct Hle as [_ Hi].
    exact (flows_to_trans _ _ _ Hi Hf).
  - destruct Htr as [Hle [Ht1 Ht2]]. split; [|split].
    + unfold security_le in Hle; destruct Hle as [_ Hi].
      exact (flows_to_trans _ _ _ Hi Hf).
    + apply IHT1 with (sigma := sigma); assumption.
    + apply IHT2 with (sigma := sigma); assumption.
  - destruct Htr as [Hle [Ht1 Ht2]]. split; [|split].
    + unfold security_le in Hle; destruct Hle as [_ Hi].
      exact (flows_to_trans _ _ _ Hi Hf).
    + apply IHT1 with (sigma := sigma); assumption.
    + apply IHT2 with (sigma := sigma); assumption.
  - destruct Htr as [Hle [Ht1 Ht2]]. split; [|split].
    + unfold security_le in Hle; destruct Hle as [_ Hi].
      exact (flows_to_trans _ _ _ Hi Hf).
    + apply IHT1 with (sigma := sigma); assumption.
    + apply IHT2 with (sigma := sigma); assumption.
Qed.

Lemma transparent_all_ir : forall (T : ty) (l : label),
  transparent T -> flows_to (security_of T).(indirect_reader) l -> all_ir_flows l T.
Proof.
  intros T l Htr Hf. unfold transparent in Htr.
  apply transparent_at_all_ir with (sigma := security_of T); assumption.
Qed.

Lemma V_erase : forall (T : ty) (l : label) (v1 v2 : tm),
  ground T -> all_ir_flows l T -> V l T (security_of T) v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  induction T; intros l v1 v2 Hg Hair HV; simpl in Hg |- *.
  - (* unit *) simpl in Hair. destruct Hair as [Hf _].
    destruct (HV Hf) as (k1 & k2 & E1 & E2). subst v1; subst v2. reflexivity.
  - (* sum *) destruct Hair as [Hf [Ha1 Ha2]]. destruct Hg as [Hg1 Hg2].
    destruct (HV Hf) as [Hleft | Hright].
    + destruct Hleft as (v1' & k1 & v2' & k2 & E1 & E2 & _ & _ & HV1).
      subst v1; subst v2. simpl. f_equal.
      apply IHT1 with (l := l); assumption.
    + destruct Hright as (v1' & k1 & v2' & k2 & E1 & E2 & _ & _ & HV1).
      subst v1; subst v2. simpl. f_equal.
      apply IHT2 with (l := l); assumption.
  - (* prod *) destruct Hair as [Hf [Ha1 Ha2]]. destruct Hg as [Hg1 Hg2].
    destruct (HV Hf) as (a1 & b1 & k1 & a2 & b2 & k2 & E1 & E2 & _ & _ & HV1 & HV2).
    subst v1; subst v2. simpl. f_equal.
    + apply IHT1 with (l := l); assumption.
    + apply IHT2 with (l := l); assumption.
  - (* arrow *) simpl in Hg. destruct Hg.
Qed.

(* ================= local closure ================= *)
Fixpoint max_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => Nat.max x (max_list xs')
  end.

Lemma in_max_list : forall (xs : list nat) (x : nat),
  In x xs -> x <= max_list xs.
Proof.
  induction xs; simpl; intros x H; [contradiction|].
  destruct H as [-> | H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IHxs; exact H | apply Nat.le_max_r].
Qed.

Definition fresh (xs : list atom) : atom := S (max_list xs).

Lemma fresh_notin : forall xs : list atom, ~ In (fresh xs) xs.
Proof.
  intros xs H. apply in_max_list in H. unfold fresh in H. lia.
Qed.

Lemma lc_at_open_rec : forall (body : tm) (k : nat) (u : tm),
  lc_at k (open_rec k u body) -> lc_at (S k) body.
Proof.
  induction body; intros k u H; simpl in H |- *.
  - destruct (Nat.eqb k n) eqn:E; simpl in H.
    + apply Nat.eqb_eq in E. subst n. lia.
    + lia.
  - trivial.
  - trivial.
  - apply IHbody with (k := S k) (u := u). exact H.
  - destruct H as [H1 H2]. split; [apply IHbody1 with (k := k) (u := u) | apply IHbody2 with (k := k) (u := u)]; assumption.
  - destruct H as [H1 H2]. split; [apply IHbody1 with (k := k) (u := u) | apply IHbody2 with (k := k) (u := u)]; assumption.
  - apply IHbody with (k := k) (u := u). exact H.
  - apply IHbody with (k := k) (u := u). exact H.
  - apply IHbody with (k := k) (u := u). exact H.
  - apply IHbody with (k := k) (u := u). exact H.
  - destruct H as [H0 [H1 H2]]. split; [apply IHbody1 with (k := k) (u := u) | split;
      [apply IHbody2 with (k := S k) (u := u) | apply IHbody3 with (k := S k) (u := u)]]; assumption.
  - apply IHbody with (k := k) (u := u). exact H.
  - destruct H as [H0 [H1 H2]]. split; [apply IHbody1 with (k := k) (u := u) | split;
      [apply IHbody2 with (k := k) (u := u) | apply IHbody3 with (k := k) (u := u)]]; assumption.
Qed.

Lemma value_lc : forall (v : tm), value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv; simpl.
  - unfold locally_closed; simpl; trivial.
  - exact H.
  - unfold locally_closed in *; simpl in *; split; assumption.
  - unfold locally_closed in *; simpl in *; assumption.
  - unfold locally_closed in *; simpl in *; assumption.
Qed.

Lemma has_type_lc : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H as
    [ Gamma x T Hlook Hwf
    | Gamma kappa Hwf
    | L Gamma T1 body T2 kappa HwfT1 Hwfkappa IHabs
    | Gamma t1 t2 T1 T2 kappa r IH1 IH2 Hflow
    | Gamma t1 t2 T1 T2 kappa IH1 IH2 Hwf
    | Gamma t T1 T2 kappa r IH Hflow
    | Gamma t T1 T2 kappa r IH Hflow
    | Gamma t T1 T2 kappa IH HwfT2 Hwfkappa
    | Gamma t T1 T2 kappa HwfT1 IH Hwfkappa
    | L Gamma t body1 body2 T1 T2 T kappa r IHt Hflow IH1 IH2
    | Gamma t T l IH
    | Gamma t T U IH Hsub
    | Gamma c yes no k T r IHc IHyes IHno Hflow ].
  - (* T_Var *) unfold locally_closed; simpl; trivial.
  - (* T_Unit *) unfold locally_closed; simpl; trivial.
  - (* T_Abs *)
    set (x := fresh L). assert (Hx : ~ In x L) by apply fresh_notin.
    pose proof (H x Hx) as Hlc. unfold locally_closed in Hlc.
    unfold locally_closed. apply lc_at_open_rec with (k := 0) (u := tm_fvar x). exact Hlc.
  - (* T_App *) unfold locally_closed in *; simpl in *; split; assumption.
  - (* T_Pair *) unfold locally_closed in *; simpl in *; split; assumption.
  - (* T_Fst *) unfold locally_closed in *; simpl in *; assumption.
  - (* T_Snd *) unfold locally_closed in *; simpl in *; assumption.
  - (* T_Inl *) unfold locally_closed in *; simpl in *; assumption.
  - (* T_Inr *) unfold locally_closed in *; simpl in *; assumption.
  - (* T_Case *)
    set (x1 := fresh L). assert (Hx1 : ~ In x1 L) by apply fresh_notin.
    set (x2 := fresh L). assert (Hx2 : ~ In x2 L) by apply fresh_notin.
    pose proof (H x1 Hx1) as Hlc1. pose proof (H1 x2 Hx2) as Hlc2.
    unfold locally_closed in *. simpl in *.
    split; [exact Hflow | split].
    + apply lc_at_open_rec with (k := 0) (u := tm_fvar x1). exact Hlc1.
    + apply lc_at_open_rec with (k := 0) (u := tm_fvar x2). exact Hlc2.
  - (* T_Protect *) unfold locally_closed in *; simpl in *; assumption.
  - (* T_Sub *) assumption.
  - (* T_If *)
    unfold locally_closed in *. simpl in *.
    split; [exact IHyes | split; [exact Hflow | exact IHhas_type1]].
Qed.

(* ================= closing substitution environments ================= *)
Definition extend_env (gamma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else gamma y.

Fixpoint subst_env (gamma : atom -> tm) (t : tm) : tm :=
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
      tm_case (subst_env gamma t0) (subst_env gamma body1) (subst_env gamma body2) r
  | tm_protect l t1 => tm_protect l (subst_env gamma t1)
  | tm_if c yes no r =>
      tm_if (subst_env gamma c) (subst_env gamma yes) (subst_env gamma no) r
  end.

Lemma lc_at_mono : forall (t : tm) (k k' : nat),
  lc_at k t -> k <= k' -> lc_at k' t.
Proof.
  induction t; simpl; intros k k' H Hle; try trivial; try lia; auto.
  - (* abs *) apply IHt with (k := S k). exact H. lia.
  - (* app *) destruct H as [H1 H2]; split; [apply IHt1 with k | apply IHt2 with k]; assumption.
  - (* pair *) destruct H as [H1 H2]; split; [apply IHt1 with k | apply IHt2 with k]; assumption.
  - (* fst *) apply IHt with k; assumption.
  - (* snd *) apply IHt with k; assumption.
  - (* inl *) apply IHt with k; assumption.
  - (* inr *) apply IHt with k; assumption.
  - (* case *) destruct H as [H0 [H1 H2]]; split; [apply IHt1 with k | split;
      [apply IHt2 with (S k) | apply IHt3 with (S k)]]; try assumption; lia.
  - (* protect *) apply IHt with k; assumption.
  - (* if *) destruct H as [H0 [H1 H2]]; split; [apply IHt1 with k | split;
      [apply IHt2 with k | apply IHt3 with k]]; assumption.
Qed.

Lemma open_rec_lc : forall (t : tm) (k : nat) (u : tm),
  lc_at k t -> open_rec k u t = t.
Proof.
  induction t; simpl; intros k u H.
  - destruct (Nat.eqb k n) eqn:E.
    + exfalso. apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt1. exact (proj1 H). apply IHt2. exact (proj2 H).
  - f_equal. apply IHt1. exact (proj1 H). apply IHt2. exact (proj2 H).
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - destruct H as [H0 [H1 H2]].
    f_equal. apply IHt1. exact H0. apply IHt2. exact H1. apply IHt3. exact H2.
  - f_equal. apply IHt. exact H.
  - destruct H as [H0 [H1 H2]].
    f_equal. apply IHt1. exact H0. apply IHt2. exact H1. apply IHt3. exact H2.
Qed.

Lemma subst_env_id : forall (t : tm),
  subst_env (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try reflexivity; try congruence.
Qed.

Lemma subst_env_agree : forall (gamma1 gamma2 : atom -> tm) (t : tm),
  (forall x : atom, In x (fv t) -> gamma1 x = gamma2 x) ->
  subst_env gamma1 t = subst_env gamma2 t.
Proof.
  intros gamma1 gamma2 t H. induction t; simpl; simpl in H.
  - reflexivity.
  - apply H. simpl. auto.
  - reflexivity.
  - f_equal. apply IHt. intros y Hy. apply H. exact Hy.
  - assert (H1 : forall x : atom, In x (fv t1) -> gamma1 x = gamma2 x)
      by (intros y Hy; apply H; apply in_or_app; left; exact Hy).
    assert (H2 : forall x : atom, In x (fv t2) -> gamma1 x = gamma2 x)
      by (intros y Hy; apply H; apply in_or_app; right; exact Hy).
    rewrite (IHt1 H1). rewrite (IHt2 H2). reflexivity.
  - assert (H1 : forall x : atom, In x (fv t1) -> gamma1 x = gamma2 x)
      by (intros y Hy; apply H; apply in_or_app; left; exact Hy).
    assert (H2 : forall x : atom, In x (fv t2) -> gamma1 x = gamma2 x)
      by (intros y Hy; apply H; apply in_or_app; right; exact Hy).
    rewrite (IHt1 H1). rewrite (IHt2 H2). reflexivity.
  - f_equal. apply IHt. intros y Hy. apply H. exact Hy.
  - f_equal. apply IHt. intros y Hy. apply H. exact Hy.
  - f_equal. apply IHt. intros y Hy. apply H. exact Hy.
  - f_equal. apply IHt. intros y Hy. apply H. exact Hy.
  - assert (H1 : forall x : atom, In x (fv t1) -> gamma1 x = gamma2 x)
      by (intros y Hy; apply H; apply in_or_app; left; exact Hy).
    assert (H2 : forall x : atom, In x (fv t2) -> gamma1 x = gamma2 x)
      by (intros y Hy; apply H; apply in_or_app; right; apply in_or_app; left; exact Hy).
    assert (H3 : forall x : atom, In x (fv t3) -> gamma1 x = gamma2 x)
      by (intros y Hy; apply H; apply in_or_app; right; apply in_or_app; right; exact Hy).
    rewrite (IHt1 H1). rewrite (IHt2 H2). rewrite (IHt3 H3). reflexivity.
  - f_equal. apply IHt. intros y Hy. apply H. exact Hy.
  - assert (H1 : forall x : atom, In x (fv t1) -> gamma1 x = gamma2 x)
      by (intros y Hy; apply H; apply in_or_app; left; exact Hy).
    assert (H2 : forall x : atom, In x (fv t2) -> gamma1 x = gamma2 x)
      by (intros y Hy; apply H; apply in_or_app; right; apply in_or_app; left; exact Hy).
    assert (H3 : forall x : atom, In x (fv t3) -> gamma1 x = gamma2 x)
      by (intros y Hy; apply H; apply in_or_app; right; apply in_or_app; right; exact Hy).
    rewrite (IHt1 H1). rewrite (IHt2 H2). rewrite (IHt3 H3). reflexivity.
Qed.

Lemma subst_env_extend_absent : forall (gamma : atom -> tm) (x : atom) (u : tm) (t : tm),
  ~ In x (fv t) -> subst_env (extend_env gamma x u) t = subst_env gamma t.
Proof.
  intros gamma x u t H. apply subst_env_agree.
  intros y Hy. unfold extend_env.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. exfalso. exact (H Hy).
  - reflexivity.
Qed.

Lemma subst_env_open_rec : forall (gamma : atom -> tm) (t : tm) (k : nat) (u : tm),
  (forall x : atom, locally_closed (gamma x)) ->
  subst_env gamma (open_rec k u t) = open_rec k (subst_env gamma u) (subst_env gamma t).
Proof.
  intros gamma t. induction t; intros k u Hlc; simpl.
  - destruct (Nat.eqb k n); simpl; reflexivity.
  - (* fvar *) simpl. symmetry. apply open_rec_lc.
    apply lc_at_mono with (k := 0); [apply Hlc | lia].
  - reflexivity.
  - (* abs *) f_equal. rewrite (IHt (S k) u Hlc). reflexivity.
  - rewrite (IHt1 k u Hlc). rewrite (IHt2 k u Hlc). reflexivity.
  - rewrite (IHt1 k u Hlc). rewrite (IHt2 k u Hlc). reflexivity.
  - f_equal. rewrite (IHt k u Hlc). reflexivity.
  - f_equal. rewrite (IHt k u Hlc). reflexivity.
  - f_equal. rewrite (IHt k u Hlc). reflexivity.
  - f_equal. rewrite (IHt k u Hlc). reflexivity.
  - rewrite (IHt1 k u Hlc). rewrite (IHt2 (S k) u Hlc). rewrite (IHt3 (S k) u Hlc). reflexivity.
  - f_equal. rewrite (IHt k u Hlc). reflexivity.
  - rewrite (IHt1 k u Hlc). rewrite (IHt2 k u Hlc). rewrite (IHt3 k u Hlc). reflexivity.
Qed.

Lemma subst_env_open : forall (gamma : atom -> tm) (body u : tm),
  (forall x : atom, locally_closed (gamma x)) ->
  subst_env gamma (open body u) = open (subst_env gamma body) (subst_env gamma u).
Proof.
  intros. unfold open. apply subst_env_open_rec. exact H.
Qed.

(* ================= context-free variables and plug substitution ================= *)
Fixpoint fvs_context (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ => fvs_context C'
  | C_AppLeft C' t _ => fvs_context C' ++ fv t
  | C_AppRight t C' _ => fv t ++ fvs_context C'
  | C_PairLeft C' t _ => fvs_context C' ++ fv t
  | C_PairRight t C' _ => fv t ++ fvs_context C'
  | C_Fst C' _ => fvs_context C'
  | C_Snd C' _ => fvs_context C'
  | C_Inl C' _ => fvs_context C'
  | C_Inr C' _ => fvs_context C'
  | C_CaseScrutinee C' t1 t2 _ => fvs_context C' ++ fv t1 ++ fv t2
  | C_CaseLeft t0 C' t2 _ => fv t0 ++ fvs_context C' ++ fv t2
  | C_CaseRight t0 t1 C' _ => fv t0 ++ fv t1 ++ fvs_context C'
  | C_Protect _ C' => fvs_context C'
  | C_IfCondition C' y n _ => fvs_context C' ++ fv y ++ fv n
  | C_IfThen c C' n _ => fv c ++ fvs_context C' ++ fv n
  | C_IfElse c y C' _ => fv c ++ fv y ++ fvs_context C'
  end.

Lemma subst_env_id_on : forall (gamma : atom -> tm) (t : tm),
  (forall x : atom, In x (fv t) -> gamma x = tm_fvar x) -> subst_env gamma t = t.
Proof.
  intros gamma t H. etransitivity.
  - apply subst_env_agree. intros x Hx. apply H. exact Hx.
  - apply subst_env_id.
Qed.

Lemma subst_env_plug : forall (gamma : atom -> tm) (C : program_context) (t : tm),
  (forall x : atom, In x (fvs_context C) -> gamma x = tm_fvar x) ->
  subst_env gamma (plug C t) = plug C (subst_env gamma t).
Proof.
  intros gamma C. induction C; intros u Hagree; simpl.
  - reflexivity.
  - (* C_Abs *) f_equal. apply IHC.
    intros x Hx. apply Hagree. exact Hx.
  - (* C_AppLeft *) rewrite IHC.
    + f_equal. apply subst_env_id_on. intros x Hx.
      apply Hagree. simpl. apply in_or_app. right. exact Hx.
    + intros x Hx. apply Hagree. simpl. apply in_or_app. left. exact Hx.
  - (* C_AppRight *) rewrite IHC.
    + f_equal. apply subst_env_id_on. intros x Hx.
      apply Hagree. simpl. apply in_or_app. left. exact Hx.
    + intros x Hx. apply Hagree. simpl. apply in_or_app. right. exact Hx.
  - (* C_PairLeft *) rewrite IHC.
    + f_equal. apply subst_env_id_on. intros x Hx.
      apply Hagree. simpl. apply in_or_app. right. exact Hx.
    + intros x Hx. apply Hagree. simpl. apply in_or_app. left. exact Hx.
  - (* C_PairRight *) rewrite IHC.
    + f_equal. apply subst_env_id_on. intros x Hx.
      apply Hagree. simpl. apply in_or_app. left. exact Hx.
    + intros x Hx. apply Hagree. simpl. apply in_or_app. right. exact Hx.
  - (* C_Fst *) f_equal. apply IHC. intros x Hx. apply Hagree. exact Hx.
  - (* C_Snd *) f_equal. apply IHC. intros x Hx. apply Hagree. exact Hx.
  - (* C_Inl *) f_equal. apply IHC. intros x Hx. apply Hagree. exact Hx.
  - (* C_Inr *) f_equal. apply IHC. intros x Hx. apply Hagree. exact Hx.
  - (* C_CaseScrutinee *) rewrite IHC.
    + f_equal; try reflexivity.
      * apply subst_env_id_on. intros x Hx.
        apply Hagree. simpl. apply in_or_app. right. apply in_or_app. left. exact Hx.
      * apply subst_env_id_on. intros x Hx.
        apply Hagree. simpl. apply in_or_app. right. apply in_or_app. right. exact Hx.
    + intros x Hx. apply Hagree. simpl. apply in_or_app. left. exact Hx.
  - (* C_CaseLeft *) rewrite IHC.
    + f_equal; try reflexivity.
      * apply subst_env_id_on. intros x Hx.
        apply Hagree. simpl. apply in_or_app. left. exact Hx.
      * apply subst_env_id_on. intros x Hx.
        apply Hagree. simpl. apply in_or_app. right. apply in_or_app. right. exact Hx.
    + intros x Hx. apply Hagree. simpl. apply in_or_app. right. apply in_or_app. left. exact Hx.
  - (* C_CaseRight *) rewrite IHC.
    + f_equal; try reflexivity.
      * apply subst_env_id_on. intros x Hx.
        apply Hagree. simpl. apply in_or_app. left. exact Hx.
      * apply subst_env_id_on. intros x Hx.
        apply Hagree. simpl. apply in_or_app. right. apply in_or_app. left. exact Hx.
    + intros x Hx. apply Hagree. simpl. apply in_or_app. right. apply in_or_app. right. exact Hx.
  - (* C_Protect *) f_equal. apply IHC. intros x Hx. apply Hagree. exact Hx.
  - (* C_IfCondition *) rewrite IHC.
    + f_equal; try reflexivity.
      * apply subst_env_id_on. intros x Hx.
        apply Hagree. simpl. apply in_or_app. right. apply in_or_app. left. exact Hx.
      * apply subst_env_id_on. intros x Hx.
        apply Hagree. simpl. apply in_or_app. right. apply in_or_app. right. exact Hx.
    + intros x Hx. apply Hagree. simpl. apply in_or_app. left. exact Hx.
  - (* C_IfThen *) rewrite IHC.
    + f_equal; try reflexivity.
      * apply subst_env_id_on. intros x Hx.
        apply Hagree. simpl. apply in_or_app. left. exact Hx.
      * apply subst_env_id_on. intros x Hx.
        apply Hagree. simpl. apply in_or_app. right. apply in_or_app. right. exact Hx.
    + intros x Hx. apply Hagree. simpl. apply in_or_app. right. apply in_or_app. left. exact Hx.
  - (* C_IfElse *) rewrite IHC.
    + f_equal; try reflexivity.
      * apply subst_env_id_on. intros x Hx.
        apply Hagree. simpl. apply in_or_app. left. exact Hx.
      * apply subst_env_id_on. intros x Hx.
        apply Hagree. simpl. apply in_or_app. right. apply in_or_app. left. exact Hx.
    + intros x Hx. apply Hagree. simpl. apply in_or_app. right. apply in_or_app. right. exact Hx.
Qed.

(* ================= additional helpers ================= *)
Definition flows_to_b (l1 l2 : label) : bool :=
  match l1, l2 with
  | High, Low => false
  | _, _ => true
  end.

Lemma flows_to_b_spec : forall l1 l2 : label,
  flows_to l1 l2 <-> flows_to_b l1 l2 = true.
Proof. intros l1 l2; destruct l1, l2; simpl; split; intro H; try reflexivity; try discriminate; try contradiction. Qed.

Lemma security_of_ty_protect : forall (l0 : label) (T : ty),
  security_of (ty_protect l0 T) = protect_security (security_of T) l0.
Proof. intros; destruct T; reflexivity. Qed.

Lemma E_ty_protect_nat : forall (l : label) (T : ty) (l0 : label) (t1 t2 : tm),
  E l (ty_protect l0 T) (security_of (ty_protect l0 T)) t1 t2
  <-> E l T (protect_security (security_of T) l0) t1 t2.
Proof.
  intros. rewrite security_of_ty_protect. apply E_ty_protect.
Qed.

Lemma lookup_update_same : forall (Gamma : context) (x : atom) (T : ty),
  lookup_context x (update Gamma x T) = Some T.
Proof.
  intros. unfold update, lookup_context. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_update_other : forall (Gamma : context) (x y : atom) (T : ty),
  y <> x -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros. unfold update, lookup_context. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply H. exact E.
  - reflexivity.
Qed.

Lemma extend_env_same : forall (gamma : atom -> tm) (x : atom) (u : tm),
  extend_env gamma x u x = u.
Proof.
  intros. unfold extend_env. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma extend_env_other : forall (gamma : atom -> tm) (x y : atom) (u : tm),
  y <> x -> extend_env gamma x u y = gamma y.
Proof.
  intros. unfold extend_env. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply H. exact E.
  - reflexivity.
Qed.

Lemma E_sub : forall (T U : ty), subtype T U ->
  forall (l : label) (sigma sigma' : security) (t1 t2 : tm),
    security_le sigma sigma' -> E l T sigma t1 t2 -> E l U sigma' t1 t2.
Proof.
  intros T U Hsub l sigma sigma' t1 t2 Hle HE.
  unfold E in *. intros v1 v2 Hm1 Hm2 Hv1 Hv2.
  eapply V_sub; [exact Hsub | exact Hle | apply HE; assumption].
Qed.

Lemma E_opaque : forall (l : label) (T : ty) (sigma : security) (t1 t2 : tm),
  ~ flows_to sigma.(indirect_reader) l -> E l T sigma t1 t2.
Proof.
  intros l T sigma t1 t2 H. unfold E. intros. apply V_opaque. exact H.
Qed.

(* ================= fundamental theorem ================= *)
Definition P (Gamma : context) (t : tm) (T : ty) : Prop :=
  forall (l : label) (gamma1 gamma2 : atom -> tm),
    (forall x : atom, locally_closed (gamma1 x)) ->
    (forall x : atom, locally_closed (gamma2 x)) ->
    (forall (x : atom) (T' : ty), lookup_context x Gamma = Some T' ->
       E l T' (security_of T') (gamma1 x) (gamma2 x)) ->
    E l T (security_of T) (subst_env gamma1 t) (subst_env gamma2 t).

Theorem fundamental : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T -> P Gamma t T.
Proof.
  apply (has_type_ind P).
  - (* T_Var *)
    intros Gamma x T Hlook Hwf l gamma1 gamma2 Hlc1 Hlc2 Henv.
    simpl. apply Henv. exact Hlook.
  - (* T_Unit *)
    intros Gamma kappa Hwf l gamma1 gamma2 Hlc1 Hlc2 Henv.
    simpl. unfold E. intros v1 v2 Hm1 Hm2 Hv1 Hv2.
    rewrite (multi_unit_inv kappa v1 Hm1).
    rewrite (multi_unit_inv kappa v2 Hm2).
    simpl. intros _. exists kappa, kappa. split; reflexivity.
  - (* T_Abs *)
    intros L Gamma T1 body T2 kappa HwfT1 Hwfkappa Hprem IHbody.
    intros l gamma1 gamma2 Hlc1 Hlc2 Henv.
    simpl. unfold E. intros w1 w2 Hm1 Hm2 Hv1 Hv2.
    rewrite (multi_abs_inv T1 (subst_env gamma1 body) kappa w1 Hm1).
    rewrite (multi_abs_inv T1 (subst_env gamma2 body) kappa w2 Hm2).
    simpl. intros Hf.
    split.
    { exists T1, (subst_env gamma1 body), kappa. split; [reflexivity | apply security_le_refl]. }
    split.
    { exists T1, (subst_env gamma2 body), kappa. split; [reflexivity | apply security_le_refl]. }
    intros a1 a2 Ha r Hflow w1' w2' Hm1' Hm2' Hv1' Hv2'.
    destruct (multi_app_inv _ _ _ _ Hm1' Hv1') as
      (T1x & bodyx & va1 & kx & Hfa1 & Hvfa1 & Ha1 & Hva1 & Hfl1 & Hres1).
    simpl in Hfa1.
    assert (Hb1 : tm_abs T1x bodyx kx = tm_abs T1 (subst_env gamma1 body) kappa)
      by (apply (multi_abs_inv _ _ _ _ Hfa1)).
    inversion Hb1; subst.
    destruct (multi_app_inv _ _ _ _ Hm2' Hv2') as
      (T2x & bodyx2 & va2 & kx2 & Hfa2 & Hvfa2 & Ha2 & Hva2 & Hfl2 & Hres2).
    simpl in Hfa2.
    assert (Hb2 : tm_abs T2x bodyx2 kx2 = tm_abs T1 (subst_env gamma2 body) kappa)
      by (apply (multi_abs_inv _ _ _ _ Hfa2)).
    inversion Hb2; subst.
    assert (HVa : V l T1 (security_of T1) va1 va2) by (apply Ha; assumption).
    set (x := fresh (L ++ fv body)).
    assert (HxL : ~ In x L).
    { intro Hx. apply (fresh_notin (L ++ fv body)). apply in_or_app. left. exact Hx. }
    assert (Hxbody : ~ In x (fv body)).
    { intro Hx. apply (fresh_notin (L ++ fv body)). apply in_or_app. right. exact Hx. }
    set (gamma1' := extend_env gamma1 x va1).
    set (gamma2' := extend_env gamma2 x va2).
    assert (Hlc1' : forall y, locally_closed (gamma1' y)).
    { intros y. unfold gamma1', extend_env. destruct (Nat.eqb y x) eqn:E.
      - apply Nat.eqb_eq in E. subst y. apply value_lc. exact Hva1.
      - apply Hlc1. }
    assert (Hlc2' : forall y, locally_closed (gamma2' y)).
    { intros y. unfold gamma2', extend_env. destruct (Nat.eqb y x) eqn:E.
      - apply Nat.eqb_eq in E. subst y. apply value_lc. exact Hva2.
      - apply Hlc2. }
    assert (Henv' : forall (y : atom) (T' : ty),
               lookup_context y (update Gamma x T1) = Some T' ->
               E l T' (security_of T') (gamma1' y) (gamma2' y)).
    { intros y T' Hlook. destruct (Nat.eqb y x) eqn:E.
      - apply Nat.eqb_eq in E. subst y.
        rewrite lookup_update_same in Hlook. inversion Hlook; subst T'.
        unfold gamma1', gamma2', extend_env. rewrite Nat.eqb_refl. simpl.
        apply E_of_V_values; assumption.
      - apply Nat.eqb_neq in E.
        rewrite (lookup_update_other Gamma x y T1 E) in Hlook.
        unfold gamma1', gamma2', extend_env.
        destruct (Nat.eqb y x) eqn:E2.
        + apply Nat.eqb_eq in E2. exfalso. apply E. exact E2.
        + simpl. apply Henv. exact Hlook. }
    pose proof (IHbody x HxL l gamma1' gamma2' Hlc1' Hlc2' Henv') as IHx.
    rewrite (subst_env_open gamma1' body (tm_fvar x) Hlc1') in IHx.
    rewrite (subst_env_open gamma2' body (tm_fvar x) Hlc2') in IHx.
    assert (Hx1 : subst_env gamma1' (tm_fvar x) = va1).
    { simpl. unfold gamma1'. apply extend_env_same. }
    assert (Hx2 : subst_env gamma2' (tm_fvar x) = va2).
    { simpl. unfold gamma2'. apply extend_env_same. }
    assert (Hbs1 : subst_env gamma1' body = subst_env gamma1 body).
    { unfold gamma1'. apply subst_env_extend_absent. exact Hxbody. }
    assert (Hbs2 : subst_env gamma2' body = subst_env gamma2 body).
    { unfold gamma2'. apply subst_env_extend_absent. exact Hxbody. }
    rewrite Hx1 in IHx. rewrite Hx2 in IHx. rewrite Hbs1 in IHx. rewrite Hbs2 in IHx.
    pose proof (E_protect l T2 (security_of T2) kappa.(indirect_reader)
                  (open (subst_env gamma1 body) va1)
                  (open (subst_env gamma2 body) va2) IHx) as Hprot.
    unfold E in Hprot.
    eapply Hprot; [exact Hres1 | exact Hres2 | exact Hv1' | exact Hv2'].
  - (* T_App *)
    intros Gamma t1 t2 T1 T2 kappa r Hprem1 IH1 Hprem2 IH2 Hflow.
    intros l gamma1 gamma2 Hlc1 Hlc2 Henv.
    rewrite E_ty_protect_nat.
    unfold E. intros w1 w2 Hm1 Hm2 Hv1 Hv2.
    destruct (multi_app_inv _ _ _ _ Hm1 Hv1) as
      (Ta1 & body1 & va1 & k1 & Hf1 & Hvf1 & Ha1 & Hva1 & Hfl1 & Hres1).
    destruct (multi_app_inv _ _ _ _ Hm2 Hv2) as
      (Ta2 & body2 & va2 & k2 & Hf2 & Hvf2 & Ha2 & Hva2 & Hfl2 & Hres2).
    pose proof (IH1 l gamma1 gamma2 Hlc1 Hlc2 Henv) as HE1.
    unfold E in HE1.
    pose proof (HE1 _ _ Hf1 Hf2 Hvf1 Hvf2) as HVfun.
    pose proof (IH2 l gamma1 gamma2 Hlc1 Hlc2 Henv) as HE2.
    unfold E in HE2.
    simpl in HVfun.
    destruct (flows_to_b kappa.(indirect_reader) l) eqn:Eb.
    + apply flows_to_b_spec in Eb.
      destruct (HVfun Eb) as [Habs1 [Habs2 Hbody]].
      assert (Hsrc1 : multi (tm_app (tm_abs Ta1 body1 k1) (subst_env gamma1 t2) r) w1).
      { eapply multi_trans with (t2 := tm_app (tm_abs Ta1 body1 k1) va1 r).
        - apply multi_app_arg; assumption.
        - eapply multi_trans with (t2 := tm_protect k1.(indirect_reader) (open body1 va1)).
          + eapply multi_step.
            * apply ST_AppAbs; assumption.
            * apply multi_refl.
          + exact Hres1. }
      assert (Hsrc2 : multi (tm_app (tm_abs Ta2 body2 k2) (subst_env gamma2 t2) r) w2).
      { eapply multi_trans with (t2 := tm_app (tm_abs Ta2 body2 k2) va2 r).
        - apply multi_app_arg; assumption.
        - eapply multi_trans with (t2 := tm_protect k2.(indirect_reader) (open body2 va2)).
          + eapply multi_step.
            * apply ST_AppAbs; assumption.
            * apply multi_refl.
          + exact Hres2. }
      eapply Hbody.
      * exact HE2.
      * exact Hflow.
      * exact Hsrc1.
      * exact Hsrc2.
      * exact Hv1.
      * exact Hv2.
    + apply V_opaque. intro Hf.
      assert (Hff : flows_to kappa.(indirect_reader) l).
      { rewrite protect_security_ir in Hf. eapply flows_to_join_r; exact Hf. }
      apply flows_to_b_spec in Hff. rewrite Hff in Eb. discriminate Eb.
  - (* T_Pair *)
    intros Gamma t1 t2 T1 T2 kappa Hprem1 IH1 Hprem2 IH2 Hwf.
    intros l gamma1 gamma2 Hlc1 Hlc2 Henv.
    simpl. unfold E. intros w1 w2 Hm1 Hm2 Hv1 Hv2.
    destruct (multi_pair_inv _ _ _ _ Hm1 Hv1) as
      (va1 & vb1 & Ha1 & Hva1 & Hb1 & Hvb1 & Heq1).
    destruct (multi_pair_inv _ _ _ _ Hm2 Hv2) as
      (va2 & vb2 & Ha2 & Hva2 & Hb2 & Hvb2 & Heq2).
    subst w1; subst w2.
    pose proof (IH1 l gamma1 gamma2 Hlc1 Hlc2 Henv) as HE1.
    unfold E in HE1.
    pose proof (HE1 _ _ Ha1 Ha2 Hva1 Hva2) as HV1.
    pose proof (IH2 l gamma1 gamma2 Hlc1 Hlc2 Henv) as HE2.
    unfold E in HE2.
    pose proof (HE2 _ _ Hb1 Hb2 Hvb1 Hvb2) as HV2.
    destruct (flows_to_b kappa.(indirect_reader) l) eqn:Eb.
    + apply flows_to_b_spec in Eb.
      simpl. exists va1, vb1, kappa, va2, vb2, kappa.
      split; [reflexivity | split; [reflexivity | split;
        [apply security_le_refl | split; [apply security_le_refl | split; assumption]]]].
    + apply V_opaque. intro Hf.
      assert (Hff : flows_to kappa.(indirect_reader) l).
      { simpl in Hf. exact Hf. }
      apply flows_to_b_spec in Hff. rewrite Hff in Eb. discriminate Eb.
  - (* T_Fst *)
    intros Gamma t T1 T2 kappa r Hprem IH Hflow.
    intros l gamma1 gamma2 Hlc1 Hlc2 Henv.
    rewrite E_ty_protect_nat.
    unfold E. intros w1 w2 Hm1 Hm2 Hv1 Hv2.
    destruct (multi_fst_inv _ _ _ Hm1 Hv1) as (vp1 & Hmt1 & Hvp1 & Hrest1).
    destruct Hrest1 as (v1 & v2 & k1 & Hpair1 & Hvv1 & Hvv2 & Hfl1 & Hres1).
    destruct (multi_fst_inv _ _ _ Hm2 Hv2) as (vp2 & Hmt2 & Hvp2 & Hrest2).
    destruct Hrest2 as (v1' & v2' & k2 & Hpair2 & Hvv1' & Hvv2' & Hfl2 & Hres2).
    subst vp1; subst vp2.
    pose proof (IH l gamma1 gamma2 Hlc1 Hlc2 Henv) as HE.
    unfold E in HE.
    pose proof (HE _ _ Hmt1 Hmt2 Hvp1 Hvp2) as HVp.
    destruct (flows_to_b kappa.(indirect_reader) l) eqn:Eb.
    + apply flows_to_b_spec in Eb.
      simpl in HVp.
      destruct (HVp Eb) as (a1 & b1 & kk1 & a2 & b2 & kk2 & Eq1 & Eq2 & L1 & L2 & HV1 & HV2).
      inversion Eq1; subst. inversion Eq2; subst.
      destruct (multi_protect_inv _ _ _ Hres1 Hv1) as (y1 & Hy1 & Hvy1 & Hw1eq).
      assert (Hy1v : y1 = a1) by (eapply multi_value_inv; eauto).
      subst y1.
      destruct (multi_protect_inv _ _ _ Hres2 Hv2) as (y2 & Hy2 & Hvy2 & Hw2eq).
      assert (Hy2v : y2 = a2) by (eapply multi_value_inv; eauto).
      subst y2.
      rewrite Hw1eq, Hw2eq.
      eapply V_mono.
      { apply protect_security_le; [apply security_le_refl |].
        apply flows_to_join.
        - destruct L1 as [_ Hk1]. exact Hk1.
        - destruct L2 as [_ Hk2]. exact Hk2. }
      { apply V_protect. exact HV1. }
    + apply V_opaque. intro Hf.
      assert (Hff : flows_to kappa.(indirect_reader) l).
      { rewrite protect_security_ir in Hf. eapply flows_to_join_r; exact Hf. }
      apply flows_to_b_spec in Hff. rewrite Hff in Eb. discriminate Eb.
  - (* T_Snd *)
    intros Gamma t T1 T2 kappa r Hprem IH Hflow.
    intros l gamma1 gamma2 Hlc1 Hlc2 Henv.
    rewrite E_ty_protect_nat.
    unfold E. intros w1 w2 Hm1 Hm2 Hv1 Hv2.
    destruct (multi_snd_inv _ _ _ Hm1 Hv1) as (vp1 & Hmt1 & Hvp1 & Hrest1).
    destruct Hrest1 as (v1 & v2 & k1 & Hpair1 & Hvv1 & Hvv2 & Hfl1 & Hres1).
    destruct (multi_snd_inv _ _ _ Hm2 Hv2) as (vp2 & Hmt2 & Hvp2 & Hrest2).
    destruct Hrest2 as (v1' & v2' & k2 & Hpair2 & Hvv1' & Hvv2' & Hfl2 & Hres2).
    subst vp1; subst vp2.
    pose proof (IH l gamma1 gamma2 Hlc1 Hlc2 Henv) as HE.
    unfold E in HE.
    pose proof (HE _ _ Hmt1 Hmt2 Hvp1 Hvp2) as HVp.
    destruct (flows_to_b kappa.(indirect_reader) l) eqn:Eb.
    + apply flows_to_b_spec in Eb.
      simpl in HVp.
      destruct (HVp Eb) as (a1 & b1 & kk1 & a2 & b2 & kk2 & Eq1 & Eq2 & L1 & L2 & HV1 & HV2).
      inversion Eq1; subst. inversion Eq2; subst.
      destruct (multi_protect_inv _ _ _ Hres1 Hv1) as (y1 & Hy1 & Hvy1 & Hw1eq).
      assert (Hy1v : y1 = b1) by (eapply multi_value_inv; eauto).
      subst y1.
      destruct (multi_protect_inv _ _ _ Hres2 Hv2) as (y2 & Hy2 & Hvy2 & Hw2eq).
      assert (Hy2v : y2 = b2) by (eapply multi_value_inv; eauto).
      subst y2.
      rewrite Hw1eq, Hw2eq.
      eapply V_mono.
      { apply protect_security_le; [apply security_le_refl |].
        apply flows_to_join.
        - destruct L1 as [_ Hk1]. exact Hk1.
        - destruct L2 as [_ Hk2]. exact Hk2. }
      { apply V_protect. exact HV2. }
    + apply V_opaque. intro Hf.
      assert (Hff : flows_to kappa.(indirect_reader) l).
      { rewrite protect_security_ir in Hf. eapply flows_to_join_r; exact Hf. }
      apply flows_to_b_spec in Hff. rewrite Hff in Eb. discriminate Eb.
  - (* T_Inl *)
    intros Gamma t T1 T2 kappa Hprem IH HwfT2 Hwfkappa.
    intros l gamma1 gamma2 Hlc1 Hlc2 Henv.
    simpl. unfold E. intros w1 w2 Hm1 Hm2 Hv1 Hv2.
    destruct (multi_inl_inv _ _ _ Hm1 Hv1) as (vt1 & Hmt1 & Hvt1 & Heq1).
    destruct (multi_inl_inv _ _ _ Hm2 Hv2) as (vt2 & Hmt2 & Hvt2 & Heq2).
    subst w1; subst w2.
    pose proof (IH l gamma1 gamma2 Hlc1 Hlc2 Henv) as HE.
    unfold E in HE.
    pose proof (HE _ _ Hmt1 Hmt2 Hvt1 Hvt2) as HV1.
    destruct (flows_to_b kappa.(indirect_reader) l) eqn:Eb.
    + apply flows_to_b_spec in Eb.
      simpl. intros _.
      left. exists vt1, kappa, vt2, kappa.
      split; [reflexivity | split; [reflexivity | split;
        [apply security_le_refl | split; [apply security_le_refl | exact HV1]]]].
    + apply V_opaque. intro Hf. simpl in Hf.
      apply flows_to_b_spec in Hf. rewrite Hf in Eb. discriminate Eb.
  - (* T_Inr *)
    intros Gamma t T1 T2 kappa HwfT1 Hprem IH Hwfkappa.
    intros l gamma1 gamma2 Hlc1 Hlc2 Henv.
    simpl. unfold E. intros w1 w2 Hm1 Hm2 Hv1 Hv2.
    destruct (multi_inr_inv _ _ _ Hm1 Hv1) as (vt1 & Hmt1 & Hvt1 & Heq1).
    destruct (multi_inr_inv _ _ _ Hm2 Hv2) as (vt2 & Hmt2 & Hvt2 & Heq2).
    subst w1; subst w2.
    pose proof (IH l gamma1 gamma2 Hlc1 Hlc2 Henv) as HE.
    unfold E in HE.
    pose proof (HE _ _ Hmt1 Hmt2 Hvt1 Hvt2) as HV2.
    destruct (flows_to_b kappa.(indirect_reader) l) eqn:Eb.
    + apply flows_to_b_spec in Eb.
      simpl. intros _.
      right. exists vt1, kappa, vt2, kappa.
      split; [reflexivity | split; [reflexivity | split;
        [apply security_le_refl | split; [apply security_le_refl | exact HV2]]]].
    + apply V_opaque. intro Hf. simpl in Hf.
      apply flows_to_b_spec in Hf. rewrite Hf in Eb. discriminate Eb.
  - (* T_Case *)
    intros L Gamma t body1 body2 T1 T2 T kappa r Hpremt IHt Hflow Hprem1 IH1 Hprem2 IH2.
    intros l gamma1 gamma2 Hlc1 Hlc2 Henv.
    rewrite E_ty_protect_nat.
    unfold E. intros w1 w2 Hm1 Hm2 Hv1 Hv2.
    destruct (multi_case_inv _ _ _ _ _ Hm1 Hv1) as (vt1 & Hmt1 & Hvt1 & Hdisj1).
    destruct (multi_case_inv _ _ _ _ _ Hm2 Hv2) as (vt2 & Hmt2 & Hvt2 & Hdisj2).
    pose proof (IHt l gamma1 gamma2 Hlc1 Hlc2 Henv) as HEt.
    unfold E in HEt.
    pose proof (HEt _ _ Hmt1 Hmt2 Hvt1 Hvt2) as HVs.
    destruct (flows_to_b kappa.(indirect_reader) l) eqn:Eb.
    + apply flows_to_b_spec in Eb.
      simpl in HVs.
      destruct (HVs Eb) as [Hleft | Hright].
      * (* inl *)
        destruct Hleft as (u1 & k1 & u2 & k2 & Eq1 & Eq2 & L1 & L2 & HV1).
        subst vt1; subst vt2.
        destruct Hdisj1 as [Hd1 | Hd1].
        { destruct Hd1 as (u1a & k1a & Eq1a & Hvu1 & Hfl1 & Hres1). inversion Eq1a; subst.
          destruct Hdisj2 as [Hd2 | Hd2].
          - destruct Hd2 as (u2a & k2a & Eq2a & Hvu2 & Hfl2 & Hres2). inversion Eq2a; subst.
            set (x := fresh (L ++ fv body1 ++ fv body2)).
            assert (HxL : ~ In x L)
              by (intro Hx; apply (fresh_notin (L ++ fv body1 ++ fv body2));
                  apply in_or_app; left; exact Hx).
            assert (Hxb1 : ~ In x (fv body1))
              by (intro Hx; apply (fresh_notin (L ++ fv body1 ++ fv body2));
                  apply in_or_app; right; apply in_or_app; left; exact Hx).
            set (gamma1' := extend_env gamma1 x u1a).
            set (gamma2' := extend_env gamma2 x u2a).
            assert (Hlc1' : forall y, locally_closed (gamma1' y)).
            { intros y. unfold gamma1', extend_env. destruct (Nat.eqb y x) eqn:E.
              - apply Nat.eqb_eq in E. subst y. apply value_lc. exact Hvu1.
              - apply Hlc1. }
            assert (Hlc2' : forall y, locally_closed (gamma2' y)).
            { intros y. unfold gamma2', extend_env. destruct (Nat.eqb y x) eqn:E.
              - apply Nat.eqb_eq in E. subst y. apply value_lc. exact Hvu2.
              - apply Hlc2. }
            assert (Henv' : forall (y : atom) (T' : ty),
                       lookup_context y (update Gamma x T1) = Some T' ->
                       E l T' (security_of T') (gamma1' y) (gamma2' y)).
            { intros y T' Hlook. destruct (Nat.eqb y x) eqn:E.
              - apply Nat.eqb_eq in E. subst y.
                rewrite lookup_update_same in Hlook. inversion Hlook; subst T'.
                unfold gamma1', gamma2', extend_env. rewrite Nat.eqb_refl. simpl.
                apply E_of_V_values; assumption.
              - apply Nat.eqb_neq in E.
                rewrite (lookup_update_other Gamma x y T1 E) in Hlook.
                unfold gamma1', gamma2', extend_env.
                destruct (Nat.eqb y x) eqn:E2.
                + apply Nat.eqb_eq in E2. exfalso. apply E. exact E2.
                + simpl. apply Henv. exact Hlook. }
            pose proof (IH1 x HxL l gamma1' gamma2' Hlc1' Hlc2' Henv') as IHx.
            rewrite (subst_env_open gamma1' body1 (tm_fvar x) Hlc1') in IHx.
            rewrite (subst_env_open gamma2' body1 (tm_fvar x) Hlc2') in IHx.
            assert (Hx1 : subst_env gamma1' (tm_fvar x) = u1a).
            { simpl. unfold gamma1'. apply extend_env_same. }
            assert (Hx2 : subst_env gamma2' (tm_fvar x) = u2a).
            { simpl. unfold gamma2'. apply extend_env_same. }
            assert (Hbs1 : subst_env gamma1' body1 = subst_env gamma1 body1).
            { unfold gamma1'. apply subst_env_extend_absent. exact Hxb1. }
            assert (Hbs2 : subst_env gamma2' body1 = subst_env gamma2 body1).
            { unfold gamma2'. apply subst_env_extend_absent. exact Hxb1. }
            rewrite Hx1 in IHx. rewrite Hx2 in IHx. rewrite Hbs1 in IHx. rewrite Hbs2 in IHx.
            pose proof (E_protect2 l T (security_of T) k1a.(indirect_reader) k2a.(indirect_reader)
                          (open (subst_env gamma1 body1) u1a)
                          (open (subst_env gamma2 body1) u2a) IHx) as Hprot.
            unfold E in Hprot.
            eapply V_mono.
            { apply protect_security_le; [apply security_le_refl |].
              apply flows_to_join.
              - destruct L1 as [_ Hk1]. exact Hk1.
              - destruct L2 as [_ Hk2]. exact Hk2. }
            { eapply Hprot; [exact Hres1 | exact Hres2 | exact Hv1 | exact Hv2]. }
          - destruct Hd2 as (u2a & k2a & Eq2a & _ & _ & _). inversion Eq2a. }
        { destruct Hd1 as (u1a & k1a & Eq1a & _ & _ & _). inversion Eq1a. }
      * (* inr *)
        destruct Hright as (u1 & k1 & u2 & k2 & Eq1 & Eq2 & L1 & L2 & HV1).
        subst vt1; subst vt2.
        destruct Hdisj1 as [Hd1 | Hd1].
        { destruct Hd1 as (u1a & k1a & Eq1a & _ & _ & _). inversion Eq1a. }
        { destruct Hd1 as (u1a & k1a & Eq1a & Hvu1 & Hfl1 & Hres1). inversion Eq1a; subst.
          destruct Hdisj2 as [Hd2 | Hd2].
          - destruct Hd2 as (u2a & k2a & Eq2a & _ & _ & _). inversion Eq2a.
          - destruct Hd2 as (u2a & k2a & Eq2a & Hvu2 & Hfl2 & Hres2). inversion Eq2a; subst.
            set (x := fresh (L ++ fv body1 ++ fv body2)).
            assert (HxL : ~ In x L)
              by (intro Hx; apply (fresh_notin (L ++ fv body1 ++ fv body2));
                  apply in_or_app; left; exact Hx).
            assert (Hxb2 : ~ In x (fv body2))
              by (intro Hx; apply (fresh_notin (L ++ fv body1 ++ fv body2));
                  apply in_or_app; right; apply in_or_app; right; exact Hx).
            set (gamma1' := extend_env gamma1 x u1a).
            set (gamma2' := extend_env gamma2 x u2a).
            assert (Hlc1' : forall y, locally_closed (gamma1' y)).
            { intros y. unfold gamma1', extend_env. destruct (Nat.eqb y x) eqn:E.
              - apply Nat.eqb_eq in E. subst y. apply value_lc. exact Hvu1.
              - apply Hlc1. }
            assert (Hlc2' : forall y, locally_closed (gamma2' y)).
            { intros y. unfold gamma2', extend_env. destruct (Nat.eqb y x) eqn:E.
              - apply Nat.eqb_eq in E. subst y. apply value_lc. exact Hvu2.
              - apply Hlc2. }
            assert (Henv' : forall (y : atom) (T' : ty),
                       lookup_context y (update Gamma x T2) = Some T' ->
                       E l T' (security_of T') (gamma1' y) (gamma2' y)).
            { intros y T' Hlook. destruct (Nat.eqb y x) eqn:E.
              - apply Nat.eqb_eq in E. subst y.
                rewrite lookup_update_same in Hlook. inversion Hlook; subst T'.
                unfold gamma1', gamma2', extend_env. rewrite Nat.eqb_refl. simpl.
                apply E_of_V_values; assumption.
              - apply Nat.eqb_neq in E.
                rewrite (lookup_update_other Gamma x y T2 E) in Hlook.
                unfold gamma1', gamma2', extend_env.
                destruct (Nat.eqb y x) eqn:E2.
                + apply Nat.eqb_eq in E2. exfalso. apply E. exact E2.
                + simpl. apply Henv. exact Hlook. }
            pose proof (IH2 x HxL l gamma1' gamma2' Hlc1' Hlc2' Henv') as IHx.
            rewrite (subst_env_open gamma1' body2 (tm_fvar x) Hlc1') in IHx.
            rewrite (subst_env_open gamma2' body2 (tm_fvar x) Hlc2') in IHx.
            assert (Hx1 : subst_env gamma1' (tm_fvar x) = u1a).
            { simpl. unfold gamma1'. apply extend_env_same. }
            assert (Hx2 : subst_env gamma2' (tm_fvar x) = u2a).
            { simpl. unfold gamma2'. apply extend_env_same. }
            assert (Hbs1 : subst_env gamma1' body2 = subst_env gamma1 body2).
            { unfold gamma1'. apply subst_env_extend_absent. exact Hxb2. }
            assert (Hbs2 : subst_env gamma2' body2 = subst_env gamma2 body2).
            { unfold gamma2'. apply subst_env_extend_absent. exact Hxb2. }
            rewrite Hx1 in IHx. rewrite Hx2 in IHx. rewrite Hbs1 in IHx. rewrite Hbs2 in IHx.
            pose proof (E_protect2 l T (security_of T) k1a.(indirect_reader) k2a.(indirect_reader)
                          (open (subst_env gamma1 body2) u1a)
                          (open (subst_env gamma2 body2) u2a) IHx) as Hprot.
            unfold E in Hprot.
            eapply V_mono.
            { apply protect_security_le; [apply security_le_refl |].
              apply flows_to_join.
              - destruct L1 as [_ Hk1]. exact Hk1.
              - destruct L2 as [_ Hk2]. exact Hk2. }
            { eapply Hprot; [exact Hres1 | exact Hres2 | exact Hv1 | exact Hv2]. } }
    + apply V_opaque. intro Hf.
      assert (Hff : flows_to kappa.(indirect_reader) l).
      { rewrite protect_security_ir in Hf. eapply flows_to_join_r; exact Hf. }
      apply flows_to_b_spec in Hff. rewrite Hff in Eb. discriminate Eb.
  - (* T_Protect *)
    intros Gamma t T l0 Hprem IH.
    intros l gamma1 gamma2 Hlc1 Hlc2 Henv.
    rewrite E_ty_protect_nat.
    simpl.
    apply E_protect with (l0 := l0).
    apply IH; assumption.
  - (* T_Sub *)
    intros Gamma t T U Hprem IH Hsub.
    intros l gamma1 gamma2 Hlc1 Hlc2 Henv.
    simpl.
    eapply E_sub with (T := T) (U := U)
                     (sigma := security_of T) (sigma' := security_of U).
    + exact Hsub.
    + apply subtype_security_le. exact Hsub.
    + apply IH; assumption.
  - (* T_If *)
    intros Gamma c yes no k T r Hpremc IHc Hpremyes IHyes Hpremno IHno Hflow.
    intros l gamma1 gamma2 Hlc1 Hlc2 Henv.
    rewrite E_ty_protect_nat.
    unfold E. intros w1 w2 Hm1 Hm2 Hv1 Hv2.
    destruct (multi_if_inv _ _ _ _ _ Hm1 Hv1) as (vc1 & Hmc1 & Hvc1 & Hdisj1).
    destruct (multi_if_inv _ _ _ _ _ Hm2 Hv2) as (vc2 & Hmc2 & Hvc2 & Hdisj2).
    pose proof (IHc l gamma1 gamma2 Hlc1 Hlc2 Henv) as HEc.
    unfold E in HEc.
    pose proof (HEc _ _ Hmc1 Hmc2 Hvc1 Hvc2) as HVs.
    destruct (flows_to_b k.(indirect_reader) l) eqn:Eb.
    + apply flows_to_b_spec in Eb.
      simpl in HVs.
      destruct (HVs Eb) as [Hleft | Hright].
      * destruct Hleft as (u1 & k1 & u2 & k2 & Eq1 & Eq2 & L1 & L2 & HV1).
        subst vc1; subst vc2.
        destruct Hdisj1 as [Hd1 | Hd1].
        { destruct Hd1 as (u1a & k1a & Eq1a & Hvu1 & Hfl1 & Hres1). inversion Eq1a; subst.
          destruct Hdisj2 as [Hd2 | Hd2].
          - destruct Hd2 as (u2a & k2a & Eq2a & Hvu2 & Hfl2 & Hres2). inversion Eq2a; subst.
            pose proof (IHyes l gamma1 gamma2 Hlc1 Hlc2 Henv) as HEy.
            unfold E in HEy.
            pose proof (E_protect2 l T (security_of T) k1a.(indirect_reader) k2a.(indirect_reader)
                          (subst_env gamma1 yes) (subst_env gamma2 yes) HEy) as Hprot.
            unfold E in Hprot.
            eapply V_mono.
            { apply protect_security_le; [apply security_le_refl |].
              apply flows_to_join.
              - destruct L1 as [_ Hk1]. exact Hk1.
              - destruct L2 as [_ Hk2]. exact Hk2. }
            { eapply Hprot; [exact Hres1 | exact Hres2 | exact Hv1 | exact Hv2]. }
          - destruct Hd2 as (u2a & k2a & Eq2a & _ & _ & _). inversion Eq2a. }
        { destruct Hd1 as (u1a & k1a & Eq1a & _ & _ & _). inversion Eq1a. }
      * destruct Hright as (u1 & k1 & u2 & k2 & Eq1 & Eq2 & L1 & L2 & HV1).
        subst vc1; subst vc2.
        destruct Hdisj1 as [Hd1 | Hd1].
        { destruct Hd1 as (u1a & k1a & Eq1a & _ & _ & _). inversion Eq1a. }
        { destruct Hd1 as (u1a & k1a & Eq1a & Hvu1 & Hfl1 & Hres1). inversion Eq1a; subst.
          destruct Hdisj2 as [Hd2 | Hd2].
          - destruct Hd2 as (u2a & k2a & Eq2a & _ & _ & _). inversion Eq2a.
          - destruct Hd2 as (u2a & k2a & Eq2a & Hvu2 & Hfl2 & Hres2). inversion Eq2a; subst.
            pose proof (IHno l gamma1 gamma2 Hlc1 Hlc2 Henv) as HEn.
            unfold E in HEn.
            pose proof (E_protect2 l T (security_of T) k1a.(indirect_reader) k2a.(indirect_reader)
                          (subst_env gamma1 no) (subst_env gamma2 no) HEn) as Hprot.
            unfold E in Hprot.
            eapply V_mono.
            { apply protect_security_le; [apply security_le_refl |].
              apply flows_to_join.
              - destruct L1 as [_ Hk1]. exact Hk1.
              - destruct L2 as [_ Hk2]. exact Hk2. }
            { eapply Hprot; [exact Hres1 | exact Hres2 | exact Hv1 | exact Hv2]. } }
    + apply V_opaque. intro Hf.
      assert (Hff : flows_to k.(indirect_reader) l).
      { rewrite protect_security_ir in Hf. eapply flows_to_join_r; exact Hf. }
      apply flows_to_b_spec in Hff. rewrite Hff in Eb. discriminate Eb.
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 HC Hg Htr Hnoflow.
  unfold same_result. intros v1 v2 Hev1 Hev2.
  destruct Hev1 as [Hm1 Hv1]. destruct Hev2 as [Hm2 Hv2].
  destruct HC as [L HC].
  set (l := (security_of T_result).(indirect_reader)).
  set (x := fresh (L ++ fvs_context C)).
  assert (HxL : ~ In x L).
  { intro Hx. apply (fresh_notin (L ++ fvs_context C)).
    apply in_or_app. left. exact Hx. }
  pose proof (HC x HxL) as Htyp.
  set (gamma1 := fun y => if Nat.eqb y x then t1 else tm_fvar y).
  set (gamma2 := fun y => if Nat.eqb y x then t2 else tm_fvar y).
  assert (Hlc1 : forall y, locally_closed (gamma1 y)).
  { intros y. unfold gamma1. destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. apply (has_type_lc empty t1 T_secret Ht1).
    - unfold locally_closed. simpl. trivial. }
  assert (Hlc2 : forall y, locally_closed (gamma2 y)).
  { intros y. unfold gamma2. destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. apply (has_type_lc empty t2 T_secret Ht2).
    - unfold locally_closed. simpl. trivial. }
  assert (Hagree1 : forall y, In y (fvs_context C) -> gamma1 y = tm_fvar y).
  { intros y Hy. unfold gamma1. destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. exfalso.
      apply (fresh_notin (L ++ fvs_context C)). apply in_or_app. right. exact Hy.
    - reflexivity. }
  assert (Hagree2 : forall y, In y (fvs_context C) -> gamma2 y = tm_fvar y).
  { intros y Hy. unfold gamma2. destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. exfalso.
      apply (fresh_notin (L ++ fvs_context C)). apply in_or_app. right. exact Hy.
    - reflexivity. }
  assert (Henv : forall (y : atom) (T' : ty),
             lookup_context y (update empty x T_secret) = Some T' ->
             E l T' (security_of T') (gamma1 y) (gamma2 y)).
  { intros y T' Hlook. destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst y. rewrite lookup_update_same in Hlook.
      inversion Hlook; subst T'.
      unfold gamma1, gamma2. rewrite Nat.eqb_refl. simpl.
      unfold E. intros a1 a2 Hma1 Hma2 Hva1 Hva2. apply V_opaque. exact Hnoflow.
    - apply Nat.eqb_neq in E.
      rewrite (lookup_update_other empty x y T_secret E) in Hlook.
      simpl in Hlook. discriminate Hlook. }
  pose proof (fundamental (update empty x T_secret) (plug C (tm_fvar x)) T_result Htyp
                l gamma1 gamma2 Hlc1 Hlc2 Henv) as HE.
  assert (Hs1 : subst_env gamma1 (plug C (tm_fvar x)) = plug C t1).
  { rewrite (subst_env_plug gamma1 C (tm_fvar x) Hagree1).
    simpl. unfold gamma1. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hs2 : subst_env gamma2 (plug C (tm_fvar x)) = plug C t2).
  { rewrite (subst_env_plug gamma2 C (tm_fvar x) Hagree2).
    simpl. unfold gamma2. rewrite Nat.eqb_refl. reflexivity. }
  rewrite Hs1 in HE. rewrite Hs2 in HE.
  unfold E in HE.
  pose proof (HE v1 v2 Hm1 Hm2 Hv1 Hv2) as HV.
  eapply V_erase.
  - exact Hg.
  - apply transparent_all_ir; [exact Htr | unfold l; apply flows_to_refl].
  - exact HV.
Qed.
