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

(* ============================================================= *)
(* Basic label / security lemmas                                  *)
(* ============================================================= *)

Lemma flows_to_refl : forall l, flows_to l l.
Proof. intros []; simpl; auto. Qed.

Lemma flows_to_trans : forall a b c, flows_to a b -> flows_to b c -> flows_to a c.
Proof. intros [] [] [] H1 H2; simpl in *; auto; contradiction. Qed.

Lemma flows_to_join_l : forall a b, flows_to a (join a b).
Proof. intros [] []; simpl; auto. Qed.

Lemma flows_to_join_r : forall a b, flows_to b (join a b).
Proof. intros [] []; simpl; auto. Qed.

Lemma flows_to_join_elim : forall a b c,
  flows_to (join a b) c -> flows_to a c /\ flows_to b c.
Proof. intros [] [] []; simpl in *; tauto. Qed.

Lemma join_low_r : forall l, join l Low = l.
Proof. intros []; reflexivity. Qed.

Lemma join_low_l : forall l, join Low l = l.
Proof. intros []; reflexivity. Qed.

Lemma join_idem : forall l, join l l = l.
Proof. intros []; reflexivity. Qed.

Lemma join_comm : forall a b, join a b = join b a.
Proof. intros [] []; reflexivity. Qed.

Lemma join_assoc : forall a b c, join (join a b) c = join a (join b c).
Proof. intros [] [] []; reflexivity. Qed.

Lemma join_mono : forall a b c d,
  flows_to a b -> flows_to c d -> flows_to (join a c) (join b d).
Proof. intros [] [] [] []; simpl in *; auto; contradiction. Qed.

Lemma security_le_refl : forall k, security_le k k.
Proof. intros [r i]; split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3] [H1 H2] [H3 H4]; simpl in *.
  split; eapply flows_to_trans; eauto.
Qed.

Lemma security_le_join : forall k1 k2 l1 l2,
  security_le k1 k2 -> flows_to l1 l2 ->
  security_le (protect_security k1 l1) (protect_security k2 l2).
Proof.
  intros [r1 i1] [r2 i2] l1 l2 [Hr Hi] Hl; simpl in *.
  split; apply join_mono; auto.
Qed.

Lemma protect_security_low : forall k, protect_security k Low = k.
Proof. intros [r i]; simpl; destruct r, i; reflexivity. Qed.

Lemma protect_security_join : forall k a b,
  protect_security (protect_security k a) b = protect_security k (join a b).
Proof. intros [r i] a b; simpl; destruct r, i, a, b; reflexivity. Qed.

Lemma join_le_elim : forall a b c,
  flows_to (join a b) c -> flows_to a c.
Proof. intros a b c H; apply (proj1 (flows_to_join_elim a b c H)). Qed.

Lemma join_le_elim_r : forall a b c,
  flows_to (join a b) c -> flows_to b c.
Proof. intros a b c H; apply (proj2 (flows_to_join_elim a b c H)). Qed.

Lemma join_upper_trans : forall a b c,
  flows_to (join a b) c -> flows_to a c.
Proof. apply join_le_elim. Qed.

(* ============================================================= *)
(* Values and their security annotations                          *)
(* ============================================================= *)

Definition value_sec (v : tm) : security :=
  match v with
  | tm_unit k => k
  | tm_abs _ _ k => k
  | tm_pair _ _ k => k
  | tm_inl _ k => k
  | tm_inr _ k => k
  | _ => public
  end.

Lemma protect_value_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l H; induction H; simpl; econstructor; eauto.
Qed.

Lemma protect_value_value_sec : forall v l,
  value v -> value_sec (protect_value v l) = protect_security (value_sec v) l.
Proof.
  intros v l H; destruct H; simpl; reflexivity.
Qed.

Lemma protect_value_pair_inv : forall a b k l,
  protect_value (tm_pair a b k) l = tm_pair a b (protect_security k l).
Proof. reflexivity. Qed.

Lemma protect_value_inl_inv : forall a k l,
  protect_value (tm_inl a k) l = tm_inl a (protect_security k l).
Proof. reflexivity. Qed.

Lemma protect_value_inr_inv : forall a k l,
  protect_value (tm_inr a k) l = tm_inr a (protect_security k l).
Proof. reflexivity. Qed.

Lemma protect_value_unit_inv : forall k l,
  protect_value (tm_unit k) l = tm_unit (protect_security k l).
Proof. reflexivity. Qed.

Lemma protect_value_abs_inv : forall T body k l,
  protect_value (tm_abs T body k) l = tm_abs T body (protect_security k l).
Proof. reflexivity. Qed.

Lemma protect_value_compose : forall v a b,
  protect_value (protect_value v a) b = protect_value v (join a b).
Proof.
  intros v a b; destruct v; simpl; try reflexivity;
  rewrite protect_security_join; reflexivity.
Qed.

(* ============================================================= *)
(* Hiddenness / bounds                                            *)
(* ============================================================= *)

Definition hidden_at (kappa : security) (T : ty) (p : label) : Prop :=
  ~ flows_to (join (security_of T).(indirect_reader) p) kappa.(indirect_reader).

Definition bound_at (T : ty) (p : label) (v : tm) : Prop :=
  security_le (value_sec v) (protect_security (security_of T) p).

(* ============================================================= *)
(* The logical relation                                           *)
(* ============================================================= *)

Fixpoint Vp (kappa : security) (T : ty) (p : label) (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_Unit k =>
      hidden_at kappa T p \/
      ((exists k1, v1 = tm_unit k1) /\ (exists k2, v2 = tm_unit k2) /\
       value_sec v1 = value_sec v2 /\
       bound_at T p v1 /\ bound_at T p v2)
  | Ty_Prod T1 T2 k =>
      hidden_at kappa T p \/
      (exists a1 b1 k1 a2 b2 k2,
        v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
        Vp kappa T1 Low a1 a2 /\ Vp kappa T2 Low b1 b2 /\
        value_sec v1 = value_sec v2 /\
        bound_at T p v1 /\ bound_at T p v2)
  | Ty_Sum T1 T2 k =>
      hidden_at kappa T p \/
      (((exists a1 k1 a2 k2,
           v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\
           Vp kappa T1 Low a1 a2)
        \/ (exists b1 k1 b2 k2,
           v1 = tm_inr b1 k1 /\ v2 = tm_inr b2 k2 /\
           Vp kappa T2 Low b1 b2))
       /\ value_sec v1 = value_sec v2 /\
       bound_at T p v1 /\ bound_at T p v2)
  | Ty_Arrow T1 T2 k =>
      hidden_at kappa T p \/
      ((exists Ta1 b1 ka1, v1 = tm_abs Ta1 b1 ka1) /\
       (exists Ta2 b2 ka2, v2 = tm_abs Ta2 b2 ka2) /\
       value_sec v1 = value_sec v2 /\
       (forall r, flows_to (join k.(reader) p) r ->
          forall u1 u2, value u1 -> value u2 -> Vp kappa T1 Low u1 u2 ->
          (hidden_at kappa T2 (join k.(indirect_reader) p) \/
           (forall w1 w2,
              tm_app v1 u1 r -->* w1 -> tm_app v2 u2 r -->* w2 ->
              value w1 -> value w2 ->
              Vp kappa T2 (join k.(indirect_reader) p) w1 w2)))
       /\ bound_at T p v1 /\ bound_at T p v2)
  end.

Definition Rp (kappa : security) (T : ty) (p : label) (t1 t2 : tm) : Prop :=
  hidden_at kappa T p \/
  (forall v1 v2, t1 -->* v1 -> t2 -->* v2 ->
     value v1 -> value v2 -> Vp kappa T p v1 v2).

Definition R (kappa : security) (T : ty) (t1 t2 : tm) : Prop :=
  Rp kappa T Low t1 t2.

Lemma R_unfold : forall kappa T t1 t2,
  R kappa T t1 t2 <->
  hidden_at kappa T Low \/
  (forall v1 v2, t1 -->* v1 -> t2 -->* v2 -> value v1 -> value v2 ->
     Vp kappa T Low v1 v2).
Proof. intros; reflexivity. Qed.

Lemma Rp_unfold : forall kappa T p t1 t2,
  Rp kappa T p t1 t2 <->
  hidden_at kappa T p \/
  (forall v1 v2, t1 -->* v1 -> t2 -->* v2 -> value v1 -> value v2 ->
     Vp kappa T p v1 v2).
Proof. intros; reflexivity. Qed.

(* ============================================================= *)
(* Environment substitution                                       *)
(* ============================================================= *)

Fixpoint subst_env (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit k => tm_unit k
  | tm_abs T body k => tm_abs T (subst_env rho body) k
  | tm_app t1 t2 r => tm_app (subst_env rho t1) (subst_env rho t2) r
  | tm_pair t1 t2 k => tm_pair (subst_env rho t1) (subst_env rho t2) k
  | tm_fst t1 r => tm_fst (subst_env rho t1) r
  | tm_snd t1 r => tm_snd (subst_env rho t1) r
  | tm_inl t1 k => tm_inl (subst_env rho t1) k
  | tm_inr t1 k => tm_inr (subst_env rho t1) k
  | tm_case t0 b1 b2 r =>
      tm_case (subst_env rho t0) (subst_env rho b1) (subst_env rho b2) r
  | tm_protect l t1 => tm_protect l (subst_env rho t1)
  | tm_if c y n r => tm_if (subst_env rho c) (subst_env rho y) (subst_env rho n) r
  end.

Definition env_rel (kappa : security) (Gamma : context)
    (rho1 rho2 : atom -> tm) : Prop :=
  (forall x, locally_closed (rho1 x)) /\
  (forall x, locally_closed (rho2 x)) /\
  (forall x T, lookup_context x Gamma = Some T -> R kappa T (rho1 x) (rho2 x)).

(* ============================================================= *)
(* Evaluation: basic facts and shape lemmas                       *)
(* ============================================================= *)

Lemma value_no_step : forall v, value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv. induction Hv; intros t Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    + eapply IHHv1; eauto.
    + eapply IHHv2; eauto.
  - inversion Hstep; subst. eapply IHHv; eauto.
  - inversion Hstep; subst. eapply IHHv; eauto.
Qed.

Lemma multi_value : forall v t, value v -> v -->* t -> t = v.
Proof.
  intros v t Hv Hm; induction Hm.
  - reflexivity.
  - exfalso; eapply value_no_step; eauto.
Qed.

Lemma multi_trans : forall t1 t2 t3,
  t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H; induction H; intros H'; auto.
  econstructor; eauto.
Qed.

Lemma eval_protect_gen : forall t w,
  t -->* w -> value w ->
  forall l x, t = tm_protect l x ->
    exists v, x -->* v /\ value v /\ w = protect_value v l.
Proof.
  intros t w Hm. induction Hm; intros Hval l x Heq.
  - subst. inversion Hval.
  - subst. inversion H; subst.
    + exists x. repeat split; auto.
      * apply multi_refl.
      * eapply multi_value; [apply protect_value_value; auto | exact Hm].
    + destruct (IHHm Hval l t' eq_refl) as [v [Hx [Hv Hw]]].
      exists v; repeat split; auto.
      eapply multi_step; eauto.
Qed.

Lemma eval_protect : forall l x w,
  tm_protect l x -->* w -> value w ->
  exists v, x -->* v /\ value v /\ w = protect_value v l.
Proof. intros; eapply eval_protect_gen; eauto. Qed.

Lemma eval_protect_value : forall l v w,
  value v -> tm_protect l v -->* w -> value w -> w = protect_value v l.
Proof.
  intros l v w Hv Hm Hw.
  destruct (eval_protect l v w Hm Hw) as [v' [Hp [Hv' Heq]]].
  rewrite (multi_value v v' Hv Hp) in Heq. exact Heq.
Qed.

Lemma eval_app_gen : forall t w,
  t -->* w -> value w ->
  forall a1 a2 ra, t = tm_app a1 a2 ra ->
    exists v1 v2, value v1 /\ value v2 /\ a1 -->* v1 /\ a2 -->* v2 /\
                  tm_app v1 v2 ra -->* w.
Proof.
  intros t w Hm. induction Hm; intros Hval a1 a2 ra Heq.
  - subst. inversion Hval.
  - subst. inversion H; subst.
    + exists (tm_abs T body kappa), a2. repeat split; auto; try (apply multi_refl).
      eapply multi_step with (t2 := tm_protect (indirect_reader kappa) (open body a2)); auto.
    + destruct (IHHm Hval t1' a2 ra eq_refl) as
        [v1 [v2 [Hv1 [Hv2 [H1 [H2 Happ]]]]]].
      exists v1, v2; repeat split; auto. eapply multi_step; eauto.
    + destruct (IHHm Hval a1 t2' ra eq_refl) as
        [v1 [v2 [Hv1 [Hv2 [H1 [H2 Happ]]]]]].
      exists v1, v2; repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma eval_app : forall t1 t2 r w,
  tm_app t1 t2 r -->* w -> value w ->
  exists v1 v2, value v1 /\ value v2 /\ t1 -->* v1 /\ t2 -->* v2 /\
                tm_app v1 v2 r -->* w.
Proof. intros; eapply eval_app_gen; eauto. Qed.

Lemma eval_pair_gen : forall t w,
  t -->* w -> value w ->
  forall a b k, t = tm_pair a b k ->
    exists v1 v2, value v1 /\ value v2 /\ a -->* v1 /\ b -->* v2 /\
                  w = tm_pair v1 v2 k.
Proof.
  intros t w Hm. induction Hm; intros Hval a b k Heq.
  - subst. inversion Hval; subst. exists a, b; repeat split; auto; apply multi_refl.
  - subst. inversion H; subst.
    + destruct (IHHm Hval t1' b k eq_refl) as
        [v1 [v2 [Hv1 [Hv2 [H1 [H2 Hw]]]]]].
      exists v1, v2; repeat split; auto. eapply multi_step; eauto.
    + destruct (IHHm Hval a t2' k eq_refl) as
        [v1 [v2 [Hv1 [Hv2 [H1 [H2 Hw]]]]]].
      exists v1, v2; repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma eval_pair : forall a b k w,
  tm_pair a b k -->* w -> value w ->
  exists v1 v2, value v1 /\ value v2 /\ a -->* v1 /\ b -->* v2 /\
                w = tm_pair v1 v2 k.
Proof. intros; eapply eval_pair_gen; eauto. Qed.

Lemma eval_fst_gen : forall t w,
  t -->* w -> value w ->
  forall s r, t = tm_fst s r ->
    exists v1 v2 k, value v1 /\ value v2 /\ s -->* tm_pair v1 v2 k /\
                    flows_to k.(reader) r /\ w = protect_value v1 k.(indirect_reader).
Proof.
  intros t w Hm. induction Hm; intros Hval s r Heq.
  - subst. inversion Hval.
  - subst. inversion H; subst.
    + exists v1, v2, kappa; repeat split; auto.
      * apply multi_refl.
      * eapply eval_protect_value; eauto.
    + destruct (IHHm Hval t' r eq_refl) as
        [v1 [v2 [k [Hv1 [Hv2 [Ht [Hf Hw]]]]]]].
      exists v1, v2, k; repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma eval_fst : forall t r w,
  tm_fst t r -->* w -> value w ->
  exists v1 v2 k, value v1 /\ value v2 /\ t -->* tm_pair v1 v2 k /\
                  flows_to k.(reader) r /\ w = protect_value v1 k.(indirect_reader).
Proof. intros; eapply eval_fst_gen; eauto. Qed.

Lemma eval_snd_gen : forall t w,
  t -->* w -> value w ->
  forall s r, t = tm_snd s r ->
    exists v1 v2 k, value v1 /\ value v2 /\ s -->* tm_pair v1 v2 k /\
                    flows_to k.(reader) r /\ w = protect_value v2 k.(indirect_reader).
Proof.
  intros t w Hm. induction Hm; intros Hval s r Heq.
  - subst. inversion Hval.
  - subst. inversion H; subst.
    + exists v1, v2, kappa; repeat split; auto.
      * apply multi_refl.
      * eapply eval_protect_value; eauto.
    + destruct (IHHm Hval t' r eq_refl) as
        [v1 [v2 [k [Hv1 [Hv2 [Ht [Hf Hw]]]]]]].
      exists v1, v2, k; repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma eval_snd : forall t r w,
  tm_snd t r -->* w -> value w ->
  exists v1 v2 k, value v1 /\ value v2 /\ t -->* tm_pair v1 v2 k /\
                  flows_to k.(reader) r /\ w = protect_value v2 k.(indirect_reader).
Proof. intros; eapply eval_snd_gen; eauto. Qed.

Lemma eval_inl_gen : forall t w,
  t -->* w -> value w ->
  forall s k, t = tm_inl s k ->
    exists v, value v /\ s -->* v /\ w = tm_inl v k.
Proof.
  intros t w Hm. induction Hm; intros Hval s k Heq.
  - subst. inversion Hval; subst. exists s; repeat split; auto; apply multi_refl.
  - subst. inversion H; subst.
    + destruct (IHHm Hval t' k eq_refl) as [v [Hv [Ht Hw]]].
      exists v; repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma eval_inl : forall t k w,
  tm_inl t k -->* w -> value w ->
  exists v, value v /\ t -->* v /\ w = tm_inl v k.
Proof. intros; eapply eval_inl_gen; eauto. Qed.

Lemma eval_inr_gen : forall t w,
  t -->* w -> value w ->
  forall s k, t = tm_inr s k ->
    exists v, value v /\ s -->* v /\ w = tm_inr v k.
Proof.
  intros t w Hm. induction Hm; intros Hval s k Heq.
  - subst. inversion Hval; subst. exists s; repeat split; auto; apply multi_refl.
  - subst. inversion H; subst.
    + destruct (IHHm Hval t' k eq_refl) as [v [Hv [Ht Hw]]].
      exists v; repeat split; auto. eapply multi_step; eauto.
Qed.

Lemma eval_inr : forall t k w,
  tm_inr t k -->* w -> value w ->
  exists v, value v /\ t -->* v /\ w = tm_inr v k.
Proof. intros; eapply eval_inr_gen; eauto. Qed.

Lemma eval_case_gen : forall t w,
  t -->* w -> value w ->
  forall s b1 b2 r, t = tm_case s b1 b2 r ->
  ((exists v k, value v /\ s -->* tm_inl v k /\ flows_to k.(reader) r /\
       (exists v', open b1 v -->* v' /\ value v' /\
                   w = protect_value v' k.(indirect_reader)))
   \/ (exists v k, value v /\ s -->* tm_inr v k /\ flows_to k.(reader) r /\
       (exists v', open b2 v -->* v' /\ value v' /\
                   w = protect_value v' k.(indirect_reader)))).
Proof.
  intros t w Hm. induction Hm; intros Hval s b1 b2 r Heq.
  - subst. inversion Hval.
  - subst. inversion H; subst.
    + left. exists v, kappa. repeat split; auto.
      * apply multi_refl.
      * destruct (eval_protect (indirect_reader kappa) (open b1 v) t3 Hm Hval)
          as [v' [Hp [Hv' Hw]]].
        exists v'. repeat split; auto.
    + right. exists v, kappa. repeat split; auto.
      * apply multi_refl.
      * destruct (eval_protect (indirect_reader kappa) (open b2 v) t3 Hm Hval)
          as [v' [Hp [Hv' Hw]]].
        exists v'. repeat split; auto.
    + destruct (IHHm Hval t' b1 b2 r eq_refl) as
        [[v [k [Hv [Ht [Hf [v' [Hp [Hv' Hw]]]]]]]]
        |[v [k [Hv [Ht [Hf [v' [Hp [Hv' Hw]]]]]]]]].
      * left. exists v, k. repeat split; auto.
        -- eapply multi_step; eauto.
        -- exists v'. repeat split; auto.
      * right. exists v, k. repeat split; auto.
        -- eapply multi_step; eauto.
        -- exists v'. repeat split; auto.
Qed.

Lemma eval_case : forall t b1 b2 r w,
  tm_case t b1 b2 r -->* w -> value w ->
  ((exists v k, value v /\ t -->* tm_inl v k /\ flows_to k.(reader) r /\
       (exists v', open b1 v -->* v' /\ value v' /\
                   w = protect_value v' k.(indirect_reader)))
   \/ (exists v k, value v /\ t -->* tm_inr v k /\ flows_to k.(reader) r /\
       (exists v', open b2 v -->* v' /\ value v' /\
                   w = protect_value v' k.(indirect_reader)))).
Proof. intros; eapply eval_case_gen; eauto. Qed.

Lemma eval_if_gen : forall t w,
  t -->* w -> value w ->
  forall c y n r, t = tm_if c y n r ->
  ((exists v k, value v /\ c -->* tm_inl v k /\ flows_to k.(reader) r /\
       (exists v', y -->* v' /\ value v' /\
                   w = protect_value v' k.(indirect_reader)))
   \/ (exists v k, value v /\ c -->* tm_inr v k /\ flows_to k.(reader) r /\
       (exists v', n -->* v' /\ value v' /\
                   w = protect_value v' k.(indirect_reader)))).
Proof.
  intros t w Hm. induction Hm; intros Hval c y n r Heq.
  - subst. inversion Hval.
  - subst. inversion H; subst.
    + (* ST_If *) destruct (IHHm Hval c' y n r eq_refl) as
        [[v [k [Hv [Ht [Hf [v' [Hp [Hv' Hw]]]]]]]]
        |[v [k [Hv [Ht [Hf [v' [Hp [Hv' Hw]]]]]]]]].
      * left. exists v, k. repeat split; auto.
        -- eapply multi_step; eauto.
        -- exists v'. repeat split; auto.
      * right. exists v, k. repeat split; auto.
        -- eapply multi_step; eauto.
        -- exists v'. repeat split; auto.
    + (* ST_IfTrue *) left. exists v, k. repeat split; auto.
      * apply multi_refl.
      * destruct (eval_protect (indirect_reader k) y t3 Hm Hval)
          as [v' [Hp [Hv' Hw]]].
        exists v'. repeat split; auto.
    + (* ST_IfFalse *) right. exists v, k. repeat split; auto.
      * apply multi_refl.
      * destruct (eval_protect (indirect_reader k) n t3 Hm Hval)
          as [v' [Hp [Hv' Hw]]].
        exists v'. repeat split; auto.
Qed.

Lemma eval_if : forall c y n r w,
  tm_if c y n r -->* w -> value w ->
  ((exists v k, value v /\ c -->* tm_inl v k /\ flows_to k.(reader) r /\
       (exists v', y -->* v' /\ value v' /\
                   w = protect_value v' k.(indirect_reader)))
   \/ (exists v k, value v /\ c -->* tm_inr v k /\ flows_to k.(reader) r /\
       (exists v', n -->* v' /\ value v' /\
                   w = protect_value v' k.(indirect_reader)))).
Proof. intros; eapply eval_if_gen; eauto. Qed.




(* ============================================================= *)
(* Monotonicity of hiddenness and bounds                          *)
(* ============================================================= *)

Lemma hidden_at_mono : forall kappa T p q,
  flows_to p q -> hidden_at kappa T p -> hidden_at kappa T q.
Proof.
  intros kappa T p q Hpq Hh Hf.
  apply Hh. unfold hidden_at in *.
  eapply flows_to_trans; [| exact Hf].
  apply join_mono; [apply flows_to_refl | exact Hpq].
Qed.

Lemma hidden_at_join_l : forall kappa T p q,
  hidden_at kappa T p -> hidden_at kappa T (join p q).
Proof. intros; apply hidden_at_mono with (p := p); auto; apply flows_to_join_l. Qed.

Lemma hidden_at_join_r : forall kappa T p q,
  hidden_at kappa T q -> hidden_at kappa T (join p q).
Proof. intros; apply hidden_at_mono with (p := q); auto; apply flows_to_join_r. Qed.

Lemma not_hidden_mono : forall kappa T p q,
  flows_to p q -> ~ hidden_at kappa T q -> ~ hidden_at kappa T p.
Proof. intros; intro Hh; apply H0; eapply hidden_at_mono; eauto. Qed.

Lemma bound_at_mono : forall T p q v,
  flows_to p q -> bound_at T p v -> bound_at T q v.
Proof.
  intros T p q v Hpq Hb. unfold bound_at in *.
  eapply security_le_trans; [exact Hb |].
  apply security_le_join; [apply security_le_refl | exact Hpq].
Qed.

Lemma bound_at_refl : forall T v, bound_at T Low v -> bound_at T Low v.
Proof. auto. Qed.

Lemma security_le_protect_r : forall k1 k2 l,
  security_le k1 k2 -> security_le k1 (protect_security k2 l).
Proof.
  intros k1 k2 l H; eapply security_le_trans; [exact H |].
  unfold security_le; simpl; split; apply flows_to_join_l.
Qed.

Lemma security_le_protect_join_r : forall k1 k2 p a,
  security_le k1 k2 ->
  security_le (protect_security k1 a) (protect_security k2 (join p a)).
Proof.
  intros; rewrite <- protect_security_join with (k := k2) (a := p) (b := a).
  apply security_le_join; [apply security_le_protect_r; exact H | apply flows_to_refl].
Qed.

(* ============================================================= *)
(* Value / evaluation construction lemmas                         *)
(* ============================================================= *)

Lemma value_abs_ann : forall T body k k',
  value (tm_abs T body k) -> value (tm_abs T body k').
Proof.
  intros T body k k' Hv; inversion Hv; subst.
  apply v_abs; assumption.
Qed.

Lemma multi_protect : forall x v l,
  x -->* v -> value v -> tm_protect l x -->* protect_value v l.
Proof.
  intros x v l Hm; induction Hm; intros Hv.
  - eapply multi_step; [apply ST_ProtectValue; exact Hv | apply multi_refl].
  - eapply multi_step; [apply ST_Protect; eauto | apply IHHm; auto].
Qed.

Lemma multi_app_arg : forall f t v r,
  value f -> t -->* v -> tm_app f t r -->* tm_app f v r.
Proof.
  intros f t v r Hf Hm; induction Hm.
  - apply multi_refl.
  - eapply multi_step; [apply ST_App2; eauto | apply IHHm].
Qed.

Lemma multi_app_value : forall T body k v r w,
  value (tm_abs T body k) -> value v -> flows_to k.(reader) r ->
  tm_app (tm_abs T body k) v r -->* w -> value w ->
  exists z, open body v -->* z /\ value z /\
            w = protect_value z k.(indirect_reader).
Proof.
  intros T body k v r w Hf Hv Hflow Hm Hval.
  inversion Hm; subst.
  - inversion Hval.
  - inversion H; subst.
    + destruct (eval_protect (indirect_reader k) (open body v) w H0 Hval)
        as [z [Hp [Hz Hw]]].
      exists z; repeat split; auto.
    + exfalso; eapply value_no_step with (v := tm_abs T body k); eauto.
    + exfalso; eapply value_no_step with (v := v); eauto.
Qed.

Lemma eval_protect_value_inv : forall l v w,
  value v -> tm_protect l v -->* w -> value w ->
  exists z, v -->* z /\ value z /\ w = protect_value z l.
Proof.
  intros l v w Hv Hm Hw; eapply eval_protect; eauto.
Qed.



Lemma eval_app_abs : forall f v r w,
  value f -> value v -> tm_app f v r -->* w -> value w ->
  exists T body k z, f = tm_abs T body k /\ flows_to k.(reader) r /\
    open body v -->* z /\ value z /\ w = protect_value z k.(indirect_reader).
Proof.
  intros f v r w Hf Hv Hm Hval.
  inversion Hm; subst.
  - inversion Hval.
  - inversion H; subst.
    + destruct (eval_protect (indirect_reader kappa) (open body v) w H0 Hval)
        as [z [Hp [Hz Hw]]].
      exists T, body, kappa, z; repeat split; auto.
    + exfalso; eapply value_no_step with (v := f); eauto.
    + exfalso; eapply value_no_step with (v := v); eauto.
Qed.

(* ============================================================= *)
(* Weakening the protection parameter                             *)
(* ============================================================= *)

Lemma Vp_Rp_weaken : forall kappa T,
  (forall p q v1 v2, flows_to p q -> Vp kappa T p v1 v2 -> Vp kappa T q v1 v2) /\
  (forall p q t1 t2, flows_to p q -> Rp kappa T p t1 t2 -> Rp kappa T q t1 t2).
Proof.
  intros kappa T.
  induction T as [k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k].
  - (* Unit *)
    assert (VpW : forall p q v1 v2,
      flows_to p q -> Vp kappa (Ty_Unit k) p v1 v2 -> Vp kappa (Ty_Unit k) q v1 v2).
    { intros p q v1 v2 Hpq H. destruct H as [Hh|Hs].
      - left; eapply hidden_at_mono; eauto.
      - right. destruct Hs as [H1 [H2 [Hann [Hb1 Hb2]]]].
        split; [exact H1 | split; [exact H2 | split; [exact Hann | split]]].
        + apply bound_at_mono with (p := p); auto.
        + apply bound_at_mono with (p := p); auto. }
    split; [exact VpW |].
    intros p q t1 t2 Hpq HR. destruct HR as [Hh|Hev].
    + left; eapply hidden_at_mono; eauto.
    + right; intros v1 v2 H1 H2 Hv1 Hv2. apply VpW with (p := p); auto.
  - (* Sum *)
    assert (VpW : forall p q v1 v2,
      flows_to p q -> Vp kappa (Ty_Sum T1 T2 k) p v1 v2 ->
      Vp kappa (Ty_Sum T1 T2 k) q v1 v2).
    { intros p q v1 v2 Hpq H. destruct H as [Hh|Hs].
      - left; eapply hidden_at_mono; eauto.
      - right. destruct Hs as [[Hinl|Hinr] [Hann [Hb1 Hb2]]].
        + split; [left; exact Hinl | split; [exact Hann | split]].
          * apply bound_at_mono with (p := p); auto.
          * apply bound_at_mono with (p := p); auto.
        + split; [right; exact Hinr | split; [exact Hann | split]].
          * apply bound_at_mono with (p := p); auto.
          * apply bound_at_mono with (p := p); auto. }
    split; [exact VpW |].
    intros p q t1 t2 Hpq HR. destruct HR as [Hh|Hev].
    + left; eapply hidden_at_mono; eauto.
    + right; intros v1 v2 H1 H2 Hv1 Hv2. apply VpW with (p := p); auto.
  - (* Prod *)
    assert (VpW : forall p q v1 v2,
      flows_to p q -> Vp kappa (Ty_Prod T1 T2 k) p v1 v2 ->
      Vp kappa (Ty_Prod T1 T2 k) q v1 v2).
    { intros p q v1 v2 Hpq H. destruct H as [Hh|Hs].
      - left; eapply hidden_at_mono; eauto.
      - right. destruct Hs as
          [a1 [b1 [k1 [a2 [b2 [k2 [Hv1 [Hv2 [HC1 [HC2 [Hann [Hb1 Hb2]]]]]]]]]]]].
        exists a1, b1, k1, a2, b2, k2.
        split; [exact Hv1 | split; [exact Hv2 | split; [exact HC1 | split; [exact HC2 | split; [exact Hann | split]]]]].
        + apply bound_at_mono with (p := p); auto.
        + apply bound_at_mono with (p := p); auto. }
    split; [exact VpW |].
    intros p q t1 t2 Hpq HR. destruct HR as [Hh|Hev].
    + left; eapply hidden_at_mono; eauto.
    + right; intros v1 v2 H1 H2 Hv1 Hv2. apply VpW with (p := p); auto.
  - (* Arrow *)
    assert (VpW : forall p q v1 v2,
      flows_to p q -> Vp kappa (Ty_Arrow T1 T2 k) p v1 v2 ->
      Vp kappa (Ty_Arrow T1 T2 k) q v1 v2).
    { intros p q v1 v2 Hpq H. destruct H as [Hh|Hs].
      - left; eapply hidden_at_mono; eauto.
      - right. destruct Hs as [Habs1 [Habs2 [Hann [Hext [Hb1 Hb2]]]]].
        split; [exact Habs1 | split; [exact Habs2 | split; [exact Hann | split]]].
        + intros r Hr u1 u2 Hvu1 Hvu2 Hrel.
          assert (Hr' : flows_to (join k.(reader) p) r).
          { eapply flows_to_trans; [| exact Hr].
            apply join_mono; [apply flows_to_refl | exact Hpq]. }
          apply (proj2 IH2) with (p := join k.(indirect_reader) p)
                                     (q := join k.(indirect_reader) q).
          * apply join_mono; [apply flows_to_refl | exact Hpq].
          * apply Hext with (r := r); auto.
        + split.
          * apply bound_at_mono with (p := p); auto.
          * apply bound_at_mono with (p := p); auto. }
    split; [exact VpW |].
    intros p q t1 t2 Hpq HR. destruct HR as [Hh|Hev].
    + left; eapply hidden_at_mono; eauto.
    + right; intros v1 v2 H1 H2 Hv1 Hv2. apply VpW with (p := p); auto.
Qed.


Lemma abs_multi_eq_gen : forall s t, s -->* t ->
  forall T body k, s = tm_abs T body k -> t = s.
Proof.
  intros s t Hm; induction Hm; intros T body k Heq.
  - reflexivity.
  - subst. exfalso; inversion H.
Qed.

Lemma abs_multi_eq : forall T body k t, tm_abs T body k -->* t -> t = tm_abs T body k.
Proof. intros; eapply abs_multi_eq_gen; eauto. Qed.


Lemma eval_app_protected : forall Ta b ka a u r w,
  value (tm_abs Ta b (protect_security ka a)) -> value u ->
  tm_app (tm_abs Ta b (protect_security ka a)) u r -->* w -> value w ->
  exists z, flows_to ka.(reader) r /\ open b u -->* z /\ value z /\
            w = protect_value z (join ka.(indirect_reader) a).
Proof.
  intros Ta b ka a u r w Hvf Hvu Hm Hval.
  destruct (eval_app_abs (tm_abs Ta b (protect_security ka a)) u r w
              Hvf Hvu Hm Hval) as
    [T' [body' [k' [z [Eabs [Hflow [Hopen [Hz Hw]]]]]]]].
  inversion Eabs; subst.
  simpl in Hflow.
  apply join_le_elim in Hflow.
  exists z; repeat split; auto.
Qed.

(* ============================================================= *)
(* Protecting values with a label                                 *)
(* ============================================================= *)

Lemma Vp_protect : forall kappa T p a v1 v2,
  Vp kappa T p v1 v2 ->
  Vp kappa T (join p a) (protect_value v1 a) (protect_value v2 a).
Proof.
  intros kappa T.
  induction T as [k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k];
  intros p a v1 v2 H.
  - (* Unit *)
    destruct H as [Hh|Hs].
    + left. apply hidden_at_mono with (p := p); auto. apply flows_to_join_l.
    + right. destruct Hs as [H1 [H2 [Hann [Hb1 Hb2]]]].
      destruct H1 as [k1 E1]; destruct H2 as [k2 E2].
      subst v1; subst v2. simpl in *.
      split.
      * exists (protect_security k1 a); reflexivity.
      * split.
        -- exists (protect_security k2 a); reflexivity.
        -- split.
           ++ rewrite Hann; reflexivity.
           ++ split.
              ** unfold bound_at; simpl.
                 rewrite <- protect_security_join with (k := k) (a := p) (b := a).
                 apply security_le_join; [exact Hb1 | apply flows_to_refl].
              ** unfold bound_at; simpl.
                 rewrite <- protect_security_join with (k := k) (a := p) (b := a).
                 apply security_le_join; [exact Hb2 | apply flows_to_refl].
  - (* Sum *)
    destruct H as [Hh|Hs].
    + left. apply hidden_at_mono with (p := p); auto. apply flows_to_join_l.
    + right. destruct Hs as [[Hinl|Hinr] [Hann [Hb1 Hb2]]].
      * destruct Hinl as [a1 [k1 [a2 [k2 [E1 [E2 Hrel]]]]]].
        subst v1; subst v2. simpl in *.
        split.
        -- left. exists a1, (protect_security k1 a), a2, (protect_security k2 a).
           repeat split; auto.
        -- split.
           ++ rewrite Hann; reflexivity.
           ++ split.
              ** unfold bound_at; simpl.
                 rewrite <- protect_security_join with (k := k) (a := p) (b := a).
                 apply security_le_join; [exact Hb1 | apply flows_to_refl].
              ** unfold bound_at; simpl.
                 rewrite <- protect_security_join with (k := k) (a := p) (b := a).
                 apply security_le_join; [exact Hb2 | apply flows_to_refl].
      * destruct Hinr as [b1 [k1 [b2 [k2 [E1 [E2 Hrel]]]]]].
        subst v1; subst v2. simpl in *.
        split.
        -- right. exists b1, (protect_security k1 a), b2, (protect_security k2 a).
           repeat split; auto.
        -- split.
           ++ rewrite Hann; reflexivity.
           ++ split.
              ** unfold bound_at; simpl.
                 rewrite <- protect_security_join with (k := k) (a := p) (b := a).
                 apply security_le_join; [exact Hb1 | apply flows_to_refl].
              ** unfold bound_at; simpl.
                 rewrite <- protect_security_join with (k := k) (a := p) (b := a).
                 apply security_le_join; [exact Hb2 | apply flows_to_refl].
  - (* Prod *)
    destruct H as [Hh|Hs].
    + left. apply hidden_at_mono with (p := p); auto. apply flows_to_join_l.
    + right. destruct Hs as
        [a1 [b1 [k1 [a2 [b2 [k2 [E1 [E2 [HC1 [HC2 [Hann [Hb1 Hb2]]]]]]]]]]]].
      subst v1; subst v2. simpl in *.
      exists a1, b1, (protect_security k1 a), a2, b2, (protect_security k2 a).
      split; [reflexivity|].
      split; [reflexivity|].
      split; [exact HC1|].
      split; [exact HC2|].
      split; [rewrite Hann; reflexivity|].
      split.
      * unfold bound_at; simpl.
        rewrite <- protect_security_join with (k := k) (a := p) (b := a).
        apply security_le_join; [exact Hb1 | apply flows_to_refl].
      * unfold bound_at; simpl.
        rewrite <- protect_security_join with (k := k) (a := p) (b := a).
        apply security_le_join; [exact Hb2 | apply flows_to_refl].
  - (* Arrow *)
    destruct H as [Hh|Hs].
    + left. apply hidden_at_mono with (p := p); auto. apply flows_to_join_l.
    + right. destruct Hs as [Habs1 [Habs2 [Hann [Hext [Hb1 Hb2]]]]].
      destruct Habs1 as [Ta1 [b1 [ka1 E1]]].
      destruct Habs2 as [Ta2 [b2 [ka2 E2]]].
      subst v1; subst v2. simpl in *.
      split.
      * exists Ta1, b1, (protect_security ka1 a); reflexivity.
      * split.
        -- exists Ta2, b2, (protect_security ka2 a); reflexivity.
        -- split.
           ++ rewrite Hann; reflexivity.
           ++ split.
              ** intros r Hr u1 u2 Hvu1 Hvu2 Hrel.
                 assert (Hr' : flows_to (join k.(reader) p) r).
                 { apply flows_to_trans with (b := join k.(reader) (join p a)).
                   + rewrite <- join_assoc. apply flows_to_join_l.
                   + exact Hr. }
                 destruct (Hext r Hr' u1 u2 Hvu1 Hvu2 Hrel) as [Hsrch|Hsrch].
                 { left. apply hidden_at_mono with (p := join k.(indirect_reader) p).
                   + rewrite <- join_assoc. apply flows_to_join_l.
                   + exact Hsrch. }
                 { right. intros z1 z2 Happ1 Happ2 Hvz1 Hvz2.
                   destruct (eval_app (tm_abs Ta1 b1 (protect_security ka1 a)) u1 r z1
                               Happ1 Hvz1) as
                     [f1 [w1 [Hvf1 [Hvw1 [Hf1 [Hw1 Happ1']]]]]].
                   assert (Ef1 : f1 = tm_abs Ta1 b1 (protect_security ka1 a)).
                   { eapply abs_multi_eq; eauto. }
                   assert (Ew1 : w1 = u1).
                   { eapply multi_value; eauto. }
                   subst f1; subst w1.
                   destruct (eval_app_protected Ta1 b1 ka1 a u1 r z1
                               Hvf1 Hvu1 Happ1' Hvz1) as
                     [z1' [Hflow1 [Hopen1 [Hz1' Hz1eq]]]].
                   destruct (eval_app (tm_abs Ta2 b2 (protect_security ka2 a)) u2 r z2
                               Happ2 Hvz2) as
                     [f2 [w2 [Hvf2 [Hvw2 [Hf2 [Hw2 Happ2']]]]]].
                   assert (Ef2 : f2 = tm_abs Ta2 b2 (protect_security ka2 a)).
                   { eapply abs_multi_eq; eauto. }
                   assert (Ew2 : w2 = u2).
                   { eapply multi_value; eauto. }
                   subst f2; subst w2.
                   destruct (eval_app_protected Ta2 b2 ka2 a u2 r z2
                               Hvf2 Hvu2 Happ2' Hvz2) as
                     [z2' [Hflow2 [Hopen2 [Hz2' Hz2eq]]]].
                   subst z1; subst z2.
                   assert (Hve1 : value (tm_abs Ta1 b1 ka1)).
                   { apply value_abs_ann with (k := protect_security ka1 a); auto. }
                   assert (Hve2 : value (tm_abs Ta2 b2 ka2)).
                   { apply value_abs_ann with (k := protect_security ka2 a); auto. }
                   assert (Hse1 : tm_app (tm_abs Ta1 b1 ka1) u1 r -->*
                                  protect_value z1' ka1.(indirect_reader)).
                   { eapply multi_trans.
                     - apply multi_step with
                         (t2 := tm_protect ka1.(indirect_reader) (open b1 u1)).
                       + apply ST_AppAbs; auto.
                       + apply multi_refl.
                     - eapply multi_protect; eauto. }
                   assert (Hse2 : tm_app (tm_abs Ta2 b2 ka2) u2 r -->*
                                  protect_value z2' ka2.(indirect_reader)).
                   { eapply multi_trans.
                     - apply multi_step with
                         (t2 := tm_protect ka2.(indirect_reader) (open b2 u2)).
                       + apply ST_AppAbs; auto.
                       + apply multi_refl.
                     - eapply multi_protect; eauto. }
                   assert (Hsrc : Vp kappa T2 (join k.(indirect_reader) p)
                              (protect_value z1' ka1.(indirect_reader))
                              (protect_value z2' ka2.(indirect_reader))).
                   { apply Hsrch.
                     - exact Hse1.
                     - exact Hse2.
                     - apply protect_value_value; exact Hz1'.
                     - apply protect_value_value; exact Hz2'. }
                   assert (Hprot : Vp kappa T2 (join (join k.(indirect_reader) p) a)
                              (protect_value (protect_value z1' ka1.(indirect_reader)) a)
                              (protect_value (protect_value z2' ka2.(indirect_reader)) a)).
                   { apply IH2 with (p := join k.(indirect_reader) p) (a := a).
                     exact Hsrc. }
                   rewrite <- join_assoc.
                   rewrite <- (protect_value_compose z1' ka1.(indirect_reader) a).
                   rewrite <- (protect_value_compose z2' ka2.(indirect_reader) a).
                   exact Hprot. }
              ** split.
                 *** unfold bound_at; simpl.
                     rewrite <- protect_security_join with (k := k) (a := p) (b := a).
                     apply security_le_join; [exact Hb1 | apply flows_to_refl].
                 *** unfold bound_at; simpl.
                     rewrite <- protect_security_join with (k := k) (a := p) (b := a).
                     apply security_le_join; [exact Hb2 | apply flows_to_refl].
Qed.


(* ============================================================= *)
(* Semantic subtyping                                             *)
(* ============================================================= *)

Lemma subtype_security_le : forall T U, subtype T U ->
  security_le (security_of T) (security_of U).
Proof.
  intros T U H; induction H; simpl; auto.
  eapply security_le_trans; eauto.
Qed.

Lemma hidden_transfer : forall kappa T U,
  security_le (security_of T) (security_of U) ->
  forall p q, flows_to p q -> hidden_at kappa T p -> hidden_at kappa U q.
Proof.
  intros kappa T U Hle p q Hpq Hh Hf.
  unfold hidden_at in *.
  apply Hh.
  eapply flows_to_trans; [| exact Hf].
  apply join_mono; [apply (proj2 Hle) | exact Hpq].
Qed.

Lemma bound_transfer : forall T U,
  security_le (security_of T) (security_of U) ->
  forall p q v, flows_to p q -> bound_at T p v -> bound_at U q v.
Proof.
  intros T U Hle p q v Hpq Hb.
  unfold bound_at in *.
  eapply security_le_trans.
  - exact Hb.
  - apply security_le_join; [exact Hle | exact Hpq].
Qed.

Lemma Rp_transfer : forall kappa T U,
  (forall p q, flows_to p q -> hidden_at kappa T p -> hidden_at kappa U q) ->
  (forall p q v1 v2, flows_to p q -> Vp kappa T p v1 v2 -> Vp kappa U q v1 v2) ->
  (forall p q t1 t2, flows_to p q -> Rp kappa T p t1 t2 -> Rp kappa U q t1 t2).
Proof.
  intros kappa T U Hh Hv p q t1 t2 Hpq HR.
  destruct HR as [Hhid|Hev].
  - left; eapply Hh; eauto.
  - right; intros v1 v2 H1 H2 Hv1 Hv2. apply Hv with (p := p) (q := q); auto.
Qed.

Lemma Vp_Rp_sub : forall kappa T U, subtype T U ->
  (forall p q v1 v2, flows_to p q -> Vp kappa T p v1 v2 -> Vp kappa U q v1 v2) /\
  (forall p q t1 t2, flows_to p q -> Rp kappa T p t1 t2 -> Rp kappa U q t1 t2).
Proof.
  intros kappa T U Hsub.
  induction Hsub as
    [k1 k2 Hwf1 Hwf2 Hle
    |T1 T2 U1 U2 k1 k2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hle
    |T1 T2 U1 U2 k1 k2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hle
    |T1 T2 U1 U2 k1 k2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hle
    |T U V Hsub1 IH1 Hsub2 IH2].
  - (* S_Unit *)
    assert (VpW : forall p q v1 v2,
      flows_to p q -> Vp kappa (Ty_Unit k1) p v1 v2 -> Vp kappa (Ty_Unit k2) q v1 v2).
    { intros p q v1 v2 Hpq H. destruct H as [Hh|Hs].
      - left. eapply hidden_transfer with (T := Ty_Unit k1); [exact Hle | exact Hpq | exact Hh].
      - right. destruct Hs as [H1 [H2 [Hann [Hb1 Hb2]]]].
        split; [exact H1 | split; [exact H2 | split; [exact Hann | split]]].
        + eapply bound_transfer with (T := Ty_Unit k1); [exact Hle | exact Hpq | exact Hb1].
        + eapply bound_transfer with (T := Ty_Unit k1); [exact Hle | exact Hpq | exact Hb2]. }
    split; [exact VpW |].
    apply Rp_transfer.
    + intros p q Hpq Hh. eapply hidden_transfer with (T := Ty_Unit k1); [exact Hle | exact Hpq | exact Hh].
    + exact VpW.
  - (* S_Sum *)
    assert (VpW : forall p q v1 v2,
      flows_to p q -> Vp kappa (Ty_Sum T1 T2 k1) p v1 v2 ->
      Vp kappa (Ty_Sum U1 U2 k2) q v1 v2).
    { intros p q v1 v2 Hpq H. destruct H as [Hh|Hs].
      - left. eapply hidden_transfer with (T := Ty_Sum T1 T2 k1); [exact Hle | exact Hpq | exact Hh].
      - right. destruct Hs as [[Hinl|Hinr] [Hann [Hb1 Hb2]]].
        + split; [left | split; [exact Hann | split]].
          * destruct Hinl as [a1 [ka [a2 [kb [E1 [E2 Hrel]]]]]].
            exists a1, ka, a2, kb. repeat split; auto.
            eapply (proj1 IH1) with (p := Low) (q := Low); auto.
            apply flows_to_refl.
          * eapply bound_transfer with (T := Ty_Sum T1 T2 k1); [exact Hle | exact Hpq | exact Hb1].
          * eapply bound_transfer with (T := Ty_Sum T1 T2 k1); [exact Hle | exact Hpq | exact Hb2].
        + split; [right | split; [exact Hann | split]].
          * destruct Hinr as [b1 [ka [b2 [kb [E1 [E2 Hrel]]]]]].
            exists b1, ka, b2, kb. repeat split; auto.
            eapply (proj1 IH2) with (p := Low) (q := Low); auto.
            apply flows_to_refl.
          * eapply bound_transfer with (T := Ty_Sum T1 T2 k1); [exact Hle | exact Hpq | exact Hb1].
          * eapply bound_transfer with (T := Ty_Sum T1 T2 k1); [exact Hle | exact Hpq | exact Hb2]. }
    split; [exact VpW |].
    apply Rp_transfer.
    + intros p q Hpq Hh. eapply hidden_transfer with (T := Ty_Sum T1 T2 k1); [exact Hle | exact Hpq | exact Hh].
    + exact VpW.
  - (* S_Prod *)
    assert (VpW : forall p q v1 v2,
      flows_to p q -> Vp kappa (Ty_Prod T1 T2 k1) p v1 v2 ->
      Vp kappa (Ty_Prod U1 U2 k2) q v1 v2).
    { intros p q v1 v2 Hpq H. destruct H as [Hh|Hs].
      - left. eapply hidden_transfer with (T := Ty_Prod T1 T2 k1); [exact Hle | exact Hpq | exact Hh].
      - right. destruct Hs as
          [a1 [b1 [ka [a2 [b2 [kb [E1 [E2 [HC1 [HC2 [Hann [Hb1 Hb2]]]]]]]]]]]].
        exists a1, b1, ka, a2, b2, kb.
        split; [exact E1|].
        split; [exact E2|].
        split.
        + eapply (proj1 IH1) with (p := Low) (q := Low); auto. apply flows_to_refl.
        + split.
          * eapply (proj1 IH2) with (p := Low) (q := Low); auto. apply flows_to_refl.
          * split; [exact Hann|]. split.
            -- eapply bound_transfer with (T := Ty_Prod T1 T2 k1); [exact Hle | exact Hpq | exact Hb1].
            -- eapply bound_transfer with (T := Ty_Prod T1 T2 k1); [exact Hle | exact Hpq | exact Hb2]. }
    split; [exact VpW |].
    apply Rp_transfer.
    + intros p q Hpq Hh. eapply hidden_transfer with (T := Ty_Prod T1 T2 k1); [exact Hle | exact Hpq | exact Hh].
    + exact VpW.
  - (* S_Arrow *)
    assert (VpW : forall p q v1 v2,
      flows_to p q -> Vp kappa (Ty_Arrow T1 T2 k1) p v1 v2 ->
      Vp kappa (Ty_Arrow U1 U2 k2) q v1 v2).
    { intros p q v1 v2 Hpq H. destruct H as [Hh|Hs].
      - left. eapply hidden_transfer with (T := Ty_Arrow T1 T2 k1); [exact Hle | exact Hpq | exact Hh].
      - right. destruct Hs as [Habs1 [Habs2 [Hann [Hext [Hb1 Hb2]]]]].
        split; [exact Habs1|]. split; [exact Habs2|]. split; [exact Hann|]. split.
        + intros r Hr u1 u2 Hvu1 Hvu2 Hrel.
          assert (Hrel' : Vp kappa T1 Low u1 u2).
          { eapply (proj1 IH1) with (p := Low) (q := Low); auto. apply flows_to_refl. }
          assert (Hr' : flows_to (join k1.(reader) p) r).
          { eapply flows_to_trans; [| exact Hr].
            apply join_mono; [apply (proj1 Hle) | exact Hpq]. }
          eapply (proj2 IH2) with (p := join k1.(indirect_reader) p)
                                     (q := join k2.(indirect_reader) q).
          * apply join_mono; [apply (proj2 Hle) | exact Hpq].
          * apply Hext with (r := r); auto.
        + split.
          * eapply bound_transfer with (T := Ty_Arrow T1 T2 k1); [exact Hle | exact Hpq | exact Hb1].
          * eapply bound_transfer with (T := Ty_Arrow T1 T2 k1); [exact Hle | exact Hpq | exact Hb2]. }
    split; [exact VpW |].
    apply Rp_transfer.
    + intros p q Hpq Hh. eapply hidden_transfer with (T := Ty_Arrow T1 T2 k1); [exact Hle | exact Hpq | exact Hh].
    + exact VpW.
  - (* S_Trans *)
    assert (VpW : forall p q v1 v2,
      flows_to p q -> Vp kappa T p v1 v2 -> Vp kappa V q v1 v2).
    { intros p q v1 v2 Hpq H.
      eapply (proj1 IH2) with (p := q) (q := q); [apply flows_to_refl |].
      eapply (proj1 IH1) with (p := p) (q := q); eauto. }
    split; [exact VpW |].
    apply Rp_transfer.
    + intros p q Hpq Hh.
      eapply hidden_transfer with (T := T); [ | exact Hpq | exact Hh].
      apply security_le_trans with (k2 := security_of U).
      * apply subtype_security_le. exact Hsub1.
      * apply subtype_security_le. exact Hsub2.
    + exact VpW.
Qed.

(* ============================================================= *)
(* Relating ty_protect, V and R                                   *)
(* ============================================================= *)

Lemma Vp_ty_protect : forall kappa T p v1 v2,
  Vp kappa (ty_protect p T) Low v1 v2 <-> Vp kappa T p v1 v2.
Proof.
  intros kappa T p v1 v2; destruct T; simpl;
  unfold hidden_at, bound_at; simpl;
  rewrite ?protect_security_join, ?join_low_r; reflexivity.
Qed.

Lemma R_ty_protect : forall kappa T p t1 t2,
  R kappa (ty_protect p T) t1 t2 <-> Rp kappa T p t1 t2.
Proof.
  intros kappa T p t1 t2. unfold R, Rp.
  assert (Hh : hidden_at kappa (ty_protect p T) Low <-> hidden_at kappa T p).
  { destruct T; unfold hidden_at; simpl;
    rewrite ?protect_security_join, ?join_low_r; reflexivity. }
  assert (Hv : forall v1 v2,
    Vp kappa (ty_protect p T) Low v1 v2 <-> Vp kappa T p v1 v2)
    by (intros; apply Vp_ty_protect).
  destruct Hh as [Hh1 Hh2]; split; intros [H|H].
  - left; apply Hh1; exact H.
  - right; intros v1 v2 H1 H2 Hv1 Hv2; apply Hv; auto.
  - left; apply Hh2; exact H.
  - right; intros v1 v2 H1 H2 Hv1 Hv2; apply Hv; auto.
Qed.

Lemma Vp_to_R : forall kappa T v1 v2,
  value v1 -> value v2 -> Vp kappa T Low v1 v2 -> R kappa T v1 v2.
Proof.
  intros kappa T v1 v2 Hv1 Hv2 HV. right.
  intros w1 w2 H1 H2 Hw1 Hw2.
  rewrite (multi_value v1 w1 Hv1 H1).
  rewrite (multi_value v2 w2 Hv2 H2).
  exact HV.
Qed.

Lemma R_protect_wrap : forall kappa T p l t1 t2,
  Rp kappa T p t1 t2 ->
  Rp kappa T (join p l) (tm_protect l t1) (tm_protect l t2).
Proof.
  intros kappa T p l t1 t2 HR. destruct HR as [Hh|Hev].
  - left. apply hidden_at_mono with (p := p); auto. apply flows_to_join_l.
  - right. intros w1 w2 H1 H2 Hw1 Hw2.
    destruct (eval_protect l t1 w1 H1 Hw1) as [z1 [Hz1 [Hvz1 Hw1']]].
    destruct (eval_protect l t2 w2 H2 Hw2) as [z2 [Hz2 [Hvz2 Hw2']]].
    rewrite Hw1'; rewrite Hw2'.
    apply Vp_protect with (p := p); auto.
Qed.


(* ============================================================= *)
(* Environment substitution: opening and extension                *)
(* ============================================================= *)

Lemma open_rec_lc_at : forall body k,
  lc_at k body -> forall j w, k <= j -> open_rec j w body = body.
Proof.
  intros body; induction body as
    [i | y | k0 | T body IH | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 k0
    | t1 IH1 r | t1 IH1 r | t1 IH1 k0 | t1 IH1 k0
    | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH | c IHc y IH1 n IH2 r];
  intros k Hlc j w Hkj; simpl in *.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E; subst i.
      pose proof (Nat.lt_le_trans j k j Hlc Hkj) as Hcontra.
      apply Nat.lt_irrefl in Hcontra. destruct Hcontra.
    + rewrite E; reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH; auto.
  - rewrite IH1, IH2; auto.
  - rewrite IH1, IH2; auto.
  - rewrite IH; auto.
  - rewrite IH; auto.
  - rewrite IH; auto.
  - rewrite IH; auto.
  - rewrite IH0, IH1, IH2; auto.
  - rewrite IH; auto.
  - rewrite IH0, IH1, IH2; auto.
Qed.

Lemma open_rec_lc : forall body,
  locally_closed body -> forall j w, open_rec j w body = body.
Proof. intros body H; apply open_rec_lc_at with (k := 0); auto. Qed.

Lemma subst_env_open_rec : forall body rho k x,
  (forall y, locally_closed (rho y)) ->
  subst_env rho (open_rec k (tm_fvar x) body) =
  open_rec k (rho x) (subst_env rho body).
Proof.
  intros body. induction body as
    [i | y | k0 | T body IH | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 k0
    | t1 IH1 r | t1 IH1 r | t1 IH1 k0 | t1 IH1 k0
    | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH | c IHc y IH1 n IH2 r];
  intros rho k x Hlc; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - apply open_rec_lc. auto.
  - reflexivity.
  - rewrite IH; auto.
  - rewrite IH1, IH2; auto.
  - rewrite IH1, IH2; auto.
  - rewrite IH; auto.
  - rewrite IH; auto.
  - rewrite IH; auto.
  - rewrite IH; auto.
  - rewrite IH0, IH1, IH2; auto.
  - rewrite IH; auto.
  - rewrite IH0, IH1, IH2; auto.
Qed.

Lemma subst_env_open : forall body rho x,
  (forall y, locally_closed (rho y)) ->
  subst_env rho (open body (tm_fvar x)) = open (subst_env rho body) (rho x).
Proof. intros; apply subst_env_open_rec. Qed.

Definition extend (rho : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else rho y.

Lemma extend_eq : forall rho x u, extend rho x u x = u.
Proof. intros; unfold extend; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma extend_neq : forall rho x y u, x <> y -> extend rho x u y = rho y.
Proof. intros rho x y u H; unfold extend; apply Nat.eqb_neq in H; rewrite H; reflexivity. Qed.

Lemma subst_env_extend_notin : forall t rho x u,
  ~ In x (fv t) -> subst_env (extend rho x u) t = subst_env rho t.
Proof.
  intros t; induction t; intros rho x u Hnotin; simpl in *; auto.
  - (* fvar a *) unfold extend. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst a; exfalso; apply Hnotin; simpl; auto.
    + reflexivity.
  - (* app *) rewrite IHt1, IHt2; auto.
    + intro H; apply Hnotin; apply in_or_app; left; exact H.
    + intro H; apply Hnotin; apply in_or_app; right; exact H.
  - (* pair *) rewrite IHt1, IHt2; auto.
    + intro H; apply Hnotin; apply in_or_app; left; exact H.
    + intro H; apply Hnotin; apply in_or_app; right; exact H.
  - (* case *) rewrite IHt0, IHt1, IHt2; auto.
    + intro H; apply Hnotin; apply in_or_app; left; exact H.
    + intro H. apply Hnotin. apply in_or_app. right. apply in_or_app. left. exact H.
    + intro H. apply Hnotin. apply in_or_app. right. apply in_or_app. right. exact H.
  - (* if *) rewrite IHt0, IHt1, IHt2; auto.
    + intro H; apply Hnotin; apply in_or_app; left; exact H.
    + intro H. apply Hnotin. apply in_or_app. right. apply in_or_app. left. exact H.
    + intro H. apply Hnotin. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

(* Free variables of a program context (its fixed parts) *)
Fixpoint fv_context (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ => fv_context C'
  | C_AppLeft C' t2 _ => fv_context C' ++ fv t2
  | C_AppRight t1 C' _ => fv t1 ++ fv_context C'
  | C_PairLeft C' t2 _ => fv_context C' ++ fv t2
  | C_PairRight t1 C' _ => fv t1 ++ fv_context C'
  | C_Fst C' _ => fv_context C'
  | C_Snd C' _ => fv_context C'
  | C_Inl C' _ => fv_context C'
  | C_Inr C' _ => fv_context C'
  | C_CaseScrutinee C' b1 b2 _ => fv_context C' ++ fv b1 ++ fv b2
  | C_CaseLeft t0 C' b2 _ => fv t0 ++ fv_context C' ++ fv b2
  | C_CaseRight t0 b1 C' _ => fv t0 ++ fv b1 ++ fv_context C'
  | C_Protect _ C' => fv_context C'
  | C_IfCondition C' y n _ => fv_context C' ++ fv y ++ fv n
  | C_IfThen c C' n _ => fv c ++ fv_context C' ++ fv n
  | C_IfElse c y C' _ => fv c ++ fv y ++ fv_context C'
  end.

Lemma subst_env_id : forall t rho,
  (forall y, In y (fv t) -> rho y = tm_fvar y) ->
  subst_env rho t = t.
Proof.
  intros t; induction t; intros rho H; simpl in *; auto.
  - (* fvar a *) apply H; simpl; auto.
  - (* app *) rewrite IHt1, IHt2; auto.
    + intros y Hy; apply H; apply in_or_app; left; exact Hy.
    + intros y Hy; apply H; apply in_or_app; right; exact Hy.
  - (* pair *) rewrite IHt1, IHt2; auto.
    + intros y Hy; apply H; apply in_or_app; left; exact Hy.
    + intros y Hy; apply H; apply in_or_app; right; exact Hy.
  - (* case *) rewrite IHt0, IHt1, IHt2; auto.
    + intros y Hy; apply H; apply in_or_app; left; exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. left. exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. right. exact Hy.
  - (* if *) rewrite IHt0, IHt1, IHt2; auto.
    + intros y Hy; apply H; apply in_or_app; left; exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. left. exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. right. exact Hy.
Qed.

Lemma plug_subst_env : forall C s rho,
  (forall y, In y (fv_context C) -> rho y = tm_fvar y) ->
  subst_env rho (plug C s) = plug C (subst_env rho s).
Proof.
  intros C; induction C; intros s rho H; simpl in *;
  try (rewrite IHC; auto; fail); auto.
  - (* C_Hole *) reflexivity.
  - (* C_Abs *) rewrite IHC; auto.
  - (* C_AppLeft *) rewrite IHC; auto. rewrite subst_env_id; auto.
    intros y Hy; apply H. apply in_or_app; right; exact Hy.
  - (* C_AppRight *) rewrite IHC; auto. rewrite subst_env_id; auto.
    intros y Hy; apply H. apply in_or_app; left; exact Hy.
  - (* C_PairLeft *) rewrite IHC; auto. rewrite subst_env_id; auto.
    intros y Hy; apply H. apply in_or_app; right; exact Hy.
  - (* C_PairRight *) rewrite IHC; auto. rewrite subst_env_id; auto.
    intros y Hy; apply H. apply in_or_app; left; exact Hy.
  - (* CaseScrutinee *) rewrite IHC; auto.
    rewrite subst_env_id; auto. rewrite subst_env_id; auto.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. left. exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. right. exact Hy.
    + intros y Hy; apply H. apply in_or_app. left. exact Hy.
  - (* CaseLeft *) rewrite IHC; auto.
    rewrite subst_env_id; auto. rewrite subst_env_id; auto.
    + intros y Hy; apply H. apply in_or_app. left. exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. left. exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. right. exact Hy.
  - (* CaseRight *) rewrite IHC; auto.
    rewrite subst_env_id; auto. rewrite subst_env_id; auto.
    + intros y Hy; apply H. apply in_or_app. left; exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. right. exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. left. exact Hy.
  - (* IfCondition *) rewrite IHC; auto.
    rewrite subst_env_id; auto. rewrite subst_env_id; auto.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. left. exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. right. exact Hy.
    + intros y Hy; apply H. apply in_or_app. left. exact Hy.
  - (* IfThen *) rewrite IHC; auto.
    rewrite subst_env_id; auto. rewrite subst_env_id; auto.
    + intros y Hy; apply H. apply in_or_app. left. exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. right. exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. left. exact Hy.
  - (* IfElse *) rewrite IHC; auto.
    rewrite subst_env_id; auto. rewrite subst_env_id; auto.
    + intros y Hy; apply H. apply in_or_app. left; exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. left. exact Hy.
    + intros y Hy; apply H. apply in_or_app. right. apply in_or_app. right. exact Hy.
Qed.

(* ============================================================= *)
(* Fresh atoms and context lookup                                 *)
(* ============================================================= *)

Definition fresh (L : list atom) : atom :=
  fold_right (fun x acc => Nat.max (S x) acc) 0 L.

Lemma in_lt_fresh : forall L m, In m L -> m < fresh L.
Proof.
  intros L; induction L as [|a L IH]; intros m Hin.
  - contradiction.
  - simpl in *. destruct Hin as [->|Hin].
    + eapply Nat.lt_le_trans; [apply Nat.lt_succ_diag_r | apply Nat.le_max_l].
    + eapply Nat.lt_le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_spec : forall L, ~ In (fresh L) L.
Proof.
  intros L Hin. pose proof (in_lt_fresh L (fresh L) Hin).
  apply Nat.lt_irrefl in H. exact H.
Qed.

Lemma lookup_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof.
  intros Gamma x T; simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_update_neq : forall Gamma x y T,
  x <> y -> lookup_context x (update Gamma y T) = lookup_context x Gamma.
Proof.
  intros Gamma x y T H; simpl. apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma lookup_empty_none : forall x, lookup_context x empty = None.
Proof. intros x; reflexivity. Qed.


(* ============================================================= *)
(* Values and typing imply local closure                          *)
(* ============================================================= *)

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; induction H; simpl; auto.
  - apply IHH1.
  - apply IHH.
Qed.

Lemma lc_open_rec : forall body k x,
  lc_at k (open_rec k (tm_fvar x) body) -> lc_at (S k) body.
Proof.
  intros body; induction body as
    [i | y | k0 | T body IH | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 k0
    | t1 IH1 r | t1 IH1 r | t1 IH1 k0 | t1 IH1 k0
    | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH | c IHc y IH1 n IH2 r];
  intros k x Hlc; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst i. apply Nat.lt_succ_diag_r.
    + apply Nat.lt_lt_succ_r; exact Hlc.
  - exact I.
  - exact I.
  - apply IH with (k := S k); auto.
  - split.
    + apply IH1 with (k := k); apply Hlc.
    + apply IH2 with (k := k); apply Hlc.
  - split.
    + apply IH1 with (k := k); apply Hlc.
    + apply IH2 with (k := k); apply Hlc.
  - apply IH with (k := k); exact Hlc.
  - apply IH with (k := k); exact Hlc.
  - apply IH with (k := k); exact Hlc.
  - apply IH with (k := k); exact Hlc.
  - split; [apply IH0 with (k := k); apply Hlc | split].
    + apply IH1 with (k := S k); apply Hlc.
    + apply IH2 with (k := S k); apply Hlc.
  - apply IH with (k := k); exact Hlc.
  - split; [apply IHc with (k := k); apply Hlc | split].
    + apply IH1 with (k := k); apply Hlc.
    + apply IH2 with (k := k); apply Hlc.
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H. induction H; simpl; auto.
  - (* T_Abs *)
    apply lc_open_rec with (k := 0) (x := fresh L).
    apply H0. apply fresh_spec.
  - (* T_App *) split; auto.
  - (* T_Pair *) split; auto.
  - (* T_Fst *) auto.
  - (* T_Snd *) auto.
  - (* T_Inl *) auto.
  - (* T_Inr *) auto.
  - (* T_Case *)
    split; [auto | split].
    + apply lc_open_rec with (k := 0) (x := fresh (L ++ fv b2)).
      apply H1. intro Hin; apply fresh_spec in Hin.
      apply Hin. apply in_or_app; left. exact Hin.
    + apply lc_open_rec with (k := 0) (x := fresh (L ++ fv b1)).
      apply H2. intro Hin; apply fresh_spec in Hin.
      apply Hin. apply in_or_app; left. exact Hin.
  - (* T_Protect *) auto.
  - (* T_Sub *) auto.
  - (* T_If *) split; [auto | split; auto].
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
