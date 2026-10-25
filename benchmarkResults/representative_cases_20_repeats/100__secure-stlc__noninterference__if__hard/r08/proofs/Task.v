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

(* ================================================================= *)
(* Basic label, security and type lemmas                             *)
(* ================================================================= *)

Lemma flows_to_refl : forall l : label, flows_to l l.
Proof. intros []; simpl; trivial. Qed.

Lemma flows_to_trans : forall a b c : label,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. intros [] [] []; simpl in *; intuition. Qed.

Lemma flows_to_low_l : forall l : label, flows_to Low l.
Proof. intros []; simpl; trivial. Qed.

Lemma not_flows_to_high_low : ~ flows_to High Low.
Proof. simpl; tauto. Qed.

Lemma flows_to_join_l : forall a b : label, flows_to a (join a b).
Proof. intros [] []; simpl; trivial. Qed.

Lemma flows_to_join_r : forall a b : label, flows_to b (join a b).
Proof. intros [] []; simpl; trivial. Qed.

Lemma join_mono : forall a b c d : label,
  flows_to a b -> flows_to c d -> flows_to (join a c) (join b d).
Proof. intros [] [] [] []; simpl in *; intuition. Qed.

Lemma security_le_refl : forall k : security, security_le k k.
Proof. intros [r i]; simpl; split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3 : security,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3]; simpl.
  intros [Hr1 Hi1] [Hr2 Hi2]; split; eapply flows_to_trans; eauto.
Qed.

Lemma security_le_protect : forall k : security, forall l : label,
  security_le k (protect_security k l).
Proof.
  intros [r i] l; simpl; split; apply flows_to_join_l.
Qed.

Lemma protect_security_mono : forall k1 k2 : security, forall l1 l2 : label,
  security_le k1 k2 -> flows_to l1 l2 ->
  security_le (protect_security k1 l1) (protect_security k2 l2).
Proof.
  intros [r1 i1] [r2 i2] l1 l2 [Hr Hi] Hl; simpl in *.
  split; eapply join_mono; eauto.
Qed.

Lemma security_of_ty_protect : forall l T,
  security_of (ty_protect l T) = protect_security (security_of T) l.
Proof.
  intros l [k | T1 T2 k | T1 T2 k | T1 T2 k]; reflexivity.
Qed.

Lemma erase_type_ty_protect : forall l T,
  erase_type (ty_protect l T) = erase_type T.
Proof.
  intros l [k | T1 T2 k | T1 T2 k | T1 T2 k]; reflexivity.
Qed.

Lemma erase_security_protect_value : forall v l,
  erase_security (protect_value v l) = erase_security v.
Proof. intros v l; destruct v; simpl; reflexivity. Qed.

Lemma erase_security_protect : forall l t,
  erase_security (tm_protect l t) = erase_security t.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* Fresh atoms                                                       *)
(* ================================================================= *)

Fixpoint max_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => Nat.max x (max_list xs')
  end.

Definition fresh (xs : list nat) : nat := S (max_list xs).

Lemma max_list_bound : forall xs x, In x xs -> x <= max_list xs.
Proof.
  induction xs as [| y ys IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [<- | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall xs, ~ In (fresh xs) xs.
Proof.
  intros xs Hin. unfold fresh in Hin.
  pose proof (max_list_bound xs (S (max_list xs)) Hin). lia.
Qed.

(* ================================================================= *)
(* Locally closed terms                                              *)
(* ================================================================= *)

Lemma lc_at_mono : forall t k k', k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  induction t as
    [ i | x | kappa | T body IHbody kappa
    | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 kappa
    | t1 IH1 r | t1 IH1 r | t1 IH1 kappa | t1 IH1 kappa
    | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y IHy n IHn r ];
    intros k k' Hle H; simpl in *.
  - lia.
  - exact I.
  - exact I.
  - apply (IHbody (S k) (S k')); [lia | exact H].
  - destruct H as [H1 H2]; split.
    + apply (IH1 k k'); [lia | exact H1].
    + apply (IH2 k k'); [lia | exact H2].
  - destruct H as [H1 H2]; split.
    + apply (IH1 k k'); [lia | exact H1].
    + apply (IH2 k k'); [lia | exact H2].
  - apply (IH1 k k'); [lia | exact H].
  - apply (IH1 k k'); [lia | exact H].
  - apply (IH1 k k'); [lia | exact H].
  - apply (IH1 k k'); [lia | exact H].
  - destruct H as [H0 [H1 H2]]. split.
    + apply (IH0 k k'); [lia | exact H0].
    + split.
      * apply (IH1 (S k) (S k')); [lia | exact H1].
      * apply (IH2 (S k) (S k')); [lia | exact H2].
  - apply (IH1 k k'); [lia | exact H].
  - destruct H as [H0 [H1 H2]]. split.
    + apply (IHc k k'); [lia | exact H0].
    + split.
      * apply (IHy k k'); [lia | exact H1].
      * apply (IHn k k'); [lia | exact H2].
Qed.

Lemma open_rec_lc : forall k m t u, k <= m -> lc_at k t -> open_rec m u t = t.
Proof.
  intros k m t u. revert k m.
  induction t as
    [ i | x | kappa | T body IHbody kappa
    | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 kappa
    | t1 IH1 r | t1 IH1 r | t1 IH1 kappa | t1 IH1 kappa
    | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y IHy n IHn r ];
    intros k m Hle H; simpl in *.
  - destruct (Nat.eqb m i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. apply (IHbody (S k) (S m)); [lia | exact H].
  - destruct H as [H1 H2]. rewrite (IH1 k m Hle H1), (IH2 k m Hle H2). reflexivity.
  - destruct H as [H1 H2]. rewrite (IH1 k m Hle H1), (IH2 k m Hle H2). reflexivity.
  - rewrite (IH1 k m Hle H). reflexivity.
  - rewrite (IH1 k m Hle H). reflexivity.
  - rewrite (IH1 k m Hle H). reflexivity.
  - rewrite (IH1 k m Hle H). reflexivity.
  - destruct H as [H0 [H1 H2]]. assert (Hle' : S k <= S m) by lia.
    rewrite (IH0 k m Hle H0), (IH1 (S k) (S m) Hle' H1), (IH2 (S k) (S m) Hle' H2).
    reflexivity.
  - rewrite (IH1 k m Hle H). reflexivity.
  - destruct H as [H0 [H1 H2]].
    rewrite (IHc k m Hle H0), (IHy k m Hle H1), (IHn k m Hle H2).
    reflexivity.
Qed.

Lemma open_rec_lc0 : forall m t u, lc_at 0 t -> open_rec m u t = t.
Proof. intros m t u H. apply open_rec_lc with (k:=0); [lia | exact H]. Qed.

Lemma lc_open_fvar_inv : forall n body x,
  lc_at n (open_rec n (tm_fvar x) body) -> lc_at (S n) body.
Proof.
  intros n body. revert n.
  induction body as
    [ i | y | kappa | T b IHb kappa
    | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 kappa
    | t1 IH1 r | t1 IH1 r | t1 IH1 kappa | t1 IH1 kappa
    | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y IHy nf IHnf r ];
    intros n x H; simpl in *.
  - destruct (Nat.eqb n i) eqn:E; simpl in *.
    + apply Nat.eqb_eq in E. lia.
    + lia.
  - exact I.
  - exact I.
  - apply (IHb (S n) x). exact H.
  - destruct H as [H1 H2]. split.
    + apply (IH1 n x). exact H1.
    + apply (IH2 n x). exact H2.
  - destruct H as [H1 H2]. split.
    + apply (IH1 n x). exact H1.
    + apply (IH2 n x). exact H2.
  - apply (IH1 n x). exact H.
  - apply (IH1 n x). exact H.
  - apply (IH1 n x). exact H.
  - apply (IH1 n x). exact H.
  - destruct H as [H0 [H1 H2]]. split.
    + apply (IH0 n x). exact H0.
    + split.
      * apply (IH1 (S n) x). exact H1.
      * apply (IH2 (S n) x). exact H2.
  - apply (IH1 n x). exact H.
  - destruct H as [H0 [H1 H2]]. split.
    + apply (IHc n x). exact H0.
    + split.
      * apply (IHy n x). exact H1.
      * apply (IHnf n x). exact H2.
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H. induction H as
    [ Gamma0 x T0 Hlook Hwf
    | Gamma0 kappa Hwf
    | L Gamma0 T1 body T2 kappa HwfT1 Hwfkappa Hbody IHbody
    | Gamma0 t1 t2 T1 T2 kappa r Ht1 IHt1 Ht2 IHt2 Hflow
    | Gamma0 t1 t2 T1 T2 kappa Ht1 IHt1 Ht2 IHt2 Hwf
    | Gamma0 t T1 T2 kappa r Ht IHt Hflow
    | Gamma0 t T1 T2 kappa r Ht IHt Hflow
    | Gamma0 t T1 T2 kappa Ht IHt HwfT2 Hwfkappa
    | Gamma0 t T1 T2 kappa HwfT1 Ht IHt Hwfkappa
    | L Gamma0 t body1 body2 T1 T2 T0 kappa r Ht IHt Hflow Hbody1 IHbody1 Hbody2 IHbody2
    | Gamma0 t T0 lp Ht IHt
    | Gamma0 t T0 U Ht IHt Hsub
    | Gamma0 c yes no k T0 r Hc IHc Hyes IHyes Hno IHno Hflow ].
  - simpl. exact I.
  - simpl. exact I.
  - simpl. set (x := fresh L). assert (Hx : ~ In x L) by apply fresh_notin.
    apply (lc_open_fvar_inv 0 body x). apply IHbody; exact Hx.
  - simpl. split; [exact IHt1 | exact IHt2].
  - simpl. split; [exact IHt1 | exact IHt2].
  - simpl. exact IHt.
  - simpl. exact IHt.
  - simpl. exact IHt.
  - simpl. exact IHt.
  - simpl. split; [exact IHt | split].
    + set (x := fresh (L ++ fv body1)).
      assert (Hx : ~ In x L).
      { intro Hin. pose proof (fresh_notin (L ++ fv body1)) as Hni.
        apply Hni. apply in_or_app. left. exact Hin. }
      apply (lc_open_fvar_inv 0 body1 x). apply IHbody1; exact Hx.
    + set (x := fresh (L ++ fv body2)).
      assert (Hx : ~ In x L).
      { intro Hin. pose proof (fresh_notin (L ++ fv body2)) as Hni.
        apply Hni. apply in_or_app. left. exact Hin. }
      apply (lc_open_fvar_inv 0 body2 x). apply IHbody2; exact Hx.
  - simpl. exact IHt.
  - simpl. exact IHt.
  - simpl. split; [exact IHc | split; [exact IHyes | exact IHno]].
Qed.


(* ================================================================= *)
(* Environment substitution                                          *)
(* ================================================================= *)

Fixpoint subst_env (s : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => s x
  | tm_unit kappa => tm_unit kappa
  | tm_abs T body kappa => tm_abs T (subst_env s body) kappa
  | tm_app t1 t2 r => tm_app (subst_env s t1) (subst_env s t2) r
  | tm_pair t1 t2 kappa => tm_pair (subst_env s t1) (subst_env s t2) kappa
  | tm_fst t1 r => tm_fst (subst_env s t1) r
  | tm_snd t1 r => tm_snd (subst_env s t1) r
  | tm_inl t1 kappa => tm_inl (subst_env s t1) kappa
  | tm_inr t1 kappa => tm_inr (subst_env s t1) kappa
  | tm_case t0 b1 b2 r =>
      tm_case (subst_env s t0) (subst_env s b1) (subst_env s b2) r
  | tm_protect l t1 => tm_protect l (subst_env s t1)
  | tm_if c y n r => tm_if (subst_env s c) (subst_env s y) (subst_env s n) r
  end.

Lemma notin_app_l : forall (x : atom) (a b : list atom),
  ~ In x (a ++ b) -> ~ In x a.
Proof.
  intros x a b H Hin. apply H. apply in_or_app. left. exact Hin.
Qed.

Lemma notin_app_r : forall (x : atom) (a b : list atom),
  ~ In x (a ++ b) -> ~ In x b.
Proof.
  intros x a b H Hin. apply H. apply in_or_app. right. exact Hin.
Qed.

Ltac solve_notin H :=
  intro Hc; apply H; simpl; repeat rewrite in_app_iff; tauto.

Lemma subst_env_id : forall (s : atom -> tm) (t : tm),
  (forall y, In y (fv t) -> s y = tm_fvar y) ->
  subst_env s t = t.
Proof.
  intros s t. revert s.
  induction t as
    [ i | x | kappa | T body IHbody kappa
    | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 kappa
    | t1 IH1 r | t1 IH1 r | t1 IH1 kappa | t1 IH1 kappa
    | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y IHy n IHn r ];
    intros s H; simpl in *.
  - reflexivity.
  - apply H. simpl. left. reflexivity.
  - reflexivity.
  - f_equal. apply IHbody. intros y Hy. apply H. simpl. exact Hy.
  - f_equal.
    + apply IH1. intros y Hy. apply H. simpl. apply in_or_app. left. exact Hy.
    + apply IH2. intros y Hy. apply H. simpl. apply in_or_app. right. exact Hy.
  - f_equal.
    + apply IH1. intros y Hy. apply H. simpl. apply in_or_app. left. exact Hy.
    + apply IH2. intros y Hy. apply H. simpl. apply in_or_app. right. exact Hy.
  - f_equal. apply IH1. intros y Hy. apply H. simpl. exact Hy.
  - f_equal. apply IH1. intros y Hy. apply H. simpl. exact Hy.
  - f_equal. apply IH1. intros y Hy. apply H. simpl. exact Hy.
  - f_equal. apply IH1. intros y Hy. apply H. simpl. exact Hy.
  - f_equal.
    + apply IH0. intros y Hy. apply H. simpl. repeat rewrite in_app_iff. tauto.
    + apply IH1. intros y Hy. apply H. simpl. repeat rewrite in_app_iff. tauto.
    + apply IH2. intros y Hy. apply H. simpl. repeat rewrite in_app_iff. tauto.
  - f_equal. apply IH1. intros y Hy. apply H. simpl. exact Hy.
  - f_equal.
    + apply IHc. intros z Hz. apply H. simpl. repeat rewrite in_app_iff. tauto.
    + apply IHy. intros z Hz. apply H. simpl. repeat rewrite in_app_iff. tauto.
    + apply IHn. intros z Hz. apply H. simpl. repeat rewrite in_app_iff. tauto.
Qed.

Lemma subst_env_single_id : forall (x : atom) (t u : tm),
  ~ In x (fv u) ->
  subst_env (fun y => if Nat.eqb y x then t else tm_fvar y) u = u.
Proof.
  intros x t u Hnin. apply subst_env_id. intros y Hy.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. exfalso. apply Hnin. exact Hy.
  - reflexivity.
Qed.

Lemma subst_env_open_rec : forall (s : atom -> tm) (x : atom) (w body : tm) (k : nat),
  (forall y, y <> x -> locally_closed (s y)) ->
  ~ In x (fv body) ->
  subst_env (fun y => if Nat.eqb y x then w else s y)
    (open_rec k (tm_fvar x) body)
  = open_rec k w (subst_env s body).
Proof.
  intros s x w body. revert s x w.
  induction body as
    [ i | y | kappa | T b IHb kappa
    | t1 IH1 t2 IH2 r | t1 IH1 t2 IH2 kappa
    | t1 IH1 r | t1 IH1 r | t1 IH1 kappa | t1 IH1 kappa
    | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y IHy n IHn r ];
    intros s x w k Hlc Hnin; simpl in *.
  - destruct (Nat.eqb k i) eqn:E; simpl.
    + rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply Hnin. simpl. left. reflexivity.
    + rewrite open_rec_lc0.
      * reflexivity.
      * apply Hlc. intro Heq. apply Nat.eqb_neq in E. apply E. exact Heq.
  - reflexivity.
  - f_equal. apply IHb; [exact Hlc | exact Hnin].
  - f_equal.
    + apply IH1; [exact Hlc | solve_notin Hnin].
    + apply IH2; [exact Hlc | solve_notin Hnin].
  - f_equal.
    + apply IH1; [exact Hlc | solve_notin Hnin].
    + apply IH2; [exact Hlc | solve_notin Hnin].
  - f_equal. apply IH1; [exact Hlc | exact Hnin].
  - f_equal. apply IH1; [exact Hlc | exact Hnin].
  - f_equal. apply IH1; [exact Hlc | exact Hnin].
  - f_equal. apply IH1; [exact Hlc | exact Hnin].
  - f_equal.
    + apply IH0; [exact Hlc | solve_notin Hnin].
    + apply IH1; [exact Hlc | solve_notin Hnin].
    + apply IH2; [exact Hlc | solve_notin Hnin].
  - f_equal. apply IH1; [exact Hlc | exact Hnin].
  - f_equal.
    + apply IHc; [exact Hlc | solve_notin Hnin].
    + apply IHy; [exact Hlc | solve_notin Hnin].
    + apply IHn; [exact Hlc | solve_notin Hnin].
Qed.

(* ================================================================= *)
(* Atoms of a program context                                        *)
(* ================================================================= *)

Fixpoint ctx_atoms (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs T C' kappa => ctx_atoms C'
  | C_AppLeft C' t2 r => ctx_atoms C' ++ fv t2
  | C_AppRight t1 C' r => fv t1 ++ ctx_atoms C'
  | C_PairLeft C' t2 kappa => ctx_atoms C' ++ fv t2
  | C_PairRight t1 C' kappa => fv t1 ++ ctx_atoms C'
  | C_Fst C' r => ctx_atoms C'
  | C_Snd C' r => ctx_atoms C'
  | C_Inl C' kappa => ctx_atoms C'
  | C_Inr C' kappa => ctx_atoms C'
  | C_CaseScrutinee C' b1 b2 r => ctx_atoms C' ++ fv b1 ++ fv b2
  | C_CaseLeft t0 C' b2 r => fv t0 ++ ctx_atoms C' ++ fv b2
  | C_CaseRight t0 b1 C' r => fv t0 ++ fv b1 ++ ctx_atoms C'
  | C_Protect l C' => ctx_atoms C'
  | C_IfCondition C' y n r => ctx_atoms C' ++ fv y ++ fv n
  | C_IfThen c C' n r => fv c ++ ctx_atoms C' ++ fv n
  | C_IfElse c y C' r => fv c ++ fv y ++ ctx_atoms C'
  end.

Lemma in_fv_plug : forall (C : program_context) (x y : atom),
  In y (fv (plug C (tm_fvar x))) <-> In y (ctx_atoms C) \/ y = x.
Proof.
  induction C as
    [ | T C' IHC kappa
    | C' IHC t2 r | t1 C' IHC r
    | C' IHC t2 kappa | t1 C' IHC kappa
    | C' IHC r | C' IHC r | C' IHC kappa | C' IHC kappa
    | C' IHC b1 b2 r | t0 C' IHC b2 r | t0 b1 C' IHC r
    | l C' IHC
    | C' IHC y n r | c C' IHC n r | c y C' IHC r ];
    intros x z; simpl.
  - simpl. firstorder.
  - apply IHC.
  - repeat rewrite in_app_iff. rewrite IHC. firstorder.
  - repeat rewrite in_app_iff. rewrite IHC. firstorder.
  - repeat rewrite in_app_iff. rewrite IHC. firstorder.
  - repeat rewrite in_app_iff. rewrite IHC. firstorder.
  - apply IHC.
  - apply IHC.
  - apply IHC.
  - apply IHC.
  - repeat rewrite in_app_iff. rewrite IHC. firstorder.
  - repeat rewrite in_app_iff. rewrite IHC. firstorder.
  - repeat rewrite in_app_iff. rewrite IHC. firstorder.
  - apply IHC.
  - repeat rewrite in_app_iff. rewrite IHC. firstorder.
  - repeat rewrite in_app_iff. rewrite IHC. firstorder.
  - repeat rewrite in_app_iff. rewrite IHC. firstorder.
Qed.

Lemma subst_env_plug_hole : forall (C : program_context) (x : atom) (t : tm),
  ~ In x (ctx_atoms C) ->
  subst_env (fun y => if Nat.eqb y x then t else tm_fvar y)
    (plug C (tm_fvar x)) = plug C t.
Proof.
  induction C as
    [ | T C' IHC kappa
    | C' IHC t2 r | t1 C' IHC r
    | C' IHC t2 kappa | t1 C' IHC kappa
    | C' IHC r | C' IHC r | C' IHC kappa | C' IHC kappa
    | C' IHC b1 b2 r | t0 C' IHC b2 r | t0 b1 C' IHC r
    | l C' IHC
    | C' IHC y0 n r | c C' IHC n r | c y0 C' IHC r ];
    intros x t Hnin; simpl in *.
  - rewrite Nat.eqb_refl. reflexivity.
  - f_equal. apply IHC. exact Hnin.
  - f_equal.
    + apply IHC. solve_notin Hnin.
    + apply subst_env_single_id. solve_notin Hnin.
  - f_equal.
    + apply subst_env_single_id. solve_notin Hnin.
    + apply IHC. solve_notin Hnin.
  - f_equal.
    + apply IHC. solve_notin Hnin.
    + apply subst_env_single_id. solve_notin Hnin.
  - f_equal.
    + apply subst_env_single_id. solve_notin Hnin.
    + apply IHC. solve_notin Hnin.
  - f_equal. apply IHC. exact Hnin.
  - f_equal. apply IHC. exact Hnin.
  - f_equal. apply IHC. exact Hnin.
  - f_equal. apply IHC. exact Hnin.
  - f_equal.
    + apply IHC. solve_notin Hnin.
    + apply subst_env_single_id. solve_notin Hnin.
    + apply subst_env_single_id. solve_notin Hnin.
  - f_equal.
    + apply subst_env_single_id. solve_notin Hnin.
    + apply IHC. solve_notin Hnin.
    + apply subst_env_single_id. solve_notin Hnin.
  - f_equal.
    + apply subst_env_single_id. solve_notin Hnin.
    + apply subst_env_single_id. solve_notin Hnin.
    + apply IHC. solve_notin Hnin.
  - f_equal. apply IHC. exact Hnin.
  - f_equal.
    + apply IHC. solve_notin Hnin.
    + apply subst_env_single_id. solve_notin Hnin.
    + apply subst_env_single_id. solve_notin Hnin.
  - f_equal.
    + apply subst_env_single_id. solve_notin Hnin.
    + apply IHC. solve_notin Hnin.
    + apply subst_env_single_id. solve_notin Hnin.
  - f_equal.
    + apply subst_env_single_id. solve_notin Hnin.
    + apply subst_env_single_id. solve_notin Hnin.
    + apply IHC. solve_notin Hnin.
Qed.


(* ================================================================= *)
(* Values and multi-step evaluation                                  *)
(* ================================================================= *)

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv as
    [ kappa | T body kappa Hlc | v1 v2 kappa H1 IH1 H2 IH2
    | v kappa H IH | v kappa H IH ].
  - simpl. exact I.
  - exact Hlc.
  - simpl. split; assumption.
  - simpl. exact IH.
  - simpl. exact IH.
Qed.

Lemma value_no_step : forall v t, value v -> ~ (v --> t).
Proof.
  intros v t Hv. revert t. induction Hv as
    [ kappa | T body kappa Hlc | v1 v2 kappa H1 IH1 H2 IH2
    | v kappa H IH | v kappa H IH ];
    intros t Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    + match goal with H : v1 --> ?x |- False => exact (IH1 x H) end.
    + match goal with H : v2 --> ?x |- False => exact (IH2 x H) end.
  - inversion Hstep; subst.
    match goal with H : v --> ?x |- False => exact (IH x H) end.
  - inversion Hstep; subst.
    match goal with H : v --> ?x |- False => exact (IH x H) end.
Qed.

Lemma value_protect_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv. destruct v; simpl; try exact Hv;
    inversion Hv; subst; constructor; assumption.
Qed.

Lemma abs_no_step : forall T b k t, ~ (tm_abs T b k --> t).
Proof. intros T b k t H; inversion H. Qed.

Lemma multi_trans : forall t1 t2 t3, t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H. induction H as [ t | a b c Hst Hm IH ]; intros H23.
  - exact H23.
  - apply multi_step with b; [exact Hst | apply IH; exact H23].
Qed.

Lemma multi_stuck : forall t u, (forall v, ~ (t --> v)) -> t -->* u -> u = t.
Proof.
  intros t u Hns H. induction H as [ t0 | a b c Hst Hm IH ].
  - reflexivity.
  - exfalso. exact (Hns b Hst).
Qed.

Lemma multi_value_eq : forall v u, value v -> v -->* u -> u = v.
Proof.
  intros v u Hv H. apply multi_stuck with (t:=v); [| exact H].
  intros w Hstep. exact (value_no_step v w Hv Hstep).
Qed.

Lemma step_protect_dec : forall (l : label) (t t' : tm),
  tm_protect l t --> t' ->
  (value t /\ t' = protect_value t l) \/
  (exists t'', t --> t'' /\ t' = tm_protect l t'').
Proof.
  intros l t t' H. inversion H; subst.
  - left. split; eauto.
  - right. eexists. split; eauto.
Qed.

Lemma step_pair_dec : forall (a b : tm) (k : security) (t' : tm),
  tm_pair a b k --> t' ->
  (exists a', a --> a' /\ t' = tm_pair a' b k) \/
  (exists b', value a /\ b --> b' /\ t' = tm_pair a b' k).
Proof.
  intros a b k t' H. inversion H; subst.
  - left. eexists. split; eauto.
  - right. eexists. split; eauto.
Qed.

Lemma step_inl_dec : forall (a : tm) (k : security) (t' : tm),
  tm_inl a k --> t' -> exists a', a --> a' /\ t' = tm_inl a' k.
Proof.
  intros a k t' H. inversion H; subst. eexists. split; eauto.
Qed.

Lemma step_inr_dec : forall (a : tm) (k : security) (t' : tm),
  tm_inr a k --> t' -> exists a', a --> a' /\ t' = tm_inr a' k.
Proof.
  intros a k t' H. inversion H; subst. eexists. split; eauto.
Qed.

Lemma step_fst_dec : forall (t : tm) (r : label) (t' : tm),
  tm_fst t r --> t' ->
  (exists v1 v2 k, t = tm_pair v1 v2 k /\ value v1 /\ value v2 /\
      flows_to k.(reader) r /\ t' = tm_protect k.(indirect_reader) v1)
  \/ (exists t'', t --> t'' /\ t' = tm_fst t'' r).
Proof.
  intros t r t' H. inversion H; subst.
  - left. eexists. eexists. eexists. repeat split; eauto.
  - right. eexists. split; eauto.
Qed.

Lemma step_snd_dec : forall (t : tm) (r : label) (t' : tm),
  tm_snd t r --> t' ->
  (exists v1 v2 k, t = tm_pair v1 v2 k /\ value v1 /\ value v2 /\
      flows_to k.(reader) r /\ t' = tm_protect k.(indirect_reader) v2)
  \/ (exists t'', t --> t'' /\ t' = tm_snd t'' r).
Proof.
  intros t r t' H. inversion H; subst.
  - left. eexists. eexists. eexists. repeat split; eauto.
  - right. eexists. split; eauto.
Qed.

Lemma step_case_dec : forall (t b1 b2 : tm) (r : label) (t' : tm),
  tm_case t b1 b2 r --> t' ->
  (exists v k, t = tm_inl v k /\ value v /\ flows_to k.(reader) r /\
      t' = tm_protect k.(indirect_reader) (open b1 v))
  \/ (exists v k, t = tm_inr v k /\ value v /\ flows_to k.(reader) r /\
      t' = tm_protect k.(indirect_reader) (open b2 v))
  \/ (exists t'', t --> t'' /\ t' = tm_case t'' b1 b2 r).
Proof.
  intros t b1 b2 r t' H. inversion H; subst.
  - left. eexists. eexists. repeat split; eauto.
  - right. left. eexists. eexists. repeat split; eauto.
  - right. right. eexists. split; eauto.
Qed.

Lemma step_if_dec : forall (c y n : tm) (r : label) (t' : tm),
  tm_if c y n r --> t' ->
  (exists v k, c = tm_inl v k /\ value v /\ flows_to k.(reader) r /\
      t' = tm_protect k.(indirect_reader) y)
  \/ (exists v k, c = tm_inr v k /\ value v /\ flows_to k.(reader) r /\
      t' = tm_protect k.(indirect_reader) n)
  \/ (exists c', c --> c' /\ t' = tm_if c' y n r).
Proof.
  intros c y n r t' H. inversion H; subst.
  - right. right. eexists. split; eauto.
  - left. eexists. eexists. repeat split; eauto.
  - right. left. eexists. eexists. repeat split; eauto.
Qed.

Lemma multi_protect_inv : forall (l : label) (t v : tm),
  tm_protect l t -->* v -> value v ->
  exists w, t -->* w /\ value w /\ v = protect_value w l.
Proof.
  intros l t v H Hv.
  remember (tm_protect l t) as s eqn:Es.
  revert l t Es.
  induction H as [ s0 | s1 s2 s3 Hst Hm IH ]; intros l0 t0 Es.
  - subst s0. inversion Hv.
  - subst s1.
    destruct (step_protect_dec l0 t0 s2 Hst) as [[Hval Heq] | (t' & Hstep & Heq)].
    + subst s2. exists t0. split; [apply multi_refl | split; [exact Hval | ]].
      apply multi_value_eq; [apply value_protect_value; exact Hval | exact Hm].
    + subst s2. edestruct (IH Hv l0 t' eq_refl) as (w & Htw & Hvw & Heq2).
      exists w. split.
      * apply multi_step with (t2 := t'); [exact Hstep | exact Htw].
      * split; [exact Hvw | exact Heq2].
Qed.

Lemma step_app_dec : forall (f a : tm) (r : label) (t' : tm),
  tm_app f a r --> t' ->
  (exists (T : ty) (b : tm) (k : security) (av : tm),
      f = tm_abs T b k /\ value (tm_abs T b k) /\ value av /\ a = av /\
      flows_to k.(reader) r /\ t' = tm_protect k.(indirect_reader) (open b av))
  \/ (exists f', f --> f' /\ t' = tm_app f' a r)
  \/ (exists a', value f /\ a --> a' /\ t' = tm_app f a' r).
Proof.
  intros f a r t H. inversion H; subst.
  - left. exists T. exists body. exists kappa. exists a. repeat split; auto.
  - right. left. exists t1'. split; [assumption | reflexivity].
  - right. right. exists t2'. repeat split; auto.
Qed.

Lemma multi_app_inv : forall (f a : tm) (r : label) (v : tm),
  tm_app f a r -->* v -> value v ->
  exists (T : ty) (b av : tm) (k : security),
    f -->* tm_abs T b k /\ value (tm_abs T b k) /\
    a -->* av /\ value av /\ flows_to k.(reader) r /\
    tm_protect k.(indirect_reader) (open b av) -->* v.
Proof.
  intros f a r v H Hv.
  remember (tm_app f a r) as s eqn:Es.
  revert f a r Es.
  induction H as [ s0 | s1 s2 s3 Hst Hm IH ]; intros f0 a0 r0 Es.
  - subst s0. inversion Hv.
  - subst s1.
    destruct (step_app_dec f0 a0 r0 s2 Hst) as
      [ (T & b & k & av & Hf & Hvabs & Hvav & Ha & Hflow & Hs2)
      | [ (f' & Hstep & Hs2) | (a' & Hvf & Hstep & Hs2) ] ].
    + subst s2. rewrite Hf, Ha.
      exists T, b, av, k. repeat split; try assumption; apply multi_refl.
    + subst s2.
      edestruct (IH Hv f' a0 r0 eq_refl) as (T2 & b2 & av2 & k2 & Hf2 & Hvf2 & Ha2 & Hva2 & Hflow2 & Htail2).
      exists T2, b2, av2, k2. repeat split; try assumption.
      apply multi_step with (t2 := f'); [exact Hstep | exact Hf2].
    + subst s2.
      edestruct (IH Hv f0 a' r0 eq_refl) as (T2 & b2 & av2 & k2 & Hf2 & Hvf2 & Ha2 & Hva2 & Hflow2 & Htail2).
      exists T2, b2, av2, k2. repeat split; try assumption.
      apply multi_step with (t2 := a'); [exact Hstep | exact Ha2].
Qed.

Lemma multi_pair_inv : forall (a b : tm) (k : security) (v : tm),
  tm_pair a b k -->* v -> value v ->
  exists w1 w2, a -->* w1 /\ value w1 /\ b -->* w2 /\ value w2 /\
    v = tm_pair w1 w2 k.
Proof.
  intros a b k v H Hv.
  remember (tm_pair a b k) as s eqn:Es.
  revert a b k Es.
  induction H as [ s0 | s1 s2 s3 Hst Hm IH ]; intros a0 b0 k0 Es.
  - subst s0. inversion Hv as [ | | v1 v2 kappa H1 H2 | | ]; subst.
    eexists. eexists. repeat split; eauto using multi_refl.
  - subst s1.
    destruct (step_pair_dec a0 b0 k0 s2 Hst) as
      [ (a' & Hstep & Hs2) | (b' & Hva & Hstep & Hs2) ].
    + subst s2.
      edestruct (IH Hv a' b0 k0 eq_refl) as (w1 & w2 & Ha & Hva' & Hb & Hvb & Heq).
      exists w1, w2. repeat split; try assumption.
      apply multi_step with (t2 := a'); [exact Hstep | exact Ha].
    + subst s2.
      edestruct (IH Hv a0 b' k0 eq_refl) as (w1 & w2 & Ha & Hva' & Hb & Hvb & Heq).
      exists w1, w2. repeat split; try assumption.
      apply multi_step with (t2 := b'); [exact Hstep | exact Hb].
Qed.

Lemma multi_inl_inv : forall (a : tm) (k : security) (v : tm),
  tm_inl a k -->* v -> value v ->
  exists w, a -->* w /\ value w /\ v = tm_inl w k.
Proof.
  intros a k v H Hv.
  remember (tm_inl a k) as s eqn:Es.
  revert a k Es.
  induction H as [ s0 | s1 s2 s3 Hst Hm IH ]; intros a0 k0 Es.
  - subst s0. inversion Hv as [ | | | v0 kappa H1 | ]; subst.
    eexists. repeat split; eauto using multi_refl.
  - subst s1.
    destruct (step_inl_dec a0 k0 s2 Hst) as (a' & Hstep & Hs2).
    subst s2. edestruct (IH Hv a' k0 eq_refl) as (w & Ha & Hvw & Heq).
    exists w. repeat split; try assumption.
    apply multi_step with (t2 := a'); [exact Hstep | exact Ha].
Qed.

Lemma multi_inr_inv : forall (a : tm) (k : security) (v : tm),
  tm_inr a k -->* v -> value v ->
  exists w, a -->* w /\ value w /\ v = tm_inr w k.
Proof.
  intros a k v H Hv.
  remember (tm_inr a k) as s eqn:Es.
  revert a k Es.
  induction H as [ s0 | s1 s2 s3 Hst Hm IH ]; intros a0 k0 Es.
  - subst s0. inversion Hv as [ | | | | v0 kappa H1 ]; subst.
    eexists. repeat split; eauto using multi_refl.
  - subst s1.
    destruct (step_inr_dec a0 k0 s2 Hst) as (a' & Hstep & Hs2).
    subst s2. edestruct (IH Hv a' k0 eq_refl) as (w & Ha & Hvw & Heq).
    exists w. repeat split; try assumption.
    apply multi_step with (t2 := a'); [exact Hstep | exact Ha].
Qed.

Lemma multi_fst_inv : forall (t : tm) (r : label) (v : tm),
  tm_fst t r -->* v -> value v ->
  exists p1 p2 k,
    t -->* tm_pair p1 p2 k /\ value p1 /\ value p2 /\
    flows_to k.(reader) r /\ v = protect_value p1 k.(indirect_reader).
Proof.
  intros t r v H Hv.
  remember (tm_fst t r) as s eqn:Es.
  revert t r Es.
  induction H as [ s0 | s1 s2 s3 Hst Hm IH ]; intros t0 r0 Es.
  - subst s0. inversion Hv.
  - subst s1.
    destruct (step_fst_dec t0 r0 s2 Hst) as
      [ (v1 & v2 & k & Ht & Hv1 & Hv2 & Hflow & Hs2)
      | (t' & Hstep & Hs2) ].
    + subst s2.
      edestruct (multi_protect_inv k.(indirect_reader) v1 _ Hm Hv) as (w & Hpw & Hvw & Heq).
      rewrite Ht. exists v1, v2, k. repeat split; try assumption; [apply multi_refl |].
      rewrite Heq. rewrite (multi_value_eq v1 w Hv1 Hpw). reflexivity.
    + subst s2.
      edestruct (IH Hv t' r0 eq_refl) as (p1 & p2 & k & Ht & Hv1 & Hv2 & Hflow & Heq).
      exists p1, p2, k. repeat split; try assumption.
      apply multi_step with (t2 := t'); [exact Hstep | exact Ht].
Qed.

Lemma multi_snd_inv : forall (t : tm) (r : label) (v : tm),
  tm_snd t r -->* v -> value v ->
  exists p1 p2 k,
    t -->* tm_pair p1 p2 k /\ value p1 /\ value p2 /\
    flows_to k.(reader) r /\ v = protect_value p2 k.(indirect_reader).
Proof.
  intros t r v H Hv.
  remember (tm_snd t r) as s eqn:Es.
  revert t r Es.
  induction H as [ s0 | s1 s2 s3 Hst Hm IH ]; intros t0 r0 Es.
  - subst s0. inversion Hv.
  - subst s1.
    destruct (step_snd_dec t0 r0 s2 Hst) as
      [ (v1 & v2 & k & Ht & Hv1 & Hv2 & Hflow & Hs2)
      | (t' & Hstep & Hs2) ].
    + subst s2.
      edestruct (multi_protect_inv k.(indirect_reader) v2 _ Hm Hv) as (w & Hpw & Hvw & Heq).
      rewrite Ht. exists v1, v2, k. repeat split; try assumption; [apply multi_refl |].
      rewrite Heq. rewrite (multi_value_eq v2 w Hv2 Hpw). reflexivity.
    + subst s2.
      edestruct (IH Hv t' r0 eq_refl) as (p1 & p2 & k & Ht & Hv1 & Hv2 & Hflow & Heq).
      exists p1, p2, k. repeat split; try assumption.
      apply multi_step with (t2 := t'); [exact Hstep | exact Ht].
Qed.

Lemma multi_case_inv : forall (t b1 b2 : tm) (r : label) (v : tm),
  tm_case t b1 b2 r -->* v -> value v ->
  (exists w k, t -->* tm_inl w k /\ value w /\ flows_to k.(reader) r /\
      tm_protect k.(indirect_reader) (open b1 w) -->* v)
  \/
  (exists w k, t -->* tm_inr w k /\ value w /\ flows_to k.(reader) r /\
      tm_protect k.(indirect_reader) (open b2 w) -->* v).
Proof.
  intros t b1 b2 r v H Hv.
  remember (tm_case t b1 b2 r) as s eqn:Es.
  revert t b1 b2 r Es.
  induction H as [ s0 | s1 s2 s3 Hst Hm IH ]; intros t0 b10 b20 r0 Es.
  - subst s0. inversion Hv.
  - subst s1.
    destruct (step_case_dec t0 b10 b20 r0 s2 Hst) as
      [ (v0 & k & Ht & Hval & Hflow & Hs2)
      | [ (v0 & k & Ht & Hval & Hflow & Hs2)
        | (t' & Hstep & Hs2) ] ].
    + subst s2. left. rewrite Ht. exists v0, k. repeat split; try assumption; apply multi_refl.
    + subst s2. right. rewrite Ht. exists v0, k. repeat split; try assumption; apply multi_refl.
    + subst s2.
      destruct (IH Hv t' b10 b20 r0 eq_refl) as
        [(w & k & Ht & Hvw & Hflow & Htail) | (w & k & Ht & Hvw & Hflow & Htail)].
      * left. exists w, k. repeat split; try assumption.
        apply multi_step with (t2 := t'); [exact Hstep | exact Ht].
      * right. exists w, k. repeat split; try assumption.
        apply multi_step with (t2 := t'); [exact Hstep | exact Ht].
Qed.

Lemma multi_if_inv : forall (c y n : tm) (r : label) (v : tm),
  tm_if c y n r -->* v -> value v ->
  (exists w k, c -->* tm_inl w k /\ value w /\ flows_to k.(reader) r /\
      tm_protect k.(indirect_reader) y -->* v)
  \/
  (exists w k, c -->* tm_inr w k /\ value w /\ flows_to k.(reader) r /\
      tm_protect k.(indirect_reader) n -->* v).
Proof.
  intros c y n r v H Hv.
  remember (tm_if c y n r) as s eqn:Es.
  revert c y n r Es.
  induction H as [ s0 | s1 s2 s3 Hst Hm IH ]; intros c0 y0 n0 r0 Es.
  - subst s0. inversion Hv.
  - subst s1.
    destruct (step_if_dec c0 y0 n0 r0 s2 Hst) as
      [ (v0 & k & Hc & Hval & Hflow & Hs2)
      | [ (v0 & k & Hc & Hval & Hflow & Hs2)
        | (c' & Hstep & Hs2) ] ].
    + subst s2. left. rewrite Hc. exists v0, k. repeat split; try assumption; apply multi_refl.
    + subst s2. right. rewrite Hc. exists v0, k. repeat split; try assumption; apply multi_refl.
    + subst s2.
      destruct (IH Hv c' y0 n0 r0 eq_refl) as
        [(w & k & Hc & Hvw & Hflow & Htail) | (w & k & Hc & Hvw & Hflow & Htail)].
      * left. exists w, k. repeat split; try assumption.
        apply multi_step with (t2 := c'); [exact Hstep | exact Hc].
      * right. exists w, k. repeat split; try assumption.
        apply multi_step with (t2 := c'); [exact Hstep | exact Hc].
Qed.


(* ================================================================= *)
(* Logical relation                                                   *)
(* ================================================================= *)

Fixpoint V (l : label) (T : ty) (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_Unit kappa =>
      flows_to kappa.(indirect_reader) l -> erase_security v1 = erase_security v2
  | Ty_Sum T1 T2 kappa =>
      flows_to kappa.(indirect_reader) l ->
      ( (exists (w1 w2 : tm) (k1 k2 : security),
            v1 = tm_inl w1 k1 /\ v2 = tm_inl w2 k2 /\
            security_le k1 kappa /\ security_le k2 kappa /\
            V l T1 w1 w2)
        \/ (exists (w1 w2 : tm) (k1 k2 : security),
            v1 = tm_inr w1 k1 /\ v2 = tm_inr w2 k2 /\
            security_le k1 kappa /\ security_le k2 kappa /\
            V l T2 w1 w2) )
  | Ty_Prod T1 T2 kappa =>
      flows_to kappa.(indirect_reader) l ->
      (exists (w1 w2 w1' w2' : tm) (k1 k2 : security),
          v1 = tm_pair w1 w2 k1 /\ v2 = tm_pair w1' w2' k2 /\
          security_le k1 kappa /\ security_le k2 kappa /\
          V l T1 w1 w1' /\ V l T2 w2 w2')
  | Ty_Arrow T1 T2 kappa =>
      flows_to kappa.(indirect_reader) l ->
      match v1, v2 with
      | tm_abs _ b1 k1, tm_abs _ b2 k2 =>
          security_le k1 kappa /\ security_le k2 kappa /\
          (forall (w1 w2 : tm), value w1 -> value w2 -> V l T1 w1 w2 ->
             forall z1 z2,
               evaluates (open b1 w1) z1 -> evaluates (open b2 w2) z2 ->
               V l T2 z1 z2)
      | _, _ => True
      end
  end.

Definition R (l : label) (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, evaluates t1 v1 -> evaluates t2 v2 -> V l T v1 v2.

Lemma V_protect_adjust : forall (T : ty) (l : label) (v1 v2 : tm),
  V l T v1 v2 ->
  forall a1 a2 b : label,
  flows_to a1 b -> flows_to a2 b ->
  V l (ty_protect b T) (protect_value v1 a1) (protect_value v2 a2).
Proof.
  intros T l v1 v2 HV a1 a2 b H1 H2.
  destruct T as [kappa | T1 T2 kappa | T1 T2 kappa | T1 T2 kappa]; simpl in *.
  - intro h.
    assert (hsource : flows_to kappa.(indirect_reader) l).
    { eapply flows_to_trans; [apply flows_to_join_l | exact h]. }
    rewrite erase_security_protect_value.
    rewrite erase_security_protect_value.
    apply HV. exact hsource.
  - intro h.
    assert (hsource : flows_to kappa.(indirect_reader) l).
    { eapply flows_to_trans; [apply flows_to_join_l | exact h]. }
    destruct (HV hsource) as
      [ (w1 & w2 & k1 & k2 & E1 & E2 & S1 & S2 & HVw)
      | (w1 & w2 & k1 & k2 & E1 & E2 & S1 & S2 & HVw) ].
    + left. exists w1, w2, (protect_security k1 a1), (protect_security k2 a2).
      split.
      * rewrite E1. reflexivity.
      * split.
        -- rewrite E2. reflexivity.
        -- split.
           ++ eapply protect_security_mono; eauto.
           ++ split.
              ** eapply protect_security_mono; eauto.
              ** exact HVw.
    + right. exists w1, w2, (protect_security k1 a1), (protect_security k2 a2).
      split.
      * rewrite E1. reflexivity.
      * split.
        -- rewrite E2. reflexivity.
        -- split.
           ++ eapply protect_security_mono; eauto.
           ++ split.
              ** eapply protect_security_mono; eauto.
              ** exact HVw.
  - intro h.
    assert (hsource : flows_to kappa.(indirect_reader) l).
    { eapply flows_to_trans; [apply flows_to_join_l | exact h]. }
    destruct (HV hsource) as (w1 & w2 & w1' & w2' & k1 & k2 & E1 & E2 & S1 & S2 & HV1 & HV2).
    exists w1, w2, w1', w2', (protect_security k1 a1), (protect_security k2 a2).
    split.
    + rewrite E1. reflexivity.
    + split.
      * rewrite E2. reflexivity.
      * split.
        -- eapply protect_security_mono; eauto.
        -- split.
           ++ eapply protect_security_mono; eauto.
           ++ split.
              ** exact HV1.
              ** exact HV2.
  - destruct v1; simpl in *; try (intro; exact I).
    destruct v2; simpl in *; try (intro; exact I).
    intro h.
    assert (hsource : flows_to kappa.(indirect_reader) l).
    { eapply flows_to_trans; [apply flows_to_join_l | exact h]. }
    specialize (HV hsource).
    destruct HV as [S1 [S2 HB]].
    split.
    + eapply protect_security_mono; eauto.
    + split.
      * eapply protect_security_mono; eauto.
      * exact HB.
Qed.


Lemma V_subtype : forall (T U : ty), subtype T U ->
  forall (l : label) (v1 v2 : tm), V l T v1 v2 -> V l U v1 v2.
Proof.
  intros T U H. induction H as
    [ k1 k2 Hwf1 Hwf2 Hsle
    | T1 T2 U1 U2 k1 k2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hsle
    | T1 T2 U1 U2 k1 k2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hsle
    | T1 T2 U1 U2 k1 k2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hsle
    | T U0 W Hsub1 IH1 Hsub2 IH2 ];
    intros l v1 v2 HV.
  - simpl in *. intro h2.
    apply HV. eapply flows_to_trans; [exact (proj2 Hsle) | exact h2].
  - simpl in *. intro h2.
    assert (h1 : flows_to k1.(indirect_reader) l).
    { eapply flows_to_trans; [exact (proj2 Hsle) | exact h2]. }
    destruct (HV h1) as
      [ (w1 & w2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HVw)
      | (w1 & w2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HVw) ].
    + left. exists w1, w2, kk1, kk2.
      split.
      * exact E1.
      * split.
        -- exact E2.
        -- split.
           ++ eapply security_le_trans; [exact S1 | exact Hsle].
           ++ split.
              ** eapply security_le_trans; [exact S2 | exact Hsle].
              ** apply (IH1 l w1 w2 HVw).
    + right. exists w1, w2, kk1, kk2.
      split.
      * exact E1.
      * split.
        -- exact E2.
        -- split.
           ++ eapply security_le_trans; [exact S1 | exact Hsle].
           ++ split.
              ** eapply security_le_trans; [exact S2 | exact Hsle].
              ** apply (IH2 l w1 w2 HVw).
  - simpl in *. intro h2.
    assert (h1 : flows_to k1.(indirect_reader) l).
    { eapply flows_to_trans; [exact (proj2 Hsle) | exact h2]. }
    destruct (HV h1) as (w1 & w2 & w1' & w2' & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1 & HV2).
    exists w1, w2, w1', w2', kk1, kk2.
    split.
    + exact E1.
    + split.
      * exact E2.
      * split.
        -- eapply security_le_trans; [exact S1 | exact Hsle].
        -- split.
           ++ eapply security_le_trans; [exact S2 | exact Hsle].
           ++ split.
              ** apply (IH1 l w1 w1' HV1).
              ** apply (IH2 l w2 w2' HV2).
  - simpl in *. intro h2.
    assert (h1 : flows_to k1.(indirect_reader) l).
    { eapply flows_to_trans; [exact (proj2 Hsle) | exact h2]. }
    destruct v1; destruct v2; simpl in *; try exact I.
    specialize (HV h1).
    destruct HV as [S1 [S2 HB]].
    split.
    + eapply security_le_trans; [exact S1 | exact Hsle].
    + split.
      * eapply security_le_trans; [exact S2 | exact Hsle].
      * intros w1 w2 Hval1 Hval2 HVw z1 z2 Ev1 Ev2.
        exact (IH2 l z1 z2
                 (HB w1 w2 Hval1 Hval2 (IH1 l w1 w2 HVw) z1 z2 Ev1 Ev2)).
  - apply (IH2 l v1 v2). apply (IH1 l v1 v2). exact HV.
Qed.


Definition env_rel (l : label) (Gamma : context) (s1 s2 : atom -> tm) : Prop :=
  (forall y, locally_closed (s1 y) /\ locally_closed (s2 y)) /\
  (forall x T, lookup_context x Gamma = Some T -> R l T (s1 x) (s2 x)).

Lemma R_of_V_value : forall (l : label) (T : ty) (v1 v2 : tm),
  value v1 -> value v2 -> V l T v1 v2 -> R l T v1 v2.
Proof.
  intros l T v1 v2 Hv1 Hv2 HV z1 z2 [E1 _] [E2 _].
  rewrite (multi_value_eq v1 z1 Hv1 E1).
  rewrite (multi_value_eq v2 z2 Hv2 E2).
  exact HV.
Qed.

Lemma R_subtype : forall (l : label) (T U : ty), subtype T U ->
  forall t1 t2, R l T t1 t2 -> R l U t1 t2.
Proof.
  intros l T U Hsub t1 t2 HR v1 v2 E1 E2.
  apply (V_subtype T U Hsub l v1 v2).
  apply HR; assumption.
Qed.

Lemma R_protect : forall (l : label) (b : label) (T : ty) (t1 t2 : tm),
  R l T t1 t2 -> R l (ty_protect b T) (tm_protect b t1) (tm_protect b t2).
Proof.
  intros l b T t1 t2 HR v1 v2 [E1 Hv1] [E2 Hv2].
  destruct (multi_protect_inv b t1 v1 E1 Hv1) as (z1 & Hz1 & Hvz1 & Heq1).
  destruct (multi_protect_inv b t2 v2 E2 Hv2) as (z2 & Hz2 & Hvz2 & Heq2).
  rewrite Heq1, Heq2.
  apply (V_protect_adjust T l z1 z2 (HR z1 z2 (conj Hz1 Hvz1) (conj Hz2 Hvz2))
           b b b (flows_to_refl b) (flows_to_refl b)).
Qed.

Lemma env_rel_update : forall (l : label) (Gamma : context)
    (s1 s2 : atom -> tm) (x : atom) (T : ty) (w1 w2 : tm),
  env_rel l Gamma s1 s2 ->
  value w1 -> value w2 -> V l T w1 w2 ->
  env_rel l (update Gamma x T)
    (fun y => if Nat.eqb y x then w1 else s1 y)
    (fun y => if Nat.eqb y x then w2 else s2 y).
Proof.
  intros l Gamma s1 s2 x T w1 w2 [Hlc HR] Hw1 Hw2 HV. split.
  - intros y. destruct (Nat.eqb y x) eqn:E.
    + split; apply value_lc; assumption.
    + apply Hlc.
  - intros y U Hy. simpl in Hy.
    destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. inversion Hy. subst U.
      apply R_of_V_value; assumption.
    + apply HR. exact Hy.
Qed.

Lemma V_vacuous : forall (T : ty) (l : label),
  ~ flows_to (security_of T).(indirect_reader) l -> forall v1 v2, V l T v1 v2.
Proof.
  intros T l H v1 v2. destruct T; simpl in *; try exact I; intro h; exfalso; apply H; exact h.
Qed.

Lemma V_protect_intro_cond : forall (l : label) (T : ty) (b a1 a2 : label) (v1 v2 : tm),
  (flows_to b l -> flows_to a1 b) ->
  (flows_to b l -> flows_to a2 b) ->
  (flows_to b l -> V l T v1 v2) ->
  V l (ty_protect b T) (protect_value v1 a1) (protect_value v2 a2).
Proof.
  intros l T b a1 a2 v1 v2 H1 H2 HV.
  destruct T as [kT | Ta Tb kT | Ta Tb kT | Ta Tb kT].
  all: intro hgoal.
  all: assert (hb : flows_to b l)
    by (eapply flows_to_trans; [apply flows_to_join_r | exact hgoal]).
  all: apply (V_protect_adjust _ l v1 v2 (HV hb) a1 a2 b (H1 hb) (H2 hb)).
  all: assumption.
Qed.

Lemma V_protect_contra : forall (l : label) (T : ty) (b a1 a2 : label) (v1 v2 : tm),
  (flows_to b l -> False) ->
  V l (ty_protect b T) (protect_value v1 a1) (protect_value v2 a2).
Proof.
  intros l T b a1 a2 v1 v2 Hc.
  destruct T as [kT | Ta Tb kT | Ta Tb kT | Ta Tb kT].
  all: intro hgoal.
  all: exfalso.
  all: apply Hc.
  all: eapply flows_to_trans; [apply flows_to_join_r | exact hgoal].
Qed.

Lemma fundamental : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T ->
  forall (l : label) (s1 s2 : atom -> tm),
  env_rel l Gamma s1 s2 ->
  R l T (subst_env s1 t) (subst_env s2 t).
Proof.
  intros Gamma t T H. induction H as
    [ Gamma0 x T0 Hlook Hwf
    | Gamma0 kappa Hwf
    | L Gamma0 T1 body T2 kappa HwfT1 Hwfkappa Hbody IHbody
    | Gamma0 t1 t2 T1 T2 kappa r Ht1 IHt1 Ht2 IHt2 Hflow
    | Gamma0 t1 t2 T1 T2 kappa Ht1 IHt1 Ht2 IHt2 Hwf
    | Gamma0 t T1 T2 kappa r Ht IHt Hflow
    | Gamma0 t T1 T2 kappa r Ht IHt Hflow
    | Gamma0 t T1 T2 kappa Ht IHt HwfT2 Hwfkappa
    | Gamma0 t T1 T2 kappa HwfT1 Ht IHt Hwfkappa
    | L Gamma0 t body1 body2 T1 T2 T0 kappa r Ht IHt Hflow Hbody1 IHbody1 Hbody2 IHbody2
    | Gamma0 t T0 lp Ht IHt
    | Gamma0 t T0 U Ht IHt Hsub
    | Gamma0 c yes no k T0 r Hc IHc Hyes IHyes Hno IHno Hflow ];
    intros l s1 s2 Henv.
  - (* T_Var *) destruct Henv as [Hlc HR]. simpl. apply (HR x T0 Hlook).
  - (* T_Unit *) destruct Henv as [Hlc HR]. unfold R. intros v1 v2 [E1 _] [E2 _].
    simpl. intro hflow.
    rewrite (multi_value_eq (tm_unit kappa) v1 (v_unit kappa) E1).
    rewrite (multi_value_eq (tm_unit kappa) v2 (v_unit kappa) E2).
    reflexivity.
  - (* T_Abs *) destruct Henv as [Hlc HR].
    unfold R. intros v1 v2 [Ev1 Hval1] [Ev2 Hval2].
    assert (E1 : v1 = tm_abs T1 (subst_env s1 body) kappa).
    { apply (multi_stuck (tm_abs T1 (subst_env s1 body) kappa) v1
               (abs_no_step T1 (subst_env s1 body) kappa) Ev1). }
    assert (E2 : v2 = tm_abs T1 (subst_env s2 body) kappa).
    { apply (multi_stuck (tm_abs T1 (subst_env s2 body) kappa) v2
               (abs_no_step T1 (subst_env s2 body) kappa) Ev2). }
    rewrite E1, E2. clear E1 E2 Hval1 Hval2 Ev1 Ev2.
    simpl. intro hflow. split.
    + apply security_le_refl.
    + split.
      * apply security_le_refl.
      * intros w1 w2 Hw1 Hw2 HVw z1 z2 [Ez1 Hz1] [Ez2 Hz2].
        set (x := fresh (L ++ fv body)).
        assert (HxL : ~ In x L).
        { intro Hin. pose proof (fresh_notin (L ++ fv body)) as Hni.
          apply Hni. apply in_or_app. left. exact Hin. }
        assert (Hxb : ~ In x (fv body)).
        { intro Hin. pose proof (fresh_notin (L ++ fv body)) as Hni.
          apply Hni. apply in_or_app. right. exact Hin. }
        pose proof (IHbody x HxL l
          (fun y => if Nat.eqb y x then w1 else s1 y)
          (fun y => if Nat.eqb y x then w2 else s2 y)
          (env_rel_update l Gamma0 s1 s2 x T1 w1 w2 (conj Hlc HR) Hw1 Hw2 HVw)) as HRb.
        assert (He1 : subst_env (fun y => if Nat.eqb y x then w1 else s1 y)
                       (open body (tm_fvar x)) = open (subst_env s1 body) w1).
        { apply (subst_env_open_rec s1 x w1 body 0).
          - intros y Hy. exact (proj1 (Hlc y)).
          - exact Hxb. }
        assert (He2 : subst_env (fun y => if Nat.eqb y x then w2 else s2 y)
                       (open body (tm_fvar x)) = open (subst_env s2 body) w2).
        { apply (subst_env_open_rec s2 x w2 body 0).
          - intros y Hy. exact (proj2 (Hlc y)).
          - exact Hxb. }
        rewrite He1, He2 in HRb.
        exact (HRb z1 z2 (conj Ez1 Hz1) (conj Ez2 Hz2)).
  - (* T_App *) destruct Henv as [Hlc HR].
    unfold R. intros v1 v2 [Ev1 Hval1] [Ev2 Hval2].
    destruct (multi_app_inv _ _ _ _ Ev1 Hval1) as
      (Tf & b1 & av1 & kf & Hf1 & Hvalf1 & Ha1 & Hvala1 & Hfl1 & Htail1).
    destruct (multi_app_inv _ _ _ _ Ev2 Hval2) as
      (Tf2 & b2 & av2 & kf2 & Hf2 & Hvalf2 & Ha2 & Hvala2 & Hfl2 & Htail2).
    assert (HVarr : V l (Ty_Arrow T1 T2 kappa)
              (tm_abs Tf b1 kf) (tm_abs Tf2 b2 kf2)).
    { exact (IHt1 l s1 s2 (conj Hlc HR)
               (tm_abs Tf b1 kf) (tm_abs Tf2 b2 kf2)
               (conj Hf1 Hvalf1) (conj Hf2 Hvalf2)). }
    assert (HVarg : V l T1 av1 av2).
    { exact (IHt2 l s1 s2 (conj Hlc HR) av1 av2
               (conj Ha1 Hvala1) (conj Ha2 Hvala2)). }
    destruct (multi_protect_inv kf.(indirect_reader) (open b1 av1) v1 Htail1 Hval1)
      as (z1 & Hz1 & Hvz1 & Heq1).
    destruct (multi_protect_inv kf2.(indirect_reader) (open b2 av2) v2 Htail2 Hval2)
      as (z2 & Hz2 & Hvz2 & Heq2).
    rewrite Heq1, Heq2.
    apply (V_protect_intro_cond l T2 kappa.(indirect_reader)
             kf.(indirect_reader) kf2.(indirect_reader) z1 z2).
    + intro hflow. simpl in HVarr. specialize (HVarr hflow).
      destruct HVarr as [Sk1 _]. exact (proj2 Sk1).
    + intro hflow. simpl in HVarr. specialize (HVarr hflow).
      destruct HVarr as [_ [Sk2 _]]. exact (proj2 Sk2).
    + intro hflow. simpl in HVarr. specialize (HVarr hflow).
      destruct HVarr as [_ [_ Hbody]].
      pose proof (Hbody av1 av2 Hvala1 Hvala2 HVarg) as HRb.
      apply HRb; split; assumption.
  - (* T_Pair *) destruct Henv as [Hlc HR].
    unfold R. intros v1 v2 [Ev1 Hval1] [Ev2 Hval2].
    destruct (multi_pair_inv _ _ _ _ Ev1 Hval1) as
      (w1 & w2 & Ha & Hva & Hb & Hvb & Heq1).
    destruct (multi_pair_inv _ _ _ _ Ev2 Hval2) as
      (w1' & w2' & Ha' & Hva' & Hb' & Hvb' & Heq2).
    intro hflow.
    exists w1, w2, w1', w2', kappa, kappa.
    split.
    + exact Heq1.
    + split.
      * exact Heq2.
      * split.
        -- apply security_le_refl.
        -- split.
           ++ apply security_le_refl.
           ++ split.
              ** exact (IHt1 l s1 s2 (conj Hlc HR) w1 w1'
                          (conj Ha Hva) (conj Ha' Hva')).
              ** exact (IHt2 l s1 s2 (conj Hlc HR) w2 w2'
                          (conj Hb Hvb) (conj Hb' Hvb')).
  - (* T_Fst *) destruct Henv as [Hlc HR].
    unfold R. intros v1 v2 [Ev1 Hval1] [Ev2 Hval2].
    destruct (multi_fst_inv _ _ _ Ev1 Hval1) as
      (p1 & p2 & kr & Htm & Hp1 & Hp2 & Hfl & Heq1).
    destruct (multi_fst_inv _ _ _ Ev2 Hval2) as
      (p1' & p2' & kr' & Htm' & Hp1' & Hp2' & Hfl' & Heq2).
    assert (HVprod : V l (Ty_Prod T1 T2 kappa) (tm_pair p1 p2 kr) (tm_pair p1' p2' kr')).
    { exact (IHt l s1 s2 (conj Hlc HR) (tm_pair p1 p2 kr) (tm_pair p1' p2' kr')
               (conj Htm (v_pair p1 p2 kr Hp1 Hp2)) (conj Htm' (v_pair p1' p2' kr' Hp1' Hp2'))). }
    assert (Hcond : flows_to kappa.(indirect_reader) l ->
              security_le kr kappa /\ security_le kr' kappa /\ V l T1 p1 p1').
    { intro hflow. simpl in HVprod. specialize (HVprod hflow).
      destruct HVprod as (w1 & w2 & w1' & w2' & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1 & HV2).
      inversion E1; inversion E2; subst. exact (conj S1 (conj S2 HV1)). }
    rewrite Heq1, Heq2.
    apply (V_protect_intro_cond l T1 kappa.(indirect_reader)
             kr.(indirect_reader) kr'.(indirect_reader) p1 p1').
    + intro h. exact (proj2 (proj1 (Hcond h))).
    + intro h. exact (proj2 (proj1 (proj2 (Hcond h)))).
    + intro h. exact (proj2 (proj2 (Hcond h))).
  - (* T_Snd *) destruct Henv as [Hlc HR].
    unfold R. intros v1 v2 [Ev1 Hval1] [Ev2 Hval2].
    destruct (multi_snd_inv _ _ _ Ev1 Hval1) as
      (p1 & p2 & kr & Htm & Hp1 & Hp2 & Hfl & Heq1).
    destruct (multi_snd_inv _ _ _ Ev2 Hval2) as
      (p1' & p2' & kr' & Htm' & Hp1' & Hp2' & Hfl' & Heq2).
    assert (HVprod : V l (Ty_Prod T1 T2 kappa) (tm_pair p1 p2 kr) (tm_pair p1' p2' kr')).
    { exact (IHt l s1 s2 (conj Hlc HR) (tm_pair p1 p2 kr) (tm_pair p1' p2' kr')
               (conj Htm (v_pair p1 p2 kr Hp1 Hp2)) (conj Htm' (v_pair p1' p2' kr' Hp1' Hp2'))). }
    assert (Hcond : flows_to kappa.(indirect_reader) l ->
              security_le kr kappa /\ security_le kr' kappa /\ V l T2 p2 p2').
    { intro hflow. simpl in HVprod. specialize (HVprod hflow).
      destruct HVprod as (w1 & w2 & w1' & w2' & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1 & HV2).
      inversion E1; inversion E2; subst. exact (conj S1 (conj S2 HV2)). }
    rewrite Heq1, Heq2.
    apply (V_protect_intro_cond l T2 kappa.(indirect_reader)
             kr.(indirect_reader) kr'.(indirect_reader) p2 p2').
    + intro h. exact (proj2 (proj1 (Hcond h))).
    + intro h. exact (proj2 (proj1 (proj2 (Hcond h)))).
    + intro h. exact (proj2 (proj2 (Hcond h))).
  - (* T_Inl *) destruct Henv as [Hlc HR].
    unfold R. intros v1 v2 [Ev1 Hval1] [Ev2 Hval2].
    destruct (multi_inl_inv _ _ _ Ev1 Hval1) as (w1 & Ha & Hva & Heq1).
    destruct (multi_inl_inv _ _ _ Ev2 Hval2) as (w2 & Ha' & Hva' & Heq2).
    intro hflow.
    left. exists w1, w2, kappa, kappa.
    split.
    + exact Heq1.
    + split.
      * exact Heq2.
      * split.
        -- apply security_le_refl.
        -- split.
           ++ apply security_le_refl.
           ++ exact (IHt l s1 s2 (conj Hlc HR) w1 w2 (conj Ha Hva) (conj Ha' Hva')).
  - (* T_Inr *) destruct Henv as [Hlc HR].
    unfold R. intros v1 v2 [Ev1 Hval1] [Ev2 Hval2].
    destruct (multi_inr_inv _ _ _ Ev1 Hval1) as (w1 & Ha & Hva & Heq1).
    destruct (multi_inr_inv _ _ _ Ev2 Hval2) as (w2 & Ha' & Hva' & Heq2).
    intro hflow.
    right. exists w1, w2, kappa, kappa.
    split.
    + exact Heq1.
    + split.
      * exact Heq2.
      * split.
        -- apply security_le_refl.
        -- split.
           ++ apply security_le_refl.
           ++ exact (IHt l s1 s2 (conj Hlc HR) w1 w2 (conj Ha Hva) (conj Ha' Hva')).
  - (* T_Case *) destruct Henv as [Hlc HR].
    unfold R. intros v1 v2 [Ev1 Hval1] [Ev2 Hval2].
    set (x := fresh (L ++ (fv body1 ++ fv body2))).
    assert (HxL : ~ In x L).
    { intro Hin. pose proof (fresh_notin (L ++ (fv body1 ++ fv body2))) as Hni.
      apply Hni. apply in_or_app. left. exact Hin. }
    assert (Hxb1 : ~ In x (fv body1)).
    { intro Hin. pose proof (fresh_notin (L ++ (fv body1 ++ fv body2))) as Hni.
      apply Hni. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (Hxb2 : ~ In x (fv body2)).
    { intro Hin. pose proof (fresh_notin (L ++ (fv body1 ++ fv body2))) as Hni.
      apply Hni. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    destruct (multi_case_inv _ _ _ _ _ Ev1 Hval1) as [D1 | D1];
      destruct (multi_case_inv _ _ _ _ _ Ev2 Hval2) as [D2 | D2].
    + (* inl / inl *)
      destruct D1 as (w1 & kr1 & Ht1 & Hw1 & Hfl1 & Htail1).
      destruct D2 as (w2 & kr2 & Ht2 & Hw2 & Hfl2 & Htail2).
      assert (HVsum : V l (Ty_Sum T1 T2 kappa) (tm_inl w1 kr1) (tm_inl w2 kr2)).
      { exact (IHt l s1 s2 (conj Hlc HR) (tm_inl w1 kr1) (tm_inl w2 kr2)
                 (conj Ht1 (v_inl w1 kr1 Hw1)) (conj Ht2 (v_inl w2 kr2 Hw2))). }
      assert (Hcond : flows_to kappa.(indirect_reader) l ->
                security_le kr1 kappa /\ security_le kr2 kappa /\ V l T1 w1 w2).
      { intro hflow. simpl in HVsum. specialize (HVsum hflow).
        destruct HVsum as
          [(u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1) |
           (u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1)].
        - inversion E1; inversion E2; subst. exact (conj S1 (conj S2 HV1)).
        - inversion E1. }
      destruct (multi_protect_inv kr1.(indirect_reader) _ v1 Htail1 Hval1)
        as (z1 & Hz1 & Hvz1 & Hz1').
      destruct (multi_protect_inv kr2.(indirect_reader) _ v2 Htail2 Hval2)
        as (z2 & Hz2 & Hvz2 & Hz2').
      assert (Hbody_cond : flows_to kappa.(indirect_reader) l -> V l T0 z1 z2).
      { intro hflow. destruct (Hcond hflow) as [S1 [S2 HV1]].
        pose proof (IHbody1 x HxL l
          (fun y => if Nat.eqb y x then w1 else s1 y)
          (fun y => if Nat.eqb y x then w2 else s2 y)
          (env_rel_update l Gamma0 s1 s2 x T1 w1 w2 (conj Hlc HR) Hw1 Hw2 HV1)) as HRb.
        assert (He1 : subst_env (fun y => if Nat.eqb y x then w1 else s1 y)
                       (open body1 (tm_fvar x)) = open (subst_env s1 body1) w1).
        { apply (subst_env_open_rec s1 x w1 body1 0).
          - intros y Hy. exact (proj1 (Hlc y)).
          - exact Hxb1. }
        assert (He2 : subst_env (fun y => if Nat.eqb y x then w2 else s2 y)
                       (open body1 (tm_fvar x)) = open (subst_env s2 body1) w2).
        { apply (subst_env_open_rec s2 x w2 body1 0).
          - intros y Hy. exact (proj2 (Hlc y)).
          - exact Hxb1. }
        rewrite He1, He2 in HRb.
        apply HRb; split; assumption. }
      rewrite Hz1', Hz2'.
      apply (V_protect_intro_cond l T0 kappa.(indirect_reader)
               kr1.(indirect_reader) kr2.(indirect_reader) z1 z2).
      * intro h. exact (proj2 (proj1 (Hcond h))).
      * intro h. exact (proj2 (proj1 (proj2 (Hcond h)))).
      * exact Hbody_cond.
    + (* inl / inr *)
      destruct D1 as (w1 & kr1 & Ht1 & Hw1 & Hfl1 & Htail1).
      destruct D2 as (w2 & kr2 & Ht2 & Hw2 & Hfl2 & Htail2).
      assert (HVsum : V l (Ty_Sum T1 T2 kappa) (tm_inl w1 kr1) (tm_inr w2 kr2)).
      { exact (IHt l s1 s2 (conj Hlc HR) (tm_inl w1 kr1) (tm_inr w2 kr2)
                 (conj Ht1 (v_inl w1 kr1 Hw1)) (conj Ht2 (v_inr w2 kr2 Hw2))). }
      destruct (multi_protect_inv kr1.(indirect_reader) _ v1 Htail1 Hval1)
        as (z1 & _ & _ & Hz1').
      destruct (multi_protect_inv kr2.(indirect_reader) _ v2 Htail2 Hval2)
        as (z2 & _ & _ & Hz2').
      rewrite Hz1', Hz2'.
      assert (Hc : flows_to kappa.(indirect_reader) l -> False).
      { intro hflow. simpl in HVsum. specialize (HVsum hflow).
        destruct HVsum as
          [(u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1) |
           (u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1)];
        [ inversion E2 | inversion E1 ]. }
      apply (V_protect_contra l T0 kappa.(indirect_reader)
               kr1.(indirect_reader) kr2.(indirect_reader) z1 z2 Hc).
    + (* inr / inl *)
      destruct D1 as (w1 & kr1 & Ht1 & Hw1 & Hfl1 & Htail1).
      destruct D2 as (w2 & kr2 & Ht2 & Hw2 & Hfl2 & Htail2).
      assert (HVsum : V l (Ty_Sum T1 T2 kappa) (tm_inr w1 kr1) (tm_inl w2 kr2)).
      { exact (IHt l s1 s2 (conj Hlc HR) (tm_inr w1 kr1) (tm_inl w2 kr2)
                 (conj Ht1 (v_inr w1 kr1 Hw1)) (conj Ht2 (v_inl w2 kr2 Hw2))). }
      destruct (multi_protect_inv kr1.(indirect_reader) _ v1 Htail1 Hval1)
        as (z1 & _ & _ & Hz1').
      destruct (multi_protect_inv kr2.(indirect_reader) _ v2 Htail2 Hval2)
        as (z2 & _ & _ & Hz2').
      rewrite Hz1', Hz2'.
      assert (Hc : flows_to kappa.(indirect_reader) l -> False).
      { intro hflow. simpl in HVsum. specialize (HVsum hflow).
        destruct HVsum as
          [(u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1) |
           (u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1)];
        [ inversion E1 | inversion E2 ]. }
      apply (V_protect_contra l T0 kappa.(indirect_reader)
               kr1.(indirect_reader) kr2.(indirect_reader) z1 z2 Hc).
    + (* inr / inr *)
      destruct D1 as (w1 & kr1 & Ht1 & Hw1 & Hfl1 & Htail1).
      destruct D2 as (w2 & kr2 & Ht2 & Hw2 & Hfl2 & Htail2).
      assert (HVsum : V l (Ty_Sum T1 T2 kappa) (tm_inr w1 kr1) (tm_inr w2 kr2)).
      { exact (IHt l s1 s2 (conj Hlc HR) (tm_inr w1 kr1) (tm_inr w2 kr2)
                 (conj Ht1 (v_inr w1 kr1 Hw1)) (conj Ht2 (v_inr w2 kr2 Hw2))). }
      assert (Hcond : flows_to kappa.(indirect_reader) l ->
                security_le kr1 kappa /\ security_le kr2 kappa /\ V l T2 w1 w2).
      { intro hflow. simpl in HVsum. specialize (HVsum hflow).
        destruct HVsum as
          [(u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1) |
           (u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1)].
        - inversion E1.
        - inversion E1; inversion E2; subst. exact (conj S1 (conj S2 HV1)). }
      destruct (multi_protect_inv kr1.(indirect_reader) _ v1 Htail1 Hval1)
        as (z1 & Hz1 & Hvz1 & Hz1').
      destruct (multi_protect_inv kr2.(indirect_reader) _ v2 Htail2 Hval2)
        as (z2 & Hz2 & Hvz2 & Hz2').
      assert (Hbody_cond : flows_to kappa.(indirect_reader) l -> V l T0 z1 z2).
      { intro hflow. destruct (Hcond hflow) as [S1 [S2 HV1]].
        pose proof (IHbody2 x HxL l
          (fun y => if Nat.eqb y x then w1 else s1 y)
          (fun y => if Nat.eqb y x then w2 else s2 y)
          (env_rel_update l Gamma0 s1 s2 x T2 w1 w2 (conj Hlc HR) Hw1 Hw2 HV1)) as HRb.
        assert (He1 : subst_env (fun y => if Nat.eqb y x then w1 else s1 y)
                       (open body2 (tm_fvar x)) = open (subst_env s1 body2) w1).
        { apply (subst_env_open_rec s1 x w1 body2 0).
          - intros y Hy. exact (proj1 (Hlc y)).
          - exact Hxb2. }
        assert (He2 : subst_env (fun y => if Nat.eqb y x then w2 else s2 y)
                       (open body2 (tm_fvar x)) = open (subst_env s2 body2) w2).
        { apply (subst_env_open_rec s2 x w2 body2 0).
          - intros y Hy. exact (proj2 (Hlc y)).
          - exact Hxb2. }
        rewrite He1, He2 in HRb.
        apply HRb; split; assumption. }
      rewrite Hz1', Hz2'.
      apply (V_protect_intro_cond l T0 kappa.(indirect_reader)
               kr1.(indirect_reader) kr2.(indirect_reader) z1 z2).
      * intro h. exact (proj2 (proj1 (Hcond h))).
      * intro h. exact (proj2 (proj1 (proj2 (Hcond h)))).
      * exact Hbody_cond.
  - (* T_Protect *) destruct Henv as [Hlc HR].
    unfold R. intros v1 v2 [Ev1 Hval1] [Ev2 Hval2].
    destruct (multi_protect_inv lp (subst_env s1 t) v1 Ev1 Hval1) as (z1 & Hz1 & Hvz1 & Heq1).
    destruct (multi_protect_inv lp (subst_env s2 t) v2 Ev2 Hval2) as (z2 & Hz2 & Hvz2 & Heq2).
    rewrite Heq1, Heq2.
    exact (V_protect_adjust T0 l z1 z2
             (IHt l s1 s2 (conj Hlc HR) z1 z2 (conj Hz1 Hvz1) (conj Hz2 Hvz2))
             lp lp lp (flows_to_refl lp) (flows_to_refl lp)).
  - (* T_Sub *) destruct Henv as [Hlc HR].
    apply (R_subtype l T0 U Hsub).
    apply IHt. exact (conj Hlc HR).
  - (* T_If *) destruct Henv as [Hlc HR].
    unfold R. intros v1 v2 [Ev1 Hval1] [Ev2 Hval2].
    destruct (multi_if_inv _ _ _ _ _ Ev1 Hval1) as [D1 | D1];
      destruct (multi_if_inv _ _ _ _ _ Ev2 Hval2) as [D2 | D2].
    + (* inl / inl *)
      destruct D1 as (w1 & kr1 & Hc1 & Hw1 & Hfl1 & Htail1).
      destruct D2 as (w2 & kr2 & Hc2 & Hw2 & Hfl2 & Htail2).
      assert (HVc : V l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                (tm_inl w1 kr1) (tm_inl w2 kr2)).
      { exact (IHc l s1 s2 (conj Hlc HR) (tm_inl w1 kr1) (tm_inl w2 kr2)
                 (conj Hc1 (v_inl w1 kr1 Hw1)) (conj Hc2 (v_inl w2 kr2 Hw2))). }
      assert (Hcond : flows_to k.(indirect_reader) l ->
                security_le kr1 k /\ security_le kr2 k).
      { intro hflow. simpl in HVc. specialize (HVc hflow).
        destruct HVc as
          [(u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1) |
           (u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1)].
        - inversion E1; inversion E2; subst. exact (conj S1 S2).
        - inversion E1. }
      destruct (multi_protect_inv kr1.(indirect_reader) (subst_env s1 yes) v1 Htail1 Hval1)
        as (z1 & Hz1 & Hvz1 & Hz1').
      destruct (multi_protect_inv kr2.(indirect_reader) (subst_env s2 yes) v2 Htail2 Hval2)
        as (z2 & Hz2 & Hvz2 & Hz2').
      rewrite Hz1', Hz2'.
      apply (V_protect_intro_cond l T0 k.(indirect_reader)
               kr1.(indirect_reader) kr2.(indirect_reader) z1 z2).
      * intro h. exact (proj2 (proj1 (Hcond h))).
      * intro h. exact (proj2 (proj2 (Hcond h))).
      * intro hh. exact (IHyes l s1 s2 (conj Hlc HR) z1 z2
                          (conj Hz1 Hvz1) (conj Hz2 Hvz2)).
    + (* inl / inr *)
      destruct D1 as (w1 & kr1 & Hc1 & Hw1 & Hfl1 & Htail1).
      destruct D2 as (w2 & kr2 & Hc2 & Hw2 & Hfl2 & Htail2).
      assert (HVc : V l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                (tm_inl w1 kr1) (tm_inr w2 kr2)).
      { exact (IHc l s1 s2 (conj Hlc HR) (tm_inl w1 kr1) (tm_inr w2 kr2)
                 (conj Hc1 (v_inl w1 kr1 Hw1)) (conj Hc2 (v_inr w2 kr2 Hw2))). }
      destruct (multi_protect_inv kr1.(indirect_reader) (subst_env s1 yes) v1 Htail1 Hval1)
        as (z1 & _ & _ & Hz1').
      destruct (multi_protect_inv kr2.(indirect_reader) (subst_env s2 no) v2 Htail2 Hval2)
        as (z2 & _ & _ & Hz2').
      rewrite Hz1', Hz2'.
      assert (Hcontra : flows_to k.(indirect_reader) l -> False).
      { intro hflow. simpl in HVc. specialize (HVc hflow).
        destruct HVc as
          [(u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1) |
           (u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1)];
        [ inversion E2 | inversion E1 ]. }
      apply (V_protect_contra l T0 k.(indirect_reader)
               kr1.(indirect_reader) kr2.(indirect_reader) z1 z2 Hcontra).
    + (* inr / inl *)
      destruct D1 as (w1 & kr1 & Hc1 & Hw1 & Hfl1 & Htail1).
      destruct D2 as (w2 & kr2 & Hc2 & Hw2 & Hfl2 & Htail2).
      assert (HVc : V l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                (tm_inr w1 kr1) (tm_inl w2 kr2)).
      { exact (IHc l s1 s2 (conj Hlc HR) (tm_inr w1 kr1) (tm_inl w2 kr2)
                 (conj Hc1 (v_inr w1 kr1 Hw1)) (conj Hc2 (v_inl w2 kr2 Hw2))). }
      destruct (multi_protect_inv kr1.(indirect_reader) (subst_env s1 no) v1 Htail1 Hval1)
        as (z1 & _ & _ & Hz1').
      destruct (multi_protect_inv kr2.(indirect_reader) (subst_env s2 yes) v2 Htail2 Hval2)
        as (z2 & _ & _ & Hz2').
      rewrite Hz1', Hz2'.
      assert (Hcontra : flows_to k.(indirect_reader) l -> False).
      { intro hflow. simpl in HVc. specialize (HVc hflow).
        destruct HVc as
          [(u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1) |
           (u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1)];
        [ inversion E1 | inversion E2 ]. }
      apply (V_protect_contra l T0 k.(indirect_reader)
               kr1.(indirect_reader) kr2.(indirect_reader) z1 z2 Hcontra).
    + (* inr / inr *)
      destruct D1 as (w1 & kr1 & Hc1 & Hw1 & Hfl1 & Htail1).
      destruct D2 as (w2 & kr2 & Hc2 & Hw2 & Hfl2 & Htail2).
      assert (HVc : V l (Ty_Sum (Ty_Unit public) (Ty_Unit public) k)
                (tm_inr w1 kr1) (tm_inr w2 kr2)).
      { exact (IHc l s1 s2 (conj Hlc HR) (tm_inr w1 kr1) (tm_inr w2 kr2)
                 (conj Hc1 (v_inr w1 kr1 Hw1)) (conj Hc2 (v_inr w2 kr2 Hw2))). }
      assert (Hcond : flows_to k.(indirect_reader) l ->
                security_le kr1 k /\ security_le kr2 k).
      { intro hflow. simpl in HVc. specialize (HVc hflow).
        destruct HVc as
          [(u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1) |
           (u1 & u2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1)].
        - inversion E1.
        - inversion E1; inversion E2; subst. exact (conj S1 S2). }
      destruct (multi_protect_inv kr1.(indirect_reader) (subst_env s1 no) v1 Htail1 Hval1)
        as (z1 & Hz1 & Hvz1 & Hz1').
      destruct (multi_protect_inv kr2.(indirect_reader) (subst_env s2 no) v2 Htail2 Hval2)
        as (z2 & Hz2 & Hvz2 & Hz2').
      rewrite Hz1', Hz2'.
      apply (V_protect_intro_cond l T0 k.(indirect_reader)
               kr1.(indirect_reader) kr2.(indirect_reader) z1 z2).
      * intro h. exact (proj2 (proj1 (Hcond h))).
      * intro h. exact (proj2 (proj2 (Hcond h))).
      * intro hh. exact (IHno l s1 s2 (conj Hlc HR) z1 z2
                          (conj Hz1 Hvz1) (conj Hz2 Hvz2)).
Qed.

Lemma V_ground_erase : forall (T : ty) (kappa0 : security),
  ground T -> transparent_at kappa0 T ->
  forall v1 v2, V kappa0.(indirect_reader) T v1 v2 ->
    erase_security v1 = erase_security v2.
Proof.
  induction T as [k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k];
    intros kappa0 Hg Htr v1 v2 HV; simpl in *.
  - apply HV. exact (proj2 (proj1 Htr)).
  - destruct Hg as [Hg1 Hg2]. destruct Htr as [Hsle [Htr1 Htr2]].
    destruct (HV (proj2 Hsle)) as
      [(w1 & w2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HVw) |
       (w1 & w2 & kk1 & kk2 & E1 & E2 & S1 & S2 & HVw)].
    + rewrite E1, E2. simpl. f_equal.
      apply (IH1 kappa0 Hg1 Htr1 w1 w2 HVw).
    + rewrite E1, E2. simpl. f_equal.
      apply (IH2 kappa0 Hg2 Htr2 w1 w2 HVw).
  - destruct Hg as [Hg1 Hg2]. destruct Htr as [Hsle [Htr1 Htr2]].
    destruct (HV (proj2 Hsle)) as
      (w1 & w2 & w1' & w2' & kk1 & kk2 & E1 & E2 & S1 & S2 & HV1 & HV2).
    rewrite E1, E2. simpl. f_equal.
    + apply (IH1 kappa0 Hg1 Htr1 w1 w1' HV1).
    + apply (IH2 kappa0 Hg2 Htr2 w2 w2' HV2).
  - contradiction.
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
  destruct HC as [L HC].
  set (x0 := fresh (L ++ fv (plug C (tm_fvar 0)))).
  assert (HxL : ~ In x0 L).
  { intro Hin. pose proof (fresh_notin (L ++ fv (plug C (tm_fvar 0)))) as Hni.
    apply Hni. apply in_or_app. left. exact Hin. }
  assert (HxC : ~ In x0 (fv (plug C (tm_fvar 0)))).
  { intro Hin. pose proof (fresh_notin (L ++ fv (plug C (tm_fvar 0)))) as Hni.
    apply Hni. apply in_or_app. right. exact Hin. }
  assert (Hxctx : ~ In x0 (ctx_atoms C)).
  { intro Hin. apply HxC. apply (proj2 (in_fv_plug C 0 x0)). left. exact Hin. }
  assert (Htyp : has_type (update empty x0 T_secret) (plug C (tm_fvar x0)) T_result).
  { apply HC. exact HxL. }
  assert (Hlc1 : locally_closed t1) by (exact (has_type_lc empty t1 T_secret Ht1)).
  assert (Hlc2 : locally_closed t2) by (exact (has_type_lc empty t2 T_secret Ht2)).
  set (s1 := fun y => if Nat.eqb y x0 then t1 else tm_fvar y).
  set (s2 := fun y => if Nat.eqb y x0 then t2 else tm_fvar y).
  assert (Henv : env_rel (security_of T_result).(indirect_reader)
                   (update empty x0 T_secret) s1 s2).
  { split.
    - intros y. unfold s1, s2. destruct (Nat.eqb y x0) eqn:E; simpl.
      + split; assumption.
      + split; exact I.
    - intros y T Hy. simpl in Hy.
      destruct (Nat.eqb y x0) eqn:E; simpl in Hy.
      + apply Nat.eqb_eq in E. subst y. inversion Hy. subst T.
        unfold R. intros v1 v2 _ _.
        unfold s1, s2. simpl.
        apply V_vacuous. exact Hnf.
      + discriminate Hy. }
  pose proof (fundamental (update empty x0 T_secret) (plug C (tm_fvar x0)) T_result Htyp
                (security_of T_result).(indirect_reader) s1 s2 Henv) as HR.
  assert (Hs1 : subst_env s1 (plug C (tm_fvar x0)) = plug C t1).
  { unfold s1. apply (subst_env_plug_hole C x0 t1 Hxctx). }
  assert (Hs2 : subst_env s2 (plug C (tm_fvar x0)) = plug C t2).
  { unfold s2. apply (subst_env_plug_hole C x0 t2 Hxctx). }
  rewrite Hs1, Hs2 in HR.
  unfold same_result. intros v1 v2 Ev1 Ev2.
  apply (V_ground_erase T_result (security_of T_result) Hg Htr v1 v2).
  apply HR; assumption.
Qed.
