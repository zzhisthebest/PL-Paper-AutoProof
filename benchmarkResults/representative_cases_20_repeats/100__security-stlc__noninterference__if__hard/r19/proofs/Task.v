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
(* Fresh atoms                                                   *)
(* ============================================================ *)

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Lemma max_list_spec : forall (l : list nat) (x : nat), In x l -> x <= max_list l.
Proof.
  induction l as [| y ys IH]; simpl; intros x Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + transitivity (max_list ys); [apply IH; auto | apply Nat.le_max_r].
Qed.

Lemma exists_fresh : forall L : list atom, exists x : atom, ~ In x L.
Proof.
  intros L. exists (S (max_list L)). intro H.
  pose proof (max_list_spec L _ H). lia.
Qed.

Lemma exists_fresh_two : forall L1 L2 : list atom,
    exists x : atom, ~ In x L1 /\ ~ In x L2.
Proof.
  intros L1 L2. destruct (exists_fresh (L1 ++ L2)) as [x Hx].
  exists x. split; intro H; apply Hx; apply in_or_app; auto.
Qed.

(* ============================================================ *)
(* Label and security algebra                                    *)
(* ============================================================ *)

Lemma flows_to_refl : forall l : label, flows_to l l.
Proof. destruct l; simpl; auto. Qed.

Lemma flows_to_trans : forall l1 l2 l3 : label,
    flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof. destruct l1, l2, l3; simpl; auto. Qed.

Lemma flows_to_inv : forall l1 l2 : label, ~ flows_to l1 l2 -> l1 = High /\ l2 = Low.
Proof. destruct l1, l2; simpl; tauto. Qed.

Lemma flows_to_high_eq : forall l : label, flows_to High l -> l = High.
Proof. intro l; destruct l; simpl; intros H; [contradiction | reflexivity]. Qed.

Lemma flows_to_low_eq : forall l : label, flows_to l Low -> l = Low.
Proof. intro l; destruct l; simpl; intros H; [reflexivity | contradiction]. Qed.

Lemma join_low_l : forall l : label, join l Low = l.
Proof. destruct l; simpl; auto. Qed.

Lemma join_low_r : forall l : label, join Low l = l.
Proof. destruct l; simpl; auto. Qed.

Lemma join_high_l : forall l : label, join l High = High.
Proof. destruct l; simpl; auto. Qed.

Lemma join_high_r : forall l : label, join High l = High.
Proof. destruct l; simpl; auto. Qed.

Lemma security_le_refl : forall k : security, security_le k k.
Proof. intros [r i]; simpl. split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3 : security,
    security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3]; simpl.
  intros [a b] [c d]. split; eapply flows_to_trans; eauto.
Qed.

Lemma security_le_ind_low : forall k1 k2 : security,
    security_le k1 k2 -> k2.(indirect_reader) = Low -> k1.(indirect_reader) = Low.
Proof.
  intros [r1 i1] [r2 i2]; simpl. intros [_ H] Hi.
  subst i2. apply flows_to_low_eq in H. auto.
Qed.

Lemma security_le_ind_high : forall k1 k2 : security,
    security_le k1 k2 -> k1.(indirect_reader) = High -> k2.(indirect_reader) = High.
Proof.
  intros [r1 i1] [r2 i2]; simpl. intros [_ H] Hi.
  subst i1. apply flows_to_high_eq in H. auto.
Qed.

Lemma protect_security_low : forall k : security, protect_security k Low = k.
Proof.
  intros [r i]; unfold protect_security; simpl.
  rewrite join_low_l, join_low_l. reflexivity.
Qed.

Lemma protect_security_high : forall k : security,
    protect_security k High = {| reader := High; indirect_reader := High |}.
Proof.
  intros [r i]; unfold protect_security; simpl.
  rewrite join_high_l, join_high_l. reflexivity.
Qed.

Lemma protect_security_le : forall k1 k2 : security, security_le k1 k2 ->
    forall l1 l2 : label, flows_to l1 l2 ->
    security_le (protect_security k1 l1) (protect_security k2 l2).
Proof.
  intros [r1 i1] [r2 i2]; simpl. intros [Hr Hi] l1 l2 Hl.
  split; unfold join; destruct l1, l2, r1, r2, i1, i2; simpl in *; auto.
Qed.

Lemma wf_security_protect : forall (k : security) (l : label),
    wf_security k -> wf_security (protect_security k l).
Proof.
  intros k l H. destruct l.
  - rewrite protect_security_low; auto.
  - rewrite protect_security_high. unfold wf_security. simpl. auto.
Qed.

Lemma wf_security_high_eq : forall k : security, wf_security k ->
    k.(indirect_reader) = High ->
    k = {| reader := High; indirect_reader := High |}.
Proof.
  intros [r i]; simpl. intros Hwf Hi. subst i.
  unfold wf_security in Hwf; simpl in Hwf.
  apply flows_to_high_eq in Hwf. subst r. reflexivity.
Qed.

(* ============================================================ *)
(* Type lemmas                                                   *)
(* ============================================================ *)

Lemma ty_protect_low : forall T : ty, ty_protect Low T = T.
Proof.
  intros T; destruct T; simpl; rewrite protect_security_low; reflexivity.
Qed.

Lemma ty_protect_high_sec : forall T : ty,
    security_of (ty_protect High T) =
      {| reader := High; indirect_reader := High |}.
Proof.
  intros T; destruct T; simpl; apply protect_security_high.
Qed.

Lemma security_of_ty_protect : forall (T : ty) (l : label),
    security_of (ty_protect l T) = protect_security (security_of T) l.
Proof. intros T; destruct T; reflexivity. Qed.

Lemma wf_ty_security : forall T : ty, wf_ty T -> wf_security (security_of T).
Proof. intros T; destruct T; simpl; intros H; tauto. Qed.

Lemma wf_ty_protect : forall (T : ty) (l : label), wf_ty T -> wf_ty (ty_protect l T).
Proof.
  intros T; destruct T; simpl; intros l H.
  - apply wf_security_protect; auto.
  - destruct H as [H1 [H2 H3]]. split; [auto | split; [auto | apply wf_security_protect; auto]].
  - destruct H as [H1 [H2 H3]]. split; [auto | split; [auto | apply wf_security_protect; auto]].
  - destruct H as [H1 [H2 H3]]. split; [auto | split; [auto | apply wf_security_protect; auto]].
Qed.

Lemma wf_ty_security_ind_high : forall T : ty, wf_ty T ->
    (security_of T).(indirect_reader) = High ->
    security_of T = {| reader := High; indirect_reader := High |}.
Proof. intros T Hwf. apply wf_security_high_eq. apply wf_ty_security; auto. Qed.

(* ============================================================ *)
(* Erasure and protection of values                              *)
(* ============================================================ *)

Lemma erase_security_protect_value : forall (v : tm) (l : label),
    erase_security (protect_value v l) = erase_security v.
Proof. intros v l; destruct v; simpl; reflexivity. Qed.

Lemma protect_value_low : forall v : tm, protect_value v Low = v.
Proof.
  intros v; destruct v; simpl; try reflexivity;
  rewrite protect_security_low; reflexivity.
Qed.

Lemma protect_security_high_eq : forall k : security,
    protect_security k High = {| reader := High; indirect_reader := High |}.
Proof. apply protect_security_high. Qed.

Lemma protect_value_value : forall (v : tm), value v -> forall l : label,
    value (protect_value v l).
Proof.
  intros v Hv. induction Hv; intros l; simpl.
  - apply v_unit.
  - apply v_abs. simpl. exact H.
  - apply v_pair; auto.
  - apply v_inl; auto.
  - apply v_inr; auto.
Qed.

Lemma value_lc : forall v : tm, value v -> locally_closed v.
Proof. intros v Hv. induction Hv; unfold locally_closed; simpl; auto. Qed.

(* ============================================================ *)
(* Big-step evaluation                                           *)
(* ============================================================ *)

Inductive eval : tm -> tm -> Prop :=
  | E_Unit : forall k, eval (tm_unit k) (tm_unit k)
  | E_Abs : forall T body k, value (tm_abs T body k) ->
      eval (tm_abs T body k) (tm_abs T body k)
  | E_Pair : forall t1 t2 k v1 v2, eval t1 v1 -> eval t2 v2 ->
      eval (tm_pair t1 t2 k) (tm_pair v1 v2 k)
  | E_Fst : forall t r v1 v2 k w, eval t (tm_pair v1 v2 k) ->
      value v1 -> value v2 -> flows_to k.(reader) r ->
      eval (tm_protect k.(indirect_reader) v1) w -> eval (tm_fst t r) w
  | E_Snd : forall t r v1 v2 k w, eval t (tm_pair v1 v2 k) ->
      value v1 -> value v2 -> flows_to k.(reader) r ->
      eval (tm_protect k.(indirect_reader) v2) w -> eval (tm_snd t r) w
  | E_Inl : forall t k v, eval t v -> eval (tm_inl t k) (tm_inl v k)
  | E_Inr : forall t k v, eval t v -> eval (tm_inr t k) (tm_inr v k)
  | E_CaseL : forall t b1 b2 r v k w, eval t (tm_inl v k) -> value v ->
      flows_to k.(reader) r ->
      eval (tm_protect k.(indirect_reader) (open b1 v)) w ->
      eval (tm_case t b1 b2 r) w
  | E_CaseR : forall t b1 b2 r v k w, eval t (tm_inr v k) -> value v ->
      flows_to k.(reader) r ->
      eval (tm_protect k.(indirect_reader) (open b2 v)) w ->
      eval (tm_case t b1 b2 r) w
  | E_Protect : forall t l v, eval t v -> eval (tm_protect l t) (protect_value v l)
  | E_App : forall t1 t2 T body k r arg w,
      eval t1 (tm_abs T body k) -> eval t2 arg ->
      value (tm_abs T body k) -> value arg ->
      flows_to k.(reader) r ->
      eval (tm_protect k.(indirect_reader) (open body arg)) w ->
      eval (tm_app t1 t2 r) w
  | E_IfL : forall c yes no r v k w, eval c (tm_inl v k) -> value v ->
      flows_to k.(reader) r -> eval (tm_protect k.(indirect_reader) yes) w ->
      eval (tm_if c yes no r) w
  | E_IfR : forall c yes no r v k w, eval c (tm_inr v k) -> value v ->
      flows_to k.(reader) r -> eval (tm_protect k.(indirect_reader) no) w ->
      eval (tm_if c yes no r) w.

Lemma eval_value : forall t v, eval t v -> value v.
Proof.
  intros t v H. induction H; eauto using protect_value_value, v_unit, v_abs, v_pair, v_inl, v_inr.
Qed.

Lemma value_eval : forall v, value v -> eval v v.
Proof.
  intros v Hv. induction Hv; simpl;
  eauto using E_Unit, E_Abs, v_abs, E_Pair, E_Inl, E_Inr.
Qed.

Lemma eval_value_unique : forall t w, eval t w -> value t -> w = t.
Proof.
  intros t w He. induction He; intros Hv.
  - reflexivity.
  - reflexivity.
  - inversion Hv; subst. f_equal; auto.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv; subst. f_equal; auto.
  - inversion Hv; subst. f_equal; auto.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
Qed.

Lemma eval_lc : forall t v, eval t v -> locally_closed v.
Proof. intros t v H. apply value_lc. apply eval_value in H. exact H. Qed.

(* ============================================================ *)
(* Locally nameless infrastructure                               *)
(* ============================================================ *)

Lemma lc_at_mono : forall (k k' : nat) (t : tm), k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t. revert k k'.
  induction t as [ i | a | s | T body IHbody s0 | t1 IHt1 t2 IHt2 r | t1 IHt1 t2 IHt2 s
                 | t IHt r | t IHt r | t IHt s | t IHt s | t0 IHt0 b1 IHb1 b2 IHb2 r
                 | l t IHt | t0 IHt0 y IHy n IHn r ];
  simpl; intros k k' Hle H.
  - lia.
  - exact I.
  - exact I.
  - apply (IHbody (S k) (S k')); [lia | exact H].
  - destruct H as [H1 H2]. split; [apply (IHt1 k k') | apply (IHt2 k k')]; auto.
  - destruct H as [H1 H2]. split; [apply (IHt1 k k') | apply (IHt2 k k')]; auto.
  - apply (IHt k k'); auto.
  - apply (IHt k k'); auto.
  - apply (IHt k k'); auto.
  - apply (IHt k k'); auto.
  - destruct H as [H1 [H2 H3]]. split; [apply (IHt0 k k') | split;
      [apply (IHb1 (S k) (S k')) | apply (IHb2 (S k) (S k'))]]; auto; lia.
  - apply (IHt k k'); auto.
  - destruct H as [H1 [H2 H3]]. split; [apply (IHt0 k k') | split;
      [apply (IHy k k') | apply (IHn k k')]]; auto.
Qed.

Lemma open_rec_lc : forall (k : nat) (t : tm), lc_at k t -> forall u : tm,
    open_rec k u t = t.
Proof.
  intros k t. revert k.
  induction t as [ i | a | s | T body IHbody s0 | t1 IHt1 t2 IHt2 r | t1 IHt1 t2 IHt2 s
                 | t IHt r | t IHt r | t IHt s | t IHt s | t0 IHt0 b1 IHb1 b2 IHb2 r
                 | l t IHt | t0 IHt0 y IHy n IHn r ];
  simpl; intros k Ht u.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. apply (IHbody (S k) Ht u).
  - destruct Ht as [H1 H2]. rewrite (IHt1 k H1 u), (IHt2 k H2 u). reflexivity.
  - destruct Ht as [H1 H2]. rewrite (IHt1 k H1 u), (IHt2 k H2 u). reflexivity.
  - rewrite (IHt k Ht u). reflexivity.
  - rewrite (IHt k Ht u). reflexivity.
  - rewrite (IHt k Ht u). reflexivity.
  - rewrite (IHt k Ht u). reflexivity.
  - destruct Ht as [H1 [H2 H3]].
    rewrite (IHt0 k H1 u), (IHb1 (S k) H2 u), (IHb2 (S k) H3 u). reflexivity.
  - rewrite (IHt k Ht u). reflexivity.
  - destruct Ht as [H1 [H2 H3]].
    rewrite (IHt0 k H1 u), (IHy k H2 u), (IHn k H3 u). reflexivity.
Qed.

Lemma open_lc_at : forall (k : nat) (u t : tm),
    lc_at k u -> lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k u t. revert k.
  induction t as [ i | a | s | T body IHbody s0 | t1 IHt1 t2 IHt2 r | t1 IHt1 t2 IHt2 s
                 | t IHt r | t IHt r | t IHt s | t IHt s | t0 IHt0 b1 IHb1 b2 IHb2 r
                 | l t IHt | t0 IHt0 y IHy n IHn r ];
  simpl; intros k Hu Ht.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst i; lia.
    + apply Nat.eqb_neq in E; simpl in Ht; lia.
  - exact I.
  - exact I.
  - apply (IHbody (S k)).
    + apply lc_at_mono with (k := k); auto; lia.
    + exact Ht.
  - destruct Ht as [H1 H2]. split.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - destruct Ht as [H1 H2]. split.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct Ht as [H1 [H2 H3]]. split.
    + eapply IHt0; eauto.
    + split.
      * apply (IHb1 (S k)); [apply lc_at_mono with (k:=k); auto; lia | exact H2].
      * apply (IHb2 (S k)); [apply lc_at_mono with (k:=k); auto; lia | exact H3].
  - eapply IHt; eauto.
  - destruct Ht as [H1 [H2 H3]]. split.
    + eapply IHt0; eauto.
    + split; [eapply IHy; eauto | eapply IHn; eauto].
Qed.

Lemma not_in_app : forall (x : atom) (l1 l2 : list atom),
    ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros x l1 l2 H. split; intro H1; apply H; apply in_or_app; auto.
Qed.

Lemma subst_fresh : forall (x : atom) (u t : tm), ~ In x (fv t) -> subst x u t = t.
Proof.
  intros x u t. revert x u.
  induction t as [ i | a | s | T body IHbody s0 | t1 IHt1 t2 IHt2 r | t1 IHt1 t2 IHt2 s
                 | t IHt r | t IHt r | t IHt s | t IHt s | t0 IHt0 b1 IHb1 b2 IHb2 r
                 | l t IHt | t0 IHt0 y IHy n IHn r ];
  simpl; intros x u Hx.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst a; exfalso; apply Hx; simpl; auto.
    + reflexivity.
  - reflexivity.
  - f_equal. apply IHbody; simpl in Hx; exact Hx.
  - destruct (not_in_app x (fv t1) (fv t2) Hx) as [H1 H2].
    rewrite (IHt1 x u H1), (IHt2 x u H2). reflexivity.
  - destruct (not_in_app x (fv t1) (fv t2) Hx) as [H1 H2].
    rewrite (IHt1 x u H1), (IHt2 x u H2). reflexivity.
  - f_equal; apply IHt; simpl in Hx; exact Hx.
  - f_equal; apply IHt; simpl in Hx; exact Hx.
  - f_equal; apply IHt; simpl in Hx; exact Hx.
  - f_equal; apply IHt; simpl in Hx; exact Hx.
  - simpl in Hx.
    destruct (not_in_app x (fv t0) (fv b1 ++ fv b2) Hx) as [Hx0 Hx1].
    destruct (not_in_app x (fv b1) (fv b2) Hx1) as [Hxb1 Hxb2].
    rewrite (IHt0 x u Hx0), (IHb1 x u Hxb1), (IHb2 x u Hxb2). reflexivity.
  - f_equal; apply IHt; simpl in Hx; exact Hx.
  - simpl in Hx.
    destruct (not_in_app x (fv t0) (fv y ++ fv n) Hx) as [Hx0 Hx1].
    destruct (not_in_app x (fv y) (fv n) Hx1) as [Hxy Hxn].
    rewrite (IHt0 x u Hx0), (IHy x u Hxy), (IHn x u Hxn). reflexivity.
Qed.

Lemma fv_open_rec_incl : forall (k : nat) (u t : tm) (x : atom),
    In x (fv t) -> In x (fv (open_rec k u t)).
Proof.
  intros k u t. revert k.
  induction t as [ i | a | s | T body IHbody s0 | t1 IHt1 t2 IHt2 r | t1 IHt1 t2 IHt2 s
                 | t IHt r | t IHt r | t IHt s | t IHt s | t0 IHt0 b1 IHb1 b2 IHb2 r
                 | l t IHt | t0 IHt0 y IHy n IHn r ];
  simpl; intros k x Hx.
  - contradiction.
  - exact Hx.
  - contradiction.
  - apply IHbody; auto.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app; left; apply IHt1; auto.
    + apply in_or_app; right; apply IHt2; auto.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app; left; apply IHt1; auto.
    + apply in_or_app; right; apply IHt2; auto.
  - apply IHt; auto.
  - apply IHt; auto.
  - apply IHt; auto.
  - apply IHt; auto.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app; left; apply IHt0; auto.
    + apply in_app_or in Hx as [Hx | Hx].
      * apply in_or_app; right; apply in_or_app; left; apply IHb1; auto.
      * apply in_or_app; right; apply in_or_app; right; apply IHb2; auto.
  - apply IHt; auto.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app; left; apply IHt0; auto.
    + apply in_app_or in Hx as [Hx | Hx].
      * apply in_or_app; right; apply in_or_app; left; apply IHy; auto.
      * apply in_or_app; right; apply in_or_app; right; apply IHn; auto.
Qed.

(* ============================================================ *)
(* Simultaneous substitution of free variables                   *)
(* ============================================================ *)

Fixpoint subst_env (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_unit k => tm_unit k
  | tm_abs T body k => tm_abs T (subst_env sigma body) k
  | tm_app t1 t2 r => tm_app (subst_env sigma t1) (subst_env sigma t2) r
  | tm_pair t1 t2 k => tm_pair (subst_env sigma t1) (subst_env sigma t2) k
  | tm_fst t1 r => tm_fst (subst_env sigma t1) r
  | tm_snd t1 r => tm_snd (subst_env sigma t1) r
  | tm_inl t1 k => tm_inl (subst_env sigma t1) k
  | tm_inr t1 k => tm_inr (subst_env sigma t1) k
  | tm_case t0 body1 body2 r =>
      tm_case (subst_env sigma t0) (subst_env sigma body1) (subst_env sigma body2) r
  | tm_protect l t1 => tm_protect l (subst_env sigma t1)
  | tm_if c yes no r =>
      tm_if (subst_env sigma c) (subst_env sigma yes) (subst_env sigma no) r
  end.

Definition id_env : atom -> tm := fun x => tm_fvar x.

Definition extend (x : atom) (u : tm) (sigma : atom -> tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Lemma subst_env_extend_id : forall (x : atom) (u t : tm),
    subst_env (extend x u id_env) t = subst x u t.
Proof.
  intros x u t. revert x u.
  induction t as [ i | a | s | T body IHbody s0 | t1 IHt1 t2 IHt2 r | t1 IHt1 t2 IHt2 s
                 | t IHt r | t IHt r | t IHt s | t IHt s | t0 IHt0 b1 IHb1 b2 IHb2 r
                 | l t IHt | t0 IHt0 y IHy n IHn r ];
  simpl; intros x u.
  - reflexivity.
  - unfold extend, id_env. simpl. reflexivity.
  - reflexivity.
  - f_equal. apply IHbody.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt0, IHb1, IHb2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt0, IHy, IHn. reflexivity.
Qed.

Lemma subst_env_lc : forall (sigma : atom -> tm) (k : nat) (t : tm),
    (forall x, lc_at 0 (sigma x)) -> lc_at k t -> lc_at k (subst_env sigma t).
Proof.
  intros sigma k t. revert k.
  induction t as [ i | a | s | T body IHbody s0 | t1 IHt1 t2 IHt2 r | t1 IHt1 t2 IHt2 s
                 | t IHt r | t IHt r | t IHt s | t IHt s | t0 IHt0 b1 IHb1 b2 IHb2 r
                 | l t IHt | t0 IHt0 y IHy n IHn r ];
  simpl; intros k Hsig Ht.
  - exact Ht.
  - apply lc_at_mono with (k := 0); auto; lia.
  - exact I.
  - apply IHbody; auto.
  - destruct Ht as [H1 H2]. split; [apply IHt1 | apply IHt2]; auto.
  - destruct Ht as [H1 H2]. split; [apply IHt1 | apply IHt2]; auto.
  - apply IHt; auto.
  - apply IHt; auto.
  - apply IHt; auto.
  - apply IHt; auto.
  - destruct Ht as [H1 [H2 H3]]. split; [apply IHt0 | split;
      [apply IHb1 | apply IHb2]]; auto.
  - apply IHt; auto.
  - destruct Ht as [H1 [H2 H3]]. split; [apply IHt0 | split;
      [apply IHy | apply IHn]]; auto.
Qed.

Lemma subst_env_extend_neq : forall (sigma : atom -> tm) (x : atom) (u : tm) (t : tm),
    ~ In x (fv t) -> subst_env (extend x u sigma) t = subst_env sigma t.
Proof.
  intros sigma x u t. revert x u.
  induction t as [ i | a | s | T body IHbody s0 | t1 IHt1 t2 IHt2 r | t1 IHt1 t2 IHt2 s
                 | t IHt r | t IHt r | t IHt s | t IHt s | t0 IHt0 b1 IHb1 b2 IHb2 r
                 | l t IHt | t0 IHt0 y IHy n IHn r ];
  simpl; intros x u Hx.
  - reflexivity.
  - unfold extend. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst a; exfalso; apply Hx; simpl; auto.
    + reflexivity.
  - reflexivity.
  - f_equal. apply IHbody; simpl in Hx; exact Hx.
  - destruct (not_in_app x (fv t1) (fv t2) Hx) as [H1 H2].
    rewrite (IHt1 x u H1), (IHt2 x u H2). reflexivity.
  - destruct (not_in_app x (fv t1) (fv t2) Hx) as [H1 H2].
    rewrite (IHt1 x u H1), (IHt2 x u H2). reflexivity.
  - f_equal; apply IHt; simpl in Hx; exact Hx.
  - f_equal; apply IHt; simpl in Hx; exact Hx.
  - f_equal; apply IHt; simpl in Hx; exact Hx.
  - f_equal; apply IHt; simpl in Hx; exact Hx.
  - simpl in Hx.
    destruct (not_in_app x (fv t0) (fv b1 ++ fv b2) Hx) as [Hx0 Hx1].
    destruct (not_in_app x (fv b1) (fv b2) Hx1) as [Hxb1 Hxb2].
    rewrite (IHt0 x u Hx0), (IHb1 x u Hxb1), (IHb2 x u Hxb2). reflexivity.
  - f_equal; apply IHt; simpl in Hx; exact Hx.
  - simpl in Hx.
    destruct (not_in_app x (fv t0) (fv y ++ fv n) Hx) as [Hx0 Hx1].
    destruct (not_in_app x (fv y) (fv n) Hx1) as [Hxy Hxn].
    rewrite (IHt0 x u Hx0), (IHy x u Hxy), (IHn x u Hxn). reflexivity.
Qed.

Lemma subst_env_open : forall (sigma : atom -> tm) (k : nat) (t : tm) (x : atom),
    (forall y, lc_at 0 (sigma y)) ->
    subst_env sigma (open_rec k (tm_fvar x) t) = open_rec k (sigma x) (subst_env sigma t).
Proof.
  intros sigma k t x. revert k.
  induction t as [ i | a | s | T body IHbody s0 | t1 IHt1 t2 IHt2 r | t1 IHt1 t2 IHt2 s
                 | t IHt r | t IHt r | t IHt s | t IHt s | t0 IHt0 b1 IHb1 b2 IHb2 r
                 | l t IHt | t0 IHt0 y IHy n IHn r ];
  simpl; intros k Hsig.
  - destruct (Nat.eqb k i); reflexivity.
  - rewrite open_rec_lc.
    + reflexivity.
    + apply lc_at_mono with (k := 0); auto; lia.
  - reflexivity.
  - f_equal. apply (IHbody (S k) Hsig).
  - rewrite (IHt1 k Hsig), (IHt2 k Hsig). reflexivity.
  - rewrite (IHt1 k Hsig), (IHt2 k Hsig). reflexivity.
  - f_equal; apply (IHt k Hsig).
  - f_equal; apply (IHt k Hsig).
  - f_equal; apply (IHt k Hsig).
  - f_equal; apply (IHt k Hsig).
  - rewrite (IHt0 k Hsig), (IHb1 (S k) Hsig), (IHb2 (S k) Hsig). reflexivity.
  - f_equal; apply (IHt k Hsig).
  - rewrite (IHt0 k Hsig), (IHy k Hsig), (IHn k Hsig). reflexivity.
Qed.

Lemma subst_env_extend_lc : forall (sigma : atom -> tm) (x : atom) (u : tm),
    (forall y, lc_at 0 (sigma y)) -> lc_at 0 u ->
    forall y, lc_at 0 (extend x u sigma y).
Proof.
  intros sigma x u Hsig Hu y. unfold extend.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma subst_env_extend_open : forall (sigma : atom -> tm) (x : atom) (u : tm) (body : tm),
    (forall y, lc_at 0 (sigma y)) -> lc_at 0 u -> ~ In x (fv body) ->
    subst_env (extend x u sigma) (open body (tm_fvar x)) =
      open (subst_env sigma body) u.
Proof.
  intros sigma x u body Hsig Hu Hfresh. unfold open.
  assert (Hrew : subst_env (extend x u sigma) (open_rec 0 (tm_fvar x) body) =
                 open_rec 0 (extend x u sigma x) (subst_env (extend x u sigma) body)).
  { apply subst_env_open. apply subst_env_extend_lc; auto. }
  rewrite Hrew.
  unfold extend at 1. rewrite Nat.eqb_refl. simpl.
  rewrite subst_env_extend_neq; auto.
Qed.

(* ============================================================ *)
(* Context lookup                                                *)
(* ============================================================ *)

Lemma lookup_context_update_same : forall (Gamma : context) (x : atom) (T : ty),
    lookup_context x (update Gamma x T) = Some T.
Proof.
  intros Gamma x T. unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_context_update_neq : forall (Gamma : context) (x y : atom) (T : ty),
    x <> y -> lookup_context x (update Gamma y T) = lookup_context x Gamma.
Proof.
  intros Gamma x y T Hxy. unfold update. simpl.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst. exfalso. apply Hxy. reflexivity.
  - reflexivity.
Qed.

Lemma lookup_context_empty : forall x : atom, lookup_context x empty = None.
Proof. intros x. reflexivity. Qed.

(* ============================================================ *)
(* Typing lemmas                                                 *)
(* ============================================================ *)

Lemma subtype_wf : forall T U, subtype T U -> wf_ty T /\ wf_ty U.
Proof.
  intros T U Hs. induction Hs; simpl; try (repeat split); tauto.
Qed.

Lemma subtype_security_le : forall T U, subtype T U ->
    security_le (security_of T) (security_of U).
Proof.
  intros T U Hs. induction Hs; simpl; eauto using security_le_trans.
Qed.

Lemma has_type_lc : forall (Gamma : context) (t : tm) (T : ty),
    has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T HT.
  induction HT as
    [ Gamma0 x T0 Hlook Hwf
    | Gamma0 k Hwf
    | L Gamma0 T1 body T2 k Hwf1 Hwf2 Hprem IHprem
    | Gamma0 t1 t2 T1 T2 k r H1 IH1 H2 IH2 Hflows
    | Gamma0 t1 t2 T1 T2 k H1 IH1 H2 IH2 Hwf
    | Gamma0 t T1 T2 k r H1 IH1 Hflows
    | Gamma0 t T1 T2 k r H1 IH1 Hflows
    | Gamma0 t T1 T2 k H1 IH1 Hwf2 Hwfsec
    | Gamma0 t T1 T2 k Hwf1 H1 IH1 Hwfsec
    | L Gamma0 t b1 b2 T1 T2 T0 k r H1 IH1 Hflows Hprem1 IHprem1 Hprem2 IHprem2
    | Gamma0 t T0 l H1 IH1
    | Gamma0 t T0 U H1 IH1 Hsub
    | Gamma0 c yes no k T0 r H1 IH1 H2 IH2 H3 IH3 Hflows ].
  - unfold locally_closed; simpl. exact I.
  - unfold locally_closed; simpl. exact I.
  - unfold locally_closed; simpl.
    destruct (exists_fresh L) as [x Hx].
    apply (open_lc_at 0 (tm_fvar x) body).
    + simpl. exact I.
    + apply (IHprem x). exact Hx.
  - unfold locally_closed; simpl. split; assumption.
  - unfold locally_closed; simpl. split; assumption.
  - unfold locally_closed; simpl. exact IH1.
  - unfold locally_closed; simpl. exact IH1.
  - unfold locally_closed; simpl. exact IH1.
  - unfold locally_closed; simpl. exact IH1.
  - unfold locally_closed; simpl. split; [exact IH1 | split].
    + destruct (exists_fresh L) as [x Hx].
      apply (open_lc_at 0 (tm_fvar x) b1); [simpl; exact I | apply IHprem1; exact Hx].
    + destruct (exists_fresh L) as [x Hx].
      apply (open_lc_at 0 (tm_fvar x) b2); [simpl; exact I | apply IHprem2; exact Hx].
  - unfold locally_closed; simpl. exact IH1.
  - exact IH1.
  - unfold locally_closed; simpl. split; [exact IH1 | split; [exact IH2 | exact IH3]].
Qed.

Lemma has_type_fv : forall (Gamma : context) (t : tm) (T : ty),
    has_type Gamma t T ->
    forall x : atom, In x (fv t) -> exists U : ty, lookup_context x Gamma = Some U.
Proof.
  intros Gamma t T HT.
  induction HT as
    [ Gamma0 x T0 Hlook Hwf
    | Gamma0 k Hwf
    | L Gamma0 T1 body T2 k Hwf1 Hwf2 Hprem IHprem
    | Gamma0 t1 t2 T1 T2 k r H1 IH1 H2 IH2 Hflows
    | Gamma0 t1 t2 T1 T2 k H1 IH1 H2 IH2 Hwf
    | Gamma0 t T1 T2 k r H1 IH1 Hflows
    | Gamma0 t T1 T2 k r H1 IH1 Hflows
    | Gamma0 t T1 T2 k H1 IH1 Hwf2 Hwfsec
    | Gamma0 t T1 T2 k Hwf1 H1 IH1 Hwfsec
    | L Gamma0 t b1 b2 T1 T2 T0 k r H1 IH1 Hflows Hprem1 IHprem1 Hprem2 IHprem2
    | Gamma0 t T0 l H1 IH1
    | Gamma0 t T0 U H1 IH1 Hsub
    | Gamma0 c yes no k T0 r H1 IH1 H2 IH2 H3 IH3 Hflows ].
  - intros y Hy. simpl in Hy. destruct Hy as [-> | []].
    exists T0. exact Hlook.
  - intros y Hy. simpl in Hy. contradiction.
  - intros y Hy. simpl in Hy.
    destruct (exists_fresh_two L [y]) as [x [HL Hxy]].
    pose proof (IHprem x HL y (fv_open_rec_incl 0 (tm_fvar x) body y Hy)) as [U HU].
    exists U. rewrite lookup_context_update_neq in HU.
    + exact HU.
    + intro E; subst x; apply Hxy; simpl; auto.
  - intros y Hy. simpl in Hy. apply in_app_or in Hy as [Hy | Hy].
    + apply IH1; auto.
    + apply IH2; auto.
  - intros y Hy. simpl in Hy. apply in_app_or in Hy as [Hy | Hy].
    + apply IH1; auto.
    + apply IH2; auto.
  - intros y Hy. simpl in Hy. apply IH1; auto.
  - intros y Hy. simpl in Hy. apply IH1; auto.
  - intros y Hy. simpl in Hy. apply IH1; auto.
  - intros y Hy. simpl in Hy. apply IH1; auto.
  - intros y Hy. simpl in Hy.
    apply in_app_or in Hy as [Hy | Hy].
    + apply IH1; auto.
    + apply in_app_or in Hy as [Hy | Hy].
      * destruct (exists_fresh_two L [y]) as [x [HL Hxy]].
        pose proof (IHprem1 x HL y (fv_open_rec_incl 0 (tm_fvar x) b1 y Hy)) as [U HU].
        exists U. rewrite lookup_context_update_neq in HU.
        -- exact HU.
        -- intro E; subst x; apply Hxy; simpl; auto.
      * destruct (exists_fresh_two L [y]) as [x [HL Hxy]].
        pose proof (IHprem2 x HL y (fv_open_rec_incl 0 (tm_fvar x) b2 y Hy)) as [U HU].
        exists U. rewrite lookup_context_update_neq in HU.
        -- exact HU.
        -- intro E; subst x; apply Hxy; simpl; auto.
  - intros y Hy. simpl in Hy. apply IH1; auto.
  - intros y Hy. apply IH1; auto.
  - intros y Hy. simpl in Hy.
    apply in_app_or in Hy as [Hy | Hy].
    + apply IH1; auto.
    + apply in_app_or in Hy as [Hy | Hy].
      * apply IH2; auto.
      * apply IH3; auto.
Qed.

Lemma has_type_wf : forall (Gamma : context) (t : tm) (T : ty),
    has_type Gamma t T -> wf_ty T.
Proof.
  intros Gamma t T HT.
  induction HT as
    [ Gamma0 x T0 Hlook Hwf
    | Gamma0 k Hwf
    | L Gamma0 T1 body T2 k Hwf1 Hwf2 Hprem IHprem
    | Gamma0 t1 t2 T1 T2 k r H1 IH1 H2 IH2 Hflows
    | Gamma0 t1 t2 T1 T2 k H1 IH1 H2 IH2 Hwf
    | Gamma0 t T1 T2 k r H1 IH1 Hflows
    | Gamma0 t T1 T2 k r H1 IH1 Hflows
    | Gamma0 t T1 T2 k H1 IH1 Hwf2 Hwfsec
    | Gamma0 t T1 T2 k Hwf1 H1 IH1 Hwfsec
    | L Gamma0 t b1 b2 T1 T2 T0 k r H1 IH1 Hflows Hprem1 IHprem1 Hprem2 IHprem2
    | Gamma0 t T0 l H1 IH1
    | Gamma0 t T0 U H1 IH1 Hsub
    | Gamma0 c yes no k T0 r H1 IH1 H2 IH2 H3 IH3 Hflows ].
  - exact Hwf.
  - simpl. exact Hwf.
  - simpl. split; [exact Hwf1 | split].
    + destruct (exists_fresh L) as [x Hx]. apply (IHprem x). exact Hx.
    + exact Hwf2.
  - simpl in IH1. apply wf_ty_protect. tauto.
  - simpl. split; [exact IH1 | split; [exact IH2 | exact Hwf]].
  - simpl in IH1. apply wf_ty_protect. tauto.
  - simpl in IH1. apply wf_ty_protect. tauto.
  - simpl. split; [exact IH1 | split; [exact Hwf2 | exact Hwfsec]].
  - simpl. split; [exact Hwf1 | split; [exact IH1 | exact Hwfsec]].
  - simpl. apply wf_ty_protect.
    destruct (exists_fresh L) as [x Hx]. apply (IHprem1 x). exact Hx.
  - apply wf_ty_protect. exact IH1.
  - apply subtype_wf in Hsub. tauto.
  - apply wf_ty_protect. exact IH2.
Qed.

(* ============================================================ *)
(* Logical relation                                              *)
(* ============================================================ *)

Definition top_security (v : tm) : security :=
  match v with
  | tm_unit k => k
  | tm_abs _ _ k => k
  | tm_pair _ _ k => k
  | tm_inl _ k => k
  | tm_inr _ k => k
  | _ => public
  end.

Definition ann (k : security) (v : tm) : Prop :=
  security_le (top_security v) k.

Fixpoint V (T : ty) (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_Unit k =>
      ann k v1 /\ ann k v2 /\
      match k.(indirect_reader) with
      | Low => erase_security v1 = erase_security v2
      | High => True
      end
  | Ty_Sum T1 T2 k =>
      ann k v1 /\ ann k v2 /\
      match k.(indirect_reader) with
      | Low =>
          (exists (w1 w2 : tm) (k1 k2 : security),
              v1 = tm_inl w1 k1 /\ v2 = tm_inl w2 k2 /\ V T1 w1 w2)
          \/ (exists (w1 w2 : tm) (k1 k2 : security),
              v1 = tm_inr w1 k1 /\ v2 = tm_inr w2 k2 /\ V T2 w1 w2)
      | High => True
      end
  | Ty_Prod T1 T2 k =>
      ann k v1 /\ ann k v2 /\
      match k.(indirect_reader) with
      | Low =>
          exists (a1 b1 a2 b2 : tm) (k1 k2 : security),
            v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\ V T1 a1 a2 /\ V T2 b1 b2
      | High => True
      end
  | Ty_Arrow T1 T2 k =>
      ann k v1 /\ ann k v2 /\
      match k.(indirect_reader) with
      | Low => forall (r : label) (u1 u2 : tm),
          locally_closed u1 -> locally_closed u2 ->
          (forall (x1 x2 : tm), eval u1 x1 -> eval u2 x2 -> V T1 x1 x2) ->
          (forall (y1 y2 : tm), eval (tm_app v1 u1 r) y1 ->
             eval (tm_app v2 u2 r) y2 -> V T2 y1 y2)
      | High => True
      end
  end.

Definition E (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, eval t1 v1 -> eval t2 v2 -> V T v1 v2.

Lemma V_unit_iff : forall (k : security) (v1 v2 : tm),
  V (Ty_Unit k) v1 v2 <->
  ann k v1 /\ ann k v2 /\
  match k.(indirect_reader) with
  | Low => erase_security v1 = erase_security v2
  | High => True
  end.
Proof. intros. destruct k as [r i]; destruct i; simpl; tauto. Qed.

Lemma V_sum_iff : forall (T1 T2 : ty) (k : security) (v1 v2 : tm),
  V (Ty_Sum T1 T2 k) v1 v2 <->
  ann k v1 /\ ann k v2 /\
  match k.(indirect_reader) with
  | Low =>
      (exists (w1 w2 : tm) (k1 k2 : security),
          v1 = tm_inl w1 k1 /\ v2 = tm_inl w2 k2 /\ V T1 w1 w2)
      \/ (exists (w1 w2 : tm) (k1 k2 : security),
          v1 = tm_inr w1 k1 /\ v2 = tm_inr w2 k2 /\ V T2 w1 w2)
  | High => True
  end.
Proof. intros. destruct k as [r i]; destruct i; simpl; tauto. Qed.

Lemma V_prod_iff : forall (T1 T2 : ty) (k : security) (v1 v2 : tm),
  V (Ty_Prod T1 T2 k) v1 v2 <->
  ann k v1 /\ ann k v2 /\
  match k.(indirect_reader) with
  | Low =>
      exists (a1 b1 a2 b2 : tm) (k1 k2 : security),
        v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\ V T1 a1 a2 /\ V T2 b1 b2
  | High => True
  end.
Proof. intros. destruct k as [r i]; destruct i; simpl; tauto. Qed.

Lemma V_arrow_iff : forall (T1 T2 : ty) (k : security) (v1 v2 : tm),
  V (Ty_Arrow T1 T2 k) v1 v2 <->
  ann k v1 /\ ann k v2 /\
  match k.(indirect_reader) with
  | Low => forall (r : label) (u1 u2 : tm),
      locally_closed u1 -> locally_closed u2 -> E T1 u1 u2 ->
      E T2 (tm_app v1 u1 r) (tm_app v2 u2 r)
  | High => True
  end.
Proof. intros. destruct k as [r i]; destruct i; simpl; unfold E; tauto. Qed.

Lemma V_unit_erase : forall (k : security) (v1 v2 : tm),
  V (Ty_Unit k) v1 v2 -> k.(indirect_reader) = Low ->
  erase_security v1 = erase_security v2.
Proof.
  intros k v1 v2 H Hi. apply V_unit_iff in H.
  destruct H as [_ [_ H]]. rewrite Hi in H. simpl in H. exact H.
Qed.

Lemma V_sum_structural : forall (T1 T2 : ty) (k : security) (v1 v2 : tm),
  V (Ty_Sum T1 T2 k) v1 v2 -> k.(indirect_reader) = Low ->
  (exists (w1 w2 : tm) (k1 k2 : security),
      v1 = tm_inl w1 k1 /\ v2 = tm_inl w2 k2 /\ V T1 w1 w2)
  \/ (exists (w1 w2 : tm) (k1 k2 : security),
      v1 = tm_inr w1 k1 /\ v2 = tm_inr w2 k2 /\ V T2 w1 w2).
Proof.
  intros T1 T2 k v1 v2 H Hi. apply V_sum_iff in H.
  destruct H as [_ [_ H]]. rewrite Hi in H. simpl in H. exact H.
Qed.

Lemma V_prod_structural : forall (T1 T2 : ty) (k : security) (v1 v2 : tm),
  V (Ty_Prod T1 T2 k) v1 v2 -> k.(indirect_reader) = Low ->
  exists (a1 b1 a2 b2 : tm) (k1 k2 : security),
    v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\ V T1 a1 a2 /\ V T2 b1 b2.
Proof.
  intros T1 T2 k v1 v2 H Hi. apply V_prod_iff in H.
  destruct H as [_ [_ H]]. rewrite Hi in H. simpl in H. exact H.
Qed.

Lemma V_arrow_structural : forall (T1 T2 : ty) (k : security) (v1 v2 : tm),
  V (Ty_Arrow T1 T2 k) v1 v2 -> k.(indirect_reader) = Low ->
  forall (r : label) (u1 u2 : tm),
    locally_closed u1 -> locally_closed u2 -> E T1 u1 u2 ->
    E T2 (tm_app v1 u1 r) (tm_app v2 u2 r).
Proof.
  intros T1 T2 k v1 v2 H Hi. apply V_arrow_iff in H.
  destruct H as [_ [_ H]]. rewrite Hi in H. simpl in H. exact H.
Qed.

Lemma V_ann1 : forall (T : ty) (v1 v2 : tm), V T v1 v2 -> ann (security_of T) v1.
Proof. intros T; destruct T; simpl; intros v1 v2 H; simpl in H; tauto. Qed.

Lemma V_ann2 : forall (T : ty) (v1 v2 : tm), V T v1 v2 -> ann (security_of T) v2.
Proof. intros T; destruct T; simpl; intros v1 v2 H; simpl in H; tauto. Qed.

Lemma security_le_high : forall k : security,
  security_le k {| reader := High; indirect_reader := High |}.
Proof. intros [r i]; destruct r; destruct i; unfold security_le; simpl; auto. Qed.

Lemma ann_high : forall v : tm, ann {| reader := High; indirect_reader := High |} v.
Proof.
  intros v. unfold ann. apply security_le_high.
Qed.

Lemma ann_security_le : forall (k1 k2 : security) (v : tm),
  security_le k1 k2 -> ann k1 v -> ann k2 v.
Proof. intros k1 k2 v Hle Ha. unfold ann in *. eapply security_le_trans; eauto. Qed.

Lemma V_high : forall (T : ty) (v1 v2 : tm),
  security_of T = {| reader := High; indirect_reader := High |} -> V T v1 v2.
Proof.
  intros T. destruct T; intros v1 v2 H; simpl in H; subst; simpl.
  all: split; [apply ann_high | split; [apply ann_high | exact I]].
Qed.

(* ============================================================ *)
(* Monotonicity of the relation under subtyping                  *)
(* ============================================================ *)

Lemma V_sub : forall T U, subtype T U -> forall v1 v2, V T v1 v2 -> V U v1 v2.
Proof.
  intros T U Hs.
  induction Hs as
    [ k1 k2 Hwf1 Hwf2 Hle
    | T1 T2 U1 U2 k1 k2 Hs1 IH1 Hs2 IH2 Hwf1 Hwf2 Hle
    | T1 T2 U1 U2 k1 k2 Hs1 IH1 Hs2 IH2 Hwf1 Hwf2 Hle
    | T1 T2 U1 U2 k1 k2 Hs1 IH1 Hs2 IH2 Hwf1 Hwf2 Hle
    | T U0 V Hs1 IH1 Hs2 IH2 ];
  intros v1 v2 HV.
  - (* S_Unit *) destruct k2 as [r2 i2]; destruct i2.
    + (* Low *)
      assert (Hi1 : k1.(indirect_reader) = Low).
      { apply security_le_ind_low with (k2 := {| reader := r2; indirect_reader := Low |}); auto. }
      pose proof (V_ann1 _ _ _ HV) as Ha1.
      pose proof (V_ann2 _ _ _ HV) as Ha2.
      apply V_unit_iff. split.
      * apply ann_security_le with (k1 := k1); [exact Hle | exact Ha1].
      * split.
        -- apply ann_security_le with (k1 := k1); [exact Hle | exact Ha2].
        -- apply V_unit_erase with (k := k1); auto.
    + (* High *)
      assert (Heq : {| reader := r2; indirect_reader := High |} =
                         {| reader := High; indirect_reader := High |}).
      { apply wf_security_high_eq; [exact Hwf2 | reflexivity]. }
      rewrite Heq. apply V_high. reflexivity.
  - (* S_Sum *) destruct k2 as [r2 i2]; destruct i2.
    + (* Low *)
      assert (Hi1 : k1.(indirect_reader) = Low).
      { apply security_le_ind_low with (k2 := {| reader := r2; indirect_reader := Low |}); auto. }
      pose proof (V_ann1 _ _ _ HV) as Ha1.
      pose proof (V_ann2 _ _ _ HV) as Ha2.
      apply V_sum_iff. split.
      * apply ann_security_le with (k1 := k1); [exact Hle | exact Ha1].
      * split.
        -- apply ann_security_le with (k1 := k1); [exact Hle | exact Ha2].
        -- destruct (V_sum_structural T1 T2 k1 v1 v2 HV Hi1) as
             [[w1 [w2 [ka [kb [E1 [E2 HW]]]]]] | [w1 [w2 [ka [kb [E1 [E2 HW]]]]]]].
           ++ left. exists w1, w2, ka, kb. split; [exact E1 | split; [exact E2 | apply IH1; exact HW]].
           ++ right. exists w1, w2, ka, kb. split; [exact E1 | split; [exact E2 | apply IH2; exact HW]].
    + (* High *)
      assert (Heq : {| reader := r2; indirect_reader := High |} =
                         {| reader := High; indirect_reader := High |}).
      { apply wf_security_high_eq; [exact Hwf2 | reflexivity]. }
      rewrite Heq. apply V_high. reflexivity.
  - (* S_Prod *) destruct k2 as [r2 i2]; destruct i2.
    + (* Low *)
      assert (Hi1 : k1.(indirect_reader) = Low).
      { apply security_le_ind_low with (k2 := {| reader := r2; indirect_reader := Low |}); auto. }
      pose proof (V_ann1 _ _ _ HV) as Ha1.
      pose proof (V_ann2 _ _ _ HV) as Ha2.
      apply V_prod_iff. split.
      * apply ann_security_le with (k1 := k1); [exact Hle | exact Ha1].
      * split.
        -- apply ann_security_le with (k1 := k1); [exact Hle | exact Ha2].
        -- destruct (V_prod_structural T1 T2 k1 v1 v2 HV Hi1) as
             [a1 [b1 [a2 [b2 [ka [kb [E1 [E2 [H1 H2]]]]]]]]].
           exists a1, b1, a2, b2, ka, kb. split; [exact E1 | split; [exact E2 | split]].
           ++ apply IH1; exact H1.
           ++ apply IH2; exact H2.
    + (* High *)
      assert (Heq : {| reader := r2; indirect_reader := High |} =
                         {| reader := High; indirect_reader := High |}).
      { apply wf_security_high_eq; [exact Hwf2 | reflexivity]. }
      rewrite Heq. apply V_high. reflexivity.
  - (* S_Arrow *) destruct k2 as [r2 i2]; destruct i2.
    + (* Low *)
      assert (Hi1 : k1.(indirect_reader) = Low).
      { apply security_le_ind_low with (k2 := {| reader := r2; indirect_reader := Low |}); auto. }
      pose proof (V_ann1 _ _ _ HV) as Ha1.
      pose proof (V_ann2 _ _ _ HV) as Ha2.
      apply V_arrow_iff. split.
      * apply ann_security_le with (k1 := k1); [exact Hle | exact Ha1].
      * split.
        -- apply ann_security_le with (k1 := k1); [exact Hle | exact Ha2].
        -- intros r u1 u2 Hlc1 Hlc2 HEU.
           assert (HE1 : E T1 u1 u2).
           { unfold E in *. intros x1 x2 He1 He2. apply IH1. apply HEU; auto. }
           pose proof (V_arrow_structural T1 T2 k1 v1 v2 HV Hi1 r u1 u2 Hlc1 Hlc2 HE1) as Hres.
           unfold E in *. intros y1 y2 He1 He2. apply IH2. apply Hres; auto.
    + (* High *)
      assert (Heq : {| reader := r2; indirect_reader := High |} =
                         {| reader := High; indirect_reader := High |}).
      { apply wf_security_high_eq; [exact Hwf2 | reflexivity]. }
      rewrite Heq. apply V_high. reflexivity.
  - (* S_Trans *) apply IH2. apply IH1. exact HV.
Qed.

Lemma E_sub : forall T U, subtype T U -> forall t1 t2, E T t1 t2 -> E U t1 t2.
Proof.
  intros T U Hs t1 t2 HE. unfold E in *.
  intros v1 v2 He1 He2. eapply V_sub; [exact Hs | apply HE; auto].
Qed.

(* ============================================================ *)
(* Protection preserves the expression relation                  *)
(* ============================================================ *)

Lemma eval_protect_low_inv : forall (t : tm) (v : tm),
  eval (tm_protect Low t) v -> eval t v.
Proof.
  intros t v He. inversion He; subst.
  rewrite protect_value_low in *. assumption.
Qed.

Lemma E_protect_low : forall (T : ty) (t1 t2 : tm),
  E T t1 t2 -> E T (tm_protect Low t1) (tm_protect Low t2).
Proof.
  intros T t1 t2 HE. unfold E in *.
  intros v1 v2 He1 He2. apply HE.
  - apply eval_protect_low_inv; exact He1.
  - apply eval_protect_low_inv; exact He2.
Qed.

Lemma E_protect : forall (T : ty) (l : label) (t1 t2 : tm),
  E T t1 t2 -> E (ty_protect l T) (tm_protect l t1) (tm_protect l t2).
Proof.
  intros T l t1 t2 HE. destruct l.
  - rewrite ty_protect_low. apply E_protect_low. exact HE.
  - unfold E in *. intros v1 v2 He1 He2. apply V_high. apply ty_protect_high_sec.
Qed.

(* ============================================================ *)
(* Erasing results                                               *)
(* ============================================================ *)

Fixpoint all_ind_low (T : ty) : Prop :=
  (security_of T).(indirect_reader) = Low /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ => all_ind_low T1 /\ all_ind_low T2
  | Ty_Arrow _ _ _ => True
  end.

Lemma transparent_all_ind_low : forall (kappa : security) (T : ty),
  transparent_at kappa T -> kappa.(indirect_reader) = Low -> all_ind_low T.
Proof.
  intros kappa T. revert kappa.
  induction T as [k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k];
  intros kappa Ht Hk; destruct Ht as [Hle Ht]; simpl in *.
  - split; [| exact I]. apply security_le_ind_low with (k2 := kappa); auto.
  - split; [| split].
    + apply security_le_ind_low with (k2 := kappa); auto.
    + apply (IH1 kappa); [exact (proj1 Ht) | exact Hk].
    + apply (IH2 kappa); [exact (proj2 Ht) | exact Hk].
  - split; [| split].
    + apply security_le_ind_low with (k2 := kappa); auto.
    + apply (IH1 kappa); [exact (proj1 Ht) | exact Hk].
    + apply (IH2 kappa); [exact (proj2 Ht) | exact Hk].
  - split; [| exact I]. apply security_le_ind_low with (k2 := kappa); auto.
Qed.

Lemma V_erase : forall (T : ty) (v1 v2 : tm),
  ground T -> all_ind_low T -> V T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  intros T. induction T as [k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k];
  intros v1 v2 Hg Hl HV.
  - (* Unit *) destruct k as [r i]; destruct i; simpl in *.
    + apply V_unit_erase with (k := {| reader := r; indirect_reader := Low |}); auto.
    + destruct Hl as [Hl _]. discriminate.
  - (* Sum *) destruct k as [r i]; destruct i; simpl in *.
    + destruct Hl as [_ [Hl1 Hl2]]. destruct Hg as [Hg1 Hg2].
      destruct (V_sum_structural T1 T2 {| reader := r; indirect_reader := Low |} v1 v2 HV eq_refl)
        as [[w1 [w2 [ka [kb [E1 [E2 HW]]]]]] | [w1 [w2 [ka [kb [E1 [E2 HW]]]]]]].
      * rewrite E1, E2. simpl. f_equal. apply IH1; auto.
      * rewrite E1, E2. simpl. f_equal. apply IH2; auto.
    + destruct Hl as [Hl _]. discriminate.
  - (* Prod *) destruct k as [r i]; destruct i; simpl in *.
    + destruct Hl as [_ [Hl1 Hl2]]. destruct Hg as [Hg1 Hg2].
      destruct (V_prod_structural T1 T2 {| reader := r; indirect_reader := Low |} v1 v2 HV eq_refl)
        as [a1 [b1 [a2 [b2 [ka [kb [E1 [E2 [H1 H2]]]]]]]]].
      rewrite E1, E2. simpl. f_equal.
      * apply IH1; auto.
      * apply IH2; auto.
    + destruct Hl as [Hl _]. discriminate.
  - (* Arrow *) destruct Hg.
Qed.

(* ============================================================ *)
(* Inversion lemmas for big-step evaluation                      *)
(* ============================================================ *)

Lemma eval_abs_inv : forall (T : ty) (body : tm) (k : security) (w : tm),
  eval (tm_abs T body k) w -> w = tm_abs T body k /\ value (tm_abs T body k).
Proof. intros T body k w H. inversion H. auto. Qed.

Lemma eval_pair_inv : forall (t1 t2 : tm) (k : security) (w : tm),
  eval (tm_pair t1 t2 k) w ->
  exists v1 v2, w = tm_pair v1 v2 k /\ eval t1 v1 /\ eval t2 v2.
Proof. intros t1 t2 k w H. inversion H; subst; eauto. Qed.

Lemma eval_inl_inv : forall (t : tm) (k : security) (w : tm),
  eval (tm_inl t k) w -> exists v, w = tm_inl v k /\ eval t v.
Proof. intros t k w H. inversion H; subst; eauto. Qed.

Lemma eval_inr_inv : forall (t : tm) (k : security) (w : tm),
  eval (tm_inr t k) w -> exists v, w = tm_inr v k /\ eval t v.
Proof. intros t k w H. inversion H; subst; eauto. Qed.

Lemma eval_app_inv : forall (t1 t2 : tm) (r : label) (w : tm),
  eval (tm_app t1 t2 r) w ->
  exists (T : ty) (body : tm) (k : security) (arg : tm),
    eval t1 (tm_abs T body k) /\ eval t2 arg /\
    value (tm_abs T body k) /\ value arg /\ flows_to k.(reader) r /\
    eval (tm_protect k.(indirect_reader) (open body arg)) w.
Proof.
  intros t1 t2 r w H. inversion H; subst.
  exists T, body, k, arg. tauto.
Qed.

Lemma eval_fst_inv : forall (t : tm) (r : label) (w : tm),
  eval (tm_fst t r) w ->
  exists v1 v2 k, eval t (tm_pair v1 v2 k) /\ value v1 /\ value v2 /\
    flows_to k.(reader) r /\ eval (tm_protect k.(indirect_reader) v1) w.
Proof.
  intros t r w H. inversion H; subst.
  exists v1, v2, k. tauto.
Qed.

Lemma eval_snd_inv : forall (t : tm) (r : label) (w : tm),
  eval (tm_snd t r) w ->
  exists v1 v2 k, eval t (tm_pair v1 v2 k) /\ value v1 /\ value v2 /\
    flows_to k.(reader) r /\ eval (tm_protect k.(indirect_reader) v2) w.
Proof.
  intros t r w H. inversion H; subst.
  exists v1, v2, k. tauto.
Qed.

Lemma eval_protect_inv : forall (l : label) (t : tm) (w : tm),
  eval (tm_protect l t) w -> exists v, w = protect_value v l /\ eval t v.
Proof. intros l t w H. inversion H; subst. exists v. tauto. Qed.

Lemma eval_case_inv : forall (t b1 b2 : tm) (r : label) (w : tm),
  eval (tm_case t b1 b2 r) w ->
  (exists v k, eval t (tm_inl v k) /\ value v /\ flows_to k.(reader) r /\
     eval (tm_protect k.(indirect_reader) (open b1 v)) w)
  \/ (exists v k, eval t (tm_inr v k) /\ value v /\ flows_to k.(reader) r /\
     eval (tm_protect k.(indirect_reader) (open b2 v)) w).
Proof.
  intros t b1 b2 r w H. inversion H; subst.
  - left. exists v, k. tauto.
  - right. exists v, k. tauto.
Qed.

Lemma eval_if_inv : forall (c yes no : tm) (r : label) (w : tm),
  eval (tm_if c yes no r) w ->
  (exists v k, eval c (tm_inl v k) /\ value v /\ flows_to k.(reader) r /\
     eval (tm_protect k.(indirect_reader) yes) w)
  \/ (exists v k, eval c (tm_inr v k) /\ value v /\ flows_to k.(reader) r /\
     eval (tm_protect k.(indirect_reader) no) w).
Proof.
  intros c yes no r w H. inversion H; subst.
  - left. exists v, k. tauto.
  - right. exists v, k. tauto.
Qed.

(* ============================================================ *)
(* Related environments                                          *)
(* ============================================================ *)

Definition env_rel (Gamma : context) (sigma1 sigma2 : atom -> tm) : Prop :=
  (forall y, lc_at 0 (sigma1 y)) /\
  (forall y, lc_at 0 (sigma2 y)) /\
  (forall x T, lookup_context x Gamma = Some T -> E T (sigma1 x) (sigma2 x)).

Lemma extend_same : forall (x : atom) (u : tm) (sigma : atom -> tm),
  extend x u sigma x = u.
Proof. intros. unfold extend. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_neq : forall (x y : atom) (u : tm) (sigma : atom -> tm),
  y <> x -> extend x u sigma y = sigma y.
Proof.
  intros x y u sigma H. unfold extend.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst. contradiction.
  - reflexivity.
Qed.

Lemma V_E_value : forall (T : ty) (v1 v2 : tm),
  value v1 -> value v2 -> V T v1 v2 -> E T v1 v2.
Proof.
  intros T v1 v2 Hv1 Hv2 HV. unfold E. intros w1 w2 He1 He2.
  assert (H1 : w1 = v1) by (apply eval_value_unique; auto). subst w1.
  assert (H2 : w2 = v2) by (apply eval_value_unique; auto). subst w2.
  exact HV.
Qed.

Lemma env_rel_extend : forall (Gamma : context) (sigma1 sigma2 : atom -> tm)
    (x : atom) (u1 u2 : tm) (T1 : ty),
  env_rel Gamma sigma1 sigma2 -> value u1 -> value u2 -> V T1 u1 u2 ->
  env_rel (update Gamma x T1) (extend x u1 sigma1) (extend x u2 sigma2).
Proof.
  intros Gamma sigma1 sigma2 x u1 u2 T1 [Hlc1 [Hlc2 Hrel]] Hv1 Hv2 HV.
  split; [| split].
  - apply subst_env_extend_lc; [exact Hlc1 | apply value_lc; exact Hv1].
  - apply subst_env_extend_lc; [exact Hlc2 | apply value_lc; exact Hv2].
  - intros y U Hy.
    destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E; subst y.
      assert (HU : U = T1).
      { rewrite lookup_context_update_same in Hy. injection Hy as Hinv. symmetry. exact Hinv. }
      subst U.
      rewrite extend_same, extend_same.
      apply V_E_value; auto.
    + apply Nat.eqb_neq in E.
      rewrite (lookup_context_update_neq Gamma y x T1 E) in Hy.
      rewrite (extend_neq x y u1 sigma1 E), (extend_neq x y u2 sigma2 E).
      apply Hrel; exact Hy.
Qed.

(* ============================================================ *)
(* Relation introduction / inversion lemmas                      *)
(* ============================================================ *)

Lemma exists_fresh_three : forall L1 L2 L3 : list atom,
  exists x : atom, ~ In x L1 /\ ~ In x L2 /\ ~ In x L3.
Proof.
  intros L1 L2 L3. destruct (exists_fresh (L1 ++ L2 ++ L3)) as [x Hx].
  exists x. repeat split; intro H; apply Hx;
    [ apply in_or_app; left; exact H
    | apply in_or_app; right; apply in_or_app; left; exact H
    | apply in_or_app; right; apply in_or_app; right; exact H ].
Qed.

Lemma env_rel_lc1 : forall (Gamma : context) (s1 s2 : atom -> tm),
  env_rel Gamma s1 s2 -> forall y, lc_at 0 (s1 y).
Proof. intros. destruct H as [H1 _]. exact (H1 y). Qed.

Lemma env_rel_lc2 : forall (Gamma : context) (s1 s2 : atom -> tm),
  env_rel Gamma s1 s2 -> forall y, lc_at 0 (s2 y).
Proof. intros. destruct H as [_ [H2 _]]. exact (H2 y). Qed.

Lemma env_rel_E : forall (Gamma : context) (s1 s2 : atom -> tm),
  env_rel Gamma s1 s2 -> forall x T, lookup_context x Gamma = Some T -> E T (s1 x) (s2 x).
Proof. intros. destruct H as [_ [_ H3]]. exact (H3 x T H0). Qed.

Lemma V_unit_self : forall k : security, V (Ty_Unit k) (tm_unit k) (tm_unit k).
Proof.
  intros [r i]; destruct i.
  - apply V_unit_iff. simpl.
    split; [unfold ann; apply security_le_refl | split; [unfold ann; apply security_le_refl | reflexivity]].
  - apply V_unit_iff. simpl.
    split; [unfold ann; apply security_le_refl | split; [unfold ann; apply security_le_refl | exact I]].
Qed.

Lemma V_pair_intro : forall (T1 T2 : ty) (k : security) (a1 b1 a2 b2 : tm),
  V T1 a1 a2 -> V T2 b1 b2 ->
  V (Ty_Prod T1 T2 k) (tm_pair a1 b1 k) (tm_pair a2 b2 k).
Proof.
  intros T1 T2 k a1 b1 a2 b2 H1 H2. destruct k as [r i]; destruct i.
  - apply V_prod_iff. simpl.
    split; [unfold ann; apply security_le_refl | split; [unfold ann; apply security_le_refl | ]].
    exists a1, b1, a2, b2, {| reader := r; indirect_reader := Low |},
           {| reader := r; indirect_reader := Low |}.
    repeat split; auto.
  - apply V_prod_iff. simpl.
    split; [unfold ann; apply security_le_refl | split; [unfold ann; apply security_le_refl | exact I]].
Qed.

Lemma V_inl_intro : forall (T1 T2 : ty) (k : security) (a1 a2 : tm),
  V T1 a1 a2 -> V (Ty_Sum T1 T2 k) (tm_inl a1 k) (tm_inl a2 k).
Proof.
  intros T1 T2 k a1 a2 H1. destruct k as [r i]; destruct i.
  - apply V_sum_iff. simpl.
    split; [unfold ann; apply security_le_refl | split; [unfold ann; apply security_le_refl | ]].
    left. exists a1, a2, {| reader := r; indirect_reader := Low |},
           {| reader := r; indirect_reader := Low |}.
    repeat split; auto.
  - apply V_sum_iff. simpl.
    split; [unfold ann; apply security_le_refl | split; [unfold ann; apply security_le_refl | exact I]].
Qed.

Lemma V_inr_intro : forall (T1 T2 : ty) (k : security) (a1 a2 : tm),
  V T2 a1 a2 -> V (Ty_Sum T1 T2 k) (tm_inr a1 k) (tm_inr a2 k).
Proof.
  intros T1 T2 k a1 a2 H1. destruct k as [r i]; destruct i.
  - apply V_sum_iff. simpl.
    split; [unfold ann; apply security_le_refl | split; [unfold ann; apply security_le_refl | ]].
    right. exists a1, a2, {| reader := r; indirect_reader := Low |},
           {| reader := r; indirect_reader := Low |}.
    repeat split; auto.
  - apply V_sum_iff. simpl.
    split; [unfold ann; apply security_le_refl | split; [unfold ann; apply security_le_refl | exact I]].
Qed.

Lemma V_prod_inv : forall (T1 T2 : ty) (k : security) (a1 b1 : tm) (ka1 : security) (v2 : tm),
  V (Ty_Prod T1 T2 k) (tm_pair a1 b1 ka1) v2 -> k.(indirect_reader) = Low ->
  exists (a2 b2 : tm) (ka2 : security),
    v2 = tm_pair a2 b2 ka2 /\ V T1 a1 a2 /\ V T2 b1 b2.
Proof.
  intros T1 T2 k a1 b1 ka1 v2 HV Hi.
  apply V_prod_structural in HV; [| exact Hi].
  destruct HV as [a1' [b1' [a2' [b2' [k1' [k2' [E1 [E2 [H1 H2]]]]]]]]].
  injection E1 as -> -> ->.
  exists a2', b2', k2'. split; [exact E2 | split; assumption].
Qed.

Lemma V_sum_inv_inl : forall (T1 T2 : ty) (k : security) (a1 : tm) (ka1 : security) (v2 : tm),
  V (Ty_Sum T1 T2 k) (tm_inl a1 ka1) v2 -> k.(indirect_reader) = Low ->
  exists (a2 : tm) (ka2 : security), v2 = tm_inl a2 ka2 /\ V T1 a1 a2.
Proof.
  intros T1 T2 k a1 ka1 v2 HV Hi.
  apply V_sum_structural in HV; [| exact Hi].
  destruct HV as [[w1 [w2 [k1 [k2 [E1 [E2 H1]]]]]] | [w1 [w2 [k1 [k2 [E1 [E2 H1]]]]]]].
  - injection E1 as -> ->. exists w2, k2. split; auto.
  - discriminate E1.
Qed.

Lemma V_sum_inv_inr : forall (T1 T2 : ty) (k : security) (a1 : tm) (ka1 : security) (v2 : tm),
  V (Ty_Sum T1 T2 k) (tm_inr a1 ka1) v2 -> k.(indirect_reader) = Low ->
  exists (a2 : tm) (ka2 : security), v2 = tm_inr a2 ka2 /\ V T2 a1 a2.
Proof.
  intros T1 T2 k a1 ka1 v2 HV Hi.
  apply V_sum_structural in HV; [| exact Hi].
  destruct HV as [[w1 [w2 [k1 [k2 [E1 [E2 H1]]]]]] | [w1 [w2 [k1 [k2 [E1 [E2 H1]]]]]]].
  - discriminate E1.
  - injection E1 as -> ->. exists w2, k2. split; auto.
Qed.

Lemma E_apply : forall (T : ty) (t1 t2 v1 v2 : tm),
  E T t1 t2 -> eval t1 v1 -> eval t2 v2 -> V T v1 v2.
Proof. intros T t1 t2 v1 v2 H HE1 HE2. unfold E in H. exact (H v1 v2 HE1 HE2). Qed.

(* ============================================================ *)
(* Fundamental theorem                                            *)
(* ============================================================ *)

Lemma fundamental : forall (Gamma : context) (t : tm) (T : ty),
    has_type Gamma t T ->
    forall (sigma1 sigma2 : atom -> tm),
      env_rel Gamma sigma1 sigma2 ->
      E T (subst_env sigma1 t) (subst_env sigma2 t).
Proof.
  intros Gamma t T HT.
  induction HT as
    [ Gamma0 x T0 Hlook Hwf
    | Gamma0 k Hwf
    | L Gamma0 T1 body T2 kappa Hwf1 Hwf2 Hprem IHprem
    | Gamma0 t1 t2 T1 T2 kappa r H1 IH1 H2 IH2 Hflows
    | Gamma0 t1 t2 T1 T2 kappa H1 IH1 H2 IH2 Hwf
    | Gamma0 t T1 T2 kappa r H1 IH1 Hflows
    | Gamma0 t T1 T2 kappa r H1 IH1 Hflows
    | Gamma0 t T1 T2 kappa H1 IH1 Hwf2 Hwfsec
    | Gamma0 t T1 T2 kappa Hwf1 H1 IH1 Hwfsec
    | L Gamma0 t b1 b2 T1 T2 T0 kappa r H1 IH1 Hflows Hprem1 IHprem1 Hprem2 IHprem2
    | Gamma0 t T0 l H1 IH1
    | Gamma0 t T0 U H1 IH1 Hsub
    | Gamma0 c yes no kappa T0 r H1 IH1 H2 IH2 H3 IH3 Hflows ];
    intros sigma1 sigma2 Henv.
  - (* Var *) simpl. exact (env_rel_E Gamma0 sigma1 sigma2 Henv x T0 Hlook).
  - (* Unit *) simpl. unfold E. intros v1 v2 He1 He2.
    inversion He1; subst. inversion He2; subst. apply V_unit_self.
  - (* Abs *) simpl. unfold E. intros v1 v2 He1 He2.
    destruct (eval_abs_inv _ _ _ _ He1) as [Ev1 Hval1]. subst v1.
    destruct (eval_abs_inv _ _ _ _ He2) as [Ev2 Hval2]. subst v2.
    destruct kappa as [rk ik]; destruct ik.
    + (* Low *)
      apply V_arrow_iff. split.
      * unfold ann. apply security_le_refl.
      * split.
        -- unfold ann. apply security_le_refl.
        -- intros r u1 u2 Hlc1 Hlc2 HE12. unfold E. intros y1 y2 He1' He2'.
           destruct (eval_app_inv _ _ _ _ He1') as
             [Ta [ba [ka [arg1 [Hf1 [Ha1 [Hva1 [Hvarg1 [Hflow1 Hres1]]]]]]]]].
           destruct (eval_abs_inv _ _ _ _ Hf1) as [Ef1 _].
           injection Ef1 as -> -> ->.
           destruct (eval_app_inv _ _ _ _ He2') as
             [Tb [bb [kb [arg2 [Hf2 [Ha2 [Hvb1 [Hvarg2 [Hflow2 Hres2]]]]]]]]].
           destruct (eval_abs_inv _ _ _ _ Hf2) as [Ef2 _].
           injection Ef2 as -> -> ->.
           assert (HVarg : V T1 arg1 arg2).
           { unfold E in HE12. exact (HE12 arg1 arg2 Ha1 Ha2). }
           destruct (exists_fresh_two L (fv body)) as [x [HL Hfvb]].
           assert (Henv' : env_rel (update Gamma0 x T1) (extend x arg1 sigma1) (extend x arg2 sigma2)).
           { apply env_rel_extend; [exact Henv | exact Hvarg1 | exact Hvarg2 | exact HVarg]. }
           pose proof (IHprem x HL (extend x arg1 sigma1) (extend x arg2 sigma2) Henv') as Hbody.
           assert (Hrw1 : subst_env (extend x arg1 sigma1) (open body (tm_fvar x)) =
                          open (subst_env sigma1 body) arg1).
           { apply subst_env_extend_open;
             [apply (env_rel_lc1 Gamma0 sigma1 sigma2 Henv) | apply value_lc; exact Hvarg1 | exact Hfvb]. }
           assert (Hrw2 : subst_env (extend x arg2 sigma2) (open body (tm_fvar x)) =
                          open (subst_env sigma2 body) arg2).
           { apply subst_env_extend_open;
             [apply (env_rel_lc2 Gamma0 sigma1 sigma2 Henv) | apply value_lc; exact Hvarg2 | exact Hfvb]. }
           rewrite Hrw1 in Hbody. rewrite Hrw2 in Hbody.
           apply E_protect_low in Hbody.
           unfold E in Hbody. exact (Hbody y1 y2 Hres1 Hres2).
    + (* High *)
      assert (Hk : {| reader := rk; indirect_reader := High |} =
                   {| reader := High; indirect_reader := High |}).
      { apply wf_security_high_eq; [exact Hwf2 | reflexivity]. }
      rewrite Hk. apply V_high. reflexivity.
  - (* App *) simpl. destruct kappa as [rk ik]; destruct ik.
    + rewrite ty_protect_low. unfold E. intros w1 w2 He1 He2.
      destruct (eval_app_inv _ _ _ _ He1) as
        [Ta [ba [ka [a1 [Hf1 [Ha1 [Hva1 [Hva1' [Hflow1 Hres1]]]]]]]]].
      destruct (eval_app_inv _ _ _ _ He2) as
        [Tb [bb [kb [a2 [Hf2 [Ha2 [Hvb1 [Hva2 [Hflow2 Hres2]]]]]]]]].
      pose proof (E_apply _ _ _ _ _ (IH1 sigma1 sigma2 Henv) Hf1 Hf2) as HVarrow.
      assert (Hlc1 : locally_closed (subst_env sigma1 t2)).
      { apply subst_env_lc; [apply (env_rel_lc1 Gamma0 sigma1 sigma2 Henv) | apply (has_type_lc Gamma0 t2 T1 H2)]. }
      assert (Hlc2 : locally_closed (subst_env sigma2 t2)).
      { apply subst_env_lc; [apply (env_rel_lc2 Gamma0 sigma1 sigma2 Henv) | apply (has_type_lc Gamma0 t2 T1 H2)]. }
      pose proof (V_arrow_structural T1 T2 {| reader := rk; indirect_reader := Low |}
                    (tm_abs Ta ba ka) (tm_abs Tb bb kb) HVarrow eq_refl
                    r (subst_env sigma1 t2) (subst_env sigma2 t2) Hlc1 Hlc2 (IH2 sigma1 sigma2 Henv)) as Happ.
      assert (Hev1 : eval (tm_app (tm_abs Ta ba ka) (subst_env sigma1 t2) r) w1).
      { eapply E_App with (T := Ta) (body := ba) (k := ka) (arg := a1); eauto using E_Abs. }
      assert (Hev2 : eval (tm_app (tm_abs Tb bb kb) (subst_env sigma2 t2) r) w2).
      { eapply E_App with (T := Tb) (body := bb) (k := kb) (arg := a2); eauto using E_Abs. }
      unfold E in Happ. exact (Happ w1 w2 Hev1 Hev2).
    + unfold E. intros w1 w2 He1 He2. apply V_high. apply ty_protect_high_sec.
  - (* Pair *) simpl. destruct kappa as [rk ik]; destruct ik.
    + unfold E. intros w1 w2 He1 He2.
      destruct (eval_pair_inv _ _ _ _ He1) as [a1 [b1 [E1 [Hp1 Hp2]]]]. subst w1.
      destruct (eval_pair_inv _ _ _ _ He2) as [a2 [b2 [E2 [Hq1 Hq2]]]]. subst w2.
      apply V_pair_intro.
      * exact (E_apply _ _ _ _ _ (IH1 sigma1 sigma2 Henv) Hp1 Hq1).
      * exact (E_apply _ _ _ _ _ (IH2 sigma1 sigma2 Henv) Hp2 Hq2).
    + unfold E. intros w1 w2 He1 He2.
      assert (Hk : {| reader := rk; indirect_reader := High |} =
                   {| reader := High; indirect_reader := High |}).
      { apply wf_security_high_eq; [exact Hwf | reflexivity]. }
      rewrite Hk. apply V_high. reflexivity.
  - (* Fst *) simpl. destruct kappa as [rk ik]; destruct ik.
    + rewrite ty_protect_low. unfold E. intros w1 w2 He1 He2.
      destruct (eval_fst_inv _ _ _ He1) as [a1 [b1 [k1 [Hp1 [Hva1 [Hvb1 [Hflow1 Hres1]]]]]]].
      destruct (eval_fst_inv _ _ _ He2) as [a2 [b2 [k2 [Hp2 [Hva2 [Hvb2 [Hflow2 Hres2]]]]]]].
      pose proof (E_apply _ _ _ _ _ (IH1 sigma1 sigma2 Henv) Hp1 Hp2) as HVprod.
      pose proof (V_ann1 _ _ _ HVprod) as Hann1.
      pose proof (V_ann2 _ _ _ HVprod) as Hann2.
      assert (Hk1 : k1.(indirect_reader) = Low).
      { apply security_le_ind_low with (k2 := {| reader := rk; indirect_reader := Low |});
        [unfold ann in Hann1; exact Hann1 | reflexivity]. }
      assert (Hk2 : k2.(indirect_reader) = Low).
      { apply security_le_ind_low with (k2 := {| reader := rk; indirect_reader := Low |});
        [unfold ann in Hann2; exact Hann2 | reflexivity]. }
      rewrite Hk1 in Hres1. rewrite Hk2 in Hres2.
      apply eval_protect_low_inv in Hres1. apply eval_protect_low_inv in Hres2.
      assert (Hw1 : w1 = a1) by (apply eval_value_unique; auto). subst w1.
      assert (Hw2 : w2 = a2) by (apply eval_value_unique; auto). subst w2.
      destruct (V_prod_inv T1 T2 {| reader := rk; indirect_reader := Low |} a1 b1 k1 (tm_pair a2 b2 k2) HVprod eq_refl)
        as [a2' [b2' [k2' [Eq [HV1 HV2]]]]].
      injection Eq as -> -> ->. exact HV1.
    + unfold E. intros w1 w2 He1 He2. apply V_high. apply ty_protect_high_sec.
  - (* Snd *) simpl. destruct kappa as [rk ik]; destruct ik.
    + rewrite ty_protect_low. unfold E. intros w1 w2 He1 He2.
      destruct (eval_snd_inv _ _ _ He1) as [a1 [b1 [k1 [Hp1 [Hva1 [Hvb1 [Hflow1 Hres1]]]]]]].
      destruct (eval_snd_inv _ _ _ He2) as [a2 [b2 [k2 [Hp2 [Hva2 [Hvb2 [Hflow2 Hres2]]]]]]].
      pose proof (E_apply _ _ _ _ _ (IH1 sigma1 sigma2 Henv) Hp1 Hp2) as HVprod.
      pose proof (V_ann1 _ _ _ HVprod) as Hann1.
      pose proof (V_ann2 _ _ _ HVprod) as Hann2.
      assert (Hk1 : k1.(indirect_reader) = Low).
      { apply security_le_ind_low with (k2 := {| reader := rk; indirect_reader := Low |});
        [unfold ann in Hann1; exact Hann1 | reflexivity]. }
      assert (Hk2 : k2.(indirect_reader) = Low).
      { apply security_le_ind_low with (k2 := {| reader := rk; indirect_reader := Low |});
        [unfold ann in Hann2; exact Hann2 | reflexivity]. }
      rewrite Hk1 in Hres1. rewrite Hk2 in Hres2.
      apply eval_protect_low_inv in Hres1. apply eval_protect_low_inv in Hres2.
      assert (Hw1 : w1 = b1) by (apply eval_value_unique; auto). subst w1.
      assert (Hw2 : w2 = b2) by (apply eval_value_unique; auto). subst w2.
      destruct (V_prod_inv T1 T2 {| reader := rk; indirect_reader := Low |} a1 b1 k1 (tm_pair a2 b2 k2) HVprod eq_refl)
        as [a2' [b2' [k2' [Eq [HV1 HV2]]]]].
      injection Eq as -> -> ->. exact HV2.
    + unfold E. intros w1 w2 He1 He2. apply V_high. apply ty_protect_high_sec.
  - (* Inl *) simpl. destruct kappa as [rk ik]; destruct ik.
    + unfold E. intros w1 w2 He1 He2.
      destruct (eval_inl_inv _ _ _ He1) as [v1 [E1 H1']]. subst w1.
      destruct (eval_inl_inv _ _ _ He2) as [v2 [E2 H2']]. subst w2.
      apply V_inl_intro. exact (E_apply _ _ _ _ _ (IH1 sigma1 sigma2 Henv) H1' H2').
    + unfold E. intros w1 w2 He1 He2.
      destruct (eval_inl_inv _ _ _ He1) as [v1 [E1 H1']]. subst w1.
      destruct (eval_inl_inv _ _ _ He2) as [v2 [E2 H2']]. subst w2.
      assert (Hk : {| reader := rk; indirect_reader := High |} =
                   {| reader := High; indirect_reader := High |}).
      { apply wf_security_high_eq; [exact Hwfsec | reflexivity]. }
      rewrite Hk. apply V_high. reflexivity.
  - (* Inr *) simpl. destruct kappa as [rk ik]; destruct ik.
    + unfold E. intros w1 w2 He1 He2.
      destruct (eval_inr_inv _ _ _ He1) as [v1 [E1 H1']]. subst w1.
      destruct (eval_inr_inv _ _ _ He2) as [v2 [E2 H2']]. subst w2.
      apply V_inr_intro. exact (E_apply _ _ _ _ _ (IH1 sigma1 sigma2 Henv) H1' H2').
    + unfold E. intros w1 w2 He1 He2.
      destruct (eval_inr_inv _ _ _ He1) as [v1 [E1 H1']]. subst w1.
      destruct (eval_inr_inv _ _ _ He2) as [v2 [E2 H2']]. subst w2.
      assert (Hk : {| reader := rk; indirect_reader := High |} =
                   {| reader := High; indirect_reader := High |}).
      { apply wf_security_high_eq; [exact Hwfsec | reflexivity]. }
      rewrite Hk. apply V_high. reflexivity.
  - (* Case *) simpl. destruct kappa as [rk ik]; destruct ik.
    + rewrite ty_protect_low. unfold E. intros w1 w2 He1 He2.
      destruct (eval_case_inv _ _ _ _ _ He1) as
        [[va1 [ka1 [Hc1 [Hval1 [Hflow1 Hres1]]]]] |
         [va1 [ka1 [Hc1 [Hval1 [Hflow1 Hres1]]]]]].
      all: destruct (eval_case_inv _ _ _ _ _ He2) as
        [[va2 [ka2 [Hc2 [Hval2 [Hflow2 Hres2]]]]] |
         [va2 [ka2 [Hc2 [Hval2 [Hflow2 Hres2]]]]]].
      all: pose proof (E_apply _ _ _ _ _ (IH1 sigma1 sigma2 Henv) Hc1 Hc2) as HVsum.
      * (* inl / inl *)
        pose proof (V_ann1 _ _ _ HVsum) as Hann1.
        pose proof (V_ann2 _ _ _ HVsum) as Hann2.
        assert (Hk1 : ka1.(indirect_reader) = Low).
        { apply security_le_ind_low with (k2 := {| reader := rk; indirect_reader := Low |});
          [unfold ann in Hann1; exact Hann1 | reflexivity]. }
        assert (Hk2 : ka2.(indirect_reader) = Low).
        { apply security_le_ind_low with (k2 := {| reader := rk; indirect_reader := Low |});
          [unfold ann in Hann2; exact Hann2 | reflexivity]. }
        rewrite Hk1 in Hres1. rewrite Hk2 in Hres2.
        apply eval_protect_low_inv in Hres1. apply eval_protect_low_inv in Hres2.
        destruct (V_sum_inv_inl T1 T2 {| reader := rk; indirect_reader := Low |} va1 ka1 (tm_inl va2 ka2) HVsum eq_refl)
          as [va2' [ka2' [Eq HVp]]].
        injection Eq as <- <-.
        destruct (exists_fresh_three L (fv b1) (fv b2)) as [x [HL [Hb1 Hb2]]].
        assert (Henv' : env_rel (update Gamma0 x T1) (extend x va1 sigma1) (extend x va2 sigma2)).
        { apply env_rel_extend; [exact Henv | exact Hval1 | exact Hval2 | exact HVp]. }
        pose proof (IHprem1 x HL (extend x va1 sigma1) (extend x va2 sigma2) Henv') as Hbody.
        assert (Hrw1 : subst_env (extend x va1 sigma1) (open b1 (tm_fvar x)) =
                       open (subst_env sigma1 b1) va1).
        { apply subst_env_extend_open;
          [apply (env_rel_lc1 Gamma0 sigma1 sigma2 Henv) | apply value_lc; exact Hval1 | exact Hb1]. }
        assert (Hrw2 : subst_env (extend x va2 sigma2) (open b1 (tm_fvar x)) =
                       open (subst_env sigma2 b1) va2).
        { apply subst_env_extend_open;
          [apply (env_rel_lc2 Gamma0 sigma1 sigma2 Henv) | apply value_lc; exact Hval2 | exact Hb1]. }
        rewrite Hrw1 in Hbody. rewrite Hrw2 in Hbody.
        unfold E in Hbody. exact (Hbody w1 w2 Hres1 Hres2).
      * (* inl / inr *) exfalso.
        destruct (V_sum_inv_inl T1 T2 {| reader := rk; indirect_reader := Low |} va1 ka1 (tm_inr va2 ka2) HVsum eq_refl)
          as [va2' [ka2' [Eq _]]].
        discriminate Eq.
      * (* inr / inl *) exfalso.
        destruct (V_sum_inv_inr T1 T2 {| reader := rk; indirect_reader := Low |} va1 ka1 (tm_inl va2 ka2) HVsum eq_refl)
          as [va2' [ka2' [Eq _]]].
        discriminate Eq.
      * (* inr / inr *)
        pose proof (V_ann1 _ _ _ HVsum) as Hann1.
        pose proof (V_ann2 _ _ _ HVsum) as Hann2.
        assert (Hk1 : ka1.(indirect_reader) = Low).
        { apply security_le_ind_low with (k2 := {| reader := rk; indirect_reader := Low |});
          [unfold ann in Hann1; exact Hann1 | reflexivity]. }
        assert (Hk2 : ka2.(indirect_reader) = Low).
        { apply security_le_ind_low with (k2 := {| reader := rk; indirect_reader := Low |});
          [unfold ann in Hann2; exact Hann2 | reflexivity]. }
        rewrite Hk1 in Hres1. rewrite Hk2 in Hres2.
        apply eval_protect_low_inv in Hres1. apply eval_protect_low_inv in Hres2.
        destruct (V_sum_inv_inr T1 T2 {| reader := rk; indirect_reader := Low |} va1 ka1 (tm_inr va2 ka2) HVsum eq_refl)
          as [va2' [ka2' [Eq HVp]]].
        injection Eq as <- <-.
        destruct (exists_fresh_three L (fv b1) (fv b2)) as [x [HL [Hb1 Hb2]]].
        assert (Henv' : env_rel (update Gamma0 x T2) (extend x va1 sigma1) (extend x va2 sigma2)).
        { apply env_rel_extend; [exact Henv | exact Hval1 | exact Hval2 | exact HVp]. }
        pose proof (IHprem2 x HL (extend x va1 sigma1) (extend x va2 sigma2) Henv') as Hbody.
        assert (Hrw1 : subst_env (extend x va1 sigma1) (open b2 (tm_fvar x)) =
                       open (subst_env sigma1 b2) va1).
        { apply subst_env_extend_open;
          [apply (env_rel_lc1 Gamma0 sigma1 sigma2 Henv) | apply value_lc; exact Hval1 | exact Hb2]. }
        assert (Hrw2 : subst_env (extend x va2 sigma2) (open b2 (tm_fvar x)) =
                       open (subst_env sigma2 b2) va2).
        { apply subst_env_extend_open;
          [apply (env_rel_lc2 Gamma0 sigma1 sigma2 Henv) | apply value_lc; exact Hval2 | exact Hb2]. }
        rewrite Hrw1 in Hbody. rewrite Hrw2 in Hbody.
        unfold E in Hbody. exact (Hbody w1 w2 Hres1 Hres2).
    + unfold E. intros w1 w2 He1 He2. apply V_high. apply ty_protect_high_sec.
  - (* Protect *) simpl. apply E_protect with (T := T0) (l := l). exact (IH1 sigma1 sigma2 Henv).
  - (* Sub *) simpl. apply E_sub with (T := T0). exact Hsub. exact (IH1 sigma1 sigma2 Henv).
  - (* If *) simpl. destruct kappa as [rk ik]; destruct ik.
    + rewrite ty_protect_low. unfold E. intros w1 w2 He1 He2.
      destruct (eval_if_inv _ _ _ _ _ He1) as
        [[va1 [ka1 [Hc1 [Hval1 [Hflow1 Hres1]]]]] |
         [va1 [ka1 [Hc1 [Hval1 [Hflow1 Hres1]]]]]].
      all: destruct (eval_if_inv _ _ _ _ _ He2) as
        [[va2 [ka2 [Hc2 [Hval2 [Hflow2 Hres2]]]]] |
         [va2 [ka2 [Hc2 [Hval2 [Hflow2 Hres2]]]]]].
      all: pose proof (E_apply _ _ _ _ _ (IH1 sigma1 sigma2 Henv) Hc1 Hc2) as HVsum.
      * (* inl / inl *)
        pose proof (V_ann1 _ _ _ HVsum) as Hann1.
        pose proof (V_ann2 _ _ _ HVsum) as Hann2.
        assert (Hk1 : ka1.(indirect_reader) = Low).
        { apply security_le_ind_low with (k2 := {| reader := rk; indirect_reader := Low |});
          [unfold ann in Hann1; exact Hann1 | reflexivity]. }
        assert (Hk2 : ka2.(indirect_reader) = Low).
        { apply security_le_ind_low with (k2 := {| reader := rk; indirect_reader := Low |});
          [unfold ann in Hann2; exact Hann2 | reflexivity]. }
        rewrite Hk1 in Hres1. rewrite Hk2 in Hres2.
        apply eval_protect_low_inv in Hres1. apply eval_protect_low_inv in Hres2.
        destruct (V_sum_inv_inl (Ty_Unit public) (Ty_Unit public)
                    {| reader := rk; indirect_reader := Low |} va1 ka1 (tm_inl va2 ka2) HVsum eq_refl)
          as [va2' [ka2' [Eq _]]].
        injection Eq as <- <-.
        exact (E_apply _ _ _ _ _ (IH2 sigma1 sigma2 Henv) Hres1 Hres2).
      * (* inl / inr *) exfalso.
        destruct (V_sum_inv_inl (Ty_Unit public) (Ty_Unit public)
                    {| reader := rk; indirect_reader := Low |} va1 ka1 (tm_inr va2 ka2) HVsum eq_refl)
          as [va2' [ka2' [Eq _]]].
        discriminate Eq.
      * (* inr / inl *) exfalso.
        destruct (V_sum_inv_inr (Ty_Unit public) (Ty_Unit public)
                    {| reader := rk; indirect_reader := Low |} va1 ka1 (tm_inl va2 ka2) HVsum eq_refl)
          as [va2' [ka2' [Eq _]]].
        discriminate Eq.
      * (* inr / inr *)
        pose proof (V_ann1 _ _ _ HVsum) as Hann1.
        pose proof (V_ann2 _ _ _ HVsum) as Hann2.
        assert (Hk1 : ka1.(indirect_reader) = Low).
        { apply security_le_ind_low with (k2 := {| reader := rk; indirect_reader := Low |});
          [unfold ann in Hann1; exact Hann1 | reflexivity]. }
        assert (Hk2 : ka2.(indirect_reader) = Low).
        { apply security_le_ind_low with (k2 := {| reader := rk; indirect_reader := Low |});
          [unfold ann in Hann2; exact Hann2 | reflexivity]. }
        rewrite Hk1 in Hres1. rewrite Hk2 in Hres2.
        apply eval_protect_low_inv in Hres1. apply eval_protect_low_inv in Hres2.
        destruct (V_sum_inv_inr (Ty_Unit public) (Ty_Unit public)
                    {| reader := rk; indirect_reader := Low |} va1 ka1 (tm_inr va2 ka2) HVsum eq_refl)
          as [va2' [ka2' [Eq _]]].
        injection Eq as <- <-.
        exact (E_apply _ _ _ _ _ (IH3 sigma1 sigma2 Henv) Hres1 Hres2).
    + unfold E. intros w1 w2 He1 He2. apply V_high. apply ty_protect_high_sec.
Qed.

(* ============================================================ *)
(* Small-step evaluations are big-step evaluations               *)
(* ============================================================ *)

Lemma step_eval : forall (t t' : tm), step t t' ->
    forall v : tm, eval t' v -> eval t v.
Proof.
  intros t t' Hstep.
  induction Hstep as
    [ T body kappa v r Hvabs Hv Hflow
    | t1 t1' t2 r Hs IHs
    | v1 t2 t2' r Hv1 Hs IHs
    | t1 t1' t2 kappa Hs IHs
    | v1 t2 t2' kappa Hv1 Hs IHs
    | v1 v2 kappa r Hv1 Hv2 Hflow
    | t t' r Hs IHs
    | v1 v2 kappa r Hv1 Hv2 Hflow
    | t t' r Hs IHs
    | t t' kappa Hs IHs
    | t t' kappa Hs IHs
    | v kappa body1 body2 r Hv Hflow
    | v kappa body1 body2 r Hv Hflow
    | t t' body1 body2 r Hs IHs
    | l v Hv
    | l t t' Hs IHs
    | c c' yes no r Hs IHs
    | v k yes no r Hv Hflow
    | v k yes no r Hv Hflow ];
    intros w Hev.
  - (* AppAbs *) eapply E_App with (T := T) (body := body) (k := kappa) (arg := v).
    + apply E_Abs; exact Hvabs.
    + apply value_eval; exact Hv.
    + exact Hvabs.
    + exact Hv.
    + exact Hflow.
    + exact Hev.
  - (* App1 *) destruct (eval_app_inv _ _ _ _ Hev) as
      [T [body [k [a [Hf [Ha [Hva [Hva' [Hfl Hres]]]]]]]]].
    eapply E_App with (T := T) (body := body) (k := k) (arg := a).
    + apply IHs. exact Hf.
    + exact Ha.
    + exact Hva.
    + exact Hva'.
    + exact Hfl.
    + exact Hres.
  - (* App2 *) destruct (eval_app_inv _ _ _ _ Hev) as
      [T [body [k [a [Hf [Ha [Hva [Hva' [Hfl Hres]]]]]]]]].
    eapply E_App with (T := T) (body := body) (k := k) (arg := a).
    + exact Hf.
    + apply IHs. exact Ha.
    + exact Hva.
    + exact Hva'.
    + exact Hfl.
    + exact Hres.
  - (* Pair1 *) destruct (eval_pair_inv _ _ _ _ Hev) as [a [b [E [H1 H2]]]]. subst w.
    apply E_Pair; [apply IHs; exact H1 | exact H2].
  - (* Pair2 *) destruct (eval_pair_inv _ _ _ _ Hev) as [a [b [E [H1 H2]]]]. subst w.
    apply E_Pair; [exact H1 | apply IHs; exact H2].
  - (* FstPair *) eapply E_Fst with (v1 := v1) (v2 := v2) (k := kappa).
    + apply E_Pair; [apply value_eval; exact Hv1 | apply value_eval; exact Hv2].
    + exact Hv1.
    + exact Hv2.
    + exact Hflow.
    + exact Hev.
  - (* Fst *) destruct (eval_fst_inv _ _ _ Hev) as [a [b [k [Hp [Hva [Hvb [Hfl Hres]]]]]]].
    eapply E_Fst with (v1 := a) (v2 := b) (k := k).
    + apply IHs. exact Hp.
    + exact Hva.
    + exact Hvb.
    + exact Hfl.
    + exact Hres.
  - (* SndPair *) eapply E_Snd with (v1 := v1) (v2 := v2) (k := kappa).
    + apply E_Pair; [apply value_eval; exact Hv1 | apply value_eval; exact Hv2].
    + exact Hv1.
    + exact Hv2.
    + exact Hflow.
    + exact Hev.
  - (* Snd *) destruct (eval_snd_inv _ _ _ Hev) as [a [b [k [Hp [Hva [Hvb [Hfl Hres]]]]]]].
    eapply E_Snd with (v1 := a) (v2 := b) (k := k).
    + apply IHs. exact Hp.
    + exact Hva.
    + exact Hvb.
    + exact Hfl.
    + exact Hres.
  - (* Inl *) destruct (eval_inl_inv _ _ _ Hev) as [a [E Ha]]. subst w.
    apply E_Inl. apply IHs. exact Ha.
  - (* Inr *) destruct (eval_inr_inv _ _ _ Hev) as [a [E Ha]]. subst w.
    apply E_Inr. apply IHs. exact Ha.
  - (* CaseLeft *) eapply E_CaseL with (v := v) (k := kappa).
    + apply E_Inl. apply value_eval. exact Hv.
    + exact Hv.
    + exact Hflow.
    + exact Hev.
  - (* CaseRight *) eapply E_CaseR with (v := v) (k := kappa).
    + apply E_Inr. apply value_eval. exact Hv.
    + exact Hv.
    + exact Hflow.
    + exact Hev.
  - (* Case *) destruct (eval_case_inv _ _ _ _ _ Hev) as
      [[a [k [Hc [Hv [Hfl Hres]]]]] | [a [k [Hc [Hv [Hfl Hres]]]]]].
    + eapply E_CaseL with (v := a) (k := k).
      * apply IHs. exact Hc.
      * exact Hv.
      * exact Hfl.
      * exact Hres.
    + eapply E_CaseR with (v := a) (k := k).
      * apply IHs. exact Hc.
      * exact Hv.
      * exact Hfl.
      * exact Hres.
  - (* ProtectValue *)
    assert (Hw : w = protect_value v l).
    { apply eval_value_unique; [exact Hev | apply protect_value_value; exact Hv]. }
    rewrite Hw. apply E_Protect. apply value_eval. exact Hv.
  - (* Protect *) destruct (eval_protect_inv _ _ _ Hev) as [a [E Ha]]. subst w.
    apply E_Protect. apply IHs. exact Ha.
  - (* If *) destruct (eval_if_inv _ _ _ _ _ Hev) as
      [[a [k [Hc [Hv [Hfl Hres]]]]] | [a [k [Hc [Hv [Hfl Hres]]]]]].
    + eapply E_IfL with (v := a) (k := k).
      * apply IHs. exact Hc.
      * exact Hv.
      * exact Hfl.
      * exact Hres.
    + eapply E_IfR with (v := a) (k := k).
      * apply IHs. exact Hc.
      * exact Hv.
      * exact Hfl.
      * exact Hres.
  - (* IfTrue *) eapply E_IfL with (v := v) (k := k).
    + apply E_Inl. apply value_eval. exact Hv.
    + exact Hv.
    + exact Hflow.
    + exact Hev.
  - (* IfFalse *) eapply E_IfR with (v := v) (k := k).
    + apply E_Inr. apply value_eval. exact Hv.
    + exact Hv.
    + exact Hflow.
    + exact Hev.
Qed.

Lemma multi_eval : forall (t v : tm), multi t v -> value v -> eval t v.
Proof.
  intros t v Hm. induction Hm; intros Hv.
  - apply value_eval. exact Hv.
  - eapply step_eval; [exact H | apply IHHm; exact Hv].
Qed.

(* ============================================================ *)
(* Atoms occurring in a program context                          *)
(* ============================================================ *)

Fixpoint ctx_atoms (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs T C' k => ctx_atoms C'
  | C_AppLeft C' t2 r => ctx_atoms C' ++ fv t2
  | C_AppRight t1 C' r => fv t1 ++ ctx_atoms C'
  | C_PairLeft C' t2 k => ctx_atoms C' ++ fv t2
  | C_PairRight t1 C' k => fv t1 ++ ctx_atoms C'
  | C_Fst C' r => ctx_atoms C'
  | C_Snd C' r => ctx_atoms C'
  | C_Inl C' k => ctx_atoms C'
  | C_Inr C' k => ctx_atoms C'
  | C_CaseScrutinee C' b1 b2 r => ctx_atoms C' ++ fv b1 ++ fv b2
  | C_CaseLeft t0 C' b2 r => fv t0 ++ ctx_atoms C' ++ fv b2
  | C_CaseRight t0 b1 C' r => fv t0 ++ fv b1 ++ ctx_atoms C'
  | C_Protect l C' => ctx_atoms C'
  | C_IfCondition C' y n r => ctx_atoms C' ++ fv y ++ fv n
  | C_IfThen c C' n r => fv c ++ ctx_atoms C' ++ fv n
  | C_IfElse c y C' r => fv c ++ fv y ++ ctx_atoms C'
  end.

Lemma subst_plug : forall (C : program_context) (x : atom) (u : tm),
  ~ In x (ctx_atoms C) -> subst x u (plug C (tm_fvar x)) = plug C u.
Proof.
  induction C as
    [ | T C' IH k | C' IH t2 r | t1 C' IH r | C' IH t2 k | t1 C' IH k
    | C' IH r | C' IH r | C' IH k | C' IH k | C' IH b1 b2 r | t0 C' IH b2 r
    | t0 b1 C' IH r | l C' IH | C' IH y n r | c C' IH n r | c y C' IH r ];
    simpl in *; intros x u Hx.
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - rewrite (IH x u Hx). reflexivity.
  - destruct (not_in_app x (ctx_atoms C') (fv t2) Hx) as [H1 H2].
    rewrite (IH x u H1), (subst_fresh x u t2 H2). reflexivity.
  - destruct (not_in_app x (fv t1) (ctx_atoms C') Hx) as [H1 H2].
    rewrite (subst_fresh x u t1 H1), (IH x u H2). reflexivity.
  - destruct (not_in_app x (ctx_atoms C') (fv t2) Hx) as [H1 H2].
    rewrite (IH x u H1), (subst_fresh x u t2 H2). reflexivity.
  - destruct (not_in_app x (fv t1) (ctx_atoms C') Hx) as [H1 H2].
    rewrite (subst_fresh x u t1 H1), (IH x u H2). reflexivity.
  - rewrite (IH x u Hx). reflexivity.
  - rewrite (IH x u Hx). reflexivity.
  - rewrite (IH x u Hx). reflexivity.
  - rewrite (IH x u Hx). reflexivity.
  - destruct (not_in_app x (ctx_atoms C') (fv b1 ++ fv b2) Hx) as [H1 H2].
    destruct (not_in_app x (fv b1) (fv b2) H2) as [Hb1 Hb2].
    rewrite (IH x u H1), (subst_fresh x u b1 Hb1), (subst_fresh x u b2 Hb2). reflexivity.
  - destruct (not_in_app x (fv t0) (ctx_atoms C' ++ fv b2) Hx) as [H0 H2].
    destruct (not_in_app x (ctx_atoms C') (fv b2) H2) as [H1 Hb2].
    rewrite (subst_fresh x u t0 H0), (IH x u H1), (subst_fresh x u b2 Hb2). reflexivity.
  - destruct (not_in_app x (fv t0) (fv b1 ++ ctx_atoms C') Hx) as [H0 H2].
    destruct (not_in_app x (fv b1) (ctx_atoms C') H2) as [Hb1 H1].
    rewrite (subst_fresh x u t0 H0), (subst_fresh x u b1 Hb1), (IH x u H1). reflexivity.
  - rewrite (IH x u Hx). reflexivity.
  - destruct (not_in_app x (ctx_atoms C') (fv y ++ fv n) Hx) as [H1 H2].
    destruct (not_in_app x (fv y) (fv n) H2) as [Hy Hn].
    rewrite (IH x u H1), (subst_fresh x u y Hy), (subst_fresh x u n Hn). reflexivity.
  - destruct (not_in_app x (fv c) (ctx_atoms C' ++ fv n) Hx) as [Hc H2].
    destruct (not_in_app x (ctx_atoms C') (fv n) H2) as [H1 Hn].
    rewrite (subst_fresh x u c Hc), (IH x u H1), (subst_fresh x u n Hn). reflexivity.
  - destruct (not_in_app x (fv c) (fv y ++ ctx_atoms C') Hx) as [Hc H2].
    destruct (not_in_app x (fv y) (ctx_atoms C') H2) as [Hy H1].
    rewrite (subst_fresh x u c Hc), (subst_fresh x u y Hy), (IH x u H1). reflexivity.
Qed.

(* ============================================================ *)
(* The singleton related environment                             *)
(* ============================================================ *)

Lemma env_rel_single : forall (x : atom) (T_hole : ty) (t1 t2 : tm),
  locally_closed t1 -> locally_closed t2 -> E T_hole t1 t2 ->
  env_rel (update empty x T_hole) (extend x t1 id_env) (extend x t2 id_env).
Proof.
  intros x T_hole t1 t2 Hlc1 Hlc2 HE. split.
  - intros y. unfold extend, id_env. destruct (Nat.eqb x y).
    + exact Hlc1.
    + exact I.
  - split.
    + intros y. unfold extend, id_env. destruct (Nat.eqb x y).
      * exact Hlc2.
      * exact I.
    + intros y U Hy. destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E; subst y.
        assert (HU : U = T_hole).
        { rewrite lookup_context_update_same in Hy. injection Hy as Hinv. symmetry. exact Hinv. }
        subst U. rewrite extend_same, extend_same. exact HE.
      * apply Nat.eqb_neq in E.
        rewrite (lookup_context_update_neq empty y x T_hole E) in Hy.
        simpl in Hy. discriminate Hy.
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 Hctx Hg Htr Hflow.
  destruct Hctx as [L Hctx].
  destruct (flows_to_inv _ _ Hflow) as [Hsec_ind Hres_ind].
  assert (Hsec : security_of T_secret =
                 {| reader := High; indirect_reader := High |}).
  { apply wf_security_high_eq.
    - exact (wf_ty_security T_secret (has_type_wf empty t1 T_secret Ht1)).
    - exact Hsec_ind. }
  destruct (exists_fresh_two L (ctx_atoms C)) as [x [HL Hxc]].
  assert (Henv : env_rel (update empty x T_secret)
                   (extend x t1 id_env) (extend x t2 id_env)).
  { apply env_rel_single.
    - exact (has_type_lc empty t1 T_secret Ht1).
    - exact (has_type_lc empty t2 T_secret Ht2).
    - unfold E. intros v1 v2 He1 He2. apply V_high. exact Hsec. }
  pose proof (fundamental (update empty x T_secret) (plug C (tm_fvar x)) T_result
                (Hctx x HL) (extend x t1 id_env) (extend x t2 id_env) Henv) as HE.
  assert (Hsub1 : subst_env (extend x t1 id_env) (plug C (tm_fvar x)) = plug C t1).
  { rewrite subst_env_extend_id. apply subst_plug. exact Hxc. }
  assert (Hsub2 : subst_env (extend x t2 id_env) (plug C (tm_fvar x)) = plug C t2).
  { rewrite subst_env_extend_id. apply subst_plug. exact Hxc. }
  rewrite Hsub1, Hsub2 in HE.
  intros v1 v2 Hev1 Hev2.
  destruct Hev1 as [Hm1 Hval1]. destruct Hev2 as [Hm2 Hval2].
  apply multi_eval in Hm1; [| exact Hval1].
  apply multi_eval in Hm2; [| exact Hval2].
  unfold E in HE.
  pose proof (HE v1 v2 Hm1 Hm2) as HV.
  apply (V_erase T_result v1 v2 Hg).
  - apply (transparent_all_ind_low (security_of T_result) T_result Htr Hres_ind).
  - exact HV.
Qed.
