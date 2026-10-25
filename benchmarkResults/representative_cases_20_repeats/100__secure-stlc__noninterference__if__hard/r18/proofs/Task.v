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

(* ================================================================== *)
(* Basic label and security lemmas                                     *)
(* ================================================================== *)

Lemma flows_to_refl : forall l : label, flows_to l l.
Proof. destruct l; simpl; exact I. Qed.

Lemma flows_to_trans : forall l1 l2 l3 : label,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof. destruct l1, l2, l3; simpl; auto. Qed.

Lemma flows_to_low_iff : forall l, flows_to l Low <-> l = Low.
Proof.
  intro l; destruct l; simpl.
  - split; intro H; [reflexivity | exact I].
  - split; intro H; [destruct H | discriminate H].
Qed.

Lemma flows_to_any_high : forall l, flows_to l High.
Proof. destruct l; reflexivity. Qed.

Lemma flows_to_any_low : forall l, flows_to Low l.
Proof. destruct l; reflexivity. Qed.

Lemma flows_to_high_low_false : ~ flows_to High Low.
Proof. simpl. intro H. exact H. Qed.

Lemma join_low : forall l, join l Low = l.
Proof. destruct l; reflexivity. Qed.

Lemma join_high : forall l, join l High = High.
Proof. destruct l; reflexivity. Qed.

Lemma protect_security_low : forall κ, protect_security κ Low = κ.
Proof.
  intros [r i]; unfold protect_security; simpl.
  rewrite join_low, join_low. reflexivity.
Qed.

Lemma protect_security_high : forall κ,
  protect_security κ High = {| reader := High; indirect_reader := High |}.
Proof.
  intros [r i]; unfold protect_security; simpl.
  rewrite join_high, join_high. reflexivity.
Qed.

Lemma protect_security_ind : forall κ l,
  (protect_security κ l).(indirect_reader) = join κ.(indirect_reader) l.
Proof. intros [r i] l; reflexivity. Qed.

Lemma protect_security_reader : forall κ l,
  (protect_security κ l).(reader) = join κ.(reader) l.
Proof. intros [r i] l; reflexivity. Qed.

Lemma security_le_refl : forall κ, security_le κ κ.
Proof.
  intros [r i]; unfold security_le; simpl.
  split; apply flows_to_refl.
Qed.

Lemma security_le_trans : forall κ1 κ2 κ3,
  security_le κ1 κ2 -> security_le κ2 κ3 -> security_le κ1 κ3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3]; unfold security_le; simpl.
  intros [H1 H2] [H3 H4]; split; eapply flows_to_trans; eauto.
Qed.

Lemma security_le_protect : forall κ1 κ2 l,
  security_le κ1 κ2 -> security_le (protect_security κ1 l) (protect_security κ2 l).
Proof.
  intros [r1 i1] [r2 i2] l [H1 H2]; unfold security_le; simpl in *.
  destruct r1, r2, i1, i2, l; simpl in *; auto.
Qed.

Lemma security_le_low_ind : forall κ1 κ2,
  security_le κ1 κ2 -> κ2.(indirect_reader) = Low -> κ1.(indirect_reader) = Low.
Proof.
  intros [r1 i1] [r2 i2]; unfold security_le; simpl.
  intros [H1 H2] H; subst.
  destruct i1; simpl in *; [reflexivity | destruct H2].
Qed.

Lemma security_le_low_reader : forall κ1 κ2,
  security_le κ1 κ2 -> κ2.(reader) = Low -> κ1.(reader) = Low.
Proof.
  intros [r1 i1] [r2 i2]; unfold security_le; simpl.
  intros [H1 H2] H; subst.
  destruct r1; simpl in *; [reflexivity | destruct H1].
Qed.

(* ---- boolean test for the Low label ---- *)

Definition is_low (l : label) : bool :=
  match l with Low => true | High => false end.

Lemma is_low_true : forall l, is_low l = true <-> l = Low.
Proof.
  intro l; destruct l; simpl.
  - split; intro H; reflexivity.
  - split; intro H; [discriminate H | discriminate H].
Qed.

Lemma is_low_false : forall l, is_low l = false <-> l = High.
Proof.
  intro l; destruct l; simpl.
  - split; intro H; [discriminate H | discriminate H].
  - split; intro H; reflexivity.
Qed.

Lemma is_low_iff_flows : forall κ,
  is_low κ.(indirect_reader) = true <-> flows_to κ.(indirect_reader) Low.
Proof.
  intros [r i]; simpl. destruct i; simpl.
  - split; intro H; reflexivity.
  - split; intro H; [discriminate H | destruct H].
Qed.

Lemma flows_low_is_low : forall κ,
  flows_to κ.(indirect_reader) Low -> is_low κ.(indirect_reader) = true.
Proof. intros κ H; apply is_low_iff_flows; exact H. Qed.

Lemma not_flows_low_is_high : forall κ,
  ~ flows_to κ.(indirect_reader) Low -> is_low κ.(indirect_reader) = false.
Proof.
  intros [r i] H; simpl in *.
  destruct i; simpl in *.
  - exfalso; apply H; exact I.
  - reflexivity.
Qed.

(* ---- type protection lemmas ---- *)

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof.
  intros [κ | T1 T2 κ | T1 T2 κ | T1 T2 κ]; simpl;
  rewrite protect_security_low; reflexivity.
Qed.

Lemma security_of_ty_protect : forall l T,
  security_of (ty_protect l T) = protect_security (security_of T) l.
Proof.
  intros l [κ | T1 T2 κ | T1 T2 κ | T1 T2 κ]; reflexivity.
Qed.

Lemma ty_protect_high_ind : forall T,
  (security_of (ty_protect High T)).(indirect_reader) = High.
Proof.
  intro T; destruct T; simpl; unfold protect_security; simpl;
  rewrite join_high; reflexivity.
Qed.

(* ---- value security extraction ---- *)

Definition value_security (v : tm) : security :=
  match v with
  | tm_unit κ => κ
  | tm_abs _ _ κ => κ
  | tm_pair _ _ κ => κ
  | tm_inl _ κ => κ
  | tm_inr _ κ => κ
  | _ => public
  end.

Lemma value_security_protect : forall v,
  value v -> forall l,
  value_security (protect_value v l) = protect_security (value_security v) l.
Proof.
  intros v Hv; induction Hv; intro l; simpl; reflexivity.
Qed.

Lemma protect_value_low : forall v, value v -> protect_value v Low = v.
Proof.
  intros v Hv; induction Hv; simpl;
  try reflexivity;
  rewrite protect_security_low; reflexivity.
Qed.

Lemma protect_value_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv; induction Hv; simpl.
  - apply v_unit.
  - apply v_abs. exact H.
  - apply v_pair; assumption.
  - apply v_inl; assumption.
  - apply v_inr; assumption.
Qed.

(* ================================================================== *)
(* The logical relation                                                *)
(* ================================================================== *)

(* The relation is indexed by the observer level, which is fixed to Low.
   A value of type T is observable at Low when the indirect reader of the
   security annotation of T is Low.  Otherwise the value is opaque and any
   two values are related.  Values also satisfy an invariant that their
   runtime security annotation is bounded (in the indirect component) by
   the security of their type. *)

Fixpoint value_rel (T : ty) (v1 v2 : tm) {struct T} : Prop :=
  value v1 /\ value v2 /\
  flows_to (value_security v1).(indirect_reader) (security_of T).(indirect_reader) /\
  flows_to (value_security v2).(indirect_reader) (security_of T).(indirect_reader) /\
  match T with
  | Ty_Unit κ =>
      if is_low κ.(indirect_reader) then
        (exists k1 k2 : security, v1 = tm_unit k1 /\ v2 = tm_unit k2)
      else True
  | Ty_Sum T1 T2 κ =>
      if is_low κ.(indirect_reader) then
        ((exists (a1 a2 : tm) (k1 k2 : security),
            v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\ value_rel T1 a1 a2) \/
         (exists (a1 a2 : tm) (k1 k2 : security),
            v1 = tm_inr a1 k1 /\ v2 = tm_inr a2 k2 /\ value_rel T2 a1 a2))
      else True
  | Ty_Prod T1 T2 κ =>
      if is_low κ.(indirect_reader) then
        (exists (a1 a2 b1 b2 : tm) (k1 k2 : security),
            v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
            value_rel T1 a1 a2 /\ value_rel T2 b1 b2)
      else True
  | Ty_Arrow T1 T2 κ =>
      if is_low κ.(indirect_reader) then
        (forall (u1 u2 : tm) (r : label),
            value_rel T1 u1 u2 -> flows_to κ.(reader) r ->
            forall w1 w2 : tm,
              evaluates (tm_app v1 u1 r) w1 ->
              evaluates (tm_app v2 u2 r) w2 -> value_rel T2 w1 w2)
      else True
  end.

Definition term_rel (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm,
    evaluates t1 v1 -> evaluates t2 v2 -> value_rel T v1 v2.

(* ---- projections of the relation ---- *)

Lemma value_rel_v1 : forall T v1 v2, value_rel T v1 v2 -> value v1.
Proof.
  intros T v1 v2 H; destruct T; simpl in H; destruct H as [H _]; exact H.
Qed.

Lemma value_rel_v2 : forall T v1 v2, value_rel T v1 v2 -> value v2.
Proof.
  intros T v1 v2 H; destruct T; simpl in H;
  destruct H as [_ [H _]]; exact H.
Qed.

Lemma value_rel_b1 : forall T v1 v2,
  value_rel T v1 v2 ->
  flows_to (value_security v1).(indirect_reader) (security_of T).(indirect_reader).
Proof.
  intros T v1 v2 H; destruct T; simpl in H;
  destruct H as [_ [_ [H _]]]; exact H.
Qed.

Lemma value_rel_b2 : forall T v1 v2,
  value_rel T v1 v2 ->
  flows_to (value_security v2).(indirect_reader) (security_of T).(indirect_reader).
Proof.
  intros T v1 v2 H; destruct T; simpl in H;
  destruct H as [_ [_ [_ [H _]]]]; exact H.
Qed.

(* ---- values and evaluation ---- *)

Lemma value_no_step : forall v, value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv; induction Hv; intros t Hstep; inversion Hstep; subst; firstorder.
Qed.

Lemma multi_value_inv : forall v u, value v -> multi v u -> u = v.
Proof.
  intros v u Hv Hm.
  remember v as t eqn:E.
  induction Hm.
  - subst. reflexivity.
  - subst v. exfalso. eapply value_no_step; eauto.
Qed.

Lemma term_rel_of_value_rel : forall T v1 v2,
  value_rel T v1 v2 -> term_rel T v1 v2.
Proof.
  intros T v1 v2 Hrel v1' v2' He1 He2.
  destruct He1 as [Hm1 Hval1]; destruct He2 as [Hm2 Hval2].
  pose proof (value_rel_v1 _ _ _ Hrel) as Hv1.
  pose proof (value_rel_v2 _ _ _ Hrel) as Hv2.
  assert (E1 : v1' = v1) by (eapply multi_value_inv; eauto).
  assert (E2 : v2' = v2) by (eapply multi_value_inv; eauto).
  subst; exact Hrel.
Qed.

(* ---- opaque types: any two values are related ---- *)

Lemma sec_ind_high : forall κ, ~ flows_to κ.(indirect_reader) Low -> κ.(indirect_reader) = High.
Proof.
  intros κ H; destruct κ.(indirect_reader); auto.
  exfalso; apply H; simpl; exact I.
Qed.

Lemma value_rel_opaque : forall T v1 v2,
  ~ flows_to (security_of T).(indirect_reader) Low ->
  value v1 -> value v2 -> value_rel T v1 v2.
Proof.
  intros T v1 v2 Hnot Hv1 Hv2.
  destruct T as [κ | T1 T2 κ | T1 T2 κ | T1 T2 κ]; simpl in *;
  rewrite (sec_ind_high κ Hnot); simpl; repeat split; auto using flows_to_any_high.
Qed.

Lemma term_rel_opaque : forall T t1 t2,
  ~ flows_to (security_of T).(indirect_reader) Low -> term_rel T t1 t2.
Proof.
  intros T t1 t2 Hnot v1 v2 [Hm1 Hv1] [Hm2 Hv2].
  eapply value_rel_opaque; eauto.
Qed.

(* ================================================================== *)
(* Decomposition of evaluations                                        *)
(* ================================================================== *)

Lemma unit_no_step : forall k t, ~ (tm_unit k --> t).
Proof. intros k t H; inversion H. Qed.

Lemma abs_no_step : forall T body k t, ~ (tm_abs T body k --> t).
Proof. intros T body k t H; inversion H. Qed.

Lemma multi_unit_inv : forall k w, multi (tm_unit k) w -> w = tm_unit k.
Proof.
  intros k w Hm; remember (tm_unit k) as t eqn:E.
  induction Hm; subst.
  - reflexivity.
  - exfalso; eapply unit_no_step; eauto.
Qed.

Lemma multi_abs_inv : forall T body k w,
  multi (tm_abs T body k) w -> w = tm_abs T body k.
Proof.
  intros T body k w Hm; remember (tm_abs T body k) as u eqn:E.
  induction Hm; subst.
  - reflexivity.
  - exfalso; eapply abs_no_step; eauto.
Qed.

Lemma multi_app_inv : forall a b r w,
  multi (tm_app a b r) w -> value w ->
  exists (T : ty) (body : tm) (k : security) (v : tm),
    multi a (tm_abs T body k) /\ value (tm_abs T body k) /\
    multi b v /\ value v /\ flows_to k.(reader) r /\
    multi (tm_protect k.(indirect_reader) (open body v)) w.
Proof.
  intros a b r w Hm.
  remember (tm_app a b r) as t eqn:E.
  revert a b r E.
  induction Hm; intros a b r E Hw.
  - subst; inversion Hw.
  - subst; inversion H; subst.
    + exists T, body, kappa, b. repeat split; try assumption; try apply multi_refl.
    + edestruct (IHHm t1' b r eq_refl Hw) as (T & body & k & v & Ha & Hva & Hb & Hvb & Hfl & Hres).
      exists T, body, k, v. repeat split; try assumption.
      econstructor; eauto.
    + edestruct (IHHm a t2' r eq_refl Hw) as (T & body & k & v & Ha & Hva & Hb & Hvb & Hfl & Hres).
      exists T, body, k, v. repeat split; try assumption.
      econstructor; eauto.
Qed.

Lemma multi_pair_inv : forall a b k w,
  multi (tm_pair a b k) w -> value w ->
  exists a' b', multi a a' /\ value a' /\ multi b b' /\ value b' /\
                w = tm_pair a' b' k.
Proof.
  intros a b k w Hm.
  remember (tm_pair a b k) as t eqn:E.
  revert a b k E.
  induction Hm; intros a b k E Hw.
  - subst; inversion Hw; subst. exists a, b. repeat split; try assumption; try apply multi_refl; try reflexivity.
  - subst; inversion H; subst.
    + edestruct (IHHm t1' b k eq_refl Hw) as (a' & b' & Ha & Hva & Hb & Hvb & Hw').
      exists a', b'. repeat split; try assumption. econstructor; eauto.
    + edestruct (IHHm a t2' k eq_refl Hw) as (a' & b' & Ha & Hva & Hb & Hvb & Hw').
      exists a', b'. repeat split; try assumption. econstructor; eauto.
Qed.

Lemma multi_fst_inv : forall t r w,
  multi (tm_fst t r) w -> value w ->
  exists v1 v2 k, multi t (tm_pair v1 v2 k) /\ value v1 /\ value v2 /\
                  flows_to k.(reader) r /\
                  multi (tm_protect k.(indirect_reader) v1) w.
Proof.
  intros t r w Hm.
  remember (tm_fst t r) as u eqn:E.
  revert t r E.
  induction Hm; intros t0 r0 E Hw.
  - subst; inversion Hw.
  - subst; inversion H; subst.
    + exists v1, v2, kappa. repeat split; try assumption; try apply multi_refl.
    + edestruct (IHHm t' r0 eq_refl Hw) as (v1 & v2 & k & Ht & Hv1 & Hv2 & Hfl & Hres).
      exists v1, v2, k. repeat split; try assumption. econstructor; eauto.
Qed.

Lemma multi_snd_inv : forall t r w,
  multi (tm_snd t r) w -> value w ->
  exists v1 v2 k, multi t (tm_pair v1 v2 k) /\ value v1 /\ value v2 /\
                  flows_to k.(reader) r /\
                  multi (tm_protect k.(indirect_reader) v2) w.
Proof.
  intros t r w Hm.
  remember (tm_snd t r) as u eqn:E.
  revert t r E.
  induction Hm; intros t0 r0 E Hw.
  - subst; inversion Hw.
  - subst; inversion H; subst.
    + exists v1, v2, kappa. repeat split; try assumption; try apply multi_refl.
    + edestruct (IHHm t' r0 eq_refl Hw) as (v1 & v2 & k & Ht & Hv1 & Hv2 & Hfl & Hres).
      exists v1, v2, k. repeat split; try assumption. econstructor; eauto.
Qed.

Lemma multi_inl_inv : forall t k w,
  multi (tm_inl t k) w -> value w ->
  exists v, multi t v /\ value v /\ w = tm_inl v k.
Proof.
  intros t k w Hm.
  remember (tm_inl t k) as u eqn:E.
  revert t k E.
  induction Hm; intros t0 k0 E Hw.
  - subst; inversion Hw; subst. exists t0. repeat split; try assumption; try apply multi_refl; try reflexivity.
  - subst; inversion H; subst.
    edestruct (IHHm t' k0 eq_refl Hw) as (v & Ht & Hv & Hw').
    exists v. repeat split; try assumption. econstructor; eauto.
Qed.

Lemma multi_inr_inv : forall t k w,
  multi (tm_inr t k) w -> value w ->
  exists v, multi t v /\ value v /\ w = tm_inr v k.
Proof.
  intros t k w Hm.
  remember (tm_inr t k) as u eqn:E.
  revert t k E.
  induction Hm; intros t0 k0 E Hw.
  - subst; inversion Hw; subst. exists t0. repeat split; try assumption; try apply multi_refl; try reflexivity.
  - subst; inversion H; subst.
    edestruct (IHHm t' k0 eq_refl Hw) as (v & Ht & Hv & Hw').
    exists v. repeat split; try assumption. econstructor; eauto.
Qed.

Lemma multi_case_inv : forall t b1 b2 r w,
  multi (tm_case t b1 b2 r) w -> value w ->
  (exists v k, multi t (tm_inl v k) /\ value v /\ flows_to k.(reader) r /\
               multi (tm_protect k.(indirect_reader) (open b1 v)) w) \/
  (exists v k, multi t (tm_inr v k) /\ value v /\ flows_to k.(reader) r /\
               multi (tm_protect k.(indirect_reader) (open b2 v)) w).
Proof.
  intros t b1 b2 r w Hm.
  remember (tm_case t b1 b2 r) as u eqn:E.
  revert t b1 b2 r E.
  induction Hm; intros t0 b10 b20 r0 E Hw.
  - subst; inversion Hw.
  - subst; inversion H; subst.
    + left. exists v, kappa. repeat split; try assumption; try apply multi_refl.
    + right. exists v, kappa. repeat split; try assumption; try apply multi_refl.
    + edestruct (IHHm t' b10 b20 r0 eq_refl Hw) as [(v & k & Ht & Hv & Hfl & Hres) | (v & k & Ht & Hv & Hfl & Hres)];
        [left | right]; exists v, k; repeat split; try assumption; econstructor; eauto.
Qed.

Lemma multi_protect_inv : forall l t w,
  multi (tm_protect l t) w -> value w ->
  exists v, multi t v /\ value v /\ w = protect_value v l.
Proof.
  intros l t w Hm.
  remember (tm_protect l t) as u eqn:E.
  revert l t E.
  induction Hm; intros l0 t0 E Hw.
  - subst; inversion Hw.
  - subst; inversion H; subst.
    + exists t0. repeat split; try assumption; try apply multi_refl.
      eapply multi_value_inv; [apply protect_value_value; exact H3 | exact Hm].
    + edestruct (IHHm l0 t' eq_refl Hw) as (v & Ht & Hv & Hw').
      exists v. repeat split; try assumption. econstructor; eauto.
Qed.

Lemma multi_if_inv : forall c y n r w,
  multi (tm_if c y n r) w -> value w ->
  (exists v k, multi c (tm_inl v k) /\ value v /\ flows_to k.(reader) r /\
               multi (tm_protect k.(indirect_reader) y) w) \/
  (exists v k, multi c (tm_inr v k) /\ value v /\ flows_to k.(reader) r /\
               multi (tm_protect k.(indirect_reader) n) w).
Proof.
  intros c y n r w Hm.
  remember (tm_if c y n r) as u eqn:E.
  revert c y n r E.
  induction Hm; intros c0 y0 n0 r0 E Hw.
  - subst; inversion Hw.
  - subst; inversion H; subst.
    + edestruct (IHHm c' y0 n0 r0 eq_refl Hw) as [(v & k & Hc & Hv & Hfl & Hres) | (v & k & Hc & Hv & Hfl & Hres)];
        [left | right]; exists v, k; repeat split; try assumption; econstructor; eauto.
    + left. exists v, k. repeat split; try assumption; try apply multi_refl.
    + right. exists v, k. repeat split; try assumption; try apply multi_refl.
Qed.

(* ================================================================== *)
(* Protection and the relation                                         *)
(* ================================================================== *)

Lemma security_le_reader : forall κ1 κ2,
  security_le κ1 κ2 -> flows_to κ1.(reader) κ2.(reader).
Proof.
  intros [r1 i1] [r2 i2]; unfold security_le; simpl; intros [H1 H2]; exact H1.
Qed.

Lemma security_le_ind : forall κ1 κ2,
  security_le κ1 κ2 -> flows_to κ1.(indirect_reader) κ2.(indirect_reader).
Proof.
  intros [r1 i1] [r2 i2]; unfold security_le; simpl; intros [H1 H2]; exact H2.
Qed.

Lemma gate_subtype : forall κ1 κ2,
  security_le κ1 κ2 -> is_low κ2.(indirect_reader) = true -> is_low κ1.(indirect_reader) = true.
Proof.
  intros κ1 κ2 Hle H2.
  apply is_low_true in H2. apply is_low_true.
  pose proof (security_le_ind _ _ Hle).
  rewrite H2 in H. apply flows_to_low_iff in H. exact H.
Qed.

Lemma gate_subtype_closed : forall κ1 κ2,
  security_le κ1 κ2 -> is_low κ1.(indirect_reader) = false -> is_low κ2.(indirect_reader) = false.
Proof.
  intros κ1 κ2 Hle H1.
  apply is_low_false in H1. apply is_low_false.
  pose proof (security_le_ind _ _ Hle).
  rewrite H1 in H. destruct κ2.(indirect_reader); simpl in *; auto. destruct H.
Qed.

Lemma security_le_from_subtype : forall T U, subtype T U ->
  security_le (security_of T) (security_of U).
Proof.
  intros T U H; induction H; simpl; auto using security_le_refl.
  eapply security_le_trans; [exact IHsubtype1 | exact IHsubtype2].
Qed.

Lemma value_rel_high_ind : forall T v1 v2,
  (security_of T).(indirect_reader) = High ->
  value v1 -> value v2 -> value_rel T v1 v2.
Proof.
  intros T v1 v2 Hind Hv1 Hv2.
  destruct T as [κ | T1 T2 κ | T1 T2 κ | T1 T2 κ]; simpl in *;
  simpl; rewrite Hind; simpl; repeat split; auto using flows_to_any_high.
Qed.

Lemma value_rel_protect_low : forall T v1 v2,
  value_rel T v1 v2 ->
  value_rel (ty_protect Low T) (protect_value v1 Low) (protect_value v2 Low).
Proof.
  intros T v1 v2 Hrel.
  rewrite ty_protect_low.
  rewrite protect_value_low by exact (value_rel_v1 T v1 v2 Hrel).
  rewrite protect_value_low by exact (value_rel_v2 T v1 v2 Hrel).
  exact Hrel.
Qed.

Lemma value_rel_protect_high : forall T v1 v2,
  value_rel T v1 v2 ->
  value_rel (ty_protect High T) (protect_value v1 High) (protect_value v2 High).
Proof.
  intros T v1 v2 Hrel.
  apply value_rel_high_ind.
  - apply ty_protect_high_ind.
  - exact (protect_value_value v1 High (value_rel_v1 T v1 v2 Hrel)).
  - exact (protect_value_value v2 High (value_rel_v2 T v1 v2 Hrel)).
Qed.

Lemma value_rel_protect : forall T v1 v2 l,
  value_rel T v1 v2 ->
  value_rel (ty_protect l T) (protect_value v1 l) (protect_value v2 l).
Proof.
  intros T v1 v2 l Hrel; destruct l.
  - apply value_rel_protect_low; exact Hrel.
  - apply value_rel_protect_high; exact Hrel.
Qed.

Lemma term_rel_protect : forall T t1 t2 l,
  term_rel T t1 t2 -> term_rel (ty_protect l T) (tm_protect l t1) (tm_protect l t2).
Proof.
  intros T t1 t2 l Hrel.
  unfold term_rel in *.
  intros v1 v2 [Hm1 Hval1] [Hm2 Hval2].
  edestruct (multi_protect_inv l t1 v1 Hm1 Hval1) as (u1 & Ht1 & Hu1 & Ev1).
  edestruct (multi_protect_inv l t2 v2 Hm2 Hval2) as (u2 & Ht2 & Hu2 & Ev2).
  pose proof (Hrel u1 u2 (conj Ht1 Hu1) (conj Ht2 Hu2)) as Hc.
  pose proof (value_rel_protect _ _ _ l Hc) as Hp.
  rewrite Ev1, Ev2. exact Hp.
Qed.

(* ================================================================== *)
(* Monotonicity of the relation with respect to subtyping              *)
(* ================================================================== *)

Lemma value_rel_subtype : forall T U, subtype T U ->
  forall v1 v2, value_rel T v1 v2 -> value_rel U v1 v2.
Proof.
  intros T U Hsub.
  induction Hsub; intros v1 v2 Hrel.
  - (* S_Unit *)
    destruct (is_low kappa2.(indirect_reader)) eqn:E2.
    + assert (E1 : is_low kappa1.(indirect_reader) = true) by (eapply gate_subtype; eauto).
      simpl. rewrite E2. simpl. repeat split.
      * exact (value_rel_v1 _ _ _ Hrel).
      * exact (value_rel_v2 _ _ _ Hrel).
      * eapply flows_to_trans; [exact (value_rel_b1 _ _ _ Hrel) | apply security_le_ind; exact H1].
      * eapply flows_to_trans; [exact (value_rel_b2 _ _ _ Hrel) | apply security_le_ind; exact H1].
      * simpl in Hrel. rewrite E1 in Hrel. simpl in Hrel.
        destruct Hrel as [_ [_ [_ [_ Hst]]]]. exact Hst.
    + simpl. rewrite E2. simpl. repeat split.
      * exact (value_rel_v1 _ _ _ Hrel).
      * exact (value_rel_v2 _ _ _ Hrel).
      * eapply flows_to_trans; [exact (value_rel_b1 _ _ _ Hrel) | apply security_le_ind; exact H1].
      * eapply flows_to_trans; [exact (value_rel_b2 _ _ _ Hrel) | apply security_le_ind; exact H1].
  - (* S_Sum *)
    destruct (is_low kappa2.(indirect_reader)) eqn:E2.
    + assert (E1 : is_low kappa1.(indirect_reader) = true) by (eapply gate_subtype; eauto).
      simpl. rewrite E2. simpl. repeat split.
      * exact (value_rel_v1 _ _ _ Hrel).
      * exact (value_rel_v2 _ _ _ Hrel).
      * eapply flows_to_trans; [exact (value_rel_b1 _ _ _ Hrel) | apply security_le_ind; exact H1].
      * eapply flows_to_trans; [exact (value_rel_b2 _ _ _ Hrel) | apply security_le_ind; exact H1].
      * simpl in Hrel. rewrite E1 in Hrel. simpl in Hrel.
        destruct Hrel as [_ [_ [_ [_ Hst]]]].
        destruct Hst as [(a1 & a2 & k1 & k2 & Ea1 & Ea2 & Hc) | (a1 & a2 & k1 & k2 & Ea1 & Ea2 & Hc)].
        -- left. exists a1, a2, k1, k2. repeat split; try assumption. apply IHHsub1; exact Hc.
        -- right. exists a1, a2, k1, k2. repeat split; try assumption. apply IHHsub2; exact Hc.
    + simpl. rewrite E2. simpl. repeat split.
      * exact (value_rel_v1 _ _ _ Hrel).
      * exact (value_rel_v2 _ _ _ Hrel).
      * eapply flows_to_trans; [exact (value_rel_b1 _ _ _ Hrel) | apply security_le_ind; exact H1].
      * eapply flows_to_trans; [exact (value_rel_b2 _ _ _ Hrel) | apply security_le_ind; exact H1].
  - (* S_Prod *)
    destruct (is_low kappa2.(indirect_reader)) eqn:E2.
    + assert (E1 : is_low kappa1.(indirect_reader) = true) by (eapply gate_subtype; eauto).
      simpl. rewrite E2. simpl. repeat split.
      * exact (value_rel_v1 _ _ _ Hrel).
      * exact (value_rel_v2 _ _ _ Hrel).
      * eapply flows_to_trans; [exact (value_rel_b1 _ _ _ Hrel) | apply security_le_ind; exact H1].
      * eapply flows_to_trans; [exact (value_rel_b2 _ _ _ Hrel) | apply security_le_ind; exact H1].
      * simpl in Hrel. rewrite E1 in Hrel. simpl in Hrel.
        destruct Hrel as [_ [_ [_ [_ Hst]]]].
        destruct Hst as (a1 & a2 & b1 & b2 & k1 & k2 & Ea1 & Ea2 & Hc1 & Hc2).
        exists a1, a2, b1, b2, k1, k2. repeat split; try assumption.
        -- apply IHHsub1; exact Hc1.
        -- apply IHHsub2; exact Hc2.
    + simpl. rewrite E2. simpl. repeat split.
      * exact (value_rel_v1 _ _ _ Hrel).
      * exact (value_rel_v2 _ _ _ Hrel).
      * eapply flows_to_trans; [exact (value_rel_b1 _ _ _ Hrel) | apply security_le_ind; exact H1].
      * eapply flows_to_trans; [exact (value_rel_b2 _ _ _ Hrel) | apply security_le_ind; exact H1].
  - (* S_Arrow *)
    destruct (is_low kappa2.(indirect_reader)) eqn:E2.
    + assert (E1 : is_low kappa1.(indirect_reader) = true) by (eapply gate_subtype; eauto).
      simpl. rewrite E2. simpl. repeat split.
      * exact (value_rel_v1 _ _ _ Hrel).
      * exact (value_rel_v2 _ _ _ Hrel).
      * eapply flows_to_trans; [exact (value_rel_b1 _ _ _ Hrel) | apply security_le_ind; exact H1].
      * eapply flows_to_trans; [exact (value_rel_b2 _ _ _ Hrel) | apply security_le_ind; exact H1].
      * simpl in Hrel. rewrite E1 in Hrel. simpl in Hrel.
        destruct Hrel as [_ [_ [_ [_ Hst]]]].
        intros u1 u2 r Hu Hr.
        intros w1 w2 He1 He2.
        apply IHHsub2.
        eapply Hst.
        -- apply IHHsub1; exact Hu.
        -- eapply flows_to_trans; [apply security_le_reader; exact H1 | exact Hr].
        -- exact He1.
        -- exact He2.
    + simpl. rewrite E2. simpl. repeat split.
      * exact (value_rel_v1 _ _ _ Hrel).
      * exact (value_rel_v2 _ _ _ Hrel).
      * eapply flows_to_trans; [exact (value_rel_b1 _ _ _ Hrel) | apply security_le_ind; exact H1].
      * eapply flows_to_trans; [exact (value_rel_b2 _ _ _ Hrel) | apply security_le_ind; exact H1].
  - (* S_Trans *)
    apply IHHsub2, IHHsub1. exact Hrel.
Qed.

Lemma term_rel_subtype : forall T U, subtype T U ->
  forall t1 t2, term_rel T t1 t2 -> term_rel U t1 t2.
Proof.
  intros T U Hsub t1 t2 Hrel.
  unfold term_rel in *.
  intros v1 v2 He1 He2.
  eapply value_rel_subtype; [exact Hsub | eapply Hrel; eauto].
Qed.

(* ================================================================== *)
(* Locally closed terms                                                *)
(* ================================================================== *)

Lemma lc_at_mono : forall t k k', k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  induction t as [i | x | kap | T body IHbody kap | a IHa b IHb r | a IHa b IHb kap
                 | a IHa r | a IHa r | a IHa kap | a IHa kap
                 | t0 IHt0 b1 IHb1 b2 IHb2 r | l a IHa | c IHc y IHy n IHn r];
  intros k k' Hle H; simpl in *; try easy.
  - lia.
  - apply IHbody with (k := S k); [lia | exact H].
  - destruct H as [H1 H2]; split; [apply IHa with (k := k) | apply IHb with (k := k)]; auto.
  - destruct H as [H1 H2]; split; [apply IHa with (k := k) | apply IHb with (k := k)]; auto.
  - apply IHa with (k := k); auto.
  - apply IHa with (k := k); auto.
  - apply IHa with (k := k); auto.
  - apply IHa with (k := k); auto.
  - destruct H as [H1 [H2 H3]]; repeat split;
    [apply IHt0 with (k := k) | apply IHb1 with (k := S k) | apply IHb2 with (k := S k)];
    auto; try lia.
  - apply IHa with (k := k); auto.
  - destruct H as [H1 [H2 H3]]; repeat split;
    [apply IHc with (k := k) | apply IHy with (k := k) | apply IHn with (k := k)]; auto.
Qed.

Lemma lc_at_mono_zero : forall t k, locally_closed t -> lc_at k t.
Proof. intros t k H; apply lc_at_mono with (k := 0); auto; lia. Qed.

Lemma open_rec_lc : forall t k u, lc_at k t -> open_rec k u t = t.
Proof.
  induction t as [i | x | kap | T body IHbody kap | a IHa b IHb r | a IHa b IHb kap
                 | a IHa r | a IHa r | a IHa kap | a IHa kap
                 | t0 IHt0 b1 IHb1 b2 IHb2 r | l a IHa | c IHc y IHy n IHn r];
  intros k u H; simpl in *.
  - destruct (Nat.eqb k i) eqn:E; [| reflexivity].
    exfalso. apply Nat.eqb_eq in E. lia.
  - reflexivity.
  - reflexivity.
  - rewrite (IHbody (S k) u H). reflexivity.
  - destruct H as [H1 H2]. rewrite (IHa k u H1), (IHb k u H2). reflexivity.
  - destruct H as [H1 H2]. rewrite (IHa k u H1), (IHb k u H2). reflexivity.
  - rewrite (IHa k u H). reflexivity.
  - rewrite (IHa k u H). reflexivity.
  - rewrite (IHa k u H). reflexivity.
  - rewrite (IHa k u H). reflexivity.
  - destruct H as [H1 [H2 H3]].
    rewrite (IHt0 k u H1), (IHb1 (S k) u H2), (IHb2 (S k) u H3). reflexivity.
  - rewrite (IHa k u H). reflexivity.
  - destruct H as [H1 [H2 H3]].
    rewrite (IHc k u H1), (IHy k u H2), (IHn k u H3). reflexivity.
Qed.

Lemma lc_open_rec_fvar : forall body x k,
  ~ In x (fv body) ->
  (lc_at k (open_rec k (tm_fvar x) body) <-> lc_at (S k) body).
Proof.
  induction body as [i | y | kap | T b IHb kap | a IHa b IHb r | a IHa b IHb kap
                     | a IHa r | a IHa r | a IHa kap | a IHa kap
                     | t0 IHt0 b1 IHb1 b2 IHb2 r | l a IHa | c IHc y IHy n IHn r];
  intros x k Hx; simpl in *.
  - destruct (Nat.eqb k i) eqn:E; simpl.
    + apply Nat.eqb_eq in E; subst. split; intro H; [lia | exact I].
    + apply Nat.eqb_neq in E. split; intro H; lia.
  - simpl. split; auto.
  - simpl. split; auto.
  - exact (IHb x (S k) Hx).
  - assert (Hxa : ~ In x (fv a)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hxb : ~ In x (fv b)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
    rewrite (IHa x k Hxa), (IHb x k Hxb). tauto.
  - assert (Hxa : ~ In x (fv a)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hxb : ~ In x (fv b)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
    rewrite (IHa x k Hxa), (IHb x k Hxb). tauto.
  - rewrite (IHa x k Hx). tauto.
  - rewrite (IHa x k Hx). tauto.
  - rewrite (IHa x k Hx). tauto.
  - rewrite (IHa x k Hx). tauto.
  - assert (Hx0 : ~ In x (fv t0)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hx1 : ~ In x (fv b1)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hx2 : ~ In x (fv b2)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    rewrite (IHt0 x k Hx0), (IHb1 x (S k) Hx1), (IHb2 x (S k) Hx2). tauto.
  - rewrite (IHa x k Hx). tauto.
  - assert (Hx0 : ~ In x (fv c)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hx1 : ~ In x (fv y)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hx2 : ~ In x (fv n)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    rewrite (IHc x k Hx0), (IHy x k Hx1), (IHn x k Hx2). tauto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv; induction Hv; simpl.
  - exact I.
  - exact H.
  - split; assumption.
  - assumption.
  - assumption.
Qed.

(* ================================================================== *)
(* Fresh atoms                                                         *)
(* ================================================================== *)

Fixpoint list_max (l : list atom) : atom :=
  match l with
  | [] => 0
  | x :: l' => max x (list_max l')
  end.

Lemma in_list_max : forall l x, In x l -> x <= list_max l.
Proof.
  induction l as [| a l IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall l : list atom, exists x, ~ In x l.
Proof.
  intro l; exists (S (list_max l)).
  intro Hin; apply in_list_max in Hin; lia.
Qed.

(* ================================================================== *)
(* Substitution environments                                           *)
(* ================================================================== *)

Fixpoint subst_env (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit kap => tm_unit kap
  | tm_abs T body kap => tm_abs T (subst_env rho body) kap
  | tm_app a b r => tm_app (subst_env rho a) (subst_env rho b) r
  | tm_pair a b kap => tm_pair (subst_env rho a) (subst_env rho b) kap
  | tm_fst a r => tm_fst (subst_env rho a) r
  | tm_snd a r => tm_snd (subst_env rho a) r
  | tm_inl a kap => tm_inl (subst_env rho a) kap
  | tm_inr a kap => tm_inr (subst_env rho a) kap
  | tm_case t0 b1 b2 r => tm_case (subst_env rho t0) (subst_env rho b1) (subst_env rho b2) r
  | tm_protect l a => tm_protect l (subst_env rho a)
  | tm_if c y n r => tm_if (subst_env rho c) (subst_env rho y) (subst_env rho n) r
  end.

Definition extend_env (rho : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else rho y.

Definition range_lc (rho : atom -> tm) : Prop :=
  forall y, locally_closed (rho y).

Lemma extend_env_eq : forall rho x u, extend_env rho x u x = u.
Proof. intros; unfold extend_env; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma extend_env_neq : forall rho x y u, y <> x -> extend_env rho x u y = rho y.
Proof.
  intros rho x y u H; unfold extend_env.
  destruct (Nat.eqb y x) eqn:E; [| reflexivity].
  exfalso. apply Nat.eqb_eq in E. exact (H E).
Qed.

Lemma range_lc_extend : forall rho x u,
  range_lc rho -> locally_closed u -> range_lc (extend_env rho x u).
Proof.
  intros rho x u Hr Hu y; unfold extend_env.
  destruct (Nat.eqb y x) eqn:E; [exact Hu | apply Hr].
Qed.

Lemma subst_env_fvar : forall rho x, subst_env rho (tm_fvar x) = rho x.
Proof. reflexivity. Qed.

Lemma subst_env_open_rec : forall rho x u body k,
  range_lc rho -> ~ In x (fv body) ->
  subst_env (extend_env rho x u) (open_rec k (tm_fvar x) body) =
  open_rec k u (subst_env rho body).
Proof.
  intros rho x u body k Hr Hx.
  revert rho x u k Hr Hx.
  induction body as [i | y | kap | T b IHb kap | a IHa b IHb r | a IHa b IHb kap
                     | a IHa r | a IHa r | a IHa kap | a IHa kap
                     | t0 IHt0 b1 IHb1 b2 IHb2 r | l a IHa | c IHc y IHy n IHn r];
  intros rho x u k Hr Hx; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + simpl. apply extend_env_eq.
    + reflexivity.
  - assert (Hyx : y <> x) by (intro Hc; apply Hx; simpl; subst; auto).
    destruct (Nat.eqb y x) eqn:E.
    + exfalso. apply Nat.eqb_eq in E. exact (Hyx E).
    + rewrite (extend_env_neq rho x y u Hyx). symmetry.
      apply open_rec_lc. apply lc_at_mono_zero. apply Hr.
  - reflexivity.
  - rewrite (IHb rho x u (S k) Hr Hx). reflexivity.
  - assert (Hxa : ~ In x (fv a)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hxb : ~ In x (fv b)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
    rewrite (IHa rho x u k Hr Hxa), (IHb rho x u k Hr Hxb). reflexivity.
  - assert (Hxa : ~ In x (fv a)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hxb : ~ In x (fv b)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
    rewrite (IHa rho x u k Hr Hxa), (IHb rho x u k Hr Hxb). reflexivity.
  - rewrite (IHa rho x u k Hr Hx). reflexivity.
  - rewrite (IHa rho x u k Hr Hx). reflexivity.
  - rewrite (IHa rho x u k Hr Hx). reflexivity.
  - rewrite (IHa rho x u k Hr Hx). reflexivity.
  - assert (Hx0 : ~ In x (fv t0)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hx1 : ~ In x (fv b1)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hx2 : ~ In x (fv b2)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    rewrite (IHt0 rho x u k Hr Hx0), (IHb1 rho x u (S k) Hr Hx1), (IHb2 rho x u (S k) Hr Hx2). reflexivity.
  - rewrite (IHa rho x u k Hr Hx). reflexivity.
  - assert (Hx0 : ~ In x (fv c)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hx1 : ~ In x (fv y)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hx2 : ~ In x (fv n)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    rewrite (IHc rho x u k Hr Hx0), (IHy rho x u k Hr Hx1), (IHn rho x u k Hr Hx2). reflexivity.
Qed.


(* ================================================================== *)
(* Free variables of program contexts                                  *)
(* ================================================================== *)

Fixpoint context_fv (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs T C' k => context_fv C'
  | C_AppLeft C' t r => fv t ++ context_fv C'
  | C_AppRight t C' r => fv t ++ context_fv C'
  | C_PairLeft C' t k => fv t ++ context_fv C'
  | C_PairRight t C' k => fv t ++ context_fv C'
  | C_Fst C' r => context_fv C'
  | C_Snd C' r => context_fv C'
  | C_Inl C' k => context_fv C'
  | C_Inr C' k => context_fv C'
  | C_CaseScrutinee C' b1 b2 r => context_fv C' ++ fv b1 ++ fv b2
  | C_CaseLeft t0 C' b2 r => fv t0 ++ context_fv C' ++ fv b2
  | C_CaseRight t0 b1 C' r => fv t0 ++ fv b1 ++ context_fv C'
  | C_Protect l C' => context_fv C'
  | C_IfCondition C' y n r => context_fv C' ++ fv y ++ fv n
  | C_IfThen c C' n r => fv c ++ context_fv C' ++ fv n
  | C_IfElse c y C' r => fv c ++ fv y ++ context_fv C'
  end.

Lemma in_fv_plug : forall C u y, In y (context_fv C) -> In y (fv (plug C u)).
Proof.
  induction C as [| T C IHC kap | C IHC t r | t C IHC r | C IHC t kap | t C IHC kap
                  | C IHC r | C IHC r | C IHC kap | C IHC kap | C IHC t1 t2 r
                  | t C IHC t2 r | t1 t2 C IHC r | l C IHC | C IHC y1 n1 r | c1 C IHC n1 r | c1 y1 C IHC r];
  intros u y Hy; simpl in *.
  - destruct Hy.
  - apply IHC; exact Hy.
  - apply in_app_or in Hy; destruct Hy as [Hy | Hy].
    + apply in_or_app; right; exact Hy.
    + apply in_or_app; left; apply IHC; exact Hy.
  - apply in_app_or in Hy; destruct Hy as [Hy | Hy].
    + apply in_or_app; left; exact Hy.
    + apply in_or_app; right; apply IHC; exact Hy.
  - apply in_app_or in Hy; destruct Hy as [Hy | Hy].
    + apply in_or_app; right; exact Hy.
    + apply in_or_app; left; apply IHC; exact Hy.
  - apply in_app_or in Hy; destruct Hy as [Hy | Hy].
    + apply in_or_app; left; exact Hy.
    + apply in_or_app; right; apply IHC; exact Hy.
  - apply IHC; exact Hy.
  - apply IHC; exact Hy.
  - apply IHC; exact Hy.
  - apply IHC; exact Hy.
  - apply in_app_or in Hy; destruct Hy as [Hy | Hy].
    + apply in_or_app; left; apply IHC; exact Hy.
    + apply in_app_or in Hy; destruct Hy as [Hy | Hy].
      * apply in_or_app; right; apply in_or_app; left; exact Hy.
      * apply in_or_app; right; apply in_or_app; right; exact Hy.
  - apply in_app_or in Hy; destruct Hy as [Hy | Hy].
    + apply in_or_app; left; exact Hy.
    + apply in_app_or in Hy; destruct Hy as [Hy | Hy].
      * apply in_or_app; right; apply in_or_app; left; apply IHC; exact Hy.
      * apply in_or_app; right; apply in_or_app; right; exact Hy.
  - apply in_app_or in Hy; destruct Hy as [Hy | Hy].
    + apply in_or_app; left; exact Hy.
    + apply in_app_or in Hy; destruct Hy as [Hy | Hy].
      * apply in_or_app; right; apply in_or_app; left; exact Hy.
      * apply in_or_app; right; apply in_or_app; right; apply IHC; exact Hy.
  - apply IHC; exact Hy.
  - apply in_app_or in Hy; destruct Hy as [Hy | Hy].
    + apply in_or_app; left; apply IHC; exact Hy.
    + apply in_app_or in Hy; destruct Hy as [Hy | Hy].
      * apply in_or_app; right; apply in_or_app; left; exact Hy.
      * apply in_or_app; right; apply in_or_app; right; exact Hy.
  - apply in_app_or in Hy; destruct Hy as [Hy | Hy].
    + apply in_or_app; left; exact Hy.
    + apply in_app_or in Hy; destruct Hy as [Hy | Hy].
      * apply in_or_app; right; apply in_or_app; left; apply IHC; exact Hy.
      * apply in_or_app; right; apply in_or_app; right; exact Hy.
  - apply in_app_or in Hy; destruct Hy as [Hy | Hy].
    + apply in_or_app; left; exact Hy.
    + apply in_app_or in Hy; destruct Hy as [Hy | Hy].
      * apply in_or_app; right; apply in_or_app; left; exact Hy.
      * apply in_or_app; right; apply in_or_app; right; apply IHC; exact Hy.
Qed.

(* ================================================================== *)
(* Locally closed preservation of typing                               *)
(* ================================================================== *)

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H; induction H; unfold locally_closed; simpl; auto.
  - (* T_Abs *) simpl.
    destruct (fresh_atom (L ++ fv body)) as [x Hx].
    assert (Hf : ~ In x (fv body)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
    apply (proj1 (lc_open_rec_fvar body x 0 Hf)).
    apply H2. intro Hc; apply Hx; apply in_or_app; left; exact Hc.
  - (* T_Case *) simpl.
    destruct (fresh_atom (L ++ fv body1 ++ fv body2)) as [x Hx].
    assert (Hf1 : ~ In x (fv body1)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hf2 : ~ In x (fv body2)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    assert (HxL : ~ In x L) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    split; [assumption | split].
    + apply (proj1 (lc_open_rec_fvar body1 x 0 Hf1)). apply H2. exact HxL.
    + apply (proj1 (lc_open_rec_fvar body2 x 0 Hf2)). apply H4. exact HxL.
Qed.

(* ================================================================== *)
(* Substitution with an environment that is the identity off one atom   *)
(* ================================================================== *)

Lemma subst_env_identity_off : forall t rho x,
  (forall y, y <> x -> rho y = tm_fvar y) ->
  ~ In x (fv t) ->
  subst_env rho t = t.
Proof.
  induction t as [i | y | kap | T b IHb kap | a IHa b IHb r | a IHa b IHb kap
                 | a IHa r | a IHa r | a IHa kap | a IHa kap
                 | t0 IHt0 b1 IHb1 b2 IHb2 r | l a IHa | c IHc y IHy n IHn r];
  intros rho x Hrho Hx; simpl in *.
  - reflexivity.
  - assert (Hne : y <> x) by (intro E; exact (Hx (or_introl E))).
    exact (Hrho y Hne).
  - reflexivity.
  - rewrite (IHb rho x Hrho Hx). reflexivity.
  - assert (Hxa : ~ In x (fv a)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hxb : ~ In x (fv b)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
    rewrite (IHa rho x Hrho Hxa), (IHb rho x Hrho Hxb). reflexivity.
  - assert (Hxa : ~ In x (fv a)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hxb : ~ In x (fv b)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
    rewrite (IHa rho x Hrho Hxa), (IHb rho x Hrho Hxb). reflexivity.
  - rewrite (IHa rho x Hrho Hx). reflexivity.
  - rewrite (IHa rho x Hrho Hx). reflexivity.
  - rewrite (IHa rho x Hrho Hx). reflexivity.
  - rewrite (IHa rho x Hrho Hx). reflexivity.
  - assert (Hx0 : ~ In x (fv t0)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hx1 : ~ In x (fv b1)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hx2 : ~ In x (fv b2)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    rewrite (IHt0 rho x Hrho Hx0), (IHb1 rho x Hrho Hx1), (IHb2 rho x Hrho Hx2). reflexivity.
  - rewrite (IHa rho x Hrho Hx). reflexivity.
  - assert (Hx0 : ~ In x (fv c)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hx1 : ~ In x (fv y)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hx2 : ~ In x (fv n)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    rewrite (IHc rho x Hrho Hx0), (IHy rho x Hrho Hx1), (IHn rho x Hrho Hx2). reflexivity.
Qed.

Lemma subst_env_open : forall rho x u body,
  range_lc rho -> ~ In x (fv body) ->
  subst_env (extend_env rho x u) (open body (tm_fvar x)) = open (subst_env rho body) u.
Proof. intros. unfold open. apply subst_env_open_rec; assumption. Qed.

Lemma subst_env_plug_fresh : forall C rho x,
  (forall y, y <> x -> rho y = tm_fvar y) ->
  ~ In x (context_fv C) ->
  subst_env rho (plug C (tm_fvar x)) = plug C (rho x).
Proof.
  induction C as [| T C IHC kap | C IHC t r | t C IHC r | C IHC t kap | t C IHC kap
                  | C IHC r | C IHC r | C IHC kap | C IHC kap | C IHC t1 t2 r
                  | t C IHC t2 r | t1 t2 C IHC r | l C IHC | C IHC y n r | c C IHC n r | c y C IHC r];
  intros rho x Hrho Hx; simpl in *.
  - reflexivity.
  - rewrite (IHC rho x Hrho Hx). reflexivity.
  - assert (Hxt : ~ In x (fv t)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hxc : ~ In x (context_fv C)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
    rewrite (subst_env_identity_off t rho x Hrho Hxt), (IHC rho x Hrho Hxc). reflexivity.
  - assert (Hxt : ~ In x (fv t)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hxc : ~ In x (context_fv C)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
    rewrite (subst_env_identity_off t rho x Hrho Hxt), (IHC rho x Hrho Hxc). reflexivity.
  - assert (Hxt : ~ In x (fv t)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hxc : ~ In x (context_fv C)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
    rewrite (subst_env_identity_off t rho x Hrho Hxt), (IHC rho x Hrho Hxc). reflexivity.
  - assert (Hxt : ~ In x (fv t)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hxc : ~ In x (context_fv C)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
    rewrite (subst_env_identity_off t rho x Hrho Hxt), (IHC rho x Hrho Hxc). reflexivity.
  - rewrite (IHC rho x Hrho Hx). reflexivity.
  - rewrite (IHC rho x Hrho Hx). reflexivity.
  - rewrite (IHC rho x Hrho Hx). reflexivity.
  - rewrite (IHC rho x Hrho Hx). reflexivity.
  - assert (Hxc : ~ In x (context_fv C)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hx1 : ~ In x (fv t1)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hx2 : ~ In x (fv t2)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    rewrite (IHC rho x Hrho Hxc), (subst_env_identity_off t1 rho x Hrho Hx1),
            (subst_env_identity_off t2 rho x Hrho Hx2). reflexivity.
  - assert (Hxt : ~ In x (fv t)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hxc : ~ In x (context_fv C)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hx2 : ~ In x (fv t2)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    rewrite (subst_env_identity_off t rho x Hrho Hxt), (IHC rho x Hrho Hxc),
            (subst_env_identity_off t2 rho x Hrho Hx2). reflexivity.
  - assert (Hx1 : ~ In x (fv t1)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hx2 : ~ In x (fv t2)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hxc : ~ In x (context_fv C)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    rewrite (subst_env_identity_off t1 rho x Hrho Hx1), (subst_env_identity_off t2 rho x Hrho Hx2),
            (IHC rho x Hrho Hxc). reflexivity.
  - rewrite (IHC rho x Hrho Hx). reflexivity.
  - assert (Hxc : ~ In x (context_fv C)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hx1 : ~ In x (fv y)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hx2 : ~ In x (fv n)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    rewrite (IHC rho x Hrho Hxc), (subst_env_identity_off y rho x Hrho Hx1),
            (subst_env_identity_off n rho x Hrho Hx2). reflexivity.
  - assert (Hxt : ~ In x (fv c)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hxc : ~ In x (context_fv C)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hx2 : ~ In x (fv n)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    rewrite (subst_env_identity_off c rho x Hrho Hxt), (IHC rho x Hrho Hxc),
            (subst_env_identity_off n rho x Hrho Hx2). reflexivity.
  - assert (Hx1 : ~ In x (fv c)) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
    assert (Hx2 : ~ In x (fv y)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hc).
    assert (Hxc : ~ In x (context_fv C)) by (intro Hc; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hc).
    rewrite (subst_env_identity_off c rho x Hrho Hx1), (subst_env_identity_off y rho x Hrho Hx2),
            (IHC rho x Hrho Hxc). reflexivity.
Qed.

(* ================================================================== *)
(* Inversion lemmas for the value relation                             *)
(* ================================================================== *)

Lemma value_rel_sum_inv : forall T1 T2 kappa v1 v2,
  is_low kappa.(indirect_reader) = true ->
  value_rel (Ty_Sum T1 T2 kappa) v1 v2 ->
  ((exists (a1 a2 : tm) (k1 k2 : security),
      v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\ value_rel T1 a1 a2) \/
   (exists (a1 a2 : tm) (k1 k2 : security),
      v1 = tm_inr a1 k1 /\ v2 = tm_inr a2 k2 /\ value_rel T2 a1 a2)).
Proof.
  intros T1 T2 kappa v1 v2 Hlow Hrel.
  simpl in Hrel. rewrite Hlow in Hrel. simpl in Hrel.
  destruct Hrel as [_ [_ [_ [_ Hst]]]]. exact Hst.
Qed.

Lemma value_rel_sum_inl : forall T1 T2 kappa a1 a2 k1 k2,
  is_low kappa.(indirect_reader) = true ->
  value_rel (Ty_Sum T1 T2 kappa) (tm_inl a1 k1) (tm_inl a2 k2) ->
  value_rel T1 a1 a2.
Proof.
  intros T1 T2 kappa a1 a2 k1 k2 Hlow Hrel.
  destruct (value_rel_sum_inv _ _ _ _ _ Hlow Hrel)
    as [(x1 & x2 & kx1 & kx2 & E1 & E2 & Hc) | (x1 & x2 & kx1 & kx2 & E1 & E2 & Hc)].
  - injection E1 as E1a E1b. injection E2 as E2a E2b. subst. exact Hc.
  - discriminate E1.
Qed.

Lemma value_rel_sum_inr : forall T1 T2 kappa a1 a2 k1 k2,
  is_low kappa.(indirect_reader) = true ->
  value_rel (Ty_Sum T1 T2 kappa) (tm_inr a1 k1) (tm_inr a2 k2) ->
  value_rel T2 a1 a2.
Proof.
  intros T1 T2 kappa a1 a2 k1 k2 Hlow Hrel.
  destruct (value_rel_sum_inv _ _ _ _ _ Hlow Hrel)
    as [(x1 & x2 & kx1 & kx2 & E1 & E2 & Hc) | (x1 & x2 & kx1 & kx2 & E1 & E2 & Hc)].
  - discriminate E1.
  - injection E1 as E1a E1b. injection E2 as E2a E2b. subst. exact Hc.
Qed.

Lemma value_rel_sum_inl_inr : forall T1 T2 kappa (a1 a2 : tm) (k1 k2 : security),
  is_low kappa.(indirect_reader) = true ->
  value_rel (Ty_Sum T1 T2 kappa) (tm_inl a1 k1) (tm_inr a2 k2) -> False.
Proof.
  intros T1 T2 kappa a1 a2 k1 k2 Hlow Hrel.
  destruct (value_rel_sum_inv _ _ _ _ _ Hlow Hrel)
    as [(x1 & x2 & kx1 & kx2 & E1 & E2 & Hc) | (x1 & x2 & kx1 & kx2 & E1 & E2 & Hc)].
  - discriminate E2.
  - discriminate E1.
Qed.

Lemma value_rel_sum_inr_inl : forall T1 T2 kappa (a1 a2 : tm) (k1 k2 : security),
  is_low kappa.(indirect_reader) = true ->
  value_rel (Ty_Sum T1 T2 kappa) (tm_inr a1 k1) (tm_inl a2 k2) -> False.
Proof.
  intros T1 T2 kappa a1 a2 k1 k2 Hlow Hrel.
  destruct (value_rel_sum_inv _ _ _ _ _ Hlow Hrel)
    as [(x1 & x2 & kx1 & kx2 & E1 & E2 & Hc) | (x1 & x2 & kx1 & kx2 & E1 & E2 & Hc)].
  - discriminate E1.
  - discriminate E2.
Qed.

Lemma value_rel_prod_inv : forall T1 T2 kappa v1 v2,
  is_low kappa.(indirect_reader) = true ->
  value_rel (Ty_Prod T1 T2 kappa) v1 v2 ->
  exists (a1 a2 b1 b2 : tm) (k1 k2 : security),
    v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
    value_rel T1 a1 a2 /\ value_rel T2 b1 b2.
Proof.
  intros T1 T2 kappa v1 v2 Hlow Hrel.
  simpl in Hrel. rewrite Hlow in Hrel. simpl in Hrel.
  destruct Hrel as [_ [_ [_ [_ Hst]]]]. exact Hst.
Qed.

Lemma value_rel_prod_fst : forall T1 T2 kappa (a1 b1 : tm) (k1 : security) (a2 b2 : tm) (k2 : security),
  is_low kappa.(indirect_reader) = true ->
  value_rel (Ty_Prod T1 T2 kappa) (tm_pair a1 b1 k1) (tm_pair a2 b2 k2) ->
  value_rel T1 a1 a2.
Proof.
  intros T1 T2 kappa a1 b1 k1 a2 b2 k2 Hlow Hrel.
  destruct (value_rel_prod_inv _ _ _ _ _ Hlow Hrel) as (x1 & x2 & y1 & y2 & kx & ky & E1 & E2 & Hc1 & Hc2).
  injection E1 as E1a E1b E1c. injection E2 as E2a E2b E2c. subst. exact Hc1.
Qed.

Lemma value_rel_prod_snd : forall T1 T2 kappa (a1 b1 : tm) (k1 : security) (a2 b2 : tm) (k2 : security),
  is_low kappa.(indirect_reader) = true ->
  value_rel (Ty_Prod T1 T2 kappa) (tm_pair a1 b1 k1) (tm_pair a2 b2 k2) ->
  value_rel T2 b1 b2.
Proof.
  intros T1 T2 kappa a1 b1 k1 a2 b2 k2 Hlow Hrel.
  destruct (value_rel_prod_inv _ _ _ _ _ Hlow Hrel) as (x1 & x2 & y1 & y2 & kx & ky & E1 & E2 & Hc1 & Hc2).
  injection E1 as E1a E1b E1c. injection E2 as E2a E2b E2c. subst. exact Hc2.
Qed.

Lemma value_rel_prod_bound1 : forall T1 T2 kappa (a1 b1 : tm) (k1 : security) (a2 b2 : tm) (k2 : security),
  value_rel (Ty_Prod T1 T2 kappa) (tm_pair a1 b1 k1) (tm_pair a2 b2 k2) ->
  flows_to k1.(indirect_reader) kappa.(indirect_reader).
Proof.
  intros. pose proof (value_rel_b1 _ _ _ H) as Hb. simpl in Hb. exact Hb.
Qed.

Lemma value_rel_prod_bound2 : forall T1 T2 kappa (a1 b1 : tm) (k1 : security) (a2 b2 : tm) (k2 : security),
  value_rel (Ty_Prod T1 T2 kappa) (tm_pair a1 b1 k1) (tm_pair a2 b2 k2) ->
  flows_to k2.(indirect_reader) kappa.(indirect_reader).
Proof.
  intros. pose proof (value_rel_b2 _ _ _ H) as Hb. simpl in Hb. exact Hb.
Qed.

Lemma value_rel_arrow_inv : forall T1 T2 kappa v1 v2,
  is_low kappa.(indirect_reader) = true ->
  value_rel (Ty_Arrow T1 T2 kappa) v1 v2 ->
  forall u1 u2 r, value_rel T1 u1 u2 -> flows_to kappa.(reader) r ->
    forall w1 w2, evaluates (tm_app v1 u1 r) w1 -> evaluates (tm_app v2 u2 r) w2 ->
    value_rel T2 w1 w2.
Proof.
  intros T1 T2 kappa v1 v2 Hlow Hrel.
  simpl in Hrel. rewrite Hlow in Hrel. simpl in Hrel.
  destruct Hrel as [_ [_ [_ [_ Hst]]]].
  intros u1 u2 r Hu Hr w1 w2 He1 He2.
  exact (Hst u1 u2 r Hu Hr w1 w2 He1 He2).
Qed.

Lemma evaluates_protect_low : forall k t w,
  k.(indirect_reader) = Low ->
  multi (tm_protect k.(indirect_reader) t) w -> value w -> evaluates t w.
Proof.
  intros k t w Hk Hm Hw. rewrite Hk in Hm.
  edestruct (multi_protect_inv Low t w Hm Hw) as (u & Htu & Hu & Ew).
  rewrite protect_value_low in Ew by exact Hu. subst w.
  split; assumption.
Qed.

Lemma ind_bound_low : forall k1 kappa,
  flows_to k1.(indirect_reader) kappa.(indirect_reader) ->
  kappa.(indirect_reader) = Low -> k1.(indirect_reader) = Low.
Proof.
  intros k1 kappa H Hl. rewrite Hl in H. apply flows_to_low_iff; exact H.
Qed.

Lemma lookup_update_same : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof.
  intros Gamma x T; simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_update_neq : forall Gamma x y T,
  x <> y -> lookup_context x (update Gamma y T) = lookup_context x Gamma.
Proof.
  intros Gamma x y T H; simpl.
  destruct (Nat.eqb x y) eqn:E; [| reflexivity].
  apply Nat.eqb_eq in E. exfalso; exact (H E).
Qed.

Lemma multi_app_abs_inv : forall T body k u r w,
  value (tm_abs T body k) -> value u -> flows_to k.(reader) r ->
  multi (tm_app (tm_abs T body k) u r) w -> value w ->
  multi (tm_protect k.(indirect_reader) (open body u)) w.
Proof.
  intros T body k u r w Hv Hu Hf Hm Hval.
  remember (tm_app (tm_abs T body k) u r) as a eqn:E.
  induction Hm; subst.
  - inversion Hval.
  - inversion H; subst.
    + assumption.
    + exfalso. exact (abs_no_step T body k t1' H4).
    + exfalso. exact (value_no_step u Hu t2' H5).
Qed.

(* ================================================================== *)
(* Environment relation                                                *)
(* ================================================================== *)

Definition env_rel (Gamma : context) (rho1 rho2 : atom -> tm) : Prop :=
  range_lc rho1 /\ range_lc rho2 /\
  forall x T, lookup_context x Gamma = Some T -> term_rel T (rho1 x) (rho2 x).

Lemma env_rel_extend : forall Gamma rho1 rho2 x T v1 v2,
  env_rel Gamma rho1 rho2 ->
  value v1 -> value v2 -> value_rel T v1 v2 ->
  env_rel (update Gamma x T) (extend_env rho1 x v1) (extend_env rho2 x v2).
Proof.
  intros Gamma rho1 rho2 x T v1 v2 [Hr1 [Hr2 Hlk]] Hv1 Hv2 Hrel.
  unfold env_rel. repeat split.
  - apply range_lc_extend; [exact Hr1 | apply value_lc; exact Hv1].
  - apply range_lc_extend; [exact Hr2 | apply value_lc; exact Hv2].
  - intros y U Hlu. destruct (Nat.eqb y x) eqn:Eyx.
    + apply Nat.eqb_eq in Eyx; subst y.
      rewrite lookup_update_same in Hlu. injection Hlu as <-.
      rewrite extend_env_eq, extend_env_eq. apply term_rel_of_value_rel; exact Hrel.
    + assert (Hyx : y <> x) by (intro Hc; apply Nat.eqb_neq in Eyx; exact (Eyx Hc)).
      rewrite lookup_update_neq in Hlu by exact Hyx.
      rewrite extend_env_neq by exact Hyx.
      rewrite extend_env_neq by exact Hyx.
      apply Hlk; exact Hlu.
Qed.

(* ================================================================== *)
(* The fundamental theorem of the logical relation                     *)
(* ================================================================== *)

Lemma fundamental : forall Gamma t T, has_type Gamma t T ->
  forall rho1 rho2, env_rel Gamma rho1 rho2 ->
  term_rel T (subst_env rho1 t) (subst_env rho2 t).
Proof.
  intros Gamma t T H.
  induction H; intros rho1 rho2 Henv.
  - (* T_Var *)
    simpl. exact (proj2 (proj2 Henv) x T H).
  - (* T_Unit *)
    simpl. unfold term_rel. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    apply multi_unit_inv in Hm1. apply multi_unit_inv in Hm2. subst.
    simpl. repeat split; auto using flows_to_refl.
    destruct (is_low kappa.(indirect_reader)) eqn:E; [exists kappa, kappa | exact I]; auto.
  - (* T_Abs *)
    simpl.
    unfold term_rel. intros v1 v2 He1 He2.
    destruct He1 as [Hm1 Hval1]; destruct He2 as [Hm2 Hval2].
    apply multi_abs_inv in Hm1. apply multi_abs_inv in Hm2. subst.
    assert (Hr1 : range_lc rho1) by (exact (proj1 Henv)).
    assert (Hr2 : range_lc rho2) by (exact (proj1 (proj2 Henv))).
    destruct (is_low kappa.(indirect_reader)) eqn:E.
    + (* gate open *)
      assert (Hlow : kappa.(indirect_reader) = Low) by (apply is_low_true; exact E).
      simpl. rewrite Hlow. simpl. repeat split; auto using flows_to_refl.
      intros u1 u2 r Hu Hr w1 w2 Ha1 Ha2.
      destruct (fresh_atom (L ++ fv body)) as [x Hx].
      assert (HxL : ~ In x L) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
      assert (Hxf : ~ In x (fv body)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
      pose proof (value_rel_v1 _ _ _ Hu) as Hvu1.
      pose proof (value_rel_v2 _ _ _ Hu) as Hvu2.
      assert (Hm1' : multi (tm_protect kappa.(indirect_reader) (open (subst_env rho1 body) u1)) w1).
      { eapply multi_app_abs_inv; [exact Hval1 | exact Hvu1 | exact Hr | apply (proj1 Ha1) | apply (proj2 Ha1)]. }
      assert (Hm2' : multi (tm_protect kappa.(indirect_reader) (open (subst_env rho2 body) u2)) w2).
      { eapply multi_app_abs_inv; [exact Hval2 | exact Hvu2 | exact Hr | apply (proj1 Ha2) | apply (proj2 Ha2)]. }
      edestruct (multi_protect_inv kappa.(indirect_reader) (open (subst_env rho1 body) u1) w1 Hm1' (proj2 Ha1))
        as (u1' & Hbody1 & Hu1' & Ew1).
      edestruct (multi_protect_inv kappa.(indirect_reader) (open (subst_env rho2 body) u2) w2 Hm2' (proj2 Ha2))
        as (u2' & Hbody2 & Hu2' & Ew2).
      assert (Ew1' : w1 = u1').
      { rewrite Ew1. rewrite Hlow. apply protect_value_low; exact Hu1'. }
      assert (Ew2' : w2 = u2').
      { rewrite Ew2. rewrite Hlow. apply protect_value_low; exact Hu2'. }
      rewrite Ew1', Ew2'.
      assert (Henv' : env_rel (update Gamma x T1) (extend_env rho1 x u1) (extend_env rho2 x u2))
        by (eapply env_rel_extend; eauto).
      pose proof (H2 x HxL _ _ Henv') as Hbodyrel.
      rewrite (subst_env_open rho1 x u1 body Hr1 Hxf) in Hbodyrel.
      rewrite (subst_env_open rho2 x u2 body Hr2 Hxf) in Hbodyrel.
      unfold term_rel in Hbodyrel.
      apply Hbodyrel; [apply (conj Hbody1 Hu1') | apply (conj Hbody2 Hu2')].
    + (* gate closed *)
      assert (Hhigh : kappa.(indirect_reader) = High) by (apply is_low_false; exact E).
      apply value_rel_high_ind.
      * simpl. exact Hhigh.
      * exact Hval1.
      * exact Hval2.
  - (* T_App *)
    simpl.
    destruct (is_low kappa.(indirect_reader)) eqn:E.
    + assert (Hlow : kappa.(indirect_reader) = Low) by (apply is_low_true; exact E).
      rewrite Hlow. rewrite ty_protect_low.
      unfold term_rel. intros w1 w2 He1 He2.
      destruct He1 as [Hm1 Hval1]; destruct He2 as [Hm2 Hval2].
      destruct (multi_app_inv _ _ _ _ Hm1 Hval1) as (Ta & ba & ka & va & Ha1 & Hva1 & Hb1 & Hvb1 & Hf1 & Hres1).
      destruct (multi_app_inv _ _ _ _ Hm2 Hval2) as (Tb & bb & kb & vb & Ha2 & Hva2 & Hb2 & Hvb2 & Hf2 & Hres2).
      pose proof (IHhas_type1 rho1 rho2 Henv (tm_abs Ta ba ka) (tm_abs Tb bb kb)
                    (conj Ha1 Hva1) (conj Ha2 Hva2)) as Harrow.
      pose proof (IHhas_type2 rho1 rho2 Henv va vb (conj Hb1 Hvb1) (conj Hb2 Hvb2)) as Harg.
      simpl in Harrow. rewrite Hlow in Harrow. simpl in Harrow.
      destruct Harrow as [_ [_ [_ [_ Hclause]]]].
      apply (Hclause va vb r Harg H1).
      * apply (conj (multi_step (tm_app (tm_abs Ta ba ka) va r)
                          (tm_protect ka.(indirect_reader) (open ba va)) w1
                          (ST_AppAbs Ta ba ka va r Hva1 Hvb1 Hf1) Hres1) Hval1).
      * apply (conj (multi_step (tm_app (tm_abs Tb bb kb) vb r)
                          (tm_protect kb.(indirect_reader) (open bb vb)) w2
                          (ST_AppAbs Tb bb kb vb r Hva2 Hvb2 Hf2) Hres2) Hval2).
    + assert (Hhigh : kappa.(indirect_reader) = High) by (apply is_low_false; exact E).
      unfold term_rel. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
      apply value_rel_high_ind.
      * rewrite security_of_ty_protect, protect_security_ind, Hhigh, join_high. reflexivity.
      * exact Hv1.
      * exact Hv2.
  - (* T_Pair *)
    simpl. unfold term_rel. intros v1 v2 He1 He2.
    destruct He1 as [Hm1 Hval1]; destruct He2 as [Hm2 Hval2].
    destruct (multi_pair_inv _ _ _ _ Hm1 Hval1) as (a1 & b1 & Ha1 & Hva1 & Hb1 & Hvb1 & E1).
    destruct (multi_pair_inv _ _ _ _ Hm2 Hval2) as (a2 & b2 & Ha2 & Hva2 & Hb2 & Hvb2 & E2).
    subst v1 v2.
    pose proof (IHhas_type1 rho1 rho2 Henv a1 a2 (conj Ha1 Hva1) (conj Ha2 Hva2)) as Hra.
    pose proof (IHhas_type2 rho1 rho2 Henv b1 b2 (conj Hb1 Hvb1) (conj Hb2 Hvb2)) as Hrb.
    simpl. repeat split.
    + apply v_pair; [apply value_rel_v1 in Hra | apply value_rel_v1 in Hrb]; assumption.
    + apply v_pair; [apply value_rel_v2 in Hra | apply value_rel_v2 in Hrb]; assumption.
    + apply flows_to_refl.
    + apply flows_to_refl.
    + destruct (is_low kappa.(indirect_reader)) eqn:E.
      * exists a1, a2, b1, b2, kappa, kappa. repeat split; try reflexivity; assumption.
      * exact I.
  - (* T_Fst *)
    simpl.
    destruct (is_low kappa.(indirect_reader)) eqn:E.
    + assert (Hlow : kappa.(indirect_reader) = Low) by (apply is_low_true; exact E).
      rewrite Hlow. rewrite ty_protect_low.
      unfold term_rel. intros w1 w2 He1 He2.
      destruct He1 as [Hm1 Hval1]; destruct He2 as [Hm2 Hval2].
      destruct (multi_fst_inv _ _ _ Hm1 Hval1) as (a1 & b1 & k1 & Ht1 & Hva1 & Hvb1 & Hf1 & Hres1).
      destruct (multi_fst_inv _ _ _ Hm2 Hval2) as (a2 & b2 & k2 & Ht2 & Hva2 & Hvb2 & Hf2 & Hres2).
      pose proof (IHhas_type rho1 rho2 Henv (tm_pair a1 b1 k1) (tm_pair a2 b2 k2)
                    (conj Ht1 (v_pair a1 b1 k1 Hva1 Hvb1))
                    (conj Ht2 (v_pair a2 b2 k2 Hva2 Hvb2))) as Hpair.
      pose proof (value_rel_prod_fst _ _ _ _ _ _ _ _ _ E Hpair) as Hcx.
      assert (Hk1 : k1.(indirect_reader) = Low).
      { exact (ind_bound_low k1 kappa (value_rel_prod_bound1 _ _ _ _ _ _ _ _ _ Hpair) Hlow). }
      assert (Hk2 : k2.(indirect_reader) = Low).
      { exact (ind_bound_low k2 kappa (value_rel_prod_bound2 _ _ _ _ _ _ _ _ _ Hpair) Hlow). }
      pose proof (evaluates_protect_low k1 a1 w1 Hk1 Hres1 Hval1) as Hev1.
      pose proof (evaluates_protect_low k2 a2 w2 Hk2 Hres2 Hval2) as Hev2.
      exact (term_rel_of_value_rel T1 a1 a2 Hcx w1 w2 Hev1 Hev2).
    + assert (Hhigh : kappa.(indirect_reader) = High) by (apply is_low_false; exact E).
      unfold term_rel. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
      apply value_rel_high_ind.
      * rewrite security_of_ty_protect, protect_security_ind, Hhigh, join_high. reflexivity.
      * exact Hv1.
      * exact Hv2.
  - (* T_Snd *)
    simpl.
    destruct (is_low kappa.(indirect_reader)) eqn:E.
    + assert (Hlow : kappa.(indirect_reader) = Low) by (apply is_low_true; exact E).
      rewrite Hlow. rewrite ty_protect_low.
      unfold term_rel. intros w1 w2 He1 He2.
      destruct He1 as [Hm1 Hval1]; destruct He2 as [Hm2 Hval2].
      destruct (multi_snd_inv _ _ _ Hm1 Hval1) as (a1 & b1 & k1 & Ht1 & Hva1 & Hvb1 & Hf1 & Hres1).
      destruct (multi_snd_inv _ _ _ Hm2 Hval2) as (a2 & b2 & k2 & Ht2 & Hva2 & Hvb2 & Hf2 & Hres2).
      pose proof (IHhas_type rho1 rho2 Henv (tm_pair a1 b1 k1) (tm_pair a2 b2 k2)
                    (conj Ht1 (v_pair a1 b1 k1 Hva1 Hvb1))
                    (conj Ht2 (v_pair a2 b2 k2 Hva2 Hvb2))) as Hpair.
      pose proof (value_rel_prod_snd _ _ _ _ _ _ _ _ _ E Hpair) as Hcy.
      assert (Hk1 : k1.(indirect_reader) = Low).
      { exact (ind_bound_low k1 kappa (value_rel_prod_bound1 _ _ _ _ _ _ _ _ _ Hpair) Hlow). }
      assert (Hk2 : k2.(indirect_reader) = Low).
      { exact (ind_bound_low k2 kappa (value_rel_prod_bound2 _ _ _ _ _ _ _ _ _ Hpair) Hlow). }
      pose proof (evaluates_protect_low k1 b1 w1 Hk1 Hres1 Hval1) as Hev1.
      pose proof (evaluates_protect_low k2 b2 w2 Hk2 Hres2 Hval2) as Hev2.
      exact (term_rel_of_value_rel T2 b1 b2 Hcy w1 w2 Hev1 Hev2).
    + assert (Hhigh : kappa.(indirect_reader) = High) by (apply is_low_false; exact E).
      unfold term_rel. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
      apply value_rel_high_ind.
      * rewrite security_of_ty_protect, protect_security_ind, Hhigh, join_high. reflexivity.
      * exact Hv1.
      * exact Hv2.
  - (* T_Inl *)
    simpl. unfold term_rel. intros w1 w2 He1 He2.
    destruct He1 as [Hm1 Hval1]; destruct He2 as [Hm2 Hval2].
    destruct (multi_inl_inv _ _ _ Hm1 Hval1) as (a1 & Hm1' & Hva1 & E1).
    destruct (multi_inl_inv _ _ _ Hm2 Hval2) as (a2 & Hm2' & Hva2 & E2).
    subst w1 w2.
    pose proof (IHhas_type rho1 rho2 Henv a1 a2 (conj Hm1' Hva1) (conj Hm2' Hva2)) as Hca.
    simpl. repeat split.
    + apply v_inl. apply value_rel_v1 in Hca; exact Hca.
    + apply v_inl. apply value_rel_v2 in Hca; exact Hca.
    + apply flows_to_refl.
    + apply flows_to_refl.
    + destruct (is_low kappa.(indirect_reader)) eqn:E; [| exact I].
      left. exists a1, a2, kappa, kappa. repeat split; try reflexivity; exact Hca.
  - (* T_Inr *)
    simpl. unfold term_rel. intros w1 w2 He1 He2.
    destruct He1 as [Hm1 Hval1]; destruct He2 as [Hm2 Hval2].
    destruct (multi_inr_inv _ _ _ Hm1 Hval1) as (a1 & Hm1' & Hva1 & E1).
    destruct (multi_inr_inv _ _ _ Hm2 Hval2) as (a2 & Hm2' & Hva2 & E2).
    subst w1 w2.
    pose proof (IHhas_type rho1 rho2 Henv a1 a2 (conj Hm1' Hva1) (conj Hm2' Hva2)) as Hca.
    simpl. repeat split.
    + apply v_inr. apply value_rel_v1 in Hca; exact Hca.
    + apply v_inr. apply value_rel_v2 in Hca; exact Hca.
    + apply flows_to_refl.
    + apply flows_to_refl.
    + destruct (is_low kappa.(indirect_reader)) eqn:E; [| exact I].
      right. exists a1, a2, kappa, kappa. repeat split; try reflexivity; exact Hca.
  - (* T_Case *)
    simpl.
    destruct (is_low kappa.(indirect_reader)) eqn:E.
    + assert (Hlow : kappa.(indirect_reader) = Low) by (apply is_low_true; exact E).
      rewrite Hlow. rewrite ty_protect_low.
      unfold term_rel. intros w1 w2 He1 He2.
      destruct He1 as [Hm1 Hval1]; destruct He2 as [Hm2 Hval2].
      destruct (multi_case_inv _ _ _ _ _ Hm1 Hval1)
        as [(v1 & k1 & Hs1 & Hv1 & Hf1 & Hres1) | (v1 & k1 & Hs1 & Hv1 & Hf1 & Hres1)].
      * destruct (multi_case_inv _ _ _ _ _ Hm2 Hval2)
          as [(v2 & k2 & Hs2 & Hv2 & Hf2 & Hres2) | (v2 & k2 & Hs2 & Hv2 & Hf2 & Hres2)].
        -- (* inl / inl *)
           pose proof (IHhas_type rho1 rho2 Henv (tm_inl v1 k1) (tm_inl v2 k2)
                         (conj Hs1 (v_inl v1 k1 Hv1)) (conj Hs2 (v_inl v2 k2 Hv2))) as Hsum.
           pose proof (value_rel_sum_inl _ _ _ _ _ _ _ E Hsum) as Hc1.
           assert (Hk1 : k1.(indirect_reader) = Low).
           { pose proof (value_rel_b1 _ _ _ Hsum) as Hb. simpl in Hb. exact (ind_bound_low k1 kappa Hb Hlow). }
           assert (Hk2 : k2.(indirect_reader) = Low).
           { pose proof (value_rel_b2 _ _ _ Hsum) as Hb. simpl in Hb. exact (ind_bound_low k2 kappa Hb Hlow). }
           pose proof (evaluates_protect_low k1 (open (subst_env rho1 body1) v1) w1 Hk1 Hres1 Hval1) as Hev1.
           pose proof (evaluates_protect_low k2 (open (subst_env rho2 body1) v2) w2 Hk2 Hres2 Hval2) as Hev2.
           destruct (fresh_atom (L ++ fv body1)) as [x Hx].
           assert (HxL : ~ In x L) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
           assert (Hxf : ~ In x (fv body1)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
           assert (Henv' : env_rel (update Gamma x T1) (extend_env rho1 x v1) (extend_env rho2 x v2))
             by (eapply env_rel_extend; eauto).
           pose proof (H2 x HxL _ _ Henv') as Hbodyrel.
           rewrite (subst_env_open rho1 x v1 body1 (proj1 Henv) Hxf) in Hbodyrel.
           rewrite (subst_env_open rho2 x v2 body1 (proj1 (proj2 Henv)) Hxf) in Hbodyrel.
           unfold term_rel in Hbodyrel.
           exact (Hbodyrel w1 w2 Hev1 Hev2).
        -- (* inl / inr: contradiction *)
           pose proof (IHhas_type rho1 rho2 Henv (tm_inl v1 k1) (tm_inr v2 k2)
                         (conj Hs1 (v_inl v1 k1 Hv1)) (conj Hs2 (v_inr v2 k2 Hv2))) as Hsum.
           exfalso. exact (value_rel_sum_inl_inr _ _ _ _ _ _ _ E Hsum).
      * destruct (multi_case_inv _ _ _ _ _ Hm2 Hval2)
          as [(v2 & k2 & Hs2 & Hv2 & Hf2 & Hres2) | (v2 & k2 & Hs2 & Hv2 & Hf2 & Hres2)].
        -- (* inr / inl: contradiction *)
           pose proof (IHhas_type rho1 rho2 Henv (tm_inr v1 k1) (tm_inl v2 k2)
                         (conj Hs1 (v_inr v1 k1 Hv1)) (conj Hs2 (v_inl v2 k2 Hv2))) as Hsum.
           exfalso. exact (value_rel_sum_inr_inl _ _ _ _ _ _ _ E Hsum).
        -- (* inr / inr *)
           pose proof (IHhas_type rho1 rho2 Henv (tm_inr v1 k1) (tm_inr v2 k2)
                         (conj Hs1 (v_inr v1 k1 Hv1)) (conj Hs2 (v_inr v2 k2 Hv2))) as Hsum.
           pose proof (value_rel_sum_inr _ _ _ _ _ _ _ E Hsum) as Hc1.
           assert (Hk1 : k1.(indirect_reader) = Low).
           { pose proof (value_rel_b1 _ _ _ Hsum) as Hb. simpl in Hb. exact (ind_bound_low k1 kappa Hb Hlow). }
           assert (Hk2 : k2.(indirect_reader) = Low).
           { pose proof (value_rel_b2 _ _ _ Hsum) as Hb. simpl in Hb. exact (ind_bound_low k2 kappa Hb Hlow). }
           pose proof (evaluates_protect_low k1 (open (subst_env rho1 body2) v1) w1 Hk1 Hres1 Hval1) as Hev1.
           pose proof (evaluates_protect_low k2 (open (subst_env rho2 body2) v2) w2 Hk2 Hres2 Hval2) as Hev2.
           destruct (fresh_atom (L ++ fv body2)) as [x Hx].
           assert (HxL : ~ In x L) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
           assert (Hxf : ~ In x (fv body2)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
           assert (Henv' : env_rel (update Gamma x T2) (extend_env rho1 x v1) (extend_env rho2 x v2))
             by (eapply env_rel_extend; eauto).
           pose proof (H4 x HxL _ _ Henv') as Hbodyrel.
           rewrite (subst_env_open rho1 x v1 body2 (proj1 Henv) Hxf) in Hbodyrel.
           rewrite (subst_env_open rho2 x v2 body2 (proj1 (proj2 Henv)) Hxf) in Hbodyrel.
           unfold term_rel in Hbodyrel.
           exact (Hbodyrel w1 w2 Hev1 Hev2).
    + assert (Hhigh : kappa.(indirect_reader) = High) by (apply is_low_false; exact E).
      unfold term_rel. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
      apply value_rel_high_ind.
      * rewrite security_of_ty_protect, protect_security_ind, Hhigh, join_high. reflexivity.
      * exact Hv1.
      * exact Hv2.
  - (* T_Protect *)
    simpl. unfold term_rel. intros w1 w2 He1 He2.
    destruct He1 as [Hm1 Hval1]; destruct He2 as [Hm2 Hval2].
    destruct (multi_protect_inv _ _ _ Hm1 Hval1) as (u1 & Ht1 & Hu1 & E1).
    destruct (multi_protect_inv _ _ _ Hm2 Hval2) as (u2 & Ht2 & Hu2 & E2).
    pose proof (IHhas_type rho1 rho2 Henv u1 u2 (conj Ht1 Hu1) (conj Ht2 Hu2)) as Hrel.
    pose proof (value_rel_protect _ _ _ l Hrel) as Hp.
    rewrite E1, E2. exact Hp.
  - (* T_Sub *)
    simpl. eapply term_rel_subtype; [exact H0 | exact (IHhas_type rho1 rho2 Henv)].
  - (* T_If *)
    simpl.
    destruct (is_low k.(indirect_reader)) eqn:E.
    + assert (Hlow : k.(indirect_reader) = Low) by (apply is_low_true; exact E).
      rewrite Hlow. rewrite ty_protect_low.
      unfold term_rel. intros w1 w2 He1 He2.
      destruct He1 as [Hm1 Hval1]; destruct He2 as [Hm2 Hval2].
      destruct (multi_if_inv _ _ _ _ _ Hm1 Hval1)
        as [(v1 & k1 & Hc1 & Hv1 & Hf1 & Hres1) | (v1 & k1 & Hc1 & Hv1 & Hf1 & Hres1)].
      * destruct (multi_if_inv _ _ _ _ _ Hm2 Hval2)
          as [(v2 & k2 & Hc2 & Hv2 & Hf2 & Hres2) | (v2 & k2 & Hc2 & Hv2 & Hf2 & Hres2)].
        -- pose proof (IHhas_type1 rho1 rho2 Henv (tm_inl v1 k1) (tm_inl v2 k2)
                         (conj Hc1 (v_inl v1 k1 Hv1)) (conj Hc2 (v_inl v2 k2 Hv2))) as Hsum.
           assert (Hk1 : k1.(indirect_reader) = Low).
           { pose proof (value_rel_b1 _ _ _ Hsum) as Hb. simpl in Hb. exact (ind_bound_low k1 k Hb Hlow). }
           assert (Hk2 : k2.(indirect_reader) = Low).
           { pose proof (value_rel_b2 _ _ _ Hsum) as Hb. simpl in Hb. exact (ind_bound_low k2 k Hb Hlow). }
           pose proof (evaluates_protect_low k1 (subst_env rho1 yes) w1 Hk1 Hres1 Hval1) as Hev1.
           pose proof (evaluates_protect_low k2 (subst_env rho2 yes) w2 Hk2 Hres2 Hval2) as Hev2.
           exact (IHhas_type2 rho1 rho2 Henv w1 w2 Hev1 Hev2).
        -- pose proof (IHhas_type1 rho1 rho2 Henv (tm_inl v1 k1) (tm_inr v2 k2)
                         (conj Hc1 (v_inl v1 k1 Hv1)) (conj Hc2 (v_inr v2 k2 Hv2))) as Hsum.
           exfalso. exact (value_rel_sum_inl_inr _ _ _ _ _ _ _ E Hsum).
      * destruct (multi_if_inv _ _ _ _ _ Hm2 Hval2)
          as [(v2 & k2 & Hc2 & Hv2 & Hf2 & Hres2) | (v2 & k2 & Hc2 & Hv2 & Hf2 & Hres2)].
        -- pose proof (IHhas_type1 rho1 rho2 Henv (tm_inr v1 k1) (tm_inl v2 k2)
                         (conj Hc1 (v_inr v1 k1 Hv1)) (conj Hc2 (v_inl v2 k2 Hv2))) as Hsum.
           exfalso. exact (value_rel_sum_inr_inl _ _ _ _ _ _ _ E Hsum).
        -- pose proof (IHhas_type1 rho1 rho2 Henv (tm_inr v1 k1) (tm_inr v2 k2)
                         (conj Hc1 (v_inr v1 k1 Hv1)) (conj Hc2 (v_inr v2 k2 Hv2))) as Hsum.
           assert (Hk1 : k1.(indirect_reader) = Low).
           { pose proof (value_rel_b1 _ _ _ Hsum) as Hb. simpl in Hb. exact (ind_bound_low k1 k Hb Hlow). }
           assert (Hk2 : k2.(indirect_reader) = Low).
           { pose proof (value_rel_b2 _ _ _ Hsum) as Hb. simpl in Hb. exact (ind_bound_low k2 k Hb Hlow). }
           pose proof (evaluates_protect_low k1 (subst_env rho1 no) w1 Hk1 Hres1 Hval1) as Hev1.
           pose proof (evaluates_protect_low k2 (subst_env rho2 no) w2 Hk2 Hres2 Hval2) as Hev2.
           exact (IHhas_type3 rho1 rho2 Henv w1 w2 Hev1 Hev2).
    + assert (Hhigh : k.(indirect_reader) = High) by (apply is_low_false; exact E).
      unfold term_rel. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
      apply value_rel_high_ind.
      * rewrite security_of_ty_protect, protect_security_ind, Hhigh, join_high. reflexivity.
      * exact Hv1.
      * exact Hv2.
Qed.

(* ================================================================== *)
(* Observable results of ground transparent types                      *)
(* ================================================================== *)

Lemma value_rel_erase : forall T v1 v2 κ,
  ground T -> transparent_at κ T -> flows_to κ.(indirect_reader) Low ->
  value_rel T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  intros T; induction T as [κ0 | T1 IHT1 T2 IHT2 κ0 | T1 IHT1 T2 IHT2 κ0 | T1 IHT1 T2 IHT2 κ0];
  intros v1 v2 κ Hground Htrans Hflow Hrel.
  - (* Ty_Unit *)
    simpl in Hground, Htrans.
    destruct Htrans as [Hle _].
    pose proof (security_le_ind _ _ Hle) as Hleind.
    assert (Hind : κ0.(indirect_reader) = Low)
      by (exact (ind_bound_low κ0 κ Hleind (proj1 (flows_to_low_iff _) Hflow))).
    assert (His : is_low κ0.(indirect_reader) = true)
      by (apply flows_low_is_low; rewrite Hind; exact I).
    simpl in Hrel. rewrite His in Hrel. simpl in Hrel.
    destruct Hrel as [_ [_ [_ [_ Hst]]]].
    destruct Hst as [k1 [k2 [E1 E2]]]. subst v1 v2. reflexivity.
  - (* Ty_Sum *)
    simpl in Hground, Htrans.
    destruct Hground as [Hg1 Hg2].
    destruct Htrans as [Hle [Htr1 Htr2]].
    pose proof (security_le_ind _ _ Hle) as Hleind.
    assert (Hind : κ0.(indirect_reader) = Low)
      by (exact (ind_bound_low κ0 κ Hleind (proj1 (flows_to_low_iff _) Hflow))).
    assert (His : is_low κ0.(indirect_reader) = true)
      by (apply flows_low_is_low; rewrite Hind; exact I).
    simpl in Hrel. rewrite His in Hrel. simpl in Hrel.
    destruct Hrel as [_ [_ [_ [_ Hst]]]].
    destruct Hst as [(a1 & a2 & k1 & k2 & E1 & E2 & Hca) | (a1 & a2 & k1 & k2 & E1 & E2 & Hca)].
    + subst v1 v2. simpl. rewrite (IHT1 a1 a2 κ Hg1 Htr1 Hflow Hca). reflexivity.
    + subst v1 v2. simpl. rewrite (IHT2 a1 a2 κ Hg2 Htr2 Hflow Hca). reflexivity.
  - (* Ty_Prod *)
    simpl in Hground, Htrans.
    destruct Hground as [Hg1 Hg2].
    destruct Htrans as [Hle [Htr1 Htr2]].
    pose proof (security_le_ind _ _ Hle) as Hleind.
    assert (Hind : κ0.(indirect_reader) = Low)
      by (exact (ind_bound_low κ0 κ Hleind (proj1 (flows_to_low_iff _) Hflow))).
    assert (His : is_low κ0.(indirect_reader) = true)
      by (apply flows_low_is_low; rewrite Hind; exact I).
    simpl in Hrel. rewrite His in Hrel. simpl in Hrel.
    destruct Hrel as [_ [_ [_ [_ Hst]]]].
    destruct Hst as (a1 & a2 & b1 & b2 & k1 & k2 & E1 & E2 & Hca & Hcb).
    subst v1 v2. simpl.
    rewrite (IHT1 a1 a2 κ Hg1 Htr1 Hflow Hca), (IHT2 b1 b2 κ Hg2 Htr2 Hflow Hcb).
    reflexivity.
  - (* Ty_Arrow *)
    simpl in Hground. destruct Hground.
Qed.

(* ================================================================== *)
(* Noninterference                                                     *)
(* ================================================================== *)

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
  intros C t1 t2 T_secret T_result Ht1 Ht2 [L HC] Hground Htrans Hnflow.
  (* the troublesome levels *)
  assert (Hres : (security_of T_result).(indirect_reader) = Low).
  { destruct ((security_of T_result).(indirect_reader)) eqn:E; auto.
    exfalso. apply Hnflow.
    destruct ((security_of T_secret).(indirect_reader)); simpl; exact I. }
  assert (Hsec : (security_of T_secret).(indirect_reader) = High).
  { destruct ((security_of T_secret).(indirect_reader)) eqn:E; [| reflexivity].
    exfalso. apply Hnflow. rewrite Hres. simpl. exact I. }
  (* any two closed terms of the secret type are related *)
  assert (Hrel_secret : term_rel T_secret t1 t2).
  { apply term_rel_opaque. rewrite Hsec. exact flows_to_high_low_false. }
  (* a fresh atom for the hole *)
  destruct (fresh_atom (L ++ context_fv C)) as [x Hx].
  assert (HxL : ~ In x L) by (intro Hc; apply Hx; apply in_or_app; left; exact Hc).
  assert (HxC : ~ In x (context_fv C)) by (intro Hc; apply Hx; apply in_or_app; right; exact Hc).
  (* the two environments *)
  pose (rho1 := extend_env (fun y => tm_fvar y) x t1).
  pose (rho2 := extend_env (fun y => tm_fvar y) x t2).
  assert (Hr1 : range_lc rho1).
  { intro y. unfold rho1, extend_env. destruct (Nat.eqb y x) eqn:E.
    - exact (has_type_lc _ _ _ Ht1).
    - unfold locally_closed. simpl. exact I. }
  assert (Hr2 : range_lc rho2).
  { intro y. unfold rho2, extend_env. destruct (Nat.eqb y x) eqn:E.
    - exact (has_type_lc _ _ _ Ht2).
    - unfold locally_closed. simpl. exact I. }
  assert (Henv : env_rel (update empty x T_secret) rho1 rho2).
  { unfold env_rel. repeat split.
    - exact Hr1.
    - exact Hr2.
    - intros y T Hlu. destruct (Nat.eqb y x) eqn:E.
      + apply Nat.eqb_eq in E; subst y.
        rewrite lookup_update_same in Hlu. injection Hlu as <-.
        unfold rho1, rho2. rewrite extend_env_eq, extend_env_eq. exact Hrel_secret.
      + assert (Hyx : y <> x) by (intro Hc; apply Nat.eqb_neq in E; exact (E Hc)).
        rewrite lookup_update_neq in Hlu by exact Hyx.
        simpl in Hlu. discriminate Hlu. }
  (* the fundamental theorem *)
  pose proof (fundamental (update empty x T_secret) (plug C (tm_fvar x)) T_result
                (HC x HxL) rho1 rho2 Henv) as Hctx.
  assert (Hid1 : forall y, y <> x -> rho1 y = tm_fvar y).
  { intros y Hy. unfold rho1. rewrite extend_env_neq by exact Hy. reflexivity. }
  assert (Hid2 : forall y, y <> x -> rho2 y = tm_fvar y).
  { intros y Hy. unfold rho2. rewrite extend_env_neq by exact Hy. reflexivity. }
  rewrite (subst_env_plug_fresh C rho1 x Hid1 HxC) in Hctx.
  rewrite (subst_env_plug_fresh C rho2 x Hid2 HxC) in Hctx.
  assert (E1 : rho1 x = t1) by (unfold rho1; apply extend_env_eq).
  assert (E2 : rho2 x = t2) by (unfold rho2; apply extend_env_eq).
  rewrite E1, E2 in Hctx.
  (* conclude *)
  unfold same_result. intros v1 v2 He1 He2.
  apply (value_rel_erase T_result v1 v2 (security_of T_result) Hground Htrans).
  - rewrite Hres. simpl. exact I.
  - exact (Hctx v1 v2 He1 He2).
Qed.
