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

(* ================================================================ *)
(* Auxiliary lemmas about labels, joins and security annotations.    *)
(* ================================================================ *)

Lemma flows_to_refl : forall l : label, flows_to l l.
Proof. destruct l; simpl; auto. Qed.

Lemma flows_to_trans : forall a b c : label,
    flows_to a b -> flows_to b c -> flows_to a c.
Proof. destruct a, b, c; simpl; auto. Qed.

Lemma flows_to_join_l : forall a b : label, flows_to a (join a b).
Proof. destruct a, b; simpl; auto. Qed.

Lemma flows_to_join_r : forall a b : label, flows_to b (join a b).
Proof. destruct a, b; simpl; auto. Qed.

Lemma flows_to_join_iff : forall a b c : label,
    flows_to (join a b) c <-> flows_to a c /\ flows_to b c.
Proof. destruct a, b, c; simpl; tauto. Qed.

Lemma join_low_r : forall a : label, join a Low = a.
Proof. destruct a; reflexivity. Qed.

Lemma join_high_r : forall a : label, join a High = High.
Proof. destruct a; reflexivity. Qed.

Lemma security_le_refl : forall κ : security, security_le κ κ.
Proof. intros [r i]; simpl; split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall a b c : security,
    security_le a b -> security_le b c -> security_le a c.
Proof.
  intros [ra ia] [rb ib] [rc ic]; simpl; intros [h1 h2] [h3 h4]; split;
    eapply flows_to_trans; eauto.
Qed.

Lemma protect_security_low : forall κ : security, protect_security κ Low = κ.
Proof. intros [r i]; simpl; destruct r; destruct i; reflexivity. Qed.

Lemma protect_security_reader : forall (κ : security) (p : label),
    (protect_security κ p).(reader) = join κ.(reader) p.
Proof. reflexivity. Qed.

Lemma protect_security_indirect : forall (κ : security) (p : label),
    (protect_security κ p).(indirect_reader) = join κ.(indirect_reader) p.
Proof. reflexivity. Qed.

Lemma security_of_ty_protect : forall (p : label) (T : ty),
    security_of (ty_protect p T) = protect_security (security_of T) p.
Proof. intros p T; destruct T; reflexivity. Qed.

(* ================================================================ *)
(* The logical relation.                                            *)
(*                                                                  *)
(* [V T v1 v2] relates two values at type [T], as seen by an        *)
(* observer whose level is [Low].  If the indirect-reader level of  *)
(* [T] is [High], the observer can learn nothing about the context  *)
(* in which the value was produced, and the relation is universal.  *)
(* Otherwise the relation is structural; every value carries a      *)
(* security annotation that must flow to the annotation of its type *)
(* so that the protections performed by the operational semantics   *)
(* are identities in all observable cases.                          *)
(* ================================================================ *)

Fixpoint V (T : ty) (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_Unit κ =>
      match κ.(indirect_reader) with
      | Low => exists (κ1 κ2 : security), v1 = tm_unit κ1 /\ v2 = tm_unit κ2
      | High => True
      end
  | Ty_Sum T1 T2 κ =>
      match κ.(indirect_reader) with
      | Low =>
          (exists (κ1 κ2 : security) (a1 a2 : tm),
              v1 = tm_inl a1 κ1 /\ v2 = tm_inl a2 κ2 /\
              security_le κ1 κ /\ security_le κ2 κ /\ V T1 a1 a2)
          \/ (exists (κ1 κ2 : security) (a1 a2 : tm),
              v1 = tm_inr a1 κ1 /\ v2 = tm_inr a2 κ2 /\
              security_le κ1 κ /\ security_le κ2 κ /\ V T2 a1 a2)
      | High => True
      end
  | Ty_Prod T1 T2 κ =>
      match κ.(indirect_reader) with
      | Low =>
          exists (κ1 κ2 : security) (a1 a2 b1 b2 : tm),
            v1 = tm_pair a1 b1 κ1 /\ v2 = tm_pair a2 b2 κ2 /\
            security_le κ1 κ /\ security_le κ2 κ /\ V T1 a1 a2 /\ V T2 b1 b2
      | High => True
      end
  | Ty_Arrow T1 T2 κ =>
      match κ.(indirect_reader) with
      | Low =>
          exists (T0 : ty) (B : tm) (κ1 : security) (T0' : ty) (B' : tm) (κ1' : security),
            v1 = tm_abs T0 B κ1 /\ v2 = tm_abs T0' B' κ1' /\
            security_le κ1 κ /\ security_le κ1' κ /\
            (forall (r : label) (a1 a2 : tm),
                flows_to κ.(reader) r ->
                (forall w1 w2, evaluates a1 w1 -> evaluates a2 w2 -> V T1 w1 w2) ->
                (forall u1 u2, evaluates (tm_app v1 a1 r) u1 ->
                               evaluates (tm_app v2 a2 r) u2 -> V T2 u1 u2))
      | High => True
      end
  end.

Definition R (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm, evaluates t1 v1 -> evaluates t2 v2 -> V T v1 v2.

Lemma V_high : forall (T : ty) (v1 v2 : tm),
    (security_of T).(indirect_reader) = High -> V T v1 v2.
Proof.
  intros T v1 v2 H. destruct T; simpl in *; rewrite H; exact I.
Qed.

Lemma V_protect_low : forall (T : ty) (v1 v2 : tm),
    V (ty_protect Low T) v1 v2 <-> V T v1 v2.
Proof.
  intros T; destruct T as [κ | T1 T2 κ | T1 T2 κ | T1 T2 κ]; intros v1 v2;
    simpl; destruct κ as [r i]; destruct r; destruct i; simpl; reflexivity.
Qed.

Lemma V_protect_high : forall (T : ty) (v1 v2 : tm),
    V (ty_protect High T) v1 v2.
Proof.
  intros T; destruct T as [κ | T1 T2 κ | T1 T2 κ | T1 T2 κ]; intros v1 v2;
    simpl; destruct κ as [r i]; destruct i; simpl; exact I.
Qed.

Lemma V_protect_intro : forall (p : label) (T : ty) (v1 v2 : tm),
    V T v1 v2 -> V (ty_protect p T) v1 v2.
Proof.
  intros p T v1 v2 H; destruct p.
  - apply V_protect_low; exact H.
  - apply V_protect_high.
Qed.

Lemma V_protect_elim : forall (p : label) (T : ty) (v1 v2 : tm),
    V (ty_protect p T) v1 v2 -> p = Low -> V T v1 v2.
Proof.
  intros p T v1 v2 H Hp; subst p; apply V_protect_low; exact H.
Qed.

Lemma protect_value_low : forall v : tm, protect_value v Low = v.
Proof.
  intros v; destruct v; simpl; try reflexivity;
    rewrite protect_security_low; reflexivity.
Qed.

Lemma value_protect_value : forall (v : tm) (l : label),
    value v -> value (protect_value v l).
Proof.
  intros v l Hv; induction Hv; simpl; eauto using value.
Qed.

(* ================================================================ *)
(* Operational semantics: basic inversions and congruences.         *)
(* ================================================================ *)

Lemma value_step_false : forall t t' : tm, step t t' -> value t -> False.
Proof.
  intros t t' H. induction H; intros Hv; inversion Hv; subst; eauto.
Qed.

Lemma multi_value : forall (v u : tm), value v -> multi v u -> u = v.
Proof.
  intros v u Hv Hm; induction Hm.
  - reflexivity.
  - exfalso; eapply value_step_false; eauto.
Qed.

Lemma multi_head_stuck : forall (t u : tm),
    (forall t', step t t' -> False) -> multi t u -> u = t.
Proof.
  intros t u H Hm; induction Hm.
  - reflexivity.
  - exfalso; eauto.
Qed.

Lemma step_abs_false : forall (T : ty) (B : tm) (κ : security) (t' : tm),
    step (tm_abs T B κ) t' -> False.
Proof. intros; inversion H. Qed.

Lemma step_unit_false : forall (κ : security) (t' : tm),
    step (tm_unit κ) t' -> False.
Proof. intros; inversion H. Qed.

Lemma multi_abs_inv : forall (T : ty) (B : tm) (κ : security) (u : tm),
    multi (tm_abs T B κ) u -> u = tm_abs T B κ.
Proof.
  intros; eapply multi_head_stuck; [apply step_abs_false | apply H].
Qed.

Lemma multi_unit_inv : forall (κ : security) (u : tm),
    multi (tm_unit κ) u -> u = tm_unit κ.
Proof.
  intros; eapply multi_head_stuck; [apply step_unit_false | apply H].
Qed.

Lemma multi_trans : forall (a b c : tm), multi a b -> multi b c -> multi a c.
Proof.
  intros a b c H1 H2; induction H1.
  - exact H2.
  - eapply multi_step; eauto.
Qed.

Lemma multi_app_l : forall (a a' b : tm) (r : label),
    multi a a' -> multi (tm_app a b r) (tm_app a' b r).
Proof.
  intros a a' b r H; induction H as [a | a x y hs hrest IH].
  - apply multi_refl.
  - eapply multi_step; [apply ST_App1; eauto | apply IH].
Qed.

Lemma multi_app_r : forall (a b b' : tm) (r : label),
    value a -> multi b b' -> multi (tm_app a b r) (tm_app a b' r).
Proof.
  intros a b b' r Hv H; induction H as [b | b x y hs hrest IH].
  - apply multi_refl.
  - eapply multi_step; [apply ST_App2; eauto | apply IH].
Qed.

Lemma multi_protect : forall (l : label) (a a' : tm),
    multi a a' -> multi (tm_protect l a) (tm_protect l a').
Proof.
  intros l a a' H; induction H as [a | a x y hs hrest IH].
  - apply multi_refl.
  - eapply multi_step; [apply ST_Protect; eauto | apply IH].
Qed.

Lemma multi_pair_l : forall (a a' b : tm) (κ : security),
    multi a a' -> multi (tm_pair a b κ) (tm_pair a' b κ).
Proof.
  intros a a' b κ H; induction H as [a | a x y hs hrest IH].
  - apply multi_refl.
  - eapply multi_step; [apply ST_Pair1; eauto | apply IH].
Qed.

Lemma multi_pair_r : forall (a b b' : tm) (κ : security),
    value a -> multi b b' -> multi (tm_pair a b κ) (tm_pair a b' κ).
Proof.
  intros a b b' κ Hv H; induction H as [b | b x y hs hrest IH].
  - apply multi_refl.
  - eapply multi_step; [apply ST_Pair2; eauto | apply IH].
Qed.

Lemma multi_inl : forall (a a' : tm) (κ : security),
    multi a a' -> multi (tm_inl a κ) (tm_inl a' κ).
Proof.
  intros a a' κ H; induction H as [a | a x y hs hrest IH].
  - apply multi_refl.
  - eapply multi_step; [apply ST_Inl; eauto | apply IH].
Qed.

Lemma multi_inr : forall (a a' : tm) (κ : security),
    multi a a' -> multi (tm_inr a κ) (tm_inr a' κ).
Proof.
  intros a a' κ H; induction H as [a | a x y hs hrest IH].
  - apply multi_refl.
  - eapply multi_step; [apply ST_Inr; eauto | apply IH].
Qed.

(* ================================================================ *)
(* Decomposition of completed evaluations.                          *)
(* ================================================================ *)

Lemma evaluates_protect : forall (l : label) (t u : tm),
    evaluates (tm_protect l t) u ->
    exists w : tm, evaluates t w /\ u = protect_value w l.
Proof.
  intros l t u [Hm Hv].
  remember (tm_protect l t) as X eqn:E.
  revert l t Hv E.
  induction Hm as [X | X y z hs hrest IH]; intros l t Hv E.
  - rewrite E in Hv; inversion Hv.
  - rewrite E in hs; inversion hs; subst; clear hs.
    + exists t; split.
      * split; [apply multi_refl | assumption].
      * eapply multi_value; [apply value_protect_value; eauto | apply hrest].
    + destruct (IH l t' Hv eq_refl) as [w [Hev Hu]].
      exists w; split; [| exact Hu].
      split; [| exact (proj2 Hev)].
      eapply multi_step; [eassumption | exact (proj1 Hev)].
Qed.

Lemma evaluates_app : forall (t1 t2 : tm) (r : label) (u : tm),
    evaluates (tm_app t1 t2 r) u ->
    exists (T0 : ty) (B : tm) (κ0 : security) (a : tm),
      multi t1 (tm_abs T0 B κ0) /\ value (tm_abs T0 B κ0) /\
      evaluates t2 a /\ flows_to κ0.(reader) r /\
      multi (tm_protect κ0.(indirect_reader) (open B a)) u.
Proof.
  intros t1 t2 r u [Hm Hv].
  remember (tm_app t1 t2 r) as X eqn:E.
  revert t1 t2 r Hv E.
  induction Hm as [X | X y z hs hrest IH]; intros t1 t2 r Hv E.
  - rewrite E in Hv; inversion Hv.
  - rewrite E in hs; inversion hs; subst; clear hs.
    + (* ST_AppAbs *)
      exists T, body, kappa, t2.
      split; [apply multi_refl | split; [assumption | split]].
      * split; [apply multi_refl | assumption].
      * split; [assumption | assumption].
    + (* ST_App1 *)
      destruct (IH t1' t2 r Hv eq_refl) as (T0 & B & κ0 & a & Hm1 & Hv1 & Hev & Hfl & Hmp).
      exists T0, B, κ0, a.
      split; [| split; [assumption | split; [assumption | split; [assumption | assumption]]]].
      eapply multi_step; [eassumption | eassumption].
    + (* ST_App2 *)
      destruct (IH t1 t2' r Hv eq_refl) as (T0 & B & κ0 & a & Hm1 & Hv1 & Hev & Hfl & Hmp).
      exists T0, B, κ0, a.
      split; [assumption | split; [assumption | split]].
      * split.
        -- eapply multi_step; [eassumption | apply (proj1 Hev)].
        -- apply (proj2 Hev).
      * split; [assumption | assumption].
Qed.

Lemma evaluates_fst : forall (t : tm) (r : label) (u : tm),
    evaluates (tm_fst t r) u ->
    exists (v1 v2 : tm) (κ0 : security),
      multi t (tm_pair v1 v2 κ0) /\ value v1 /\ value v2 /\
      flows_to κ0.(reader) r /\
      multi (tm_protect κ0.(indirect_reader) v1) u.
Proof.
  intros t r u [Hm Hv].
  remember (tm_fst t r) as X eqn:E.
  revert t r Hv E.
  induction Hm as [X | X y z hs hrest IH]; intros t r Hv E.
  - rewrite E in Hv; inversion Hv.
  - rewrite E in hs; inversion hs; subst; clear hs.
    + (* ST_FstPair *)
      exists v1, v2, kappa.
      split; [apply multi_refl | split; [assumption | split; [assumption | split; [assumption | assumption]]]].
    + (* ST_Fst *)
      destruct (IH t' r Hv eq_refl) as (v1 & v2 & κ0 & Hm1 & Hv1 & Hv2 & Hfl & Hmp).
      exists v1, v2, κ0.
      split; [| split; [assumption | split; [assumption | split; [assumption | assumption]]]].
      eapply multi_step; [eassumption | eassumption].
Qed.

Lemma evaluates_snd : forall (t : tm) (r : label) (u : tm),
    evaluates (tm_snd t r) u ->
    exists (v1 v2 : tm) (κ0 : security),
      multi t (tm_pair v1 v2 κ0) /\ value v1 /\ value v2 /\
      flows_to κ0.(reader) r /\
      multi (tm_protect κ0.(indirect_reader) v2) u.
Proof.
  intros t r u [Hm Hv].
  remember (tm_snd t r) as X eqn:E.
  revert t r Hv E.
  induction Hm as [X | X y z hs hrest IH]; intros t r Hv E.
  - rewrite E in Hv; inversion Hv.
  - rewrite E in hs; inversion hs; subst; clear hs.
    + (* ST_SndPair *)
      exists v1, v2, kappa.
      split; [apply multi_refl | split; [assumption | split; [assumption | split; [assumption | assumption]]]].
    + (* ST_Snd *)
      destruct (IH t' r Hv eq_refl) as (v1 & v2 & κ0 & Hm1 & Hv1 & Hv2 & Hfl & Hmp).
      exists v1, v2, κ0.
      split; [| split; [assumption | split; [assumption | split; [assumption | assumption]]]].
      eapply multi_step; [eassumption | eassumption].
Qed.

Lemma evaluates_case : forall (t b1 b2 : tm) (r : label) (u : tm),
    evaluates (tm_case t b1 b2 r) u ->
    (exists (v : tm) (κ0 : security),
        multi t (tm_inl v κ0) /\ value v /\ flows_to κ0.(reader) r /\
        multi (tm_protect κ0.(indirect_reader) (open b1 v)) u)
    \/ (exists (v : tm) (κ0 : security),
        multi t (tm_inr v κ0) /\ value v /\ flows_to κ0.(reader) r /\
        multi (tm_protect κ0.(indirect_reader) (open b2 v)) u).
Proof.
  intros t b1 b2 r u [Hm Hv].
  remember (tm_case t b1 b2 r) as X eqn:E.
  revert t b1 b2 r Hv E.
  induction Hm as [X | X y z hs hrest IH]; intros t b1 b2 r Hv E.
  - rewrite E in Hv; inversion Hv.
  - rewrite E in hs; inversion hs; subst; clear hs.
    + (* ST_CaseLeft *)
      left; exists v, kappa.
      split; [apply multi_refl | split; [assumption | split; [assumption | assumption]]].
    + (* ST_CaseRight *)
      right; exists v, kappa.
      split; [apply multi_refl | split; [assumption | split; [assumption | assumption]]].
    + (* ST_Case *)
      destruct (IH t' b1 b2 r Hv eq_refl) as [(v & κ0 & Hm1 & Hvv & Hfl & Hmp) | (v & κ0 & Hm1 & Hvv & Hfl & Hmp)].
      * left; exists v, κ0.
        split; [| split; [assumption | split; [assumption | assumption]]].
        eapply multi_step; [eassumption | eassumption].
      * right; exists v, κ0.
        split; [| split; [assumption | split; [assumption | assumption]]].
        eapply multi_step; [eassumption | eassumption].
Qed.

Lemma evaluates_if : forall (c yes no : tm) (r : label) (u : tm),
    evaluates (tm_if c yes no r) u ->
    (exists (v : tm) (κ0 : security),
        multi c (tm_inl v κ0) /\ value v /\ flows_to κ0.(reader) r /\
        multi (tm_protect κ0.(indirect_reader) yes) u)
    \/ (exists (v : tm) (κ0 : security),
        multi c (tm_inr v κ0) /\ value v /\ flows_to κ0.(reader) r /\
        multi (tm_protect κ0.(indirect_reader) no) u).
Proof.
  intros c yes no r u [Hm Hv].
  remember (tm_if c yes no r) as X eqn:E.
  revert c yes no r Hv E.
  induction Hm as [X | X y z hs hrest IH]; intros c yes no r Hv E.
  - rewrite E in Hv; inversion Hv.
  - rewrite E in hs; inversion hs; subst; clear hs.
    + (* ST_If *)
      destruct (IH c' yes no r Hv eq_refl) as [(v & κ0 & Hm1 & Hvv & Hfl & Hmp) | (v & κ0 & Hm1 & Hvv & Hfl & Hmp)].
      * left; exists v, κ0.
        split; [| split; [assumption | split; [assumption | assumption]]].
        eapply multi_step; [eassumption | eassumption].
      * right; exists v, κ0.
        split; [| split; [assumption | split; [assumption | assumption]]].
        eapply multi_step; [eassumption | eassumption].
    + (* ST_IfTrue *)
      left; exists v, k.
      split; [apply multi_refl | split; [assumption | split; [assumption | assumption]]].
    + (* ST_IfFalse *)
      right; exists v, k.
      split; [apply multi_refl | split; [assumption | split; [assumption | assumption]]].
Qed.

Lemma evaluates_pair : forall (a b : tm) (κ : security) (u : tm),
    evaluates (tm_pair a b κ) u ->
    exists (v1 v2 : tm), multi a v1 /\ multi b v2 /\ value v1 /\ value v2 /\
                        u = tm_pair v1 v2 κ.
Proof.
  intros a b κ u [Hm Hv].
  remember (tm_pair a b κ) as X eqn:E.
  revert a b κ Hv E.
  induction Hm as [X | X y z hs hrest IH]; intros a b κ Hv E.
  - rewrite E in Hv; inversion Hv; subst.
    exists a, b; split; [apply multi_refl | split; [apply multi_refl | split; [assumption | split; [assumption | reflexivity]]]].
  - rewrite E in hs; inversion hs; subst; clear hs.
    + (* ST_Pair1 *)
      destruct (IH t1' b κ Hv eq_refl) as (v1 & v2 & Hm1 & Hm2 & Hv1 & Hv2 & Hu).
      exists v1, v2; split; [| split; [| split; [| split]]].
      * eapply multi_step; [eassumption | eassumption].
      * assumption.
      * assumption.
      * assumption.
      * assumption.
    + (* ST_Pair2 *)
      destruct (IH a t2' κ Hv eq_refl) as (v1 & v2 & Hm1 & Hm2 & Hv1 & Hv2 & Hu).
      exists v1, v2; split; [| split; [| split; [| split]]].
      * assumption.
      * eapply multi_step; [eassumption | eassumption].
      * assumption.
      * assumption.
      * assumption.
Qed.

Lemma evaluates_inl : forall (a : tm) (κ : security) (u : tm),
    evaluates (tm_inl a κ) u ->
    exists v : tm, multi a v /\ value v /\ u = tm_inl v κ.
Proof.
  intros a κ u [Hm Hv].
  remember (tm_inl a κ) as X eqn:E.
  revert a κ Hv E.
  induction Hm as [X | X y z hs hrest IH]; intros a κ Hv E.
  - rewrite E in Hv; inversion Hv; subst.
    exists a; split; [apply multi_refl | split; [assumption | reflexivity]].
  - rewrite E in hs; inversion hs; subst; clear hs.
    destruct (IH t' κ Hv eq_refl) as (v & Hm1 & Hvv & Hu).
    exists v; split; [| split; [assumption | assumption]].
    eapply multi_step; [eassumption | eassumption].
Qed.

Lemma evaluates_inr : forall (a : tm) (κ : security) (u : tm),
    evaluates (tm_inr a κ) u ->
    exists v : tm, multi a v /\ value v /\ u = tm_inr v κ.
Proof.
  intros a κ u [Hm Hv].
  remember (tm_inr a κ) as X eqn:E.
  revert a κ Hv E.
  induction Hm as [X | X y z hs hrest IH]; intros a κ Hv E.
  - rewrite E in Hv; inversion Hv; subst.
    exists a; split; [apply multi_refl | split; [assumption | reflexivity]].
  - rewrite E in hs; inversion hs; subst; clear hs.
    destruct (IH t' κ Hv eq_refl) as (v & Hm1 & Hvv & Hu).
    exists v; split; [| split; [assumption | assumption]].
    eapply multi_step; [eassumption | eassumption].
Qed.

(* ================================================================ *)
(* Subtyping is contained in the logical relation.                  *)
(* ================================================================ *)

Lemma subtype_security_le : forall (T U : ty),
    subtype T U -> security_le (security_of T) (security_of U).
Proof.
  intros T U H; induction H; simpl; eauto using security_le_trans.
Qed.

Lemma subtype_V : forall (T U : ty), subtype T U ->
    forall v1 v2 : tm, V T v1 v2 -> V U v1 v2.
Proof.
  intros T U Hsub.
  induction Hsub as
      [κ1 κ2 Hw1 Hw2 Hle
      | T1 T2 U1 U2 κ1 κ2 Hs1 IHs1 Hs2 IHs2 Hw1 Hw2 Hle
      | T1 T2 U1 U2 κ1 κ2 Hs1 IHs1 Hs2 IHs2 Hw1 Hw2 Hle
      | T1 T2 U1 U2 κ1 κ2 Hs1 IHs1 Hs2 IHs2 Hw1 Hw2 Hle
      | T U0 X Hs1 IHs1 Hs2 IHs2];
    intros v1 v2 HV.
  - (* S_Unit *)
    destruct κ2 as [r2 i2]; destruct i2.
    + destruct κ1 as [r1 i1]; destruct i1.
      * simpl in HV |- *. exact HV.
      * exfalso; exact (proj2 Hle).
    + apply V_high; reflexivity.
  - (* S_Sum *)
    destruct κ2 as [r2 i2]; destruct i2.
    + destruct κ1 as [r1 i1]; destruct i1.
      * simpl in HV |- *.
        destruct HV as [(κa & κb & a1 & a2 & E1 & E2 & Hsa & Hsb & HVA) |
                       (κa & κb & a1 & a2 & E1 & E2 & Hsa & Hsb & HVA)].
        -- assert (Hle_a : security_le κa {| reader := r2; indirect_reader := Low |})
             by (eapply security_le_trans; [exact Hsa | exact Hle]).
           assert (Hle_b : security_le κb {| reader := r2; indirect_reader := Low |})
             by (eapply security_le_trans; [exact Hsb | exact Hle]).
           assert (HVA' : V U1 a1 a2) by (apply IHs1; exact HVA).
           left; exists κa, κb, a1, a2.
           split; [exact E1 | split; [exact E2 | split; [exact Hle_a | split; [exact Hle_b | exact HVA']]]].
        -- assert (Hle_a : security_le κa {| reader := r2; indirect_reader := Low |})
             by (eapply security_le_trans; [exact Hsa | exact Hle]).
           assert (Hle_b : security_le κb {| reader := r2; indirect_reader := Low |})
             by (eapply security_le_trans; [exact Hsb | exact Hle]).
           assert (HVA' : V U2 a1 a2) by (apply IHs2; exact HVA).
           right; exists κa, κb, a1, a2.
           split; [exact E1 | split; [exact E2 | split; [exact Hle_a | split; [exact Hle_b | exact HVA']]]].
      * exfalso; exact (proj2 Hle).
    + apply V_high; reflexivity.
  - (* S_Prod *)
    destruct κ2 as [r2 i2]; destruct i2.
    + destruct κ1 as [r1 i1]; destruct i1.
      * simpl in HV |- *.
        destruct HV as (κa & κb & a1 & a2 & b1 & b2 & E1 & E2 & Hsa & Hsb & HVA & HVB).
        assert (Hle_a : security_le κa {| reader := r2; indirect_reader := Low |})
          by (eapply security_le_trans; [exact Hsa | exact Hle]).
        assert (Hle_b : security_le κb {| reader := r2; indirect_reader := Low |})
          by (eapply security_le_trans; [exact Hsb | exact Hle]).
        assert (HVA' : V U1 a1 a2) by (apply IHs1; exact HVA).
        assert (HVB' : V U2 b1 b2) by (apply IHs2; exact HVB).
        exists κa, κb, a1, a2, b1, b2.
        split; [exact E1 | split; [exact E2 | split; [exact Hle_a | split; [exact Hle_b | split; [exact HVA' | exact HVB']]]]].
      * exfalso; exact (proj2 Hle).
    + apply V_high; reflexivity.
  - (* S_Arrow *)
    destruct κ2 as [r2 i2]; destruct i2.
    + destruct κ1 as [r1 i1]; destruct i1.
      * simpl in HV |- *.
        destruct HV as (T0 & B & κa & T0' & B' & κa' & E1 & E2 & Hsa & Hsb & HFA).
        assert (Hle_a : security_le κa {| reader := r2; indirect_reader := Low |})
          by (eapply security_le_trans; [exact Hsa | exact Hle]).
        assert (Hle_b : security_le κa' {| reader := r2; indirect_reader := Low |})
          by (eapply security_le_trans; [exact Hsb | exact Hle]).
        exists T0, B, κa, T0', B', κa'.
        split; [exact E1 | split; [exact E2 | split; [exact Hle_a | split; [exact Hle_b | idtac]]]].
        intros r a1 a2 Hflow HRU.
        assert (Hflow' : flows_to r1 r).
        { eapply flows_to_trans; [| exact Hflow]. exact (proj1 Hle). }
        assert (HRT : R T1 a1 a2).
        { intros w1 w2 He1 He2. apply IHs1. apply HRU; assumption. }
        specialize (HFA r a1 a2 Hflow' HRT).
        intros u1 u2 Hu1 Hu2. apply IHs2. apply HFA; assumption.
      * exfalso; exact (proj2 Hle).
    + apply V_high; reflexivity.
  - (* S_Trans *)
    apply IHs2, IHs1. exact HV.
Qed.

Lemma subtype_R : forall (T U : ty), subtype T U ->
    forall t1 t2 : tm, R T t1 t2 -> R U t1 t2.
Proof.
  intros T U Hsub t1 t2 HR v1 v2 He1 He2.
  apply (subtype_V T U Hsub). apply HR; assumption.
Qed.

(* ================================================================ *)
(* Locally closed terms, simultaneous substitution, and opening.    *)
(* ================================================================ *)

Lemma lc_at_open_rec_inv : forall (body u : tm) (k : nat),
    lc_at k (open_rec k u body) -> lc_at (S k) body.
Proof.
  intros body; induction body; intros u k H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; [| simpl in H; lia].
    apply Nat.eqb_eq in E; subst n; lia.
  - auto.
  - auto.
  - eapply IHbody. exact H.
  - destruct H as [H1 H2]; simpl; split; eauto.
  - destruct H as [H1 H2]; simpl; split; eauto.
  - simpl; eauto.
  - simpl; eauto.
  - simpl; eauto.
  - simpl; eauto.
  - destruct H as [H1 [H2 H3]]; simpl; repeat split; eauto.
  - simpl; eauto.
  - destruct H as [H1 [H2 H3]]; simpl; repeat split; eauto.
Qed.

Lemma lc_at_open_rec_id : forall (t : tm) (n : nat), lc_at n t ->
    forall (k : nat) (u : tm), n <= k -> open_rec k u t = t.
Proof.
  intros t; induction t; intros m Hlc k u Hnk; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E; subst n; exfalso; lia.
  - reflexivity.
  - reflexivity.
  - f_equal. eapply IHt; [exact Hlc | lia].
  - destruct Hlc as [H1 H2]; f_equal.
    + eapply IHt1; [exact H1 | lia].
    + eapply IHt2; [exact H2 | lia].
  - destruct Hlc as [H1 H2]; f_equal.
    + eapply IHt1; [exact H1 | lia].
    + eapply IHt2; [exact H2 | lia].
  - f_equal; eapply IHt; [exact Hlc | lia].
  - f_equal; eapply IHt; [exact Hlc | lia].
  - f_equal; eapply IHt; [exact Hlc | lia].
  - f_equal; eapply IHt; [exact Hlc | lia].
  - destruct Hlc as [H1 [H2 H3]]; f_equal.
    + eapply IHt1; [exact H1 | lia].
    + eapply IHt2; [exact H2 | lia].
    + eapply IHt3; [exact H3 | lia].
  - f_equal; eapply IHt; [exact Hlc | lia].
  - destruct Hlc as [H1 [H2 H3]]; f_equal.
    + eapply IHt1; [exact H1 | lia].
    + eapply IHt2; [exact H2 | lia].
    + eapply IHt3; [exact H3 | lia].
Qed.

Fixpoint subst_all (δ : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => δ x
  | tm_unit κ => tm_unit κ
  | tm_abs T body κ => tm_abs T (subst_all δ body) κ
  | tm_app t1 t2 r => tm_app (subst_all δ t1) (subst_all δ t2) r
  | tm_pair t1 t2 κ => tm_pair (subst_all δ t1) (subst_all δ t2) κ
  | tm_fst t1 r => tm_fst (subst_all δ t1) r
  | tm_snd t1 r => tm_snd (subst_all δ t1) r
  | tm_inl t1 κ => tm_inl (subst_all δ t1) κ
  | tm_inr t1 κ => tm_inr (subst_all δ t1) κ
  | tm_case t0 b1 b2 r =>
      tm_case (subst_all δ t0) (subst_all δ b1) (subst_all δ b2) r
  | tm_protect l t1 => tm_protect l (subst_all δ t1)
  | tm_if c yes no r =>
      tm_if (subst_all δ c) (subst_all δ yes) (subst_all δ no) r
  end.

Definition extend_env (δ : atom -> tm) (x : atom) (w : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then w else δ y.

Lemma subst_all_open_rec : forall (δ : atom -> tm),
    (forall x : atom, lc_at 0 (δ x)) ->
    forall (k : nat) (u body : tm),
      subst_all δ (open_rec k u body) =
      open_rec k (subst_all δ u) (subst_all δ body).
Proof.
  intros δ Hlc k u body; revert k.
  induction body; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite (lc_at_open_rec_id (δ a) 0 (Hlc a) k (subst_all δ u) (Nat.le_0_l k)).
    reflexivity.
  - reflexivity.
  - simpl; rewrite IHbody; reflexivity.
  - simpl; rewrite IHbody1, IHbody2; reflexivity.
  - simpl; rewrite IHbody1, IHbody2; reflexivity.
  - simpl; rewrite IHbody; reflexivity.
  - simpl; rewrite IHbody; reflexivity.
  - simpl; rewrite IHbody; reflexivity.
  - simpl; rewrite IHbody; reflexivity.
  - simpl; rewrite IHbody1, IHbody2, IHbody3; reflexivity.
  - simpl; rewrite IHbody; reflexivity.
  - simpl; rewrite IHbody1, IHbody2, IHbody3; reflexivity.
Qed.

Lemma In_app_l : forall (a b : list atom) (x : atom), In x a -> In x (a ++ b).
Proof. intros; apply in_or_app; auto. Qed.

Lemma In_app_r : forall (a b : list atom) (x : atom), In x b -> In x (a ++ b).
Proof. intros; apply in_or_app; auto. Qed.

Lemma subst_all_ext : forall (δ1 δ2 : atom -> tm) (t : tm),
    (forall x : atom, In x (fv t) -> δ1 x = δ2 x) ->
    subst_all δ1 t = subst_all δ2 t.
Proof.
  intros δ1 δ2 t H; induction t; simpl.
  - reflexivity.
  - apply H; simpl; auto.
  - reflexivity.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl. apply In_app_l. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl. apply In_app_r. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl. apply In_app_l. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl. apply In_app_r. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl.
      apply In_app_l. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl.
      apply In_app_r. apply In_app_l. exact Hx.
    + apply IHt3. intros x Hx. apply H. simpl.
      apply In_app_r. apply In_app_r. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl.
      apply In_app_l. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl.
      apply In_app_r. apply In_app_l. exact Hx.
    + apply IHt3. intros x Hx. apply H. simpl.
      apply In_app_r. apply In_app_r. exact Hx.
Qed.

Lemma subst_all_id_on_fv : forall (δ : atom -> tm) (t : tm),
    (forall x : atom, In x (fv t) -> δ x = tm_fvar x) ->
    subst_all δ t = t.
Proof.
  intros δ t H; induction t; simpl.
  - reflexivity.
  - apply H; simpl; auto.
  - reflexivity.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl. apply In_app_l. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl. apply In_app_r. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl. apply In_app_l. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl. apply In_app_r. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl.
      apply In_app_l. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl.
      apply In_app_r. apply In_app_l. exact Hx.
    + apply IHt3. intros x Hx. apply H. simpl.
      apply In_app_r. apply In_app_r. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl.
      apply In_app_l. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl.
      apply In_app_r. apply In_app_l. exact Hx.
    + apply IHt3. intros x Hx. apply H. simpl.
      apply In_app_r. apply In_app_r. exact Hx.
Qed.

Lemma open_subst_all_extend : forall (δ : atom -> tm) (x : atom) (w body : tm),
    lc_at 0 w -> (forall y : atom, lc_at 0 (δ y)) -> ~ In x (fv body) ->
    subst_all (extend_env δ x w) (open body (tm_fvar x)) =
    open (subst_all δ body) w.
Proof.
  intros δ x w body Hw Hlc Hfresh.
  unfold open.
  rewrite subst_all_open_rec.
  - unfold extend_env. simpl. rewrite Nat.eqb_refl. simpl.
    rewrite subst_all_ext with (δ1 := extend_env δ x w) (δ2 := δ).
    + reflexivity.
    + intros y Hy.
      unfold extend_env.
      assert (Hne : (y =? x) = false).
      { apply Nat.eqb_neq. intro; subst y; exact (Hfresh Hy). }
      rewrite Hne; reflexivity.
  - intros y; unfold extend_env; destruct (Nat.eqb y x); auto.
Qed.

Lemma fresh_atom : forall (L : list atom), exists x : atom, ~ In x L.
Proof.
  assert (H : forall (L : list atom), exists x : atom, forall y : atom, In y L -> y < x).
  { induction L as [| a L [x Hx]].
    - exists 0; intros y Hy; simpl in Hy; contradiction.
    - exists (S (Nat.max a x)); intros y [Heq | Hy].
      + lia.
      + specialize (Hx y Hy); lia. }
  intros L; destruct (H L) as [x Hx].
  exists x; intros Hin; specialize (Hx x Hin); lia.
Qed.

Lemma value_lc : forall (v : tm), value v -> lc_at 0 v.
Proof.
  intros v Hv; induction Hv; simpl; auto.
Qed.

Lemma has_type_lc : forall (Gamma : context) (t : tm) (T : ty),
    has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T H.
  induction H as
      [Gamma0 x T0 Hlook Hwf
      | Gamma0 kappa Hwf
      | L Gamma0 T1 body T2 kappa Hwf1 Hwf2 Habs IHAbs
      | Gamma0 t1 t2 T1 T2 kappa r Ht1 IHt1 Ht2 IHt2 Hflow
      | Gamma0 t1 t2 T1 T2 kappa Ht1 IHt1 Ht2 IHt2 Hwf
      | Gamma0 t T1 T2 kappa r Ht IHt Hflow
      | Gamma0 t T1 T2 kappa r Ht IHt Hflow
      | Gamma0 t T1 T2 kappa Ht IHt Hwf2 Hwf
      | Gamma0 t T1 T2 kappa Hwf1 Ht IHt Hwf
      | L Gamma0 t body1 body2 T1 T2 T0 kappa r Ht IHt Hflow Hb1 IHb1 Hb2 IHb2
      | Gamma0 t T0 l Ht IHt
      | Gamma0 t T0 U Ht IHt Hsub
      | Gamma0 c yes no k T0 r Hc IHc Hy IHy Hn IHn Hflow];
    simpl.
  - exact I.
  - exact I.
  - destruct (fresh_atom L) as [x Hx].
    pose proof (IHAbs x Hx) as Hlc.
    exact (lc_at_open_rec_inv body (tm_fvar x) 0 Hlc).
  - split; [exact IHt1 | exact IHt2].
  - split; [exact IHt1 | exact IHt2].
  - exact IHt.
  - exact IHt.
  - exact IHt.
  - exact IHt.
  - destruct (fresh_atom L) as [x Hx].
    pose proof (IHb1 x Hx) as Hlc1.
    pose proof (IHb2 x Hx) as Hlc2.
    pose proof (lc_at_open_rec_inv body1 (tm_fvar x) 0 Hlc1) as HLc1.
    pose proof (lc_at_open_rec_inv body2 (tm_fvar x) 0 Hlc2) as HLc2.
    repeat split; assumption.
  - exact IHt.
  - exact IHt.
  - repeat split; assumption.
Qed.

Fixpoint fv_ctx (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ => fv_ctx C'
  | C_AppLeft C' t _ => fv_ctx C' ++ fv t
  | C_AppRight t C' _ => fv t ++ fv_ctx C'
  | C_PairLeft C' t _ => fv_ctx C' ++ fv t
  | C_PairRight t C' _ => fv t ++ fv_ctx C'
  | C_Fst C' _ => fv_ctx C'
  | C_Snd C' _ => fv_ctx C'
  | C_Inl C' _ => fv_ctx C'
  | C_Inr C' _ => fv_ctx C'
  | C_CaseScrutinee C' t1 t2 _ => fv_ctx C' ++ fv t1 ++ fv t2
  | C_CaseLeft t0 C' t2 _ => fv t0 ++ fv_ctx C' ++ fv t2
  | C_CaseRight t0 t1 C' _ => fv t0 ++ fv t1 ++ fv_ctx C'
  | C_Protect _ C' => fv_ctx C'
  | C_IfCondition C' y n _ => fv_ctx C' ++ fv y ++ fv n
  | C_IfThen c C' n _ => fv c ++ fv_ctx C' ++ fv n
  | C_IfElse c y C' _ => fv c ++ fv y ++ fv_ctx C'
  end.

Lemma In_three_l : forall (a b c : list atom) (x : atom), In x a -> In x (a ++ b ++ c).
Proof. intros; apply In_app_l; exact H. Qed.

Lemma In_three_m : forall (a b c : list atom) (x : atom), In x b -> In x (a ++ b ++ c).
Proof. intros; apply In_app_r; apply In_app_l; exact H. Qed.

Lemma In_three_r : forall (a b c : list atom) (x : atom), In x c -> In x (a ++ b ++ c).
Proof. intros; apply In_app_r; apply In_app_r; exact H. Qed.

Lemma subst_all_plug : forall (δ : atom -> tm) (C : program_context) (t : tm),
    (forall x : atom, In x (fv_ctx C) -> δ x = tm_fvar x) ->
    subst_all δ (plug C t) = plug C (subst_all δ t).
Proof.
  intros δ C.
  induction C as
      [ | T C' IHC κ | C' IHC t2 r | t1 C' IHC r | C' IHC t2 κ | t1 C' IHC κ
      | C' IHC r | C' IHC r | C' IHC κ | C' IHC κ
      | C' IHC b1 b2 r | t0 C' IHC b2 r | t0 b1 C' IHC r | l C' IHC
      | C' IHC y n r | c C' IHC n r | c y C' IHC r];
    intros t H; simpl.
  - reflexivity.
  - rewrite (IHC t). reflexivity. intros x Hx; apply H; exact Hx.
  - assert (Hp : forall x, In x (fv_ctx C') -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_app_l; exact Hx. }
    assert (Hq : forall x, In x (fv t2) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_app_r; exact Hx. }
    rewrite (IHC t Hp). rewrite (subst_all_id_on_fv δ t2 Hq). reflexivity.
  - assert (Hp : forall x, In x (fv_ctx C') -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_app_r; exact Hx. }
    assert (Hq : forall x, In x (fv t1) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_app_l; exact Hx. }
    rewrite (IHC t Hp). rewrite (subst_all_id_on_fv δ t1 Hq). reflexivity.
  - assert (Hp : forall x, In x (fv_ctx C') -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_app_l; exact Hx. }
    assert (Hq : forall x, In x (fv t2) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_app_r; exact Hx. }
    rewrite (IHC t Hp). rewrite (subst_all_id_on_fv δ t2 Hq). reflexivity.
  - assert (Hp : forall x, In x (fv_ctx C') -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_app_r; exact Hx. }
    assert (Hq : forall x, In x (fv t1) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_app_l; exact Hx. }
    rewrite (IHC t Hp). rewrite (subst_all_id_on_fv δ t1 Hq). reflexivity.
  - rewrite (IHC t). reflexivity. intros x Hx; apply H; exact Hx.
  - rewrite (IHC t). reflexivity. intros x Hx; apply H; exact Hx.
  - rewrite (IHC t). reflexivity. intros x Hx; apply H; exact Hx.
  - rewrite (IHC t). reflexivity. intros x Hx; apply H; exact Hx.
  - assert (Hp : forall x, In x (fv_ctx C') -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_l; exact Hx. }
    assert (Hq1 : forall x, In x (fv b1) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_m; exact Hx. }
    assert (Hq2 : forall x, In x (fv b2) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_r; exact Hx. }
    rewrite (IHC t Hp). rewrite (subst_all_id_on_fv δ b1 Hq1).
    rewrite (subst_all_id_on_fv δ b2 Hq2). reflexivity.
  - assert (Hp : forall x, In x (fv_ctx C') -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_m; exact Hx. }
    assert (Hq1 : forall x, In x (fv t0) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_l; exact Hx. }
    assert (Hq2 : forall x, In x (fv b2) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_r; exact Hx. }
    rewrite (IHC t Hp). rewrite (subst_all_id_on_fv δ t0 Hq1).
    rewrite (subst_all_id_on_fv δ b2 Hq2). reflexivity.
  - assert (Hp : forall x, In x (fv_ctx C') -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_r; exact Hx. }
    assert (Hq1 : forall x, In x (fv t0) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_l; exact Hx. }
    assert (Hq2 : forall x, In x (fv b1) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_m; exact Hx. }
    rewrite (IHC t Hp). rewrite (subst_all_id_on_fv δ t0 Hq1).
    rewrite (subst_all_id_on_fv δ b1 Hq2). reflexivity.
  - rewrite (IHC t). reflexivity. intros x Hx; apply H; exact Hx.
  - assert (Hp : forall x, In x (fv_ctx C') -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_l; exact Hx. }
    assert (Hq1 : forall x, In x (fv y) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_m; exact Hx. }
    assert (Hq2 : forall x, In x (fv n) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_r; exact Hx. }
    rewrite (IHC t Hp). rewrite (subst_all_id_on_fv δ y Hq1).
    rewrite (subst_all_id_on_fv δ n Hq2). reflexivity.
  - assert (Hp : forall x, In x (fv_ctx C') -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_m; exact Hx. }
    assert (Hq1 : forall x, In x (fv c) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_l; exact Hx. }
    assert (Hq2 : forall x, In x (fv n) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_r; exact Hx. }
    rewrite (IHC t Hp). rewrite (subst_all_id_on_fv δ c Hq1).
    rewrite (subst_all_id_on_fv δ n Hq2). reflexivity.
  - assert (Hp : forall x, In x (fv_ctx C') -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_r; exact Hx. }
    assert (Hq1 : forall x, In x (fv c) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_l; exact Hx. }
    assert (Hq2 : forall x, In x (fv y) -> δ x = tm_fvar x).
    { intros x Hx; apply H; apply In_three_m; exact Hx. }
    rewrite (IHC t Hp). rewrite (subst_all_id_on_fv δ c Hq1).
    rewrite (subst_all_id_on_fv δ y Hq2). reflexivity.
Qed.

(* ================================================================ *)
(* Inversion principles for the value relation, and environments.   *)
(* ================================================================ *)

Lemma security_le_ind_low : forall (κ1 κ2 : security),
    security_le κ1 κ2 -> κ2.(indirect_reader) = Low -> κ1.(indirect_reader) = Low.
Proof.
  intros [r1 i1] [r2 i2] Hle Hi2. destruct i2.
  - destruct Hle as [Hr Hi]. destruct i1; simpl in *; auto; contradiction.
  - discriminate Hi2.
Qed.

Lemma V_unit_inv : forall (κ : security) (v1 v2 : tm),
    κ.(indirect_reader) = Low -> V (Ty_Unit κ) v1 v2 ->
    exists (κ1 κ2 : security), v1 = tm_unit κ1 /\ v2 = tm_unit κ2.
Proof.
  intros κ v1 v2 H HV.
  destruct κ as [r i]; destruct i; [| discriminate H].
  simpl in HV |- *. exact HV.
Qed.

Lemma V_sum_inv : forall (T1 T2 : ty) (κ : security) (v1 v2 : tm),
    κ.(indirect_reader) = Low -> V (Ty_Sum T1 T2 κ) v1 v2 ->
    ((exists (κ1 κ2 : security) (a1 a2 : tm),
         v1 = tm_inl a1 κ1 /\ v2 = tm_inl a2 κ2 /\
         security_le κ1 κ /\ security_le κ2 κ /\ V T1 a1 a2)
     \/ (exists (κ1 κ2 : security) (a1 a2 : tm),
         v1 = tm_inr a1 κ1 /\ v2 = tm_inr a2 κ2 /\
         security_le κ1 κ /\ security_le κ2 κ /\ V T2 a1 a2)).
Proof.
  intros T1 T2 κ v1 v2 H HV.
  destruct κ as [r i]; destruct i; [| discriminate H].
  simpl in HV |- *. exact HV.
Qed.

Lemma V_prod_inv : forall (T1 T2 : ty) (κ : security) (v1 v2 : tm),
    κ.(indirect_reader) = Low -> V (Ty_Prod T1 T2 κ) v1 v2 ->
    exists (κ1 κ2 : security) (a1 a2 b1 b2 : tm),
      v1 = tm_pair a1 b1 κ1 /\ v2 = tm_pair a2 b2 κ2 /\
      security_le κ1 κ /\ security_le κ2 κ /\ V T1 a1 a2 /\ V T2 b1 b2.
Proof.
  intros T1 T2 κ v1 v2 H HV.
  destruct κ as [r i]; destruct i; [| discriminate H].
  simpl in HV |- *. exact HV.
Qed.

Lemma V_arrow_inv : forall (T1 T2 : ty) (κ : security) (v1 v2 : tm),
    κ.(indirect_reader) = Low -> V (Ty_Arrow T1 T2 κ) v1 v2 ->
    exists (T0 : ty) (B : tm) (κ1 : security) (T0' : ty) (B' : tm) (κ1' : security),
      v1 = tm_abs T0 B κ1 /\ v2 = tm_abs T0' B' κ1' /\
      security_le κ1 κ /\ security_le κ1' κ /\
      (forall (r : label) (a1 a2 : tm),
          flows_to κ.(reader) r ->
          (forall w1 w2, evaluates a1 w1 -> evaluates a2 w2 -> V T1 w1 w2) ->
          (forall u1 u2, evaluates (tm_app v1 a1 r) u1 ->
                         evaluates (tm_app v2 a2 r) u2 -> V T2 u1 u2)).
Proof.
  intros T1 T2 κ v1 v2 H HV.
  destruct κ as [r i]; destruct i; [| discriminate H].
  simpl in HV |- *. exact HV.
Qed.

Definition env_rel (Gamma : context) (δ1 δ2 : atom -> tm) : Prop :=
  (forall x : atom, lc_at 0 (δ1 x) /\ lc_at 0 (δ2 x)) /\
  (forall (x : atom) (T : ty), lookup_context x Gamma = Some T -> R T (δ1 x) (δ2 x)).

Lemma R_of_V_value : forall (T : ty) (v1 v2 : tm),
    value v1 -> value v2 -> V T v1 v2 -> R T v1 v2.
Proof.
  intros T v1 v2 Hv1 Hv2 HV u1 u2 [Hm1 _] [Hm2 _].
  rewrite (multi_value v1 u1 Hv1 Hm1), (multi_value v2 u2 Hv2 Hm2).
  exact HV.
Qed.

Lemma env_rel_extend : forall (Gamma : context) (δ1 δ2 : atom -> tm)
    (x : atom) (T1 : ty) (w1 w2 : tm),
    env_rel Gamma δ1 δ2 -> value w1 -> value w2 -> V T1 w1 w2 ->
    env_rel (update Gamma x T1) (extend_env δ1 x w1) (extend_env δ2 x w2).
Proof.
  intros Gamma δ1 δ2 x T1 w1 w2 [Hlc HenvR] Hv1 Hv2 HV.
  split.
  - intros y. unfold extend_env. destruct (Nat.eqb y x).
    + split; apply value_lc; assumption.
    + apply Hlc.
  - intros y T' Hlook. unfold extend_env.
    destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E; subst y.
      unfold update in Hlook. simpl in Hlook.
      rewrite Nat.eqb_refl in Hlook. simpl in Hlook.
      injection Hlook as HT'. subst T'.
      apply R_of_V_value; assumption.
    + unfold update in Hlook. simpl in Hlook. rewrite E in Hlook.
      apply HenvR; exact Hlook.
Qed.

(* ================================================================ *)
(* The fundamental theorem of the logical relation.                 *)
(* ================================================================ *)

Lemma fundamental : forall (Gamma : context) (t : tm) (T : ty),
    has_type Gamma t T ->
    forall (δ1 δ2 : atom -> tm), env_rel Gamma δ1 δ2 ->
    R T (subst_all δ1 t) (subst_all δ2 t).
Proof.
  intros Gamma t T H.
  induction H as
      [Gamma0 x T0 Hlook Hwf
      | Gamma0 kappa Hwf
      | L Gamma0 T1 body T2 kappa Hwf1 Hwf2 Habs IHAbs
      | Gamma0 t1 t2 T1 T2 kappa r Ht1 IHt1 Ht2 IHt2 Hflow
      | Gamma0 t1 t2 T1 T2 kappa Ht1 IHt1 Ht2 IHt2 Hwf
      | Gamma0 t T1 T2 kappa r Ht IHt Hflow
      | Gamma0 t T1 T2 kappa r Ht IHt Hflow
      | Gamma0 t T1 T2 kappa Ht IHt Hwf2 Hwf
      | Gamma0 t T1 T2 kappa Hwf1 Ht IHt Hwf
      | L Gamma0 t body1 body2 T1 T2 T0 kappa r Ht IHt Hflow Hb1 IHb1 Hb2 IHb2
      | Gamma0 t T0 l Ht IHt
      | Gamma0 t T0 U Ht IHt Hsub
      | Gamma0 c yes no k T0 r Hc IHc Hy IHy Hn IHn Hflow];
    intros δ1 δ2 [Hlc HenvR].
  - (* T_Var *)
    apply HenvR; exact Hlook.
  - (* T_Unit *)
    unfold R. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    rewrite (multi_unit_inv kappa v1 Hm1), (multi_unit_inv kappa v2 Hm2).
    destruct kappa as [kr ki]; destruct ki.
    + simpl. exists {| reader := kr; indirect_reader := Low |},
                     {| reader := kr; indirect_reader := Low |}.
      simpl. auto.
    + apply V_high; reflexivity.
  - (* T_Abs *)
    unfold R. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    rewrite (multi_abs_inv T1 (subst_all δ1 body) kappa v1 Hm1).
    rewrite (multi_abs_inv T1 (subst_all δ2 body) kappa v2 Hm2).
    destruct kappa as [kr ki]; destruct ki.
    + simpl.
      exists T1, (subst_all δ1 body), {| reader := kr; indirect_reader := Low |},
             T1, (subst_all δ2 body), {| reader := kr; indirect_reader := Low |}.
      split; [reflexivity | split; [reflexivity | split; [apply security_le_refl
        | split; [apply security_le_refl | idtac]]]].
      intros r a1 a2 Hflow' HR1.
      intros u1 u2 [Hmu1 Hvu1] [Hmu2 Hvu2].
      destruct (evaluates_app (tm_abs T1 (subst_all δ1 body) {| reader := kr; indirect_reader := Low |}) a1 r u1 (conj Hmu1 Hvu1)) as (T0 & B & k0 & a & Hmabs & Hvalabs & Heva & Hfl & Hmp).
      destruct (evaluates_app (tm_abs T1 (subst_all δ2 body) {| reader := kr; indirect_reader := Low |}) a2 r u2 (conj Hmu2 Hvu2)) as (T0' & B' & k0' & a' & Hmabs' & Hvalabs' & Heva' & Hfl' & Hmp').
      assert (Eabs : tm_abs T0 B k0 = tm_abs T1 (subst_all δ1 body) {| reader := kr; indirect_reader := Low |})
        by (apply multi_abs_inv; exact Hmabs).
      injection Eabs as ET1 EB1 Ek1. subst.
      assert (Eabs' : tm_abs T0' B' k0' = tm_abs T1 (subst_all δ2 body) {| reader := kr; indirect_reader := Low |})
        by (apply multi_abs_inv; exact Hmabs').
      injection Eabs' as ET2 EB2 Ek2. subst.
      destruct (evaluates_protect Low (open (subst_all δ1 body) a) u1 (conj Hmp Hvu1)) as (w1 & Hevw1 & Hu1).
      destruct (evaluates_protect Low (open (subst_all δ2 body) a') u2 (conj Hmp' Hvu2)) as (w2 & Hevw2 & Hu2).
      rewrite protect_value_low in Hu1. rewrite protect_value_low in Hu2.
      assert (HV1 : V T1 a a') by (apply HR1; assumption).
      destruct (fresh_atom (L ++ fv body)) as [x Hx].
      assert (HxL : ~ In x L) by (intro Hc; apply Hx; apply In_app_l; exact Hc).
      assert (Hxf : ~ In x (fv body)) by (intro Hc; apply Hx; apply In_app_r; exact Hc).
      assert (Henv' : env_rel (update Gamma0 x T1) (extend_env δ1 x a) (extend_env δ2 x a')).
      { apply env_rel_extend; [exact (conj Hlc HenvR) | exact (proj2 Heva) | exact (proj2 Heva') | exact HV1]. }
      pose proof (IHAbs x HxL (extend_env δ1 x a) (extend_env δ2 x a') Henv') as HRbody.
      rewrite (open_subst_all_extend δ1 x a body (value_lc a (proj2 Heva)) (fun y => proj1 (Hlc y)) Hxf) in HRbody.
      rewrite (open_subst_all_extend δ2 x a' body (value_lc a' (proj2 Heva')) (fun y => proj2 (Hlc y)) Hxf) in HRbody.
      rewrite Hu1, Hu2. apply HRbody; assumption.
    + apply V_high; reflexivity.
  - (* T_App *)
    unfold R. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct kappa as [kr ki]; destruct ki.
    + apply V_protect_low.
      destruct (evaluates_app (subst_all δ1 t1) (subst_all δ1 t2) r v1 (conj Hm1 Hv1)) as (T0 & B & k0 & a & Hmabs & Hvalabs & Heva & Hfl & Hmp).
      destruct (evaluates_app (subst_all δ2 t1) (subst_all δ2 t2) r v2 (conj Hm2 Hv2)) as (T0' & B' & k0' & a' & Hmabs' & Hvalabs' & Heva' & Hfl' & Hmp').
      pose proof (IHt1 δ1 δ2 (conj Hlc HenvR)) as HR1.
      pose proof (IHt2 δ1 δ2 (conj Hlc HenvR)) as HR2.
      pose proof (HR1 (tm_abs T0 B k0) (tm_abs T0' B' k0') (conj Hmabs Hvalabs) (conj Hmabs' Hvalabs')) as HVarrow.
      destruct (V_arrow_inv T1 T2 {| reader := kr; indirect_reader := Low |} (tm_abs T0 B k0) (tm_abs T0' B' k0') eq_refl HVarrow) as (Ta & Ba & ka & Tb & Bb & kb & E1 & E2 & Hle_a & Hle_b & HFA).
      injection E1 as ET1 EB1 Ek1. subst Ta. subst Ba. subst ka.
      injection E2 as ET2 EB2 Ek2. subst Tb. subst Bb. subst kb.
      assert (Hk0 : k0.(indirect_reader) = Low)
        by (eapply security_le_ind_low; [exact Hle_a | reflexivity]).
      assert (Hk0' : k0'.(indirect_reader) = Low)
        by (eapply security_le_ind_low; [exact Hle_b | reflexivity]).
      destruct (evaluates_protect k0.(indirect_reader) (open B a) v1 (conj Hmp Hv1)) as (w1 & Hevw1 & Hu1).
      destruct (evaluates_protect k0'.(indirect_reader) (open B' a') v2 (conj Hmp' Hv2)) as (w2 & Hevw2 & Hu2).
      rewrite Hk0 in Hu1. rewrite protect_value_low in Hu1.
      rewrite Hk0' in Hu2. rewrite protect_value_low in Hu2.
      assert (Happ1 : evaluates (tm_app (tm_abs T0 B k0) (subst_all δ1 t2) r) v1).
      { split.
        - eapply multi_trans.
          + eapply multi_app_r; [exact Hvalabs | apply (proj1 Heva)].
          + eapply multi_step.
            * apply ST_AppAbs; [exact Hvalabs | apply (proj2 Heva) | exact Hfl].
            * exact Hmp.
        - exact Hv1. }
      assert (Happ2 : evaluates (tm_app (tm_abs T0' B' k0') (subst_all δ2 t2) r) v2).
      { split.
        - eapply multi_trans.
          + eapply multi_app_r; [exact Hvalabs' | apply (proj1 Heva')].
          + eapply multi_step.
            * apply ST_AppAbs; [exact Hvalabs' | apply (proj2 Heva') | exact Hfl'].
            * exact Hmp'.
        - exact Hv2. }
      specialize (HFA r (subst_all δ1 t2) (subst_all δ2 t2) Hflow HR2).
      apply HFA; assumption.
    + apply V_protect_high.
  - (* T_Pair *)
    unfold R. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct kappa as [kr ki]; destruct ki.
    + simpl.
      destruct (evaluates_pair (subst_all δ1 t1) (subst_all δ1 t2) {| reader := kr; indirect_reader := Low |} v1 (conj Hm1 Hv1)) as (x1 & y1 & Hmx & Hmy & Hvx & Hvy & Hu).
      destruct (evaluates_pair (subst_all δ2 t1) (subst_all δ2 t2) {| reader := kr; indirect_reader := Low |} v2 (conj Hm2 Hv2)) as (x2 & y2 & Hmx' & Hmy' & Hvx' & Hvy' & Hu').
      exists {| reader := kr; indirect_reader := Low |}, {| reader := kr; indirect_reader := Low |}, x1, x2, y1, y2.
      split; [exact Hu | split; [exact Hu' | split; [apply security_le_refl
        | split; [apply security_le_refl | split]]]].
      * pose proof (IHt1 δ1 δ2 (conj Hlc HenvR)) as HR1.
        exact (HR1 x1 x2 (conj Hmx Hvx) (conj Hmx' Hvx')).
      * pose proof (IHt2 δ1 δ2 (conj Hlc HenvR)) as HR2.
        exact (HR2 y1 y2 (conj Hmy Hvy) (conj Hmy' Hvy')).
    + apply V_high; reflexivity.
  - (* T_Fst *)
    unfold R. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct kappa as [kr ki]; destruct ki.
    + apply V_protect_low.
      destruct (evaluates_fst (subst_all δ1 t) r v1 (conj Hm1 Hv1)) as (x1 & y1 & k0 & Hm & Hvx & Hvy & Hfl & Hmp).
      destruct (evaluates_fst (subst_all δ2 t) r v2 (conj Hm2 Hv2)) as (x2 & y2 & k0' & Hm' & Hvx' & Hvy' & Hfl' & Hmp').
      pose proof (IHt δ1 δ2 (conj Hlc HenvR)) as HR.
      pose proof (HR (tm_pair x1 y1 k0) (tm_pair x2 y2 k0') (conj Hm (v_pair x1 y1 k0 Hvx Hvy)) (conj Hm' (v_pair x2 y2 k0' Hvx' Hvy'))) as HVprod.
      destruct (V_prod_inv T1 T2 {| reader := kr; indirect_reader := Low |} (tm_pair x1 y1 k0) (tm_pair x2 y2 k0') eq_refl HVprod) as (ka & kb & a1 & a2 & b1 & b2 & E1 & E2 & Hle_a & Hle_b & HVA & HVB).
      injection E1 as EA1 EB1 Ek1. subst a1. subst b1. subst ka.
      injection E2 as EA2 EB2 Ek2. subst a2. subst b2. subst kb.
      assert (Hk0 : k0.(indirect_reader) = Low)
        by (eapply security_le_ind_low; [exact Hle_a | reflexivity]).
      destruct (evaluates_protect k0.(indirect_reader) x1 v1 (conj Hmp Hv1)) as (w1 & Hevw1 & Hu1).
      rewrite Hk0 in Hu1. rewrite protect_value_low in Hu1.
      assert (Hw1 : w1 = x1) by (eapply multi_value; [exact Hvx | apply (proj1 Hevw1)]).
      assert (Hv1' : v1 = x1) by (rewrite Hu1; exact Hw1).
      assert (Hk0' : k0'.(indirect_reader) = Low)
        by (eapply security_le_ind_low; [exact Hle_b | reflexivity]).
      destruct (evaluates_protect k0'.(indirect_reader) x2 v2 (conj Hmp' Hv2)) as (w2 & Hevw2 & Hu2).
      rewrite Hk0' in Hu2. rewrite protect_value_low in Hu2.
      assert (Hw2 : w2 = x2) by (eapply multi_value; [exact Hvx' | apply (proj1 Hevw2)]).
      assert (Hv2' : v2 = x2) by (rewrite Hu2; exact Hw2).
      rewrite Hv1', Hv2'. exact HVA.
    + apply V_protect_high.
  - (* T_Snd *)
    unfold R. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct kappa as [kr ki]; destruct ki.
    + apply V_protect_low.
      destruct (evaluates_snd (subst_all δ1 t) r v1 (conj Hm1 Hv1)) as (x1 & y1 & k0 & Hm & Hvx & Hvy & Hfl & Hmp).
      destruct (evaluates_snd (subst_all δ2 t) r v2 (conj Hm2 Hv2)) as (x2 & y2 & k0' & Hm' & Hvx' & Hvy' & Hfl' & Hmp').
      pose proof (IHt δ1 δ2 (conj Hlc HenvR)) as HR.
      pose proof (HR (tm_pair x1 y1 k0) (tm_pair x2 y2 k0') (conj Hm (v_pair x1 y1 k0 Hvx Hvy)) (conj Hm' (v_pair x2 y2 k0' Hvx' Hvy'))) as HVprod.
      destruct (V_prod_inv T1 T2 {| reader := kr; indirect_reader := Low |} (tm_pair x1 y1 k0) (tm_pair x2 y2 k0') eq_refl HVprod) as (ka & kb & a1 & a2 & b1 & b2 & E1 & E2 & Hle_a & Hle_b & HVA & HVB).
      injection E1 as EA1 EB1 Ek1. subst a1. subst b1. subst ka.
      injection E2 as EA2 EB2 Ek2. subst a2. subst b2. subst kb.
      assert (Hk0 : k0.(indirect_reader) = Low)
        by (eapply security_le_ind_low; [exact Hle_a | reflexivity]).
      destruct (evaluates_protect k0.(indirect_reader) y1 v1 (conj Hmp Hv1)) as (w1 & Hevw1 & Hu1).
      rewrite Hk0 in Hu1. rewrite protect_value_low in Hu1.
      assert (Hw1 : w1 = y1) by (eapply multi_value; [exact Hvy | apply (proj1 Hevw1)]).
      assert (Hv1' : v1 = y1) by (rewrite Hu1; exact Hw1).
      assert (Hk0' : k0'.(indirect_reader) = Low)
        by (eapply security_le_ind_low; [exact Hle_b | reflexivity]).
      destruct (evaluates_protect k0'.(indirect_reader) y2 v2 (conj Hmp' Hv2)) as (w2 & Hevw2 & Hu2).
      rewrite Hk0' in Hu2. rewrite protect_value_low in Hu2.
      assert (Hw2 : w2 = y2) by (eapply multi_value; [exact Hvy' | apply (proj1 Hevw2)]).
      assert (Hv2' : v2 = y2) by (rewrite Hu2; exact Hw2).
      rewrite Hv1', Hv2'. exact HVB.
    + apply V_protect_high.
  - (* T_Inl *)
    unfold R. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct kappa as [kr ki]; destruct ki.
    + simpl. left.
      destruct (evaluates_inl (subst_all δ1 t) {| reader := kr; indirect_reader := Low |} v1 (conj Hm1 Hv1)) as (x1 & Hmx & Hvx & Hu).
      destruct (evaluates_inl (subst_all δ2 t) {| reader := kr; indirect_reader := Low |} v2 (conj Hm2 Hv2)) as (x2 & Hmx' & Hvx' & Hu').
      exists {| reader := kr; indirect_reader := Low |}, {| reader := kr; indirect_reader := Low |}, x1, x2.
      split; [exact Hu | split; [exact Hu' | split; [apply security_le_refl
        | split; [apply security_le_refl | idtac]]]].
      pose proof (IHt δ1 δ2 (conj Hlc HenvR)) as HR.
      exact (HR x1 x2 (conj Hmx Hvx) (conj Hmx' Hvx')).
    + apply V_high; reflexivity.
  - (* T_Inr *)
    unfold R. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct kappa as [kr ki]; destruct ki.
    + simpl. right.
      destruct (evaluates_inr (subst_all δ1 t) {| reader := kr; indirect_reader := Low |} v1 (conj Hm1 Hv1)) as (x1 & Hmx & Hvx & Hu).
      destruct (evaluates_inr (subst_all δ2 t) {| reader := kr; indirect_reader := Low |} v2 (conj Hm2 Hv2)) as (x2 & Hmx' & Hvx' & Hu').
      exists {| reader := kr; indirect_reader := Low |}, {| reader := kr; indirect_reader := Low |}, x1, x2.
      split; [exact Hu | split; [exact Hu' | split; [apply security_le_refl
        | split; [apply security_le_refl | idtac]]]].
      pose proof (IHt δ1 δ2 (conj Hlc HenvR)) as HR.
      exact (HR x1 x2 (conj Hmx Hvx) (conj Hmx' Hvx')).
    + apply V_high; reflexivity.
  - (* T_Case *)
    unfold R. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct kappa as [kr ki]; destruct ki.
    + apply V_protect_low.
      destruct (evaluates_case (subst_all δ1 t) (subst_all δ1 body1) (subst_all δ1 body2) r v1 (conj Hm1 Hv1)) as [(v & k0 & Hm1c & Hv1c & Hfl1 & Hmp1) | (v & k0 & Hm1c & Hv1c & Hfl1 & Hmp1)];
      destruct (evaluates_case (subst_all δ2 t) (subst_all δ2 body1) (subst_all δ2 body2) r v2 (conj Hm2 Hv2)) as [(v' & k0' & Hm2c & Hv2c & Hfl2 & Hmp2) | (v' & k0' & Hm2c & Hv2c & Hfl2 & Hmp2)].
      * (* inl / inl *)
        pose proof (IHt δ1 δ2 (conj Hlc HenvR)) as HRsum.
        pose proof (HRsum (tm_inl v k0) (tm_inl v' k0') (conj Hm1c (v_inl v k0 Hv1c)) (conj Hm2c (v_inl v' k0' Hv2c))) as HVsum.
        destruct (V_sum_inv T1 T2 {| reader := kr; indirect_reader := Low |} (tm_inl v k0) (tm_inl v' k0') eq_refl HVsum) as [(ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA) | (ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA)].
        -- injection E1 as EA1 Ek1. subst a1. subst ka.
           injection E2 as EA2 Ek2. subst a2. subst kb.
           assert (Hk0 : k0.(indirect_reader) = Low)
             by (eapply security_le_ind_low; [exact Hle_a | reflexivity]).
           destruct (evaluates_protect k0.(indirect_reader) (open (subst_all δ1 body1) v) v1 (conj Hmp1 Hv1)) as (w1 & Hevw1 & Hu1).
           rewrite Hk0 in Hu1. rewrite protect_value_low in Hu1.
           assert (Hk0' : k0'.(indirect_reader) = Low)
             by (eapply security_le_ind_low; [exact Hle_b | reflexivity]).
           destruct (evaluates_protect k0'.(indirect_reader) (open (subst_all δ2 body1) v') v2 (conj Hmp2 Hv2)) as (w2 & Hevw2 & Hu2).
           rewrite Hk0' in Hu2. rewrite protect_value_low in Hu2.
           destruct (fresh_atom (L ++ fv body1 ++ fv body2)) as [x Hx].
           assert (HxL : ~ In x L) by (intro Hc; apply Hx; apply In_three_l; exact Hc).
           assert (Hxf1 : ~ In x (fv body1)) by (intro Hc; apply Hx; apply In_three_m; exact Hc).
           assert (Henv' : env_rel (update Gamma0 x T1) (extend_env δ1 x v) (extend_env δ2 x v')).
           { apply env_rel_extend; [exact (conj Hlc HenvR) | exact Hv1c | exact Hv2c | exact HVA]. }
           pose proof (IHb1 x HxL (extend_env δ1 x v) (extend_env δ2 x v') Henv') as HRbody.
           rewrite (open_subst_all_extend δ1 x v body1 (value_lc v Hv1c) (fun y => proj1 (Hlc y)) Hxf1) in HRbody.
           rewrite (open_subst_all_extend δ2 x v' body1 (value_lc v' Hv2c) (fun y => proj2 (Hlc y)) Hxf1) in HRbody.
           rewrite Hu1, Hu2. apply HRbody; assumption.
        -- discriminate E2.
      * (* inl / inr *)
        pose proof (IHt δ1 δ2 (conj Hlc HenvR)) as HRsum.
        pose proof (HRsum (tm_inl v k0) (tm_inr v' k0') (conj Hm1c (v_inl v k0 Hv1c)) (conj Hm2c (v_inr v' k0' Hv2c))) as HVsum.
        destruct (V_sum_inv T1 T2 {| reader := kr; indirect_reader := Low |} (tm_inl v k0) (tm_inr v' k0') eq_refl HVsum) as [(ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA) | (ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA)].
        -- discriminate E2.
        -- discriminate E1.
      * (* inr / inl *)
        pose proof (IHt δ1 δ2 (conj Hlc HenvR)) as HRsum.
        pose proof (HRsum (tm_inr v k0) (tm_inl v' k0') (conj Hm1c (v_inr v k0 Hv1c)) (conj Hm2c (v_inl v' k0' Hv2c))) as HVsum.
        destruct (V_sum_inv T1 T2 {| reader := kr; indirect_reader := Low |} (tm_inr v k0) (tm_inl v' k0') eq_refl HVsum) as [(ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA) | (ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA)].
        -- discriminate E1.
        -- discriminate E2.
      * (* inr / inr *)
        pose proof (IHt δ1 δ2 (conj Hlc HenvR)) as HRsum.
        pose proof (HRsum (tm_inr v k0) (tm_inr v' k0') (conj Hm1c (v_inr v k0 Hv1c)) (conj Hm2c (v_inr v' k0' Hv2c))) as HVsum.
        destruct (V_sum_inv T1 T2 {| reader := kr; indirect_reader := Low |} (tm_inr v k0) (tm_inr v' k0') eq_refl HVsum) as [(ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA) | (ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA)].
        -- discriminate E1.
        -- injection E1 as EA1 Ek1. subst a1. subst ka.
           injection E2 as EA2 Ek2. subst a2. subst kb.
           assert (Hk0 : k0.(indirect_reader) = Low)
             by (eapply security_le_ind_low; [exact Hle_a | reflexivity]).
           destruct (evaluates_protect k0.(indirect_reader) (open (subst_all δ1 body2) v) v1 (conj Hmp1 Hv1)) as (w1 & Hevw1 & Hu1).
           rewrite Hk0 in Hu1. rewrite protect_value_low in Hu1.
           assert (Hk0' : k0'.(indirect_reader) = Low)
             by (eapply security_le_ind_low; [exact Hle_b | reflexivity]).
           destruct (evaluates_protect k0'.(indirect_reader) (open (subst_all δ2 body2) v') v2 (conj Hmp2 Hv2)) as (w2 & Hevw2 & Hu2).
           rewrite Hk0' in Hu2. rewrite protect_value_low in Hu2.
           destruct (fresh_atom (L ++ fv body1 ++ fv body2)) as [x Hx].
           assert (HxL : ~ In x L) by (intro Hc; apply Hx; apply In_three_l; exact Hc).
           assert (Hxf2 : ~ In x (fv body2)) by (intro Hc; apply Hx; apply In_three_r; exact Hc).
           assert (Henv' : env_rel (update Gamma0 x T2) (extend_env δ1 x v) (extend_env δ2 x v')).
           { apply env_rel_extend; [exact (conj Hlc HenvR) | exact Hv1c | exact Hv2c | exact HVA]. }
           pose proof (IHb2 x HxL (extend_env δ1 x v) (extend_env δ2 x v') Henv') as HRbody.
           rewrite (open_subst_all_extend δ1 x v body2 (value_lc v Hv1c) (fun y => proj1 (Hlc y)) Hxf2) in HRbody.
           rewrite (open_subst_all_extend δ2 x v' body2 (value_lc v' Hv2c) (fun y => proj2 (Hlc y)) Hxf2) in HRbody.
           rewrite Hu1, Hu2. apply HRbody; assumption.
    + apply V_protect_high.
  - (* T_Protect *)
    unfold R. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct (evaluates_protect l (subst_all δ1 t) v1 (conj Hm1 Hv1)) as (w1 & Hev1 & Hu1).
    destruct (evaluates_protect l (subst_all δ2 t) v2 (conj Hm2 Hv2)) as (w2 & Hev2 & Hu2).
    pose proof (IHt δ1 δ2 (conj Hlc HenvR)) as HR.
    pose proof (HR w1 w2 Hev1 Hev2) as HV.
    destruct l.
    + rewrite Hu1, Hu2. rewrite protect_value_low, protect_value_low.
      apply V_protect_low. exact HV.
    + rewrite Hu1, Hu2. apply V_protect_high.
  - (* T_Sub *)
    apply subtype_R with (T := T0).
    + exact Hsub.
    + apply IHt; exact (conj Hlc HenvR).
  - (* T_If *)
    unfold R. intros v1 v2 [Hm1 Hv1] [Hm2 Hv2].
    destruct k as [kr ki]; destruct ki.
    + apply V_protect_low.
      destruct (evaluates_if (subst_all δ1 c) (subst_all δ1 yes) (subst_all δ1 no) r v1 (conj Hm1 Hv1)) as [(v & k0 & Hm1c & Hv1c & Hfl1 & Hmp1) | (v & k0 & Hm1c & Hv1c & Hfl1 & Hmp1)];
      destruct (evaluates_if (subst_all δ2 c) (subst_all δ2 yes) (subst_all δ2 no) r v2 (conj Hm2 Hv2)) as [(v' & k0' & Hm2c & Hv2c & Hfl2 & Hmp2) | (v' & k0' & Hm2c & Hv2c & Hfl2 & Hmp2)].
      * (* inl / inl *)
        pose proof (IHc δ1 δ2 (conj Hlc HenvR)) as HRsum.
        pose proof (HRsum (tm_inl v k0) (tm_inl v' k0') (conj Hm1c (v_inl v k0 Hv1c)) (conj Hm2c (v_inl v' k0' Hv2c))) as HVsum.
        destruct (V_sum_inv (Ty_Unit public) (Ty_Unit public) {| reader := kr; indirect_reader := Low |} (tm_inl v k0) (tm_inl v' k0') eq_refl HVsum) as [(ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA) | (ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA)].
        -- injection E1 as EA1 Ek1. subst a1. subst ka.
           injection E2 as EA2 Ek2. subst a2. subst kb.
           assert (Hk0 : k0.(indirect_reader) = Low)
             by (eapply security_le_ind_low; [exact Hle_a | reflexivity]).
           destruct (evaluates_protect k0.(indirect_reader) (subst_all δ1 yes) v1 (conj Hmp1 Hv1)) as (w1 & Hevw1 & Hu1).
           rewrite Hk0 in Hu1. rewrite protect_value_low in Hu1.
           assert (Hk0' : k0'.(indirect_reader) = Low)
             by (eapply security_le_ind_low; [exact Hle_b | reflexivity]).
           destruct (evaluates_protect k0'.(indirect_reader) (subst_all δ2 yes) v2 (conj Hmp2 Hv2)) as (w2 & Hevw2 & Hu2).
           rewrite Hk0' in Hu2. rewrite protect_value_low in Hu2.
           rewrite Hu1, Hu2.
           apply (IHy δ1 δ2 (conj Hlc HenvR)); assumption.
        -- discriminate E2.
      * (* inl / inr *)
        pose proof (IHc δ1 δ2 (conj Hlc HenvR)) as HRsum.
        pose proof (HRsum (tm_inl v k0) (tm_inr v' k0') (conj Hm1c (v_inl v k0 Hv1c)) (conj Hm2c (v_inr v' k0' Hv2c))) as HVsum.
        destruct (V_sum_inv (Ty_Unit public) (Ty_Unit public) {| reader := kr; indirect_reader := Low |} (tm_inl v k0) (tm_inr v' k0') eq_refl HVsum) as [(ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA) | (ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA)].
        -- discriminate E2.
        -- discriminate E1.
      * (* inr / inl *)
        pose proof (IHc δ1 δ2 (conj Hlc HenvR)) as HRsum.
        pose proof (HRsum (tm_inr v k0) (tm_inl v' k0') (conj Hm1c (v_inr v k0 Hv1c)) (conj Hm2c (v_inl v' k0' Hv2c))) as HVsum.
        destruct (V_sum_inv (Ty_Unit public) (Ty_Unit public) {| reader := kr; indirect_reader := Low |} (tm_inr v k0) (tm_inl v' k0') eq_refl HVsum) as [(ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA) | (ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA)].
        -- discriminate E1.
        -- discriminate E2.
      * (* inr / inr *)
        pose proof (IHc δ1 δ2 (conj Hlc HenvR)) as HRsum.
        pose proof (HRsum (tm_inr v k0) (tm_inr v' k0') (conj Hm1c (v_inr v k0 Hv1c)) (conj Hm2c (v_inr v' k0' Hv2c))) as HVsum.
        destruct (V_sum_inv (Ty_Unit public) (Ty_Unit public) {| reader := kr; indirect_reader := Low |} (tm_inr v k0) (tm_inr v' k0') eq_refl HVsum) as [(ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA) | (ka & kb & a1 & a2 & E1 & E2 & Hle_a & Hle_b & HVA)].
        -- discriminate E1.
        -- injection E1 as EA1 Ek1. subst a1. subst ka.
           injection E2 as EA2 Ek2. subst a2. subst kb.
           assert (Hk0 : k0.(indirect_reader) = Low)
             by (eapply security_le_ind_low; [exact Hle_a | reflexivity]).
           destruct (evaluates_protect k0.(indirect_reader) (subst_all δ1 no) v1 (conj Hmp1 Hv1)) as (w1 & Hevw1 & Hu1).
           rewrite Hk0 in Hu1. rewrite protect_value_low in Hu1.
           assert (Hk0' : k0'.(indirect_reader) = Low)
             by (eapply security_le_ind_low; [exact Hle_b | reflexivity]).
           destruct (evaluates_protect k0'.(indirect_reader) (subst_all δ2 no) v2 (conj Hmp2 Hv2)) as (w2 & Hevw2 & Hu2).
           rewrite Hk0' in Hu2. rewrite protect_value_low in Hu2.
           rewrite Hu1, Hu2.
           apply (IHn δ1 δ2 (conj Hlc HenvR)); assumption.
    + apply V_protect_high.
Qed.

(* ================================================================ *)
(* Adequacy: related values of a ground, transparent type have the  *)
(* same erasure.                                                    *)
(* ================================================================ *)

Lemma adequacy_at : forall (T : ty) (v1 v2 : tm),
    ground T ->
    forall (κ : security),
      transparent_at κ T -> κ.(indirect_reader) = Low ->
      V T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  intros T; induction T as
      [κT | T1 IHT1 T2 IHT2 κT | T1 IHT1 T2 IHT2 κT | T1 IHT1 T2 IHT2 κT];
    intros v1 v2 Hg κ Htr Hk HV.
  - (* Unit *) simpl in Htr. destruct Htr as [Hle _].
    assert (Hlow : κT.(indirect_reader) = Low)
      by (eapply security_le_ind_low; [exact Hle | exact Hk]).
    destruct (V_unit_inv κT v1 v2 Hlow HV) as (κ1 & κ2 & E1 & E2).
    rewrite E1, E2. reflexivity.
  - (* Sum *) simpl in Htr. destruct Htr as [Hle [Htr1 Htr2]].
    assert (Hlow : κT.(indirect_reader) = Low)
      by (eapply security_le_ind_low; [exact Hle | exact Hk]).
    destruct (V_sum_inv T1 T2 κT v1 v2 Hlow HV) as
        [(κ1 & κ2 & a1 & a2 & E1 & E2 & Hsa & Hsb & HV1)
        | (κ1 & κ2 & a1 & a2 & E1 & E2 & Hsa & Hsb & HV1)].
    + rewrite E1, E2. simpl. rewrite (IHT1 a1 a2 (proj1 Hg) κ Htr1 Hk HV1). reflexivity.
    + rewrite E1, E2. simpl. rewrite (IHT2 a1 a2 (proj2 Hg) κ Htr2 Hk HV1). reflexivity.
  - (* Prod *) simpl in Htr. destruct Htr as [Hle [Htr1 Htr2]].
    assert (Hlow : κT.(indirect_reader) = Low)
      by (eapply security_le_ind_low; [exact Hle | exact Hk]).
    destruct (V_prod_inv T1 T2 κT v1 v2 Hlow HV) as
      (κ1 & κ2 & a1 & a2 & b1 & b2 & E1 & E2 & Hsa & Hsb & HVA & HVB).
    rewrite E1, E2. simpl.
    rewrite (IHT1 a1 a2 (proj1 Hg) κ Htr1 Hk HVA).
    rewrite (IHT2 b1 b2 (proj2 Hg) κ Htr2 Hk HVB). reflexivity.
  - (* Arrow *) simpl in Hg. destruct Hg.
Qed.

Lemma nflow_to_low : forall (l1 l2 : label),
    ~ flows_to l1 l2 -> l1 = High /\ l2 = Low.
Proof.
  destruct l1, l2; simpl; intros H.
  - exfalso; apply H; auto.
  - exfalso; apply H; auto.
  - split; reflexivity.
  - exfalso; apply H; auto.
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 HC Hg Htr Hni.
  destruct (nflow_to_low _ _ Hni) as [Hsi Hri].
  destruct HC as [L HL].
  destruct (fresh_atom (L ++ fv_ctx C)) as [x Hx].
  assert (HxL : ~ In x L) by (intro Hc; apply Hx; apply In_app_l; exact Hc).
  assert (HxC : ~ In x (fv_ctx C)) by (intro Hc; apply Hx; apply In_app_r; exact Hc).
  assert (Hty : has_type (update empty x T_secret) (plug C (tm_fvar x)) T_result)
    by (apply HL; exact HxL).
  set (δ1 := extend_env (fun y => tm_fvar y) x t1).
  set (δ2 := extend_env (fun y => tm_fvar y) x t2).
  assert (Hdx1 : δ1 x = t1).
  { unfold δ1, extend_env. simpl. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hdx2 : δ2 x = t2).
  { unfold δ2, extend_env. simpl. rewrite Nat.eqb_refl. reflexivity. }
  assert (Henv : env_rel (update empty x T_secret) δ1 δ2).
  { split.
    - intros y. destruct (Nat.eqb y x) eqn:E.
      + apply Nat.eqb_eq in E; subst y. rewrite Hdx1, Hdx2.
        split.
        * exact (has_type_lc empty t1 T_secret Ht1).
        * exact (has_type_lc empty t2 T_secret Ht2).
      + unfold δ1, δ2, extend_env. rewrite E. simpl. split; exact I.
    - intros y T' Hlook.
      destruct (Nat.eqb y x) eqn:E.
      + apply Nat.eqb_eq in E; subst y.
        unfold update in Hlook. simpl in Hlook.
        rewrite Nat.eqb_refl in Hlook. simpl in Hlook.
        injection Hlook as HT'. subst T'.
        rewrite Hdx1, Hdx2.
        intros w1 w2 _ _.
        apply V_high; exact Hsi.
      + unfold update in Hlook. simpl in Hlook. rewrite E in Hlook. discriminate Hlook.
  }
  pose proof (fundamental _ _ _ Hty δ1 δ2 Henv) as HR.
  assert (Hprem1 : forall y : atom, In y (fv_ctx C) -> δ1 y = tm_fvar y).
  { intros y Hy. unfold δ1, extend_env.
    assert (Hne : (y =? x) = false) by (apply Nat.eqb_neq; intro Hc; subst y; exact (HxC Hy)).
    rewrite Hne. reflexivity. }
  assert (Hprem2 : forall y : atom, In y (fv_ctx C) -> δ2 y = tm_fvar y).
  { intros y Hy. unfold δ2, extend_env.
    assert (Hne : (y =? x) = false) by (apply Nat.eqb_neq; intro Hc; subst y; exact (HxC Hy)).
    rewrite Hne. reflexivity. }
  assert (Hsub1 : subst_all δ1 (tm_fvar x) = t1).
  { unfold δ1, extend_env. simpl. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hsub2 : subst_all δ2 (tm_fvar x) = t2).
  { unfold δ2, extend_env. simpl. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hrew1 : subst_all δ1 (plug C (tm_fvar x)) = plug C t1).
  { rewrite (subst_all_plug δ1 C (tm_fvar x) Hprem1). rewrite Hsub1. reflexivity. }
  assert (Hrew2 : subst_all δ2 (plug C (tm_fvar x)) = plug C t2).
  { rewrite (subst_all_plug δ2 C (tm_fvar x) Hprem2). rewrite Hsub2. reflexivity. }
  rewrite Hrew1, Hrew2 in HR.
  intros v1 v2 Hev1 Hev2.
  apply (adequacy_at T_result v1 v2 Hg (security_of T_result) Htr Hri).
  apply HR; assumption.
Qed.
