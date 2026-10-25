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



(* ===================================================================== *)
(* Label algebra                                                          *)
(* ===================================================================== *)

Lemma flows_to_refl : forall l : label, flows_to l l.
Proof. intros []; simpl; auto. Qed.

Lemma flows_to_trans : forall a b c : label,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. intros [] [] [] H1 H2; simpl in *; auto. Qed.

Lemma flows_to_join_l : forall a b c : label,
  flows_to (join a b) c -> flows_to a c.
Proof. intros [] [] []; simpl; auto. Qed.

Lemma flows_to_join_r : forall a b c : label,
  flows_to (join a b) c -> flows_to b c.
Proof. intros [] [] []; simpl; auto. Qed.

Lemma flows_to_join : forall a b c : label,
  flows_to a c -> flows_to b c -> flows_to (join a b) c.
Proof. intros [] [] []; simpl; auto. Qed.

Lemma join_comm : forall a b : label, join a b = join b a.
Proof. intros [] []; reflexivity. Qed.

Lemma join_assoc : forall a b c : label,
  join (join a b) c = join a (join b c).
Proof. intros [] [] []; reflexivity. Qed.

Lemma join_idem : forall a : label, join a a = a.
Proof. intros []; reflexivity. Qed.

Lemma join_Low_r : forall a : label, join a Low = a.
Proof. intros []; reflexivity. Qed.

Lemma join_Low_l : forall a : label, join Low a = a.
Proof. intros []; reflexivity. Qed.

Lemma join_mono : forall a b c d : label,
  flows_to a b -> flows_to c d -> flows_to (join a c) (join b d).
Proof. intros [] [] [] []; simpl; auto. Qed.

Lemma flows_to_join_ab : forall a b : label, flows_to a (join a b).
Proof. intros [] []; simpl; auto. Qed.

Lemma flows_to_join_ba : forall a b : label, flows_to b (join a b).
Proof. intros [] []; simpl; auto. Qed.

Lemma flows_to_join_Low : forall a b : label,
  flows_to a b -> flows_to (join a Low) b.
Proof. intros; rewrite join_Low_r; exact H. Qed.

Lemma flows_to_join_r_mono : forall a b c : label,
  flows_to a b -> flows_to (join c a) (join c b).
Proof. intros; apply join_mono; auto using flows_to_refl. Qed.

Lemma flows_to_join_l_mono : forall a b c : label,
  flows_to a b -> flows_to (join a c) (join b c).
Proof. intros; apply join_mono; auto using flows_to_refl. Qed.

Lemma flows_to_false_iff : forall a b : label,
  (~ flows_to a b) <-> (a = High /\ b = Low).
Proof.
  intros a b; destruct a, b; simpl; split.
  - intros H; exfalso; apply H; exact I.
  - intros [H _]; discriminate H.
  - intros H; exfalso; apply H; exact I.
  - intros [H _]; discriminate H.
  - intros _; split; reflexivity.
  - intros [_ _] Hf; exact Hf.
  - intros H; exfalso; apply H; exact I.
  - intros [_ H]; discriminate H.
Qed.

(* ===================================================================== *)
(* Security algebra                                                       *)
(* ===================================================================== *)

Lemma protect_security_Low : forall k : security, protect_security k Low = k.
Proof. intros [r i]; destruct r, i; reflexivity. Qed.

Lemma protect_security_protect_Low : forall k j,
  protect_security (protect_security k j) Low = protect_security k j.
Proof. intros [r i] j; destruct r, i, j; reflexivity. Qed.

Lemma security_of_ty_protect : forall j T,
  security_of (ty_protect j T) = protect_security (security_of T) j.
Proof. intros j [k|T1 T2 k|T1 T2 k|T1 T2 k]; reflexivity. Qed.

Lemma security_le_refl : forall k, security_le k k.
Proof. intros [r i]; simpl; split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros [r1 i1] [r2 i2] [r3 i3] [H1 H2] [H3 H4]; simpl in *; split;
  eauto using flows_to_trans.
Qed.

Lemma security_le_protect_Low_inv : forall k1 k2,
  security_le k1 (protect_security k2 Low) -> security_le k1 k2.
Proof.
  intros [r1 i1] [r2 i2] H.
  unfold protect_security in H. cbn in H.
  rewrite !join_Low_r in H. exact H.
Qed.

Lemma security_le_protect : forall k j, security_le k (protect_security k j).
Proof. intros [r i] j; simpl; split; apply flows_to_join_ab. Qed.

Lemma security_le_protect_mono : forall k1 k2 j1 j2,
  security_le k1 k2 -> flows_to j1 j2 ->
  security_le (protect_security k1 j1) (protect_security k2 j2).
Proof.
  intros [r1 i1] [r2 i2] j1 j2 [H1 H2] H3; simpl in *; split;
  apply join_mono; auto.
Qed.

(* ===================================================================== *)
(* Values                                                                 *)
(* ===================================================================== *)

Lemma value_no_step : forall (v t : tm), value v -> v --> t -> False.
Proof.
  intros v t Hv Hs; revert t Hs; induction Hv; intros t Hs; inversion Hs; subst; eauto.
Qed.

Lemma step_abs_false : forall T body k t, ~ (tm_abs T body k --> t).
Proof. intros T body k t H; inversion H. Qed.

Lemma value_protect_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv; destruct Hv as [k | T body k Hlc | v1 v2 k H1 H2 | v1 k H1 | v1 k H1]; simpl.
  - apply v_unit.
  - apply v_abs; exact Hlc.
  - apply v_pair; auto.
  - apply v_inl; auto.
  - apply v_inr; auto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv; induction Hv.
  - unfold locally_closed; simpl; auto.
  - exact H.
  - unfold locally_closed in *; simpl in *; auto.
  - unfold locally_closed in *; simpl in *; auto.
  - unfold locally_closed in *; simpl in *; auto.
Qed.

Lemma multi_value : forall t v, multi t v -> value t -> v = t.
Proof.
  intros t v Hm; induction Hm as [| t1 t2 t3 Hstep Hm IH]; intros Hv.
  - reflexivity.
  - exfalso; exact (value_no_step t1 t2 Hv Hstep).
Qed.

Lemma multi_abs : forall T body k v, multi (tm_abs T body k) v -> v = tm_abs T body k.
Proof.
  intros T body k v Hm.
  remember (tm_abs T body k) as u eqn:Hu.
  revert Hu.
  induction Hm as [| a b c Hstep Hm IH]; intros Hu.
  - subst; reflexivity.
  - subst a; exfalso; exact (step_abs_false T body k b Hstep).
Qed.

Lemma multi_unit : forall k v, multi (tm_unit k) v -> v = tm_unit k.
Proof.
  intros k v Hm.
  remember (tm_unit k) as u eqn:Hu.
  revert Hu.
  induction Hm as [| a b c Hstep Hm IH]; intros Hu.
  - subst; reflexivity.
  - subst a; exfalso; inversion Hstep.
Qed.

(* ===================================================================== *)
(* Single-step inversion                                                  *)
(* ===================================================================== *)

Lemma step_protect_inv : forall l t t',
  tm_protect l t --> t' ->
  (exists v, t = v /\ value v /\ t' = protect_value v l)
  \/ (exists t1, t --> t1 /\ t' = tm_protect l t1).
Proof. intros l t t' H; inversion H; eauto. Qed.

Lemma step_app_inv : forall t1 t2 r t',
  tm_app t1 t2 r --> t' ->
  (exists T body kappa v,
      t1 = tm_abs T body kappa /\ value (tm_abs T body kappa) /\
      t2 = v /\ value v /\ flows_to kappa.(reader) r /\
      t' = tm_protect kappa.(indirect_reader) (open body v))
  \/ (exists t1', t1 --> t1' /\ t' = tm_app t1' t2 r)
  \/ (exists v1 t2', t1 = v1 /\ value v1 /\ t2 --> t2' /\ t' = tm_app v1 t2' r).
Proof.
  intros; inversion H; subst.
  - left; eexists T, body, kappa, t2; repeat split; eauto.
  - right; left; eauto 10.
  - right; right; eauto 10.
Qed.

Lemma step_pair_inv : forall t1 t2 k t',
  tm_pair t1 t2 k --> t' ->
  (exists t1', t1 --> t1' /\ t' = tm_pair t1' t2 k)
  \/ (exists v1 t2', t1 = v1 /\ value v1 /\ t2 --> t2' /\ t' = tm_pair v1 t2' k).
Proof.
  intros; inversion H; subst.
  - left; eauto 10.
  - right; eauto 10.
Qed.

Lemma step_fst_inv : forall t r t',
  tm_fst t r --> t' ->
  (exists v1 v2 k, t = tm_pair v1 v2 k /\ value v1 /\ value v2 /\
                   flows_to k.(reader) r /\ t' = tm_protect k.(indirect_reader) v1)
  \/ (exists t1, t --> t1 /\ t' = tm_fst t1 r).
Proof.
  intros; inversion H; subst.
  - left; eauto 10.
  - right; eauto 10.
Qed.

Lemma step_snd_inv : forall t r t',
  tm_snd t r --> t' ->
  (exists v1 v2 k, t = tm_pair v1 v2 k /\ value v1 /\ value v2 /\
                   flows_to k.(reader) r /\ t' = tm_protect k.(indirect_reader) v2)
  \/ (exists t1, t --> t1 /\ t' = tm_snd t1 r).
Proof.
  intros; inversion H; subst.
  - left; eauto 10.
  - right; eauto 10.
Qed.

Lemma step_inl_inv : forall t k t',
  tm_inl t k --> t' -> exists t1, t --> t1 /\ t' = tm_inl t1 k.
Proof. intros; inversion H; subst; eauto. Qed.

Lemma step_inr_inv : forall t k t',
  tm_inr t k --> t' -> exists t1, t --> t1 /\ t' = tm_inr t1 k.
Proof. intros; inversion H; subst; eauto. Qed.

Lemma step_case_inv : forall t b1 b2 r t',
  tm_case t b1 b2 r --> t' ->
  (exists v k, t = tm_inl v k /\ value v /\ flows_to k.(reader) r /\
               t' = tm_protect k.(indirect_reader) (open b1 v))
  \/ (exists v k, t = tm_inr v k /\ value v /\ flows_to k.(reader) r /\
                  t' = tm_protect k.(indirect_reader) (open b2 v))
  \/ (exists t1, t --> t1 /\ t' = tm_case t1 b1 b2 r).
Proof.
  intros; inversion H; subst.
  - left; eauto 10.
  - right; left; eauto 10.
  - right; right; eauto 10.
Qed.

Lemma step_if_inv : forall c y n r t',
  tm_if c y n r --> t' ->
  (exists v k, c = tm_inl v k /\ value v /\ flows_to k.(reader) r /\
               t' = tm_protect k.(indirect_reader) y)
  \/ (exists v k, c = tm_inr v k /\ value v /\ flows_to k.(reader) r /\
                  t' = tm_protect k.(indirect_reader) n)
  \/ (exists c1, c --> c1 /\ t' = tm_if c1 y n r).
Proof.
  intros; inversion H; subst.
  - right; right; eauto 10.
  - left; eauto 10.
  - right; left; eauto 10.
Qed.

(* ===================================================================== *)
(* Multi-step inversion                                                   *)
(* ===================================================================== *)

Lemma multi_protect_gen : forall s u,
  multi s u -> value u ->
  forall l e, s = tm_protect l e ->
  exists v, multi e v /\ value v /\ u = protect_value v l.
Proof.
  intros s u Hm; induction Hm as [a0 | a b c Hstep Hm IH]; intros Hv l e Hs.
  - subst a0; inversion Hv.
  - subst a.
    destruct (step_protect_inv l e b Hstep) as [[v [He [Hvv Hb]]] | [e' [Hstep' Hb]]].
    + subst e. exists v. split; [apply multi_refl | split; [exact Hvv | ]].
      rewrite Hb in Hm.
      apply (multi_value (protect_value v l) c Hm (value_protect_value v l Hvv)).
    + subst b.
      destruct (IH Hv l e' eq_refl) as [v [Hm' [Hvv Hu]]].
      exists v. split; [|split]; auto. eapply multi_step; eauto.
Qed.

Lemma multi_protect_inv : forall l e u,
  multi (tm_protect l e) u -> value u ->
  exists v, multi e v /\ value v /\ u = protect_value v l.
Proof. intros; eapply multi_protect_gen; eauto. Qed.

Lemma multi_protect_value : forall l e v,
  multi e v -> value v -> multi (tm_protect l e) (protect_value v l).
Proof.
  intros l e v Hm; induction Hm as [a0 | a b c Hstep Hm IH]; intros Hv.
  - apply multi_step with (t2 := protect_value a0 l); [apply ST_ProtectValue; exact Hv | apply multi_refl].
  - eapply multi_step; [apply ST_Protect; exact Hstep | apply IH; exact Hv].
Qed.

Lemma multi_app_gen : forall s u,
  multi s u -> value u ->
  forall e1 e2 r, s = tm_app e1 e2 r ->
  exists v1 w1, multi e1 v1 /\ value v1 /\ multi e2 w1 /\ value w1 /\
                multi (tm_app v1 w1 r) u.
Proof.
  intros s u Hm; induction Hm as [a0 | a b c Hstep Hm IH]; intros Hv e1 e2 r Hs.
  - subst a0; inversion Hv.
  - subst a.
    destruct (step_app_inv e1 e2 r b Hstep)
      as [[T [body [k [v [He1 [Hvabs [He2 [Hv2 [Hflow Hb]]]]]]]]]
         | [[e1' [Hstep' Hb]] | [v1' [e2' [He1 [Hv1 [Hstep' Hb]]]]]]].
    + subst e1; subst e2; subst b.
      exists (tm_abs T body k), v. split; [apply multi_refl | split; [exact Hvabs | ]].
      split; [apply multi_refl | split; [exact Hv2 | ]].
      eapply multi_step; [apply ST_AppAbs; eauto | exact Hm].
    + subst b.
      destruct (IH Hv e1' e2 r eq_refl) as [v1 [w1 [Hm1 [Hval1 [Hm2 [Hval2 Hmapp]]]]]].
      exists v1, w1.
      split; [eapply multi_step; eauto | split; [exact Hval1 | split; [exact Hm2 | split; [exact Hval2 | exact Hmapp]]]].
    + subst b; subst e1.
      destruct (IH Hv v1' e2' r eq_refl) as [v1 [w1 [Hm1 [Hval1 [Hm2 [Hval2 Hmapp]]]]]].
      exists v1, w1.
      split; [exact Hm1 | split; [exact Hval1 | split; [eapply multi_step; eauto | split; [exact Hval2 | exact Hmapp]]]].
Qed.

Lemma multi_app_inv : forall e1 e2 r u,
  multi (tm_app e1 e2 r) u -> value u ->
  exists v1 w1, multi e1 v1 /\ value v1 /\ multi e2 w1 /\ value w1 /\
                multi (tm_app v1 w1 r) u.
Proof. intros; eapply multi_app_gen; eauto. Qed.

Lemma multi_app_abs_gen : forall s u,
  multi s u -> value u ->
  forall T body k w r, s = tm_app (tm_abs T body k) w r -> value w ->
  exists v, multi (open body w) v /\ value v /\ u = protect_value v k.(indirect_reader).
Proof.
  intros s u Hm; induction Hm as [a0 | a b c Hstep Hm IH]; intros Hv T body k w r Hs Hvw.
  - subst a0; inversion Hv.
  - subst a.
    destruct (step_app_inv (tm_abs T body k) w r b Hstep)
      as [[T0 [body0 [k0 [v [He1 [Hvabs [He2 [Hv2 [Hflow Hb]]]]]]]]]
         | [[e1' [Hstep' Hb]] | [v1' [e2' [He1 [Hv1 [Hstep' Hb]]]]]]].
    + injection He1 as HT Hbody Hk.
      subst T0 body0 k0.
      subst v.
      rewrite Hb in Hm.
      destruct (multi_protect_inv k.(indirect_reader) (open body w) c Hm Hv)
        as [v0 [Hm' [Hvv Hu]]].
      exists v0; split; [|split]; auto.
    + exfalso; exact (step_abs_false T body k e1' Hstep').
    + exfalso; exact (value_no_step w e2' Hvw Hstep').
Qed.

Lemma multi_app_abs_inv : forall T body k w r u,
  value w ->
  multi (tm_app (tm_abs T body k) w r) u -> value u ->
  exists v, multi (open body w) v /\ value v /\ u = protect_value v k.(indirect_reader).
Proof. intros; eapply multi_app_abs_gen; eauto. Qed.



Lemma multi_pair_gen : forall s u,
  multi s u -> value u ->
  forall e1 e2 k, s = tm_pair e1 e2 k ->
  exists v1 v2, multi e1 v1 /\ value v1 /\ multi e2 v2 /\ value v2 /\ u = tm_pair v1 v2 k.
Proof.
  intros s u Hm; induction Hm as [a0 | a b c Hstep Hm IH]; intros Hv e1 e2 k Hs.
  - subst a0; inversion Hv; subst.
    exists e1, e2. split; [apply multi_refl | split; [assumption | split; [apply multi_refl | split; [assumption | reflexivity]]]].
  - subst a.
    destruct (step_pair_inv e1 e2 k b Hstep)
      as [[e1' [Hstep' Hb]] | [v1' [e2' [He1 [Hv1 [Hstep' Hb]]]]]].
    + subst b.
      destruct (IH Hv e1' e2 k eq_refl) as [v1 [v2 [Hm1 [Hval1 [Hm2 [Hval2 Hu]]]]]].
      exists v1, v2. split; [eapply multi_step; eauto | split; [exact Hval1 | split; [exact Hm2 | split; [exact Hval2 | exact Hu]]]].
    + subst b; subst e1.
      destruct (IH Hv v1' e2' k eq_refl) as [v1 [v2 [Hm1 [Hval1 [Hm2 [Hval2 Hu]]]]]].
      exists v1, v2. split; [exact Hm1 | split; [exact Hval1 | split; [eapply multi_step; eauto | split; [exact Hval2 | exact Hu]]]].
Qed.

Lemma multi_pair_inv : forall e1 e2 k u,
  multi (tm_pair e1 e2 k) u -> value u ->
  exists v1 v2, multi e1 v1 /\ value v1 /\ multi e2 v2 /\ value v2 /\ u = tm_pair v1 v2 k.
Proof. intros; eapply multi_pair_gen; eauto. Qed.

Lemma multi_fst_gen : forall s u,
  multi s u -> value u ->
  forall e r, s = tm_fst e r ->
  exists v1 v2 k, multi e (tm_pair v1 v2 k) /\ value v1 /\ value v2 /\
                 flows_to k.(reader) r /\ u = protect_value v1 k.(indirect_reader).
Proof.
  intros s u Hm; induction Hm as [a0 | a b c Hstep Hm IH]; intros Hv e r Hs.
  - subst a0; inversion Hv.
  - subst a.
    destruct (step_fst_inv e r b Hstep)
      as [[v1 [v2 [k [He [Hv1 [Hv2 [Hflow Hb]]]]]]] | [e' [Hstep' Hb]]].
    + subst e; subst b.
      destruct (multi_protect_inv k.(indirect_reader) v1 c Hm Hv) as [v0 [Hm1 [Hv0 Hu]]].
      assert (Hveq : v0 = v1) by (apply (multi_value v1 v0 Hm1); exact Hv1).
      subst v0.
      exists v1, v2, k. split; [apply multi_refl | split; [exact Hv1 | split; [exact Hv2 | split; [exact Hflow | exact Hu]]]].
    + subst b.
      destruct (IH Hv e' r eq_refl) as [v1 [v2 [k [Hm' [Hv1 [Hv2 [Hflow Hu]]]]]]].
      exists v1, v2, k. split; [eapply multi_step; eauto | split; [exact Hv1 | split; [exact Hv2 | split; [exact Hflow | exact Hu]]]].
Qed.

Lemma multi_fst_inv : forall e r u,
  multi (tm_fst e r) u -> value u ->
  exists v1 v2 k, multi e (tm_pair v1 v2 k) /\ value v1 /\ value v2 /\
                 flows_to k.(reader) r /\ u = protect_value v1 k.(indirect_reader).
Proof. intros; eapply multi_fst_gen; eauto. Qed.

Lemma multi_snd_gen : forall s u,
  multi s u -> value u ->
  forall e r, s = tm_snd e r ->
  exists v1 v2 k, multi e (tm_pair v1 v2 k) /\ value v1 /\ value v2 /\
                 flows_to k.(reader) r /\ u = protect_value v2 k.(indirect_reader).
Proof.
  intros s u Hm; induction Hm as [a0 | a b c Hstep Hm IH]; intros Hv e r Hs.
  - subst a0; inversion Hv.
  - subst a.
    destruct (step_snd_inv e r b Hstep)
      as [[v1 [v2 [k [He [Hv1 [Hv2 [Hflow Hb]]]]]]] | [e' [Hstep' Hb]]].
    + subst e; subst b.
      destruct (multi_protect_inv k.(indirect_reader) v2 c Hm Hv) as [v0 [Hm1 [Hv0 Hu]]].
      assert (Hveq : v0 = v2) by (apply (multi_value v2 v0 Hm1); exact Hv2).
      subst v0.
      exists v1, v2, k. split; [apply multi_refl | split; [exact Hv1 | split; [exact Hv2 | split; [exact Hflow | exact Hu]]]].
    + subst b.
      destruct (IH Hv e' r eq_refl) as [v1 [v2 [k [Hm' [Hv1 [Hv2 [Hflow Hu]]]]]]].
      exists v1, v2, k. split; [eapply multi_step; eauto | split; [exact Hv1 | split; [exact Hv2 | split; [exact Hflow | exact Hu]]]].
Qed.

Lemma multi_snd_inv : forall e r u,
  multi (tm_snd e r) u -> value u ->
  exists v1 v2 k, multi e (tm_pair v1 v2 k) /\ value v1 /\ value v2 /\
                 flows_to k.(reader) r /\ u = protect_value v2 k.(indirect_reader).
Proof. intros; eapply multi_snd_gen; eauto. Qed.

Lemma multi_inl_gen : forall s u,
  multi s u -> value u -> forall e k, s = tm_inl e k ->
  exists v, multi e v /\ value v /\ u = tm_inl v k.
Proof.
  intros s u Hm; induction Hm as [a0 | a b c Hstep Hm IH]; intros Hv e k Hs.
  - subst a0; inversion Hv; subst.
    exists e; split; [apply multi_refl | split; [assumption | reflexivity]].
  - subst a.
    destruct (step_inl_inv e k b Hstep) as [e' [Hstep' Hb]].
    subst b. destruct (IH Hv e' k eq_refl) as [v [Hm' [Hvv Hu]]].
    exists v; split; [eapply multi_step; eauto | split; [exact Hvv | exact Hu]].
Qed.

Lemma multi_inl_inv : forall e k u,
  multi (tm_inl e k) u -> value u -> exists v, multi e v /\ value v /\ u = tm_inl v k.
Proof. intros; eapply multi_inl_gen; eauto. Qed.

Lemma multi_inr_gen : forall s u,
  multi s u -> value u -> forall e k, s = tm_inr e k ->
  exists v, multi e v /\ value v /\ u = tm_inr v k.
Proof.
  intros s u Hm; induction Hm as [a0 | a b c Hstep Hm IH]; intros Hv e k Hs.
  - subst a0; inversion Hv; subst.
    exists e; split; [apply multi_refl | split; [assumption | reflexivity]].
  - subst a.
    destruct (step_inr_inv e k b Hstep) as [e' [Hstep' Hb]].
    subst b. destruct (IH Hv e' k eq_refl) as [v [Hm' [Hvv Hu]]].
    exists v; split; [eapply multi_step; eauto | split; [exact Hvv | exact Hu]].
Qed.

Lemma multi_inr_inv : forall e k u,
  multi (tm_inr e k) u -> value u -> exists v, multi e v /\ value v /\ u = tm_inr v k.
Proof. intros; eapply multi_inr_gen; eauto. Qed.

Lemma multi_case_gen : forall s u,
  multi s u -> value u ->
  forall e b1 b2 r, s = tm_case e b1 b2 r ->
  (exists v k, multi e (tm_inl v k) /\ value v /\ flows_to k.(reader) r /\
               exists w, multi (open b1 v) w /\ value w /\ u = protect_value w k.(indirect_reader))
  \/ (exists v k, multi e (tm_inr v k) /\ value v /\ flows_to k.(reader) r /\
               exists w, multi (open b2 v) w /\ value w /\ u = protect_value w k.(indirect_reader)).
Proof.
  intros s u Hm; induction Hm as [a0 | a b c Hstep Hm IH]; intros Hv e b1 b2 r Hs.
  - subst a0; inversion Hv.
  - subst a.
    destruct (step_case_inv e b1 b2 r b Hstep)
      as [[v [k [He [Hv' [Hflow Hb]]]]] |
          [[v [k [He [Hv' [Hflow Hb]]]]] | [e' [Hstep' Hb]]]].
    + subst e; subst b.
      destruct (multi_protect_inv k.(indirect_reader) (open b1 v) c Hm Hv) as [w [Hm' [Hvv Hu]]].
      left. exists v, k. split; [apply multi_refl | split; [exact Hv' | split; [exact Hflow | exists w; split; [exact Hm' | split; [exact Hvv | exact Hu]]]]].
    + subst e; subst b.
      destruct (multi_protect_inv k.(indirect_reader) (open b2 v) c Hm Hv) as [w [Hm' [Hvv Hu]]].
      right. exists v, k. split; [apply multi_refl | split; [exact Hv' | split; [exact Hflow | exists w; split; [exact Hm' | split; [exact Hvv | exact Hu]]]]].
    + subst b.
      destruct (IH Hv e' b1 b2 r eq_refl)
        as [[v [k [Hm' [Hv' [Hflow [w [Hmw [Hvw Hu]]]]]]]] |
            [v [k [Hm' [Hv' [Hflow [w [Hmw [Hvw Hu]]]]]]]]].
      * left. exists v, k. split; [eapply multi_step; eauto | split; [exact Hv' | split; [exact Hflow | exists w; split; [exact Hmw | split; [exact Hvw | exact Hu]]]]].
      * right. exists v, k. split; [eapply multi_step; eauto | split; [exact Hv' | split; [exact Hflow | exists w; split; [exact Hmw | split; [exact Hvw | exact Hu]]]]].
Qed.

Lemma multi_case_inv : forall e b1 b2 r u,
  multi (tm_case e b1 b2 r) u -> value u ->
  (exists v k, multi e (tm_inl v k) /\ value v /\ flows_to k.(reader) r /\
               exists w, multi (open b1 v) w /\ value w /\ u = protect_value w k.(indirect_reader))
  \/ (exists v k, multi e (tm_inr v k) /\ value v /\ flows_to k.(reader) r /\
               exists w, multi (open b2 v) w /\ value w /\ u = protect_value w k.(indirect_reader)).
Proof. intros; eapply multi_case_gen; eauto. Qed.

Lemma multi_if_gen : forall s u,
  multi s u -> value u ->
  forall c y n r, s = tm_if c y n r ->
  (exists v k, multi c (tm_inl v k) /\ value v /\ flows_to k.(reader) r /\
               exists w, multi y w /\ value w /\ u = protect_value w k.(indirect_reader))
  \/ (exists v k, multi c (tm_inr v k) /\ value v /\ flows_to k.(reader) r /\
               exists w, multi n w /\ value w /\ u = protect_value w k.(indirect_reader)).
Proof.
  intros s u Hm; induction Hm as [a0 | a b c0 Hstep Hm IH]; intros Hv c y n r Hs.
  - subst a0; inversion Hv.
  - subst a.
    destruct (step_if_inv c y n r b Hstep)
      as [[v [k [Hc [Hv' [Hflow Hb]]]]] |
          [[v [k [Hc [Hv' [Hflow Hb]]]]] | [c' [Hstep' Hb]]]].
    + subst c; subst b.
      destruct (multi_protect_inv k.(indirect_reader) y c0 Hm Hv) as [w [Hm' [Hvv Hu]]].
      left. exists v, k. split; [apply multi_refl | split; [exact Hv' | split; [exact Hflow | exists w; split; [exact Hm' | split; [exact Hvv | exact Hu]]]]].
    + subst c; subst b.
      destruct (multi_protect_inv k.(indirect_reader) n c0 Hm Hv) as [w [Hm' [Hvv Hu]]].
      right. exists v, k. split; [apply multi_refl | split; [exact Hv' | split; [exact Hflow | exists w; split; [exact Hm' | split; [exact Hvv | exact Hu]]]]].
    + subst b.
      destruct (IH Hv c' y n r eq_refl)
        as [[v [k [Hm' [Hv' [Hflow [w [Hmw [Hvw Hu]]]]]]]] |
            [v [k [Hm' [Hv' [Hflow [w [Hmw [Hvw Hu]]]]]]]]].
      * left. exists v, k. split; [eapply multi_step; eauto | split; [exact Hv' | split; [exact Hflow | exists w; split; [exact Hmw | split; [exact Hvw | exact Hu]]]]].
      * right. exists v, k. split; [eapply multi_step; eauto | split; [exact Hv' | split; [exact Hflow | exists w; split; [exact Hmw | split; [exact Hvw | exact Hu]]]]].
Qed.

Lemma multi_if_inv : forall c y n r u,
  multi (tm_if c y n r) u -> value u ->
  (exists v k, multi c (tm_inl v k) /\ value v /\ flows_to k.(reader) r /\
               exists w, multi y w /\ value w /\ u = protect_value w k.(indirect_reader))
  \/ (exists v k, multi c (tm_inr v k) /\ value v /\ flows_to k.(reader) r /\
               exists w, multi n w /\ value w /\ u = protect_value w k.(indirect_reader)).
Proof. intros; eapply multi_if_gen; eauto. Qed.

(* ===================================================================== *)
(* Substitution                                                           *)
(* ===================================================================== *)

Fixpoint subst_rho (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit k => tm_unit k
  | tm_abs T body k => tm_abs T (subst_rho rho body) k
  | tm_app t1 t2 r => tm_app (subst_rho rho t1) (subst_rho rho t2) r
  | tm_pair t1 t2 k => tm_pair (subst_rho rho t1) (subst_rho rho t2) k
  | tm_fst t1 r => tm_fst (subst_rho rho t1) r
  | tm_snd t1 r => tm_snd (subst_rho rho t1) r
  | tm_inl t1 k => tm_inl (subst_rho rho t1) k
  | tm_inr t1 k => tm_inr (subst_rho rho t1) k
  | tm_case t0 b1 b2 r =>
      tm_case (subst_rho rho t0) (subst_rho rho b1) (subst_rho rho b2) r
  | tm_protect l t1 => tm_protect l (subst_rho rho t1)
  | tm_if c y n r => tm_if (subst_rho rho c) (subst_rho rho y) (subst_rho rho n) r
  end.

Definition extend_rho (rho : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else rho y.

Definition id_rho : atom -> tm := fun y => tm_fvar y.

Lemma subst_rho_agree : forall t rho1 rho2,
  (forall x, In x (fv t) -> rho1 x = rho2 x) ->
  subst_rho rho1 t = subst_rho rho2 t.
Proof.
  induction t as [i | x | k | T body IHbody kb | t1 IH1 t2 IH2 r
                 | t1 IH1 t2 IH2 k | t1 IH1 r | t1 IH1 r | t1 IH1 k | t1 IH1 k
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y IHy n IHn r];
    intros rho1 rho2 Hagree; simpl in *.
  - reflexivity.
  - apply Hagree; simpl; auto.
  - reflexivity.
  - f_equal. apply IHbody. intros y Hy. apply Hagree. simpl; auto.
  - f_equal.
    + apply IH1. intros y Hy. apply Hagree. simpl; rewrite in_app_iff; left; exact Hy.
    + apply IH2. intros y Hy. apply Hagree. simpl; auto with datatypes.
  - f_equal.
    + apply IH1. intros y Hy. apply Hagree. simpl; rewrite in_app_iff; left; exact Hy.
    + apply IH2. intros y Hy. apply Hagree. simpl; auto with datatypes.
  - f_equal. apply IH1. intros y Hy. apply Hagree. simpl; auto.
  - f_equal. apply IH1. intros y Hy. apply Hagree. simpl; auto.
  - f_equal. apply IH1. intros y Hy. apply Hagree. simpl; auto.
  - f_equal. apply IH1. intros y Hy. apply Hagree. simpl; auto.
  - f_equal.
    + apply IH0. intros y Hy. apply Hagree. simpl; auto with datatypes.
    + apply IH1. intros y Hy. apply Hagree. simpl; auto with datatypes.
    + apply IH2. intros y Hy. apply Hagree. simpl; auto with datatypes.
  - f_equal. apply IH1. intros y Hy. apply Hagree. simpl; auto.
  - f_equal.
    + apply IHc. intros y0 Hy0. apply Hagree. simpl; auto with datatypes.
    + apply IHy. intros y0 Hy0. apply Hagree. simpl; auto with datatypes.
    + apply IHn. intros y0 Hy0. apply Hagree. simpl; auto with datatypes.
Qed.

Lemma subst_rho_id : forall t, subst_rho id_rho t = t.
Proof.
  induction t as [i | x | k | T body IHbody kb | t1 IH1 t2 IH2 r
                 | t1 IH1 t2 IH2 k | t1 IH1 r | t1 IH1 r | t1 IH1 k | t1 IH1 k
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y IHy n IHn r];
    simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal; exact IHbody.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; exact IH1.
  - f_equal; exact IH1.
  - f_equal; exact IH1.
  - f_equal; exact IH1.
  - f_equal; assumption.
  - f_equal; exact IH1.
  - f_equal; assumption.
Qed.

Lemma open_rec_lc_at : forall t k' k u, lc_at k' t -> k' <= k -> open_rec k u t = t.
Proof.
  induction t as [i | x | kb | T body IHbody kb | t1 IH1 t2 IH2 r
                 | t1 IH1 t2 IH2 kb | t1 IH1 r | t1 IH1 r | t1 IH1 kb | t1 IH1 kb
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y IHy n IHn r];
    intros k' k u Hlc Hle; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. apply (IHbody (S k') (S k) u); [exact Hlc | lia].
  - destruct Hlc as [H1 H2]. f_equal.
    + apply (IH1 k' k u); auto.
    + apply (IH2 k' k u); auto.
  - destruct Hlc as [H1 H2]. f_equal.
    + apply (IH1 k' k u); auto.
    + apply (IH2 k' k u); auto.
  - f_equal. apply (IH1 k' k u); auto.
  - f_equal. apply (IH1 k' k u); auto.
  - f_equal. apply (IH1 k' k u); auto.
  - f_equal. apply (IH1 k' k u); auto.
  - destruct Hlc as [H1 [H2 H3]]. f_equal.
    + apply (IH0 k' k u); auto.
    + apply (IH1 (S k') (S k) u); [exact H2 | lia].
    + apply (IH2 (S k') (S k) u); [exact H3 | lia].
  - f_equal. apply (IH1 k' k u); auto.
  - destruct Hlc as [H1 [H2 H3]]. f_equal.
    + apply (IHc k' k u); auto.
    + apply (IHy k' k u); auto.
    + apply (IHn k' k u); auto.
Qed.

Lemma open_rec_lc : forall t, locally_closed t -> forall k u, open_rec k u t = t.
Proof. intros t H k u. exact (open_rec_lc_at t 0 k u H (Nat.le_0_l k)). Qed.

Lemma subst_rho_open_rec : forall body rho k x,
  (forall y, locally_closed (rho y)) ->
  subst_rho rho (open_rec k (tm_fvar x) body) = open_rec k (rho x) (subst_rho rho body).
Proof.
  induction body as [i | y | kb | T b IHbody kb | t1 IH1 t2 IH2 r
                 | t1 IH1 t2 IH2 kb | t1 IH1 r | t1 IH1 r | t1 IH1 kb | t1 IH1 kb
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y IHy n IHn r];
    intros rho k x Hrho; simpl in *.
  - destruct (Nat.eqb k i); reflexivity.
  - rewrite (open_rec_lc (rho y) (Hrho y) k (rho x)). reflexivity.
  - reflexivity.
  - f_equal. apply IHbody. exact Hrho.
  - f_equal.
    + apply IH1. exact Hrho.
    + apply IH2. exact Hrho.
  - f_equal.
    + apply IH1. exact Hrho.
    + apply IH2. exact Hrho.
  - f_equal. apply IH1. exact Hrho.
  - f_equal. apply IH1. exact Hrho.
  - f_equal. apply IH1. exact Hrho.
  - f_equal. apply IH1. exact Hrho.
  - f_equal.
    + apply IH0. exact Hrho.
    + apply IH1. exact Hrho.
    + apply IH2. exact Hrho.
  - f_equal. apply IH1. exact Hrho.
  - f_equal.
    + apply IHc. exact Hrho.
    + apply IHy. exact Hrho.
    + apply IHn. exact Hrho.
Qed.

Lemma lc_at_open_inv : forall body k x,
  lc_at k (open_rec k (tm_fvar x) body) -> lc_at (S k) body.
Proof.
  induction body as [i | y | kb | T b IHbody kb | t1 IH1 t2 IH2 r
                 | t1 IH1 t2 IH2 kb | t1 IH1 r | t1 IH1 r | t1 IH1 kb | t1 IH1 kb
                 | t0 IH0 b1 IH1 b2 IH2 r | l t1 IH1 | c IHc y IHy n IHn r];
    intros k x H; simpl in *.
  - destruct (Nat.eqb k i) eqn:E; simpl in *.
    + apply Nat.eqb_eq in E; lia.
    + apply Nat.eqb_neq in E; lia.
  - auto.
  - auto.
  - apply (IHbody (S k) x). exact H.
  - destruct H as [H1 H2]. split.
    + apply (IH1 k x). exact H1.
    + apply (IH2 k x). exact H2.
  - destruct H as [H1 H2]. split.
    + apply (IH1 k x). exact H1.
    + apply (IH2 k x). exact H2.
  - apply (IH1 k x). exact H.
  - apply (IH1 k x). exact H.
  - apply (IH1 k x). exact H.
  - apply (IH1 k x). exact H.
  - destruct H as [H1 [H2 H3]]. split.
    + apply (IH0 k x). exact H1.
    + split.
      * apply (IH1 (S k) x). exact H2.
      * apply (IH2 (S k) x). exact H3.
  - apply (IH1 k x). exact H.
  - destruct H as [H1 [H2 H3]]. split.
    + apply (IHc k x). exact H1.
    + split.
      * apply (IHy k x). exact H2.
      * apply (IHn k x). exact H3.
Qed.

Fixpoint max_list (L : list nat) : nat :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_list L')
  end.

Lemma max_list_spec : forall L x, In x L -> x <= max_list L.
Proof.
  induction L as [| a L' IH]; intros x Hx.
  - inversion Hx.
  - simpl in *. destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hx | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (max_list L)). intros Hx.
  apply max_list_spec in Hx. lia.
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T H.
  induction H as [Gamma0 x0 T0 Hlook Hwf
                 | Gamma0 k0 Hwf
                 | L0 Gamma0 T1 body T2 kappa0 HwfT1 HwfK Hbody IHbody
                 | Gamma0 t1 t2 T1 T2 kappa0 r0 H1 IH1 H2 IH2 Hflow
                 | Gamma0 t1 t2 T1 T2 kappa0 H1 IH1 H2 IH2 HwfK
                 | Gamma0 t T1 T2 kappa0 r0 H1 IH1 Hflow
                 | Gamma0 t T1 T2 kappa0 r0 H1 IH1 Hflow
                 | Gamma0 t T1 T2 kappa0 H1 IH1 HwfT2 HwfK
                 | Gamma0 t T1 T2 kappa0 HwfT1 H1 IH1 HwfK
                 | L0 Gamma0 t body1 body2 T1 T2 T0 kappa0 r0 H0 IH0 Hflow
                      Hbody1 IHbody1 Hbody2 IHbody2
                 | Gamma0 t T0 l0 H1 IH1
                 | Gamma0 t T0 U0 H1 IH1 Hsub
                 | Gamma0 c yes no k0 T0 r0 Hc IHc Hy IHy Hn IHn Hflow];
    simpl.
  - auto.
  - auto.
  - destruct (fresh_atom L0) as [x Hx].
    apply (lc_at_open_inv body 0 x). apply (IHbody x Hx).
  - split; assumption.
  - split; assumption.
  - exact IH1.
  - exact IH1.
  - exact IH1.
  - exact IH1.
  - split.
    + exact IH0.
    + split.
      * destruct (fresh_atom L0) as [x Hx].
        apply (lc_at_open_inv body1 0 x). apply (IHbody1 x Hx).
      * destruct (fresh_atom L0) as [x Hx].
        apply (lc_at_open_inv body2 0 x). apply (IHbody2 x Hx).
  - exact IH1.
  - exact IH1.
  - split; [exact IHc | split; assumption].
Qed.

Fixpoint context_fv (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs T C' k => context_fv C'
  | C_AppLeft C' t2 r => context_fv C' ++ fv t2
  | C_AppRight t1 C' r => fv t1 ++ context_fv C'
  | C_PairLeft C' t2 k => context_fv C' ++ fv t2
  | C_PairRight t1 C' k => fv t1 ++ context_fv C'
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

Lemma notin_app_l : forall x (a b : list atom), ~ In x (a ++ b) -> ~ In x a.
Proof. intros x a b H Hin; apply H; apply in_or_app; auto. Qed.

Lemma notin_app_r : forall x (a b : list atom), ~ In x (a ++ b) -> ~ In x b.
Proof. intros x a b H Hin; apply H; apply in_or_app; auto. Qed.

Lemma subst_rho_extend_id_notin : forall t x u,
  ~ In x (fv t) -> subst_rho (extend_rho id_rho x u) t = t.
Proof.
  intros t x u Hx.
  transitivity (subst_rho id_rho t).
  - apply subst_rho_agree.
    intros y Hy. unfold extend_rho, id_rho.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply Hx. exact Hy.
    + reflexivity.
  - apply subst_rho_id.
Qed.

Lemma subst_rho_plug : forall C x u,
  ~ In x (context_fv C) ->
  subst_rho (extend_rho id_rho x u) (plug C (tm_fvar x)) = plug C u.
Proof.
  induction C as [| T C' IHC k | C' IHC t2 r | t1 C' IHC r | C' IHC t2 k | t1 C' IHC k
                 | C' IHC r | C' IHC r | C' IHC k | C' IHC k
                 | C' IHC b1 b2 r | t0 C' IHC b2 r | t0 b1 C' IHC r | l C' IHC
                 | C' IHC y n r | c C' IHC n r | c y C' IHC r];
    intros x u Hx; simpl in *.
  - unfold extend_rho. rewrite Nat.eqb_refl. reflexivity.
  - f_equal. apply IHC. exact Hx.
  - f_equal.
    + apply IHC. apply (notin_app_l x (context_fv C') (fv t2)). exact Hx.
    + apply subst_rho_extend_id_notin. apply (notin_app_r x (context_fv C') (fv t2)). exact Hx.
  - f_equal.
    + apply subst_rho_extend_id_notin. apply (notin_app_l x (fv t1) (context_fv C')). exact Hx.
    + apply IHC. apply (notin_app_r x (fv t1) (context_fv C')). exact Hx.
  - f_equal.
    + apply IHC. apply (notin_app_l x (context_fv C') (fv t2)). exact Hx.
    + apply subst_rho_extend_id_notin. apply (notin_app_r x (context_fv C') (fv t2)). exact Hx.
  - f_equal.
    + apply subst_rho_extend_id_notin. apply (notin_app_l x (fv t1) (context_fv C')). exact Hx.
    + apply IHC. apply (notin_app_r x (fv t1) (context_fv C')). exact Hx.
  - f_equal. apply IHC. exact Hx.
  - f_equal. apply IHC. exact Hx.
  - f_equal. apply IHC. exact Hx.
  - f_equal. apply IHC. exact Hx.
  - (* CaseScrutinee: fv = context_fv C' ++ (fv b1 ++ fv b2) *)
    pose proof (notin_app_l x (context_fv C') (fv b1 ++ fv b2) Hx) as Hc'.
    pose proof (notin_app_r x (context_fv C') (fv b1 ++ fv b2) Hx) as Hrest.
    pose proof (notin_app_l x (fv b1) (fv b2) Hrest) as Hb1.
    pose proof (notin_app_r x (fv b1) (fv b2) Hrest) as Hb2.
    f_equal.
    + apply IHC. exact Hc'.
    + apply subst_rho_extend_id_notin. exact Hb1.
    + apply subst_rho_extend_id_notin. exact Hb2.
  - (* CaseLeft: fv = fv t0 ++ (context_fv C' ++ fv b2) *)
    pose proof (notin_app_l x (fv t0) (context_fv C' ++ fv b2) Hx) as Ht0.
    pose proof (notin_app_r x (fv t0) (context_fv C' ++ fv b2) Hx) as Hrest.
    pose proof (notin_app_l x (context_fv C') (fv b2) Hrest) as Hc'.
    pose proof (notin_app_r x (context_fv C') (fv b2) Hrest) as Hb2.
    f_equal.
    + apply subst_rho_extend_id_notin. exact Ht0.
    + apply IHC. exact Hc'.
    + apply subst_rho_extend_id_notin. exact Hb2.
  - (* CaseRight: fv = fv t0 ++ (fv b1 ++ context_fv C') *)
    pose proof (notin_app_l x (fv t0) (fv b1 ++ context_fv C') Hx) as Ht0.
    pose proof (notin_app_r x (fv t0) (fv b1 ++ context_fv C') Hx) as Hrest.
    pose proof (notin_app_l x (fv b1) (context_fv C') Hrest) as Hb1.
    pose proof (notin_app_r x (fv b1) (context_fv C') Hrest) as Hc'.
    f_equal.
    + apply subst_rho_extend_id_notin. exact Ht0.
    + apply subst_rho_extend_id_notin. exact Hb1.
    + apply IHC. exact Hc'.
  - f_equal. apply IHC. exact Hx.
  - (* IfCondition: fv = context_fv C' ++ (fv y ++ fv n) *)
    pose proof (notin_app_l x (context_fv C') (fv y ++ fv n) Hx) as Hc'.
    pose proof (notin_app_r x (context_fv C') (fv y ++ fv n) Hx) as Hrest.
    pose proof (notin_app_l x (fv y) (fv n) Hrest) as Hy.
    pose proof (notin_app_r x (fv y) (fv n) Hrest) as Hn.
    f_equal.
    + apply IHC. exact Hc'.
    + apply subst_rho_extend_id_notin. exact Hy.
    + apply subst_rho_extend_id_notin. exact Hn.
  - (* IfThen: fv = fv c ++ (context_fv C' ++ fv n) *)
    pose proof (notin_app_l x (fv c) (context_fv C' ++ fv n) Hx) as Hc1.
    pose proof (notin_app_r x (fv c) (context_fv C' ++ fv n) Hx) as Hrest.
    pose proof (notin_app_l x (context_fv C') (fv n) Hrest) as Hc'.
    pose proof (notin_app_r x (context_fv C') (fv n) Hrest) as Hn.
    f_equal.
    + apply subst_rho_extend_id_notin. exact Hc1.
    + apply IHC. exact Hc'.
    + apply subst_rho_extend_id_notin. exact Hn.
  - (* IfElse: fv = fv c ++ (fv y ++ context_fv C') *)
    pose proof (notin_app_l x (fv c) (fv y ++ context_fv C') Hx) as Hc1.
    pose proof (notin_app_r x (fv c) (fv y ++ context_fv C') Hx) as Hrest.
    pose proof (notin_app_l x (fv y) (context_fv C') Hrest) as Hy.
    pose proof (notin_app_r x (fv y) (context_fv C') Hrest) as Hc'.
    f_equal.
    + apply subst_rho_extend_id_notin. exact Hc1.
    + apply subst_rho_extend_id_notin. exact Hy.
    + apply IHC. exact Hc'.
Qed.

(* ===================================================================== *)
(* Logical relation                                                       *)
(* ===================================================================== *)

Definition vis (l j : label) (T : ty) : Prop :=
  flows_to (join (security_of T).(indirect_reader) j) l.

Fixpoint VpS (l j : label) (T : ty) (x y : tm) {struct T} : Prop :=
  match T with
  | Ty_Unit k =>
      exists kv1 kv2 : security, x = tm_unit kv1 /\ y = tm_unit kv2
  | Ty_Sum T1 T2 k =>
      exists kv1 kv2 : security,
        security_le kv1 (protect_security k j) /\
        security_le kv2 (protect_security k j) /\
        ((exists u1 u2 : tm, x = tm_inl u1 kv1 /\ y = tm_inl u2 kv2 /\
             (vis l Low T1 -> VpS l Low T1 u1 u2))
         \/ (exists u1 u2 : tm, x = tm_inr u1 kv1 /\ y = tm_inr u2 kv2 /\
             (vis l Low T2 -> VpS l Low T2 u1 u2)))
  | Ty_Prod T1 T2 k =>
      exists kv1 kv2 : security,
        security_le kv1 (protect_security k j) /\
        security_le kv2 (protect_security k j) /\
        (exists a1 b1 a2 b2 : tm,
            x = tm_pair a1 b1 kv1 /\ y = tm_pair a2 b2 kv2 /\
            (vis l Low T1 -> VpS l Low T1 a1 a2) /\
            (vis l Low T2 -> VpS l Low T2 b1 b2))
  | Ty_Arrow T1 T2 k =>
      exists (T1x T1y : ty) (bodyx bodyy : tm) (kv1 kv2 : security),
        x = tm_abs T1x bodyx kv1 /\ y = tm_abs T1y bodyy kv2 /\
        security_le kv1 (protect_security k j) /\
        security_le kv2 (protect_security k j) /\
        (forall (w1 w2 : tm) (r : label),
            value w1 -> value w2 -> flows_to (join k.(reader) j) r ->
            (vis l Low T1 -> VpS l Low T1 w1 w2) ->
            forall u1 u2 : tm,
              evaluates (tm_app x w1 r) u1 -> evaluates (tm_app y w2 r) u2 ->
              (vis l (join k.(indirect_reader) j) T2 -> VpS l (join k.(indirect_reader) j) T2 u1 u2))
  end.

Definition Vp (l j : label) (T : ty) (x y : tm) : Prop :=
  vis l j T -> VpS l j T x y.

Definition E (l j : label) (T : ty) (e1 e2 : tm) : Prop :=
  forall v1 v2 : tm, evaluates e1 v1 -> evaluates e2 v2 -> Vp l j T v1 v2.

Definition env_rel (l : label) (Gamma : context) (rho1 rho2 : atom -> tm) : Prop :=
  (forall x, locally_closed (rho1 x)) /\
  (forall x, locally_closed (rho2 x)) /\
  (forall x T, lookup_context x Gamma = Some T -> E l Low T (rho1 x) (rho2 x)).

Lemma Vp_mono_j : forall T l j j' x y,
  flows_to j j' -> Vp l j T x y -> Vp l j' T x y.
Proof.
  induction T as [k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k];
    intros l j j' x y Hjj' H; simpl in *.
  - intros Hvis.
    apply H. apply flows_to_trans with (b := join k.(indirect_reader) j').
    + apply join_mono; [apply flows_to_refl | exact Hjj'].
    + exact Hvis.
  - intros Hvis.
    destruct (H (flows_to_trans _ _ _ (flows_to_join_r_mono j j' k.(indirect_reader) Hjj') Hvis))
      as [kv1 [kv2 [Hs1 [Hs2 Hb]]]].
    exists kv1, kv2. split.
    + eapply security_le_trans; [exact Hs1 | apply security_le_protect_mono; [apply security_le_refl | exact Hjj']].
    + split.
      * eapply security_le_trans; [exact Hs2 | apply security_le_protect_mono; [apply security_le_refl | exact Hjj']].
      * destruct Hb as [[u1 [u2 [Ex [Ey Hp]]]] | [u1 [u2 [Ex [Ey Hp]]]]].
        -- left. exists u1, u2. auto.
        -- right. exists u1, u2. auto.
  - intros Hvis.
    destruct (H (flows_to_trans _ _ _ (flows_to_join_r_mono j j' k.(indirect_reader) Hjj') Hvis))
      as [kv1 [kv2 [Hs1 [Hs2 Hb]]]].
    exists kv1, kv2. split.
    + eapply security_le_trans; [exact Hs1 | apply security_le_protect_mono; [apply security_le_refl | exact Hjj']].
    + split.
      * eapply security_le_trans; [exact Hs2 | apply security_le_protect_mono; [apply security_le_refl | exact Hjj']].
      * destruct Hb as [a1 [b1 [a2 [b2 [Ex [Ey [Hpa Hpb]]]]]]].
        exists a1, b1, a2, b2. auto.
  - intros Hvis.
    destruct (H (flows_to_trans _ _ _ (flows_to_join_r_mono j j' k.(indirect_reader) Hjj') Hvis))
      as [T1x [T1y [bodyx [bodyy [kv1 [kv2 [Ex [Ey [Hs1 [Hs2 Hfun]]]]]]]]]].
    exists T1x, T1y, bodyx, bodyy, kv1, kv2. split; [exact Ex | split; [exact Ey | split]].
    + eapply security_le_trans; [exact Hs1 | apply security_le_protect_mono; [apply security_le_refl | exact Hjj']].
    + split.
      * eapply security_le_trans; [exact Hs2 | apply security_le_protect_mono; [apply security_le_refl | exact Hjj']].
      * intros w1 w2 r Hv1 Hv2 Hr Hrel u1 u2 Hev1 Hev2.
        change (Vp l (join k.(indirect_reader) j') T2 u1 u2).
        eapply IH2.
        -- apply flows_to_join_r_mono. exact Hjj'.
        -- intros Hvis_src.
           apply (Hfun w1 w2 r Hv1 Hv2).
           ++ apply flows_to_trans with (b := join k.(reader) j').
              ** apply flows_to_join_r_mono. exact Hjj'.
              ** exact Hr.
           ++ exact Hrel.
           ++ exact Hev1.
           ++ exact Hev2.
           ++ exact Hvis_src.
Qed.

Lemma Vp_Low_protect : forall T l j x y,
  Vp l Low (ty_protect j T) x y <-> Vp l j T x y.
Proof.
  induction T as [k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k];
    intros l j x y; destruct k as [r i]; destruct r, i, j; cbn;
    split; intros H; exact H.
Qed.

Lemma protect_value_protect_value : forall v j1 j2,
  protect_value (protect_value v j1) j2 = protect_value v (join j1 j2).
Proof.
  intros v j1 j2.
  destruct v as [i | x | s | T b s | t1 t2 r | t1 t2 s | t1 r | t1 r | t1 s | t1 s
                | t0 b1 b2 r | l t1 | c y n r]; simpl; try reflexivity.
  - destruct s as [rr ii]; destruct rr, ii, j1, j2; reflexivity.
  - destruct s as [rr ii]; destruct rr, ii, j1, j2; reflexivity.
  - destruct s as [rr ii]; destruct rr, ii, j1, j2; reflexivity.
  - destruct s as [rr ii]; destruct rr, ii, j1, j2; reflexivity.
  - destruct s as [rr ii]; destruct rr, ii, j1, j2; reflexivity.
Qed.

Lemma join4_reassoc : forall a b c d : label,
  join (join (join a b) c) d = join a (join (join b c) d).
Proof. intros [] [] [] []; reflexivity. Qed.

Lemma join_rot : forall a b c d : label,
  join (join a b) (join c d) = join (join (join a c) b) d.
Proof. intros [] [] [] []; reflexivity. Qed.

Lemma value_abs_transfer : forall T body k1 k2,
  value (tm_abs T body k1) -> value (tm_abs T body k2).
Proof.
  intros T body k1 k2 H. inversion H; subst. apply v_abs. assumption.
Qed.

Lemma multi_app_abs_value : forall T body k w r u,
  value w -> multi (tm_app (tm_abs T body k) w r) u -> value u ->
  value (tm_abs T body k) /\ flows_to k.(reader) r.
Proof.
  intros T body k w r u Hvw Hm.
  remember (tm_app (tm_abs T body k) w r) as s eqn:Hs.
  revert Hs.
  induction Hm as [a0 | a b c Hstep Hm IH]; intros Hs.
  - subst a0. intro Hv. inversion Hv.
  - subst a. intro Hv.
    inversion Hstep; subst.
    + split; assumption.
    + exfalso; exact (step_abs_false T body k t1' H3).
    + exfalso; exact (value_no_step w t2' Hvw H4).
Qed.

Lemma protect_security_ind : forall k j,
  (protect_security k j).(indirect_reader) = join k.(indirect_reader) j.
Proof. intros [r i] j; reflexivity. Qed.

Lemma protect_security_read : forall k j,
  (protect_security k j).(reader) = join k.(reader) j.
Proof. intros [r i] j; reflexivity. Qed.

Lemma flows_to_ind_join : forall (k : security) j j1 j2 l,
  flows_to (join k.(indirect_reader) (join (join j j1) j2)) l ->
  flows_to (join k.(indirect_reader) j) l.
Proof.
  intros k j j1 j2 l H.
  eapply flows_to_trans.
  - apply flows_to_join_r_mono.
    apply flows_to_trans with (b := join j j1); [apply flows_to_join_ab | apply flows_to_join_ab].
  - exact H.
Qed.

Lemma flows_to_reader_join : forall (k : security) j j1 j2 r,
  flows_to (join k.(reader) (join (join j j1) j2)) r ->
  flows_to (join k.(reader) j) r.
Proof.
  intros k j j1 j2 r H.
  eapply flows_to_trans.
  - apply flows_to_join_r_mono.
    apply flows_to_trans with (b := join j j1); [apply flows_to_join_ab | apply flows_to_join_ab].
  - exact H.
Qed.

Lemma protect_security_join_reassoc : forall k j j1 j2,
  protect_security k (join (join j j1) j2) = protect_security (protect_security k j) (join j1 j2).
Proof.
  intros [r i] j j1 j2. destruct r; destruct i; destruct j; destruct j1; destruct j2; reflexivity.
Qed.

Lemma Vp_protect : forall T l j j1 j2 x y,
  Vp l j T x y ->
  Vp l (join (join j j1) j2) T (protect_value x j1) (protect_value y j2).
Proof.
  induction T as [k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k];
    intros l j j1 j2 x y H; simpl in *.
  - (* Unit *)
    intros Hvis.
    destruct (H (flows_to_trans _ _ _
      (flows_to_join_r_mono j (join (join j j1) j2) k.(indirect_reader)
         (flows_to_trans _ _ _ (flows_to_join_ab j j1) (flows_to_join_ab (join j j1) j2)))
      Hvis)) as [kv1 [kv2 [Ex Ey]]].
    exists (protect_security kv1 j1), (protect_security kv2 j2).
    rewrite Ex, Ey. simpl; auto.
  - (* Sum *)
    intros Hvis.
    destruct (H (flows_to_ind_join k j j1 j2 l Hvis)) as [kv1 [kv2 [Hs1 [Hs2 Hb]]]].
    exists (protect_security kv1 j1), (protect_security kv2 j2).
    split.
    + replace (protect_security k (join (join j j1) j2))
        with (protect_security (protect_security k j) (join j1 j2))
        by (symmetry; apply protect_security_join_reassoc).
      apply (security_le_protect_mono kv1 (protect_security k j) j1 (join j1 j2));
        [exact Hs1 | apply flows_to_join_ab].
    + split.
      * replace (protect_security k (join (join j j1) j2))
          with (protect_security (protect_security k j) (join j1 j2))
          by (symmetry; apply protect_security_join_reassoc).
        apply (security_le_protect_mono kv2 (protect_security k j) j2 (join j1 j2));
          [exact Hs2 | apply flows_to_join_ba].
      * destruct Hb as [[u1 [u2 [Ex [Ey Hp]]]] | [u1 [u2 [Ex [Ey Hp]]]]].
        -- left. exists u1, u2. split; [rewrite Ex; reflexivity | split; [rewrite Ey; reflexivity | exact Hp]].
        -- right. exists u1, u2. split; [rewrite Ex; reflexivity | split; [rewrite Ey; reflexivity | exact Hp]].
  - (* Prod *)
    intros Hvis.
    destruct (H (flows_to_ind_join k j j1 j2 l Hvis)) as [kv1 [kv2 [Hs1 [Hs2 Hb]]]].
    exists (protect_security kv1 j1), (protect_security kv2 j2).
    split.
    + replace (protect_security k (join (join j j1) j2))
        with (protect_security (protect_security k j) (join j1 j2))
        by (symmetry; apply protect_security_join_reassoc).
      apply (security_le_protect_mono kv1 (protect_security k j) j1 (join j1 j2));
        [exact Hs1 | apply flows_to_join_ab].
    + split.
      * replace (protect_security k (join (join j j1) j2))
          with (protect_security (protect_security k j) (join j1 j2))
          by (symmetry; apply protect_security_join_reassoc).
        apply (security_le_protect_mono kv2 (protect_security k j) j2 (join j1 j2));
          [exact Hs2 | apply flows_to_join_ba].
      * destruct Hb as [a1 [b1 [a2 [b2 [Ex [Ey [Hpa Hpb]]]]]]].
        exists a1, b1, a2, b2. split; [rewrite Ex; reflexivity | split; [rewrite Ey; reflexivity | split; assumption]].
  - (* Arrow *)
    intros Hvis.
    destruct (H (flows_to_ind_join k j j1 j2 l Hvis))
      as [T1x [T1y [bodyx [bodyy [kv1 [kv2 [Ex [Ey [Hs1 [Hs2 Hfun]]]]]]]]]].
    destruct Hs1 as [Hr1 Hi1]; destruct Hs2 as [Hr2 Hi2].
    exists T1x, T1y, bodyx, bodyy, (protect_security kv1 j1), (protect_security kv2 j2).
    split; [rewrite Ex; reflexivity | split; [rewrite Ey; reflexivity | split]].
    + replace (protect_security k (join (join j j1) j2))
        with (protect_security (protect_security k j) (join j1 j2))
        by (symmetry; apply protect_security_join_reassoc).
      apply (security_le_protect_mono kv1 (protect_security k j) j1 (join j1 j2));
        [split; [exact Hr1 | exact Hi1] | apply flows_to_join_ab].
    + split.
      * replace (protect_security k (join (join j j1) j2))
          with (protect_security (protect_security k j) (join j1 j2))
          by (symmetry; apply protect_security_join_reassoc).
        apply (security_le_protect_mono kv2 (protect_security k j) j2 (join j1 j2));
        [split; [exact Hr2 | exact Hi2] | apply flows_to_join_ba].
      * intros w1 w2 r Hv1 Hv2 Hr Hrel u1 u2 Hev1 Hev2.
        destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
        rewrite Ex in Hm1. rewrite Ey in Hm2.
        simpl in Hm1, Hm2.
        destruct (multi_app_abs_inv T1x bodyx (protect_security kv1 j1) w1 r u1 Hv1 Hm1 Hval1)
          as [v1 [Hm1' [Hval1' Hu1]]].
        destruct (multi_app_abs_inv T1y bodyy (protect_security kv2 j2) w2 r u2 Hv2 Hm2 Hval2)
          as [v2 [Hm2' [Hval2' Hu2]]].
        destruct (multi_app_abs_value T1x bodyx (protect_security kv1 j1) w1 r u1 Hv1 Hm1 Hval1)
          as [Hvabs1 Hflow1].
        destruct (multi_app_abs_value T1y bodyy (protect_security kv2 j2) w2 r u2 Hv2 Hm2 Hval2)
          as [Hvabs2 Hflow2].
        assert (Hvx : value (tm_abs T1x bodyx kv1))
          by (apply (value_abs_transfer T1x bodyx (protect_security kv1 j1) kv1); exact Hvabs1).
        assert (Hvy : value (tm_abs T1y bodyy kv2))
          by (apply (value_abs_transfer T1y bodyy (protect_security kv2 j2) kv2); exact Hvabs2).
        assert (Hev1s : evaluates (tm_app (tm_abs T1x bodyx kv1) w1 r)
                                  (protect_value v1 kv1.(indirect_reader))).
        { split.
          - eapply multi_step.
            + apply ST_AppAbs; [exact Hvx | exact Hv1 | ].
              apply flows_to_trans with (b := join k.(reader) j).
              * exact Hr1.
              * apply flows_to_reader_join with (j1 := j1) (j2 := j2). exact Hr.
            + apply multi_protect_value; [exact Hm1' | exact Hval1'].
          - apply value_protect_value. exact Hval1'. }
        assert (Hev2s : evaluates (tm_app (tm_abs T1y bodyy kv2) w2 r)
                                  (protect_value v2 kv2.(indirect_reader))).
        { split.
          - eapply multi_step.
            + apply ST_AppAbs; [exact Hvy | exact Hv2 | ].
              apply flows_to_trans with (b := join k.(reader) j).
              * exact Hr2.
              * apply flows_to_reader_join with (j1 := j1) (j2 := j2). exact Hr.
            + apply multi_protect_value; [exact Hm2' | exact Hval2'].
          - apply value_protect_value. exact Hval2'. }
        assert (Hsrc : Vp l (join k.(indirect_reader) j) T2
                          (protect_value v1 kv1.(indirect_reader))
                          (protect_value v2 kv2.(indirect_reader))).
        { intros Hvis_src.
          apply (Hfun w1 w2 r Hv1 Hv2).
          - apply flows_to_reader_join with (j1 := j1) (j2 := j2). exact Hr.
          - exact Hrel.
          - rewrite Ex. exact Hev1s.
          - rewrite Ey. exact Hev2s.
          - exact Hvis_src. }
        subst u1; subst u2.
        rewrite protect_security_ind.
        rewrite protect_security_ind.
        rewrite <- protect_value_protect_value.
        rewrite <- protect_value_protect_value.
        rewrite <- (join4_reassoc k.(indirect_reader) j j1 j2).
        apply (IH2 l (join k.(indirect_reader) j) j1 j2
                 (protect_value v1 kv1.(indirect_reader))
                 (protect_value v2 kv2.(indirect_reader)) Hsrc).
Qed.


Lemma Vp_subtype : forall T U, subtype T U ->
  forall l j j' x y, flows_to j j' -> Vp l j T x y -> Vp l j' U x y.
Proof.
  intros T U Hsub.
  induction Hsub as [k1 k2 Hwf1 Hwf2 Hsec
                   | T1 T2 U1 U2 k1 k2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hsec
                   | T1 T2 U1 U2 k1 k2 Hsub1 IH1 Hsub2 IH2 Hwf1 Hwf2 Hsec
                   | T1 T2 U1 U2 k1 k2 HsubU1T1 IH1 HsubT2U2 IH2 Hwf1 Hwf2 Hsec
                   | T0 U0 V0 Hsub1 IH1 Hsub2 IH2];
    intros l j j' x y Hjj' H; simpl in *.
  - (* Unit *)
    intros Hvis.
    destruct (H (flows_to_trans _ _ _
       (join_mono _ _ _ _ (proj2 Hsec) Hjj') Hvis)) as [kv1 [kv2 [Ex Ey]]].
    exists kv1, kv2. auto.
  - (* Sum *)
    intros Hvis.
    destruct (H (flows_to_trans _ _ _
       (join_mono _ _ _ _ (proj2 Hsec) Hjj') Hvis)) as [kv1 [kv2 [Hs1 [Hs2 Hb]]]].
    exists kv1, kv2. split.
    + eapply security_le_trans; [exact Hs1 | apply (security_le_protect_mono k1 k2 j j'); auto].
    + split.
      * eapply security_le_trans; [exact Hs2 | apply (security_le_protect_mono k1 k2 j j'); auto].
      * destruct Hb as [[u1 [u2 [Ex [Ey Hp]]]] | [u1 [u2 [Ex [Ey Hp]]]]].
        -- left. exists u1, u2. split; [exact Ex | split; [exact Ey | ]].
           apply (IH1 l Low Low u1 u2); auto using flows_to_refl.
        -- right. exists u1, u2. split; [exact Ex | split; [exact Ey | ]].
           apply (IH2 l Low Low u1 u2); auto using flows_to_refl.
  - (* Prod *)
    intros Hvis.
    destruct (H (flows_to_trans _ _ _
       (join_mono _ _ _ _ (proj2 Hsec) Hjj') Hvis)) as [kv1 [kv2 [Hs1 [Hs2 Hb]]]].
    exists kv1, kv2. split.
    + eapply security_le_trans; [exact Hs1 | apply (security_le_protect_mono k1 k2 j j'); auto].
    + split.
      * eapply security_le_trans; [exact Hs2 | apply (security_le_protect_mono k1 k2 j j'); auto].
      * destruct Hb as [a1 [b1 [a2 [b2 [Ex [Ey [Hpa Hpb]]]]]]].
        exists a1, b1, a2, b2. split; [exact Ex | split; [exact Ey | split]].
        -- apply (IH1 l Low Low a1 a2); auto using flows_to_refl.
        -- apply (IH2 l Low Low b1 b2); auto using flows_to_refl.
  - (* Arrow *)
    intros Hvis.
    destruct (H (flows_to_trans _ _ _
       (join_mono _ _ _ _ (proj2 Hsec) Hjj') Hvis))
      as [T1x [T1y [bodyx [bodyy [kv1 [kv2 [Ex [Ey [Hs1 [Hs2 Hfun]]]]]]]]]].
    exists T1x, T1y, bodyx, bodyy, kv1, kv2.
    split; [exact Ex | split; [exact Ey | split]].
    + eapply security_le_trans; [exact Hs1 | apply (security_le_protect_mono k1 k2 j j'); auto].
    + split.
      * eapply security_le_trans; [exact Hs2 | apply (security_le_protect_mono k1 k2 j j'); auto].
      * intros w1 w2 r Hv1 Hv2 Hr Hrel u1 u2 Hev1 Hev2.
        apply (IH2 l (join k1.(indirect_reader) j) (join k2.(indirect_reader) j') u1 u2).
        -- apply join_mono; [exact (proj2 Hsec) | exact Hjj'].
        -- intros Hvis_src.
           exact (Hfun w1 w2 r Hv1 Hv2
                    (flows_to_trans _ _ _ (join_mono _ _ _ _ (proj1 Hsec) Hjj') Hr)
                    (IH1 l Low Low w1 w2 (flows_to_refl Low) Hrel)
                    u1 u2 Hev1 Hev2 Hvis_src).
  - (* Trans *)
    eapply IH2; [exact Hjj' | ].
    eapply IH1; [apply flows_to_refl | exact H].
Qed.

(* ===================================================================== *)
(* Lookup and environment helpers                                         *)
(* ===================================================================== *)

Lemma lookup_update_same : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros; unfold update; simpl; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma lookup_update_other : forall Gamma x y T,
  y <> x -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T Hxy; unfold update; simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E; contradiction.
  - reflexivity.
Qed.

Lemma join_Low_left_idem : forall a : label, join (join Low a) a = join a Low.
Proof. destruct a; reflexivity. Qed.

Lemma join_same_right : forall a b : label, join (join a b) b = join a b.
Proof. destruct a, b; reflexivity. Qed.

(* ===================================================================== *)
(* Term relation lemmas                                                   *)
(* ===================================================================== *)

Lemma E_of_V : forall T l j x y,
  value x -> value y -> Vp l j T x y -> E l j T x y.
Proof.
  intros T l j x y Hvx Hvy HV v1 v2 Hev1 Hev2.
  destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
  rewrite (multi_value x v1 Hm1 Hvx). rewrite (multi_value y v2 Hm2 Hvy).
  exact HV.
Qed.

Lemma E_protect : forall T l j j' e1 e2,
  E l j T e1 e2 -> E l (join j j') T (tm_protect j' e1) (tm_protect j' e2).
Proof.
  intros T l j j' e1 e2 HE v1 v2 Hev1 Hev2.
  destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
  destruct (multi_protect_inv j' e1 v1 Hm1 Hval1) as [u1 [Hmu1 [Hvu1 Hu1]]].
  destruct (multi_protect_inv j' e2 v2 Hm2 Hval2) as [u2 [Hmu2 [Hvu2 Hu2]]].
  rewrite Hu1, Hu2.
  rewrite <- (join_same_right j j').
  apply Vp_protect.
  apply HE; [split; assumption | split; assumption].
Qed.

Lemma E_subtype : forall T U, subtype T U ->
  forall l j j', flows_to j j' -> forall e1 e2,
  E l j T e1 e2 -> E l j' U e1 e2.
Proof.
  intros T U Hsub l j j' Hjj' e1 e2 HE v1 v2 Hev1 Hev2.
  apply (Vp_subtype T U Hsub l j j' v1 v2 Hjj').
  apply HE; assumption.
Qed.

Lemma E_Low_protect : forall T l j e1 e2,
  E l Low (ty_protect j T) e1 e2 <-> E l j T e1 e2.
Proof.
  intros; split; intros H v1 v2 Hev1 Hev2.
  - apply (proj1 (Vp_Low_protect T l j v1 v2)). apply H; auto.
  - apply (proj2 (Vp_Low_protect T l j v1 v2)). apply H; auto.
Qed.

(* ===================================================================== *)
(* Erasure of related ground values                                       *)
(* ===================================================================== *)

Lemma erase_same : forall T kappa l v1 v2,
  ground T -> transparent_at kappa T -> flows_to kappa.(indirect_reader) l ->
  Vp l Low T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  induction T as [k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k | T1 IH1 T2 IH2 k];
    intros kappa l v1 v2 Hg Htr Hflow HV; simpl in *.
  - (* Unit *)
    destruct Htr as [Hle _].
    assert (Hvis : flows_to (join k.(indirect_reader) Low) l).
    { rewrite join_Low_r. eapply flows_to_trans; [exact (proj2 Hle) | exact Hflow]. }
    destruct (HV Hvis) as [kv1 [kv2 [Ex Ey]]].
    rewrite Ex, Ey. reflexivity.
  - (* Sum *)
    destruct Hg as [Hg1 Hg2].
    destruct Htr as [Hle [Htr1 Htr2]].
    assert (Hvis : flows_to (join k.(indirect_reader) Low) l).
    { rewrite join_Low_r. eapply flows_to_trans; [exact (proj2 Hle) | exact Hflow]. }
    destruct (HV Hvis) as [kv1 [kv2 [Hs1 [Hs2 [Hb1 | Hb2]]]]].
    + destruct Hb1 as [u1 [u2 [Ex [Ey Hp]]]].
      rewrite Ex, Ey. simpl.
      rewrite (IH1 kappa l u1 u2 Hg1 Htr1 Hflow Hp). reflexivity.
    + destruct Hb2 as [u1 [u2 [Ex [Ey Hp]]]].
      rewrite Ex, Ey. simpl.
      rewrite (IH2 kappa l u1 u2 Hg2 Htr2 Hflow Hp). reflexivity.
  - (* Prod *)
    destruct Hg as [Hg1 Hg2].
    destruct Htr as [Hle [Htr1 Htr2]].
    assert (Hvis : flows_to (join k.(indirect_reader) Low) l).
    { rewrite join_Low_r. eapply flows_to_trans; [exact (proj2 Hle) | exact Hflow]. }
    destruct (HV Hvis) as [kv1 [kv2 [Hs1 [Hs2 Hb]]]].
    destruct Hb as [a1 [b1 [a2 [b2 [Ex [Ey [Hpa Hpb]]]]]]].
    rewrite Ex, Ey. simpl.
    rewrite (IH1 kappa l a1 a2 Hg1 Htr1 Hflow Hpa).
    rewrite (IH2 kappa l b1 b2 Hg2 Htr2 Hflow Hpb). reflexivity.
  - (* Arrow *)
    destruct Hg.
Qed.

Lemma Vp_protect_result : forall T l k k1 k2 w1 w2,
  vis l k T ->
  Vp l Low T w1 w2 ->
  flows_to k1 k -> flows_to k2 k ->
  VpS l k T (protect_value w1 k1) (protect_value w2 k2).
Proof.
  intros T l k k1 k2 w1 w2 Hvis HV Hf1 Hf2.
  exact (Vp_mono_j T l (join (join Low k1) k2) k
           (protect_value w1 k1) (protect_value w2 k2)
           (flows_to_join (join Low k1) k2 k (flows_to_join Low k1 k I Hf1) Hf2)
           (Vp_protect T l Low k1 k2 w1 w2 HV)
           Hvis).
Qed.

(* ===================================================================== *)
(* Fundamental theorem                                                    *)
(* ===================================================================== *)

Lemma E_level_eq : forall T l j1 j2 e1 e2,
  j1 = j2 -> E l j1 T e1 e2 -> E l j2 T e1 e2.
Proof. intros T l j1 j2 e1 e2 H; subst j2; auto. Qed.

Lemma extend_rho_same : forall rho x u, extend_rho rho x u x = u.
Proof. intros; unfold extend_rho; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma subst_rho_extend_lc : forall rho x u y,
  locally_closed u -> (forall z, locally_closed (rho z)) ->
  locally_closed (extend_rho rho x u y).
Proof.
  intros rho x u y Hu Hrho; unfold extend_rho.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma subst_rho_extend_agree : forall body rho x u,
  ~ In x (fv body) ->
  subst_rho (extend_rho rho x u) body = subst_rho rho body.
Proof.
  intros body rho x u Hx. apply subst_rho_agree.
  intros y Hy. unfold extend_rho.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst y; exfalso; apply Hx; exact Hy.
  - reflexivity.
Qed.

Lemma subst_rho_open_extend_eq : forall body rho x u,
  (forall y, locally_closed (rho y)) -> locally_closed u -> ~ In x (fv body) ->
  subst_rho (extend_rho rho x u) (open body (tm_fvar x)) =
  open (subst_rho rho body) u.
Proof.
  intros body rho x u Hrho Hu Hx.
  change (subst_rho (extend_rho rho x u) (open_rec 0 (tm_fvar x) body) =
          open_rec 0 u (subst_rho rho body)).
  rewrite (subst_rho_open_rec body (extend_rho rho x u) 0 x).
  - rewrite extend_rho_same.
    rewrite (subst_rho_extend_agree body rho x u Hx). reflexivity.
  - intros y. apply subst_rho_extend_lc; auto.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall l rho1 rho2, env_rel l Gamma rho1 rho2 ->
  E l Low T (subst_rho rho1 t) (subst_rho rho2 t).
Proof.
  intros Gamma t T Hty.
  induction Hty as [Gamma0 x0 T0 Hlook Hwf
                 | Gamma0 k0 Hwf
                 | L0 Gamma0 T1 body T2 kappa0 HwfT1 HwfK Hbody IHbody
                 | Gamma0 t1 t2 T1 T2 kappa0 r0 H1 IH1 H2 IH2 Hflow
                 | Gamma0 t1 t2 T1 T2 kappa0 H1 IH1 H2 IH2 HwfK
                 | Gamma0 t T1 T2 kappa0 r0 H1 IH1 Hflow
                 | Gamma0 t T1 T2 kappa0 r0 H1 IH1 Hflow
                 | Gamma0 t T1 T2 kappa0 H1 IH1 HwfT2 HwfK
                 | Gamma0 t T1 T2 kappa0 HwfT1 H1 IH1 HwfK
                 | L0 Gamma0 t body1 body2 T1 T2 T0 kappa0 r0 H0 IH0 Hflow
                      Hbody1 IHbody1 Hbody2 IHbody2
                 | Gamma0 t T0 l0 H1 IH1
                 | Gamma0 t T0 U0 H1 IH1 Hsub
                 | Gamma0 c yes no k0 T0 r0 Hc IHc Hy IHy Hn IHn Hflow];
    intros l rho1 rho2 Henv; simpl.

  - (* T_Var *)
    destruct Henv as [Hlc1 [Hlc2 HenvE]]. apply HenvE. exact Hlook.

  - (* T_Unit *)
    intros v1 v2 Hev1 Hev2.
    destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
    rewrite (multi_unit k0 v1 Hm1), (multi_unit k0 v2 Hm2).
    intros _. exists k0, k0. auto.

  - (* T_Abs *)
    intros v1 v2 Hev1 Hev2.
    destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
    rewrite (multi_abs T1 (subst_rho rho1 body) kappa0 v1 Hm1).
    rewrite (multi_abs T1 (subst_rho rho2 body) kappa0 v2 Hm2).
    intros Hvis.
    exists T1, T1, (subst_rho rho1 body), (subst_rho rho2 body), kappa0, kappa0.
    split; [reflexivity | split; [reflexivity | split]].
    + apply security_le_protect.
    + split.
      * apply security_le_protect.
      * intros w1 w2 r Hvw1 Hvw2 Hr Hrel u1 u2 Hev1' Hev2'.
        destruct Hev1' as [Hm1' Hval1']; destruct Hev2' as [Hm2' Hval2'].
        destruct (multi_app_abs_inv T1 (subst_rho rho1 body) kappa0 w1 r u1 Hvw1 Hm1' Hval1')
          as [v1' [Hmv1 [Hvv1 Hu1]]].
        destruct (multi_app_abs_inv T1 (subst_rho rho2 body) kappa0 w2 r u2 Hvw2 Hm2' Hval2')
          as [v2' [Hmv2 [Hvv2 Hu2]]].
        subst u1; subst u2.
        destruct (fresh_atom (L0 ++ fv body)) as [x Hx].
        assert (HxL : ~ In x L0) by (intro H; apply Hx; apply in_or_app; auto).
        assert (Hxfv : ~ In x (fv body)) by (intro H; apply Hx; apply in_or_app; auto).
        assert (Henv' : env_rel l (update Gamma0 x T1) (extend_rho rho1 x w1) (extend_rho rho2 x w2)).
        { split.
          - intros y. unfold extend_rho. destruct (Nat.eqb x y).
            + apply value_lc; exact Hvw1.
            + apply (proj1 Henv).
          - split.
            + intros y. unfold extend_rho. destruct (Nat.eqb x y).
              * apply value_lc; exact Hvw2.
              * apply (proj1 (proj2 Henv)).
            + intros y U Hlook.
              unfold extend_rho.
              destruct (Nat.eqb x y) eqn:E.
              * apply Nat.eqb_eq in E; subst y.
                rewrite lookup_update_same in Hlook.
                injection Hlook as HU. subst U.
                apply E_of_V; [exact Hvw1 | exact Hvw2 | exact Hrel].
              * assert (Hyx : y <> x) by (intro H; subst y; rewrite Nat.eqb_refl in E; discriminate).
                rewrite (lookup_update_other Gamma0 x y T1 Hyx) in Hlook.
                apply (proj2 (proj2 Henv)); exact Hlook. }
        pose proof (IHbody x HxL l (extend_rho rho1 x w1) (extend_rho rho2 x w2) Henv') as HbodyE.
        assert (Hrew1 : subst_rho (extend_rho rho1 x w1) (open body (tm_fvar x))
                        = open (subst_rho rho1 body) w1).
        { apply subst_rho_open_extend_eq; [apply (proj1 Henv) | apply value_lc; exact Hvw1 | exact Hxfv]. }
        assert (Hrew2 : subst_rho (extend_rho rho2 x w2) (open body (tm_fvar x))
                        = open (subst_rho rho2 body) w2).
        { apply subst_rho_open_extend_eq; [apply (proj1 (proj2 Henv)) | apply value_lc; exact Hvw2 | exact Hxfv]. }
        rewrite Hrew1 in HbodyE. rewrite Hrew2 in HbodyE.
        rewrite <- (join_Low_left_idem kappa0.(indirect_reader)).
        apply Vp_protect.
        apply HbodyE; [split; [exact Hmv1 | exact Hvv1] | split; [exact Hmv2 | exact Hvv2]].

  - (* T_App *)
    intros v1 v2 Hev1 Hev2.
    destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
    destruct (multi_app_inv (subst_rho rho1 t1) (subst_rho rho1 t2) r0 v1 Hm1 Hval1)
      as [f1 [a1 [Hmf1 [Hvf1 [Hma1 [Hva1 Hmapp1]]]]]].
    destruct (multi_app_inv (subst_rho rho2 t1) (subst_rho rho2 t2) r0 v2 Hm2 Hval2)
      as [f2 [a2 [Hmf2 [Hvf2 [Hma2 [Hva2 Hmapp2]]]]]].
    apply (proj2 (Vp_Low_protect T2 l kappa0.(indirect_reader) v1 v2)).
    apply (Vp_mono_j T2 l (join kappa0.(indirect_reader) Low) kappa0.(indirect_reader) v1 v2).
    + rewrite join_Low_r. apply flows_to_refl.
    + intros Hvisf.
      pose proof (IH1 l rho1 rho2 Henv) as HE1.
      pose proof (IH2 l rho1 rho2 Henv) as HE2.
      assert (HVf : Vp l Low (Ty_Arrow T1 T2 kappa0) f1 f2).
      { apply HE1; [split; [exact Hmf1 | exact Hvf1] | split; [exact Hmf2 | exact Hvf2]]. }
      assert (HVa : Vp l Low T1 a1 a2).
      { apply HE2; [split; [exact Hma1 | exact Hva1] | split; [exact Hma2 | exact Hva2]]. }
      assert (Hvis_arrow : vis l Low (Ty_Arrow T1 T2 kappa0)).
      { unfold vis; simpl. eapply flows_to_join_r. exact Hvisf. }
      destruct (HVf Hvis_arrow) as [T1x [T1y [bodyx [bodyy [kv1 [kv2 [Ex [Ey [Hs1 [Hs2 Hfun]]]]]]]]]].
      exact (Hfun a1 a2 r0 Hva1 Hva2
               (flows_to_join_Low (reader kappa0) r0 Hflow)
               HVa v1 v2 (conj Hmapp1 Hval1) (conj Hmapp2 Hval2) Hvisf).

  - (* T_Pair *)
    intros v1 v2 Hev1 Hev2.
    destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
    destruct (multi_pair_inv (subst_rho rho1 t1) (subst_rho rho1 t2) kappa0 v1 Hm1 Hval1)
      as [a1 [b1 [Ha1 [Hva1 [Hb1 [Hvb1 Hu1]]]]]].
    destruct (multi_pair_inv (subst_rho rho2 t1) (subst_rho rho2 t2) kappa0 v2 Hm2 Hval2)
      as [a2 [b2 [Ha2 [Hva2 [Hb2 [Hvb2 Hu2]]]]]].
    rewrite Hu1, Hu2.
    intros Hvis.
    exists kappa0, kappa0. split; [apply security_le_protect | split; [apply security_le_protect | ]].
    exists a1, b1, a2, b2. split; [reflexivity | split; [reflexivity | split]].
    + apply (IH1 l rho1 rho2 Henv); [split; [exact Ha1 | exact Hva1] | split; [exact Ha2 | exact Hva2]].
    + apply (IH2 l rho1 rho2 Henv); [split; [exact Hb1 | exact Hvb1] | split; [exact Hb2 | exact Hvb2]].

  - (* T_Fst *)
    intros v1 v2 Hev1 Hev2.
    destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
    destruct (multi_fst_inv (subst_rho rho1 t) r0 v1 Hm1 Hval1)
      as [a1 [b1 [k1 [Hm1' [Hva1 [Hvb1 [Hflow1 Hu1]]]]]]].
    destruct (multi_fst_inv (subst_rho rho2 t) r0 v2 Hm2 Hval2)
      as [a2 [b2 [k2 [Hm2' [Hva2 [Hvb2 [Hflow2 Hu2]]]]]]].
    rewrite Hu1, Hu2.
    apply (proj2 (Vp_Low_protect T1 l kappa0.(indirect_reader)
                   (protect_value a1 k1.(indirect_reader)) (protect_value a2 k2.(indirect_reader)))).
    intros Hvis2.
    assert (Hvisp : flows_to (join kappa0.(indirect_reader) Low) l).
    { rewrite join_Low_r. eapply flows_to_trans; [apply flows_to_join_ba | exact Hvis2]. }
    assert (HVprod : Vp l Low (Ty_Prod T1 T2 kappa0) (tm_pair a1 b1 k1) (tm_pair a2 b2 k2)).
    { apply (IH1 l rho1 rho2 Henv); [split; [exact Hm1' | apply v_pair; [exact Hva1 | exact Hvb1]] | split; [exact Hm2' | apply v_pair; [exact Hva2 | exact Hvb2]]]. }
    destruct (HVprod Hvisp) as [kv1 [kv2 [Hs1 [Hs2 Hb]]]].
    destruct Hb as [c1 [d1 [c2 [d2 [Ex [Ey [Hpc Hpd]]]]]]].
    injection Ex as Ea1 Eb1 Ek1. injection Ey as Ea2 Eb2 Ek2.
    subst c1; subst d1; subst kv1. subst c2; subst d2; subst kv2.
    apply security_le_protect_Low_inv in Hs1.
    apply security_le_protect_Low_inv in Hs2.
    apply (Vp_mono_j T1 l (join (join Low k1.(indirect_reader)) k2.(indirect_reader))
             kappa0.(indirect_reader)
             (protect_value a1 k1.(indirect_reader)) (protect_value a2 k2.(indirect_reader))).
    + apply flows_to_join.
      * apply flows_to_join; [exact I | exact (proj2 Hs1)].
      * exact (proj2 Hs2).
    + apply Vp_protect. exact Hpc.
    + exact Hvis2.
  - (* T_Snd *)
    intros v1 v2 Hev1 Hev2.
    destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
    destruct (multi_snd_inv (subst_rho rho1 t) r0 v1 Hm1 Hval1)
      as [a1 [b1 [k1 [Hm1' [Hva1 [Hvb1 [Hflow1 Hu1]]]]]]].
    destruct (multi_snd_inv (subst_rho rho2 t) r0 v2 Hm2 Hval2)
      as [a2 [b2 [k2 [Hm2' [Hva2 [Hvb2 [Hflow2 Hu2]]]]]]].
    rewrite Hu1, Hu2.
    apply (proj2 (Vp_Low_protect T2 l kappa0.(indirect_reader)
                   (protect_value b1 k1.(indirect_reader)) (protect_value b2 k2.(indirect_reader)))).
    intros Hvis2.
    assert (Hvisp : flows_to (join kappa0.(indirect_reader) Low) l).
    { rewrite join_Low_r. eapply flows_to_trans; [apply flows_to_join_ba | exact Hvis2]. }
    assert (HVprod : Vp l Low (Ty_Prod T1 T2 kappa0) (tm_pair a1 b1 k1) (tm_pair a2 b2 k2)).
    { apply (IH1 l rho1 rho2 Henv); [split; [exact Hm1' | apply v_pair; [exact Hva1 | exact Hvb1]] | split; [exact Hm2' | apply v_pair; [exact Hva2 | exact Hvb2]]]. }
    destruct (HVprod Hvisp) as [kv1 [kv2 [Hs1 [Hs2 Hb]]]].
    destruct Hb as [c1 [d1 [c2 [d2 [Ex [Ey [Hpc Hpd]]]]]]].
    injection Ex as Ea1 Eb1 Ek1. injection Ey as Ea2 Eb2 Ek2.
    subst c1; subst d1; subst kv1. subst c2; subst d2; subst kv2.
    apply security_le_protect_Low_inv in Hs1.
    apply security_le_protect_Low_inv in Hs2.
    apply (Vp_mono_j T2 l (join (join Low k1.(indirect_reader)) k2.(indirect_reader))
             kappa0.(indirect_reader)
             (protect_value b1 k1.(indirect_reader)) (protect_value b2 k2.(indirect_reader))).
    + apply flows_to_join.
      * apply flows_to_join; [exact I | exact (proj2 Hs1)].
      * exact (proj2 Hs2).
    + apply Vp_protect. exact Hpd.
    + exact Hvis2.

  - (* T_Inl *)
    intros v1 v2 Hev1 Hev2.
    destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
    destruct (multi_inl_inv (subst_rho rho1 t) kappa0 v1 Hm1 Hval1) as [a1 [Ha1 [Hva1 Hu1]]].
    destruct (multi_inl_inv (subst_rho rho2 t) kappa0 v2 Hm2 Hval2) as [a2 [Ha2 [Hva2 Hu2]]].
    rewrite Hu1, Hu2.
    intros Hvis.
    exists kappa0, kappa0. split; [apply security_le_protect | split; [apply security_le_protect | ]].
    left. exists a1, a2. split; [reflexivity | split; [reflexivity | ]].
    apply (IH1 l rho1 rho2 Henv); [split; [exact Ha1 | exact Hva1] | split; [exact Ha2 | exact Hva2]].

  - (* T_Inr *)
    intros v1 v2 Hev1 Hev2.
    destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
    destruct (multi_inr_inv (subst_rho rho1 t) kappa0 v1 Hm1 Hval1) as [a1 [Ha1 [Hva1 Hu1]]].
    destruct (multi_inr_inv (subst_rho rho2 t) kappa0 v2 Hm2 Hval2) as [a2 [Ha2 [Hva2 Hu2]]].
    rewrite Hu1, Hu2.
    intros Hvis.
    exists kappa0, kappa0. split; [apply security_le_protect | split; [apply security_le_protect | ]].
    right. exists a1, a2. split; [reflexivity | split; [reflexivity | ]].
    apply (IH1 l rho1 rho2 Henv); [split; [exact Ha1 | exact Hva1] | split; [exact Ha2 | exact Hva2]].

  - (* T_Case *)
    intros v1 v2 Hev1 Hev2.
    destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
    destruct (multi_case_inv (subst_rho rho1 t) (subst_rho rho1 body1) (subst_rho rho1 body2) r0 v1 Hm1 Hval1)
      as [[a1 [k1 [Hm1' [Hva1 [Hflow1 [w1 [Hmw1 [Hvw1 Hu1]]]]]]]] |
          [a1 [k1 [Hm1' [Hva1 [Hflow1 [w1 [Hmw1 [Hvw1 Hu1]]]]]]]]].
    all: destruct (multi_case_inv (subst_rho rho2 t) (subst_rho rho2 body1) (subst_rho rho2 body2) r0 v2 Hm2 Hval2)
      as [[a2 [k2 [Hm2' [Hva2 [Hflow2 [w2 [Hmw2 [Hvw2 Hu2]]]]]]]] |
          [a2 [k2 [Hm2' [Hva2 [Hflow2 [w2 [Hmw2 [Hvw2 Hu2]]]]]]]]].
    all: rewrite Hu1, Hu2.
    all: rewrite (Vp_Low_protect T0 l kappa0.(indirect_reader)).
    all: intros Hvis2.
    all: assert (Hviss : flows_to (join kappa0.(indirect_reader) Low) l)
      by (rewrite join_Low_r; eapply flows_to_join_r; exact Hvis2).
    (* Case LL: both inl *)
    { assert (HVs : Vp l Low (Ty_Sum T1 T2 kappa0) (tm_inl a1 k1) (tm_inl a2 k2)).
      { apply (IH0 l rho1 rho2 Henv);
          [split; [exact Hm1' | apply v_inl; exact Hva1]
          | split; [exact Hm2' | apply v_inl; exact Hva2]]. }
      destruct (HVs Hviss) as [kv1 [kv2 [Hs1 [Hs2 [[c1 [c2 [Ex [Ey Hp]]]] | [c1 [c2 [Ex [Ey Hp]]]]]]]]].
      - injection Ex as Ea1 Ek1. injection Ey as Ea2 Ek2.
        subst c1. subst c2. subst kv1. subst kv2.
        apply security_le_protect_Low_inv in Hs1.
        apply security_le_protect_Low_inv in Hs2.
        destruct (fresh_atom (L0 ++ fv body1 ++ fv body2)) as [x Hx].
        assert (HxL : ~ In x L0) by (intro H; apply Hx; apply in_or_app; left; exact H).
        assert (Hxfv1 : ~ In x (fv body1))
          by (intro H; apply Hx; apply in_or_app; right; apply in_or_app; left; exact H).
        assert (Hxfv2 : ~ In x (fv body2))
          by (intro H; apply Hx; apply in_or_app; right; apply in_or_app; right; exact H).
        assert (Henv' : env_rel l (update Gamma0 x T1) (extend_rho rho1 x a1) (extend_rho rho2 x a2)).
        { split.
          - intros y. unfold extend_rho. destruct (Nat.eqb x y).
            + apply value_lc; exact Hva1.
            + apply (proj1 Henv).
          - split.
            + intros y. unfold extend_rho. destruct (Nat.eqb x y).
              * apply value_lc; exact Hva2.
              * apply (proj1 (proj2 Henv)).
            + intros y U Hlook. unfold extend_rho.
              destruct (Nat.eqb x y) eqn:E.
              * apply Nat.eqb_eq in E; subst y.
                rewrite lookup_update_same in Hlook. injection Hlook as HU. subst U.
                apply E_of_V; [exact Hva1 | exact Hva2 | exact Hp].
              * assert (Hyx : y <> x) by (intro H; subst y; rewrite Nat.eqb_refl in E; discriminate).
                rewrite (lookup_update_other Gamma0 x y T1 Hyx) in Hlook.
                apply (proj2 (proj2 Henv)); exact Hlook. }
        pose proof (IHbody1 x HxL l (extend_rho rho1 x a1) (extend_rho rho2 x a2) Henv') as Hbranch.
        assert (Hrew1 : subst_rho (extend_rho rho1 x a1) (open body1 (tm_fvar x)) = open (subst_rho rho1 body1) a1).
        { apply subst_rho_open_extend_eq; [apply (proj1 Henv) | apply value_lc; exact Hva1 | exact Hxfv1]. }
        assert (Hrew2 : subst_rho (extend_rho rho2 x a2) (open body1 (tm_fvar x)) = open (subst_rho rho2 body1) a2).
        { apply subst_rho_open_extend_eq; [apply (proj1 (proj2 Henv)) | apply value_lc; exact Hva2 | exact Hxfv1]. }
        rewrite Hrew1 in Hbranch. rewrite Hrew2 in Hbranch.
        assert (Hbr : Vp l Low T0 w1 w2).
        { apply Hbranch; [split; [exact Hmw1 | exact Hvw1] | split; [exact Hmw2 | exact Hvw2]]. }
        apply (Vp_protect_result T0 l kappa0.(indirect_reader) k1.(indirect_reader) k2.(indirect_reader) w1 w2 Hvis2 Hbr (proj2 Hs1) (proj2 Hs2)).
      - discriminate Ex. }
    (* Case LR *)
    { assert (HVs : Vp l Low (Ty_Sum T1 T2 kappa0) (tm_inl a1 k1) (tm_inr a2 k2)).
      { apply (IH0 l rho1 rho2 Henv);
          [split; [exact Hm1' | apply v_inl; exact Hva1]
          | split; [exact Hm2' | apply v_inr; exact Hva2]]. }
      destruct (HVs Hviss) as [kv1 [kv2 [Hs1 [Hs2 [[c1 [c2 [Ex [Ey Hp]]]] | [c1 [c2 [Ex [Ey Hp]]]]]]]]].
      - discriminate Ey.
      - discriminate Ex. }
    (* Case RL *)
    { assert (HVs : Vp l Low (Ty_Sum T1 T2 kappa0) (tm_inr a1 k1) (tm_inl a2 k2)).
      { apply (IH0 l rho1 rho2 Henv);
          [split; [exact Hm1' | apply v_inr; exact Hva1]
          | split; [exact Hm2' | apply v_inl; exact Hva2]]. }
      destruct (HVs Hviss) as [kv1 [kv2 [Hs1 [Hs2 [[c1 [c2 [Ex [Ey Hp]]]] | [c1 [c2 [Ex [Ey Hp]]]]]]]]].
      - discriminate Ex.
      - discriminate Ey. }
    (* Case RR: both inr *)
    { assert (HVs : Vp l Low (Ty_Sum T1 T2 kappa0) (tm_inr a1 k1) (tm_inr a2 k2)).
      { apply (IH0 l rho1 rho2 Henv);
          [split; [exact Hm1' | apply v_inr; exact Hva1]
          | split; [exact Hm2' | apply v_inr; exact Hva2]]. }
      destruct (HVs Hviss) as [kv1 [kv2 [Hs1 [Hs2 [[c1 [c2 [Ex [Ey Hp]]]] | [c1 [c2 [Ex [Ey Hp]]]]]]]]].
      - discriminate Ex.
      - injection Ex as Ea1 Ek1. injection Ey as Ea2 Ek2.
        subst c1. subst c2. subst kv1. subst kv2.
        apply security_le_protect_Low_inv in Hs1.
        apply security_le_protect_Low_inv in Hs2.
        destruct (fresh_atom (L0 ++ fv body1 ++ fv body2)) as [x Hx].
        assert (HxL : ~ In x L0) by (intro H; apply Hx; apply in_or_app; left; exact H).
        assert (Hxfv1 : ~ In x (fv body1))
          by (intro H; apply Hx; apply in_or_app; right; apply in_or_app; left; exact H).
        assert (Hxfv2 : ~ In x (fv body2))
          by (intro H; apply Hx; apply in_or_app; right; apply in_or_app; right; exact H).
        assert (Henv' : env_rel l (update Gamma0 x T2) (extend_rho rho1 x a1) (extend_rho rho2 x a2)).
        { split.
          - intros y. unfold extend_rho. destruct (Nat.eqb x y).
            + apply value_lc; exact Hva1.
            + apply (proj1 Henv).
          - split.
            + intros y. unfold extend_rho. destruct (Nat.eqb x y).
              * apply value_lc; exact Hva2.
              * apply (proj1 (proj2 Henv)).
            + intros y U Hlook. unfold extend_rho.
              destruct (Nat.eqb x y) eqn:E.
              * apply Nat.eqb_eq in E; subst y.
                rewrite lookup_update_same in Hlook. injection Hlook as HU. subst U.
                apply E_of_V; [exact Hva1 | exact Hva2 | exact Hp].
              * assert (Hyx : y <> x) by (intro H; subst y; rewrite Nat.eqb_refl in E; discriminate).
                rewrite (lookup_update_other Gamma0 x y T2 Hyx) in Hlook.
                apply (proj2 (proj2 Henv)); exact Hlook. }
        pose proof (IHbody2 x HxL l (extend_rho rho1 x a1) (extend_rho rho2 x a2) Henv') as Hbranch.
        assert (Hrew1 : subst_rho (extend_rho rho1 x a1) (open body2 (tm_fvar x)) = open (subst_rho rho1 body2) a1).
        { apply subst_rho_open_extend_eq; [apply (proj1 Henv) | apply value_lc; exact Hva1 | exact Hxfv2]. }
        assert (Hrew2 : subst_rho (extend_rho rho2 x a2) (open body2 (tm_fvar x)) = open (subst_rho rho2 body2) a2).
        { apply subst_rho_open_extend_eq; [apply (proj1 (proj2 Henv)) | apply value_lc; exact Hva2 | exact Hxfv2]. }
        rewrite Hrew1 in Hbranch. rewrite Hrew2 in Hbranch.
        assert (Hbr : Vp l Low T0 w1 w2).
        { apply Hbranch; [split; [exact Hmw1 | exact Hvw1] | split; [exact Hmw2 | exact Hvw2]]. }
        apply (Vp_protect_result T0 l kappa0.(indirect_reader) k1.(indirect_reader) k2.(indirect_reader) w1 w2 Hvis2 Hbr (proj2 Hs1) (proj2 Hs2)). }

  - (* T_Protect *)
    apply (proj2 (E_Low_protect T0 l l0 (tm_protect l0 (subst_rho rho1 t)) (tm_protect l0 (subst_rho rho2 t)))).
    apply (E_level_eq T0 l (join Low l0) l0).
    + apply join_Low_l.
    + apply (E_protect T0 l Low l0).
      apply IH1. exact Henv.

  - (* T_Sub *)
    apply (E_subtype T0 U0 Hsub l Low Low).
    + apply flows_to_refl.
    + apply IH1. exact Henv.

  - (* T_If *)
    intros v1 v2 Hev1 Hev2.
    destruct Hev1 as [Hm1 Hval1]; destruct Hev2 as [Hm2 Hval2].
    destruct (multi_if_inv (subst_rho rho1 c) (subst_rho rho1 yes) (subst_rho rho1 no) r0 v1 Hm1 Hval1)
      as [[a1 [k1 [Hc1 [Hva1 [Hflow1 [w1 [Hmw1 [Hvw1 Hu1]]]]]]]] |
          [a1 [k1 [Hc1 [Hva1 [Hflow1 [w1 [Hmw1 [Hvw1 Hu1]]]]]]]]].
    all: destruct (multi_if_inv (subst_rho rho2 c) (subst_rho rho2 yes) (subst_rho rho2 no) r0 v2 Hm2 Hval2)
      as [[a2 [k2 [Hc2 [Hva2 [Hflow2 [w2 [Hmw2 [Hvw2 Hu2]]]]]]]] |
          [a2 [k2 [Hc2 [Hva2 [Hflow2 [w2 [Hmw2 [Hvw2 Hu2]]]]]]]]].
    all: rewrite Hu1, Hu2.
    all: rewrite (Vp_Low_protect T0 l k0.(indirect_reader)).
    all: intros Hvis2.
    all: assert (Hvisc : flows_to (join k0.(indirect_reader) Low) l)
      by (rewrite join_Low_r; eapply flows_to_join_r; exact Hvis2).
    (* LL *)
    { assert (HVc : Vp l Low (Ty_Sum (Ty_Unit public) (Ty_Unit public) k0) (tm_inl a1 k1) (tm_inl a2 k2)).
      { apply (IHc l rho1 rho2 Henv);
          [split; [exact Hc1 | apply v_inl; exact Hva1]
          | split; [exact Hc2 | apply v_inl; exact Hva2]]. }
      destruct (HVc Hvisc) as [kv1 [kv2 [Hs1 [Hs2 [[d1 [d2 [Ex [Ey Hp]]]] | [d1 [d2 [Ex [Ey Hp]]]]]]]]].
      - injection Ex as Ea1 Ek1. injection Ey as Ea2 Ek2.
        subst d1. subst d2. subst kv1. subst kv2.
        apply security_le_protect_Low_inv in Hs1.
        apply security_le_protect_Low_inv in Hs2.
        assert (Hbr : Vp l Low T0 w1 w2).
        { apply (IHy l rho1 rho2 Henv); [split; [exact Hmw1 | exact Hvw1] | split; [exact Hmw2 | exact Hvw2]]. }
        apply (Vp_protect_result T0 l k0.(indirect_reader) k1.(indirect_reader) k2.(indirect_reader) w1 w2 Hvis2 Hbr (proj2 Hs1) (proj2 Hs2)).
      - discriminate Ey. }
    (* LR *)
    { assert (HVc : Vp l Low (Ty_Sum (Ty_Unit public) (Ty_Unit public) k0) (tm_inl a1 k1) (tm_inr a2 k2)).
      { apply (IHc l rho1 rho2 Henv);
          [split; [exact Hc1 | apply v_inl; exact Hva1]
          | split; [exact Hc2 | apply v_inr; exact Hva2]]. }
      destruct (HVc Hvisc) as [kv1 [kv2 [Hs1 [Hs2 [[d1 [d2 [Ex [Ey Hp]]]] | [d1 [d2 [Ex [Ey Hp]]]]]]]]].
      - discriminate Ey.
      - discriminate Ex. }
    (* RL *)
    { assert (HVc : Vp l Low (Ty_Sum (Ty_Unit public) (Ty_Unit public) k0) (tm_inr a1 k1) (tm_inl a2 k2)).
      { apply (IHc l rho1 rho2 Henv);
          [split; [exact Hc1 | apply v_inr; exact Hva1]
          | split; [exact Hc2 | apply v_inl; exact Hva2]]. }
      destruct (HVc Hvisc) as [kv1 [kv2 [Hs1 [Hs2 [[d1 [d2 [Ex [Ey Hp]]]] | [d1 [d2 [Ex [Ey Hp]]]]]]]]].
      - discriminate Ex.
      - discriminate Ey. }
    (* RR *)
    { assert (HVc : Vp l Low (Ty_Sum (Ty_Unit public) (Ty_Unit public) k0) (tm_inr a1 k1) (tm_inr a2 k2)).
      { apply (IHc l rho1 rho2 Henv);
          [split; [exact Hc1 | apply v_inr; exact Hva1]
          | split; [exact Hc2 | apply v_inr; exact Hva2]]. }
      destruct (HVc Hvisc) as [kv1 [kv2 [Hs1 [Hs2 [[d1 [d2 [Ex [Ey Hp]]]] | [d1 [d2 [Ex [Ey Hp]]]]]]]]].
      - discriminate Ex.
      - injection Ex as Ea1 Ek1. injection Ey as Ea2 Ek2.
        subst d1. subst d2. subst kv1. subst kv2.
        apply security_le_protect_Low_inv in Hs1.
        apply security_le_protect_Low_inv in Hs2.
        assert (Hbr : Vp l Low T0 w1 w2).
        { apply (IHn l rho1 rho2 Henv); [split; [exact Hmw1 | exact Hvw1] | split; [exact Hmw2 | exact Hvw2]]. }
        apply (Vp_protect_result T0 l k0.(indirect_reader) k1.(indirect_reader) k2.(indirect_reader) w1 w2 Hvis2 Hbr (proj2 Hs1) (proj2 Hs2)). }
Qed.

(* ===================================================================== *)
(* Noninterference                                                        *)
(* ===================================================================== *)

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
  intros C t1 t2 T_secret T_result Hty1 Hty2 Hctx Hground Htrans Hno.
  apply flows_to_false_iff in Hno.
  destruct Hno as [Hsec_ind Hres_ind].
  destruct Hctx as [L HL].
  destruct (fresh_atom (L ++ context_fv C)) as [x Hx].
  assert (HxL : ~ In x L) by (intro H; apply Hx; apply in_or_app; auto).
  assert (HxC : ~ In x (context_fv C)) by (intro H; apply Hx; apply in_or_app; auto).
  set (rho1 := extend_rho id_rho x t1).
  set (rho2 := extend_rho id_rho x t2).
  assert (Henv : env_rel Low (update empty x T_secret) rho1 rho2).
  { split.
    - intros y. unfold rho1, extend_rho. simpl. destruct (Nat.eqb x y) eqn:E.
      + apply Nat.eqb_eq in E; subst y. apply has_type_lc in Hty1. exact Hty1.
      + unfold locally_closed. simpl. auto.
    - split.
      + intros y. unfold rho2, extend_rho. simpl. destruct (Nat.eqb x y) eqn:E.
        * apply Nat.eqb_eq in E; subst y. apply has_type_lc in Hty2. exact Hty2.
        * unfold locally_closed. simpl. auto.
      + intros y U Hlook. unfold rho1, rho2, extend_rho. simpl.
        destruct (Nat.eqb x y) eqn:E.
        * apply Nat.eqb_eq in E; subst y.
          rewrite lookup_update_same in Hlook. injection Hlook as HU. subst U.
          intros v1 v2 Hev1 Hev2 Hvis.
          exfalso. unfold vis in Hvis.
          rewrite Hsec_ind in Hvis. rewrite join_Low_r in Hvis. simpl in Hvis. exact Hvis.
        * assert (Hyx : y <> x) by (intro H; subst y; rewrite Nat.eqb_refl in E; discriminate).
          rewrite (lookup_update_other empty x y T_secret Hyx) in Hlook.
          simpl in Hlook. discriminate Hlook. }
  pose proof (fundamental (update empty x T_secret) (plug C (tm_fvar x)) T_result
                (HL x HxL) Low rho1 rho2 Henv) as HE.
  assert (Hsub1 : subst_rho rho1 (plug C (tm_fvar x)) = plug C t1).
  { unfold rho1. apply subst_rho_plug. exact HxC. }
  assert (Hsub2 : subst_rho rho2 (plug C (tm_fvar x)) = plug C t2).
  { unfold rho2. apply subst_rho_plug. exact HxC. }
  rewrite Hsub1, Hsub2 in HE.
  intros v1 v2 Hev1 Hev2.
  apply (erase_same T_result (security_of T_result) Low v1 v2 Hground Htrans).
  - rewrite Hres_ind. simpl. exact I.
  - apply HE; [exact Hev1 | exact Hev2].
Qed.
