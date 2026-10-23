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

(* Big-step evaluation makes the two-run relation compositional. *)
Inductive eval : tm -> tm -> Prop :=
  | E_Unit : forall k, eval (tm_unit k) (tm_unit k)
  | E_Abs : forall A b k, value (tm_abs A b k) ->
      eval (tm_abs A b k) (tm_abs A b k)
  | E_App : forall f a A b k va w r,
      eval f (tm_abs A b k) -> eval a va ->
      flows_to k.(reader) r -> eval (open b va) w ->
      eval (tm_app f a r) (protect_value w k.(indirect_reader))
  | E_Pair : forall t1 t2 v1 v2 k,
      eval t1 v1 -> eval t2 v2 -> eval (tm_pair t1 t2 k) (tm_pair v1 v2 k)
  | E_Fst : forall t v1 v2 k r,
      eval t (tm_pair v1 v2 k) -> flows_to k.(reader) r ->
      eval (tm_fst t r) (protect_value v1 k.(indirect_reader))
  | E_Snd : forall t v1 v2 k r,
      eval t (tm_pair v1 v2 k) -> flows_to k.(reader) r ->
      eval (tm_snd t r) (protect_value v2 k.(indirect_reader))
  | E_Inl : forall t v k,
      eval t v -> eval (tm_inl t k) (tm_inl v k)
  | E_Inr : forall t v k,
      eval t v -> eval (tm_inr t k) (tm_inr v k)
  | E_CaseLeft : forall t v k b1 b2 r w,
      eval t (tm_inl v k) -> flows_to k.(reader) r ->
      eval (open b1 v) w ->
      eval (tm_case t b1 b2 r) (protect_value w k.(indirect_reader))
  | E_CaseRight : forall t v k b1 b2 r w,
      eval t (tm_inr v k) -> flows_to k.(reader) r ->
      eval (open b2 v) w ->
      eval (tm_case t b1 b2 r) (protect_value w k.(indirect_reader))
  | E_Protect : forall l t v,
      eval t v -> eval (tm_protect l t) (protect_value v l)
  | E_IfTrue : forall c v k y n r w,
      eval c (tm_inl v k) -> flows_to k.(reader) r -> eval y w ->
      eval (tm_if c y n r) (protect_value w k.(indirect_reader))
  | E_IfFalse : forall c v k y n r w,
      eval c (tm_inr v k) -> flows_to k.(reader) r -> eval n w ->
      eval (tm_if c y n r) (protect_value w k.(indirect_reader)).

(* A high indirect reader hides the entire value. At a low reader, sums and
   products expose their components and functions are compared by use. *)
Fixpoint vrel (T : ty) (v1 v2 : tm) : Prop :=
  value v1 /\ value v2 /\
  match (security_of T).(indirect_reader) with
  | High => True
  | Low =>
      match T with
      | Ty_Unit _ => exists k1 k2, v1 = tm_unit k1 /\ v2 = tm_unit k2 /\
          k1.(indirect_reader) = Low /\ k2.(indirect_reader) = Low
      | Ty_Sum A B _ =>
          (exists a1 a2 k1 k2,
              v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\
              k1.(indirect_reader) = Low /\ k2.(indirect_reader) = Low /\
              vrel A a1 a2) \/
          (exists b1 b2 k1 k2,
              v1 = tm_inr b1 k1 /\ v2 = tm_inr b2 k2 /\
              k1.(indirect_reader) = Low /\ k2.(indirect_reader) = Low /\
              vrel B b1 b2)
      | Ty_Prod A B _ =>
          exists a1 a2 b1 b2 k1 k2,
            v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
            k1.(indirect_reader) = Low /\ k2.(indirect_reader) = Low /\
            vrel A a1 a2 /\ vrel B b1 b2
      | Ty_Arrow A B _ =>
          (exists A1 b1 k1 A2 b2 k2,
            v1 = tm_abs A1 b1 k1 /\ v2 = tm_abs A2 b2 k2 /\
            k1.(indirect_reader) = Low /\ k2.(indirect_reader) = Low) /\
          forall a1 a2, vrel A a1 a2 ->
            forall r1 r2 w1 w2,
              eval (tm_app v1 a1 r1) w1 ->
              eval (tm_app v2 a2 r2) w2 -> vrel B w1 w2
      end
  end.

Definition termrel (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, eval t1 v1 -> eval t2 v2 -> vrel T v1 v2.

Lemma protect_value_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l Hv. induction Hv; simpl; try constructor; auto.
Qed.

Lemma protect_value_low : forall v, value v -> protect_value v Low = v.
Proof.
  intros v Hv. inversion Hv; subst; simpl;
    destruct kappa as [r i]; destruct r, i; reflexivity.
Qed.

Lemma eval_value : forall t v, eval t v -> value v.
Proof.
  intros t v H. induction H;
    eauto using v_unit, v_abs, v_pair, v_inl, v_inr, protect_value_value.
  all: inversion IHeval; subst; eauto using protect_value_value.
Qed.

Lemma eval_of_value : forall v, value v -> eval v v.
Proof.
  intros v Hv. induction Hv; eauto using E_Unit, E_Abs, E_Pair, E_Inl, E_Inr.
  apply E_Abs. constructor. assumption.
Qed.

Lemma eval_value_inv : forall v w, value v -> eval v w -> w = v.
Proof.
  intros v w Hv. revert w. induction Hv; intros w He;
    inversion He; subst; try reflexivity;
    repeat match goal with
    | H : eval ?a ?b |- _ =>
        first [let E := fresh "E" in
               assert (E : b = a) by (eauto); clear H; subst b
              | fail 1]
    end; reflexivity.
Qed.

Lemma step_back_eval : forall t t' w,
  t --> t' -> eval t' w -> eval t w.
Proof.
  intros t t' w Hs. revert w.
  induction Hs; intros w He; inversion He; subst;
    eauto 8 using eval_of_value, eval.
  all: pose proof (eval_value_inv _ _ (protect_value_value _ _ H) He) as ->;
    apply E_Protect; apply eval_of_value; assumption.
Qed.

Lemma multi_to_eval : forall t v,
  t -->* v -> value v -> eval t v.
Proof.
  intros t v Hm. induction Hm; intros Hv.
  - now apply eval_of_value.
  - eapply step_back_eval; eauto.
Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof.
  intros T. destruct T; simpl; destruct s as [r i];
    destruct r, i; reflexivity.
Qed.

Lemma ty_protect_high : forall T,
  (security_of (ty_protect High T)).(indirect_reader) = High.
Proof.
  intros T. destruct T; simpl; destruct s as [r i];
    destruct r, i; reflexivity.
Qed.

Lemma vrel_values : forall T v1 v2,
  vrel T v1 v2 -> value v1 /\ value v2.
Proof.
  intros T v1 v2 H. destruct T; simpl in H; tauto.
Qed.

Lemma termrel_high : forall T t1 t2,
  (security_of T).(indirect_reader) = High -> termrel T t1 t2.
Proof.
  intros T t1 t2 H v1 v2 E1 E2.
  destruct T; simpl in *; rewrite H;
    repeat split; eauto using eval_value.
Qed.

Lemma vrel_protect_low : forall T v1 v2,
  vrel T v1 v2 ->
  vrel (ty_protect Low T) (protect_value v1 Low) (protect_value v2 Low).
Proof.
  intros T v1 v2 H. destruct (vrel_values _ _ _ H) as [H1 H2].
  rewrite ty_protect_low, (protect_value_low _ H1), (protect_value_low _ H2).
  exact H.
Qed.

Lemma vrel_protect_high : forall T v1 v2,
  value v1 -> value v2 ->
  vrel (ty_protect High T) (protect_value v1 High) (protect_value v2 High).
Proof.
  intros T v1 v2 H1 H2. destruct T; simpl;
    destruct s as [r i]; destruct r, i; simpl;
    repeat split; eauto using protect_value_value.
Qed.

Fixpoint inst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit k => tm_unit k
  | tm_abs A b k => tm_abs A (inst rho b) k
  | tm_app f a r => tm_app (inst rho f) (inst rho a) r
  | tm_pair a b k => tm_pair (inst rho a) (inst rho b) k
  | tm_fst a r => tm_fst (inst rho a) r
  | tm_snd a r => tm_snd (inst rho a) r
  | tm_inl a k => tm_inl (inst rho a) k
  | tm_inr a k => tm_inr (inst rho a) k
  | tm_case a b c r => tm_case (inst rho a) (inst rho b) (inst rho c) r
  | tm_protect l a => tm_protect l (inst rho a)
  | tm_if a b c r => tm_if (inst rho a) (inst rho b) (inst rho c) r
  end.

Definition rho_set (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

Definition envrel (Gamma : context) (rho1 rho2 : atom -> tm) : Prop :=
  (forall x, locally_closed (rho1 x) /\ locally_closed (rho2 x)) /\
  forall x T, lookup_context x Gamma = Some T ->
    termrel T (rho1 x) (rho2 x).

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H. induction H; unfold locally_closed in *; simpl in *; auto.
Qed.

Lemma open_rec_lc_at : forall t n k u,
  lc_at n t -> n <= k -> open_rec k u t = t.
Proof.
  intros t. induction t; intros depth k u Hle Hnk; simpl in *;
    try reflexivity;
    try (assert (k <> n) as Hneq by lia;
         apply Nat.eqb_neq in Hneq; now rewrite Hneq).
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end;
      f_equal; eauto using le_n_S with arith.
Qed.

Lemma open_rec_lc : forall t k u,
  locally_closed t -> open_rec k u t = t.
Proof.
  intros. eapply open_rec_lc_at; eauto. lia.
Qed.

Lemma inst_open_rec : forall t rho u k,
  (forall x, locally_closed (rho x)) ->
  inst rho (open_rec k u t) = open_rec k (inst rho u) (inst rho t).
Proof.
  intros t. induction t; intros rho u k Hlc; simpl;
    try (f_equal; eauto; fail).
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_lc. apply Hlc.
Qed.

Lemma inst_ext : forall t rho1 rho2,
  (forall x, In x (fv t) -> rho1 x = rho2 x) ->
  inst rho1 t = inst rho2 t.
Proof.
  intros t. induction t; intros rho1 rho2 Heq; simpl in *;
    try reflexivity;
    try (apply Heq; now left).
  all: f_equal;
    first [eapply IHt | eapply IHt1 | eapply IHt2 | eapply IHt3];
    intros x Hx; apply Heq;
    simpl; repeat rewrite in_app_iff; firstorder.
Qed.

Lemma rho_set_lc : forall rho x v,
  (forall y, locally_closed (rho y)) -> locally_closed v ->
  forall y, locally_closed (rho_set rho x v y).
Proof.
  intros rho x v Hr Hv y. unfold rho_set.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma inst_open_fresh : forall body rho x v,
  (forall y, locally_closed (rho y)) -> locally_closed v ->
  ~ In x (fv body) ->
  inst (rho_set rho x v) (open body (tm_fvar x)) =
    open (inst rho body) v.
Proof.
  intros body rho x v Hr Hv Hfresh. unfold open.
  rewrite inst_open_rec by (eapply rho_set_lc; eauto).
  simpl. unfold rho_set. rewrite Nat.eqb_refl.
  f_equal. apply inst_ext. intros y Hy.
  unfold rho_set. assert (x <> y) as Hneq.
  { intro Heq. apply Hfresh. now subst. }
  apply Nat.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Lemma envrel_update : forall Gamma rho1 rho2 x T v1 v2,
  envrel Gamma rho1 rho2 -> vrel T v1 v2 ->
  envrel (update Gamma x T) (rho_set rho1 x v1) (rho_set rho2 x v2).
Proof.
  intros Gamma rho1 rho2 x T v1 v2 [Hval Hrel] Hvr.
  destruct (vrel_values _ _ _ Hvr) as [Hv1 Hv2].
  pose proof (value_lc _ Hv1) as Hlc1.
  pose proof (value_lc _ Hv2) as Hlc2.
  split.
  - intro y. split.
    + eapply rho_set_lc; eauto. intro z. exact (proj1 (Hval z)).
    + eapply rho_set_lc; eauto. intro z. exact (proj2 (Hval z)).
  - intros y U Hlookup. unfold update in Hlookup; simpl in Hlookup.
    unfold rho_set. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      rewrite Nat.eqb_refl in Hlookup. inversion Hlookup; subst.
      intros w1 w2 E1 E2.
      pose proof (eval_value_inv _ _ Hv1 E1) as ->.
      pose proof (eval_value_inv _ _ Hv2 E2) as ->.
      exact Hvr.
    + apply Hrel. rewrite Nat.eqb_sym, E in Hlookup. exact Hlookup.
Qed.

Lemma security_le_low : forall k1 k2,
  security_le k1 k2 -> k2.(indirect_reader) = Low ->
  k1.(indirect_reader) = Low.
Proof.
  intros [r1 i1] [r2 i2] [_ Hi] Hlow.
  simpl in *. subst i2. destruct i1; simpl in *; auto; contradiction.
Qed.

Lemma vrel_at_high : forall T v1 v2,
  (security_of T).(indirect_reader) = High ->
  value v1 -> value v2 -> vrel T v1 v2.
Proof.
  intros T v1 v2 H H1 H2. destruct T; simpl in *;
    rewrite H; repeat split; auto.
Qed.

Lemma vrel_subtype : forall T U v1 v2,
  subtype T U -> vrel T v1 v2 -> vrel U v1 v2.
Proof.
  intros T U v1 v2 Hsub. revert v1 v2.
  induction Hsub; intros v1 v2 Hvr;
    try (eapply IHHsub2; eauto).
  - destruct (vrel_values _ _ _ Hvr) as [Hv1 Hv2].
    destruct (indirect_reader kappa2) eqn:Et.
    + assert (Es : indirect_reader kappa1 = Low)
        by (eapply security_le_low; eauto).
      simpl in *. rewrite Es in Hvr. rewrite Et.
      destruct Hvr as [_ [_ Hshape]].
      repeat split; auto.
    + eapply vrel_at_high; eauto.
  - destruct (vrel_values _ _ _ Hvr) as [Hv1 Hv2].
    destruct (indirect_reader kappa2) eqn:Et.
    + assert (Es : indirect_reader kappa1 = Low)
        by (eapply security_le_low; eauto).
      simpl in *. rewrite Es in Hvr. rewrite Et.
      destruct Hvr as [_ [_ Hshape]].
      repeat split; auto.
      destruct Hshape as [Hl | Hr].
      * destruct Hl as (a1 & a2 & k1 & k2 & E1 & E2 & K1 & K2 & Harg).
        left. exists a1, a2, k1, k2. repeat split; auto.
      * destruct Hr as (b1 & b2 & k1 & k2 & E1 & E2 & K1 & K2 & Harg).
        right. exists b1, b2, k1, k2. repeat split; auto.
    + eapply vrel_at_high; eauto.
  - destruct (vrel_values _ _ _ Hvr) as [Hv1 Hv2].
    destruct (indirect_reader kappa2) eqn:Et.
    + assert (Es : indirect_reader kappa1 = Low)
        by (eapply security_le_low; eauto).
      simpl in *. rewrite Es in Hvr. rewrite Et.
      destruct Hvr as [_ [_ Hshape]].
      repeat split; auto.
      destruct Hshape as (a1 & a2 & b1 & b2 & k1 & k2 & E1 & E2 & K1 & K2 & Ha & Hb).
      exists a1, a2, b1, b2, k1, k2. repeat split; auto.
    + eapply vrel_at_high; eauto.
  - destruct (vrel_values _ _ _ Hvr) as [Hv1 Hv2].
    destruct (indirect_reader kappa2) eqn:Et.
    + assert (Es : indirect_reader kappa1 = Low)
        by (eapply security_le_low; eauto).
      simpl in *. rewrite Es in Hvr. rewrite Et.
      destruct Hvr as [_ [_ [Hform Hfun]]].
      repeat split; auto.
      intros a1 a2 Ha r1 r2 w1 w2 E1 E2.
      eapply IHHsub2. eapply Hfun; eauto using IHHsub1.
    + eapply vrel_at_high; eauto.
Qed.

Definition fresh (L : list atom) : atom :=
  S (fold_right Nat.max 0 L).

Lemma list_le_max : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a xs IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [-> | H].
    + lia.
    + specialize (IH _ H). lia.
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L H. unfold fresh in H.
  pose proof (list_le_max _ _ H). lia.
Qed.

Lemma inst_id : forall t, inst tm_fvar t = t.
Proof.
  intro t. induction t; simpl; f_equal; auto.
Qed.

Lemma eval_app_abs_inv : forall A b k a r w,
  value (tm_abs A b k) -> value a ->
  eval (tm_app (tm_abs A b k) a r) w ->
  exists z, eval (open b a) z /\ w = protect_value z k.(indirect_reader).
Proof.
  intros A b k a r w Hf Ha He. inversion He; subst.
  pose proof (eval_value_inv _ _ Hf H2) as E1.
  pose proof (eval_value_inv _ _ Ha H3) as E2.
  inversion E1; subst.
  eexists. split; eauto.
Qed.

Lemma abs_compat : forall A B k b1 b2,
  (forall a1 a2, vrel A a1 a2 ->
     termrel B (open b1 a1) (open b2 a2)) ->
  termrel (Ty_Arrow A B k) (tm_abs A b1 k) (tm_abs A b2 k).
Proof.
  intros A B k b1 b2 Hbody v1 v2 E1 E2.
  inversion E1; inversion E2; subst.
  pose proof (eval_value _ _ E1) as Hv1.
  pose proof (eval_value _ _ E2) as Hv2.
  destruct (indirect_reader k) eqn:Ek.
  - simpl. rewrite Ek. split; [exact Hv1|].
    split; [exact Hv2|]. split.
    + exists A, b1, k, A, b2, k. repeat split; auto.
    + intros a1 a2 Ha r1 r2 w1 w2 Ea1 Ea2.
    destruct (vrel_values _ _ _ Ha) as [Hva1 Hva2].
    destruct (eval_app_abs_inv _ _ _ _ _ _ Hv1 Hva1 Ea1)
      as [z1 [Ez1 Ew1]].
    destruct (eval_app_abs_inv _ _ _ _ _ _ Hv2 Hva2 Ea2)
      as [z2 [Ez2 Ew2]].
    rewrite Ek in Ew1, Ew2.
    rewrite (protect_value_low _ (eval_value _ _ Ez1)) in Ew1.
    rewrite (protect_value_low _ (eval_value _ _ Ez2)) in Ew2.
    subst w1 w2. eapply Hbody; eauto.
  - eapply vrel_at_high; eauto.
Qed.

Lemma app_compat : forall A B k f1 f2 a1 a2 r,
  termrel (Ty_Arrow A B k) f1 f2 -> termrel A a1 a2 ->
  termrel (ty_protect k.(indirect_reader) B)
    (tm_app f1 a1 r) (tm_app f2 a2 r).
Proof.
  intros A B k f1 f2 a1 a2 r Hf Ha.
  destruct (indirect_reader k) eqn:Ek.
  - rewrite ty_protect_low.
    intros w1 w2 E1 E2. inversion E1; inversion E2; subst.
    pose proof (Hf _ _ H2 H10) as Hr.
    simpl in Hr. rewrite Ek in Hr.
    destruct Hr as [_ [_ Hfun]].
    pose proof (Ha _ _ H3 H11) as Harg.
    eapply Hfun; eauto 8 using E_App, eval_of_value.
    all: eapply E_App; eauto using eval_of_value, eval_value.
  - eapply termrel_high. now rewrite ty_protect_high.
Qed.

Lemma pair_compat : forall A B k a1 a2 b1 b2,
  termrel A a1 a2 -> termrel B b1 b2 ->
  termrel (Ty_Prod A B k)
    (tm_pair a1 b1 k) (tm_pair a2 b2 k).
Proof.
  intros A B k a1 a2 b1 b2 Ha Hb w1 w2 E1 E2.
  inversion E1; inversion E2; subst.
  destruct (indirect_reader k) eqn:Ek.
  - simpl. rewrite Ek. repeat split; eauto using eval_value.
    eexists _, _, _, _, _, _. repeat split; eauto.
  - eapply vrel_at_high; eauto using eval_value.
Qed.

Lemma inl_compat : forall A B k a1 a2,
  termrel A a1 a2 ->
  termrel (Ty_Sum A B k) (tm_inl a1 k) (tm_inl a2 k).
Proof.
  intros A B k a1 a2 Ha w1 w2 E1 E2.
  inversion E1; inversion E2; subst.
  destruct (indirect_reader k) eqn:Ek.
  - simpl. rewrite Ek. repeat split; eauto using eval_value.
    left. eexists _, _, _, _. repeat split; eauto.
  - eapply vrel_at_high; eauto using eval_value.
Qed.

Lemma inr_compat : forall A B k a1 a2,
  termrel B a1 a2 ->
  termrel (Ty_Sum A B k) (tm_inr a1 k) (tm_inr a2 k).
Proof.
  intros A B k a1 a2 Ha w1 w2 E1 E2.
  inversion E1; inversion E2; subst.
  destruct (indirect_reader k) eqn:Ek.
  - simpl. rewrite Ek. repeat split; eauto using eval_value.
    right. eexists _, _, _, _. repeat split; eauto.
  - eapply vrel_at_high; eauto using eval_value.
Qed.

Lemma fst_compat : forall A B k t1 t2 r,
  termrel (Ty_Prod A B k) t1 t2 ->
  termrel (ty_protect k.(indirect_reader) A)
    (tm_fst t1 r) (tm_fst t2 r).
Proof.
  intros A B k t1 t2 r Ht.
  destruct (indirect_reader k) eqn:Ek.
  - rewrite ty_protect_low. intros w1 w2 E1 E2.
    inversion E1; inversion E2; subst.
    pose proof (Ht _ _ H1 H6) as Hr.
    simpl in Hr. rewrite Ek in Hr.
    destruct Hr as [_ [_ (a1 & a2 & b1 & b2 & ka & kb &
      F1 & F2 & K1 & K2 & Ha & Hb)]].
    inversion F1; inversion F2; subst.
    destruct (vrel_values _ _ _ Ha) as [Hva1 Hva2].
    rewrite K1, K2.
    rewrite (protect_value_low _ Hva1), (protect_value_low _ Hva2).
    exact Ha.
  - eapply termrel_high. now rewrite ty_protect_high.
Qed.

Lemma snd_compat : forall A B k t1 t2 r,
  termrel (Ty_Prod A B k) t1 t2 ->
  termrel (ty_protect k.(indirect_reader) B)
    (tm_snd t1 r) (tm_snd t2 r).
Proof.
  intros A B k t1 t2 r Ht.
  destruct (indirect_reader k) eqn:Ek.
  - rewrite ty_protect_low. intros w1 w2 E1 E2.
    inversion E1; inversion E2; subst.
    pose proof (Ht _ _ H1 H6) as Hr.
    simpl in Hr. rewrite Ek in Hr.
    destruct Hr as [_ [_ (a1 & a2 & b1 & b2 & ka & kb &
      F1 & F2 & K1 & K2 & Ha & Hb)]].
    inversion F1; inversion F2; subst.
    destruct (vrel_values _ _ _ Hb) as [Hvb1 Hvb2].
    rewrite K1, K2.
    rewrite (protect_value_low _ Hvb1), (protect_value_low _ Hvb2).
    exact Hb.
  - eapply termrel_high. now rewrite ty_protect_high.
Qed.

Lemma protect_compat : forall T l t1 t2,
  termrel T t1 t2 ->
  termrel (ty_protect l T) (tm_protect l t1) (tm_protect l t2).
Proof.
  intros T l t1 t2 Ht. destruct l.
  - rewrite ty_protect_low. intros w1 w2 E1 E2.
    inversion E1; inversion E2; subst.
    rewrite (protect_value_low _ (eval_value _ _ H2)).
    rewrite (protect_value_low _ (eval_value _ _ H6)).
    eapply Ht; eauto.
  - eapply termrel_high. now rewrite ty_protect_high.
Qed.

Lemma case_compat : forall A B T k s1 s2 b11 b12 b21 b22 r,
  termrel (Ty_Sum A B k) s1 s2 ->
  (forall a1 a2, vrel A a1 a2 ->
     termrel T (open b11 a1) (open b12 a2)) ->
  (forall a1 a2, vrel B a1 a2 ->
     termrel T (open b21 a1) (open b22 a2)) ->
  termrel (ty_protect k.(indirect_reader) T)
    (tm_case s1 b11 b21 r) (tm_case s2 b12 b22 r).
Proof.
  intros A B T k s1 s2 b11 b12 b21 b22 r Hs Hl Hr.
  destruct (indirect_reader k) eqn:Ek.
  - rewrite ty_protect_low. intros w1 w2 E1 E2.
    inversion E1; inversion E2; subst.
    all: pose proof (Hs _ _ H4 H12) as Hsum;
      simpl in Hsum; rewrite Ek in Hsum;
      destruct Hsum as [_ [_ [Hshape | Hshape]]];
      destruct Hshape as (a1 & a2 & ka & kb & F1 & F2 & K1 & K2 & Harg);
      inversion F1; inversion F2; subst;
      rewrite K1, K2;
      rewrite (protect_value_low _ (eval_value _ _ H6)),
        (protect_value_low _ (eval_value _ _ H14));
      first [solve [eapply Hl; eauto] | solve [eapply Hr; eauto]].
  - eapply termrel_high. now rewrite ty_protect_high.
Qed.

Lemma open_branch_fundamental : forall L Gamma A body T rho1 rho2,
  (forall x, ~ In x L -> forall rho1' rho2',
    envrel (update Gamma x A) rho1' rho2' ->
    termrel T (inst rho1' (open body (tm_fvar x)))
      (inst rho2' (open body (tm_fvar x)))) ->
  envrel Gamma rho1 rho2 ->
  forall a1 a2, vrel A a1 a2 ->
    termrel T (open (inst rho1 body) a1) (open (inst rho2 body) a2).
Proof.
  intros L Gamma A body T rho1 rho2 Hbranch Henv a1 a2 Ha.
  set (x := fresh (L ++ fv body)).
  assert (Hfresh : ~ In x (L ++ fv body)) by apply fresh_notin.
  assert (HL : ~ In x L).
  { intro Hin. apply Hfresh. apply in_or_app. now left. }
  assert (Hbody : ~ In x (fv body)).
  { intro Hin. apply Hfresh. apply in_or_app. now right. }
  pose proof (Hbranch x HL (rho_set rho1 x a1) (rho_set rho2 x a2)
    (envrel_update _ _ _ _ _ _ _ Henv Ha)) as Hrel.
  destruct (vrel_values _ _ _ Ha) as [Hv1 Hv2].
  assert (E1 : inst (rho_set rho1 x a1) (open body (tm_fvar x)) =
               open (inst rho1 body) a1).
  { eapply inst_open_fresh; eauto using value_lc.
    intro y. exact (proj1 (proj1 Henv y)). }
  assert (E2 : inst (rho_set rho2 x a2) (open body (tm_fvar x)) =
               open (inst rho2 body) a2).
  { eapply inst_open_fresh; eauto using value_lc.
    intro y. exact (proj2 (proj1 Henv y)). }
  now rewrite E1, E2 in Hrel.
Qed.

Lemma if_compat : forall T k c1 c2 y1 y2 n1 n2 r,
  termrel (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) c1 c2 ->
  termrel T y1 y2 -> termrel T n1 n2 ->
  termrel (ty_protect k.(indirect_reader) T)
    (tm_if c1 y1 n1 r) (tm_if c2 y2 n2 r).
Proof.
  intros T k c1 c2 y1 y2 n1 n2 r Hc Hy Hn.
  destruct (indirect_reader k) eqn:Ek.
  - rewrite ty_protect_low. intros w1 w2 E1 E2.
    inversion E1; inversion E2; subst.
    all: pose proof (Hc _ _ H4 H12) as Hsum;
      simpl in Hsum; rewrite Ek in Hsum;
      destruct Hsum as [_ [_ [Hshape | Hshape]]];
      destruct Hshape as (a1 & a2 & ka & kb & F1 & F2 & K1 & K2 & Harg);
      inversion F1; inversion F2; subst;
      rewrite K1, K2;
      rewrite (protect_value_low _ (eval_value _ _ H6)),
        (protect_value_low _ (eval_value _ _ H14));
      first [solve [eapply Hy; eauto] | solve [eapply Hn; eauto]].
  - eapply termrel_high. now rewrite ty_protect_high.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho1 rho2, envrel Gamma rho1 rho2 ->
    termrel T (inst rho1 t) (inst rho2 t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho1 rho2 Henv; simpl.
  - (* variable *)
    destruct Henv as [_ Henv].
    exact (Henv _ _ H).
  - (* unit *)
    intros v1 v2 E1 E2. inversion E1; inversion E2; subst.
    destruct kappa as [r i]; destruct i; simpl;
      repeat split; eauto using v_unit.
    eexists _, _. repeat split; reflexivity.
  - (* abstraction *)
    eapply abs_compat. intros a1 a2 Ha.
    set (x := fresh (L ++ fv body)).
    assert (Hfresh : ~ In x (L ++ fv body)) by apply fresh_notin.
    assert (HL : ~ In x L).
    { intro Hin. apply Hfresh. apply in_or_app. now left. }
    assert (Hbody : ~ In x (fv body)).
    { intro Hin. apply Hfresh. apply in_or_app. now right. }
    pose proof (H2 x HL (rho_set rho1 x a1) (rho_set rho2 x a2)
      (envrel_update _ _ _ _ _ _ _ Henv Ha)) as Hr.
    destruct (vrel_values _ _ _ Ha) as [Hva1 Hva2].
    assert (E1 : inst (rho_set rho1 x a1) (open body (tm_fvar x)) =
                 open (inst rho1 body) a1).
    { eapply inst_open_fresh; eauto using value_lc.
      intro y. exact (proj1 (proj1 Henv y)). }
    assert (E2 : inst (rho_set rho2 x a2) (open body (tm_fvar x)) =
                 open (inst rho2 body) a2).
    { eapply inst_open_fresh; eauto using value_lc.
      intro y. exact (proj2 (proj1 Henv y)). }
    now rewrite E1, E2 in Hr.
  - (* application *)
    eapply app_compat; eauto.
  - (* pair *)
    eapply pair_compat; eauto.
  - (* first projection *)
    eapply fst_compat; eauto.
  - (* second projection *)
    eapply snd_compat; eauto.
  - (* left injection *)
    eapply inl_compat; eauto.
  - (* right injection *)
    eapply inr_compat; eauto.
  - (* case *)
    eapply case_compat.
    + eauto.
    + intros a1 a2 Ha. eapply open_branch_fundamental; eauto.
    + intros a1 a2 Ha. eapply open_branch_fundamental; eauto.
  - (* explicit protection *)
    eapply protect_compat; eauto.
  - (* subsumption *)
    intros v1 v2 E1 E2. eapply vrel_subtype; [exact H|].
    exact (IHHty _ _ Henv _ _ E1 E2).
  - (* conditional *)
    eapply if_compat; eauto.
Qed.

Lemma lc_open_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intro t. induction t; intros k x H; simpl in *;
    try exact I;
    try (destruct (Nat.eqb k n) eqn:E;
         [apply Nat.eqb_eq in E; lia | simpl in H; lia]).
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto.
Qed.

Lemma has_type_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty;
    unfold locally_closed in *; simpl in *; eauto;
    try tauto.
  all: repeat match goal with
       | H : forall x, ~ In x ?L -> lc_at 0 (open ?b (tm_fvar x)) |- _ =>
           let Hb := fresh "Hb" in
           pose proof (lc_open_inv b 0 (fresh L) (H _ (fresh_notin L))) as Hb;
           clear H
       end; tauto.
Qed.

Definition context_fv (C : program_context) : list atom :=
  fv (plug C (tm_unit public)).

Lemma inst_single_fresh : forall t x v,
  ~ In x (fv t) -> inst (rho_set tm_fvar x v) t = t.
Proof.
  intros t x v Hfresh. transitivity (inst tm_fvar t).
  2: apply inst_id.
  apply inst_ext. intros y Hy. unfold rho_set.
  assert (x <> y) as Hneq.
  { intro E. apply Hfresh. now subst. }
  apply Nat.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Lemma inst_plug_single : forall C x v,
  ~ In x (context_fv C) ->
  inst (rho_set tm_fvar x v) (plug C (tm_fvar x)) = plug C v.
Proof.
  intros C. induction C; intros x v Hfresh;
    unfold context_fv in Hfresh; simpl in *;
    try (unfold rho_set; now rewrite Nat.eqb_refl).
  all: f_equal;
    try (apply IHC; intro Hin; apply Hfresh;
         simpl; repeat rewrite in_app_iff; firstorder);
    try (apply inst_single_fresh; intro Hin; apply Hfresh;
         simpl; repeat rewrite in_app_iff; firstorder).
Qed.

Lemma envrel_single : forall x T t1 t2,
  locally_closed t1 -> locally_closed t2 -> termrel T t1 t2 ->
  envrel (update empty x T)
    (rho_set tm_fvar x t1) (rho_set tm_fvar x t2).
Proof.
  intros x T t1 t2 Hlc1 Hlc2 Hr. split.
  - intro y. unfold rho_set. destruct (Nat.eqb x y);
      unfold locally_closed in *; simpl; auto.
  - intros y U Hlookup. unfold update, empty in Hlookup.
    simpl in Hlookup. destruct (Nat.eqb y x) eqn:E;
      try discriminate.
    apply Nat.eqb_eq in E. subst y.
    inversion Hlookup; subst U. unfold rho_set.
    now rewrite Nat.eqb_refl.
Qed.

Lemma vrel_ground_erase : forall T k v1 v2,
  ground T -> transparent_at k T -> k.(indirect_reader) = Low ->
  vrel T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  induction T; intros k v1 v2 Hg Htr Hlow Hr;
    simpl in Hg, Htr.
  - destruct Htr as [Hle _].
    assert (E : indirect_reader s = Low)
      by (eapply security_le_low; eauto).
    simpl in Hr. rewrite E in Hr.
    destruct Hr as [_ [_ (k1 & k2 & F1 & F2 & K1 & K2)]].
    subst. reflexivity.
  - destruct Htr as [Hle [Htr1 Htr2]].
    assert (E : indirect_reader s = Low)
      by (eapply security_le_low; eauto).
    simpl in Hr. rewrite E in Hr.
    destruct Hr as [_ [_ [Hl | Hr]]].
    + destruct Hl as (a1 & a2 & k1 & k2 & F1 & F2 & K1 & K2 & Ha).
      subst. simpl. f_equal. eapply IHT1; eauto. exact (proj1 Hg).
    + destruct Hr as (b1 & b2 & k1 & k2 & F1 & F2 & K1 & K2 & Hb).
      subst. simpl. f_equal. eapply IHT2; eauto. exact (proj2 Hg).
  - destruct Htr as [Hle [Htr1 Htr2]].
    assert (E : indirect_reader s = Low)
      by (eapply security_le_low; eauto).
    simpl in Hr. rewrite E in Hr.
    destruct Hr as [_ [_ (a1 & a2 & b1 & b2 & k1 & k2 &
      F1 & F2 & K1 & K2 & Ha & Hb)]].
    subst. simpl. f_equal.
    + eapply IHT1; eauto. exact (proj1 Hg).
    + eapply IHT2; eauto. exact (proj2 Hg).
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
  intros C t1 t2 T_secret T_result Ht1 Ht2 Hctx Hg Htr Hnonflow.
  assert (Hs : (security_of T_secret).(indirect_reader) = High).
  { destruct (security_of T_secret).(indirect_reader);
      destruct (security_of T_result).(indirect_reader);
      simpl in Hnonflow; auto; contradiction. }
  assert (Hr : (security_of T_result).(indirect_reader) = Low).
  { destruct (security_of T_secret).(indirect_reader);
      destruct (security_of T_result).(indirect_reader);
      simpl in Hnonflow; auto; contradiction. }
  destruct Hctx as [L Hctx].
  set (x := fresh (L ++ context_fv C)).
  assert (Hfresh : ~ In x (L ++ context_fv C)) by apply fresh_notin.
  assert (HL : ~ In x L).
  { intro Hin. apply Hfresh. apply in_or_app. now left. }
  assert (HC : ~ In x (context_fv C)).
  { intro Hin. apply Hfresh. apply in_or_app. now right. }
  pose proof (termrel_high T_secret t1 t2 Hs) as Hsecret.
  pose proof (envrel_single x T_secret t1 t2
    (has_type_lc _ _ _ Ht1) (has_type_lc _ _ _ Ht2) Hsecret) as Henv.
  pose proof (fundamental _ _ _ (Hctx x HL) _ _ Henv) as Hrel.
  rewrite (inst_plug_single C x t1 HC) in Hrel.
  rewrite (inst_plug_single C x t2 HC) in Hrel.
  intros v1 v2 [E1 Hv1] [E2 Hv2].
  pose proof (Hrel _ _ (multi_to_eval _ _ E1 Hv1)
    (multi_to_eval _ _ E2 Hv2)) as Hvr.
  eapply vrel_ground_erase; eauto.
Qed.
