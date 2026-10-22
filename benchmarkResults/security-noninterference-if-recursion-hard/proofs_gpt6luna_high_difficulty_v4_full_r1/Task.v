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
  | Ty_Arrow : ty -> ty -> security -> ty
  | Ty_Nat : security -> ty.

Definition security_of (T : ty) : security :=
  match T with
  | Ty_Unit kappa | Ty_Nat kappa => kappa
  | Ty_Sum _ _ kappa | Ty_Prod _ _ kappa | Ty_Arrow _ _ kappa => kappa
  end.

Definition ty_protect (l : label) (T : ty) : ty :=
  match T with
  | Ty_Unit kappa => Ty_Unit (protect_security kappa l)
  | Ty_Nat kappa => Ty_Nat (protect_security kappa l)
  | Ty_Sum T1 T2 kappa => Ty_Sum T1 T2 (protect_security kappa l)
  | Ty_Prod T1 T2 kappa => Ty_Prod T1 T2 (protect_security kappa l)
  | Ty_Arrow T1 T2 kappa => Ty_Arrow T1 T2 (protect_security kappa l)
  end.

Fixpoint wf_ty (T : ty) : Prop :=
  match T with
  | Ty_Unit kappa | Ty_Nat kappa => wf_security kappa
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
  | tm_nat : nat -> security -> tm
  | tm_succ : tm -> label -> tm
  | tm_natrec : tm -> tm -> tm -> label -> tm
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
  | tm_nat n s => tm_nat n s
  | tm_succ t r => tm_succ (open_rec k u t) r
  | tm_natrec n b s r => tm_natrec (open_rec k u n) (open_rec k u b) (open_rec k u s) r
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
  | tm_nat n s => tm_nat n s
  | tm_succ t r => tm_succ (subst x u t) r
  | tm_natrec n b s r => tm_natrec (subst x u n) (subst x u b) (subst x u s) r
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_unit _ | tm_nat _ _ => []
  | tm_fvar x => [x]
  | tm_abs _ body _ => fv body
  | tm_app t1 t2 _ | tm_pair t1 t2 _ => fv t1 ++ fv t2
  | tm_fst t1 _ | tm_snd t1 _ | tm_inl t1 _ | tm_inr t1 _
  | tm_protect _ t1 | tm_succ t1 _ => fv t1
  | tm_natrec n b s _ => fv n ++ fv b ++ fv s
  | tm_case t0 body1 body2 _ | tm_if t0 body1 body2 _ => fv t0 ++ fv body1 ++ fv body2
  end.

Fixpoint lc_at (k : nat) (t : tm) : Prop :=
  match t with
  | tm_bvar i => i < k
  | tm_fvar _ | tm_unit _ | tm_nat _ _ => True
  | tm_abs _ body _ => lc_at (S k) body
  | tm_app t1 t2 _ | tm_pair t1 t2 _ => lc_at k t1 /\ lc_at k t2
  | tm_fst t1 _ | tm_snd t1 _ | tm_inl t1 _ | tm_inr t1 _
  | tm_protect _ t1 | tm_succ t1 _ => lc_at k t1
  | tm_natrec n b s _ => lc_at k n /\ lc_at k b /\ lc_at k s
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
  | v_inr : forall v kappa, value v -> value (tm_inr v kappa)
  | v_nat : forall n kappa, value (tm_nat n kappa).

Definition protect_value (v : tm) (l : label) : tm :=
  match v with
  | tm_unit kappa => tm_unit (protect_security kappa l)
  | tm_abs T body kappa => tm_abs T body (protect_security kappa l)
  | tm_pair v1 v2 kappa => tm_pair v1 v2 (protect_security kappa l)
  | tm_inl v1 kappa => tm_inl v1 (protect_security kappa l)
  | tm_inr v1 kappa => tm_inr v1 (protect_security kappa l)
  | tm_nat n kappa => tm_nat n (protect_security kappa l)
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
  | Ty_Nat _ => Ty_Nat public
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
  | tm_nat n _ => tm_nat n public
  | tm_succ t _ => tm_succ (erase_security t) Low
  | tm_natrec n b s _ => tm_natrec (erase_security n) (erase_security b) (erase_security s) Low
  end.

Fixpoint natrec_unroll (n : nat) (base step_function : tm) (r : label) : tm :=
  match n with
  | O => base
  | S k => tm_app (tm_app step_function (tm_nat k public) r)
                  (natrec_unroll k base step_function r) r
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
  | ST_Succ : forall t t' r,
      t --> t' -> tm_succ t r --> tm_succ t' r
  | ST_SuccNat : forall n k r,
      flows_to k.(reader) r ->
      tm_succ (tm_nat n k) r --> tm_protect k.(indirect_reader) (tm_nat (S n) public)
  | ST_RecArg : forall n n' b s r,
      n --> n' -> tm_natrec n b s r --> tm_natrec n' b s r
  | ST_RecBase : forall n k b b' s r,
      b --> b' -> tm_natrec (tm_nat n k) b s r --> tm_natrec (tm_nat n k) b' s r
  | ST_RecStep : forall n k b s s' r,
      value b -> s --> s' -> tm_natrec (tm_nat n k) b s r --> tm_natrec (tm_nat n k) b s' r
  | ST_RecUnroll : forall n k b s r,
      value b -> value s -> flows_to k.(reader) r ->
      tm_natrec (tm_nat n k) b s r --> tm_protect k.(indirect_reader) (natrec_unroll n b s r)
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
  | S_Trans : forall T U V, subtype T U -> subtype U V -> subtype T V
  | S_Nat : forall k1 k2, wf_security k1 -> wf_security k2 -> security_le k1 k2 ->
      subtype (Ty_Nat k1) (Ty_Nat k2).

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
  | T_Nat : forall Gamma n k, wf_security k -> has_type Gamma (tm_nat n k) (Ty_Nat k)
  | T_Succ : forall Gamma t k r,
      has_type Gamma t (Ty_Nat k) -> flows_to k.(reader) r ->
      has_type Gamma (tm_succ t r) (ty_protect k.(indirect_reader) (Ty_Nat public))
  | T_NatRec : forall Gamma n b s k T r,
      has_type Gamma n (Ty_Nat k) -> has_type Gamma b T ->
      has_type Gamma s (Ty_Arrow (Ty_Nat public) (Ty_Arrow T T public) public) ->
      flows_to k.(reader) r ->
      has_type Gamma (tm_natrec n b s r) (ty_protect k.(indirect_reader) T)
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
  | C_Succ : program_context -> label -> program_context
  | C_RecArg : program_context -> tm -> tm -> label -> program_context
  | C_RecBase : tm -> program_context -> tm -> label -> program_context
  | C_RecStep : tm -> tm -> program_context -> label -> program_context
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
  | C_Succ C' r => tm_succ (plug C' t) r
  | C_RecArg C' b s r => tm_natrec (plug C' t) b s r
  | C_RecBase n C' s r => tm_natrec n (plug C' t) s r
  | C_RecStep n b C' r => tm_natrec n b (plug C' t) r
  end.

Definition context_has_type (C : program_context) (T_hole T_result : ty) : Prop :=
  exists L : list atom, forall x : atom, ~ In x L ->
    has_type (update empty x T_hole) (plug C (tm_fvar x)) T_result.

Fixpoint ground (T : ty) : Prop :=
  match T with
  | Ty_Unit _ | Ty_Nat _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ => ground T1 /\ ground T2
  | Ty_Arrow _ _ _ => False
  end.

Fixpoint transparent_at (kappa : security) (T : ty) : Prop :=
  security_le (security_of T) kappa /\
  match T with
  | Ty_Unit _ | Ty_Nat _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      transparent_at kappa T1 /\ transparent_at kappa T2
  end.

Definition transparent (T : ty) : Prop := transparent_at (security_of T) T.

Definition same_result (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm,
    evaluates t1 v1 -> evaluates t2 v2 ->
    erase_security v1 = erase_security v2.

(* The observer-indexed relation used below deliberately forgets values whose
   indirect reader is above the observer.  At visible products and sums it
   relates their components; at arrows it is extensional, and accounts for
   the protection applied by function invocation. *)
Definition security_bound (observer : label) (T : ty) (k : security) : Prop :=
  match observer with
  | Low => flows_to k.(indirect_reader) (security_of T).(indirect_reader)
  | High => True
  end.

Fixpoint value_rel (observer : label) (T : ty) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_Unit kappa =>
      match kappa.(indirect_reader), observer with
      | High, Low => True
      | _, _ => exists k1 k2, v1 = tm_unit k1 /\ v2 = tm_unit k2 /\
          security_bound observer (Ty_Unit kappa) k1 /\ security_bound observer (Ty_Unit kappa) k2
      end
  | Ty_Nat kappa =>
      match kappa.(indirect_reader), observer with
      | High, Low => True
      | _, _ => exists n1 n2 k1 k2,
          v1 = tm_nat n1 k1 /\ v2 = tm_nat n2 k2 /\ n1 = n2 /\
          security_bound observer (Ty_Nat kappa) k1 /\ security_bound observer (Ty_Nat kappa) k2
      end
  | Ty_Sum A B kappa =>
      match kappa.(indirect_reader), observer with
      | High, Low => True
      | _, _ =>
          (exists a1 a2 k1 k2, v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\
             value_rel observer A a1 a2 /\ security_bound observer (Ty_Sum A B kappa) k1 /\
             security_bound observer (Ty_Sum A B kappa) k2) \/
          (exists b1 b2 k1 k2, v1 = tm_inr b1 k1 /\ v2 = tm_inr b2 k2 /\
             value_rel observer B b1 b2 /\ security_bound observer (Ty_Sum A B kappa) k1 /\
             security_bound observer (Ty_Sum A B kappa) k2)
      end
  | Ty_Prod A B kappa =>
      match kappa.(indirect_reader), observer with
      | High, Low => True
      | _, _ => exists a1 a2 b1 b2 k1 k2,
          v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
          security_bound observer (Ty_Prod A B kappa) k1 /\
          security_bound observer (Ty_Prod A B kappa) k2 /\
          value_rel observer A a1 a2 /\ value_rel observer B b1 b2
      end
  | Ty_Arrow A B kappa =>
      match kappa.(indirect_reader), observer with
      | High, Low => True
      | _, _ => exists T1 T2 b1 b2 k1 k2,
          v1 = tm_abs T1 b1 k1 /\ v2 = tm_abs T2 b2 k2 /\
          security_bound observer (Ty_Arrow A B kappa) k1 /\
          security_bound observer (Ty_Arrow A B kappa) k2 /\
          (forall a1 a2 w1 w2,
             value_rel observer A a1 a2 ->
             value a1 -> value a2 ->
             evaluates (tm_app v1 a1 k1.(reader)) w1 ->
             evaluates (tm_app v2 a2 k2.(reader)) w2 ->
             value_rel (join observer kappa.(indirect_reader)) B w1 w2)
      end
  end.

Definition term_rel (observer : label) (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, evaluates t1 v1 -> evaluates t2 v2 ->
    value_rel observer T v1 v2.

Lemma flows_low_eq : forall l, flows_to l Low -> l = Low.
Proof. destruct l; simpl; intros; [reflexivity|contradiction]. Qed.

Lemma flows_refl : forall l, flows_to l l.
Proof. destruct l; simpl; exact I. Qed.

Lemma flows_trans : forall l1 l2 l3,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof. destruct l1,l2,l3; simpl; intuition. Qed.

Lemma join_low_eq : forall l1 l2, join l1 l2 = Low -> l1 = Low /\ l2 = Low.
Proof. destruct l1, l2; simpl; intuition congruence. Qed.

Lemma transparent_ir_flow : forall T kappa,
  transparent_at kappa T ->
  flows_to (security_of T).(indirect_reader) kappa.(indirect_reader).
Proof.
  induction T; intros kappa H; simpl in *;
    destruct H as [H _]; unfold security_le in H; tauto.
Qed.

Lemma transparent_visible : forall T kappa,
  transparent_at kappa T -> kappa.(indirect_reader) = Low ->
  (security_of T).(indirect_reader) = Low.
Proof.
  intros T kappa Ht Hlow.
  pose proof (transparent_ir_flow T kappa Ht) as Hflow.
  rewrite Hlow in Hflow. destruct (security_of T) as [r ir]; simpl in *.
  destruct ir; simpl in *; [reflexivity|contradiction].
Qed.

Lemma visible_ground_erasure : forall kappa T v1 v2,
  ground T -> transparent_at kappa T -> kappa.(indirect_reader) = Low ->
  value_rel Low T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  intros kappa T. induction T; intros v1 v2 Hground Htrans Hlow Hrel; simpl in *.
  - assert (Htop : (security_of (Ty_Unit s)).(indirect_reader) = Low).
    { eapply transparent_visible; eassumption. }
    simpl in Htop.
    rewrite Htop in Hrel. simpl in Hrel.
    destruct (indirect_reader s); simpl in *.
    + destruct Hrel as [k1 [k2 [-> [-> [_ _]]]]]; reflexivity.
    + discriminate.
  - destruct Hground as [Hg1 Hg2].
    destruct Htrans as [Hle [Ht1 Ht2]].
    assert (Htop : (security_of (Ty_Sum T1 T2 s)).(indirect_reader) = Low).
    { unfold security_le in Hle. apply flows_low_eq.
      rewrite <- Hlow. exact (proj2 Hle). }
    simpl in Htop.
    rewrite Htop in Hrel. simpl in Hrel.
    destruct Hrel as [[a1 [a2 [k1 [k2 [-> [-> [Hsub [_ _]]]]]]]]|
                      [b1 [b2 [k1 [k2 [-> [-> [Hsub [_ _]]]]]]]]].
    + simpl. f_equal. eapply IHT1; eauto.
    + simpl. f_equal. eapply IHT2; eauto.
  - destruct Hground as [Hg1 Hg2].
    destruct Htrans as [Hle [Ht1 Ht2]].
    assert (Htop : (security_of (Ty_Prod T1 T2 s)).(indirect_reader) = Low).
    { unfold security_le in Hle. apply flows_low_eq.
      rewrite <- Hlow. exact (proj2 Hle). }
    simpl in Htop.
    rewrite Htop in Hrel. simpl in Hrel.
    destruct Hrel as [a1 [a2 [b1 [b2 [k1 [k2 [-> [-> [_ [_ [Ha Hb]]]]]]]]]]].
    simpl. f_equal; [eapply IHT1 | eapply IHT2]; eauto.
  - contradiction.
  - assert (Htop : (security_of (Ty_Nat s)).(indirect_reader) = Low).
    { eapply transparent_visible; eassumption. }
    simpl in Htop. rewrite Htop in Hrel. simpl in Hrel.
    destruct Hrel as [n1 [n2 [k1 [k2 [-> [-> [-> [_ _]]]]]]]]. reflexivity.
Qed.

Lemma nonflow_high_low : forall l1 l2,
  ~ flows_to l1 l2 -> l1 = High /\ l2 = Low.
Proof. destruct l1, l2; simpl; intuition congruence. Qed.

Lemma noninterference_label_obligations : forall T_secret T_result,
  ~ flows_to (security_of T_secret).(indirect_reader)
      (security_of T_result).(indirect_reader) ->
  (security_of T_secret).(indirect_reader) = High /\
  (security_of T_result).(indirect_reader) = Low.
Proof.
  intros. apply nonflow_high_low. assumption.
Qed.

Lemma hidden_values_related : forall T v1 v2,
  (security_of T).(indirect_reader) = High ->
  value_rel Low T v1 v2.
Proof.
  destruct T; simpl; intros v1 v2 H; rewrite H; simpl; exact I.
Qed.

Lemma value_rel_protect : forall observer l T v1 v2,
  value_rel (join observer l) T v1 v2 ->
  value_rel observer (ty_protect l T) v1 v2.
Proof.
  intros observer l T. destruct observer, l, T; simpl; intros v1 v2 H.
  all: try exact H.
  all: destruct s as [r i]; destruct i; simpl in *; try exact H; exact I.
Qed.

Lemma hidden_evaluations_related : forall T t1 t2 v1 v2,
  (security_of T).(indirect_reader) = High ->
  evaluates t1 v1 -> evaluates t2 v2 -> value_rel Low T v1 v2.
Proof.
  intros. eapply hidden_values_related; eassumption.
Qed.

Lemma transparent_ground_relation_erases : forall T v1 v2,
  ground T -> transparent T -> (security_of T).(indirect_reader) = Low ->
  value_rel Low T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  intros T v1 v2 Hg Ht Hlow Hrel.
  eapply visible_ground_erasure; eauto.
Qed.

Lemma term_rel_ground_same_result : forall T t1 t2,
  ground T -> transparent T -> (security_of T).(indirect_reader) = Low ->
  term_rel Low T t1 t2 -> same_result t1 t2.
Proof.
  intros T t1 t2 Hg Ht Hlow Hrel v1 v2 He1 He2.
  eapply transparent_ground_relation_erases; eauto.
Qed.

Lemma subst_fresh : forall t x u, ~ In x (fv t) -> subst x u t = t.
Proof.
  induction t; intros x u Hfresh; simpl in *;
    repeat rewrite in_app_iff in Hfresh; try reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. simpl; auto.
    + reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal; [apply IHt1 | apply IHt2]; tauto.
  - f_equal; [apply IHt1 | apply IHt2]; tauto.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; tauto.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; tauto.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; tauto.
Qed.

Fixpoint context_fv (C : program_context) : list atom :=
  match C with
  | C_Hole => []
  | C_Abs _ C' _ | C_Fst C' _ | C_Snd C' _ | C_Inl C' _ | C_Inr C' _
  | C_Protect _ C' | C_Succ C' _ => context_fv C'
  | C_AppLeft C' t _ | C_PairLeft C' t _ => context_fv C' ++ fv t
  | C_AppRight t C' _ | C_PairRight t C' _ => fv t ++ context_fv C'
  | C_CaseScrutinee C' t1 t2 _ | C_IfCondition C' t1 t2 _ =>
      context_fv C' ++ fv t1 ++ fv t2
  | C_CaseLeft t0 C' t2 _ | C_IfThen t0 C' t2 _ =>
      fv t0 ++ context_fv C' ++ fv t2
  | C_CaseRight t0 t1 C' _ | C_IfElse t0 t1 C' _ =>
      fv t0 ++ fv t1 ++ context_fv C'
  | C_RecArg C' b s _ => context_fv C' ++ fv b ++ fv s
  | C_RecBase n C' s _ => fv n ++ context_fv C' ++ fv s
  | C_RecStep n b C' _ => fv n ++ fv b ++ context_fv C'
  end.

Lemma subst_plug_fresh_context : forall C x u,
  ~ In x (context_fv C) ->
  subst x u (plug C (tm_fvar x)) = plug C u.
Proof.
  induction C; intros x u Hfresh; simpl in *; try reflexivity.
  all: repeat rewrite in_app_iff in Hfresh.
  all: simpl; f_equal; try (eapply IHC; tauto);
    try (rewrite subst_fresh by tauto; reflexivity).
  all: now rewrite Nat.eqb_refl.
Qed.

Fixpoint subst_context (Gamma : context) (rho : atom -> tm) (t : tm) : tm :=
  match Gamma with
  | [] => t
  | (x, _) :: Gamma' => subst_context Gamma' rho (subst x (rho x) t)
  end.

Definition closed_environment (rho : atom -> tm) : Prop :=
  forall x, closed (rho x).

Lemma subst_context_closed : forall Gamma rho t,
  closed_environment rho -> fv t = [] -> subst_context Gamma rho t = t.
Proof.
  induction Gamma as [|[x T] Gamma IH]; intros rho t Henv Hclosed; simpl; auto.
  assert (E : subst x (rho x) t = t).
  { apply subst_fresh. rewrite Hclosed. simpl. tauto. }
  rewrite E. apply IH; assumption.
Qed.

Lemma subst_context_fvar : forall Gamma rho x T,
  lookup_context x Gamma = Some T -> closed_environment rho ->
  subst_context Gamma rho (tm_fvar x) = rho x.
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros rho x T Hlookup Henv; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; subst. inversion Hlookup; subst.
      simpl. rewrite Nat.eqb_refl. eapply subst_context_closed.
      * exact Henv.
      * exact (proj2 (Henv y)).
    + assert (F : Nat.eqb y x = false).
      { apply Nat.eqb_neq. intro H. subst. rewrite Nat.eqb_refl in E. discriminate. }
      simpl. rewrite F. eapply IH; eauto.
Qed.

Lemma lc_at_incr : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t Hlc. revert k Hlc. induction t; intros k Hlc; simpl in *; try lia.
  - apply IHt. exact Hlc.
  - destruct Hlc as [H1 H2]. split; [eapply IHt1 | eapply IHt2]; eassumption.
  - destruct Hlc as [H1 H2]. split; [eapply IHt1 | eapply IHt2]; eassumption.
  - apply IHt. exact Hlc.
  - apply IHt. exact Hlc.
  - apply IHt. exact Hlc.
  - apply IHt. exact Hlc.
  - destruct Hlc as [H0 [H1 H2]]. repeat split; eauto.
  - apply IHt. exact Hlc.
  - apply IHt. exact Hlc.
  - destruct Hlc as [H0 [H1 H2]]. repeat split; eauto.
  - destruct Hlc as [H0 [H1 H2]]. repeat split; eauto.
Qed.

Lemma lc_at_mono : forall j k t, j <= k -> lc_at j t -> lc_at k t.
Proof.
  intros j k t Hjk Hlc. induction Hjk.
  - exact Hlc.
  - apply lc_at_incr. exact IHHjk.
Qed.

Lemma open_rec_lc : forall k t v, lc_at k t -> open_rec k v t = t.
Proof.
  intros k t v Hlc. revert k v Hlc. induction t; intros k v Hlc; simpl in *; try reflexivity.
  try (destruct (Nat.eqb k n) eqn:E;
       [apply Nat.eqb_eq in E; subst; lia|reflexivity]).
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end;
    f_equal; eauto.
Qed.

Lemma subst_open_rec : forall t k v x u,
  locally_closed u ->
  subst x u (open_rec k v t) = open_rec k (subst x u v) (subst x u t).
Proof.
  induction t; intros k v x u Hlc; simpl; try reflexivity.
  try solve [destruct (Nat.eqb k n); reflexivity].
  all: try (destruct (Nat.eqb x a); simpl; try reflexivity;
    rewrite open_rec_lc with (k := k) (v := subst x u v); auto;
    unfold locally_closed in Hlc;
    eapply lc_at_mono with (j := 0); [lia|exact Hlc]).
  all: f_equal; eauto.
Qed.

Lemma subst_open_fresh : forall body x y u,
  x <> y -> locally_closed u ->
  subst x u (open body (tm_fvar y)) =
  open (subst x u body) (tm_fvar y).
Proof.
  intros body x y u Hxy Hlc. unfold open.
  rewrite subst_open_rec by exact Hlc.
  simpl. assert (Nat.eqb x y = false) as E.
  { apply Nat.eqb_neq. exact Hxy. }
  rewrite E. reflexivity.
Qed.

Fixpoint context_atoms (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x, _) :: Gamma' => x :: context_atoms Gamma'
  end.

Lemma subst_context_open : forall Gamma rho body y,
  ~ In y (context_atoms Gamma) -> closed_environment rho ->
  subst_context Gamma rho (open body (tm_fvar y)) =
  open (subst_context Gamma rho body) (tm_fvar y).
Proof.
  induction Gamma as [|[x T] Gamma IH]; intros rho body y Hfresh Henv; simpl; auto.
  assert (Hxy : x <> y) by (intro E; subst; apply Hfresh; simpl; auto).
  rewrite subst_open_fresh with (u := rho x) by
    (try assumption; exact (proj1 (Henv x))).
  rewrite IH; auto. intro Hin. apply Hfresh. simpl; right; exact Hin.
Qed.

Lemma multi_pair_inv : forall t1 t2 k v,
  multi (tm_pair t1 t2 k) v -> value v ->
  exists v1 v2, v = tm_pair v1 v2 k /\ evaluates t1 v1 /\ evaluates t2 v2.
Proof.
  intros t1 t2 k v Hmulti Hv.
  assert (Hgen : forall t w, multi t w -> value w ->
      forall a b q, t = tm_pair a b q ->
      exists a' b', w = tm_pair a' b' q /\ evaluates a a' /\ evaluates b b').
  { intros t w Hm. induction Hm; intros Hval a b q Hstart.
    - inversion Hval; subst; try discriminate.
      inversion H1; subst. exists a, b. repeat split; try reflexivity;
        eauto using multi_refl.
    - rewrite Hstart in H. inversion H; subst.
      + destruct (IHHm Hval t1' b q eq_refl) as [w1 [w2 [E [He1 He2]]]].
        exists w1, w2. split; [exact E|]. split.
        * destruct He1 as [Hm1 Hv1]. split; [econstructor; eassumption|exact Hv1].
        * exact He2.
      + destruct (IHHm Hval a t2' q eq_refl) as [w1 [w2 [E [He1 He2]]]].
        exists w1, w2. split; [exact E|]. split.
        * exact He1.
        * destruct He2 as [Hm2 Hv2]. split; [econstructor; eassumption|exact Hv2]. }
  eapply Hgen; eauto.
Qed.

Lemma evaluates_pair_inv : forall t1 t2 k v,
  evaluates (tm_pair t1 t2 k) v ->
  exists v1 v2, v = tm_pair v1 v2 k /\ evaluates t1 v1 /\ evaluates t2 v2.
Proof.
  intros t1 t2 k v [Hm Hv]. eapply multi_pair_inv; eassumption.
Qed.

Lemma evaluates_fst_inv : forall t r w,
  evaluates (tm_fst t r) w ->
  exists a b k, evaluates t (tm_pair a b k) /\
    evaluates (tm_protect k.(indirect_reader) a) w.
Proof.
  intros t r w [Hm Hw].
  assert (Hgen : forall t0 w0, multi t0 w0 -> value w0 -> forall u q,
    t0 = tm_fst u q -> exists a b k, evaluates u (tm_pair a b k) /\
      evaluates (tm_protect k.(indirect_reader) a) w0).
  { intros t0 w0 Hmulti. induction Hmulti; intros Hval u q Hstart.
    - subst. inversion Hval.
    - rewrite Hstart in H. inversion H; subst.
      + exists v1,v2,kappa. split.
        * split; [constructor|constructor; assumption].
        * split; [exact Hmulti|exact Hval].
      + destruct (IHHmulti Hval t' q eq_refl) as [a [b [k [Hu Hw0]]]].
        exists a,b,k. split.
        * destruct Hu as [Hm' Hv']. split; [econstructor; eassumption|exact Hv'].
        * exact Hw0.
      }
  eapply Hgen; eauto.
Qed.

Lemma evaluates_snd_inv : forall t r w,
  evaluates (tm_snd t r) w ->
  exists a b k, evaluates t (tm_pair a b k) /\
    evaluates (tm_protect k.(indirect_reader) b) w.
Proof.
  intros t r w [Hm Hw].
  assert (Hgen : forall t0 w0, multi t0 w0 -> value w0 -> forall u q,
    t0 = tm_snd u q -> exists a b k, evaluates u (tm_pair a b k) /\
      evaluates (tm_protect k.(indirect_reader) b) w0).
  { intros t0 w0 Hmulti. induction Hmulti; intros Hval u q Hstart.
    - subst. inversion Hval.
    - rewrite Hstart in H. inversion H; subst.
      + exists v1,v2,kappa. split.
        * split; [constructor|constructor; assumption].
        * split; [exact Hmulti|exact Hval].
      + destruct (IHHmulti Hval t' q eq_refl) as [a [b [k [Hu Hw0]]]].
        exists a,b,k. split.
        * destruct Hu as [Hm' Hv']. split; [econstructor; eassumption|exact Hv'].
        * exact Hw0.
      }
  eapply Hgen; eauto.
Qed.

Lemma evaluates_case_inv : forall c b1 b2 r w,
  evaluates (tm_case c b1 b2 r) w ->
  (exists a k, value a /\ evaluates c (tm_inl a k) /\
      evaluates (tm_protect k.(indirect_reader) (open b1 a)) w) \/
  (exists a k, value a /\ evaluates c (tm_inr a k) /\
      evaluates (tm_protect k.(indirect_reader) (open b2 a)) w).
Proof.
  intros c b1 b2 r w [Hm Hw].
  assert (Hgen : forall t0 w0, multi t0 w0 -> value w0 -> forall c0 (l : label),
    t0 = tm_case c0 b1 b2 l ->
    (exists a k, value a /\ evaluates c0 (tm_inl a k) /\
        evaluates (tm_protect k.(indirect_reader) (open b1 a)) w0) \/
    (exists a k, value a /\ evaluates c0 (tm_inr a k) /\
        evaluates (tm_protect k.(indirect_reader) (open b2 a)) w0)).
  { intros t0 w0 Hmulti. induction Hmulti; intros Hval c0 l Hstart.
    - subst. inversion Hval.
    - rewrite Hstart in H. inversion H; subst.
      + left. exists v,kappa. split; [assumption|]. split.
        * split; [constructor|constructor; assumption].
        * split; [exact Hmulti|exact Hval].
      + right. exists v,kappa. split; [assumption|]. split.
        * split; [constructor|constructor; assumption].
        * split; [exact Hmulti|exact Hval].
      + destruct (IHHmulti Hval t' l eq_refl) as [HL|HR].
        * left. destruct HL as [a [k [Va [Ec Er]]]]. exists a,k. split; [exact Va|]. split.
          -- destruct Ec as [Mc Vc]. split; [econstructor; eassumption|exact Vc].
          -- exact Er.
        * right. destruct HR as [a [k [Va [Ec Er]]]]. exists a,k. split; [exact Va|]. split.
          -- destruct Ec as [Mc Vc]. split; [econstructor; eassumption|exact Vc].
          -- exact Er. }
  eapply Hgen; eauto.
Qed.

Lemma term_rel_pair : forall observer A B k t1 t2 s1 s2,
  term_rel observer A t1 t2 -> term_rel observer B s1 s2 ->
  term_rel observer (Ty_Prod A B k)
    (tm_pair t1 s1 k) (tm_pair t2 s2 k).
Proof.
  intros observer A B k t1 t2 s1 s2 HR1 HR2 v1 v2 E1 E2.
  destruct k as [rk ir]. destruct observer, ir; simpl; try exact I.
  - destruct (evaluates_pair_inv _ _ _ _ E1) as [a1 [b1 [-> [Ea1 Eb1]]]].
    destruct (evaluates_pair_inv _ _ _ _ E2) as [a2 [b2 [-> [Ea2 Eb2]]]].
    exists a1, a2, b1, b2, {| reader := rk; indirect_reader := Low |},
      {| reader := rk; indirect_reader := Low |}. repeat split; eauto.
  - destruct (evaluates_pair_inv _ _ _ _ E1) as [a1 [b1 [-> [Ea1 Eb1]]]].
    destruct (evaluates_pair_inv _ _ _ _ E2) as [a2 [b2 [-> [Ea2 Eb2]]]].
    exists a1, a2, b1, b2, {| reader := rk; indirect_reader := Low |},
      {| reader := rk; indirect_reader := Low |}. repeat split; eauto.
  - destruct (evaluates_pair_inv _ _ _ _ E1) as [a1 [b1 [-> [Ea1 Eb1]]]].
    destruct (evaluates_pair_inv _ _ _ _ E2) as [a2 [b2 [-> [Ea2 Eb2]]]].
    exists a1, a2, b1, b2, {| reader := rk; indirect_reader := High |},
      {| reader := rk; indirect_reader := High |}. repeat split; eauto.
Qed.

Lemma multi_inl_inv : forall t k v,
  multi (tm_inl t k) v -> value v ->
  exists a, v = tm_inl a k /\ evaluates t a.
Proof.
  intros t k v Hmulti Hv.
  assert (Hgen : forall t0 w, multi t0 w -> value w -> forall a q,
    t0 = tm_inl a q -> exists a', w = tm_inl a' q /\ evaluates a a').
  { intros t0 w Hm. induction Hm; intros Hval a q Hstart.
    - inversion Hval; subst; try discriminate. inversion H0; subst.
      exists a. split; [reflexivity|]. split; [constructor|assumption].
    - rewrite Hstart in H. inversion H; subst.
      destruct (IHHm Hval t' q eq_refl) as [w [E He]].
      exists w. split; [exact E|]. destruct He as [Hm1 Hv1].
      split; [econstructor; eassumption|exact Hv1]. }
  eapply Hgen; eauto.
Qed.

Lemma evaluates_inl_inv : forall t k v,
  evaluates (tm_inl t k) v -> exists a, v = tm_inl a k /\ evaluates t a.
Proof. intros t k v [Hm Hv]. eapply multi_inl_inv; eassumption. Qed.

Lemma multi_inr_inv : forall t k v,
  multi (tm_inr t k) v -> value v ->
  exists a, v = tm_inr a k /\ evaluates t a.
Proof.
  intros t k v Hmulti Hv.
  assert (Hgen : forall t0 w, multi t0 w -> value w -> forall a q,
    t0 = tm_inr a q -> exists a', w = tm_inr a' q /\ evaluates a a').
  { intros t0 w Hm. induction Hm; intros Hval a q Hstart.
    - inversion Hval; subst; try discriminate. inversion H0; subst.
      exists a. split; [reflexivity|]. split; [constructor|assumption].
    - rewrite Hstart in H. inversion H; subst.
      destruct (IHHm Hval t' q eq_refl) as [w [E He]].
      exists w. split; [exact E|]. destruct He as [Hm1 Hv1].
      split; [econstructor; eassumption|exact Hv1]. }
  eapply Hgen; eauto.
Qed.

Lemma evaluates_inr_inv : forall t k v,
  evaluates (tm_inr t k) v -> exists a, v = tm_inr a k /\ evaluates t a.
Proof. intros t k v [Hm Hv]. eapply multi_inr_inv; eassumption. Qed.

Lemma term_rel_inl : forall observer A B k t1 t2,
  term_rel observer A t1 t2 ->
  term_rel observer (Ty_Sum A B k) (tm_inl t1 k) (tm_inl t2 k).
Proof.
  intros observer A B k t1 t2 HR v1 v2 E1 E2.
  destruct k as [rk ir]. destruct observer, ir; simpl; try exact I.
  all: destruct (evaluates_inl_inv _ _ _ E1) as [a1 [-> Ea1]];
    destruct (evaluates_inl_inv _ _ _ E2) as [a2 [-> Ea2]];
    left; exists a1, a2; eexists; eexists; repeat split; eauto.
Qed.

Lemma term_rel_inr : forall observer A B k t1 t2,
  term_rel observer B t1 t2 ->
  term_rel observer (Ty_Sum A B k) (tm_inr t1 k) (tm_inr t2 k).
Proof.
  intros observer A B k t1 t2 HR v1 v2 E1 E2.
  destruct k as [rk ir]. destruct observer, ir; simpl; try exact I.
  all: destruct (evaluates_inr_inv _ _ _ E1) as [a1 [-> Ea1]];
    destruct (evaluates_inr_inv _ _ _ E2) as [a2 [-> Ea2]];
    right; exists a1, a2; eexists; eexists; repeat split; eauto.
Qed.

Lemma value_no_step : forall v t, value v -> ~ step v t.
Proof.
  intros v t Hv. revert t. induction Hv; intros t Hstep; inversion Hstep; subst; eauto.
  all: match goal with
       | Hs : ?a --> ?b, IH : forall t, ~ ?a --> t |- False => exact (IH b Hs)
       end.
Qed.

Lemma value_multi_eq : forall v w, value v -> multi v w -> w = v.
Proof.
  intros v w Hv Hm. induction Hm; auto.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma evaluates_unit_inv : forall k v,
  evaluates (tm_unit k) v -> v = tm_unit k.
Proof.
  intros k v [Hm Hv]. exact (value_multi_eq (tm_unit k) v (v_unit k) Hm).
Qed.

Lemma evaluates_nat_inv : forall n k v,
  evaluates (tm_nat n k) v -> v = tm_nat n k.
Proof.
  intros n k v [Hm Hv]. exact (value_multi_eq (tm_nat n k) v (v_nat n k) Hm).
Qed.

Lemma term_rel_unit : forall observer k,
  term_rel observer (Ty_Unit k) (tm_unit k) (tm_unit k).
Proof.
  intros observer k v1 v2 E1 E2.
  destruct k as [rk ir]. destruct observer, ir; simpl; try exact I.
  all: pose proof (evaluates_unit_inv _ _ E1) as Eq1;
    pose proof (evaluates_unit_inv _ _ E2) as Eq2; subst v1; subst v2;
    eexists; eexists; repeat split; reflexivity.
Qed.

Lemma term_rel_nat : forall observer n k,
  term_rel observer (Ty_Nat k) (tm_nat n k) (tm_nat n k).
Proof.
  intros observer n k v1 v2 E1 E2.
  destruct k as [rk ir]. destruct observer, ir; simpl; try exact I.
  all: pose proof (evaluates_nat_inv _ _ _ E1) as Eq1;
    pose proof (evaluates_nat_inv _ _ _ E2) as Eq2; subst v1; subst v2;
    eexists; eexists; eexists; eexists; repeat split; reflexivity.
Qed.

Lemma protect_value_value : forall v l, value v -> value (protect_value v l).
Proof.
  intros v l Hv. induction Hv; simpl; try constructor; eauto.
Qed.

Lemma multi_protect_inv : forall l t w,
  multi (tm_protect l t) w -> value w ->
  exists v, evaluates t v /\ w = protect_value v l.
Proof.
  intros l t w Hmulti Hw.
  assert (Hgen : forall t0 w0, multi t0 w0 -> value w0 -> forall l0 a,
    t0 = tm_protect l0 a -> exists v, evaluates a v /\ w0 = protect_value v l0).
  { intros t0 w0 Hm. induction Hm; intros Hval l0 a Hstart.
    - subst. inversion Hval.
    - rewrite Hstart in H. inversion H; subst.
      + exists a. split; [split; [apply multi_refl|assumption]|].
        exact (value_multi_eq (protect_value a l0) t3
          (protect_value_value a l0 H3) Hm).
      + destruct (IHHm Hval l0 t' eq_refl) as [v [Heq E]].
        exists v. split; [|exact E].
        destruct Heq as [Hm1 Hv1]. split; [econstructor; eassumption|exact Hv1]. }
  eapply Hgen; eauto.
Qed.

Lemma evaluates_protect_inv : forall l t w,
  evaluates (tm_protect l t) w ->
  exists v, evaluates t v /\ w = protect_value v l.
Proof. intros l t w [Hm Hw]. eapply multi_protect_inv; eassumption. Qed.

Lemma protect_value_low : forall v, protect_value v Low = v.
Proof.
  destruct v; simpl; try reflexivity;
    try (destruct s as [r i]; destruct r; destruct i; reflexivity).
Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof.
  destruct T; simpl; try reflexivity;
    destruct s as [r i]; destruct r; destruct i; reflexivity.
Qed.

Lemma ty_protect_high_ir : forall T,
  (security_of (ty_protect High T)).(indirect_reader) = High.
Proof.
  destruct T; simpl; destruct s as [r i]; destruct r; destruct i; reflexivity.
Qed.

Lemma term_rel_protect_low : forall T t1 t2,
  term_rel Low T t1 t2 ->
  term_rel Low (ty_protect Low T) (tm_protect Low t1) (tm_protect Low t2).
Proof.
  intros T t1 t2 HR v1 v2 E1 E2.
  destruct (evaluates_protect_inv _ _ _ E1) as [a1 [Ea1 ->]].
  destruct (evaluates_protect_inv _ _ _ E2) as [a2 [Ea2 ->]].
  rewrite protect_value_low, protect_value_low, ty_protect_low.
  eapply HR; eassumption.
Qed.

Lemma term_rel_protect_high : forall T t1 t2,
  term_rel Low T t1 t2 ->
  term_rel Low (ty_protect High T) (tm_protect High t1) (tm_protect High t2).
Proof.
  intros T t1 t2 _ v1 v2 _ _. eapply hidden_values_related.
  apply ty_protect_high_ir.
Qed.

Lemma multi_app_inv : forall t1 t2 r w,
  multi (tm_app t1 t2 r) w -> value w ->
  exists T body kappa a,
    value (tm_abs T body kappa) /\ value a /\
    evaluates t1 (tm_abs T body kappa) /\ evaluates t2 a /\
    evaluates (tm_protect kappa.(indirect_reader) (open body a)) w.
Proof.
  intros t1 t2 r w Hmulti Hw.
  assert (Hgen : forall t v, multi t v -> value v -> forall a b q,
    t = tm_app a b q ->
    exists T body kappa arg,
      value (tm_abs T body kappa) /\ value arg /\
      evaluates a (tm_abs T body kappa) /\ evaluates b arg /\
      evaluates (tm_protect kappa.(indirect_reader) (open body arg)) v).
  { intros t v Hm. induction Hm; intros Hv a b q Hstart.
    - subst. inversion Hv.
    - rewrite Hstart in H. inversion H; subst.
      + exists T, body, kappa, b. repeat split; eauto using multi_refl.
      + destruct (IHHm Hv t1' b q eq_refl)
          as [T [body [kap [arg [Habs [Harg [Hea [Heb Her]]]]]]]].
        exists T, body, kap, arg. split; [exact Habs|]. split; [exact Harg|].
        split.
        * destruct Hea as [Hm1 Hva].
          split; [econstructor; eassumption|exact Hva].
        * split; [exact Heb|exact Her].
      + destruct (IHHm Hv a t2' q eq_refl)
          as [T [body [kap [arg [Habs [Harg [Hea [Heb Her]]]]]]]].
        exists T, body, kap, arg. split; [exact Habs|]. split; [exact Harg|].
        split.
        * exact Hea.
        * split.
          -- destruct Heb as [Hm2 Hvb]. split; [econstructor; eassumption|exact Hvb].
          -- exact Her.
      }
  eapply Hgen; eauto.
Qed.

Lemma evaluates_app_inv : forall t1 t2 r w,
  evaluates (tm_app t1 t2 r) w ->
  exists T body kappa a,
    value (tm_abs T body kappa) /\ value a /\
    evaluates t1 (tm_abs T body kappa) /\ evaluates t2 a /\
    evaluates (tm_protect kappa.(indirect_reader) (open body a)) w.
Proof. intros t1 t2 r w [Hm Hv]. eapply multi_app_inv; eassumption. Qed.

Lemma evaluates_app_value_iff : forall T body kappa a r w,
  value (tm_abs T body kappa) -> value a -> flows_to kappa.(reader) r ->
  (evaluates (tm_app (tm_abs T body kappa) a r) w <->
   evaluates (tm_protect kappa.(indirect_reader) (open body a)) w).
Proof.
  intros T body kappa a r w Habs Harg Hflow. split.
  - intro He.
    destruct (evaluates_app_inv _ _ _ _ He)
      as [T' [body' [k' [a' [Habs' [Harg' [Hef [Hea Her]]]]]]]].
    pose proof (value_multi_eq _ _ Habs (proj1 Hef)) as Eabs.
    pose proof (value_multi_eq _ _ Harg (proj1 Hea)) as Earg.
    inversion Eabs; subst. exact Her.
  - intros [Hm Hv]. split.
    + econstructor; [eapply ST_AppAbs; eauto|exact Hm].
    + exact Hv.
Qed.

Lemma multi_succ_inv : forall t r w,
  multi (tm_succ t r) w -> value w ->
  exists n k, evaluates t (tm_nat n k) /\
    evaluates (tm_protect k.(indirect_reader) (tm_nat (S n) public)) w.
Proof.
  intros t r w Hmulti Hw.
  assert (Hgen : forall t0 v, multi t0 v -> value v -> forall u q,
    t0 = tm_succ u q ->
    exists n k, evaluates u (tm_nat n k) /\
      evaluates (tm_protect k.(indirect_reader) (tm_nat (S n) public)) v).
  { intros t0 v Hm. induction Hm; intros Hval u q Hstart.
    - subst. inversion Hval.
    - rewrite Hstart in H. inversion H; subst.
      + destruct (IHHm Hval t' q eq_refl) as [n [k [He Hr]]].
        exists n, k. split.
        * destruct He as [Hm1 Hv1]. split; [econstructor; eassumption|exact Hv1].
        * exact Hr.
      + exists n, k. split.
        * split; [constructor|constructor].
        * exact (conj Hm Hval). }
  eapply Hgen; eauto.
Qed.

Lemma evaluates_succ_inv : forall t r w,
  evaluates (tm_succ t r) w ->
  exists n k, evaluates t (tm_nat n k) /\
    evaluates (tm_protect k.(indirect_reader) (tm_nat (S n) public)) w.
Proof. intros t r w [Hm Hv]. eapply multi_succ_inv; eassumption. Qed.

Lemma term_rel_succ : forall k r t1 t2,
  term_rel Low (Ty_Nat k) t1 t2 ->
  term_rel Low (ty_protect k.(indirect_reader) (Ty_Nat public))
    (tm_succ t1 r) (tm_succ t2 r).
Proof.
  intros [rk ik] r t1 t2 HR v1 v2 E1 E2.
  destruct (evaluates_succ_inv _ _ _ E1) as [n1 [k1 [En1 Er1]]].
  destruct (evaluates_succ_inv _ _ _ E2) as [n2 [k2 [En2 Er2]]].
  destruct ik.
  - pose proof (HR _ _ En1 En2) as Hnr.
    simpl in Hnr. destruct Hnr as [m1 [m2 [ka [kb [Ena [Enb Hmn]]]]]].
    destruct Hmn as [Hmn [Hflow1 Hflow2]].
    inversion Ena; inversion Enb; subst.
    destruct (evaluates_protect_inv _ _ _ Er1) as [w1 [Ew1 ->]].
    destruct (evaluates_protect_inv _ _ _ Er2) as [w2 [Ew2 ->]].
    pose proof (evaluates_nat_inv _ _ _ Ew1) as ->.
    pose proof (evaluates_nat_inv _ _ _ Ew2) as ->.
    assert (Hka : indirect_reader ka = Low) by (eapply flows_low_eq; exact Hflow1).
    assert (Hkb : indirect_reader kb = Low) by (eapply flows_low_eq; exact Hflow2).
    simpl.
    exists (S m2), (S m2),
      (protect_security public (indirect_reader ka)),
      (protect_security public (indirect_reader kb)); repeat split; try reflexivity;
      unfold security_bound; simpl; rewrite Hka || rewrite Hkb; reflexivity.
  - eapply hidden_values_related. simpl. reflexivity.
Qed.

Lemma term_rel_app : forall observer A B k r f1 f2 a1 a2,
  term_rel observer (Ty_Arrow A B k) f1 f2 ->
  term_rel observer A a1 a2 ->
  term_rel observer (ty_protect k.(indirect_reader) B)
    (tm_app f1 a1 r) (tm_app f2 a2 r).
Proof.
  intros observer A B k r f1 f2 a1 a2 HRf HRa v1 v2 E1 E2.
  destruct k as [kr ki].
  destruct (evaluates_app_inv _ _ _ _ E1)
    as [Tf [bf [kf [avf [Vf [Vavf [Ef [Eavf Erf]]]]]]]].
  destruct (evaluates_app_inv _ _ _ _ E2)
    as [Tg [bg [kg [avg [Vg [Vavg [Eg [Eavg Erg]]]]]]]].
  pose proof (HRf _ _ Ef Eg) as Hfr.
  pose proof (HRa _ _ Eavf Eavg) as Har.
  destruct observer, ki; simpl in *.
  - destruct Hfr as [T1 [T2 [body1 [body2 [k1 [k2 [F1 [F2 Hext]]]]]]]].
    inversion F1; subst. inversion F2; subst.
    pose proof (proj2 (evaluates_app_value_iff _ _ _ _ _ _ Vf Vavf (flows_refl (reader k1))) Erf) as Eapp1.
    pose proof (proj2 (evaluates_app_value_iff _ _ _ _ _ _ Vg Vavg (flows_refl (reader k2))) Erg) as Eapp2.
    eapply value_rel_protect.
    eapply Hext with (a1 := avf) (a2 := avg); eauto.
  - eapply hidden_values_related.
    destruct B; simpl; destruct s as [r0 i0]; destruct i0; reflexivity.
  - destruct Hfr as [T1 [T2 [body1 [body2 [k1 [k2 [F1 [F2 Hext]]]]]]]].
    inversion F1; subst. inversion F2; subst.
    pose proof (proj2 (evaluates_app_value_iff _ _ _ _ _ _ Vf Vavf (flows_refl (reader k1))) Erf) as Eapp1.
    pose proof (proj2 (evaluates_app_value_iff _ _ _ _ _ _ Vg Vavg (flows_refl (reader k2))) Erg) as Eapp2.
    eapply value_rel_protect.
    eapply Hext with (a1 := avf) (a2 := avg); eauto.
  - destruct Hfr as [T1 [T2 [body1 [body2 [k1 [k2 [F1 [F2 Hext]]]]]]]].
    inversion F1; subst. inversion F2; subst.
    pose proof (proj2 (evaluates_app_value_iff _ _ _ _ _ _ Vf Vavf (flows_refl (reader k1))) Erf) as Eapp1.
    pose proof (proj2 (evaluates_app_value_iff _ _ _ _ _ _ Vg Vavg (flows_refl (reader k2))) Erg) as Eapp2.
    eapply value_rel_protect.
    eapply Hext with (a1 := avf) (a2 := avg); eauto.
Qed.

Fixpoint subst_sim (Gamma : context) (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => match lookup_context x Gamma with Some _ => rho x | None => tm_fvar x end
  | tm_unit k => tm_unit k
  | tm_abs T b k => tm_abs T (subst_sim Gamma rho b) k
  | tm_app t1 t2 r => tm_app (subst_sim Gamma rho t1) (subst_sim Gamma rho t2) r
  | tm_pair t1 t2 k => tm_pair (subst_sim Gamma rho t1) (subst_sim Gamma rho t2) k
  | tm_fst t r => tm_fst (subst_sim Gamma rho t) r
  | tm_snd t r => tm_snd (subst_sim Gamma rho t) r
  | tm_inl t k => tm_inl (subst_sim Gamma rho t) k
  | tm_inr t k => tm_inr (subst_sim Gamma rho t) k
  | tm_case t b1 b2 r => tm_case (subst_sim Gamma rho t) (subst_sim Gamma rho b1) (subst_sim Gamma rho b2) r
  | tm_protect l t => tm_protect l (subst_sim Gamma rho t)
  | tm_nat n k => tm_nat n k
  | tm_succ t r => tm_succ (subst_sim Gamma rho t) r
  | tm_natrec n b s r => tm_natrec (subst_sim Gamma rho n) (subst_sim Gamma rho b) (subst_sim Gamma rho s) r
  | tm_if c y n r => tm_if (subst_sim Gamma rho c) (subst_sim Gamma rho y) (subst_sim Gamma rho n) r
  end.

Definition env_update (rho : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else rho y.

Definition env_rel (observer : label) (Gamma : context)
    (rho1 rho2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    term_rel observer T (rho1 x) (rho2 x).

Definition lc_environment (rho : atom -> tm) : Prop :=
  forall x, locally_closed (rho x).

Lemma lc_environment_update : forall rho x a,
  lc_environment rho -> locally_closed a ->
  lc_environment (env_update rho x a).
Proof.
  intros rho x a Henv Ha y. unfold env_update. destruct (Nat.eqb y x); auto.
Qed.

Fixpoint environment_fv (Gamma : context) (rho : atom -> tm) : list atom :=
  match Gamma with
  | [] => []
  | (x, _) :: Gamma' => fv (rho x) ++ environment_fv Gamma' rho
  end.

Lemma exists_fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (fold_right Nat.max 0 L)).
  intro H.
  assert (Hbound : forall xs x, In x xs -> x <= fold_right Nat.max 0 xs).
  { induction xs as [|a xs IH]; intros x Hin; simpl in *; [contradiction|].
    destruct Hin as [->|Hin].
    - apply Nat.le_max_l.
    - eapply Nat.le_trans; [eapply IH; exact Hin|apply Nat.le_max_r]. }
  specialize (Hbound L (S (fold_right Nat.max 0 L)) H). lia.
Qed.

Lemma lookup_environment_fv : forall Gamma rho x T z,
  lookup_context x Gamma = Some T -> In z (fv (rho x)) ->
  In z (environment_fv Gamma rho).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros rho x T z Hlookup Hz; simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst x. apply in_app_iff. left. exact Hz.
  - apply in_app_iff. right. eapply IH; eauto.
Qed.

Lemma exists_fresh_env_binder : forall L Gamma body rho1 rho2,
  exists y, ~ In y L /\ ~ In y (context_atoms Gamma) /\ ~ In y (fv body) /\
    (forall x T, lookup_context x Gamma = Some T -> ~ In y (fv (rho1 x))) /\
    (forall x T, lookup_context x Gamma = Some T -> ~ In y (fv (rho2 x))) /\
    ~ In y (fv (subst_sim Gamma rho1 body)) /\
    ~ In y (fv (subst_sim Gamma rho2 body)).
Proof.
  intros L Gamma body rho1 rho2.
  set (All := L ++ context_atoms Gamma ++ fv body ++ environment_fv Gamma rho1 ++
    environment_fv Gamma rho2 ++ fv (subst_sim Gamma rho1 body) ++ fv (subst_sim Gamma rho2 body)).
  destruct (exists_fresh_atom All) as [y Hy]. exists y. repeat split.
  - intro H. apply Hy. unfold All. apply in_app_iff. left. exact H.
  - intro H. apply Hy. unfold All. apply in_app_iff. right. apply in_app_iff. left. exact H.
  - intro H. apply Hy. unfold All. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. exact H.
  - intros x T Hlook H. apply Hy. unfold All. apply in_app_iff. right. apply in_app_iff. right.
    apply in_app_iff. right. apply in_app_iff. left. eapply lookup_environment_fv; eauto.
  - intros x T Hlook H. apply Hy. unfold All. apply in_app_iff. right. apply in_app_iff. right.
    apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
    eapply lookup_environment_fv; eauto.
  - intro H. apply Hy. unfold All. apply in_app_iff. right. apply in_app_iff. right.
    apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
    apply in_app_iff. left. exact H.
  - intro H. apply Hy. unfold All. apply in_app_iff. right. apply in_app_iff. right.
    apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
    apply in_app_iff. right. exact H.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv; unfold locally_closed in *; simpl in *; auto.
Qed.

Lemma subst_sim_single : forall t x T rho,
  subst_sim (update empty x T) rho t = subst x (rho x) t.
Proof.
  induction t; intros x T rho; simpl; try reflexivity.
  - rewrite Nat.eqb_sym. destruct (Nat.eqb x a) eqn:E; simpl.
    + apply Nat.eqb_eq in E. subst. reflexivity.
    + reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2]; eauto.
  - f_equal; [apply IHt1 | apply IHt2]; eauto.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; eauto.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; eauto.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; eauto.
Qed.

Lemma subst_sim_plug : forall C x T rho,
  ~ In x (context_fv C) ->
  subst_sim (update empty x T) rho (plug C (tm_fvar x)) = plug C (rho x).
Proof.
  intros C x T rho Hfresh. rewrite subst_sim_single.
  apply subst_plug_fresh_context. exact Hfresh.
Qed.

Lemma context_atoms_lookup_none : forall Gamma x,
  ~ In x (context_atoms Gamma) -> lookup_context x Gamma = None.
Proof.
  induction Gamma as [|[y T] Gamma IH]; intros x H; simpl; auto.
  assert (Hxy : x <> y) by (intro E; subst; apply H; simpl; auto).
  destruct (Nat.eqb x y) eqn:E; [apply Nat.eqb_eq in E; contradiction|].
  apply IH. intro Hin. apply H. simpl; auto.
Qed.

Lemma subst_sim_open_rec : forall Gamma rho y A a body k,
  ~ In y (context_atoms Gamma) ->
  (forall x T, lookup_context x Gamma = Some T -> ~ In y (fv (rho x))) ->
  locally_closed a ->
  subst_sim (update Gamma y A) (env_update rho y a)
      (open_rec k (tm_fvar y) body) =
    subst y a (subst_sim Gamma rho (open_rec k (tm_fvar y) body)).
Proof.
  induction body; intros k; simpl; intros Hfresh Hrho Ha; try reflexivity.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + rewrite (context_atoms_lookup_none Gamma y Hfresh). simpl.
      unfold env_update. rewrite Nat.eqb_refl. simpl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb a0 y) eqn:E.
    + apply Nat.eqb_eq in E; subst a0. simpl.
      rewrite (context_atoms_lookup_none Gamma y Hfresh). simpl.
      unfold env_update. rewrite Nat.eqb_refl. simpl. reflexivity.
    + assert (Nat.eqb y a0 = false) as E' by (apply Nat.eqb_neq; apply Nat.eqb_neq in E; congruence).
      simpl.
      destruct (lookup_context a0 Gamma) as [T|] eqn:L; simpl.
      * unfold env_update. rewrite E. rewrite subst_fresh.
        -- reflexivity.
        -- eapply (Hrho a0 T). exact L.
      * simpl. rewrite E'. reflexivity.
  - f_equal. eapply IHbody; eauto.
  - f_equal; [eapply IHbody1 | eapply IHbody2]; eauto.
  - f_equal; [eapply IHbody1 | eapply IHbody2]; eauto.
  - f_equal. eapply IHbody; eauto.
  - f_equal. eapply IHbody; eauto.
  - f_equal. eapply IHbody; eauto.
  - f_equal. eapply IHbody; eauto.
  - f_equal; [eapply IHbody1 | eapply IHbody2 | eapply IHbody3]; eauto.
  - f_equal. eapply IHbody; eauto.
  - f_equal. eapply IHbody; eauto.
  - f_equal; [eapply IHbody1 | eapply IHbody2 | eapply IHbody3]; eauto.
  - f_equal; [eapply IHbody1 | eapply IHbody2 | eapply IHbody3]; eauto.
Qed.

Lemma subst_open_same : forall body y a,
  locally_closed a -> ~ In y (fv body) ->
  subst y a (open body (tm_fvar y)) = open body a.
Proof.
  intros body y a Hlc Hfresh. unfold open.
  rewrite subst_open_rec by exact Hlc. simpl. rewrite Nat.eqb_refl.
  rewrite subst_fresh by exact Hfresh. reflexivity.
Qed.


Lemma value_rel_subtype : forall T U observer v1 v2,
  subtype T U -> value_rel observer T v1 v2 -> value_rel observer U v1 v2.
Proof.
  intros T U observer v1 v2 Hsub. revert observer v1 v2.
  induction Hsub; intros observer v1 v2 Hrel.
  - match goal with Hle : security_le _ _ |- _ => destruct Hle as [_ Hflow] end.
    destruct observer; destruct kappa1 as [r1 i1]; destruct kappa2 as [r2 i2];
      destruct i1, i2; cbn [security_of value_rel flows_to indirect_reader] in *;
      try contradiction; try exact I.
    all: destruct Hrel as [q1 [q2 [E1 E2]]]; exists q1,q2; split; assumption.
  - match goal with Hle : security_le _ _ |- _ => destruct Hle as [_ Hflow] end.
    destruct observer; destruct kappa1 as [r1 i1]; destruct kappa2 as [r2 i2];
      destruct i1, i2; cbn [security_of value_rel flows_to indirect_reader] in *;
      try contradiction; try exact I.
    all: destruct Hrel as [[a1 [a2 [q1 [q2 [E1 [E2 [Ha [Hb1 Hb2]]]]]]]]|
                            [b1 [b2 [q1 [q2 [E1 [E2 [Hb [Hb1 Hb2]]]]]]]]].
    all: first [left; exists a1,a2,q1,q2; repeat split; eauto using flows_trans
              | right; exists b1,b2,q1,q2; repeat split; eauto using flows_trans].
  - match goal with Hle : security_le _ _ |- _ => destruct Hle as [_ Hflow] end.
    destruct observer; destruct kappa1 as [r1 i1]; destruct kappa2 as [r2 i2];
      destruct i1, i2; cbn [security_of value_rel flows_to indirect_reader] in *;
      try contradiction; try exact I.
    all: destruct Hrel as [a1 [a2 [b1 [b2 [q1 [q2 [E1 [E2 [Hb1 [Hb2 [Ha Hb]]]]]]]]]]].
    all: exists a1,a2,b1,b2,q1,q2; repeat split; eauto using flows_trans.
  - match goal with Hle : security_le _ _ |- _ => destruct Hle as [_ Hflow] end.
    destruct observer; destruct kappa1 as [r1 i1]; destruct kappa2 as [r2 i2];
      destruct i1, i2; cbn [security_of value_rel flows_to indirect_reader] in *;
      try contradiction; try exact I.
    all: destruct Hrel as [A1 [A2 [b1 [b2 [q1 [q2 [-> [-> [Hb1 [Hb2 Hext]]]]]]]]]].
    all: exists A1,A2,b1,b2,q1,q2; repeat split; try reflexivity; eauto using flows_trans.
    all: intros a1 a2 w1 w2 Ha Va1 Va2 Ea1 Ea2.
    all: pose proof (IHHsub1 _ a1 a2 Ha) as Harg.
    all: pose proof (Hext a1 a2 w1 w2 Harg Va1 Va2 Ea1 Ea2) as Hout.
    all: eapply IHHsub2; eauto.
  - eapply IHHsub2. eapply IHHsub1. exact Hrel.
  - match goal with Hle : security_le _ _ |- _ => destruct Hle as [_ Hflow] end.
    destruct observer; destruct k1 as [r1 i1]; destruct k2 as [r2 i2];
      destruct i1, i2; cbn [security_of value_rel flows_to indirect_reader] in *;
      try contradiction; try exact I.
    all: destruct Hrel as [n1 [n2 [q1 [q2 [E1 [E2 [E3 [B1 B2]]]]]]]].
    all: exists n1,n2,q1,q2; repeat split; try congruence; eauto using flows_trans.
Qed.

Lemma lc_at_open_fvar_inv : forall k body x,
  lc_at k (open_rec k (tm_fvar x) body) -> lc_at (S k) body.
Proof.
  intros k body. revert k. induction body; intros k x H; simpl in *; try assumption; try exact I.
  - destruct (Nat.eqb k n) eqn:E; simpl in *.
    + apply Nat.eqb_eq in E. subst. lia.
    + lia.
  - eapply (IHbody (S k) x). exact H.
  - destruct H as [H1 H2]. split; [eapply IHbody1|eapply IHbody2]; eassumption.
  - destruct H as [H1 H2]. split; [eapply IHbody1|eapply IHbody2]; eassumption.
  - eapply IHbody; eassumption.
  - eapply IHbody; eassumption.
  - eapply IHbody; eassumption.
  - eapply IHbody; eassumption.
  - destruct H as [H0 [H1 H2]]. split.
    + eapply (IHbody1 k x); exact H0.
    + split.
      * eapply (IHbody2 (S k) x); exact H1.
      * eapply (IHbody3 (S k) x); exact H2.
  - eapply IHbody; eassumption.
  - eapply IHbody; eassumption.
  - destruct H as [H1 [H2 H3]]. repeat split.
    + eapply (IHbody1 k x); exact H1.
    + eapply (IHbody2 k x); exact H2.
    + eapply (IHbody3 k x); exact H3.
  - destruct H as [H1 [H2 H3]]. repeat split.
    + eapply (IHbody1 k x); exact H1.
    + eapply (IHbody2 k x); exact H2.
    + eapply (IHbody3 k x); exact H3.
Qed.

Lemma lc_from_open_all : forall L body,
  (forall x, ~ In x L -> locally_closed (open body (tm_fvar x))) ->
  lc_at 1 body.
Proof.
  intros L body H. destruct (exists_fresh_atom L) as [x Hx].
  specialize (H x Hx). unfold locally_closed, open in H.
  eapply lc_at_open_fvar_inv with (x := x); exact H.
Qed.

Lemma has_type_locally_closed : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T HT. induction HT; unfold locally_closed in *; simpl in *;
    eauto using lc_from_open_all.
Qed.

Lemma lc_at_subst_sim : forall t Gamma rho k,
  lc_at k t -> (forall x, locally_closed (rho x)) ->
  lc_at k (subst_sim Gamma rho t).
Proof.
  induction t; intros Gamma rho k Hlc Hrho; simpl in *; try exact Hlc; try exact I.
  - destruct (lookup_context a Gamma) as [T|]; simpl.
    + eapply lc_at_mono with (j := 0); [lia|exact (Hrho a)].
    + exact I.
  - eapply IHt; eauto.
  - destruct Hlc as [H1 H2]. split; [eapply IHt1|eapply IHt2]; eauto.
  - destruct Hlc as [H1 H2]. split; [eapply IHt1|eapply IHt2]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct Hlc as [H0 [H1 H2]]. repeat split; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct Hlc as [H1 [H2 H3]]. repeat split; eauto.
  - destruct Hlc as [H1 [H2 H3]]. repeat split; eauto.
Qed.

Lemma term_rel_value : forall observer T a1 a2,
  value a1 -> value a2 -> value_rel observer T a1 a2 ->
  term_rel observer T a1 a2.
Proof.
  intros observer T a1 a2 Va1 Va2 Hrel v1 v2 [M1 V1] [M2 V2].
  pose proof (value_multi_eq a1 v1 Va1 M1) as E1.
  pose proof (value_multi_eq a2 v2 Va2 M2) as E2.
  subst v1. subst v2. exact Hrel.
Qed.

Lemma env_rel_extend : forall observer Gamma rho1 rho2 y A a1 a2,
  ~ In y (context_atoms Gamma) ->
  env_rel observer Gamma rho1 rho2 ->
  term_rel observer A a1 a2 ->
  env_rel observer (update Gamma y A)
    (env_update rho1 y a1) (env_update rho2 y a2).
Proof.
  intros observer Gamma rho1 rho2 y A a1 a2 Hfresh Henv Harg x T Hlookup.
  simpl in Hlookup. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst x. inversion Hlookup; subst T.
    unfold env_update. rewrite Nat.eqb_refl. exact Harg.
  - assert (Nat.eqb y x = false) as E' by
      (apply Nat.eqb_neq; apply Nat.eqb_neq in E; congruence).
    unfold env_update. rewrite E. eapply Henv. exact Hlookup.
Qed.

Lemma lookup_in_context_atoms : forall Gamma x T,
  lookup_context x Gamma = Some T -> In x (context_atoms Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T H; simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst. simpl. auto.
  - right. eapply IH; eauto.
Qed.

Lemma fv_open_rec_preserve : forall t k u x,
  In x (fv t) -> In x (fv (open_rec k u t)).
Proof.
  induction t; intros k u x H; simpl in *; try contradiction.
  - exact H.
  - eapply IHt; eauto.
  - apply in_app_iff in H as [H|H]; apply in_app_iff; [left; eapply IHt1|right; eapply IHt2]; eauto.
  - apply in_app_iff in H as [H|H]; apply in_app_iff; [left; eapply IHt1|right; eapply IHt2]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - apply in_app_iff in H as [H|H].
    + apply in_app_iff. left. eapply IHt1; eauto.
    + apply in_app_iff in H as [H|H].
      * apply in_app_iff. right. apply in_app_iff. left. eapply IHt2; eauto.
      * apply in_app_iff. right. apply in_app_iff. right. eapply IHt3; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - apply in_app_iff in H as [H|H].
    + apply in_app_iff. left. eapply IHt1; eauto.
    + apply in_app_iff. right. apply in_app_iff in H as [H|H].
      * apply in_app_iff. left. eapply IHt2; eauto.
      * apply in_app_iff. right. eapply IHt3; eauto.
  - apply in_app_iff in H as [H|H].
    + apply in_app_iff. left. eapply IHt1; eauto.
    + apply in_app_iff. right. apply in_app_iff in H as [H|H].
      * apply in_app_iff. left. eapply IHt2; eauto.
      * apply in_app_iff. right. eapply IHt3; eauto.
Qed.

Lemma typing_fv_bound : forall Gamma t T,
  has_type Gamma t T -> forall x, In x (fv t) -> In x (context_atoms Gamma).
Proof.
  intros Gamma t T HT. induction HT; intros z Hin; simpl in *.
  - destruct Hin as [->|[]]. eapply lookup_in_context_atoms; eauto.
  - contradiction.
  - destruct (exists_fresh_atom (L ++ context_atoms Gamma ++ fv body)) as [y Hy].
    assert (HyL : ~ In y L) by (intro Hfresh'; apply Hy; repeat rewrite in_app_iff; auto).
    assert (HyG : ~ In y (context_atoms Gamma)) by (intro Hfresh'; apply Hy; repeat rewrite in_app_iff; auto).
    assert (HyB : ~ In y (fv body)) by (intro Hfresh'; apply Hy; repeat rewrite in_app_iff; auto).
    specialize (H2 y HyL z (fv_open_rec_preserve body 0 (tm_fvar y) z Hin)).
    simpl in H2. destruct H2 as [E|HinG].
    + subst z. contradiction.
    + exact HinG.
  - apply in_app_iff in Hin as [Hleft|Hright].
    + eapply IHHT1; eauto.
    + eapply IHHT2; eauto.
  - apply in_app_iff in Hin as [Hleft|Hright].
    + eapply IHHT1; eauto.
    + eapply IHHT2; eauto.
  - eapply IHHT; eauto.
  - eapply IHHT; eauto.
  - eapply IHHT; eauto.
  - eapply IHHT; eauto.
  - apply in_app_iff in Hin as [Hleft|Hright].
    + eapply IHHT; eauto.
    + apply in_app_iff in Hright as [Hmid|Hright].
      * destruct (exists_fresh_atom (L ++ context_atoms Gamma ++ fv body1)) as [y Hy].
        assert (HyL : ~ In y L) by (intro Hfresh'; apply Hy; repeat rewrite in_app_iff; auto).
        assert (HyG : ~ In y (context_atoms Gamma)) by (intro Hfresh'; apply Hy; repeat rewrite in_app_iff; auto).
        assert (HyB : ~ In y (fv body1)) by (intro Hfresh'; apply Hy; repeat rewrite in_app_iff; auto).
        specialize (H1 y HyL z (fv_open_rec_preserve body1 0 (tm_fvar y) z Hmid)).
        simpl in H1. destruct H1 as [E|HinG]; [subst z; contradiction|exact HinG].
      * destruct (exists_fresh_atom (L ++ context_atoms Gamma ++ fv body2)) as [y Hy].
        assert (HyL : ~ In y L) by (intro Hfresh'; apply Hy; repeat rewrite in_app_iff; auto).
        assert (HyG : ~ In y (context_atoms Gamma)) by (intro Hfresh'; apply Hy; repeat rewrite in_app_iff; auto).
        assert (HyB : ~ In y (fv body2)) by (intro Hfresh'; apply Hy; repeat rewrite in_app_iff; auto).
        specialize (H3 y HyL z (fv_open_rec_preserve body2 0 (tm_fvar y) z Hright)).
        simpl in H3. destruct H3 as [E|HinG]; [subst z; contradiction|exact HinG].
  - eapply IHHT; eauto.
  - eapply IHHT; eauto.
  - contradiction.
  - eapply IHHT; eauto.
  - apply in_app_iff in Hin as [Hleft|Hright].
    + eapply IHHT1; eauto.
    + apply in_app_iff in Hright as [Hmid|Hright].
      * eapply IHHT2; eauto.
      * eapply IHHT3; eauto.
  - apply in_app_iff in Hin as [Hleft|Hright].
    + eapply IHHT1; eauto.
    + apply in_app_iff in Hright as [Hmid|Hright].
      * eapply IHHT2; eauto.
      * eapply IHHT3; eauto.
Qed.

Lemma context_atoms_lookup_some : forall Gamma x,
  In x (context_atoms Gamma) -> exists T, lookup_context x Gamma = Some T.
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x H; simpl in *; [contradiction|].
  destruct H as [->|H].
  - exists U. simpl. rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + exists U. simpl. reflexivity.
    + destruct (IH x H) as [T HT]. exists T. simpl. exact HT.
Qed.

Lemma subst_sim_fv_empty : forall t Gamma rho,
  (forall x, In x (fv t) -> exists T, lookup_context x Gamma = Some T) ->
  closed_environment rho -> fv (subst_sim Gamma rho t) = [].
Proof.
  induction t; intros Gamma rho Hbound Hclosed; simpl in *; try reflexivity.
  - destruct (Hbound a (or_introl eq_refl)) as [T HT]. rewrite HT.
    exact (proj2 (Hclosed a)).
  - eapply IHt; eauto.
  - assert (R1 : fv (subst_sim Gamma rho t1) = []).
    { eapply IHt1; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. apply in_app_iff; auto. }
    assert (R2 : fv (subst_sim Gamma rho t2) = []).
    { eapply IHt2; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. apply in_app_iff; auto. }
    rewrite R1,R2. reflexivity.
  - assert (R1 : fv (subst_sim Gamma rho t1) = []).
    { eapply IHt1; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. apply in_app_iff; auto. }
    assert (R2 : fv (subst_sim Gamma rho t2) = []).
    { eapply IHt2; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. apply in_app_iff; auto. }
    rewrite R1,R2. reflexivity.
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - assert (R1 : fv (subst_sim Gamma rho t1) = []).
    { eapply IHt1; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. repeat rewrite in_app_iff; auto. }
    assert (R2 : fv (subst_sim Gamma rho t2) = []).
    { eapply IHt2; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. repeat rewrite in_app_iff; auto. }
    assert (R3 : fv (subst_sim Gamma rho t3) = []).
    { eapply IHt3; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. repeat rewrite in_app_iff; auto. }
    rewrite R1,R2,R3. reflexivity.
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - assert (R1 : fv (subst_sim Gamma rho t1) = []).
    { eapply IHt1; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. repeat rewrite in_app_iff; auto. }
    assert (R2 : fv (subst_sim Gamma rho t2) = []).
    { eapply IHt2; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. repeat rewrite in_app_iff; auto. }
    assert (R3 : fv (subst_sim Gamma rho t3) = []).
    { eapply IHt3; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. repeat rewrite in_app_iff; auto. }
    rewrite R1,R2,R3. reflexivity.
  - assert (R1 : fv (subst_sim Gamma rho t1) = []).
    { eapply IHt1; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. repeat rewrite in_app_iff; auto. }
    assert (R2 : fv (subst_sim Gamma rho t2) = []).
    { eapply IHt2; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. repeat rewrite in_app_iff; auto. }
    assert (R3 : fv (subst_sim Gamma rho t3) = []).
    { eapply IHt3; [|exact Hclosed]. intros x Hx. apply Hbound. simpl. repeat rewrite in_app_iff; auto. }
    rewrite R1,R2,R3. reflexivity.
Qed.

Lemma typed_subst_closed : forall Gamma t T rho,
  has_type Gamma t T -> closed_environment rho ->
  closed (subst_sim Gamma rho t).
Proof.
  intros Gamma t T rho HT Henv. split.
  - eapply lc_at_subst_sim.
    + exact (has_type_locally_closed Gamma t T HT).
    + intro x. exact (proj1 (Henv x)).
  - eapply subst_sim_fv_empty.
    + intros x Hx. apply context_atoms_lookup_some.
      eapply typing_fv_bound; eauto.
    + exact Henv.
Qed.

Lemma fv_open_rec_subset : forall t k u x,
  In x (fv (open_rec k u t)) -> In x (fv t ++ fv u).
Proof.
  induction t; intros k u x H; simpl in *.
  - destruct (Nat.eqb k n); simpl in *; [assumption|contradiction].
  - simpl in H. simpl. destruct H as [H|[]]. subst x. left. reflexivity.
  - contradiction.
  - eapply IHt; eauto.
  - apply in_app_iff in H as [H|H].
    + pose proof (IHt1 k u x H) as HH. apply in_app_iff in HH as [HH|HH].
      * apply in_app_iff. left. apply in_app_iff. left. exact HH.
      * apply in_app_iff. right. exact HH.
    + pose proof (IHt2 k u x H) as HH. apply in_app_iff in HH as [HH|HH].
      * apply in_app_iff. left. apply in_app_iff. right. exact HH.
      * apply in_app_iff. right. exact HH.
  - apply in_app_iff in H as [H|H].
    + pose proof (IHt1 k u x H) as HH. apply in_app_iff in HH as [HH|HH].
      * apply in_app_iff. left. apply in_app_iff. left. exact HH.
      * apply in_app_iff. right. exact HH.
    + pose proof (IHt2 k u x H) as HH. apply in_app_iff in HH as [HH|HH].
      * apply in_app_iff. left. apply in_app_iff. right. exact HH.
      * apply in_app_iff. right. exact HH.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - apply in_app_iff in H as [H|H].
    + pose proof (IHt1 k u x H) as HH. apply in_app_iff in HH as [HH|HH].
      * apply in_app_iff. left. apply in_app_iff. left. exact HH.
      * apply in_app_iff. right. exact HH.
    + apply in_app_iff in H as [H|H].
      * pose proof (IHt2 (S k) u x H) as HH. apply in_app_iff in HH as [HH|HH].
        -- apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. left. exact HH.
        -- apply in_app_iff. right. exact HH.
      * pose proof (IHt3 (S k) u x H) as HH. apply in_app_iff in HH as [HH|HH].
        -- apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. exact HH.
        -- apply in_app_iff. right. exact HH.
  - eapply IHt; eauto.
  - contradiction.
  - eapply IHt; eauto.
  - apply in_app_iff in H as [H|H].
    + pose proof (IHt1 k u x H) as HH. repeat rewrite in_app_iff in *. tauto.
    + apply in_app_iff in H as [H|H].
      * pose proof (IHt2 k u x H) as HH. repeat rewrite in_app_iff in *. tauto.
      * pose proof (IHt3 k u x H) as HH. repeat rewrite in_app_iff in *. tauto.
  - apply in_app_iff in H as [H|H].
    + pose proof (IHt1 k u x H) as HH. repeat rewrite in_app_iff in *. tauto.
    + apply in_app_iff in H as [H|H].
      * pose proof (IHt2 k u x H) as HH. repeat rewrite in_app_iff in *. tauto.
      * pose proof (IHt3 k u x H) as HH. repeat rewrite in_app_iff in *. tauto.
Qed.

Lemma fv_natrec_unroll_subset : forall n b s r x,
  In x (fv (natrec_unroll n b s r)) -> In x (fv b ++ fv s).
Proof.
  induction n; intros b s r x H.
  - apply in_app_iff. left. exact H.
  - simpl in H |- *. rewrite app_nil_r in H. apply in_app_iff in H as [H|H].
    + apply in_app_iff. right. exact H.
    + eapply IHn; eauto.
Qed.

Lemma fv_protect_value_subset : forall v l x,
  In x (fv (protect_value v l)) -> In x (fv v).
Proof. destruct v; simpl; intros; auto. Qed.

Lemma step_fv_subset : forall t t', t --> t' ->
  forall x, In x (fv t') -> In x (fv t).
Proof.
  intros t t' Hstep. induction Hstep; intros x Hx; simpl in *;
    repeat rewrite in_app_iff in *; intuition eauto using fv_open_rec_subset,
      fv_natrec_unroll_subset, fv_protect_value_subset.
  - pose proof (fv_open_rec_subset body 0 v x Hx) as Hsub.
    apply in_app_iff in Hsub. exact Hsub.
  - pose proof (fv_open_rec_subset body1 0 v x Hx) as Hsub.
    apply in_app_iff in Hsub as [Harg|Hbranch]; tauto.
  - pose proof (fv_open_rec_subset body2 0 v x Hx) as Hsub.
    apply in_app_iff in Hsub as [Harg|Hbranch]; tauto.
  - pose proof (fv_natrec_unroll_subset n b s r x Hx) as Hsub.
    apply in_app_iff in Hsub. exact Hsub.
Qed.

Lemma multi_fv_subset : forall t t', t -->* t' ->
  forall x, In x (fv t') -> In x (fv t).
Proof.
  intros t t' Hm. induction Hm; intros x Hx; eauto using step_fv_subset.
Qed.

Lemma evaluates_closed_fv : forall t v,
  evaluates t v -> fv t = [] -> fv v = [].
Proof.
  intros t v [Hm Hv] Hempty.
  destruct (fv v) as [|a rest] eqn:E; [reflexivity|].
  assert (Ha : In a (fv v)) by (rewrite E; simpl; auto).
  pose proof (multi_fv_subset t v Hm a Ha) as Hin.
  rewrite Hempty in Hin. contradiction.
Qed.

Lemma subst_sim_commute_open_rec : forall Gamma rho y body k,
  ~ In y (context_atoms Gamma) ->
  (forall x, locally_closed (rho x)) ->
  subst_sim Gamma rho (open_rec k (tm_fvar y) body) =
    open_rec k (tm_fvar y) (subst_sim Gamma rho body).
Proof.
  induction body; intros k Hfresh Hrho; simpl; try reflexivity.
  - destruct (Nat.eqb k n); simpl.
    + rewrite (context_atoms_lookup_none Gamma y Hfresh). reflexivity.
    + reflexivity.
  - destruct (lookup_context a Gamma) as [T|] eqn:L; simpl.
    + destruct (Nat.eqb a y) eqn:E.
      * apply Nat.eqb_eq in E; subst a.
        rewrite (context_atoms_lookup_none Gamma y Hfresh) in L. discriminate.
      * rewrite open_rec_lc with (k := k) (v := tm_fvar y) (t := rho a).
        -- reflexivity.
        -- eapply lc_at_mono with (j := 0); [lia|exact (Hrho a)].
    + destruct (Nat.eqb a y); reflexivity.
  - f_equal. eapply IHbody; eauto.
  - f_equal; [eapply IHbody1|eapply IHbody2]; eauto.
  - f_equal; [eapply IHbody1|eapply IHbody2]; eauto.
  - f_equal. eapply IHbody; eauto.
  - f_equal. eapply IHbody; eauto.
  - f_equal. eapply IHbody; eauto.
  - f_equal. eapply IHbody; eauto.
  - f_equal; [eapply IHbody1|eapply IHbody2|eapply IHbody3]; eauto.
  - f_equal. eapply IHbody; eauto.
  - f_equal. eapply IHbody; eauto.
  - f_equal; [eapply IHbody1|eapply IHbody2|eapply IHbody3]; eauto.
  - f_equal; [eapply IHbody1|eapply IHbody2|eapply IHbody3]; eauto.
Qed.

Lemma subst_sim_open_arg : forall Gamma rho y A a body,
  ~ In y (context_atoms Gamma) ->
  lc_environment rho ->
  (forall x T, lookup_context x Gamma = Some T -> ~ In y (fv (rho x))) ->
  locally_closed a -> ~ In y (fv (subst_sim Gamma rho body)) ->
  subst_sim (update Gamma y A) (env_update rho y a) (open body (tm_fvar y)) =
    open (subst_sim Gamma rho body) a.
Proof.
  intros Gamma rho y A a body Hctx Hlc Havoid Harg Hfresh.
  unfold open at 1. rewrite subst_sim_open_rec with (Gamma := Gamma) (rho := rho)
    (y := y) (A := A) (a := a) (body := body) (k := 0); auto.
  rewrite subst_sim_commute_open_rec; auto.
  apply subst_open_same; assumption.
Qed.

Lemma term_rel_fst : forall A B k t1 t2 r,
  term_rel Low (Ty_Prod A B k) t1 t2 ->
  term_rel Low (ty_protect k.(indirect_reader) A) (tm_fst t1 r) (tm_fst t2 r).
Proof.
  intros A B [rk ik] t1 t2 r HR w1 w2 E1 E2. destruct ik.
  - destruct (evaluates_fst_inv _ _ _ E1) as [a1 [b1 [q1 [Ep1 Er1]]]].
    destruct (evaluates_fst_inv _ _ _ E2) as [a2 [b2 [q2 [Ep2 Er2]]]].
    pose proof (HR _ _ Ep1 Ep2) as Hpair. simpl in Hpair.
    destruct Hpair as [a1' [a2' [b1' [b2' [q1' [q2' [Eqa [Eqb [B1 [B2 [Ha Hb]]]]]]]]]]].
    inversion Eqa; inversion Eqb; subst.
    assert (Hq1 : indirect_reader q1' = Low) by (eapply flows_low_eq; exact B1).
    assert (Hq2 : indirect_reader q2' = Low) by (eapply flows_low_eq; exact B2).
    destruct (evaluates_protect_inv (indirect_reader q1') a1' w1 Er1) as [u1 [Eu1 Hu1]].
    destruct (evaluates_protect_inv (indirect_reader q2') a2' w2 Er2) as [u2 [Eu2 Hu2]].
    assert (Va1 : value a1') by (pose proof (proj2 Ep1) as Vp; inversion Vp; assumption).
    assert (Va2 : value a2') by (pose proof (proj2 Ep2) as Vp; inversion Vp; assumption).
    pose proof (value_multi_eq a1' u1 Va1 (proj1 Eu1)) as Eua1. subst u1.
    pose proof (value_multi_eq a2' u2 Va2 (proj1 Eu2)) as Eua2. subst u2.
    rewrite Hq1 in Hu1. rewrite Hq2 in Hu2.
    rewrite protect_value_low in Hu1, Hu2. rewrite Hu1, Hu2. rewrite ty_protect_low. exact Ha.
  - eapply hidden_values_related. apply ty_protect_high_ir.
Qed.

Lemma term_rel_snd : forall A B k t1 t2 r,
  term_rel Low (Ty_Prod A B k) t1 t2 ->
  term_rel Low (ty_protect k.(indirect_reader) B) (tm_snd t1 r) (tm_snd t2 r).
Proof.
  intros A B [rk ik] t1 t2 r HR w1 w2 E1 E2. destruct ik.
  - destruct (evaluates_snd_inv _ _ _ E1) as [a1 [b1 [q1 [Ep1 Er1]]]].
    destruct (evaluates_snd_inv _ _ _ E2) as [a2 [b2 [q2 [Ep2 Er2]]]].
    pose proof (HR _ _ Ep1 Ep2) as Hpair. simpl in Hpair.
    destruct Hpair as [a1' [a2' [b1' [b2' [q1' [q2' [Eqa [Eqb [B1 [B2 [Ha Hb]]]]]]]]]]].
    inversion Eqa; inversion Eqb; subst.
    assert (Hq1 : indirect_reader q1' = Low) by (eapply flows_low_eq; exact B1).
    assert (Hq2 : indirect_reader q2' = Low) by (eapply flows_low_eq; exact B2).
    destruct (evaluates_protect_inv (indirect_reader q1') b1' w1 Er1) as [u1 [Eu1 Hu1]].
    destruct (evaluates_protect_inv (indirect_reader q2') b2' w2 Er2) as [u2 [Eu2 Hu2]].
    assert (Vb1 : value b1') by (pose proof (proj2 Ep1) as Vp; inversion Vp; assumption).
    assert (Vb2 : value b2') by (pose proof (proj2 Ep2) as Vp; inversion Vp; assumption).
    pose proof (value_multi_eq b1' u1 Vb1 (proj1 Eu1)) as Eub1. subst u1.
    pose proof (value_multi_eq b2' u2 Vb2 (proj1 Eu2)) as Eub2. subst u2.
    rewrite Hq1 in Hu1. rewrite Hq2 in Hu2.
    rewrite protect_value_low in Hu1, Hu2. rewrite Hu1, Hu2. rewrite ty_protect_low. exact Hb.
  - eapply hidden_values_related. apply ty_protect_high_ir.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho1 rho2, lc_environment rho1 -> lc_environment rho2 ->
    env_rel Low Gamma rho1 rho2 ->
    term_rel Low T (subst_sim Gamma rho1 t) (subst_sim Gamma rho2 t).
Proof.
  intros Gamma t T HT. induction HT; intros rho1 rho2 Hc1 Hc2 Henv; simpl.
  - rewrite H. eapply Henv. exact H.
  - apply term_rel_unit.
  - destruct (exists_fresh_env_binder L Gamma body rho1 rho2)
      as [y [HyL [HyG [HyBody [HyR1 [HyR2 [HyS1 HyS2]]]]]]].
    assert (HbodyLC : lc_at 1 body).
    { pose proof (has_type_locally_closed (update Gamma y T1)
        (open body (tm_fvar y)) T2 (H1 y HyL)) as HopenLC.
      unfold locally_closed, open in HopenLC.
      eapply lc_at_open_fvar_inv with (x := y); exact HopenLC. }
    assert (Vabs1 : value (tm_abs T1 (subst_sim Gamma rho1 body) kappa)).
    { apply v_abs. unfold locally_closed. eapply lc_at_subst_sim; eauto. }
    assert (Vabs2 : value (tm_abs T1 (subst_sim Gamma rho2 body) kappa)).
    { apply v_abs. unfold locally_closed. eapply lc_at_subst_sim; eauto. }
    intros v1 v2 [M1 V1] [M2 V2].
    assert (Ev1 : v1 = tm_abs T1 (subst_sim Gamma rho1 body) kappa)
      by (eapply value_multi_eq; [exact Vabs1|exact M1]).
    assert (Ev2 : v2 = tm_abs T1 (subst_sim Gamma rho2 body) kappa)
      by (eapply value_multi_eq; [exact Vabs2|exact M2]).
    subst v1. subst v2. destruct (indirect_reader kappa) eqn:Eir.
    + unfold value_rel. rewrite Eir. simpl.
      exists T1,T1,(subst_sim Gamma rho1 body),(subst_sim Gamma rho2 body),kappa,kappa.
      split; [reflexivity|]. split; [reflexivity|].
      split; [unfold security_bound; apply flows_refl|].
      split; [unfold security_bound; apply flows_refl|].
      intros a1 a2 w1 w2 Harg Va1 Va2 Ea1 Ea2.
      pose proof (term_rel_value Low T1 a1 a2 Va1 Va2 Harg) as HargTerm.
      pose proof (env_rel_extend Low Gamma rho1 rho2 y T1 a1 a2 HyG Henv HargTerm) as Henv'.
      pose proof (lc_environment_update rho1 y a1 Hc1 (value_locally_closed a1 Va1)) as Hlc1'.
      pose proof (lc_environment_update rho2 y a2 Hc2 (value_locally_closed a2 Va2)) as Hlc2'.
      pose proof (H2 y HyL (env_update rho1 y a1) (env_update rho2 y a2)
          Hlc1' Hlc2' Henv') as HbodyRel.
      rewrite (subst_sim_open_arg Gamma rho1 y T1 a1 body HyG Hc1 HyR1
          (value_locally_closed a1 Va1) HyS1) in HbodyRel.
      rewrite (subst_sim_open_arg Gamma rho2 y T1 a2 body HyG Hc2 HyR2
          (value_locally_closed a2 Va2) HyS2) in HbodyRel.
      pose proof (proj1 (evaluates_app_value_iff T1 (subst_sim Gamma rho1 body)
          kappa a1 (reader kappa) w1 Vabs1 Va1 (flows_refl (reader kappa))) Ea1) as Ep1.
      pose proof (proj1 (evaluates_app_value_iff T1 (subst_sim Gamma rho2 body)
          kappa a2 (reader kappa) w2 Vabs2 Va2 (flows_refl (reader kappa))) Ea2) as Ep2.
      rewrite Eir in Ep1, Ep2. simpl.
      destruct (evaluates_protect_inv Low _ _ Ep1) as [u1 [Eu1 ->]].
      destruct (evaluates_protect_inv Low _ _ Ep2) as [u2 [Eu2 ->]].
      rewrite protect_value_low, protect_value_low. eapply HbodyRel; eassumption.
    + unfold value_rel. rewrite Eir. simpl. exact I.
  - eapply term_rel_app; [eapply IHHT1|eapply IHHT2]; eauto.
  - eapply term_rel_pair; [eapply IHHT1|eapply IHHT2]; eauto.
  - eapply term_rel_fst. eapply IHHT; eauto.
  - eapply term_rel_snd. eapply IHHT; eauto.
  - eapply term_rel_inl. eapply IHHT; eauto.
  - eapply term_rel_inr. eapply IHHT; eauto.
  - match goal with |- ?G => idtac G end.
  - destruct l; [eapply term_rel_protect_low|eapply term_rel_protect_high];
      eapply IHHT; eauto.
  - intros v1 v2 E1 E2. eapply value_rel_subtype; [exact H|].
    eapply IHHT; eauto.
  - apply term_rel_nat.
  - eapply term_rel_succ. eapply IHHT; eauto.
  - match goal with |- ?G => idtac G end.
  - match goal with |- ?G => idtac G end.
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
