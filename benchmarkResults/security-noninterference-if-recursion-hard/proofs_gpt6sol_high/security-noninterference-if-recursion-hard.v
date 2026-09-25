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

(* A terminating big-step presentation of the operational semantics.  It is
   convenient for stating the logical relation; the result of a [big]
   derivation is always a value. *)
Inductive big : tm -> tm -> Prop :=
  | B_Value : forall v, value v -> big v v
  | B_App : forall f a T body k v w r,
      big f (tm_abs T body k) -> big a v ->
      flows_to k.(reader) r -> big (open body v) w ->
      big (tm_app f a r) (protect_value w k.(indirect_reader))
  | B_Pair : forall a b v w k,
      big a v -> big b w -> big (tm_pair a b k) (tm_pair v w k)
  | B_Fst : forall t v w k r,
      big t (tm_pair v w k) -> flows_to k.(reader) r ->
      big (tm_fst t r) (protect_value v k.(indirect_reader))
  | B_Snd : forall t v w k r,
      big t (tm_pair v w k) -> flows_to k.(reader) r ->
      big (tm_snd t r) (protect_value w k.(indirect_reader))
  | B_Inl : forall t v k, big t v -> big (tm_inl t k) (tm_inl v k)
  | B_Inr : forall t v k, big t v -> big (tm_inr t k) (tm_inr v k)
  | B_CaseLeft : forall t body1 body2 v k w r,
      big t (tm_inl v k) -> flows_to k.(reader) r ->
      big (open body1 v) w ->
      big (tm_case t body1 body2 r) (protect_value w k.(indirect_reader))
  | B_CaseRight : forall t body1 body2 v k w r,
      big t (tm_inr v k) -> flows_to k.(reader) r ->
      big (open body2 v) w ->
      big (tm_case t body1 body2 r) (protect_value w k.(indirect_reader))
  | B_Protect : forall l t v, big t v ->
      big (tm_protect l t) (protect_value v l)
  | B_Succ : forall t n k r,
      big t (tm_nat n k) -> flows_to k.(reader) r ->
      big (tm_succ t r)
        (protect_value (tm_nat (S n) public) k.(indirect_reader))
  | B_Rec : forall t b s n k v w z r,
      big t (tm_nat n k) -> big b v -> big s w ->
      flows_to k.(reader) r -> big (natrec_unroll n v w r) z ->
      big (tm_natrec t b s r) (protect_value z k.(indirect_reader))
  | B_IfTrue : forall c yes no v k w r,
      big c (tm_inl v k) -> flows_to k.(reader) r -> big yes w ->
      big (tm_if c yes no r) (protect_value w k.(indirect_reader))
  | B_IfFalse : forall c yes no v k w r,
      big c (tm_inr v k) -> flows_to k.(reader) r -> big no w ->
      big (tm_if c yes no r) (protect_value w k.(indirect_reader)).

(* At a high indirect-reader level a pair of values carries no observable
   requirement.  At a low level, ground values have the same shape and
   data, and functions map related value arguments to related results.
   The security bound records the annotation on the actual value, which
   can be more precise than the type after subsumption. *)
Fixpoint value_rel (T : ty) (v1 v2 : tm) : Prop :=
  match (security_of T).(indirect_reader) with
  | High => True
  | Low =>
      match T, v1, v2 with
      | Ty_Unit k, tm_unit k1, tm_unit k2 =>
          security_le k1 k /\ security_le k2 k
      | Ty_Nat k, tm_nat n1 k1, tm_nat n2 k2 =>
          n1 = n2 /\ security_le k1 k /\ security_le k2 k
      | Ty_Sum A B k, tm_inl a k1, tm_inl b k2 =>
          security_le k1 k /\ security_le k2 k /\ value_rel A a b
      | Ty_Sum A B k, tm_inr a k1, tm_inr b k2 =>
          security_le k1 k /\ security_le k2 k /\ value_rel B a b
      | Ty_Prod A B k, tm_pair a1 b1 k1, tm_pair a2 b2 k2 =>
          security_le k1 k /\ security_le k2 k /\
          value_rel A a1 a2 /\ value_rel B b1 b2
      | Ty_Arrow A B k, tm_abs A1 body1 k1, tm_abs A2 body2 k2 =>
          security_le k1 k /\ security_le k2 k /\
          (forall a1 a2 r, value a1 -> value a2 ->
            value_rel A a1 a2 -> flows_to k.(reader) r ->
            forall w1 w2,
              big (tm_app v1 a1 r) w1 -> big (tm_app v2 a2 r) w2 ->
              value_rel B w1 w2)
      | _, _, _ => False
      end
  end.

Definition expr_rel (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, big t1 v1 -> big t2 v2 -> value_rel T v1 v2.

Lemma security_le_refl : forall k, security_le k k.
Proof. intros [r i]; destruct r, i; split; simpl; auto. Qed.

Lemma flows_to_trans : forall a b c,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. intros [] [] []; simpl; auto. Qed.

Lemma security_le_trans : forall a b c,
  security_le a b -> security_le b c -> security_le a c.
Proof.
  intros a b c [H1 H2] [H3 H4]; split;
    eapply flows_to_trans; eauto.
Qed.

Lemma protect_security_low : forall k, protect_security k Low = k.
Proof. intros [r i]; destruct r, i; reflexivity. Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof. intros []; simpl; rewrite protect_security_low; reflexivity. Qed.

Lemma protect_value_low : forall v, protect_value v Low = v.
Proof.
  intros []; simpl; try reflexivity;
    rewrite protect_security_low; reflexivity.
Qed.

Lemma protect_value_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l H; inversion H; subst; simpl; try (constructor; assumption);
    try constructor.
Qed.

Lemma big_result_value : forall t v, big t v -> value v.
Proof.
  intros t v H; induction H; eauto using value, protect_value_value;
    inversion IHbig; subst; eauto using protect_value_value.
Qed.

Lemma big_value_self : forall v w, value v -> big v w -> v = w.
Proof.
  intros v w Hv Hb; revert Hv.
  induction Hb; intros Hv; try solve [inversion Hv].
  - reflexivity.
  - inversion Hv; subst. f_equal; [eapply IHHb1 | eapply IHHb2]; eauto.
  - inversion Hv; subst. f_equal. eapply IHHb; eauto.
  - inversion Hv; subst. f_equal. eapply IHHb; eauto.
Qed.

Lemma expr_rel_value : forall T v1 v2,
  value v1 -> value v2 -> value_rel T v1 v2 -> expr_rel T v1 v2.
Proof.
  unfold expr_rel. intros T v1 v2 Hv1 Hv2 Hr w1 w2 Hb1 Hb2.
  pose proof (big_value_self _ _ Hv1 Hb1) as E1.
  pose proof (big_value_self _ _ Hv2 Hb2) as E2.
  subst; assumption.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed v.
Proof.
  intros v H; induction H; unfold locally_closed in *; simpl; auto.
Qed.

Lemma value_rel_high : forall T v1 v2,
  (security_of T).(indirect_reader) = High -> value_rel T v1 v2.
Proof.
  intros [] v1 v2 H; simpl in *; rewrite H; exact I.
Qed.

Lemma expr_rel_high : forall T t1 t2,
  (security_of T).(indirect_reader) = High -> expr_rel T t1 t2.
Proof.
  unfold expr_rel; intros; apply value_rel_high; assumption.
Qed.

Lemma ty_protect_high : forall T l,
  l = High \/ (security_of T).(indirect_reader) = High ->
  (security_of (ty_protect l T)).(indirect_reader) = High.
Proof.
  intros [] [] [H|H]; simpl in *; try discriminate;
    destruct s as [r i]; simpl in *; destruct i; simpl in *;
    try discriminate; reflexivity.
Qed.

Lemma ty_protect_low_inv : forall T l,
  (security_of (ty_protect l T)).(indirect_reader) = Low ->
  l = Low /\ (security_of T).(indirect_reader) = Low.
Proof.
  intros T l H. destruct l.
  - split; auto. rewrite ty_protect_low in H; exact H.
  - exfalso. pose proof (ty_protect_high T High (or_introl eq_refl)).
    congruence.
Qed.

Lemma security_le_low_indirect : forall a b,
  security_le a b -> b.(indirect_reader) = Low ->
  a.(indirect_reader) = Low.
Proof.
  intros [ar ai] [br bi] [_ H] E; simpl in *; subst bi.
  destruct ai; auto; contradiction.
Qed.

Lemma value_rel_protect : forall T v1 v2 l,
  value_rel T v1 v2 ->
  value_rel (ty_protect l T)
    (protect_value v1 l) (protect_value v2 l).
Proof.
  intros T v1 v2 l H.
  destruct l.
  - repeat rewrite protect_value_low. rewrite ty_protect_low. exact H.
  - apply value_rel_high. apply ty_protect_high. left; reflexivity.
Qed.

Lemma big_protect_inv : forall l t w,
  big (tm_protect l t) w ->
  exists v, big t v /\ w = protect_value v l.
Proof.
  intros l t w H; inversion H; subst.
  - inversion H0.
  - eauto.
Qed.

Lemma big_pair_inv : forall a b k w,
  big (tm_pair a b k) w ->
  exists va vb, big a va /\ big b vb /\ w = tm_pair va vb k.
Proof.
  intros a b k w H; inversion H; subst.
  - inversion H0; subst; exists a, b; repeat split; eauto using big.
  - eauto.
Qed.

Lemma big_inl_inv : forall a k w,
  big (tm_inl a k) w ->
  exists va, big a va /\ w = tm_inl va k.
Proof.
  intros a k w H; inversion H; subst.
  - inversion H0; subst; exists a; split; eauto using big.
  - eauto.
Qed.

Lemma big_inr_inv : forall a k w,
  big (tm_inr a k) w ->
  exists va, big a va /\ w = tm_inr va k.
Proof.
  intros a k w H; inversion H; subst.
  - inversion H0; subst; exists a; split; eauto using big.
  - eauto.
Qed.

Ltac impossible_value :=
  match goal with
  | H : value (tm_app _ _ _) |- _ => inversion H
  | H : value (tm_fst _ _) |- _ => inversion H
  | H : value (tm_snd _ _) |- _ => inversion H
  | H : value (tm_case _ _ _ _) |- _ => inversion H
  | H : value (tm_protect _ _) |- _ => inversion H
  | H : value (tm_succ _ _) |- _ => inversion H
  | H : value (tm_natrec _ _ _ _) |- _ => inversion H
  | H : value (tm_if _ _ _ _) |- _ => inversion H
  end.

Lemma big_step_backward : forall t t' v,
  t --> t' -> big t' v -> big t v.
Proof.
  intros t t' v Hs; revert v.
  induction Hs; intros w Hw.
  - destruct (big_protect_inv _ _ _ Hw) as [z [Hz ->]].
    eapply B_App; eauto using big.
  - inversion Hw; subst; try solve [impossible_value].
    eapply B_App; eauto.
  - inversion Hw; subst; try solve [impossible_value].
    eapply B_App; eauto.
  - destruct (big_pair_inv _ _ _ _ Hw) as [a [b [Ha [Hb ->]]]].
    eapply B_Pair; eauto.
  - destruct (big_pair_inv _ _ _ _ Hw) as [a [b [Ha [Hb ->]]]].
    eapply B_Pair; eauto using big.
  - destruct (big_protect_inv _ _ _ Hw) as [z [Hz ->]].
    eapply B_Fst; eauto using big.
  - inversion Hw; subst; try solve [impossible_value].
    eapply B_Fst; eauto.
  - destruct (big_protect_inv _ _ _ Hw) as [z [Hz ->]].
    eapply B_Snd; eauto using big.
  - inversion Hw; subst; try solve [impossible_value].
    eapply B_Snd; eauto.
  - destruct (big_inl_inv _ _ _ Hw) as [a [Ha ->]].
    eapply B_Inl; eauto.
  - destruct (big_inr_inv _ _ _ Hw) as [a [Ha ->]].
    eapply B_Inr; eauto.
  - destruct (big_protect_inv _ _ _ Hw) as [z [Hz ->]].
    eapply B_CaseLeft; eauto using big.
  - destruct (big_protect_inv _ _ _ Hw) as [z [Hz ->]].
    eapply B_CaseRight; eauto using big.
  - inversion Hw; subst; try solve [impossible_value].
    eapply B_CaseLeft; eauto.
    eapply B_CaseRight; eauto.
  - pose proof (protect_value_value v l H) as Hv.
    pose proof (big_value_self _ _ Hv Hw) as E; subst w.
    apply B_Protect. apply B_Value. exact H.
  - destruct (big_protect_inv _ _ _ Hw) as [z [Hz ->]].
    eapply B_Protect; eauto.
  - inversion Hw; subst; try solve [impossible_value].
    eapply B_Succ; eauto.
  - destruct (big_protect_inv _ _ _ Hw) as [z [Hz ->]].
    inversion Hz; subst; try solve [impossible_value].
    eapply B_Succ; eauto using big, value.
  - inversion Hw; subst; try solve [impossible_value].
    eapply B_Rec; eauto.
  - inversion Hw; subst; try solve [impossible_value].
    eapply B_Rec; eauto.
  - inversion Hw; subst; try solve [impossible_value].
    eapply B_Rec; eauto.
  - destruct (big_protect_inv _ _ _ Hw) as [z [Hz ->]].
    eapply B_Rec; eauto using big, value.
  - inversion Hw; subst; try solve [impossible_value].
    eapply B_IfTrue; eauto.
    eapply B_IfFalse; eauto.
  - destruct (big_protect_inv _ _ _ Hw) as [z [Hz ->]].
    eapply B_IfTrue; eauto using big.
  - destruct (big_protect_inv _ _ _ Hw) as [z [Hz ->]].
    eapply B_IfFalse; eauto using big.
Qed.

Lemma evaluates_big : forall t v, evaluates t v -> big t v.
Proof.
  intros t v [Hm Hv]; induction Hm; eauto using big, big_step_backward.
Qed.

Fixpoint close (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit k => tm_unit k
  | tm_abs T body k => tm_abs T (close rho body) k
  | tm_app a b r => tm_app (close rho a) (close rho b) r
  | tm_pair a b k => tm_pair (close rho a) (close rho b) k
  | tm_fst a r => tm_fst (close rho a) r
  | tm_snd a r => tm_snd (close rho a) r
  | tm_inl a k => tm_inl (close rho a) k
  | tm_inr a k => tm_inr (close rho a) k
  | tm_case a b c r => tm_case (close rho a) (close rho b) (close rho c) r
  | tm_protect l a => tm_protect l (close rho a)
  | tm_nat n k => tm_nat n k
  | tm_succ a r => tm_succ (close rho a) r
  | tm_natrec a b c r => tm_natrec (close rho a) (close rho b) (close rho c) r
  | tm_if a b c r => tm_if (close rho a) (close rho b) (close rho c) r
  end.

Lemma open_rec_inert : forall t d k u,
  lc_at d t -> d <= k -> open_rec k u t = t.
Proof.
  induction t; intros d k u Hle Hk; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal. eapply IHt; eauto; lia.
  - destruct Hle. f_equal; [eapply IHt1 | eapply IHt2]; eauto.
  - destruct Hle. f_equal; [eapply IHt1 | eapply IHt2]; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - destruct Hle as [? [? ?]]. f_equal;
      [eapply IHt1 | eapply IHt2 | eapply IHt3]; eauto; lia.
  - f_equal; eauto.
  - f_equal; eauto.
  - destruct Hle as [? [? ?]]. f_equal;
      [eapply IHt1 | eapply IHt2 | eapply IHt3]; eauto.
  - destruct Hle as [? [? ?]]. f_equal;
      [eapply IHt1 | eapply IHt2 | eapply IHt3]; eauto.
Qed.

Lemma open_rec_closed : forall t k u,
  locally_closed t -> open_rec k u t = t.
Proof. intros t k u H; eapply open_rec_inert; eauto; lia. Qed.

Definition env_rel (Gamma : context) (rho1 rho2 : atom -> tm) : Prop :=
  (forall x, locally_closed (rho1 x) /\ locally_closed (rho2 x)) /\
  (forall x T, lookup_context x Gamma = Some T ->
     expr_rel T (rho1 x) (rho2 x)).

Definition put (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

Lemma close_open_rec : forall t k u rho,
  (forall x, locally_closed (rho x)) ->
  close rho (open_rec k u t) =
    open_rec k (close rho u) (close rho t).
Proof.
  induction t; intros k u rho Hr; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_closed. apply Hr.
  - f_equal. apply IHt. exact Hr.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hr.
  - f_equal; [apply IHt1 | apply IHt2]; exact Hr.
  - f_equal; apply IHt; exact Hr.
  - f_equal; apply IHt; exact Hr.
  - f_equal; apply IHt; exact Hr.
  - f_equal; apply IHt; exact Hr.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; exact Hr.
  - f_equal; apply IHt; exact Hr.
  - f_equal; apply IHt; exact Hr.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; exact Hr.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; exact Hr.
Qed.

Lemma close_open : forall body u rho,
  (forall x, locally_closed (rho x)) ->
  close rho (open body u) = open (close rho body) (close rho u).
Proof. intros; unfold open; apply close_open_rec; assumption. Qed.

Lemma close_ext : forall t rho1 rho2,
  (forall x, In x (fv t) -> rho1 x = rho2 x) ->
  close rho1 t = close rho2 t.
Proof.
  induction t; intros rho1 rho2 H; simpl in *; try reflexivity.
  - apply H. simpl; auto.
  - f_equal. apply IHt. exact H.
  - f_equal; [apply IHt1 | apply IHt2]; intros x Hx; apply H;
      apply in_or_app; [left | right]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; intros x Hx; apply H;
      apply in_or_app; [left | right]; assumption.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3];
      intros x Hx; apply H; repeat rewrite in_app_iff;
      try (left; assumption); try (right; left; assumption);
      right; right; assumption.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3];
      intros x Hx; apply H; repeat rewrite in_app_iff;
      try (left; assumption); try (right; left; assumption);
      right; right; assumption.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3];
      intros x Hx; apply H; repeat rewrite in_app_iff;
      try (left; assumption); try (right; left; assumption);
      right; right; assumption.
Qed.

Lemma big_app_inv : forall f a r z,
  big (tm_app f a r) z ->
  exists A body k v w,
    big f (tm_abs A body k) /\ big a v /\
    flows_to k.(reader) r /\ big (open body v) w /\
    z = protect_value w k.(indirect_reader).
Proof.
  intros f a r z H; inversion H; subst; try impossible_value; eauto 10.
Qed.

Lemma expr_rel_pair : forall A B k a1 a2 b1 b2,
  expr_rel A a1 a2 -> expr_rel B b1 b2 ->
  expr_rel (Ty_Prod A B k) (tm_pair a1 b1 k) (tm_pair a2 b2 k).
Proof.
  intros A B [r i] a1 a2 b1 b2 Ha Hb va vb Hba Hbb.
  destruct i; [|exact I].
  destruct (big_pair_inv _ _ _ _ Hba)
    as [x1 [y1 [Hx1 [Hy1 E1]]]].
  destruct (big_pair_inv _ _ _ _ Hbb)
    as [x2 [y2 [Hx2 [Hy2 E2]]]].
  subst va vb; simpl; repeat split; try (destruct r; simpl; auto).
Qed.

Lemma expr_rel_inl : forall A B k a1 a2,
  expr_rel A a1 a2 ->
  expr_rel (Ty_Sum A B k) (tm_inl a1 k) (tm_inl a2 k).
Proof.
  intros A B [r i] a1 a2 Ha va vb Hba Hbb.
  destruct i; [|exact I].
  destruct (big_inl_inv _ _ _ Hba) as [x1 [Hx1 E1]].
  destruct (big_inl_inv _ _ _ Hbb) as [x2 [Hx2 E2]].
  subst va vb; simpl; repeat split; try (destruct r; simpl; auto).
Qed.

Lemma expr_rel_inr : forall A B k a1 a2,
  expr_rel B a1 a2 ->
  expr_rel (Ty_Sum A B k) (tm_inr a1 k) (tm_inr a2 k).
Proof.
  intros A B [r i] a1 a2 Ha va vb Hba Hbb.
  destruct i; [|exact I].
  destruct (big_inr_inv _ _ _ Hba) as [x1 [Hx1 E1]].
  destruct (big_inr_inv _ _ _ Hbb) as [x2 [Hx2 E2]].
  subst va vb; simpl; repeat split; try (destruct r; simpl; auto).
Qed.

Lemma expr_rel_protect : forall T l a1 a2,
  expr_rel T a1 a2 ->
  expr_rel (ty_protect l T) (tm_protect l a1) (tm_protect l a2).
Proof.
  intros T l a1 a2 Hrel va vb Hba Hbb.
  destruct (big_protect_inv _ _ _ Hba) as [x1 [Hx1 E1]].
  destruct (big_protect_inv _ _ _ Hbb) as [x2 [Hx2 E2]].
  subst va vb. apply value_rel_protect. eapply Hrel; eauto.
Qed.

Lemma expr_rel_app : forall A B k r f1 f2 a1 a2,
  flows_to k.(reader) r ->
  expr_rel (Ty_Arrow A B k) f1 f2 ->
  expr_rel A a1 a2 ->
  expr_rel (ty_protect k.(indirect_reader) B)
    (tm_app f1 a1 r) (tm_app f2 a2 r).
Proof.
  intros A B k r f1 f2 a1 a2 Hflow Hf Ha z1 z2 Hb1 Hb2.
  destruct ((security_of (ty_protect k.(indirect_reader) B)).(indirect_reader))
    eqn:Eout.
  - apply ty_protect_low_inv in Eout as [Ek EB].
    rewrite Ek in *; rewrite ty_protect_low.
    destruct (big_app_inv _ _ _ _ Hb1)
      as [A1 [body1 [k1 [v1 [w1 [Hf1 [Ha1 [Hk1 [Hw1 Ez1]]]]]]]]].
    destruct (big_app_inv _ _ _ _ Hb2)
      as [A2 [body2 [k2 [v2 [w2 [Hf2 [Ha2 [Hk2 [Hw2 Ez2]]]]]]]]].
    subst z1 z2.
    pose proof (Hf _ _ Hf1 Hf2) as Hfr.
    simpl in Hfr. rewrite Ek in Hfr.
    destruct Hfr as [_ [_ Hfun]].
    pose proof (Hfun v1 v2 r (big_result_value _ _ Ha1)
      (big_result_value _ _ Ha2) (Ha _ _ Ha1 Ha2) Hflow) as Hres.
    eapply Hres; eapply B_App; eauto using big, big_result_value.
  - apply value_rel_high. exact Eout.
Qed.

Lemma subtype_security_le : forall T U,
  subtype T U -> security_le (security_of T) (security_of U).
Proof.
  intros T U H; induction H; simpl; eauto using security_le_trans.
Qed.

Lemma value_rel_subtype : forall T U,
  subtype T U -> forall v1 v2,
  value_rel T v1 v2 -> value_rel U v1 v2.
Proof.
  intros T U Hsub; induction Hsub; intros v1 v2 Hr.
  - destruct (indirect_reader kappa2) eqn:E2.
    + match goal with Hle : security_le kappa1 kappa2 |- _ =>
        pose proof (security_le_low_indirect _ _ Hle E2) as E1 end.
      simpl in Hr; rewrite E1 in Hr.
      simpl; rewrite E2.
      destruct v1; destruct v2; simpl in Hr; try contradiction.
      destruct Hr as [Ha Hb]; split;
        eapply security_le_trans; eauto.
    + apply value_rel_high; simpl; exact E2.
  - destruct (indirect_reader kappa2) eqn:E2.
    + match goal with Hle : security_le kappa1 kappa2 |- _ =>
        pose proof (security_le_low_indirect _ _ Hle E2) as E1 end.
      simpl in Hr; rewrite E1 in Hr.
      simpl; rewrite E2.
      destruct v1; destruct v2; simpl in Hr; try contradiction;
        destruct Hr as [Ha [Hb Hchild]];
        repeat split;
        try (eapply security_le_trans; eauto);
        eauto.
    + apply value_rel_high; simpl; exact E2.
  - destruct (indirect_reader kappa2) eqn:E2.
    + match goal with Hle : security_le kappa1 kappa2 |- _ =>
        pose proof (security_le_low_indirect _ _ Hle E2) as E1 end.
      simpl in Hr; rewrite E1 in Hr.
      simpl; rewrite E2.
      destruct v1; destruct v2; simpl in Hr; try contradiction.
      destruct Hr as [Ha [Hb [Hleft Hright]]].
      repeat split;
        try (eapply security_le_trans; eauto);
        eauto.
    + apply value_rel_high; simpl; exact E2.
  - destruct (indirect_reader kappa2) eqn:E2.
    + match goal with Hle : security_le kappa1 kappa2 |- _ =>
        pose proof (security_le_low_indirect _ _ Hle E2) as E1;
        pose proof (proj1 Hle) as Hreader end.
      simpl in Hr; rewrite E1 in Hr.
      simpl; rewrite E2.
      destruct v1; destruct v2; simpl in Hr; try contradiction.
      destruct Hr as [Ha [Hb Hfun]].
      repeat split;
        try (eapply security_le_trans; eauto).
      intros a1 a2 r Hva1 Hva2 Harg Hflow w1 w2 Hap1 Hap2.
      apply IHHsub2.
      eapply (Hfun a1 a2 r Hva1 Hva2 (IHHsub1 a1 a2 Harg)); eauto.
      eapply flows_to_trans; [exact Hreader|exact Hflow].
    + apply value_rel_high; simpl; exact E2.
  - apply IHHsub2. apply IHHsub1. exact Hr.
  - destruct (indirect_reader k2) eqn:E2.
    + match goal with Hle : security_le k1 k2 |- _ =>
        pose proof (security_le_low_indirect _ _ Hle E2) as E1 end.
      simpl in Hr; rewrite E1 in Hr.
      simpl; rewrite E2.
      destruct v1; destruct v2; simpl in Hr; try contradiction.
      destruct Hr as [En [Ha Hb]].
      destruct Ha as [Har Hai]; destruct Hb as [Hbr Hbi].
      destruct H1 as [Hrr Hii].
      repeat split; eauto using flows_to_trans.
    + apply value_rel_high; simpl; exact E2.
Qed.

Lemma expr_rel_subtype : forall T U t1 t2,
  subtype T U -> expr_rel T t1 t2 -> expr_rel U t1 t2.
Proof.
  intros T U t1 t2 Hsub Hr v1 v2 Hb1 Hb2.
  eapply value_rel_subtype; eauto.
Qed.

Lemma big_fst_inv : forall t r z,
  big (tm_fst t r) z ->
  exists a b k, big t (tm_pair a b k) /\ flows_to k.(reader) r /\
    z = protect_value a k.(indirect_reader).
Proof.
  intros t r z H; inversion H; subst; try impossible_value; eauto 10.
Qed.

Lemma big_snd_inv : forall t r z,
  big (tm_snd t r) z ->
  exists a b k, big t (tm_pair a b k) /\ flows_to k.(reader) r /\
    z = protect_value b k.(indirect_reader).
Proof.
  intros t r z H; inversion H; subst; try impossible_value; eauto 10.
Qed.

Lemma big_succ_inv : forall t r z,
  big (tm_succ t r) z ->
  exists n k, big t (tm_nat n k) /\ flows_to k.(reader) r /\
    z = protect_value (tm_nat (S n) public) k.(indirect_reader).
Proof.
  intros t r z H; inversion H; subst; try impossible_value; eauto 10.
Qed.

Lemma big_rec_inv : forall t b s r z,
  big (tm_natrec t b s r) z ->
  exists n k v w u,
    big t (tm_nat n k) /\ big b v /\ big s w /\
    flows_to k.(reader) r /\ big (natrec_unroll n v w r) u /\
    z = protect_value u k.(indirect_reader).
Proof.
  intros t b s r z H; inversion H; subst; try impossible_value; eauto 12.
Qed.

Lemma big_if_inv : forall c y n r z,
  big (tm_if c y n r) z ->
  (exists v k w,
      big c (tm_inl v k) /\ flows_to k.(reader) r /\
      big y w /\ z = protect_value w k.(indirect_reader)) \/
  (exists v k w,
      big c (tm_inr v k) /\ flows_to k.(reader) r /\
      big n w /\ z = protect_value w k.(indirect_reader)).
Proof.
  intros c y n r z H; inversion H; subst; try impossible_value; eauto 12.
Qed.

Lemma big_case_inv : forall t b1 b2 r z,
  big (tm_case t b1 b2 r) z ->
  (exists v k w,
      big t (tm_inl v k) /\ flows_to k.(reader) r /\
      big (open b1 v) w /\ z = protect_value w k.(indirect_reader)) \/
  (exists v k w,
      big t (tm_inr v k) /\ flows_to k.(reader) r /\
      big (open b2 v) w /\ z = protect_value w k.(indirect_reader)).
Proof.
  intros t b1 b2 r z H; inversion H; subst; try impossible_value; eauto 12.
Qed.

Lemma expr_rel_fst : forall A B k r t1 t2,
  expr_rel (Ty_Prod A B k) t1 t2 ->
  expr_rel (ty_protect k.(indirect_reader) A)
    (tm_fst t1 r) (tm_fst t2 r).
Proof.
  intros A B k r t1 t2 Ht z1 z2 Hb1 Hb2.
  destruct ((security_of (ty_protect k.(indirect_reader) A)).(indirect_reader))
    eqn:Eout.
  - apply ty_protect_low_inv in Eout as [Ek EA].
    rewrite Ek in *; rewrite ty_protect_low.
    destruct (big_fst_inv _ _ _ Hb1)
      as [a1 [b1 [k1 [Ht1 [_ Ez1]]]]].
    destruct (big_fst_inv _ _ _ Hb2)
      as [a2 [b2 [k2 [Ht2 [_ Ez2]]]]].
    subst z1 z2.
    pose proof (Ht _ _ Ht1 Ht2) as Hr.
    simpl in Hr; rewrite Ek in Hr.
    destruct Hr as [Hs1 [Hs2 [HA HB]]].
    pose proof (security_le_low_indirect _ _ Hs1 Ek) as E1.
    pose proof (security_le_low_indirect _ _ Hs2 Ek) as E2.
    rewrite E1, E2; repeat rewrite protect_value_low.
    exact HA.
  - apply value_rel_high. exact Eout.
Qed.

Lemma expr_rel_snd : forall A B k r t1 t2,
  expr_rel (Ty_Prod A B k) t1 t2 ->
  expr_rel (ty_protect k.(indirect_reader) B)
    (tm_snd t1 r) (tm_snd t2 r).
Proof.
  intros A B k r t1 t2 Ht z1 z2 Hb1 Hb2.
  destruct ((security_of (ty_protect k.(indirect_reader) B)).(indirect_reader))
    eqn:Eout.
  - apply ty_protect_low_inv in Eout as [Ek EB].
    rewrite Ek in *; rewrite ty_protect_low.
    destruct (big_snd_inv _ _ _ Hb1)
      as [a1 [b1 [k1 [Ht1 [_ Ez1]]]]].
    destruct (big_snd_inv _ _ _ Hb2)
      as [a2 [b2 [k2 [Ht2 [_ Ez2]]]]].
    subst z1 z2.
    pose proof (Ht _ _ Ht1 Ht2) as Hr.
    simpl in Hr; rewrite Ek in Hr.
    destruct Hr as [Hs1 [Hs2 [HA HB]]].
    pose proof (security_le_low_indirect _ _ Hs1 Ek) as E1.
    pose proof (security_le_low_indirect _ _ Hs2 Ek) as E2.
    rewrite E1, E2; repeat rewrite protect_value_low.
    exact HB.
  - apply value_rel_high. exact Eout.
Qed.

Lemma expr_rel_succ : forall k r t1 t2,
  expr_rel (Ty_Nat k) t1 t2 ->
  expr_rel (ty_protect k.(indirect_reader) (Ty_Nat public))
    (tm_succ t1 r) (tm_succ t2 r).
Proof.
  intros k r t1 t2 Ht z1 z2 Hb1 Hb2.
  destruct ((security_of (ty_protect k.(indirect_reader)
      (Ty_Nat public))).(indirect_reader)) eqn:Eout.
  - apply ty_protect_low_inv in Eout as [Ek _].
    rewrite Ek in *; rewrite ty_protect_low.
    destruct (big_succ_inv _ _ _ Hb1) as [n1 [k1 [Ht1 [_ Ez1]]]].
    destruct (big_succ_inv _ _ _ Hb2) as [n2 [k2 [Ht2 [_ Ez2]]]].
    subst z1 z2.
    pose proof (Ht _ _ Ht1 Ht2) as Hr.
    simpl in Hr; rewrite Ek in Hr.
    destruct Hr as [En [Hs1 Hs2]].
    pose proof (security_le_low_indirect _ _ Hs1 Ek) as E1.
    pose proof (security_le_low_indirect _ _ Hs2 Ek) as E2.
    rewrite E1, E2; repeat rewrite protect_value_low.
    subst n2; simpl; repeat split; auto using security_le_refl.
  - apply value_rel_high. exact Eout.
Qed.

Lemma expr_rel_if : forall k T r c1 c2 y1 y2 n1 n2,
  expr_rel (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) c1 c2 ->
  expr_rel T y1 y2 -> expr_rel T n1 n2 ->
  expr_rel (ty_protect k.(indirect_reader) T)
    (tm_if c1 y1 n1 r) (tm_if c2 y2 n2 r).
Proof.
  intros k T r c1 c2 y1 y2 n1 n2 Hc Hy Hn z1 z2 Hb1 Hb2.
  destruct ((security_of (ty_protect k.(indirect_reader) T)).(indirect_reader))
    eqn:Eout.
  - apply ty_protect_low_inv in Eout as [Ek ET].
    rewrite Ek in *; rewrite ty_protect_low.
    destruct (big_if_inv _ _ _ _ _ Hb1) as
      [[v1 [k1 [w1 [Hc1 [_ [Hb1' Ez1]]]]]]|
       [v1 [k1 [w1 [Hc1 [_ [Hb1' Ez1]]]]]]];
    destruct (big_if_inv _ _ _ _ _ Hb2) as
      [[v2 [k2 [w2 [Hc2 [_ [Hb2' Ez2]]]]]]|
       [v2 [k2 [w2 [Hc2 [_ [Hb2' Ez2]]]]]]];
    subst z1 z2;
    pose proof (Hc _ _ Hc1 Hc2) as Hcr;
    simpl in Hcr; rewrite Ek in Hcr; try contradiction;
    destruct Hcr as [Hs1 [Hs2 _]];
    pose proof (security_le_low_indirect _ _ Hs1 Ek) as E1;
    pose proof (security_le_low_indirect _ _ Hs2 Ek) as E2;
    rewrite E1, E2; repeat rewrite protect_value_low;
    [eapply Hy | eapply Hn]; eauto.
  - apply value_rel_high. exact Eout.
Qed.

Lemma expr_rel_nat_public : forall n,
  expr_rel (Ty_Nat public) (tm_nat n public) (tm_nat n public).
Proof.
  intros n v1 v2 Hb1 Hb2.
  pose proof (big_value_self _ _ (v_nat n public) Hb1) as E1.
  pose proof (big_value_self _ _ (v_nat n public) Hb2) as E2.
  subst v1 v2; simpl; repeat split; auto.
Qed.

Lemma expr_rel_natrec_unroll : forall n T r b1 b2 s1 s2,
  expr_rel T b1 b2 ->
  expr_rel (Ty_Arrow (Ty_Nat public)
    (Ty_Arrow T T public) public) s1 s2 ->
  expr_rel T (natrec_unroll n b1 s1 r) (natrec_unroll n b2 s2 r).
Proof.
  induction n; intros T r b1 b2 s1 s2 Hb Hs; simpl.
  - exact Hb.
  - assert (Hinner : expr_rel (Ty_Arrow T T public)
      (tm_app s1 (tm_nat n public) r)
      (tm_app s2 (tm_nat n public) r)).
    { change (expr_rel
        (ty_protect (indirect_reader public) (Ty_Arrow T T public))
        (tm_app s1 (tm_nat n public) r)
        (tm_app s2 (tm_nat n public) r)).
      eapply expr_rel_app; eauto using expr_rel_nat_public.
      destruct r; simpl; auto. }
    replace T with (ty_protect Low T) by apply ty_protect_low.
    eapply (expr_rel_app T T public r
      (tm_app s1 (tm_nat n public) r)
      (tm_app s2 (tm_nat n public) r)
      (natrec_unroll n b1 s1 r)
      (natrec_unroll n b2 s2 r)); eauto.
    destruct r; simpl; auto.
Qed.

Lemma expr_rel_natrec : forall k T r n1 n2 b1 b2 s1 s2,
  expr_rel (Ty_Nat k) n1 n2 ->
  expr_rel T b1 b2 ->
  expr_rel (Ty_Arrow (Ty_Nat public)
    (Ty_Arrow T T public) public) s1 s2 ->
  expr_rel (ty_protect k.(indirect_reader) T)
    (tm_natrec n1 b1 s1 r) (tm_natrec n2 b2 s2 r).
Proof.
  intros k T r n1 n2 b1 b2 s1 s2 Hn Hb Hs z1 z2 Hbig1 Hbig2.
  destruct ((security_of (ty_protect k.(indirect_reader) T)).(indirect_reader))
    eqn:Eout.
  - apply ty_protect_low_inv in Eout as [Ek ET].
    rewrite Ek in *; rewrite ty_protect_low.
    destruct (big_rec_inv _ _ _ _ _ Hbig1)
      as [m1 [k1 [v1 [w1 [u1 [Hn1 [Hb1 [Hs1 [_ [Hu1 Ez1]]]]]]]]]].
    destruct (big_rec_inv _ _ _ _ _ Hbig2)
      as [m2 [k2 [v2 [w2 [u2 [Hn2 [Hb2 [Hs2 [_ [Hu2 Ez2]]]]]]]]]].
    subst z1 z2.
    pose proof (Hn _ _ Hn1 Hn2) as Hnr.
    simpl in Hnr; rewrite Ek in Hnr.
    destruct Hnr as [Em [Hk1 Hk2]].
    pose proof (security_le_low_indirect _ _ Hk1 Ek) as E1.
    pose proof (security_le_low_indirect _ _ Hk2 Ek) as E2.
    rewrite E1, E2; repeat rewrite protect_value_low.
    subst m2.
    eapply (expr_rel_natrec_unroll m1 T r v1 v2 w1 w2).
    + apply expr_rel_value; eauto using big_result_value.
    + apply expr_rel_value; eauto using big_result_value.
    + exact Hu1.
    + exact Hu2.
  - apply value_rel_high. exact Eout.
Qed.

Lemma expr_rel_case : forall A B T k r t1 t2 b11 b12 b21 b22,
  expr_rel (Ty_Sum A B k) t1 t2 ->
  (forall v1 v2, value v1 -> value v2 -> value_rel A v1 v2 ->
    expr_rel T (open b11 v1) (open b12 v2)) ->
  (forall v1 v2, value v1 -> value v2 -> value_rel B v1 v2 ->
    expr_rel T (open b21 v1) (open b22 v2)) ->
  expr_rel (ty_protect k.(indirect_reader) T)
    (tm_case t1 b11 b21 r) (tm_case t2 b12 b22 r).
Proof.
  intros A B T k r t1 t2 b11 b12 b21 b22 Ht HL HR z1 z2 Hb1 Hb2.
  destruct ((security_of (ty_protect k.(indirect_reader) T)).(indirect_reader))
    eqn:Eout.
  - apply ty_protect_low_inv in Eout as [Ek ET].
    rewrite Ek in *; rewrite ty_protect_low.
    destruct (big_case_inv _ _ _ _ _ Hb1) as
      [[v1 [k1 [w1 [Ht1 [_ [Hw1 Ez1]]]]]]|
       [v1 [k1 [w1 [Ht1 [_ [Hw1 Ez1]]]]]]];
    destruct (big_case_inv _ _ _ _ _ Hb2) as
      [[v2 [k2 [w2 [Ht2 [_ [Hw2 Ez2]]]]]]|
       [v2 [k2 [w2 [Ht2 [_ [Hw2 Ez2]]]]]]];
    subst z1 z2;
    pose proof (Ht _ _ Ht1 Ht2) as Htr;
    simpl in Htr; rewrite Ek in Htr; try contradiction;
    destruct Htr as [Hs1 [Hs2 Hpayload]];
    pose proof (security_le_low_indirect _ _ Hs1 Ek) as E1;
    pose proof (security_le_low_indirect _ _ Hs2 Ek) as E2;
    assert (Hv1 : value v1) by
      (pose proof (big_result_value _ _ Ht1) as Hv; inversion Hv; assumption);
    assert (Hv2 : value v2) by
      (pose proof (big_result_value _ _ Ht2) as Hv; inversion Hv; assumption);
    rewrite E1, E2; repeat rewrite protect_value_low;
    [eapply (HL v1 v2) | eapply (HR v1 v2)]; eauto.
  - apply value_rel_high. exact Eout.
Qed.

Lemma in_fold_max : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [E|H].
    + subst; lia.
    + specialize (IH x H); lia.
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (fold_right Nat.max 0 L)).
  intros H. pose proof (in_fold_max L _ H). lia.
Qed.

Lemma env_rel_put : forall Gamma rho1 rho2 x T v1 v2,
  env_rel Gamma rho1 rho2 ->
  value v1 -> value v2 -> value_rel T v1 v2 ->
  env_rel (update Gamma x T)
    (put rho1 x v1) (put rho2 x v2).
Proof.
  intros Gamma rho1 rho2 x T v1 v2 [Hlc Hrel]
    Hv1 Hv2 Hvr; split.
  - intros y. unfold put. destruct (Nat.eqb x y).
    + split; eauto using value_locally_closed.
    + apply Hlc.
  - intros y U Hlookup. unfold update in Hlookup.
    simpl in Hlookup. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E; subst y. inversion Hlookup; subst U.
      unfold put. rewrite Nat.eqb_refl.
      apply expr_rel_value; assumption.
    + apply Nat.eqb_neq in E. unfold put.
      destruct (Nat.eqb x y) eqn:F;
        [apply Nat.eqb_eq in F; subst; exfalso; apply E; reflexivity|].
      apply Hrel. exact Hlookup.
Qed.

Lemma close_put_fresh : forall t rho x v,
  ~ In x (fv t) -> close (put rho x v) t = close rho t.
Proof.
  intros t rho x v Hfresh. apply close_ext.
  intros y Hy. unfold put. destruct (Nat.eqb x y) eqn:E; auto.
  apply Nat.eqb_eq in E; subst; contradiction.
Qed.

Lemma close_put_open : forall body rho x v,
  ~ In x (fv body) ->
  (forall y, locally_closed (put rho x v y)) ->
  close (put rho x v) (open body (tm_fvar x)) =
    open (close rho body) v.
Proof.
  intros body rho x v Hfresh Hlc.
  rewrite close_open by exact Hlc.
  rewrite close_put_fresh by exact Hfresh.
  unfold put. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma expr_rel_unit : forall k,
  expr_rel (Ty_Unit k) (tm_unit k) (tm_unit k).
Proof.
  intros k v1 v2 Hb1 Hb2.
  pose proof (big_value_self _ _ (v_unit k) Hb1) as E1.
  pose proof (big_value_self _ _ (v_unit k) Hb2) as E2.
  subst v1 v2. destruct k as [r i]; destruct i; simpl; auto.
  repeat split; destruct r; simpl; auto.
Qed.

Lemma expr_rel_nat : forall n k,
  expr_rel (Ty_Nat k) (tm_nat n k) (tm_nat n k).
Proof.
  intros n k v1 v2 Hb1 Hb2.
  pose proof (big_value_self _ _ (v_nat n k) Hb1) as E1.
  pose proof (big_value_self _ _ (v_nat n k) Hb2) as E2.
  subst v1 v2. destruct k as [r i]; destruct i; simpl; auto.
  repeat split; destruct r; simpl; auto.
Qed.

Lemma expr_rel_abs : forall A B k body1 body2,
  (forall a1 a2, value a1 -> value a2 -> value_rel A a1 a2 ->
    expr_rel B (open body1 a1) (open body2 a2)) ->
  expr_rel (Ty_Arrow A B k)
    (tm_abs A body1 k) (tm_abs A body2 k).
Proof.
  intros A B [rr ir] body1 body2 Hbody z1 z2 Hb1 Hb2.
  destruct ir; [|exact I].
  inversion Hb1; subst; inversion Hb2; subst.
  pose proof (big_result_value _ _ Hb1) as Hvabs1.
  pose proof (big_result_value _ _ Hb2) as Hvabs2.
  simpl.
  assert (Hsec : security_le {| reader := rr; indirect_reader := Low |}
    {| reader := rr; indirect_reader := Low |})
    by apply security_le_refl.
  repeat split; try (destruct rr; simpl; auto).
  all: intros a1 a2 r Hva1 Hva2 Harg Hflow w1 w2 Happ1 Happ2;
    destruct (big_app_inv _ _ _ _ Happ1)
      as [A1 [b1 [k1 [v1 [u1 [Hf1 [Ha1 [_ [Hu1 Ew1]]]]]]]]];
    destruct (big_app_inv _ _ _ _ Happ2)
      as [A2 [b2 [k2 [v2 [u2 [Hf2 [Ha2 [_ [Hu2 Ew2]]]]]]]]];
    pose proof (big_value_self _ _ Hvabs1 Hf1) as Ef1;
    pose proof (big_value_self _ _ Hvabs2 Hf2) as Ef2;
    inversion Ef1; inversion Ef2; subst;
    pose proof (big_value_self _ _ Hva1 Ha1) as Ea1;
    pose proof (big_value_self _ _ Hva2 Ha2) as Ea2;
    subst v1 v2;
    simpl; repeat rewrite protect_value_low;
    exact (Hbody a1 a2 Hva1 Hva2 Harg u1 u2 Hu1 Hu2).
Qed.

Lemma rel_open_from_cofinite : forall L Gamma A B body rho1 rho2,
  env_rel Gamma rho1 rho2 ->
  (forall x, ~ In x L ->
    forall sigma1 sigma2,
      env_rel (update Gamma x A) sigma1 sigma2 ->
      expr_rel B
        (close sigma1 (open body (tm_fvar x)))
        (close sigma2 (open body (tm_fvar x)))) ->
  forall a1 a2,
    value a1 -> value a2 -> value_rel A a1 a2 ->
    expr_rel B (open (close rho1 body) a1) (open (close rho2 body) a2).
Proof.
  intros L Gamma A B body rho1 rho2 Henv Hco a1 a2 Hva1 Hva2 Harg.
  destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
  assert (HxL : ~ In x L).
  { intro Hx. apply Hfresh. apply in_or_app. left; exact Hx. }
  assert (HxBody : ~ In x (fv body)).
  { intro Hx. apply Hfresh. apply in_or_app. right; exact Hx. }
  pose proof (env_rel_put Gamma rho1 rho2 x A a1 a2
    Henv Hva1 Hva2 Harg) as Henv'.
  pose proof (Hco x HxL (put rho1 x a1) (put rho2 x a2) Henv')
    as Hr.
  assert (Hlc1 : forall y, locally_closed (put rho1 x a1 y)).
  { intro y. exact (proj1 ((proj1 Henv') y)). }
  assert (Hlc2 : forall y, locally_closed (put rho2 x a2 y)).
  { intro y. exact (proj2 ((proj1 Henv') y)). }
  rewrite (close_put_open body rho1 x a1 HxBody Hlc1) in Hr.
  rewrite (close_put_open body rho2 x a2 HxBody Hlc2) in Hr.
  exact Hr.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho1 rho2, env_rel Gamma rho1 rho2 ->
    expr_rel T (close rho1 t) (close rho2 t).
Proof.
  intros Gamma t T Hty; induction Hty; intros rho1 rho2 Henv; simpl.
  all: eauto using expr_rel_unit, expr_rel_nat, expr_rel_pair,
    expr_rel_inl, expr_rel_inr, expr_rel_protect, expr_rel_app,
    expr_rel_fst, expr_rel_snd, expr_rel_succ, expr_rel_natrec,
    expr_rel_if, expr_rel_subtype.
  - exact ((proj2 Henv) x T H).
  - eapply expr_rel_abs.
    intros a1 a2 Hva1 Hva2 Harg.
    destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
    assert (HxL : ~ In x L).
    { intro Hx. apply Hfresh. apply in_or_app. left; exact Hx. }
    assert (HxBody : ~ In x (fv body)).
    { intro Hx. apply Hfresh. apply in_or_app. right; exact Hx. }
    pose proof (env_rel_put Gamma rho1 rho2 x T1 a1 a2
      Henv Hva1 Hva2 Harg) as Henv'.
    pose proof (H2 x HxL (put rho1 x a1) (put rho2 x a2) Henv')
      as Hr.
    assert (Hlc1 : forall y, locally_closed (put rho1 x a1 y)).
    { intro y. exact (proj1 ((proj1 Henv') y)). }
    assert (Hlc2 : forall y, locally_closed (put rho2 x a2 y)).
    { intro y. exact (proj2 ((proj1 Henv') y)). }
    rewrite (close_put_open body rho1 x a1 HxBody Hlc1) in Hr.
    rewrite (close_put_open body rho2 x a2 HxBody Hlc2) in Hr.
    exact Hr.
  - eapply expr_rel_case; eauto.
    + eapply rel_open_from_cofinite; eauto.
    + eapply rel_open_from_cofinite; eauto.
Qed.

Lemma lc_at_open_fvar : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x H; simpl in *; try exact I.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + simpl in H; lia.
  - eapply IHt; eauto.
  - destruct H; split; [eapply IHt1 | eapply IHt2]; eauto.
  - destruct H; split; [eapply IHt1 | eapply IHt2]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct H as [? [? ?]]. repeat split;
      [eapply IHt1 | eapply IHt2 | eapply IHt3]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct H as [? [? ?]]. repeat split;
      [eapply IHt1 | eapply IHt2 | eapply IHt3]; eauto.
  - destruct H as [? [? ?]]. repeat split;
      [eapply IHt1 | eapply IHt2 | eapply IHt3]; eauto.
Qed.

Lemma has_type_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty; induction Hty; unfold locally_closed in *;
    simpl in *; eauto.
  - destruct (fresh_atom L) as [x Hx].
    specialize (H1 x Hx).
    unfold open in H1.
    eapply lc_at_open_fvar; eauto.
  - destruct (fresh_atom L) as [x Hx].
    specialize (H1 x Hx).
    specialize (H3 x Hx).
    unfold open in H1, H3.
    repeat split; eauto using lc_at_open_fvar.
Qed.

Lemma close_id : forall t,
  close (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; f_equal; auto.
Qed.

Lemma close_put_identity : forall t x u,
  close (put (fun y => tm_fvar y) x u) t = subst x u t.
Proof.
  induction t; intros x u; simpl; try (f_equal; auto); reflexivity.
Qed.

Lemma subst_fresh : forall t x u,
  ~ In x (fv t) -> subst x u t = t.
Proof.
  intros t x u H.
  rewrite <- close_put_identity, <- close_id.
  apply close_ext. intros y Hy.
  unfold put. destruct (Nat.eqb x y) eqn:E; auto.
  apply Nat.eqb_eq in E; subst; contradiction.
Qed.

Ltac derive_context_fresh :=
  match goal with
  | H : ~ In ?x ?xs |- ~ In ?x ?ys =>
      intro Hin; apply H; simpl in *;
      repeat rewrite in_app_iff in *; tauto
  end.

Lemma subst_plug : forall C x u,
  ~ In x (fv (plug C (tm_unit public))) ->
  subst x u (plug C (tm_fvar x)) = plug C u.
Proof.
  induction C; intros x u Hfresh; simpl in *; try reflexivity;
    try (rewrite Nat.eqb_refl; reflexivity);
    try (rewrite IHC by derive_context_fresh);
    repeat (rewrite subst_fresh by derive_context_fresh);
    reflexivity.
Qed.

Lemma value_rel_ground_erase : forall T k v1 v2,
  ground T -> transparent_at k T -> k.(indirect_reader) = Low ->
  value_rel T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  induction T; intros k v1 v2 Hg Htr Ek Hr.
  - destruct Htr as [Hsec _].
    pose proof (security_le_low_indirect _ _ Hsec Ek) as Es.
    simpl in Es, Hr; rewrite Es in Hr.
    destruct v1; destruct v2; simpl in Hr; try contradiction; reflexivity.
  - destruct Hg as [Hg1 Hg2].
    destruct Htr as [Hsec [Ht1 Ht2]].
    pose proof (security_le_low_indirect _ _ Hsec Ek) as Es.
    simpl in Es, Hr; rewrite Es in Hr.
    destruct v1; destruct v2; simpl in Hr; try contradiction;
      destruct Hr as [_ [_ Hchild]]; simpl; f_equal;
      [eapply IHT1 | eapply IHT2]; eauto.
  - destruct Hg as [Hg1 Hg2].
    destruct Htr as [Hsec [Ht1 Ht2]].
    pose proof (security_le_low_indirect _ _ Hsec Ek) as Es.
    simpl in Es, Hr; rewrite Es in Hr.
    destruct v1; destruct v2; simpl in Hr; try contradiction.
    destruct Hr as [_ [_ [Hleft Hright]]].
    simpl. f_equal.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - contradiction.
  - destruct Htr as [Hsec _].
    pose proof (security_le_low_indirect _ _ Hsec Ek) as Es.
    simpl in Es, Hr; rewrite Es in Hr.
    destruct v1; destruct v2; simpl in Hr; try contradiction.
    destruct Hr as [En _]. subst. reflexivity.
Qed.

Lemma env_rel_put_expr : forall Gamma rho1 rho2 x T t1 t2,
  env_rel Gamma rho1 rho2 ->
  locally_closed t1 -> locally_closed t2 -> expr_rel T t1 t2 ->
  env_rel (update Gamma x T)
    (put rho1 x t1) (put rho2 x t2).
Proof.
  intros Gamma rho1 rho2 x T t1 t2 [Hlc Hrel]
    Ht1 Ht2 Hr; split.
  - intros y. unfold put. destruct (Nat.eqb x y); auto.
  - intros y U Hlookup. unfold update in Hlookup.
    simpl in Hlookup. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E; subst y. inversion Hlookup; subst U.
      unfold put. rewrite Nat.eqb_refl. exact Hr.
    + apply Nat.eqb_neq in E. unfold put.
      destruct (Nat.eqb x y) eqn:F;
        [apply Nat.eqb_eq in F; subst; exfalso; apply E; reflexivity|].
      apply Hrel. exact Hlookup.
Qed.

Lemma env_rel_empty_id :
  env_rel empty (fun x => tm_fvar x) (fun x => tm_fvar x).
Proof.
  split.
  - intro x; split; unfold locally_closed; simpl; exact I.
  - intros x T H; discriminate H.
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
  intros C t1 t2 T_secret T_result Ht1 Ht2
    [L Hctx] Hg Htrans Hnon.
  assert (Es : (security_of T_secret).(indirect_reader) = High).
  { destruct ((security_of T_secret).(indirect_reader)) eqn:E; auto.
    destruct ((security_of T_result).(indirect_reader));
      simpl in Hnon; contradiction. }
  assert (Er : (security_of T_result).(indirect_reader) = Low).
  { destruct ((security_of T_result).(indirect_reader)) eqn:E; auto.
    destruct ((security_of T_secret).(indirect_reader));
      simpl in Hnon; contradiction. }
  destruct (fresh_atom
    (L ++ fv (plug C (tm_unit public)))) as [x Hfresh].
  assert (HxL : ~ In x L).
  { intro Hx. apply Hfresh. apply in_or_app. left; exact Hx. }
  assert (HxC : ~ In x (fv (plug C (tm_unit public)))).
  { intro Hx. apply Hfresh. apply in_or_app. right; exact Hx. }
  pose proof (Hctx x HxL) as Htyped.
  pose proof (has_type_lc _ _ _ Ht1) as Hlc1.
  pose proof (has_type_lc _ _ _ Ht2) as Hlc2.
  pose proof (expr_rel_high T_secret t1 t2 Es) as Hsecret.
  pose proof (env_rel_put_expr empty
    (fun y => tm_fvar y) (fun y => tm_fvar y)
    x T_secret t1 t2 env_rel_empty_id Hlc1 Hlc2 Hsecret)
    as Henv.
  pose proof (fundamental _ _ _ Htyped
    (put (fun y => tm_fvar y) x t1)
    (put (fun y => tm_fvar y) x t2) Henv) as Hr.
  repeat rewrite close_put_identity in Hr.
  rewrite (subst_plug C x t1 HxC) in Hr.
  rewrite (subst_plug C x t2 HxC) in Hr.
  unfold same_result.
  intros v1 v2 He1 He2.
  eapply (value_rel_ground_erase T_result (security_of T_result));
    eauto.
  eapply Hr; apply evaluates_big; assumption.
Qed.
