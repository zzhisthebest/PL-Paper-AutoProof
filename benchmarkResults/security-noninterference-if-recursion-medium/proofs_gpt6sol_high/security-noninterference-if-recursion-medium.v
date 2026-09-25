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

Definition expression_lifting (R : tm -> tm -> Prop) (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm, evaluates t1 v1 -> evaluates t2 v2 -> R v1 v2.

Definition underlying_typed (T : ty) (t : tm) : Prop :=
  has_type empty (erase_security t) (erase_type T).

Fixpoint value_relation (observer : label) (T : ty) (v1 v2 : tm) : Prop :=
  value v1 /\ value v2 /\
  underlying_typed T v1 /\ underlying_typed T v2 /\
  (flows_to (security_of T).(indirect_reader) observer ->
    match T with
    | Ty_Unit _ =>
        exists kappa1 kappa2 : security,
          v1 = tm_unit kappa1 /\ v2 = tm_unit kappa2
    | Ty_Sum T1 T2 _ =>
        (exists (u1 u2 : tm) (kappa1 kappa2 : security),
          v1 = tm_inl u1 kappa1 /\ v2 = tm_inl u2 kappa2 /\
          value_relation observer T1 u1 u2) \/
        (exists (u1 u2 : tm) (kappa1 kappa2 : security),
          v1 = tm_inr u1 kappa1 /\ v2 = tm_inr u2 kappa2 /\
          value_relation observer T2 u1 u2)
    | Ty_Prod T1 T2 _ =>
        exists (a1 b1 a2 b2 : tm) (kappa1 kappa2 : security),
          v1 = tm_pair a1 b1 kappa1 /\ v2 = tm_pair a2 b2 kappa2 /\
          value_relation observer T1 a1 a2 /\
          value_relation observer T2 b1 b2
    | Ty_Arrow T1 T2 _ =>
        exists (U1 U2 : ty) (body1 body2 : tm) (kappa1 kappa2 : security),
          v1 = tm_abs U1 body1 kappa1 /\ v2 = tm_abs U2 body2 kappa2 /\
          forall arg1 arg2 : tm,
            value_relation observer T1 arg1 arg2 ->
            expression_lifting (value_relation observer T2)
              (tm_app v1 arg1 High) (tm_app v2 arg2 High)
    | Ty_Nat _ => exists n k1 k2, v1 = tm_nat n k1 /\ v2 = tm_nat n k2
    end).

Definition expression_relation (observer : label) (T : ty) (t1 t2 : tm) : Prop :=
  underlying_typed T t1 /\ underlying_typed T t2 /\
  expression_lifting (value_relation observer T) t1 t2.

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

Lemma erase_type_protect : forall l T,
  erase_type (ty_protect l T) = erase_type T.
Proof. intros l [] ; reflexivity. Qed.

Lemma erase_type_public_protect : forall T,
  ty_protect Low (erase_type T) = erase_type T.
Proof. intros []; reflexivity. Qed.

Lemma erase_type_wf : forall T, wf_ty (erase_type T).
Proof.
  induction T; simpl; try exact I; repeat split; auto.
Qed.

Lemma erase_security_open_rec : forall k u t,
  erase_security (open_rec k u t) =
  open_rec k (erase_security u) (erase_security t).
Proof.
  intros k u t; revert k.
  induction t; intros k; simpl; try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity).
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma erase_security_open : forall body u,
  erase_security (open body u) =
  open (erase_security body) (erase_security u).
Proof. intros; apply erase_security_open_rec. Qed.

Fixpoint erase_context (Gamma : context) : context :=
  match Gamma with
  | [] => []
  | (x,T) :: rest => (x, erase_type T) :: erase_context rest
  end.

Lemma erase_lookup : forall Gamma x T,
  lookup_context x Gamma = Some T ->
  lookup_context x (erase_context Gamma) = Some (erase_type T).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E; [inversion H; subst; reflexivity|].
    apply IH in H. exact H.
Qed.

Lemma erase_context_update : forall Gamma x T,
  erase_context (update Gamma x T) =
  update (erase_context Gamma) x (erase_type T).
Proof. reflexivity. Qed.

Lemma erase_subtype : forall T U,
  subtype T U -> erase_type T = erase_type U.
Proof.
  intros T U H; induction H; simpl; try congruence.
Qed.

Lemma erase_typing : forall Gamma t T,
  has_type Gamma t T ->
  has_type (erase_context Gamma) (erase_security t) (erase_type T).
Proof.
  intros Gamma t T H; induction H; simpl in *.
  - apply T_Var. apply erase_lookup; assumption. apply erase_type_wf.
  - apply T_Unit. exact I.
  - eapply T_Abs with (L := L); try apply erase_type_wf; try exact I.
    intros x Hfresh. specialize (H2 x Hfresh).
    rewrite erase_security_open in H2. simpl in H2. exact H2.
  - rewrite erase_type_protect. rewrite <- erase_type_public_protect.
    eapply T_App with
      (T1 := erase_type T1) (kappa := public); eauto; simpl; trivial.
  - eapply T_Pair; eauto. exact I.
  - rewrite erase_type_protect. rewrite <- erase_type_public_protect.
    eapply T_Fst with
      (T2 := erase_type T2) (kappa := public); eauto; simpl; trivial.
  - rewrite erase_type_protect. rewrite <- erase_type_public_protect.
    eapply T_Snd with
      (T1 := erase_type T1) (kappa := public); eauto; simpl; trivial.
  - eapply T_Inl; eauto using erase_type_wf. exact I.
  - eapply T_Inr; eauto using erase_type_wf. exact I.
  - rewrite erase_type_protect. rewrite <- erase_type_public_protect.
    eapply T_Case with (L := L) (T1 := erase_type T1)
      (T2 := erase_type T2) (kappa := public); eauto; simpl; trivial.
    + intros x Hfresh. specialize (H2 x Hfresh).
      rewrite erase_security_open in H2. simpl in H2. exact H2.
    + intros x Hfresh. specialize (H4 x Hfresh).
      rewrite erase_security_open in H4. simpl in H4. exact H4.
  - rewrite erase_type_protect. assumption.
  - rewrite (erase_subtype _ _ H0) in IHhas_type. exact IHhas_type.
  - apply T_Nat. exact I.
  - change (Ty_Nat public) with (ty_protect Low (Ty_Nat public)).
    eapply T_Succ with (k := public); eauto; simpl; trivial.
  - rewrite erase_type_protect. rewrite <- erase_type_public_protect.
    eapply T_NatRec with
      (k := public) (T := erase_type T); eauto; simpl; trivial.
  - rewrite erase_type_protect. rewrite <- erase_type_public_protect.
    eapply T_If with
      (k := public) (T := erase_type T); eauto; simpl; trivial.
Qed.

Lemma flows_trans : forall a b c,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. intros [] [] []; simpl; intuition. Qed.

Lemma ground_transparent_relation_erases : forall T k v1 v2,
  ground T -> transparent_at k T ->
  flows_to k.(indirect_reader) Low ->
  value_relation Low T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  induction T; intros k v1 v2 Hg Htr Hlow Hr;
    destruct k as [kr ki]; simpl in *;
    destruct Htr as [[_ Hsec] Hchildren];
    destruct Hr as [_ [_ [_ [_ Hshape]]]];
    specialize (Hshape (flows_trans _ _ _ Hsec Hlow)).
  - destruct Hshape as [k1 [k2 [-> ->]]]. reflexivity.
  - destruct Hg as [Hg1 Hg2].
    destruct Hchildren as [Htr1 Htr2].
    destruct Hshape as [[u1 [u2 [k1 [k2 [-> [-> Hu]]]]]] |
                        [u1 [u2 [k1 [k2 [-> [-> Hu]]]]]]]; simpl;
      f_equal; eauto.
  - destruct Hg as [Hg1 Hg2].
    destruct Hchildren as [Htr1 Htr2].
    destruct Hshape as (a1 & b1 & a2 & b2 & k1 & k2 & -> & -> & Ha & Hb); simpl.
    f_equal; eauto.
  - contradiction.
  - destruct Hshape as [n [k1 [k2 [-> ->]]]]. reflexivity.
Qed.

Lemma expression_relation_noninterference : forall T t1 t2,
  ground T -> transparent T ->
  flows_to (security_of T).(indirect_reader) Low ->
  expression_relation Low T t1 t2 -> same_result t1 t2.
Proof.
  intros T t1 t2 Hg Htr Hlow [_ [_ Hrel]] v1 v2 He1 He2.
  eapply ground_transparent_relation_erases; eauto.
Qed.

Inductive big_evaluates : tm -> tm -> Prop :=
  | BE_Value : forall v, value v -> big_evaluates v v
  | BE_App : forall f a T body k va out r,
      big_evaluates f (tm_abs T body k) ->
      big_evaluates a va ->
      flows_to k.(reader) r ->
      big_evaluates (open body va) out ->
      big_evaluates (tm_app f a r) (protect_value out k.(indirect_reader))
  | BE_Pair : forall a b va vb k,
      big_evaluates a va -> big_evaluates b vb ->
      big_evaluates (tm_pair a b k) (tm_pair va vb k)
  | BE_Fst : forall t a b k r,
      big_evaluates t (tm_pair a b k) -> flows_to k.(reader) r ->
      big_evaluates (tm_fst t r) (protect_value a k.(indirect_reader))
  | BE_Snd : forall t a b k r,
      big_evaluates t (tm_pair a b k) -> flows_to k.(reader) r ->
      big_evaluates (tm_snd t r) (protect_value b k.(indirect_reader))
  | BE_Inl : forall t v k,
      big_evaluates t v -> big_evaluates (tm_inl t k) (tm_inl v k)
  | BE_Inr : forall t v k,
      big_evaluates t v -> big_evaluates (tm_inr t k) (tm_inr v k)
  | BE_CaseLeft : forall t b1 b2 a k out r,
      big_evaluates t (tm_inl a k) -> flows_to k.(reader) r ->
      big_evaluates (open b1 a) out ->
      big_evaluates (tm_case t b1 b2 r) (protect_value out k.(indirect_reader))
  | BE_CaseRight : forall t b1 b2 a k out r,
      big_evaluates t (tm_inr a k) -> flows_to k.(reader) r ->
      big_evaluates (open b2 a) out ->
      big_evaluates (tm_case t b1 b2 r) (protect_value out k.(indirect_reader))
  | BE_Protect : forall l t v,
      big_evaluates t v ->
      big_evaluates (tm_protect l t) (protect_value v l)
  | BE_Succ : forall t n k r,
      big_evaluates t (tm_nat n k) -> flows_to k.(reader) r ->
      big_evaluates (tm_succ t r)
        (protect_value (tm_nat (S n) public) k.(indirect_reader))
  | BE_NatRec : forall t b s n k vb vs out r,
      big_evaluates t (tm_nat n k) -> big_evaluates b vb ->
      big_evaluates s vs -> flows_to k.(reader) r ->
      big_evaluates (natrec_unroll n vb vs r) out ->
      big_evaluates (tm_natrec t b s r)
        (protect_value out k.(indirect_reader))
  | BE_IfTrue : forall c y n a k out r,
      big_evaluates c (tm_inl a k) -> flows_to k.(reader) r ->
      big_evaluates y out ->
      big_evaluates (tm_if c y n r) (protect_value out k.(indirect_reader))
  | BE_IfFalse : forall c y n a k out r,
      big_evaluates c (tm_inr a k) -> flows_to k.(reader) r ->
      big_evaluates n out ->
      big_evaluates (tm_if c y n r) (protect_value out k.(indirect_reader)).

Lemma protect_value_is_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l Hv; inversion Hv; subst; simpl; eauto using value.
Qed.

Lemma big_evaluates_value : forall t v, big_evaluates t v -> value v.
Proof.
  intros t v H; induction H; eauto using value, protect_value_is_value.
  all: inversion IHbig_evaluates; subst; eauto using protect_value_is_value.
Qed.

Lemma big_evaluates_value_inv : forall v out,
  value v -> big_evaluates v out -> out = v.
Proof.
  intros v out Hv; revert out.
  induction Hv; intros out He; inversion He; subst; eauto;
    try match goal with H : big_evaluates _ _ |- _ =>
      specialize (IHHv _ H); subst; reflexivity end.
  all: try match goal with
    H1 : big_evaluates ?a _, H2 : big_evaluates ?b _ |- _ =>
      specialize (IHHv1 _ H1); specialize (IHHv2 _ H2);
      subst; reflexivity end.
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

Lemma big_evaluates_step_back : forall t t' v,
  t --> t' -> big_evaluates t' v -> big_evaluates t v.
Proof.
  intros t t' v Hstep; revert v.
  induction Hstep; intros z He;
    try solve [
      match goal with
      | Hv : value ?w,
        Heval : big_evaluates (protect_value ?w ?ell) ?out
        |- big_evaluates (tm_protect ?ell ?w) ?out =>
          pose proof (protect_value_is_value w ell Hv) as Hpv;
          pose proof (big_evaluates_value_inv _ _ Hpv Heval) as Heq;
          subst out; apply BE_Protect; apply BE_Value; exact Hv
      end];
    try (inversion He; subst; try impossible_value;
         eauto 10 using big_evaluates, big_evaluates_value);
    try (inversion He; subst; try impossible_value;
         match goal with H : value (tm_pair _ _ _) |- _ => inversion H; subst end;
         eauto 10 using big_evaluates, big_evaluates_value);
    try (inversion He; subst; try impossible_value;
         match goal with H : value (tm_inl _ _) |- _ => inversion H; subst end;
         eauto 10 using big_evaluates, big_evaluates_value);
    try (inversion He; subst; try impossible_value;
         match goal with H : value (tm_inr _ _) |- _ => inversion H; subst end;
         eauto 10 using big_evaluates, big_evaluates_value).
  - pose proof (big_evaluates_value_inv _ _ (v_nat _ _) H3) as ->.
    eapply BE_Succ; [apply BE_Value; constructor | exact H].
  - eapply BE_NatRec; [apply BE_Value; constructor |
      apply BE_Value; exact H | apply BE_Value; exact H0 |
      exact H1 | exact H5].
Qed.

Lemma evaluates_big : forall t v,
  evaluates t v -> big_evaluates t v.
Proof.
  intros t v [Hm Hv]; induction Hm.
  - apply BE_Value; exact Hv.
  - eapply big_evaluates_step_back; eauto.
Qed.

Lemma multi_trans : forall a b c,
  a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c Hab Hbc; induction Hab; eauto using multi.
Qed.

Lemma multi_lift : forall (F : tm -> tm),
  (forall a b, a --> b -> F a --> F b) ->
  forall a b, a -->* b -> F a -->* F b.
Proof.
  intros F HF a b H; induction H; eauto using multi.
Qed.

Lemma multi_one : forall a b, a --> b -> a -->* b.
Proof. intros; eauto using multi. Qed.

Lemma big_evaluates_multi : forall t v,
  big_evaluates t v -> t -->* v.
Proof.
  intros t v H; induction H.
  - constructor.
  - eapply multi_trans.
    { eapply multi_lift with (F := fun x => tm_app x a r);
        [intros; apply ST_App1; assumption | exact IHbig_evaluates1]. }
    eapply multi_trans.
    { eapply multi_lift with (F := fun x => tm_app (tm_abs T body k) x r);
        [intros; apply ST_App2; eauto using big_evaluates_value |
         exact IHbig_evaluates2]. }
    eapply multi_trans.
    { apply multi_one. apply ST_AppAbs; eauto using big_evaluates_value. }
    eapply multi_trans.
    { eapply multi_lift with
        (F := fun x => tm_protect (indirect_reader k) x);
        [intros; apply ST_Protect; assumption | exact IHbig_evaluates3]. }
    apply multi_one. apply ST_ProtectValue.
    eauto using big_evaluates_value.
  - eapply multi_trans.
    { eapply multi_lift with (F := fun x => tm_pair x b k);
        [intros; apply ST_Pair1; assumption | exact IHbig_evaluates1]. }
    eapply multi_lift with (F := fun x => tm_pair va x k);
      [intros; apply ST_Pair2; eauto using big_evaluates_value |
       exact IHbig_evaluates2].
  - eapply multi_trans.
    { eapply multi_lift with (F := fun x => tm_fst x r);
        [intros; apply ST_Fst; assumption | exact IHbig_evaluates]. }
    eapply multi_trans.
    { apply multi_one. apply ST_FstPair.
      - pose proof (big_evaluates_value _ _ H) as Hv.
        inversion Hv; assumption.
      - pose proof (big_evaluates_value _ _ H) as Hv.
        inversion Hv; assumption.
      - assumption. }
    apply multi_one. apply ST_ProtectValue.
    pose proof (big_evaluates_value _ _ H) as Hv.
    inversion Hv; assumption.
  - eapply multi_trans.
    { eapply multi_lift with (F := fun x => tm_snd x r);
        [intros; apply ST_Snd; assumption | exact IHbig_evaluates]. }
    eapply multi_trans.
    { apply multi_one. apply ST_SndPair.
      - pose proof (big_evaluates_value _ _ H) as Hv.
        inversion Hv; assumption.
      - pose proof (big_evaluates_value _ _ H) as Hv.
        inversion Hv; assumption.
      - assumption. }
    apply multi_one. apply ST_ProtectValue.
    pose proof (big_evaluates_value _ _ H) as Hv.
    inversion Hv; assumption.
  - eapply multi_lift with (F := fun x => tm_inl x k);
      [intros; apply ST_Inl; assumption | exact IHbig_evaluates].
  - eapply multi_lift with (F := fun x => tm_inr x k);
      [intros; apply ST_Inr; assumption | exact IHbig_evaluates].
  - eapply multi_trans.
    { eapply multi_lift with (F := fun x => tm_case x b1 b2 r);
        [intros; apply ST_Case; assumption | exact IHbig_evaluates1]. }
    eapply multi_trans.
    { apply multi_one. apply ST_CaseLeft.
      - pose proof (big_evaluates_value _ _ H) as Hv.
        inversion Hv; assumption.
      - assumption. }
    eapply multi_trans.
    { eapply multi_lift with
        (F := fun x => tm_protect (indirect_reader k) x);
        [intros; apply ST_Protect; assumption | exact IHbig_evaluates2]. }
    apply multi_one. apply ST_ProtectValue.
    eauto using big_evaluates_value.
  - eapply multi_trans.
    { eapply multi_lift with (F := fun x => tm_case x b1 b2 r);
        [intros; apply ST_Case; assumption | exact IHbig_evaluates1]. }
    eapply multi_trans.
    { apply multi_one. apply ST_CaseRight.
      - pose proof (big_evaluates_value _ _ H) as Hv.
        inversion Hv; assumption.
      - assumption. }
    eapply multi_trans.
    { eapply multi_lift with
        (F := fun x => tm_protect (indirect_reader k) x);
        [intros; apply ST_Protect; assumption | exact IHbig_evaluates2]. }
    apply multi_one. apply ST_ProtectValue.
    eauto using big_evaluates_value.
  - eapply multi_trans.
    { eapply multi_lift with (F := fun x => tm_protect l x);
        [intros; apply ST_Protect; assumption | exact IHbig_evaluates]. }
    apply multi_one. apply ST_ProtectValue.
    eauto using big_evaluates_value.
  - eapply multi_trans.
    { eapply multi_lift with (F := fun x => tm_succ x r);
        [intros; apply ST_Succ; assumption | exact IHbig_evaluates]. }
    eapply multi_trans.
    { apply multi_one. apply ST_SuccNat. assumption. }
    apply multi_one. apply ST_ProtectValue. constructor.
  - eapply multi_trans.
    { eapply multi_lift with (F := fun x => tm_natrec x b s r);
        [intros; apply ST_RecArg; assumption | exact IHbig_evaluates1]. }
    eapply multi_trans.
    { eapply multi_lift with
        (F := fun x => tm_natrec (tm_nat n k) x s r);
        [intros; apply ST_RecBase; assumption | exact IHbig_evaluates2]. }
    eapply multi_trans.
    { eapply multi_lift with
        (F := fun x => tm_natrec (tm_nat n k) vb x r);
        [intros; apply ST_RecStep; eauto using big_evaluates_value |
         exact IHbig_evaluates3]. }
    eapply multi_trans.
    { apply multi_one. apply ST_RecUnroll;
        eauto using big_evaluates_value. }
    eapply multi_trans.
    { eapply multi_lift with
        (F := fun x => tm_protect (indirect_reader k) x);
        [intros; apply ST_Protect; assumption | exact IHbig_evaluates4]. }
    apply multi_one. apply ST_ProtectValue.
    eauto using big_evaluates_value.
  - eapply multi_trans.
    { eapply multi_lift with (F := fun x => tm_if x y n r);
        [intros; apply ST_If; assumption | exact IHbig_evaluates1]. }
    eapply multi_trans.
    { apply multi_one. apply ST_IfTrue.
      - pose proof (big_evaluates_value _ _ H) as Hv.
        inversion Hv; assumption.
      - assumption. }
    eapply multi_trans.
    { eapply multi_lift with
        (F := fun x => tm_protect (indirect_reader k) x);
        [intros; apply ST_Protect; assumption | exact IHbig_evaluates2]. }
    apply multi_one. apply ST_ProtectValue.
    eauto using big_evaluates_value.
  - eapply multi_trans.
    { eapply multi_lift with (F := fun x => tm_if x y n r);
        [intros; apply ST_If; assumption | exact IHbig_evaluates1]. }
    eapply multi_trans.
    { apply multi_one. apply ST_IfFalse.
      - pose proof (big_evaluates_value _ _ H) as Hv.
        inversion Hv; assumption.
      - assumption. }
    eapply multi_trans.
    { eapply multi_lift with
        (F := fun x => tm_protect (indirect_reader k) x);
        [intros; apply ST_Protect; assumption | exact IHbig_evaluates2]. }
    apply multi_one. apply ST_ProtectValue.
    eauto using big_evaluates_value.
Qed.

Lemma hidden_values_related : forall observer T v1 v2,
  ~ flows_to (security_of T).(indirect_reader) observer ->
  value v1 -> value v2 ->
  underlying_typed T v1 -> underlying_typed T v2 ->
  value_relation observer T v1 v2.
Proof.
  intros observer T v1 v2 Hhidden Hv1 Hv2 Ht1 Ht2.
  destruct T; simpl in *; repeat split; try assumption;
    intros Hflow; contradiction.
Qed.

Lemma nonflow_to_low : forall a b,
  ~ flows_to a b -> a = High /\ b = Low.
Proof. intros [] [] H; simpl in H; tauto. Qed.

Lemma big_evaluates_evaluates : forall t v,
  big_evaluates t v -> evaluates t v.
Proof.
  intros t v H; split.
  - apply big_evaluates_multi; exact H.
  - apply big_evaluates_value with (t := t); exact H.
Qed.

Lemma erase_protect_value : forall v l,
  erase_security (protect_value v l) = erase_security v.
Proof. intros [] []; reflexivity. Qed.

Lemma value_relation_values : forall observer T v1 v2,
  value_relation observer T v1 v2 -> value v1 /\ value v2.
Proof. intros observer [] v1 v2 H; exact (conj (proj1 H) (proj1 (proj2 H))). Qed.

Lemma value_relation_underlying : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  underlying_typed T v1 /\ underlying_typed T v2.
Proof.
  intros observer [] v1 v2 H; simpl in H; tauto.
Qed.

Lemma value_locally_closed : forall v,
  value v -> locally_closed v.
Proof.
  intros v Hv; induction Hv; unfold locally_closed in *; simpl in *; tauto.
Qed.

Lemma open_rec_avoid : forall t j k u,
  lc_at j t -> j <= k -> open_rec k u t = t.
Proof.
  intros t; induction t; intros j k u Hlc Hjk; simpl in *.
  all: try (destruct (Nat.eqb k n) eqn:E;
            [apply Nat.eqb_eq in E; lia|reflexivity]).
  all: try (repeat match goal with H : _ /\ _ |- _ => destruct H end;
            f_equal; eauto using le_n_S).
  all: reflexivity.
Qed.

Definition env_set (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

Fixpoint close_env (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit k => tm_unit k
  | tm_abs T body k => tm_abs T (close_env rho body) k
  | tm_app a b r => tm_app (close_env rho a) (close_env rho b) r
  | tm_pair a b k => tm_pair (close_env rho a) (close_env rho b) k
  | tm_fst a r => tm_fst (close_env rho a) r
  | tm_snd a r => tm_snd (close_env rho a) r
  | tm_inl a k => tm_inl (close_env rho a) k
  | tm_inr a k => tm_inr (close_env rho a) k
  | tm_case a b c r =>
      tm_case (close_env rho a) (close_env rho b) (close_env rho c) r
  | tm_protect l a => tm_protect l (close_env rho a)
  | tm_nat n k => tm_nat n k
  | tm_succ a r => tm_succ (close_env rho a) r
  | tm_natrec a b c r =>
      tm_natrec (close_env rho a) (close_env rho b) (close_env rho c) r
  | tm_if a b c r =>
      tm_if (close_env rho a) (close_env rho b) (close_env rho c) r
  end.

Lemma close_env_open_rec : forall rho t k u,
  (forall x, locally_closed (rho x)) ->
  close_env rho (open_rec k u t) =
  open_rec k (close_env rho u) (close_env rho t).
Proof.
  intros rho t; induction t; intros k u Hlc; simpl;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; auto; reflexivity).
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_avoid with (j := 0).
    + exact (Hlc a).
    + lia.
Qed.

Lemma close_env_ext : forall rho1 rho2 t,
  (forall x, In x (fv t) -> rho1 x = rho2 x) ->
  close_env rho1 t = close_env rho2 t.
Proof.
  intros rho1 rho2 t; induction t; intros Heq; simpl in *;
    try reflexivity;
    try (f_equal;
         first [apply IHt | apply IHt1 | apply IHt2 | apply IHt3];
         intros x Hx; apply Heq; simpl;
         repeat rewrite in_app_iff; tauto).
  apply Heq. simpl; auto.
Qed.

Lemma close_env_set_fresh : forall rho x v t,
  ~ In x (fv t) -> close_env (env_set rho x v) t = close_env rho t.
Proof.
  intros rho x v t Hfresh; apply close_env_ext.
  intros y Hy; unfold env_set.
  destruct (Nat.eqb x y) eqn:E; auto.
  apply Nat.eqb_eq in E; subst; contradiction.
Qed.

Lemma close_env_open_fresh : forall rho x v body,
  (forall y, locally_closed (rho y)) ->
  locally_closed v -> ~ In x (fv body) ->
  close_env (env_set rho x v) (open body (tm_fvar x)) =
  open (close_env rho body) v.
Proof.
  intros rho x v body Hr Hv Hfresh.
  unfold open.
  rewrite (close_env_open_rec (env_set rho x v) body 0 (tm_fvar x)).
  - simpl. rewrite close_env_set_fresh by exact Hfresh.
    unfold env_set. rewrite Nat.eqb_refl. reflexivity.
  - intros y; unfold env_set.
    destruct (Nat.eqb x y); auto.
Qed.

Definition environments_related (observer : label) (Gamma : context)
    (rho1 rho2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation observer T (rho1 x) (rho2 x).

Lemma environments_related_update : forall observer Gamma rho1 rho2 x T v1 v2,
  environments_related observer Gamma rho1 rho2 ->
  value_relation observer T v1 v2 ->
  environments_related observer (update Gamma x T)
    (env_set rho1 x v1) (env_set rho2 x v2).
Proof.
  intros observer Gamma rho1 rho2 x T v1 v2 Henv Hv y U Hlookup.
  unfold update in Hlookup; simpl in Hlookup.
  unfold env_set.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E; subst.
    rewrite Nat.eqb_refl. inversion Hlookup; subst; exact Hv.
  - assert (Nat.eqb x y = false) as E' by
        (rewrite Nat.eqb_sym; exact E).
    rewrite E'. eapply Henv; eassumption.
Qed.

Lemma fundamental_variable : forall observer Gamma rho1 rho2 x T,
  lookup_context x Gamma = Some T ->
  environments_related observer Gamma rho1 rho2 ->
  expression_relation observer T (close_env rho1 (tm_fvar x))
    (close_env rho2 (tm_fvar x)).
Proof.
  intros observer Gamma rho1 rho2 x T Hlookup Henv.
  simpl. pose proof (Henv x T Hlookup) as Hr.
  destruct (value_relation_underlying _ _ _ _ Hr) as [Ht1 Ht2].
  repeat split; auto.
  intros v1 v2 He1 He2.
  pose proof (value_relation_values _ _ _ _ Hr) as [Hv1 Hv2].
  apply evaluates_big in He1. apply evaluates_big in He2.
  pose proof (big_evaluates_value_inv _ _ Hv1 He1) as ->.
  pose proof (big_evaluates_value_inv _ _ Hv2 He2) as ->.
  exact Hr.
Qed.

Lemma big_pair_inv : forall a b k v,
  big_evaluates (tm_pair a b k) v ->
  exists va vb, v = tm_pair va vb k /\
    big_evaluates a va /\ big_evaluates b vb.
Proof.
  intros a b k v He; inversion He; subst.
  - match goal with H : value (tm_pair _ _ _) |- _ => inversion H; subst end.
    exists a, b. repeat split; try reflexivity; apply BE_Value; assumption.
  - eauto.
Qed.

Lemma big_inl_inv : forall a k v,
  big_evaluates (tm_inl a k) v ->
  exists va, v = tm_inl va k /\ big_evaluates a va.
Proof.
  intros a k v He; inversion He; subst.
  - match goal with H : value (tm_inl _ _) |- _ => inversion H; subst end.
    exists a. split; [reflexivity|apply BE_Value; assumption].
  - eauto.
Qed.

Lemma big_inr_inv : forall a k v,
  big_evaluates (tm_inr a k) v ->
  exists va, v = tm_inr va k /\ big_evaluates a va.
Proof.
  intros a k v He; inversion He; subst.
  - match goal with H : value (tm_inr _ _) |- _ => inversion H; subst end.
    exists a. split; [reflexivity|apply BE_Value; assumption].
  - eauto.
Qed.

Lemma expression_relation_pair : forall observer T1 T2 k a1 a2 b1 b2,
  expression_relation observer T1 a1 a2 ->
  expression_relation observer T2 b1 b2 ->
  expression_relation observer (Ty_Prod T1 T2 k)
    (tm_pair a1 b1 k) (tm_pair a2 b2 k).
Proof.
  intros observer T1 T2 k a1 a2 b1 b2
    [Ha1 [Ha2 Hra]] [Hb1 [Hb2 Hrb]].
  unfold expression_relation, underlying_typed in *.
  simpl. split.
  - eapply T_Pair; eauto. exact I.
  - split.
    + eapply T_Pair; eauto. exact I.
    + intros w1 w2 He1 He2.
    apply evaluates_big in He1. apply evaluates_big in He2.
    destruct (big_pair_inv _ _ _ _ He1) as (va1 & vb1 & -> & Hva1 & Hvb1).
    destruct (big_pair_inv _ _ _ _ He2) as (va2 & vb2 & -> & Hva2 & Hvb2).
    pose proof (Hra _ _ (big_evaluates_evaluates _ _ Hva1)
      (big_evaluates_evaluates _ _ Hva2)) as Hra'.
    pose proof (Hrb _ _ (big_evaluates_evaluates _ _ Hvb1)
      (big_evaluates_evaluates _ _ Hvb2)) as Hrb'.
    destruct (value_relation_values _ _ _ _ Hra') as [Hva1' Hva2'].
    destruct (value_relation_values _ _ _ _ Hrb') as [Hvb1' Hvb2'].
    destruct (value_relation_underlying _ _ _ _ Hra') as [Hta1 Hta2].
    destruct (value_relation_underlying _ _ _ _ Hrb') as [Htb1 Htb2].
      simpl. repeat split; try (constructor; assumption);
        try (eapply T_Pair; eauto; exact I).
      intros _. exists va1, vb1, va2, vb2, k, k.
      repeat split; assumption.
Qed.

Lemma expression_relation_inl : forall observer T1 T2 k a1 a2,
  expression_relation observer T1 a1 a2 ->
  expression_relation observer (Ty_Sum T1 T2 k)
    (tm_inl a1 k) (tm_inl a2 k).
Proof.
  intros observer T1 T2 k a1 a2 [Ha1 [Ha2 Hr]].
  unfold expression_relation, underlying_typed in *; simpl.
  split.
  - eapply T_Inl; eauto using erase_type_wf. exact I.
  - split.
    + eapply T_Inl; eauto using erase_type_wf. exact I.
    + intros w1 w2 He1 He2.
      apply evaluates_big in He1. apply evaluates_big in He2.
      destruct (big_inl_inv _ _ _ He1) as (va1 & -> & Hva1).
      destruct (big_inl_inv _ _ _ He2) as (va2 & -> & Hva2).
      pose proof (Hr _ _ (big_evaluates_evaluates _ _ Hva1)
        (big_evaluates_evaluates _ _ Hva2)) as Hrel.
      destruct (value_relation_values _ _ _ _ Hrel) as [Hv1 Hv2].
      destruct (value_relation_underlying _ _ _ _ Hrel) as [Ht1 Ht2].
      simpl. repeat split; try (constructor; assumption);
        try (eapply T_Inl; eauto using erase_type_wf; exact I).
      intros _. left. exists va1, va2, k, k.
      repeat split; assumption.
Qed.

Lemma expression_relation_inr : forall observer T1 T2 k a1 a2,
  expression_relation observer T2 a1 a2 ->
  expression_relation observer (Ty_Sum T1 T2 k)
    (tm_inr a1 k) (tm_inr a2 k).
Proof.
  intros observer T1 T2 k a1 a2 [Ha1 [Ha2 Hr]].
  unfold expression_relation, underlying_typed in *; simpl.
  split.
  - eapply T_Inr; eauto using erase_type_wf. exact I.
  - split.
    + eapply T_Inr; eauto using erase_type_wf. exact I.
    + intros w1 w2 He1 He2.
      apply evaluates_big in He1. apply evaluates_big in He2.
      destruct (big_inr_inv _ _ _ He1) as (va1 & -> & Hva1).
      destruct (big_inr_inv _ _ _ He2) as (va2 & -> & Hva2).
      pose proof (Hr _ _ (big_evaluates_evaluates _ _ Hva1)
        (big_evaluates_evaluates _ _ Hva2)) as Hrel.
      destruct (value_relation_values _ _ _ _ Hrel) as [Hv1 Hv2].
      destruct (value_relation_underlying _ _ _ _ Hrel) as [Ht1 Ht2].
      simpl. repeat split; try (constructor; assumption);
        try (eapply T_Inr; eauto using erase_type_wf; exact I).
      intros _. right. exists va1, va2, k, k.
      repeat split; assumption.
Qed.

Lemma expression_relation_unit : forall observer k,
  expression_relation observer (Ty_Unit k) (tm_unit k) (tm_unit k).
Proof.
  intros observer k. unfold expression_relation, underlying_typed.
  simpl. split.
  - apply T_Unit. exact I.
  - split.
    + apply T_Unit. exact I.
    + intros a b Ha Hb.
      apply evaluates_big in Ha. apply evaluates_big in Hb.
      pose proof (big_evaluates_value_inv _ _ (v_unit k) Ha) as ->.
      pose proof (big_evaluates_value_inv _ _ (v_unit k) Hb) as ->.
      simpl. split; [constructor|].
      split; [constructor|].
      split; [apply T_Unit; exact I|].
      split; [apply T_Unit; exact I|].
      intros _. exists k, k. auto.
Qed.

Lemma expression_relation_nat : forall observer n k,
  expression_relation observer (Ty_Nat k) (tm_nat n k) (tm_nat n k).
Proof.
  intros observer n k. unfold expression_relation, underlying_typed.
  simpl. split.
  - apply T_Nat. exact I.
  - split.
    + apply T_Nat. exact I.
    + intros a b Ha Hb.
      apply evaluates_big in Ha. apply evaluates_big in Hb.
      pose proof (big_evaluates_value_inv _ _ (v_nat n k) Ha) as ->.
      pose proof (big_evaluates_value_inv _ _ (v_nat n k) Hb) as ->.
      simpl. split; [constructor|].
      split; [constructor|].
      split; [apply T_Nat; exact I|].
      split; [apply T_Nat; exact I|].
      intros _. exists n, k, k. auto.
Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof. intros []; destruct s; destruct reader0, indirect_reader0; reflexivity. Qed.

Lemma protect_value_low : forall v, protect_value v Low = v.
Proof.
  intros []; simpl; try reflexivity;
    destruct s; destruct reader0, indirect_reader0; reflexivity.
Qed.

Lemma big_protect_inv : forall l t v,
  big_evaluates (tm_protect l t) v ->
  exists w, big_evaluates t w /\ v = protect_value w l.
Proof.
  intros l t v He; inversion He; subst; eauto.
  match goal with H : value (tm_protect _ _) |- _ => inversion H end.
Qed.

Lemma expression_relation_protect_lowobserver : forall l T t1 t2,
  expression_relation Low T t1 t2 ->
  expression_relation Low (ty_protect l T)
    (tm_protect l t1) (tm_protect l t2).
Proof.
  intros l T t1 t2 [Ht1 [Ht2 Hr]].
  unfold expression_relation, underlying_typed in *.
  rewrite erase_type_protect. simpl.
  split; [exact Ht1|]. split; [exact Ht2|].
  intros v1 v2 He1 He2.
  apply evaluates_big in He1. apply evaluates_big in He2.
  destruct (big_protect_inv _ _ _ He1) as (w1 & Hw1 & ->).
  destruct (big_protect_inv _ _ _ He2) as (w2 & Hw2 & ->).
  pose proof (Hr _ _ (big_evaluates_evaluates _ _ Hw1)
    (big_evaluates_evaluates _ _ Hw2)) as Hrel.
  destruct l.
  - rewrite !protect_value_low, ty_protect_low. exact Hrel.
  - apply hidden_values_related.
    + destruct T; destruct s; destruct reader0, indirect_reader0;
        simpl; tauto.
    + apply protect_value_is_value.
      exact (proj1 (value_relation_values _ _ _ _ Hrel)).
    + apply protect_value_is_value.
      exact (proj2 (value_relation_values _ _ _ _ Hrel)).
    + unfold underlying_typed. rewrite erase_type_protect.
      rewrite erase_protect_value.
      exact (proj1 (value_relation_underlying _ _ _ _ Hrel)).
    + unfold underlying_typed. rewrite erase_type_protect.
      rewrite erase_protect_value.
      exact (proj2 (value_relation_underlying _ _ _ _ Hrel)).
Qed.

Lemma value_relation_protect_lowobserver : forall l T v1 v2,
  value_relation Low T v1 v2 ->
  value_relation Low (ty_protect l T)
    (protect_value v1 l) (protect_value v2 l).
Proof.
  intros l T v1 v2 Hr.
  destruct l.
  - rewrite !protect_value_low, ty_protect_low. exact Hr.
  - apply hidden_values_related.
    + destruct T; destruct s; destruct reader0, indirect_reader0;
        simpl; tauto.
    + apply protect_value_is_value.
      exact (proj1 (value_relation_values _ _ _ _ Hr)).
    + apply protect_value_is_value.
      exact (proj2 (value_relation_values _ _ _ _ Hr)).
    + unfold underlying_typed. rewrite erase_type_protect.
      rewrite erase_protect_value.
      exact (proj1 (value_relation_underlying _ _ _ _ Hr)).
    + unfold underlying_typed. rewrite erase_type_protect.
      rewrite erase_protect_value.
      exact (proj2 (value_relation_underlying _ _ _ _ Hr)).
Qed.

Definition fresh_for (xs : list atom) : atom :=
  S (fold_right Nat.max 0 xs).

Lemma fresh_for_not_in : forall xs, ~ In (fresh_for xs) xs.
Proof.
  intros xs Hin.
  assert (Hbound : forall ys y, In y ys -> y <= fold_right Nat.max 0 ys).
  { induction ys as [|a ys IH]; intros y Hy; simpl in *.
    - contradiction.
    - destruct Hy as [-> | Hy].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [apply IH; exact Hy|apply Nat.le_max_r]. }
  specialize (Hbound xs _ Hin). unfold fresh_for in Hbound.
  lia.
Qed.

Lemma fv_open_rec_subset : forall t k u x,
  In x (fv (open_rec k u t)) ->
  In x (fv t) \/ In x (fv u).
Proof.
  intros t; induction t; intros k u x Hx; simpl in *;
    repeat rewrite in_app_iff in *; try tauto; eauto 5.
  destruct (Nat.eqb k n); simpl in *; tauto.
  all: intuition;
    match goal with
    | Hx' : In ?y (fv (open_rec ?j ?w _)) |- _ =>
        first [pose proof (IHt1 j w y Hx') |
               pose proof (IHt2 j w y Hx') |
               pose proof (IHt3 j w y Hx')]; tauto
    end.
Qed.

Lemma lookup_update_agree_open : forall Gamma Delta T x body,
  ~ In x (fv body) ->
  (forall y, In y (fv body) ->
    lookup_context y Gamma = lookup_context y Delta) ->
  forall y, In y (fv (open body (tm_fvar x))) ->
    lookup_context y (update Gamma x T) =
    lookup_context y (update Delta x T).
Proof.
  intros Gamma Delta T x body Hfresh Hagree y Hy.
  destruct (fv_open_rec_subset body 0 (tm_fvar x) y Hy) as [Hbody|Harg].
  - assert (y <> x) by (intro E; subst; contradiction).
    unfold update; simpl.
    assert (Nat.eqb y x = false) as E by (apply Nat.eqb_neq; exact H).
    rewrite E. apply Hagree; exact Hbody.
  - simpl in Harg. destruct Harg as [->|[]].
    unfold update; simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma typing_context_invariance : forall Gamma t T,
  has_type Gamma t T -> forall Delta,
  (forall x, In x (fv t) ->
    lookup_context x Gamma = lookup_context x Delta) ->
  has_type Delta t T.
Proof.
  intros Gamma t T Hty; induction Hty; intros Delta Hagree;
    simpl in Hagree.
  - apply T_Var.
    + rewrite <- (Hagree x); [exact H|simpl; auto].
    + exact H0.
  - apply T_Unit; exact H.
  - eapply T_Abs with (L := L ++ fv body); eauto.
    intros x Hfresh.
    assert (HnotL : ~ In x L) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hnotbody : ~ In x (fv body))
      by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    apply H2 with (Delta := update Delta x T1); auto.
    intros y Hy.
    destruct (fv_open_rec_subset body 0 (tm_fvar x) y Hy) as [Hbody|Harg].
    + assert (y <> x) by (intro E; subst; contradiction).
      unfold update; simpl.
      assert (Nat.eqb y x = false) as E by (apply Nat.eqb_neq; exact H3).
      rewrite E. apply Hagree; exact Hbody.
    + simpl in Harg. destruct Harg as [->|[]].
      unfold update; simpl. rewrite Nat.eqb_refl. reflexivity.
  - eapply T_App.
    + apply IHHty1. intros x Hx; apply Hagree.
      apply in_or_app; left; exact Hx.
    + apply IHHty2. intros x Hx; apply Hagree.
      apply in_or_app; right; exact Hx.
    + exact H.
  - eapply T_Pair.
    + apply IHHty1. intros x Hx; apply Hagree.
      apply in_or_app; left; exact Hx.
    + apply IHHty2. intros x Hx; apply Hagree.
      apply in_or_app; right; exact Hx.
    + exact H.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
  - eapply T_Inl; eauto.
  - eapply T_Inr; eauto.
  - eapply T_Case with (L := L ++ fv body1 ++ fv body2).
    + apply IHHty. intros x Hx; apply Hagree.
      repeat rewrite in_app_iff; tauto.
    + exact H.
    + intros x Hfresh.
      apply H1 with (Delta := update Delta x T1).
      * intro Hin; apply Hfresh. repeat rewrite in_app_iff; tauto.
      * apply lookup_update_agree_open.
        -- intro Hin; apply Hfresh. repeat rewrite in_app_iff; tauto.
        -- intros y Hy; apply Hagree.
           repeat rewrite in_app_iff; tauto.
    + intros x Hfresh.
      apply H3 with (Delta := update Delta x T2).
      * intro Hin; apply Hfresh. repeat rewrite in_app_iff; tauto.
      * apply lookup_update_agree_open.
        -- intro Hin; apply Hfresh. repeat rewrite in_app_iff; tauto.
        -- intros y Hy; apply Hagree.
           repeat rewrite in_app_iff; tauto.
  - apply T_Protect. apply IHHty; exact Hagree.
  - eapply T_Sub; [apply IHHty; exact Hagree|exact H].
  - apply T_Nat; exact H.
  - apply T_Succ; [apply IHHty; exact Hagree|exact H].
  - eapply T_NatRec.
    + apply IHHty1. intros x Hx; apply Hagree.
      repeat rewrite in_app_iff; tauto.
    + apply IHHty2. intros x Hx; apply Hagree.
      repeat rewrite in_app_iff; tauto.
    + apply IHHty3. intros x Hx; apply Hagree.
      repeat rewrite in_app_iff; tauto.
    + exact H.
  - eapply T_If.
    + apply IHHty1. intros x Hx; apply Hagree.
      repeat rewrite in_app_iff; tauto.
    + apply IHHty2. intros x Hx; apply Hagree.
      repeat rewrite in_app_iff; tauto.
    + apply IHHty3. intros x Hx; apply Hagree.
      repeat rewrite in_app_iff; tauto.
    + exact H.
Qed.

Lemma typing_weakening_fresh : forall Gamma t T x U,
  has_type Gamma t T -> ~ In x (fv t) ->
  has_type (update Gamma x U) t T.
Proof.
  intros Gamma t T x U Hty Hfresh.
  eapply typing_context_invariance; [exact Hty|].
  intros y Hy. unfold update; simpl.
  assert (y <> x) by (intro E; subst; contradiction).
  assert (Nat.eqb y x = false) as E by (apply Nat.eqb_neq; exact H).
  rewrite E. reflexivity.
Qed.

Definition environment_fv (Gamma : context) (rho : atom -> tm) : list atom :=
  flat_map (fun p => fv (rho (fst p))) Gamma.

Lemma lookup_in_context : forall Gamma x T,
  lookup_context x Gamma = Some T -> In (x, T) Gamma.
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T Hlookup; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; subst. inversion Hlookup; subst.
      left; reflexivity.
    + right. apply IH; exact Hlookup.
Qed.

Lemma environment_fv_contains : forall Gamma rho x T y,
  lookup_context x Gamma = Some T ->
  In y (fv (rho x)) -> In y (environment_fv Gamma rho).
Proof.
  intros Gamma rho x T y Hlookup Hfv.
  unfold environment_fv. apply in_flat_map.
  exists (x,T). split.
  - apply lookup_in_context; exact Hlookup.
  - simpl. exact Hfv.
Qed.

Lemma subtype_wf : forall T U,
  subtype T U -> wf_ty T /\ wf_ty U.
Proof.
  intros T U Hsub; induction Hsub; simpl in *; try tauto.
  Show.
Qed.

Lemma wf_security_protect : forall k l,
  wf_security k -> wf_security (protect_security k l).
Proof.
  intros [r i] l H; destruct r, i, l;
    unfold wf_security, flows_to, protect_security, join in *;
    simpl in *; tauto.
Qed.

Lemma wf_ty_protect : forall T l,
  wf_ty T -> wf_ty (ty_protect l T).
Proof.
  intros T l; destruct T; simpl; intros H;
    try (apply wf_security_protect; exact H);
    destruct H as [H1 [H2 Hk]];
    repeat split; auto using wf_security_protect.
Qed.

Lemma typing_wf : forall Gamma t T,
  has_type Gamma t T -> wf_ty T.
Proof.
  intros Gamma t T Hty; induction Hty; simpl in *;
    try tauto; try (apply wf_ty_protect; auto).
  - repeat split; auto.
    exact (H2 (fresh_for L) (fresh_for_not_in L)).
  - destruct IHHty1 as [_ [Hout _]]. exact Hout.
  - destruct IHHty as [Hout _]. exact Hout.
  - destruct IHHty as [_ [Hout _]]. exact Hout.
  - exact (H1 (fresh_for L) (fresh_for_not_in L)).
  - exact (proj2 (subtype_wf _ _ H)).
  - apply wf_security_protect. exact I.
Qed.

Lemma typing_close_env_branch : forall L Gamma body Targ T Delta rho,
  wf_ty Targ ->
  (forall x, ~ In x L -> forall Delta' rho',
    (forall y U, lookup_context y (update Gamma x Targ) = Some U ->
      has_type Delta' (rho' y) U) ->
    (forall y, locally_closed (rho' y)) ->
    has_type Delta' (close_env rho' (open body (tm_fvar x))) T) ->
  (forall y U, lookup_context y Gamma = Some U ->
    has_type Delta (rho y) U) ->
  (forall y, locally_closed (rho y)) ->
  forall x, ~ In x (L ++ fv body ++ environment_fv Gamma rho) ->
    has_type (update Delta x Targ)
      (open (close_env rho body) (tm_fvar x)) T.
Proof.
  intros L Gamma body Targ T Delta rho Hwf Hbranch Henv Hlc x Hfresh.
  assert (HnotL : ~ In x L) by
    (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
  assert (Hnotbody : ~ In x (fv body)) by
    (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
  assert (Hnotenv : ~ In x (environment_fv Gamma rho)) by
    (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
  assert (Hlcvar : locally_closed (tm_fvar x)) by
    (unfold locally_closed; simpl; exact I).
  rewrite <- (close_env_open_fresh rho x (tm_fvar x) body
    Hlc Hlcvar Hnotbody).
  apply Hbranch with (Delta' := update Delta x Targ).
  - exact HnotL.
  - intros y U Hlookup.
    unfold update in Hlookup; simpl in Hlookup.
    unfold env_set.
    destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      rewrite Nat.eqb_refl. inversion Hlookup; subst.
      apply T_Var; [simpl; rewrite Nat.eqb_refl; reflexivity|exact Hwf].
    + assert (Nat.eqb x y = false) as E' by
        (rewrite Nat.eqb_sym; exact E).
      rewrite E'. apply typing_weakening_fresh.
      * apply Henv; exact Hlookup.
      * intro Hin; apply Hnotenv.
        eapply environment_fv_contains; eauto.
  - intros y; unfold env_set; destruct (Nat.eqb x y); auto.
Qed.

Lemma typing_close_env : forall Gamma t T,
  has_type Gamma t T -> forall Delta rho,
  (forall x U, lookup_context x Gamma = Some U ->
    has_type Delta (rho x) U) ->
  (forall x, locally_closed (rho x)) ->
  has_type Delta (close_env rho t) T.
Proof.
  intros Gamma t T Hty; induction Hty;
    intros Delta rho Henv Hlc; simpl.
  - apply Henv; exact H.
  - apply T_Unit; exact H.
  - eapply T_Abs with
      (L := L ++ fv body ++ environment_fv Gamma rho); eauto.
    intros x Hfresh.
    assert (HnotL : ~ In x L) by
      (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (Hnotbody : ~ In x (fv body)) by
      (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (Hnotenv : ~ In x (environment_fv Gamma rho)) by
      (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (Hlcvar : locally_closed (tm_fvar x)) by
      (unfold locally_closed; simpl; exact I).
    rewrite <- (close_env_open_fresh rho x (tm_fvar x) body
      Hlc Hlcvar Hnotbody).
    apply H2 with (Delta := update Delta x T1).
    + exact HnotL.
    + intros y U Hlookup.
      unfold update in Hlookup; simpl in Hlookup.
      unfold env_set.
      destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E; subst.
        rewrite Nat.eqb_refl. inversion Hlookup; subst.
        apply T_Var; [simpl; rewrite Nat.eqb_refl; reflexivity|exact H].
      * assert (Nat.eqb x y = false) as E' by
          (rewrite Nat.eqb_sym; exact E).
        rewrite E'.
        apply typing_weakening_fresh.
        -- apply Henv; exact Hlookup.
        -- intro Hin; apply Hnotenv.
           eapply environment_fv_contains; eauto.
    + intros y; unfold env_set.
      destruct (Nat.eqb x y); auto.
  - eapply T_App; eauto.
  - eapply T_Pair; eauto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
  - eapply T_Inl; eauto.
  - eapply T_Inr; eauto.
  - destruct (typing_wf _ _ _ Hty) as [Hwf1 [Hwf2 _]].
    eapply T_Case with
      (L := L ++ fv body1 ++ fv body2 ++ environment_fv Gamma rho).
    + apply IHHty; assumption.
    + exact H.
    + intros x Hfresh.
      eapply typing_close_env_branch with
        (L := L) (Gamma := Gamma) (body := body1)
        (Targ := T1) (Delta := Delta) (rho := rho);
        eauto.
      intro Hin; apply Hfresh.
      repeat rewrite in_app_iff in *; tauto.
    + intros x Hfresh.
      eapply typing_close_env_branch with
        (L := L) (Gamma := Gamma) (body := body2)
        (Targ := T2) (Delta := Delta) (rho := rho);
        eauto.
      intro Hin; apply Hfresh.
      repeat rewrite in_app_iff in *; tauto.
  - apply T_Protect. apply IHHty; assumption.
  - eapply T_Sub; [apply IHHty; assumption|exact H].
  - apply T_Nat; exact H.
  - eapply T_Succ; eauto.
  - eapply T_NatRec; eauto.
  - eapply T_If; eauto.
Qed.

Lemma erase_close_env : forall rho t,
  erase_security (close_env rho t) =
  close_env (fun x => erase_security (rho x)) (erase_security t).
Proof.
  intros rho t; induction t; simpl;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity).
Qed.

Lemma erase_lc_at : forall t k,
  lc_at k t -> lc_at k (erase_security t).
Proof.
  intros t; induction t; intros k Hlc; simpl in *;
    try tauto; try (eauto).
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto.
Qed.

Lemma erase_lookup_inv : forall Gamma x U,
  lookup_context x (erase_context Gamma) = Some U ->
  exists T, lookup_context x Gamma = Some T /\ U = erase_type T.
Proof.
  induction Gamma as [|[y T] Gamma IH]; intros x U Hlookup; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. exists T; split; reflexivity.
    + apply IH in Hlookup. destruct Hlookup as [V [Hlook ->]].
      exists V; split; [exact Hlook|reflexivity].
Qed.

Lemma underlying_close_env : forall Gamma t T rho,
  has_type Gamma t T ->
  (forall x, locally_closed (rho x)) ->
  (forall x U, lookup_context x Gamma = Some U ->
    underlying_typed U (rho x)) ->
  underlying_typed T (close_env rho t).
Proof.
  intros Gamma t T rho Hty Hlc Henv.
  unfold underlying_typed in *.
  rewrite erase_close_env.
  eapply typing_close_env.
  - apply erase_typing; exact Hty.
  - intros x U Hlookup.
    destruct (erase_lookup_inv _ _ _ Hlookup) as [V [Hlook ->]].
    exact (Henv x V Hlook).
  - intros x. unfold locally_closed in *.
    apply erase_lc_at. apply Hlc.
Qed.

Lemma lc_open_to_body : forall body k x,
  lc_at k (open_rec k (tm_fvar x) body) ->
  lc_at (S k) body.
Proof.
  intros body; induction body; intros k x Hlc; simpl in *;
    try solve [tauto | eauto 8 using IHbody, IHbody1, IHbody2, IHbody3 |
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      repeat split; eauto 8 using IHbody, IHbody1, IHbody2, IHbody3].
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; lia.
    + cbn in Hlc. lia.
  - apply IHbody with (x := x). exact Hlc.
  - destruct Hlc as [H1 H2]. split.
    + apply IHbody1 with (x := x); exact H1.
    + apply IHbody2 with (x := x); exact H2.
  - destruct Hlc as [H1 H2]. split.
    + apply IHbody1 with (x := x); exact H1.
    + apply IHbody2 with (x := x); exact H2.
  - apply IHbody with (x := x); exact Hlc.
  - apply IHbody with (x := x); exact Hlc.
  - apply IHbody with (x := x); exact Hlc.
  - apply IHbody with (x := x); exact Hlc.
  - destruct Hlc as [H1 [H2 H3]]. repeat split.
    + apply IHbody1 with (x := x); exact H1.
    + apply IHbody2 with (x := x); exact H2.
    + apply IHbody3 with (x := x); exact H3.
  - apply IHbody with (x := x); exact Hlc.
  - apply IHbody with (x := x); exact Hlc.
  - destruct Hlc as [H1 [H2 H3]]. repeat split;
      [apply IHbody1 with (x := x); exact H1 |
       apply IHbody2 with (x := x); exact H2 |
       apply IHbody3 with (x := x); exact H3].
  - destruct Hlc as [H1 [H2 H3]]. repeat split;
      [apply IHbody1 with (x := x); exact H1 |
       apply IHbody2 with (x := x); exact H2 |
       apply IHbody3 with (x := x); exact H3].
Qed.

Lemma typing_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty; induction Hty; unfold locally_closed in *;
    simpl in *; try tauto; try exact I.
  - apply lc_open_to_body with (x := fresh_for L).
    exact (H2 (fresh_for L) (fresh_for_not_in L)).
  - split; [exact IHHty|]. split.
    + apply lc_open_to_body with (x := fresh_for L).
      exact (H1 (fresh_for L) (fresh_for_not_in L)).
    + apply lc_open_to_body with (x := fresh_for L).
      exact (H3 (fresh_for L) (fresh_for_not_in L)).
Qed.

Lemma erase_lc_at_reverse : forall t k,
  lc_at k (erase_security t) -> lc_at k t.
Proof.
  intros t; induction t; intros k Hlc; simpl in *;
    try tauto; try eauto.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto.
Qed.

Lemma underlying_locally_closed : forall T t,
  underlying_typed T t -> locally_closed t.
Proof.
  intros T t Ht. unfold underlying_typed in Ht.
  apply erase_lc_at_reverse.
  apply typing_lc in Ht. exact Ht.
Qed.

Lemma big_app_abs_inv : forall T body k arg out r,
  value (tm_abs T body k) -> value arg ->
  big_evaluates (tm_app (tm_abs T body k) arg r) out ->
  exists w, big_evaluates (open body arg) w /\
    out = protect_value w k.(indirect_reader).
Proof.
  intros T body k arg out r Habs Harg He.
  inversion He; subst.
  - match goal with H : value (tm_app _ _ _) |- _ => inversion H end.
  - match goal with
    Hf : big_evaluates (tm_abs T body k) (tm_abs _ _ _) |- _ =>
      pose proof (big_evaluates_value_inv _ _ Habs Hf) as Ef;
      inversion Ef; subst
    end.
    match goal with
    Ha : big_evaluates arg _ |- _ =>
      pose proof (big_evaluates_value_inv _ _ Harg Ha) as Ea;
      subst
    end.
    eauto.
Qed.

Lemma expression_relation_abs_low : forall T1 T2 k body1 body2,
  underlying_typed (Ty_Arrow T1 T2 k) (tm_abs T1 body1 k) ->
  underlying_typed (Ty_Arrow T1 T2 k) (tm_abs T1 body2 k) ->
  (forall arg1 arg2,
    value_relation Low T1 arg1 arg2 ->
    expression_relation Low T2 (open body1 arg1) (open body2 arg2)) ->
  expression_relation Low (Ty_Arrow T1 T2 k)
    (tm_abs T1 body1 k) (tm_abs T1 body2 k).
Proof.
  intros T1 T2 k body1 body2 Ht1 Ht2 Hbody.
  unfold expression_relation. split; [exact Ht1|].
  split; [exact Ht2|].
  intros v1 v2 He1 He2.
  apply evaluates_big in He1. apply evaluates_big in He2.
  assert (Hv1 : value (tm_abs T1 body1 k)) by
    (apply v_abs; apply underlying_locally_closed with
      (T := Ty_Arrow T1 T2 k); exact Ht1).
  assert (Hv2 : value (tm_abs T1 body2 k)) by
    (apply v_abs; apply underlying_locally_closed with
      (T := Ty_Arrow T1 T2 k); exact Ht2).
  pose proof (big_evaluates_value_inv _ _ Hv1 He1) as ->.
  pose proof (big_evaluates_value_inv _ _ Hv2 He2) as ->.
  simpl. split; [exact Hv1|]. split; [exact Hv2|].
  split; [exact Ht1|]. split; [exact Ht2|].
  intros Hvisible.
  exists T1, T1, body1, body2, k, k.
  split; [reflexivity|]. split; [reflexivity|].
  intros arg1 arg2 Harg out1 out2 Happ1 Happ2.
  destruct (value_relation_values _ _ _ _ Harg) as [Harg1 Harg2].
  apply evaluates_big in Happ1. apply evaluates_big in Happ2.
  destruct (big_app_abs_inv _ _ _ _ _ _ Hv1 Harg1 Happ1)
    as (w1 & Hw1 & ->).
  destruct (big_app_abs_inv _ _ _ _ _ _ Hv2 Harg2 Happ2)
    as (w2 & Hw2 & ->).
  destruct k as [r i]. destruct i.
  - rewrite !protect_value_low.
    destruct (Hbody arg1 arg2 Harg) as [_ [_ Hrel]].
    apply Hrel; apply big_evaluates_evaluates; assumption.
  - simpl in Hvisible. contradiction.
Qed.

Lemma subtype_indirect_flow : forall T U,
  subtype T U ->
  flows_to (security_of T).(indirect_reader)
    (security_of U).(indirect_reader).
Proof.
  intros T U H; induction H; simpl in *;
    try (destruct H1 as [_ Hflow]; exact Hflow);
    try (destruct H3 as [_ Hflow]; exact Hflow).
  eapply flows_trans; eauto.
Qed.

Lemma underlying_subtype : forall T U v,
  subtype T U -> underlying_typed T v -> underlying_typed U v.
Proof.
  intros T U v Hsub Ht.
  unfold underlying_typed in *.
  rewrite <- (erase_subtype _ _ Hsub). exact Ht.
Qed.

Lemma value_relation_subtype : forall T U,
  subtype T U -> forall v1 v2,
  value_relation Low T v1 v2 -> value_relation Low U v1 v2.
Proof.
  intros T U Hsub; induction Hsub; intros v1 v2 Hr.
  - simpl in *. destruct Hr as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    assert (Hs : subtype (Ty_Unit kappa1) (Ty_Unit kappa2))
      by (apply S_Unit; assumption).
    split; [exact Hv1|]. split; [exact Hv2|].
    split; [exact (underlying_subtype _ _ _ Hs Ht1)|].
    split; [exact (underlying_subtype _ _ _ Hs Ht2)|].
    intros Hvis. apply Hshape.
    eapply flows_trans; [exact (proj2 H1)|exact Hvis].
  - simpl in *. destruct Hr as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    assert (Hs : subtype (Ty_Sum T1 T2 kappa1)
      (Ty_Sum U1 U2 kappa2)) by (apply S_Sum; assumption).
    split; [exact Hv1|]. split; [exact Hv2|].
    split; [exact (underlying_subtype _ _ _ Hs Ht1)|].
    split; [exact (underlying_subtype _ _ _ Hs Ht2)|].
    intros Hvis.
    specialize (Hshape (flows_trans _ _ _ (proj2 H1) Hvis)).
    destruct Hshape as [[a1 [a2 [k1 [k2 [He1 [He2 Ha]]]]]] |
      [a1 [a2 [k1 [k2 [He1 [He2 Ha]]]]]]];
      [left|right]; exists a1, a2, k1, k2;
      repeat split; auto.
  - simpl in *. destruct Hr as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    assert (Hs : subtype (Ty_Prod T1 T2 kappa1)
      (Ty_Prod U1 U2 kappa2)) by (apply S_Prod; assumption).
    split; [exact Hv1|]. split; [exact Hv2|].
    split; [exact (underlying_subtype _ _ _ Hs Ht1)|].
    split; [exact (underlying_subtype _ _ _ Hs Ht2)|].
    intros Hvis.
    specialize (Hshape (flows_trans _ _ _ (proj2 H1) Hvis)).
    destruct Hshape as (a1 & b1 & a2 & b2 & k1 & k2 & He1 & He2 & Ha & Hb).
    exists a1, b1, a2, b2, k1, k2.
    repeat split; auto.
  - simpl in *. destruct Hr as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    assert (Hs : subtype (Ty_Arrow T1 T2 kappa1)
      (Ty_Arrow U1 U2 kappa2)) by (apply S_Arrow; assumption).
    split; [exact Hv1|]. split; [exact Hv2|].
    split; [exact (underlying_subtype _ _ _ Hs Ht1)|].
    split; [exact (underlying_subtype _ _ _ Hs Ht2)|].
    intros Hvis.
    specialize (Hshape (flows_trans _ _ _ (proj2 H1) Hvis)).
    destruct Hshape as (A1 & A2 & body1 & body2 & k1 & k2 & He1 & He2 & Hfun).
    exists A1, A2, body1, body2, k1, k2.
    split; [exact He1|]. split; [exact He2|].
    intros arg1 arg2 Harg out1 out2 Hev1 Hev2.
    apply IHHsub2.
    exact (Hfun arg1 arg2 (IHHsub1 _ _ Harg) out1 out2 Hev1 Hev2).
  - apply IHHsub2, IHHsub1; exact Hr.
  - simpl in *. destruct Hr as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    assert (Hs : subtype (Ty_Nat k1) (Ty_Nat k2))
      by (apply S_Nat; assumption).
    split; [exact Hv1|]. split; [exact Hv2|].
    split; [exact (underlying_subtype _ _ _ Hs Ht1)|].
    split; [exact (underlying_subtype _ _ _ Hs Ht2)|].
    intros Hvis. apply Hshape.
    eapply flows_trans; [exact (proj2 H1)|exact Hvis].
Qed.

Lemma expression_relation_subtype : forall T U t1 t2,
  subtype T U ->
  expression_relation Low T t1 t2 ->
  expression_relation Low U t1 t2.
Proof.
  intros T U t1 t2 Hsub [Ht1 [Ht2 Hr]].
  split; [eapply underlying_subtype; eauto|].
  split; [eapply underlying_subtype; eauto|].
  intros v1 v2 He1 He2.
  apply value_relation_subtype with (T := T);
    auto.
Qed.

Theorem fundamental_low : forall Gamma t T,
  has_type Gamma t T ->
  forall rho1 rho2,
  (forall x, locally_closed (rho1 x)) ->
  (forall x, locally_closed (rho2 x)) ->
  environments_related Low Gamma rho1 rho2 ->
  expression_relation Low T (close_env rho1 t) (close_env rho2 t).
Proof.
  intros Gamma t T Htype; induction Htype;
    intros rho1 rho2 Hlc1 Hlc2 Henv; simpl.
  - eapply fundamental_variable; eauto.
  - apply expression_relation_unit.
  - apply expression_relation_abs_low.
    + change (underlying_typed (Ty_Arrow T1 T2 kappa)
        (close_env rho1 (tm_abs T1 body kappa))).
      eapply underlying_close_env with (Gamma := Gamma);
        [eapply T_Abs with (L := L); eauto|
        exact Hlc1|].
      intros x U Hlookup.
      exact (proj1 (value_relation_underlying _ _ _ _
        (Henv x U Hlookup))).
    + change (underlying_typed (Ty_Arrow T1 T2 kappa)
        (close_env rho2 (tm_abs T1 body kappa))).
      eapply underlying_close_env with (Gamma := Gamma);
        [eapply T_Abs with (L := L); eauto|
        exact Hlc2|].
      intros x U Hlookup.
      exact (proj2 (value_relation_underlying _ _ _ _
        (Henv x U Hlookup))).
    + intros arg1 arg2 Harg.
      set (x := fresh_for (L ++ fv body)).
      assert (HnotL : ~ In x L) by
        (unfold x; intro Hin; apply fresh_for_not_in with
          (xs := L ++ fv body); apply in_or_app; left; exact Hin).
      assert (Hnotbody : ~ In x (fv body)) by
        (unfold x; intro Hin; apply fresh_for_not_in with
          (xs := L ++ fv body); apply in_or_app; right; exact Hin).
      specialize (H2 x HnotL (env_set rho1 x arg1)
        (env_set rho2 x arg2)).
      assert (Hlcarg1 : locally_closed arg1) by
        (apply value_locally_closed;
         exact (proj1 (value_relation_values _ _ _ _ Harg))).
      assert (Hlcarg2 : locally_closed arg2) by
        (apply value_locally_closed;
         exact (proj2 (value_relation_values _ _ _ _ Harg))).
      assert (Hlce1 : forall y, locally_closed (env_set rho1 x arg1 y)).
      { intros y; unfold env_set. destruct (Nat.eqb x y); auto. }
      assert (Hlce2 : forall y, locally_closed (env_set rho2 x arg2 y)).
      { intros y; unfold env_set. destruct (Nat.eqb x y); auto. }
      specialize (H2 Hlce1 Hlce2
        (environments_related_update _ _ _ _ _ _ _ _ Henv Harg)).
      rewrite close_env_open_fresh in H2 by assumption.
      rewrite close_env_open_fresh in H2 by assumption.
      exact H2.
  - Show.
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
