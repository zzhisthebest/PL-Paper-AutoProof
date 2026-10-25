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
  | tm_natrec : tm -> tm -> tm -> label -> tm.

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
  | tm_case t0 body1 body2 _ => fv t0 ++ fv body1 ++ fv body2
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
      has_type Gamma (tm_natrec n b s r) (ty_protect k.(indirect_reader) T).

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
  | C_RecStep : tm -> tm -> program_context -> label -> program_context.

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

Lemma flows_to_trans : forall a b c,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. destruct a, b, c; simpl; tauto. Qed.

Lemma visible_components : forall k U observer,
  security_le (security_of U) k ->
  flows_to k.(indirect_reader) observer ->
  flows_to (security_of U).(indirect_reader) observer.
Proof.
  intros k U observer [_ Hle] Hlow.
  eapply flows_to_trans; eauto.
Qed.

Lemma relation_ground_equal_at : forall observer T k v1 v2,
  ground T -> transparent_at k T ->
  flows_to k.(indirect_reader) observer ->
  value_relation observer T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  intros observer T.
  induction T as [k|T1 IH1 T2 IH2 k|T1 IH1 T2 IH2 k|
                  T1 IH1 T2 IH2 k|k];
    intros outer v1 v2 Hg Ht Hflow Hr; simpl in Hg, Ht, Hr.
  - destruct Ht as [Hle _].
    destruct Hr as [_ [_ [_ [_ H]]]].
    destruct (H (flows_to_trans _ _ _ (proj2 Hle) Hflow))
      as [k1 [k2 [-> ->]]]. reflexivity.
  - destruct Hg as [Hg1 Hg2].
    destruct Ht as [Hle [Ht1 Ht2]].
    destruct Hr as [_ [_ [_ [_ H]]]].
    destruct (H (flows_to_trans _ _ _ (proj2 Hle) Hflow)) as
      [[u1 [u2 [k1 [k2 [-> [-> Hu]]]]]] |
       [u1 [u2 [k1 [k2 [-> [-> Hu]]]]]]]; simpl; f_equal.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
  - destruct Hg as [Hg1 Hg2].
    destruct Ht as [Hle [Ht1 Ht2]].
    destruct Hr as [_ [_ [_ [_ H]]]].
    destruct (H (flows_to_trans _ _ _ (proj2 Hle) Hflow))
      as (a1 & b1 & a2 & b2 & k1 & k2 & -> & -> & Ha & Hb).
    simpl. f_equal.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
  - contradiction.
  - destruct Ht as [Hle _].
    destruct Hr as [_ [_ [_ [_ H]]]].
    destruct (H (flows_to_trans _ _ _ (proj2 Hle) Hflow))
      as [n [k1 [k2 [-> ->]]]]. reflexivity.
Qed.

Lemma relation_ground_equal : forall observer T v1 v2,
  ground T -> transparent T ->
  flows_to (security_of T).(indirect_reader) observer ->
  value_relation observer T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof. intros. eapply relation_ground_equal_at; eauto. Qed.

Lemma erase_open_rec : forall t u k,
  erase_security (open_rec k u t) =
  open_rec k (erase_security u) (erase_security t).
Proof.
  induction t; intros u k; simpl; try (f_equal; eauto); auto.
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma erase_open : forall t u,
  erase_security (open t u) =
  open (erase_security t) (erase_security u).
Proof. intros; apply erase_open_rec. Qed.

Lemma erase_subst : forall t x u,
  erase_security (subst x u t) =
  subst x (erase_security u) (erase_security t).
Proof.
  induction t; intros x u; simpl; try (f_equal; eauto); auto.
  destruct (Nat.eqb x a); reflexivity.
Qed.

Lemma erase_type_protect : forall T l,
  erase_type (ty_protect l T) = erase_type T.
Proof. destruct T; reflexivity. Qed.

Lemma protect_low_erase_type : forall T,
  ty_protect Low (erase_type T) = erase_type T.
Proof. destruct T; reflexivity. Qed.

Lemma erase_protect_value : forall v l,
  erase_security (protect_value v l) = erase_security v.
Proof. destruct v; reflexivity. Qed.

Lemma lc_at_erase : forall t k,
  lc_at k t -> lc_at k (erase_security t).
Proof.
  induction t; intros k H; simpl in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto.
Qed.

Lemma erase_value : forall v,
  value v -> value (erase_security v).
Proof.
  intros v Hv. induction Hv; simpl; constructor;
    unfold locally_closed in *; eauto using lc_at_erase.
Qed.

Lemma wf_erase_type : forall T, wf_ty (erase_type T).
Proof.
  induction T; simpl; try (repeat split; eauto);
    unfold wf_security, public, flows_to; simpl; exact I.
Qed.

Lemma subtype_erase_eq : forall T U,
  subtype T U -> erase_type T = erase_type U.
Proof.
  intros T U H. induction H; simpl; congruence.
Qed.

Definition erase_context (Gamma : context) : context :=
  map (fun '(x, T) => (x, erase_type T)) Gamma.

Lemma lookup_erase_context : forall Gamma x T,
  lookup_context x Gamma = Some T ->
  lookup_context x (erase_context Gamma) = Some (erase_type T).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y); simpl in *; auto.
    inversion H; reflexivity.
Qed.

Lemma lookup_erase_context_inv : forall Gamma x U,
  lookup_context x (erase_context Gamma) = Some U ->
  exists T, lookup_context x Gamma = Some T /\ U = erase_type T.
Proof.
  induction Gamma as [|[y T] Gamma IH]; intros x U H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:Hxy; simpl in *.
    + inversion H; subst.
      exists T. split; auto.
    + destruct (IH _ _ H) as [V [HV ->]].
      exists V. split; auto.
Qed.

Lemma erase_context_update : forall Gamma x T,
  erase_context (update Gamma x T) =
  update (erase_context Gamma) x (erase_type T).
Proof. reflexivity. Qed.

Lemma typing_erase : forall Gamma t T,
  has_type Gamma t T ->
  has_type (erase_context Gamma) (erase_security t) (erase_type T).
Proof.
  intros Gamma t T Htyp. induction Htyp; simpl in *.
  - apply T_Var; auto using lookup_erase_context, wf_erase_type.
  - apply T_Unit. exact I.
  - eapply T_Abs with (L := L); eauto using wf_erase_type.
    + exact I.
    + intros x Hx. rewrite <- erase_context_update.
      change (tm_fvar x) with (erase_security (tm_fvar x)).
      rewrite <- erase_open. apply H2; assumption.
  - rewrite erase_type_protect. rewrite <- protect_low_erase_type.
    eapply T_App with (kappa := public); eauto. exact I.
  - eapply T_Pair; eauto. exact I.
  - rewrite erase_type_protect. rewrite <- protect_low_erase_type.
    eapply T_Fst with (kappa := public); eauto. exact I.
  - rewrite erase_type_protect. rewrite <- protect_low_erase_type.
    eapply T_Snd with (kappa := public); eauto. exact I.
  - eapply T_Inl; eauto using wf_erase_type. exact I.
  - eapply T_Inr; eauto using wf_erase_type. exact I.
  - rewrite erase_type_protect. rewrite <- protect_low_erase_type.
    eapply T_Case with (L := L) (kappa := public); eauto.
    + exact I.
    + intros x Hx. rewrite <- erase_context_update.
      change (tm_fvar x) with (erase_security (tm_fvar x)).
      rewrite <- erase_open. apply H1; assumption.
    + intros x Hx. rewrite <- erase_context_update.
      change (tm_fvar x) with (erase_security (tm_fvar x)).
      rewrite <- erase_open. apply H3; assumption.
  - rewrite erase_type_protect. exact IHHtyp.
  - match goal with Hsub : subtype _ _ |- _ =>
      rewrite (subtype_erase_eq _ _ Hsub) in IHHtyp end.
    exact IHHtyp.
  - apply T_Nat. exact I.
  - eapply T_Succ with (k := public); eauto. exact I.
  - rewrite erase_type_protect. rewrite <- protect_low_erase_type.
    eapply T_NatRec with (k := public); eauto. exact I.
Qed.

Lemma multi_trans : forall t1 t2 t3,
  t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H12 H23. induction H12; eauto using multi.
Qed.

Lemma multi_app1 : forall t1 t1' t2 r,
  t1 -->* t1' -> tm_app t1 t2 r -->* tm_app t1' t2 r.
Proof.
  intros t1 t1' t2 r H. induction H; eauto using multi, step.
Qed.

Lemma multi_app2 : forall v1 t2 t2' r,
  value v1 -> t2 -->* t2' ->
  tm_app v1 t2 r -->* tm_app v1 t2' r.
Proof.
  intros v1 t2 t2' r Hv H. induction H; eauto using multi, step.
Qed.

Lemma multi_protect : forall l t t',
  t -->* t' -> tm_protect l t -->* tm_protect l t'.
Proof.
  intros l t t' H. induction H; eauto using multi, step.
Qed.

Lemma multi_pair1 : forall t1 t1' t2 k,
  t1 -->* t1' -> tm_pair t1 t2 k -->* tm_pair t1' t2 k.
Proof.
  intros t1 t1' t2 k H. induction H; eauto using multi, step.
Qed.

Lemma multi_pair2 : forall v1 t2 t2' k,
  value v1 -> t2 -->* t2' -> tm_pair v1 t2 k -->* tm_pair v1 t2' k.
Proof.
  intros v1 t2 t2' k Hv H. induction H; eauto using multi, step.
Qed.

Lemma multi_fst : forall t t' r,
  t -->* t' -> tm_fst t r -->* tm_fst t' r.
Proof.
  intros t t' r H. induction H; eauto using multi, step.
Qed.

Lemma multi_snd : forall t t' r,
  t -->* t' -> tm_snd t r -->* tm_snd t' r.
Proof.
  intros t t' r H. induction H; eauto using multi, step.
Qed.

Lemma multi_inl : forall t t' k,
  t -->* t' -> tm_inl t k -->* tm_inl t' k.
Proof.
  intros t t' k H. induction H; eauto using multi, step.
Qed.

Lemma multi_inr : forall t t' k,
  t -->* t' -> tm_inr t k -->* tm_inr t' k.
Proof.
  intros t t' k H. induction H; eauto using multi, step.
Qed.

Lemma multi_case : forall t t' b1 b2 r,
  t -->* t' -> tm_case t b1 b2 r -->* tm_case t' b1 b2 r.
Proof.
  intros t t' b1 b2 r H. induction H; eauto using multi, step.
Qed.

Lemma multi_succ : forall t t' r,
  t -->* t' -> tm_succ t r -->* tm_succ t' r.
Proof.
  intros t t' r H. induction H; eauto using multi, step.
Qed.

Lemma multi_rec_arg : forall n n' b s r,
  n -->* n' -> tm_natrec n b s r -->* tm_natrec n' b s r.
Proof.
  intros n n' b s r H. induction H; eauto using multi, step.
Qed.

Lemma multi_rec_base : forall n k b b' s r,
  b -->* b' -> tm_natrec (tm_nat n k) b s r -->*
  tm_natrec (tm_nat n k) b' s r.
Proof.
  intros n k b b' s r H. induction H; eauto using multi, step.
Qed.

Lemma multi_rec_step : forall n k b s s' r,
  value b -> s -->* s' -> tm_natrec (tm_nat n k) b s r -->*
  tm_natrec (tm_nat n k) b s' r.
Proof.
  intros n k b s s' r Hb H. induction H; eauto using multi, step.
Qed.

Definition context_extends (Gamma Delta : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
              lookup_context x Delta = Some T.

Lemma context_extends_update : forall Gamma Delta x T,
  context_extends Gamma Delta ->
  context_extends (update Gamma x T) (update Delta x T).
Proof.
  intros Gamma Delta x T H y U Hy. simpl in *.
  destruct (Nat.eqb y x); auto.
Qed.

Lemma typing_context_extends : forall Gamma t T,
  has_type Gamma t T -> forall Delta,
  context_extends Gamma Delta -> has_type Delta t T.
Proof.
  intros Gamma t T Htyp. induction Htyp; intros Delta Hext;
    eauto using has_type.
  - eapply T_Abs with (L := L); eauto.
    intros x Hx. apply H2; auto using context_extends_update.
  - eapply T_Case with (L := L); eauto.
    + intros x Hx. apply H1; auto using context_extends_update.
    + intros x Hx. apply H3; auto using context_extends_update.
Qed.

Lemma typing_empty_any : forall t T Gamma,
  has_type empty t T -> has_type Gamma t T.
Proof.
  intros t T Gamma H. eapply typing_context_extends; eauto.
  intros x U Hlookup. discriminate Hlookup.
Qed.

Fixpoint remove_context (x : atom) (Gamma : context) : context :=
  match Gamma with
  | [] => []
  | (y, T) :: Gamma' =>
      if Nat.eqb x y then remove_context x Gamma'
      else (y, T) :: remove_context x Gamma'
  end.

Lemma lookup_remove_other : forall Gamma x y,
  x <> y ->
  lookup_context y (remove_context x Gamma) = lookup_context y Gamma.
Proof.
  induction Gamma as [|[z T] Gamma IH]; intros x y Hxy; simpl; auto.
  destruct (Nat.eqb x z) eqn:Hxz.
  - apply Nat.eqb_eq in Hxz. subst z. simpl.
    destruct (Nat.eqb y x) eqn:Hyx.
    + apply Nat.eqb_eq in Hyx. congruence.
    + apply IH; auto.
  - simpl. destruct (Nat.eqb y z); auto.
Qed.

Lemma remove_context_update_other : forall Gamma x y T,
  x <> y ->
  remove_context x (update Gamma y T) =
  update (remove_context x Gamma) y T.
Proof.
  intros. simpl. destruct (Nat.eqb x y) eqn:Hxy.
  - apply Nat.eqb_eq in Hxy. congruence.
  - reflexivity.
Qed.

Lemma open_rec_lc : forall t j k u,
  lc_at j t -> j <= k -> open_rec k u t = t.
Proof.
  induction t; intros j k u Hlc Hle; simpl in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try (f_equal; eauto; fail);
    try reflexivity.
  - destruct (Nat.eqb k n) eqn:Hkn; auto.
    apply Nat.eqb_eq in Hkn. lia.
  - f_equal. eapply IHt; eauto. lia.
  - f_equal.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto; lia.
    + eapply IHt3; eauto; lia.
Qed.

Lemma subst_open_rec_fvar : forall t x u y k,
  x <> y -> locally_closed u ->
  subst x u (open_rec k (tm_fvar y) t) =
  open_rec k (tm_fvar y) (subst x u t).
Proof.
  induction t; intros x u y k Hxy Hlc; simpl;
    try (f_equal; eauto); auto.
  - destruct (Nat.eqb k n); simpl; auto.
    destruct (Nat.eqb x y) eqn:Hxyb; auto.
    apply Nat.eqb_eq in Hxyb. congruence.
  - destruct (Nat.eqb x a) eqn:Hxa; simpl; auto.
    apply Nat.eqb_eq in Hxa. subst a.
    symmetry. eapply open_rec_lc with (j := 0); eauto. lia.
Qed.

Lemma typing_subst : forall Gamma t U,
  has_type Gamma t U ->
  forall x v T,
    lookup_context x Gamma = Some T ->
    (forall Delta, has_type Delta v T) ->
    locally_closed v ->
    has_type (remove_context x Gamma) (subst x v t) U.
Proof.
  intros Gamma t U Htyp. induction Htyp;
    intros z v V Hz Hv Hlc; simpl in *;
    eauto using has_type.
  - destruct (Nat.eqb z x) eqn:Hzx.
    + apply Nat.eqb_eq in Hzx. subst x.
      assert (T = V) by congruence. subst T.
      apply Hv.
    + apply Nat.eqb_neq in Hzx.
      apply T_Var; auto.
      rewrite lookup_remove_other; auto.
  - eapply T_Abs with (L := z :: L); eauto.
    intros y Hy. simpl in Hy.
    assert (Hneq : z <> y) by (intro E; apply Hy; left; exact E).
    assert (Hfresh : ~ In y L) by (intro Hin; apply Hy; right; exact Hin).
    rewrite <- remove_context_update_other by exact Hneq.
    unfold open. rewrite <- subst_open_rec_fvar; auto.
    eapply H2; eauto. simpl. destruct (Nat.eqb z y) eqn:Hzy.
    + apply Nat.eqb_eq in Hzy. congruence.
    + exact Hz.
  - eapply T_Case with (L := z :: L); eauto.
    + intros y Hy. simpl in Hy.
      assert (Hneq : z <> y) by (intro E; apply Hy; left; exact E).
      assert (Hfresh : ~ In y L) by (intro Hin; apply Hy; right; exact Hin).
      rewrite <- remove_context_update_other by exact Hneq.
      unfold open. rewrite <- subst_open_rec_fvar; auto.
      eapply H1; eauto. simpl. destruct (Nat.eqb z y) eqn:Hzy.
      * apply Nat.eqb_eq in Hzy. congruence.
      * exact Hz.
    + intros y Hy. simpl in Hy.
      assert (Hneq : z <> y) by (intro E; apply Hy; left; exact E).
      assert (Hfresh : ~ In y L) by (intro Hin; apply Hy; right; exact Hin).
      rewrite <- remove_context_update_other by exact Hneq.
      unfold open. rewrite <- subst_open_rec_fvar; auto.
      eapply H3; eauto. simpl. destruct (Nat.eqb z y) eqn:Hzy.
      * apply Nat.eqb_eq in Hzy. congruence.
      * exact Hz.
Qed.

Lemma notin_append : forall (A B : list atom) x,
  ~ In x (A ++ B) -> ~ In x A /\ ~ In x B.
Proof.
  intros A B x H. split; intro Hin; apply H; apply in_or_app; auto.
Qed.

Lemma subst_fresh : forall t x u,
  ~ In x (fv t) -> subst x u t = t.
Proof.
  induction t; intros x u Hfresh; simpl in *;
    try (f_equal; eauto; fail); auto.
  - destruct (Nat.eqb x a) eqn:Hxa; auto.
    apply Nat.eqb_eq in Hxa. subst a. exfalso.
    apply Hfresh. simpl. auto.
  - apply notin_append in Hfresh. destruct Hfresh as [H1 H2].
    f_equal; eauto.
  - apply notin_append in Hfresh. destruct Hfresh as [H1 H2].
    f_equal; eauto.
  - apply notin_append in Hfresh. destruct Hfresh as [H1 H23].
    apply notin_append in H23. destruct H23 as [H2 H3].
    f_equal; eauto.
  - apply notin_append in Hfresh. destruct Hfresh as [H1 H23].
    apply notin_append in H23. destruct H23 as [H2 H3].
    f_equal; eauto.
Qed.

Lemma subst_open_rec : forall t x v u k,
  locally_closed v ->
  subst x v (open_rec k u t) =
  open_rec k (subst x v u) (subst x v t).
Proof.
  induction t; intros x v u k Hlc; simpl;
    try (f_equal; eauto); auto.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Nat.eqb x a) eqn:Hxa; simpl; auto.
    symmetry. eapply open_rec_lc with (j := 0); eauto. lia.
Qed.

Lemma subst_open_fresh : forall body x v,
  locally_closed v -> ~ In x (fv body) ->
  subst x v (open body (tm_fvar x)) = open body v.
Proof.
  intros body x v Hlc Hfresh. unfold open.
  rewrite subst_open_rec by exact Hlc. simpl.
  rewrite Nat.eqb_refl. rewrite subst_fresh by exact Hfresh.
  reflexivity.
Qed.

Lemma value_locally_closed : forall v,
  value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv; simpl; repeat split; auto.
Qed.

Lemma atom_list_bound : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (fold_right Nat.max 0 L)).
  intro Hin. pose proof (atom_list_bound L _ Hin). lia.
Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof.
  destruct T; destruct s as [r i]; destruct r, i; reflexivity.
Qed.

Inductive erased_typed : context -> tm -> ty -> Prop :=
  | E_Var : forall Gamma x T,
      lookup_context x Gamma = Some T -> wf_ty T ->
      erased_typed Gamma (tm_fvar x) T
  | E_Unit : forall Gamma,
      erased_typed Gamma (tm_unit public) (Ty_Unit public)
  | E_Abs : forall L Gamma A body B,
      wf_ty A ->
      (forall x, ~ In x L ->
         erased_typed (update Gamma x A) (open body (tm_fvar x)) B) ->
      erased_typed Gamma (tm_abs A body public) (Ty_Arrow A B public)
  | E_App : forall Gamma f a A B,
      erased_typed Gamma f (Ty_Arrow A B public) ->
      erased_typed Gamma a A ->
      erased_typed Gamma (tm_app f a Low) B
  | E_Pair : forall Gamma a b A B,
      erased_typed Gamma a A -> erased_typed Gamma b B ->
      erased_typed Gamma (tm_pair a b public) (Ty_Prod A B public)
  | E_Fst : forall Gamma t A B,
      erased_typed Gamma t (Ty_Prod A B public) ->
      erased_typed Gamma (tm_fst t Low) A
  | E_Snd : forall Gamma t A B,
      erased_typed Gamma t (Ty_Prod A B public) ->
      erased_typed Gamma (tm_snd t Low) B
  | E_Inl : forall Gamma t A B,
      erased_typed Gamma t A -> wf_ty B ->
      erased_typed Gamma (tm_inl t public) (Ty_Sum A B public)
  | E_Inr : forall Gamma t A B,
      wf_ty A -> erased_typed Gamma t B ->
      erased_typed Gamma (tm_inr t public) (Ty_Sum A B public)
  | E_Case : forall L Gamma t b1 b2 A B R,
      erased_typed Gamma t (Ty_Sum A B public) ->
      wf_ty A -> wf_ty B ->
      (forall x, ~ In x L ->
         erased_typed (update Gamma x A) (open b1 (tm_fvar x)) R) ->
      (forall x, ~ In x L ->
         erased_typed (update Gamma x B) (open b2 (tm_fvar x)) R) ->
      erased_typed Gamma (tm_case t b1 b2 Low) R
  | E_Nat : forall Gamma n,
      erased_typed Gamma (tm_nat n public) (Ty_Nat public)
  | E_Succ : forall Gamma t,
      erased_typed Gamma t (Ty_Nat public) ->
      erased_typed Gamma (tm_succ t Low) (Ty_Nat public)
  | E_NatRec : forall Gamma n b s R,
      erased_typed Gamma n (Ty_Nat public) ->
      erased_typed Gamma b R ->
      erased_typed Gamma s
        (Ty_Arrow (Ty_Nat public) (Ty_Arrow R R public) public) ->
      erased_typed Gamma (tm_natrec n b s Low) R.

Lemma erased_typed_to_has_type : forall Gamma t T,
  erased_typed Gamma t T -> has_type Gamma t T.
Proof.
  intros Gamma t T H. induction H.
  - apply T_Var; auto.
  - apply T_Unit. exact I.
  - eapply T_Abs with (L := L); eauto. exact I.
  - rewrite <- ty_protect_low.
    eapply T_App with (kappa := public); eauto. exact I.
  - eapply T_Pair; eauto. exact I.
  - rewrite <- ty_protect_low.
    eapply T_Fst with (kappa := public); eauto. exact I.
  - rewrite <- ty_protect_low.
    eapply T_Snd with (kappa := public); eauto. exact I.
  - eapply T_Inl; eauto. exact I.
  - eapply T_Inr; eauto. exact I.
  - rewrite <- ty_protect_low.
    eapply T_Case with (L := L) (kappa := public); eauto. exact I.
  - apply T_Nat. exact I.
  - rewrite <- ty_protect_low.
    eapply T_Succ with (k := public); eauto. exact I.
  - rewrite <- ty_protect_low.
    eapply T_NatRec with (k := public); eauto. exact I.
Qed.

Lemma typing_erase_strict : forall Gamma t T,
  has_type Gamma t T ->
  erased_typed (erase_context Gamma) (erase_security t) (erase_type T).
Proof.
  intros Gamma t T Htyp. induction Htyp; simpl in *.
  - apply E_Var; auto using lookup_erase_context, wf_erase_type.
  - apply E_Unit.
  - eapply E_Abs with (L := L); eauto using wf_erase_type.
    intros x Hx. rewrite <- erase_context_update.
    change (tm_fvar x) with (erase_security (tm_fvar x)).
    rewrite <- erase_open. apply H2; assumption.
  - rewrite erase_type_protect. eapply E_App; eauto.
  - eapply E_Pair; eauto.
  - rewrite erase_type_protect. eapply E_Fst; eauto.
  - rewrite erase_type_protect. eapply E_Snd; eauto.
  - eapply E_Inl; eauto using wf_erase_type.
  - eapply E_Inr; eauto using wf_erase_type.
  - rewrite erase_type_protect.
    eapply E_Case with (L := L); eauto using wf_erase_type.
    + intros x Hx. rewrite <- erase_context_update.
      change (tm_fvar x) with (erase_security (tm_fvar x)).
      rewrite <- erase_open. apply H1; assumption.
    + intros x Hx. rewrite <- erase_context_update.
      change (tm_fvar x) with (erase_security (tm_fvar x)).
      rewrite <- erase_open. apply H3; assumption.
  - rewrite erase_type_protect. exact IHHtyp.
  - match goal with Hsub : subtype _ _ |- _ =>
      rewrite (subtype_erase_eq _ _ Hsub) in IHHtyp end.
    exact IHHtyp.
  - apply E_Nat.
  - apply E_Succ. exact IHHtyp.
  - rewrite erase_type_protect. eapply E_NatRec; eauto.
Qed.

Lemma erased_typed_context_extends : forall Gamma t T,
  erased_typed Gamma t T -> forall Delta,
  context_extends Gamma Delta -> erased_typed Delta t T.
Proof.
  intros Gamma t T Htyp. induction Htyp; intros Delta Hext;
    eauto using erased_typed.
  - eapply E_Abs with (L := L); eauto.
    intros x Hx. apply H1; auto using context_extends_update.
  - eapply E_Case with (L := L); eauto.
    + intros x Hx. apply H2; auto using context_extends_update.
    + intros x Hx. apply H4; auto using context_extends_update.
Qed.

Lemma erased_typed_empty_any : forall t T Gamma,
  erased_typed empty t T -> erased_typed Gamma t T.
Proof.
  intros t T Gamma H. eapply erased_typed_context_extends; eauto.
  intros x U Hlookup. discriminate Hlookup.
Qed.

Lemma erased_typed_subst : forall Gamma t U,
  erased_typed Gamma t U ->
  forall x v T,
    lookup_context x Gamma = Some T ->
    (forall Delta, erased_typed Delta v T) ->
    locally_closed v ->
    erased_typed (remove_context x Gamma) (subst x v t) U.
Proof.
  intros Gamma t U Htyp. induction Htyp;
    intros z v V Hz Hv Hlc; simpl in *;
    eauto using erased_typed.
  - destruct (Nat.eqb z x) eqn:Hzx.
    + apply Nat.eqb_eq in Hzx. subst x.
      assert (T = V) by congruence. subst T. apply Hv.
    + apply Nat.eqb_neq in Hzx.
      apply E_Var; auto.
      rewrite lookup_remove_other; auto.
  - eapply E_Abs with (L := z :: L); eauto.
    intros y Hy. simpl in Hy.
    assert (Hneq : z <> y) by (intro E; apply Hy; left; exact E).
    assert (Hfresh : ~ In y L) by (intro Hin; apply Hy; right; exact Hin).
    rewrite <- remove_context_update_other by exact Hneq.
    unfold open. rewrite <- subst_open_rec_fvar; auto.
    eapply H1; eauto. simpl. destruct (Nat.eqb z y) eqn:Hzy.
    + apply Nat.eqb_eq in Hzy. congruence.
    + exact Hz.
  - eapply E_Case with (L := z :: L); eauto.
    + intros y Hy. simpl in Hy.
      assert (Hneq : z <> y) by (intro E; apply Hy; left; exact E).
      assert (Hfresh : ~ In y L) by (intro Hin; apply Hy; right; exact Hin).
      rewrite <- remove_context_update_other by exact Hneq.
      unfold open. rewrite <- subst_open_rec_fvar; auto.
      eapply H2; eauto. simpl. destruct (Nat.eqb z y) eqn:Hzy.
      * apply Nat.eqb_eq in Hzy. congruence.
      * exact Hz.
    + intros y Hy. simpl in Hy.
      assert (Hneq : z <> y) by (intro E; apply Hy; left; exact E).
      assert (Hfresh : ~ In y L) by (intro Hin; apply Hy; right; exact Hin).
      rewrite <- remove_context_update_other by exact Hneq.
      unfold open. rewrite <- subst_open_rec_fvar; auto.
      eapply H4; eauto. simpl. destruct (Nat.eqb z y) eqn:Hzy.
      * apply Nat.eqb_eq in Hzy. congruence.
      * exact Hz.
Qed.

Lemma erased_typed_open : forall L body A B v,
  (forall x, ~ In x L ->
     erased_typed (update empty x A) (open body (tm_fvar x)) B) ->
  erased_typed empty v A -> value v ->
  erased_typed empty (open body v) B.
Proof.
  intros L body A B v Hbody Hv Hvalue.
  destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
  apply notin_append in Hfresh. destruct Hfresh as [HL Hfv].
  specialize (Hbody x HL).
  assert (Hlookup : lookup_context x (update empty x A) = Some A)
    by (simpl; rewrite Nat.eqb_refl; reflexivity).
  pose proof (erased_typed_subst _ _ _ Hbody x v A Hlookup
    (fun Delta => erased_typed_empty_any _ _ Delta Hv)
    (value_locally_closed _ Hvalue)) as Hsub.
  simpl in Hsub. rewrite Nat.eqb_refl in Hsub.
  rewrite subst_open_fresh in Hsub
    by (auto using value_locally_closed).
  exact Hsub.
Qed.

Lemma erased_typed_unroll : forall n b s R,
  erased_typed empty b R ->
  erased_typed empty s
    (Ty_Arrow (Ty_Nat public) (Ty_Arrow R R public) public) ->
  erased_typed empty (natrec_unroll n b s Low) R.
Proof.
  induction n as [|n IH]; intros b s R Hb Hs; simpl; auto.
  eapply E_App.
  - eapply E_App; eauto using E_Nat.
  - eapply IH; eauto.
Qed.

Lemma erase_natrec_unroll : forall n b s r,
  erase_security (natrec_unroll n b s r) =
  natrec_unroll n (erase_security b) (erase_security s) Low.
Proof.
  induction n; intros b s r; simpl; auto.
  rewrite IHn. reflexivity.
Qed.

Lemma erased_typed_step : forall t t',
  t --> t' -> forall T,
  erased_typed empty (erase_security t) T ->
  erased_typed empty (erase_security t') T.
Proof.
  intros t t' Hstep. induction Hstep; intros R Htyp; simpl in *;
    try solve [inversion Htyp; subst; eauto using erased_typed].
  - inversion Htyp; subst.
    match goal with Habs : erased_typed empty (tm_abs _ _ public) _ |- _ =>
      inversion Habs; subst end.
    rewrite erase_open.
    eapply erased_typed_open; eauto using erase_value.
  - inversion Htyp; subst.
    match goal with Hp : erased_typed empty (tm_pair _ _ public) _ |- _ =>
      inversion Hp; subst end.
    assumption.
  - inversion Htyp; subst.
    match goal with Hp : erased_typed empty (tm_pair _ _ public) _ |- _ =>
      inversion Hp; subst end.
    assumption.
  - inversion Htyp; subst.
    match goal with Hi : erased_typed empty (tm_inl _ public) _ |- _ =>
      inversion Hi; subst end.
    rewrite erase_open.
    eapply erased_typed_open; eauto using erase_value.
  - inversion Htyp; subst.
    match goal with Hi : erased_typed empty (tm_inr _ public) _ |- _ =>
      inversion Hi; subst end.
    rewrite erase_open.
    eapply erased_typed_open; eauto using erase_value.
  - rewrite erase_protect_value. exact Htyp.
  - rewrite erase_natrec_unroll.
    inversion Htyp; subst. eapply erased_typed_unroll; eauto.
Qed.

Lemma erased_typed_multi : forall t t' T,
  t -->* t' -> erased_typed empty (erase_security t) T ->
  erased_typed empty (erase_security t') T.
Proof.
  intros t t' T Hmulti. induction Hmulti; intros Htyp; auto.
  apply IHHmulti. eapply erased_typed_step; eauto.
Qed.

Lemma source_value_underlying : forall t v T,
  has_type empty t T -> evaluates t v -> underlying_typed T v.
Proof.
  intros t v T Htyp [Hmulti _]. unfold underlying_typed.
  apply erased_typed_to_has_type.
  eapply erased_typed_multi; eauto.
  exact (typing_erase_strict empty t T Htyp).
Qed.

Fixpoint close_term (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_unit k => tm_unit k
  | tm_abs A body k => tm_abs A (close_term sigma body) k
  | tm_app f a r => tm_app (close_term sigma f) (close_term sigma a) r
  | tm_pair a b k => tm_pair (close_term sigma a) (close_term sigma b) k
  | tm_fst t r => tm_fst (close_term sigma t) r
  | tm_snd t r => tm_snd (close_term sigma t) r
  | tm_inl t k => tm_inl (close_term sigma t) k
  | tm_inr t k => tm_inr (close_term sigma t) k
  | tm_case t b1 b2 r =>
      tm_case (close_term sigma t) (close_term sigma b1)
        (close_term sigma b2) r
  | tm_protect l t => tm_protect l (close_term sigma t)
  | tm_nat n k => tm_nat n k
  | tm_succ t r => tm_succ (close_term sigma t) r
  | tm_natrec n b s r =>
      tm_natrec (close_term sigma n) (close_term sigma b)
        (close_term sigma s) r
  end.

Definition sigma_update (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then v else sigma y.

Lemma close_term_update_fresh : forall t sigma x v,
  ~ In x (fv t) ->
  close_term (sigma_update sigma x v) t = close_term sigma t.
Proof.
  induction t; intros sigma x v Hfresh; simpl in *;
    repeat match goal with H : ~ In _ (_ ++ _) |- _ =>
      apply notin_append in H; destruct H end;
    try (f_equal; eauto); auto.
  unfold sigma_update. destruct (Nat.eqb a x) eqn:Hax; auto.
  apply Nat.eqb_eq in Hax. subst a. exfalso.
  apply Hfresh. simpl. auto.
Qed.

Lemma close_term_open_rec : forall t sigma u k,
  (forall x, locally_closed (sigma x)) ->
  close_term sigma (open_rec k u t) =
  open_rec k (close_term sigma u) (close_term sigma t).
Proof.
  induction t; intros sigma u k Hlc; simpl;
    try (f_equal; eauto); auto.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. eapply open_rec_lc with (j := 0); [apply Hlc | lia].
Qed.

Lemma close_term_open : forall t sigma u,
  (forall x, locally_closed (sigma x)) ->
  close_term sigma (open t u) =
  open (close_term sigma t) (close_term sigma u).
Proof. intros; apply close_term_open_rec; auto. Qed.

Lemma close_term_open_update : forall body sigma x v,
  ~ In x (fv body) ->
  (forall y, locally_closed (sigma y)) ->
  locally_closed v ->
  close_term (sigma_update sigma x v) (open body (tm_fvar x)) =
  open (close_term sigma body) v.
Proof.
  intros body sigma x v Hfresh Hlc Hv.
  rewrite close_term_open by
    (intro y; unfold sigma_update; destruct (Nat.eqb y x); auto).
  rewrite close_term_update_fresh by exact Hfresh.
  unfold sigma_update. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma close_term_erase : forall t sigma,
  erase_security (close_term sigma t) =
  close_term (fun x => erase_security (sigma x)) (erase_security t).
Proof.
  induction t; intros sigma; simpl; try (f_equal; eauto); auto.
Qed.

Lemma erase_type_idem : forall T,
  erase_type (erase_type T) = erase_type T.
Proof. induction T; simpl; congruence. Qed.

Lemma erase_security_idem : forall t,
  erase_security (erase_security t) = erase_security t.
Proof.
  induction t; simpl;
    rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3, ?erase_type_idem;
    reflexivity.
Qed.

Definition erased_env_typed (Gamma Delta : context) (sigma : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
              erased_typed Delta (sigma x) T.

Lemma lookup_notin_dom : forall Gamma x,
  ~ In x (map fst Gamma) -> lookup_context x Gamma = None.
Proof.
  induction Gamma as [|[y T] Gamma IH]; intros x Hnot; simpl in *; auto.
  assert (Hxy : x <> y) by (intro E; subst; apply Hnot; simpl; auto).
  destruct (Nat.eqb x y) eqn:Hb.
  - apply Nat.eqb_eq in Hb. congruence.
  - apply IH. intro Hin. apply Hnot. simpl. auto.
Qed.

Lemma context_extends_fresh_cons : forall Delta x A,
  lookup_context x Delta = None ->
  context_extends Delta (update Delta x A).
Proof.
  intros Delta x A Hnone y T Hy. simpl.
  destruct (Nat.eqb y x) eqn:Hxy; auto.
  apply Nat.eqb_eq in Hxy. subst. congruence.
Qed.

Lemma erased_env_typed_extend : forall Gamma Delta sigma x A,
  erased_env_typed Gamma Delta sigma -> wf_ty A ->
  lookup_context x Delta = None ->
  erased_env_typed (update Gamma x A) (update Delta x A)
    (sigma_update sigma x (tm_fvar x)).
Proof.
  intros Gamma Delta sigma x A Henv Hwf Hnone y T Hy.
  unfold sigma_update. simpl in *.
  destruct (Nat.eqb y x) eqn:Hyx.
  - inversion Hy; subst. apply E_Var; auto.
    simpl. rewrite Nat.eqb_refl. reflexivity.
  - eapply erased_typed_context_extends.
    + apply Henv. exact Hy.
    + apply context_extends_fresh_cons. exact Hnone.
Qed.

Lemma sigma_update_lc : forall sigma x v,
  (forall y, locally_closed (sigma y)) -> locally_closed v ->
  forall y, locally_closed (sigma_update sigma x v y).
Proof.
  intros sigma x v Hsigma Hv y. unfold sigma_update.
  destruct (Nat.eqb y x); auto.
Qed.

Lemma erased_typed_close : forall Gamma t T,
  erased_typed Gamma t T ->
  forall Delta sigma,
    erased_env_typed Gamma Delta sigma ->
    (forall x, locally_closed (sigma x)) ->
    erased_typed Delta (close_term sigma t) T.
Proof.
  intros Gamma t T Htyp. induction Htyp;
    intros Delta sigma Henv Hlc; simpl;
    try solve [econstructor; eauto].
  - apply Henv. exact H.
  - eapply E_Abs with (L := L ++ fv body ++ map fst Delta); eauto.
    intros x Hx.
    apply notin_append in Hx. destruct Hx as [HL Htail].
    apply notin_append in Htail. destruct Htail as [Hbody Hdom].
    rewrite <- (close_term_open_update body sigma x (tm_fvar x)); eauto.
    eapply H1; eauto using sigma_update_lc.
    eapply erased_env_typed_extend; eauto using lookup_notin_dom.
    apply sigma_update_lc; auto. simpl; exact I.
    simpl; exact I.
  - eapply E_Case with
      (L := L ++ fv b1 ++ fv b2 ++ map fst Delta); eauto.
    + intros x Hx.
      apply notin_append in Hx. destruct Hx as [HL Htail].
      apply notin_append in Htail. destruct Htail as [Hb1 Htail].
      apply notin_append in Htail. destruct Htail as [Hb2 Hdom].
      rewrite <- (close_term_open_update b1 sigma x (tm_fvar x)); eauto.
      eapply H2; eauto using sigma_update_lc.
      eapply erased_env_typed_extend; eauto using lookup_notin_dom.
      apply sigma_update_lc; auto. simpl; exact I.
      simpl; exact I.
    + intros x Hx.
      apply notin_append in Hx. destruct Hx as [HL Htail].
      apply notin_append in Htail. destruct Htail as [Hb1 Htail].
      apply notin_append in Htail. destruct Htail as [Hb2 Hdom].
      rewrite <- (close_term_open_update b2 sigma x (tm_fvar x)); eauto.
      eapply H4; eauto using sigma_update_lc.
      eapply erased_env_typed_extend; eauto using lookup_notin_dom.
      apply sigma_update_lc; auto. simpl; exact I.
      simpl; exact I.
Qed.

Definition related_env (observer : label) (Gamma : context)
    (sigma1 sigma2 : atom -> tm) : Prop :=
  (forall x T, lookup_context x Gamma = Some T ->
     value_relation observer T (sigma1 x) (sigma2 x)) /\
  (forall x, locally_closed (sigma1 x) /\ locally_closed (sigma2 x)).

Lemma relation_strict_left : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  erased_typed empty (erase_security v1) (erase_type T).
Proof.
  intros observer T v1 v2 Hrel.
  assert (Htyp : underlying_typed T v1)
    by (destruct T; simpl in Hrel; tauto).
  unfold underlying_typed in Htyp.
  pose proof (typing_erase_strict empty _ _ Htyp) as Hstrict.
  simpl in Hstrict.
  rewrite erase_security_idem, erase_type_idem in Hstrict.
  exact Hstrict.
Qed.

Lemma relation_strict_right : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  erased_typed empty (erase_security v2) (erase_type T).
Proof.
  intros observer T v1 v2 Hrel.
  assert (Htyp : underlying_typed T v2)
    by (destruct T; simpl in Hrel; tauto).
  unfold underlying_typed in Htyp.
  pose proof (typing_erase_strict empty _ _ Htyp) as Hstrict.
  simpl in Hstrict.
  rewrite erase_security_idem, erase_type_idem in Hstrict.
  exact Hstrict.
Qed.

Lemma related_env_close_underlying : forall observer Gamma t T sigma1 sigma2,
  has_type Gamma t T -> related_env observer Gamma sigma1 sigma2 ->
  underlying_typed T (close_term sigma1 t) /\
  underlying_typed T (close_term sigma2 t).
Proof.
  intros observer Gamma t T sigma1 sigma2 Htyp [Hrel Hlc].
  pose proof (typing_erase_strict _ _ _ Htyp) as Hstrict.
  split; unfold underlying_typed; rewrite close_term_erase;
    apply erased_typed_to_has_type.
  - eapply erased_typed_close; eauto.
    + intros x U Hlookup.
      destruct (lookup_erase_context_inv _ _ _ Hlookup)
        as [V [HV ->]].
      eapply relation_strict_left. apply Hrel. exact HV.
    + intros x. apply lc_at_erase. apply (proj1 (Hlc x)).
  - eapply erased_typed_close; eauto.
    + intros x U Hlookup.
      destruct (lookup_erase_context_inv _ _ _ Hlookup)
        as [V [HV ->]].
      eapply relation_strict_right. apply Hrel. exact HV.
    + intros x. apply lc_at_erase. apply (proj2 (Hlc x)).
Qed.

Lemma protect_value_is_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l Hv. inversion Hv; subst; simpl; try constructor; auto.
Qed.

Inductive big_eval : tm -> tm -> Prop :=
  | BE_Value : forall v, value v -> big_eval v v
  | BE_App : forall f a A body k va w r,
      big_eval f (tm_abs A body k) -> big_eval a va ->
      flows_to k.(reader) r -> big_eval (open body va) w ->
      big_eval (tm_app f a r) (protect_value w k.(indirect_reader))
  | BE_Pair : forall a b va vb k,
      big_eval a va -> big_eval b vb ->
      big_eval (tm_pair a b k) (tm_pair va vb k)
  | BE_Fst : forall t va vb k w r,
      big_eval t (tm_pair va vb k) ->
      flows_to k.(reader) r -> big_eval va w ->
      big_eval (tm_fst t r) (protect_value w k.(indirect_reader))
  | BE_Snd : forall t va vb k w r,
      big_eval t (tm_pair va vb k) ->
      flows_to k.(reader) r -> big_eval vb w ->
      big_eval (tm_snd t r) (protect_value w k.(indirect_reader))
  | BE_Inl : forall t v k,
      big_eval t v -> big_eval (tm_inl t k) (tm_inl v k)
  | BE_Inr : forall t v k,
      big_eval t v -> big_eval (tm_inr t k) (tm_inr v k)
  | BE_CaseLeft : forall t va k b1 b2 w r,
      big_eval t (tm_inl va k) -> flows_to k.(reader) r ->
      big_eval (open b1 va) w ->
      big_eval (tm_case t b1 b2 r) (protect_value w k.(indirect_reader))
  | BE_CaseRight : forall t va k b1 b2 w r,
      big_eval t (tm_inr va k) -> flows_to k.(reader) r ->
      big_eval (open b2 va) w ->
      big_eval (tm_case t b1 b2 r) (protect_value w k.(indirect_reader))
  | BE_Protect : forall l t v,
      big_eval t v -> big_eval (tm_protect l t) (protect_value v l)
  | BE_Succ : forall t n k r,
      big_eval t (tm_nat n k) -> flows_to k.(reader) r ->
      big_eval (tm_succ t r)
        (protect_value (tm_nat (S n) public) k.(indirect_reader))
  | BE_NatRec : forall n b s m k vb vs w r,
      big_eval n (tm_nat m k) -> big_eval b vb -> big_eval s vs ->
      flows_to k.(reader) r ->
      big_eval (natrec_unroll m vb vs r) w ->
      big_eval (tm_natrec n b s r)
        (protect_value w k.(indirect_reader)).

Lemma big_eval_value : forall t v,
  big_eval t v -> value v.
Proof.
  intros t v H. induction H; eauto using value, protect_value_is_value.
Qed.

Lemma big_eval_value_identity : forall v w,
  value v -> big_eval v w -> v = w.
Proof.
  intros v w Hv Hbe. induction Hbe; auto;
    inversion Hv; subst; f_equal; eauto.
Qed.

Lemma big_eval_sound : forall t v,
  big_eval t v -> evaluates t v.
Proof.
  intros t v Hbe. induction Hbe; unfold evaluates in *.
  - split; [constructor | assumption].
  - destruct IHHbe1 as [Hf _]. destruct IHHbe2 as [Ha _].
    destruct IHHbe3 as [Hb _]. split.
    + eapply multi_trans. apply multi_app1. exact Hf.
      eapply multi_trans. apply multi_app2;
        eauto using big_eval_value, value.
      eapply multi_step.
      * apply ST_AppAbs; eauto using big_eval_value, value.
      * eapply multi_trans. apply multi_protect. exact Hb.
        eapply multi_step.
        -- apply ST_ProtectValue. eauto using big_eval_value.
        -- apply multi_refl.
    + apply protect_value_is_value. eauto using big_eval_value.
  - destruct IHHbe1 as [Ha _]. destruct IHHbe2 as [Hb _]. split.
    + eapply multi_trans. apply multi_pair1. exact Ha.
      apply multi_pair2; eauto using big_eval_value.
    + constructor; eauto using big_eval_value.
  - destruct IHHbe1 as [Ht _]. destruct IHHbe2 as [Hw _]. split.
    + eapply multi_trans. apply multi_fst. exact Ht.
      eapply multi_step.
      * apply ST_FstPair; auto.
        all: pose proof (big_eval_value _ _ Hbe1) as Hpv;
          inversion Hpv; auto.
      * eapply multi_trans. apply multi_protect. exact Hw.
        eapply multi_step.
        -- apply ST_ProtectValue. eauto using big_eval_value.
        -- apply multi_refl.
    + apply protect_value_is_value. eauto using big_eval_value.
  - destruct IHHbe1 as [Ht _]. destruct IHHbe2 as [Hw _]. split.
    + eapply multi_trans. apply multi_snd. exact Ht.
      eapply multi_step.
      * apply ST_SndPair; auto.
        all: pose proof (big_eval_value _ _ Hbe1) as Hpv;
          inversion Hpv; auto.
      * eapply multi_trans. apply multi_protect. exact Hw.
        eapply multi_step.
        -- apply ST_ProtectValue. eauto using big_eval_value.
        -- apply multi_refl.
    + apply protect_value_is_value. eauto using big_eval_value.
  - destruct IHHbe as [Ht _]. split.
    + apply multi_inl. exact Ht.
    + constructor. eauto using big_eval_value.
  - destruct IHHbe as [Ht _]. split.
    + apply multi_inr. exact Ht.
    + constructor. eauto using big_eval_value.
  - destruct IHHbe1 as [Ht _]. destruct IHHbe2 as [Hw _]. split.
    + eapply multi_trans. apply multi_case. exact Ht.
      eapply multi_step.
      * apply ST_CaseLeft; auto.
        pose proof (big_eval_value _ _ Hbe1) as Hiv.
        inversion Hiv; auto.
      * eapply multi_trans. apply multi_protect. exact Hw.
        eapply multi_step.
        -- apply ST_ProtectValue. eauto using big_eval_value.
        -- apply multi_refl.
    + apply protect_value_is_value. eauto using big_eval_value.
  - destruct IHHbe1 as [Ht _]. destruct IHHbe2 as [Hw _]. split.
    + eapply multi_trans. apply multi_case. exact Ht.
      eapply multi_step.
      * apply ST_CaseRight; auto.
        pose proof (big_eval_value _ _ Hbe1) as Hiv.
        inversion Hiv; auto.
      * eapply multi_trans. apply multi_protect. exact Hw.
        eapply multi_step.
        -- apply ST_ProtectValue. eauto using big_eval_value.
        -- apply multi_refl.
    + apply protect_value_is_value. eauto using big_eval_value.
  - destruct IHHbe as [Ht _]. split.
    + eapply multi_trans. apply multi_protect. exact Ht.
      eapply multi_step.
      * apply ST_ProtectValue. eauto using big_eval_value.
      * apply multi_refl.
    + apply protect_value_is_value. eauto using big_eval_value.
  - destruct IHHbe as [Ht _]. split.
    + eapply multi_trans. apply multi_succ. exact Ht.
      eapply multi_step.
      * apply ST_SuccNat. assumption.
      * eapply multi_step.
        -- apply ST_ProtectValue. constructor.
        -- apply multi_refl.
    + apply protect_value_is_value. constructor.
  - destruct IHHbe1 as [Hn _]. destruct IHHbe2 as [Hb _].
    destruct IHHbe3 as [Hs _]. destruct IHHbe4 as [Hu _]. split.
    + eapply multi_trans. apply multi_rec_arg. exact Hn.
      eapply multi_trans. apply multi_rec_base. exact Hb.
      eapply multi_trans. apply multi_rec_step;
        eauto using big_eval_value.
      eapply multi_step.
      * apply ST_RecUnroll; eauto using big_eval_value.
      * eapply multi_trans. apply multi_protect. exact Hu.
        eapply multi_step.
        -- apply ST_ProtectValue. eauto using big_eval_value.
        -- apply multi_refl.
    + apply protect_value_is_value. eauto using big_eval_value.
Qed.

Lemma big_eval_step_back : forall t t',
  t --> t' -> forall v, big_eval t' v -> big_eval t v.
Proof.
  intros t t' Hstep. induction Hstep; intros w Hbe;
    try solve [match goal with
      Hv : value ?v, Hb : big_eval (protect_value ?v ?l) ?w |- _ =>
        pose proof (big_eval_value_identity _ _
          (protect_value_is_value v l Hv) Hb) as Heq;
        subst w; apply BE_Protect; apply BE_Value; exact Hv
      end];
    inversion Hbe; subst; eauto using big_eval;
    try solve [match goal with H : value (tm_app _ _ _) |- _ => inversion H end];
    try solve [match goal with H : value (tm_fst _ _) |- _ => inversion H end];
    try solve [match goal with H : value (tm_snd _ _) |- _ => inversion H end];
    try solve [match goal with H : value (tm_case _ _ _ _) |- _ => inversion H end];
    try solve [match goal with H : value (tm_protect _ _) |- _ => inversion H end];
    try solve [match goal with H : value (tm_succ _ _) |- _ => inversion H end];
    try solve [match goal with H : value (tm_natrec _ _ _ _) |- _ => inversion H end].
  - match goal with Hpv : value (tm_pair _ _ _) |- _ => inversion Hpv; subst end.
    apply BE_Pair.
    + apply IHHstep. apply BE_Value. assumption.
    + apply BE_Value. assumption.
  - match goal with Hpv : value (tm_pair _ _ _) |- _ => inversion Hpv; subst end.
    apply BE_Pair.
    + apply BE_Value. assumption.
    + apply IHHstep. apply BE_Value. assumption.
  - match goal with Hiv : value (tm_inl _ _) |- _ => inversion Hiv; subst end.
    apply BE_Inl. apply IHHstep. apply BE_Value. assumption.
  - match goal with Hiv : value (tm_inr _ _) |- _ => inversion Hiv; subst end.
    apply BE_Inr. apply IHHstep. apply BE_Value. assumption.
  - assert (Heq : v = tm_nat (S n) public).
    { symmetry. eapply big_eval_value_identity; eauto using value. }
    subst v. apply BE_Succ; eauto using big_eval, value.
  - eapply BE_NatRec; eauto using big_eval, value.
Qed.

Lemma big_eval_complete : forall t v,
  evaluates t v -> big_eval t v.
Proof.
  intros t v [Hmulti Hv]. induction Hmulti.
  - apply BE_Value. exact Hv.
  - eapply big_eval_step_back; eauto.
Qed.

Lemma big_eval_pair_inv : forall a b k v,
  big_eval (tm_pair a b k) v ->
  exists va vb,
    v = tm_pair va vb k /\ big_eval a va /\ big_eval b vb.
Proof.
  intros a b k v H. inversion H; subst.
  - match goal with Hv : value (tm_pair _ _ _) |- _ =>
      inversion Hv; subst end.
    exists a, b. repeat split; eauto using big_eval.
  - exists va, vb. repeat split; auto.
Qed.

Lemma big_eval_inl_inv : forall t k v,
  big_eval (tm_inl t k) v ->
  exists u, v = tm_inl u k /\ big_eval t u.
Proof.
  intros t k v H. inversion H; subst.
  - match goal with Hv : value (tm_inl _ _) |- _ =>
      inversion Hv; subst end.
    exists t. split; eauto using big_eval.
  - exists v0. split; auto.
Qed.

Lemma big_eval_inr_inv : forall t k v,
  big_eval (tm_inr t k) v ->
  exists u, v = tm_inr u k /\ big_eval t u.
Proof.
  intros t k v H. inversion H; subst.
  - match goal with Hv : value (tm_inr _ _) |- _ =>
      inversion Hv; subst end.
    exists t. split; eauto using big_eval.
  - exists v0. split; auto.
Qed.

Lemma big_eval_app_abs_inv : forall A body k a r w,
  value (tm_abs A body k) -> value a ->
  big_eval (tm_app (tm_abs A body k) a r) w ->
  exists u, big_eval (open body a) u /\
    w = protect_value u k.(indirect_reader).
Proof.
  intros A body k a r w Habs Ha Hbe.
  inversion Hbe; subst;
    try solve [match goal with H : value (tm_app _ _ _) |- _ =>
      inversion H end].
  match goal with Hf : big_eval (tm_abs A body k) (tm_abs _ _ _) |- _ =>
    pose proof (big_eval_value_identity _ _ Habs Hf) as Ef;
    inversion Ef; subst end.
  match goal with Harg : big_eval a _ |- _ =>
    pose proof (big_eval_value_identity _ _ Ha Harg) as Ea;
    subst end.
  eexists; split; eauto.
Qed.

Lemma underlying_typed_evaluates : forall t v T,
  underlying_typed T t -> evaluates t v -> underlying_typed T v.
Proof.
  intros t v T Htyp [Hmulti _]. unfold underlying_typed in *.
  pose proof (typing_erase_strict empty _ _ Htyp) as Hstrict.
  simpl in Hstrict.
  rewrite erase_security_idem, erase_type_idem in Hstrict.
  apply erased_typed_to_has_type.
  eapply erased_typed_multi; eauto.
Qed.

Lemma value_relation_opaque : forall observer T v1 v2,
  value v1 -> value v2 ->
  underlying_typed T v1 -> underlying_typed T v2 ->
  ~ flows_to (security_of T).(indirect_reader) observer ->
  value_relation observer T v1 v2.
Proof.
  intros observer T v1 v2 Hv1 Hv2 Ht1 Ht2 Hhidden.
  destruct T; simpl; repeat split; auto; contradiction.
Qed.

Lemma value_relation_values : forall observer T v1 v2,
  value_relation observer T v1 v2 -> value v1 /\ value v2.
Proof.
  intros observer T v1 v2 H. destruct T; simpl in H; tauto.
Qed.

Lemma underlying_subtype : forall T U t,
  subtype T U -> underlying_typed T t -> underlying_typed U t.
Proof.
  intros T U t Hsub Htyp. unfold underlying_typed in *.
  rewrite <- (subtype_erase_eq _ _ Hsub). exact Htyp.
Qed.

Lemma relation_subtype : forall T U,
  subtype T U -> forall observer v1 v2,
  value_relation observer T v1 v2 ->
  value_relation observer U v1 v2.
Proof.
  intros T U Hsub. induction Hsub;
    intros observer v1 v2 Hrel.
  - simpl in *. destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try assumption;
      try (unfold underlying_typed in *; simpl in *; assumption).
    intros Hflow. apply Hshape.
    eapply flows_to_trans; [apply (proj2 H1) | exact Hflow].
  - simpl in *. destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    assert (Hsu : subtype (Ty_Sum T1 T2 kappa1)
                             (Ty_Sum U1 U2 kappa2))
      by (apply S_Sum; eauto).
    repeat split; try assumption;
      try (eapply underlying_subtype; [exact Hsu | eassumption]).
    intros Hflow.
    assert (Hlow : flows_to (indirect_reader kappa1) observer)
      by (eapply flows_to_trans; [apply (proj2 H1) | exact Hflow]).
    destruct (Hshape Hlow) as
      [(a1 & a2 & k1 & k2 & -> & -> & Ha) |
       (a1 & a2 & k1 & k2 & -> & -> & Ha)].
    + left. exists a1, a2, k1, k2. repeat split; auto.
    + right. exists a1, a2, k1, k2. repeat split; auto.
  - simpl in *. destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    assert (Hsu : subtype (Ty_Prod T1 T2 kappa1)
                             (Ty_Prod U1 U2 kappa2))
      by (apply S_Prod; eauto).
    repeat split; try assumption;
      try (eapply underlying_subtype; [exact Hsu | eassumption]).
    intros Hflow.
    assert (Hlow : flows_to (indirect_reader kappa1) observer)
      by (eapply flows_to_trans; [apply (proj2 H1) | exact Hflow]).
    destruct (Hshape Hlow) as
      (a1 & b1 & a2 & b2 & k1 & k2 & -> & -> & Ha & Hb).
    exists a1, b1, a2, b2, k1, k2. repeat split; auto.
  - simpl in *. destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    assert (Hsu : subtype (Ty_Arrow T1 T2 kappa1)
                             (Ty_Arrow U1 U2 kappa2))
      by (apply S_Arrow; eauto).
    repeat split; try assumption;
      try (eapply underlying_subtype; [exact Hsu | eassumption]).
    intros Hflow.
    assert (Hlow : flows_to (indirect_reader kappa1) observer)
      by (eapply flows_to_trans; [apply (proj2 H1) | exact Hflow]).
    destruct (Hshape Hlow) as
      (A1 & A2 & b1 & b2 & k1 & k2 & -> & -> & Happ).
    exists A1, A2, b1, b2, k1, k2. repeat split; auto.
    intros a1 a2 Ha v1' v2' He1 He2.
    apply IHHsub2.
    eapply Happ; eauto.
  - apply IHHsub2. apply IHHsub1. exact Hrel.
  - simpl in *. destruct Hrel as [Hv1 [Hv2 [Ht1 [Ht2 Hshape]]]].
    repeat split; try assumption;
      try (unfold underlying_typed in *; simpl in *; assumption).
    intros Hflow. apply Hshape.
    eapply flows_to_trans; [apply (proj2 H1) | exact Hflow].
Qed.

Lemma protect_security_low : forall k,
  protect_security k Low = k.
Proof.
  intros [r i]. destruct r, i; reflexivity.
Qed.

Lemma protect_value_low : forall v,
  value v -> protect_value v Low = v.
Proof.
  intros v Hv. inversion Hv; subst; simpl;
    rewrite protect_security_low; reflexivity.
Qed.

Lemma security_of_ty_protect : forall l T,
  security_of (ty_protect l T) =
  protect_security (security_of T) l.
Proof. destruct T; reflexivity. Qed.

Lemma protected_visible_low : forall l T,
  flows_to (security_of (ty_protect l T)).(indirect_reader) Low ->
  l = Low /\ flows_to (security_of T).(indirect_reader) Low.
Proof.
  intros l T H. rewrite security_of_ty_protect in H.
  destruct l, (security_of T) as [r i]; destruct i;
    simpl in *; intuition discriminate.
Qed.

Lemma related_env_update : forall observer Gamma sigma1 sigma2 x T v1 v2,
  related_env observer Gamma sigma1 sigma2 ->
  value_relation observer T v1 v2 ->
  related_env observer (update Gamma x T)
    (sigma_update sigma1 x v1) (sigma_update sigma2 x v2).
Proof.
  intros observer Gamma sigma1 sigma2 x T v1 v2
    [Hrel Hlc] Hvalue. split.
  - intros y U Hy. unfold sigma_update. simpl in *.
    destruct (Nat.eqb y x) eqn:Hyx.
    + inversion Hy; subst. exact Hvalue.
    + apply Hrel. exact Hy.
  - intros y. unfold sigma_update.
    destruct (Nat.eqb y x).
    + pose proof (value_relation_values _ _ _ _ Hvalue)
        as [Hv1 Hv2].
      split; apply value_locally_closed; assumption.
    + apply Hlc.
Qed.

Lemma close_term_identity : forall t,
  close_term tm_fvar t = t.
Proof.
  induction t; simpl; try (f_equal; eauto); reflexivity.
Qed.

Lemma related_env_empty : related_env Low empty tm_fvar tm_fvar.
Proof.
  split.
  - intros x T Hlookup. discriminate Hlookup.
  - intros x. unfold locally_closed. simpl. auto.
Qed.

Lemma lc_open_rec_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x Hlc; simpl in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try (repeat split; eauto); auto.
  - destruct (Nat.eqb k n) eqn:Hkn; simpl in *.
    + apply Nat.eqb_eq in Hkn. lia.
    + lia.
Qed.

Lemma typing_locally_closed : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Htyp. induction Htyp; unfold locally_closed in *;
    simpl in *; try (repeat split; eauto); auto.
  - destruct (fresh_atom L) as [x Hx].
    apply (lc_open_rec_inv body 0 x). apply H2. exact Hx.
  - destruct (fresh_atom L) as [x Hx].
    repeat split; auto.
    + apply (lc_open_rec_inv body1 0 x). apply H1. exact Hx.
  - destruct (fresh_atom L) as [x Hx].
    apply (lc_open_rec_inv body2 0 x). apply H3. exact Hx.
Qed.

Lemma value_expression_relation : forall observer T v1 v2,
  value_relation observer T v1 v2 ->
  expression_relation observer T v1 v2.
Proof.
  intros observer T v1 v2 Hrel.
  assert (Hv : value v1 /\ value v2)
    by (eapply value_relation_values; eauto).
  destruct Hv as [Hv1 Hv2].
  assert (Ht1 : underlying_typed T v1)
    by (destruct T; simpl in Hrel; tauto).
  assert (Ht2 : underlying_typed T v2)
    by (destruct T; simpl in Hrel; tauto).
  unfold expression_relation, expression_lifting.
  repeat split; auto. intros w1 w2 He1 He2.
  apply big_eval_complete in He1. apply big_eval_complete in He2.
  pose proof (big_eval_value_identity _ _ Hv1 He1) as E1.
  pose proof (big_eval_value_identity _ _ Hv2 He2) as E2.
  subst. exact Hrel.
Qed.

Definition related_expr_env (Gamma : context)
    (sigma1 sigma2 : atom -> tm) : Prop :=
  (forall x T, lookup_context x Gamma = Some T ->
     expression_relation Low T (sigma1 x) (sigma2 x)) /\
  (forall x, locally_closed (sigma1 x) /\ locally_closed (sigma2 x)).

Lemma related_expr_env_update : forall Gamma sigma1 sigma2 x T v1 v2,
  related_expr_env Gamma sigma1 sigma2 ->
  value_relation Low T v1 v2 ->
  related_expr_env (update Gamma x T)
    (sigma_update sigma1 x v1) (sigma_update sigma2 x v2).
Proof.
  intros Gamma sigma1 sigma2 x T v1 v2 [Hrel Hlc] Hvalue.
  split.
  - intros y U Hy. unfold sigma_update. simpl in *.
    destruct (Nat.eqb y x) eqn:Hyx.
    + inversion Hy; subst. apply value_expression_relation. exact Hvalue.
    + apply Hrel. exact Hy.
  - intros y. unfold sigma_update.
    destruct (Nat.eqb y x).
    + pose proof (value_relation_values _ _ _ _ Hvalue)
        as [Hv1 Hv2].
      split; apply value_locally_closed; assumption.
    + apply Hlc.
Qed.

Lemma related_expr_env_close_underlying : forall Gamma t T sigma1 sigma2,
  has_type Gamma t T -> related_expr_env Gamma sigma1 sigma2 ->
  underlying_typed T (close_term sigma1 t) /\
  underlying_typed T (close_term sigma2 t).
Proof.
  intros Gamma t T sigma1 sigma2 Htyp [Hrel Hlc].
  pose proof (typing_erase_strict _ _ _ Htyp) as Hstrict.
  split; unfold underlying_typed; rewrite close_term_erase;
    apply erased_typed_to_has_type.
  - eapply erased_typed_close; eauto.
    + intros x U Hlookup.
      destruct (lookup_erase_context_inv _ _ _ Hlookup)
        as [V [HV ->]].
      specialize (Hrel x V HV). unfold expression_relation in Hrel.
      destruct Hrel as [Ht _]. unfold underlying_typed in Ht.
      pose proof (typing_erase_strict empty _ _ Ht) as Hsigma.
      simpl in Hsigma.
      rewrite erase_security_idem, erase_type_idem in Hsigma.
      exact Hsigma.
    + intros x. apply lc_at_erase. apply (proj1 (Hlc x)).
  - eapply erased_typed_close; eauto.
    + intros x U Hlookup.
      destruct (lookup_erase_context_inv _ _ _ Hlookup)
        as [V [HV ->]].
      specialize (Hrel x V HV). unfold expression_relation in Hrel.
      destruct Hrel as [_ [Ht _]]. unfold underlying_typed in Ht.
      pose proof (typing_erase_strict empty _ _ Ht) as Hsigma.
      simpl in Hsigma.
      rewrite erase_security_idem, erase_type_idem in Hsigma.
      exact Hsigma.
    + intros x. apply lc_at_erase. apply (proj2 (Hlc x)).
Qed.

Lemma opaque_expression_lifting : forall T t1 t2,
  underlying_typed T t1 -> underlying_typed T t2 ->
  ~ flows_to (security_of T).(indirect_reader) Low ->
  expression_lifting (value_relation Low T) t1 t2.
Proof.
  intros T t1 t2 Ht1 Ht2 Hhidden v1 v2 He1 He2.
  eapply value_relation_opaque; eauto using underlying_typed_evaluates.
  - exact (proj2 He1).
  - exact (proj2 He2).
Qed.

Theorem fundamental_low_lifting : forall Gamma t T,
  has_type Gamma t T -> forall sigma1 sigma2,
  related_expr_env Gamma sigma1 sigma2 ->
  expression_lifting (value_relation Low T)
    (close_term sigma1 t) (close_term sigma2 t).
Proof.
  intros Gamma t T Htyp. pose proof Htyp as Hself. induction Htyp;
    intros sigma1 sigma2 Henv v1 v2 He1 He2; simpl in *;
    pose proof (related_expr_env_close_underlying
      _ _ _ _ _ Hself Henv) as [Hclosed1 Hclosed2];
    pose proof (underlying_typed_evaluates _ _ _ Hclosed1 He1) as Hout1;
    pose proof (underlying_typed_evaluates _ _ _ Hclosed2 He2) as Hout2.
  - destruct Henv as [Hrel _].
    destruct (Hrel x T H) as [_ [_ Hlift]].
    eapply Hlift; eauto.
  - apply big_eval_complete in He1. apply big_eval_complete in He2.
    pose proof (big_eval_value_identity _ _ (v_unit kappa) He1) as E1.
    pose proof (big_eval_value_identity _ _ (v_unit kappa) He2) as E2.
    subst v1 v2. repeat split; auto using value.
    intros _. exists kappa, kappa. auto.
  - pose proof (big_eval_complete _ _ He1) as B1.
    pose proof (big_eval_complete _ _ He2) as B2.
    inversion B1; subst v1.
    inversion B2; subst v2.
    repeat split; auto.
    intros Hvisible.
    exists T1, T1, (close_term sigma1 body), (close_term sigma2 body),
      kappa, kappa. repeat split; auto.
    intros a1 a2 Ha w1 w2 Ea1 Ea2.
    destruct (value_relation_values _ _ _ _ Ha) as [Hva1 Hva2].
    destruct Henv as [Hrel Hlc].
    assert (Henv' : related_expr_env (update Gamma 0 T1)
      (sigma_update sigma1 0 a1) (sigma_update sigma2 0 a2)).
    { apply related_expr_env_update; auto. split; auto. }
    (* A fresh opening atom connects the cofinite body premise to the
       applications of the two abstractions. *)
    destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
    apply notin_append in Hfresh. destruct Hfresh as [HL Hb].
    assert (Henvx : related_expr_env (update Gamma x T1)
      (sigma_update sigma1 x a1) (sigma_update sigma2 x a2)).
    { apply related_expr_env_update; auto. split; auto. }
    pose proof (H2 x HL (H1 x HL) _ _ Henvx) as Hbody.
    assert (Eopen1 : close_term (sigma_update sigma1 x a1)
      (open body (tm_fvar x)) = open (close_term sigma1 body) a1).
    { apply close_term_open_update; auto using value_locally_closed. }
    assert (Eopen2 : close_term (sigma_update sigma2 x a2)
      (open body (tm_fvar x)) = open (close_term sigma2 body) a2).
    { apply close_term_open_update; auto using value_locally_closed. }
    rewrite Eopen1, Eopen2 in Hbody.
    pose proof (big_eval_app_abs_inv _ _ _ _ _ _
      (big_eval_value _ _ B1) Hva1 (big_eval_complete _ _ Ea1))
      as (u1 & Bu1 & Ew1).
    pose proof (big_eval_app_abs_inv _ _ _ _ _ _
      (big_eval_value _ _ B2) Hva2 (big_eval_complete _ _ Ea2))
      as (u2 & Bu2 & Ew2).
    destruct (indirect_reader kappa) eqn:Hk; simpl in Hvisible.
    + rewrite protect_value_low in Ew1 by
        (eapply big_eval_value; eauto).
      rewrite protect_value_low in Ew2 by
        (eapply big_eval_value; eauto).
      subst w1 w2. eapply Hbody; eauto using big_eval_sound.
    + contradiction.
Admitted.

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
