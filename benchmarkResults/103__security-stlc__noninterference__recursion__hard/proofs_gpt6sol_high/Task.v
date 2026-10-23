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

(* The relation is indexed by the indirect reader.  In particular, a
   protected value at High need not have the same constructor in both runs.
   At Low, functions are compared by their applications to related values. *)
Fixpoint related_value (T : ty) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_Unit k =>
      match k.(indirect_reader) with
      | High => True
      | Low => exists k1 k2, v1 = tm_unit k1 /\ v2 = tm_unit k2 /\
          k1.(indirect_reader) = Low /\ k2.(indirect_reader) = Low
      end
  | Ty_Nat k =>
      match k.(indirect_reader) with
      | High => True
      | Low => exists n k1 k2, v1 = tm_nat n k1 /\ v2 = tm_nat n k2 /\
          k1.(indirect_reader) = Low /\ k2.(indirect_reader) = Low
      end
  | Ty_Sum A B k =>
      match k.(indirect_reader) with
      | High => True
      | Low =>
          (exists a1 a2 k1 k2, v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\
             k1.(indirect_reader) = Low /\ k2.(indirect_reader) = Low /\
             related_value A a1 a2) \/
          (exists b1 b2 k1 k2, v1 = tm_inr b1 k1 /\ v2 = tm_inr b2 k2 /\
             k1.(indirect_reader) = Low /\ k2.(indirect_reader) = Low /\
             related_value B b1 b2)
      end
  | Ty_Prod A B k =>
      match k.(indirect_reader) with
      | High => True
      | Low => exists a1 a2 b1 b2 k1 k2,
          v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
          k1.(indirect_reader) = Low /\ k2.(indirect_reader) = Low /\
          related_value A a1 a2 /\ related_value B b1 b2
      end
  | Ty_Arrow A B k =>
      match k.(indirect_reader) with
      | High => True
      | Low => forall r a1 a2 w1 w2,
          flows_to k.(reader) r ->
          value a1 -> value a2 -> related_value A a1 a2 ->
          evaluates (tm_app v1 a1 r) w1 ->
          evaluates (tm_app v2 a2 r) w2 ->
          related_value B w1 w2
      end
  end.

Definition related_term (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, evaluates t1 v1 -> evaluates t2 v2 ->
    related_value T v1 v2.

Lemma related_ground_erases : forall T k v1 v2,
  k.(indirect_reader) = Low ->
  ground T -> transparent_at k T -> related_value T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  induction T; intros k v1 v2 Hlow Hg Htr Hr;
    simpl in Hg, Htr, Hr;
    destruct Htr as [Hle Hparts];
    destruct (indirect_reader s) eqn:Hs.
  - destruct Hr as (k1 & k2 & -> & -> & _ & _); reflexivity.
  - destruct Hle as [_ Hflow].
    unfold flows_to in Hflow; rewrite Hs, Hlow in Hflow; contradiction.
  - destruct Hg as [Hg1 Hg2]; destruct Hparts as [Ht1 Ht2].
    destruct Hr as [(a1 & a2 & k1 & k2 & -> & -> & _ & _ & Ha) |
                    (b1 & b2 & k1 & k2 & -> & -> & _ & _ & Hb)]; simpl;
      f_equal; eauto.
  - destruct Hle as [_ Hflow].
    unfold flows_to in Hflow; rewrite Hs, Hlow in Hflow; contradiction.
  - destruct Hg as [Hg1 Hg2]; destruct Hparts as [Ht1 Ht2].
    destruct Hr as (a1 & a2 & b1 & b2 & k1 & k2 & -> & -> & _ & _ & Ha & Hb);
      simpl; f_equal; eauto.
  - destruct Hle as [_ Hflow].
    unfold flows_to in Hflow; rewrite Hs, Hlow in Hflow; contradiction.
  - contradiction.
  - contradiction.
  - destruct Hr as (n & k1 & k2 & -> & -> & _ & _); reflexivity.
  - destruct Hle as [_ Hflow].
    unfold flows_to in Hflow; rewrite Hs, Hlow in Hflow; contradiction.
Qed.

Lemma flows_to_trans : forall a b c,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. destruct a, b, c; simpl; tauto. Qed.

Lemma security_le_low : forall k1 k2,
  security_le k1 k2 -> k2.(indirect_reader) = Low ->
  k1.(indirect_reader) = Low.
Proof.
  intros [r1 i1] [r2 i2] [_ H] E; simpl in *.
  destruct i1, i2; simpl in *;
    first [reflexivity | contradiction | discriminate].
Qed.

Lemma related_value_subtype : forall T U,
  subtype T U -> forall v1 v2,
    related_value T v1 v2 -> related_value U v1 v2.
Proof.
  intros T U Hsub; induction Hsub; intros v1 v2 Hr; simpl in *.
  - destruct (indirect_reader kappa2) eqn:E; [|exact I].
    match goal with Hle : security_le _ _ |- _ =>
      rewrite (security_le_low _ _ Hle E) in Hr end; exact Hr.
  - destruct (indirect_reader kappa2) eqn:E; [|exact I].
    match goal with Hle : security_le _ _ |- _ =>
      rewrite (security_le_low _ _ Hle E) in Hr end.
    destruct Hr as [(a1 & a2 & k1 & k2 & -> & -> & Hk1 & Hk2 & Ha) |
                    (b1 & b2 & k1 & k2 & -> & -> & Hk1 & Hk2 & Hb)].
    + left. exists a1, a2, k1, k2. repeat split; auto.
    + right. exists b1, b2, k1, k2. repeat split; auto.
  - destruct (indirect_reader kappa2) eqn:E; [|exact I].
    match goal with Hle : security_le _ _ |- _ =>
      rewrite (security_le_low _ _ Hle E) in Hr end.
    destruct Hr as (a1 & a2 & b1 & b2 & k1 & k2 & -> & -> & Hk1 & Hk2 & Ha & Hb).
    exists a1, a2, b1, b2, k1, k2. repeat split; auto.
  - destruct (indirect_reader kappa2) eqn:E; [|exact I].
    match goal with Hle : security_le _ _ |- _ =>
      rewrite (security_le_low _ _ Hle E) in Hr end.
    intros r a1 a2 w1 w2 Hflow Va1 Va2 Ha He1 He2.
    apply (IHHsub2 w1 w2).
    apply (Hr r a1 a2 w1 w2); auto.
    destruct H1 as [Hreader _].
    eapply flows_to_trans; eauto.
  - eapply IHHsub2, IHHsub1; eauto.
  - destruct (indirect_reader k2) eqn:E; [|exact I].
    match goal with Hle : security_le _ _ |- _ =>
      rewrite (security_le_low _ _ Hle E) in Hr end; exact Hr.
Qed.

Lemma value_no_step : forall v t, value v -> ~ step v t.
Proof.
  intros v t Hv; revert t.
  induction Hv; intros t Hs; inversion Hs; subst; eauto;
    match goal with
    | IH : forall _, ~ step ?u _, H : step ?u _ |- _ =>
        exact (IH _ H)
    end.
Qed.

Lemma step_deterministic : forall t u v,
  step t u -> step t v -> u = v.
Proof.
  intros t u v Hs; revert v.
  induction Hs; intros w Ht; inversion Ht; subst;
    try solve [f_equal; eauto];
    try solve [exfalso;
      multimatch goal with Hstep : step ?a _ |- _ =>
        eapply (value_no_step a _);
          [solve [eauto using value] | exact Hstep]
      end].
Qed.

Lemma multi_strip : forall t u v,
  step t u -> multi t v -> value v -> multi u v.
Proof.
  intros t u v Hstep Hmulti Hv.
  inversion Hmulti; subst.
  - exfalso; eapply value_no_step; eauto.
  - assert (u = t2) by (eapply step_deterministic; eauto).
    subst; assumption.
Qed.

Lemma evaluates_suffix : forall t u v,
  multi t u -> evaluates t v -> evaluates u v.
Proof.
  intros t u v Hprefix; revert v.
  induction Hprefix; intros v [Hrun Hv].
  - split; assumption.
  - apply IHHprefix. split; [eapply multi_strip; eauto | exact Hv].
Qed.

Lemma evaluates_unique : forall t v w,
  evaluates t v -> evaluates t w -> v = w.
Proof.
  intros t v w [Hrun Hv] Hew.
  destruct (evaluates_suffix _ _ _ Hrun Hew) as [Htail _].
  inversion Htail; subst; auto.
  exfalso; eapply value_no_step; eauto.
Qed.

Fixpoint instantiate (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit k => tm_unit k
  | tm_abs T b k => tm_abs T (instantiate rho b) k
  | tm_app a b r => tm_app (instantiate rho a) (instantiate rho b) r
  | tm_pair a b k => tm_pair (instantiate rho a) (instantiate rho b) k
  | tm_fst a r => tm_fst (instantiate rho a) r
  | tm_snd a r => tm_snd (instantiate rho a) r
  | tm_inl a k => tm_inl (instantiate rho a) k
  | tm_inr a k => tm_inr (instantiate rho a) k
  | tm_case a b c r =>
      tm_case (instantiate rho a) (instantiate rho b) (instantiate rho c) r
  | tm_protect l a => tm_protect l (instantiate rho a)
  | tm_nat n k => tm_nat n k
  | tm_succ a r => tm_succ (instantiate rho a) r
  | tm_natrec a b c r =>
      tm_natrec (instantiate rho a) (instantiate rho b) (instantiate rho c) r
  end.

Definition extend_subst (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

Definition related_subst (Gamma : context) (rho1 rho2 : atom -> tm) : Prop :=
  (forall x, locally_closed (rho1 x) /\ locally_closed (rho2 x)) /\
  forall x T, lookup_context x Gamma = Some T ->
    related_term T (rho1 x) (rho2 x).

Lemma open_rec_lc : forall t j k u,
  lc_at j t -> j <= k -> open_rec k u t = t.
Proof.
  induction t; intros j k u Hlc Hle; simpl in *;
    try reflexivity;
    try solve [f_equal; eauto using le_n_S];
    try solve [destruct Hlc; f_equal; eauto];
    try solve [destruct Hlc as [? [? ?]]; f_equal; eauto].
  destruct (Nat.eqb k n) eqn:E; auto.
  apply Nat.eqb_eq in E; lia.
  destruct Hlc as [H1 [H2 H3]].
  f_equal; eauto using le_n_S.
Qed.

Lemma instantiate_open_fvar : forall t rho k x,
  (forall y, locally_closed (rho y)) ->
  instantiate rho (open_rec k (tm_fvar x) t) =
  open_rec k (rho x) (instantiate rho t).
Proof.
  induction t; intros rho k x Hlc; simpl;
    try solve [f_equal; eauto].
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_lc with (j := 0).
    + apply Hlc.
    + lia.
Qed.

Lemma not_in_app_split : forall (x : atom) A B,
  ~ In x (A ++ B) -> ~ In x A /\ ~ In x B.
Proof. intros; rewrite in_app_iff in H; tauto. Qed.

Lemma instantiate_extend_fresh : forall t rho x v,
  ~ In x (fv t) ->
  instantiate (extend_subst rho x v) t = instantiate rho t.
Proof.
  induction t; intros rho x v Hfresh; simpl in *;
    try reflexivity;
    try solve [f_equal; eauto];
    try solve [apply not_in_app_split in Hfresh; destruct Hfresh;
               f_equal; eauto].
  - unfold extend_subst. destruct (Nat.eqb x a) eqn:E; auto.
    apply Nat.eqb_eq in E; subst. exfalso; apply Hfresh; auto.
  - apply not_in_app_split in Hfresh. destruct Hfresh as [Ha Hb].
    apply not_in_app_split in Hb. destruct Hb as [Hb Hc].
    f_equal; eauto.
  - apply not_in_app_split in Hfresh. destruct Hfresh as [Ha Hbc].
    apply not_in_app_split in Hbc. destruct Hbc as [Hb Hc].
    f_equal; eauto.
Qed.

Lemma evaluates_value : forall v, value v -> evaluates v v.
Proof. intros v Hv; split; [constructor | exact Hv]. Qed.

Lemma evaluates_step_back : forall t u v,
  step t u -> evaluates u v -> evaluates t v.
Proof.
  intros t u v Hs [Hm Hv]. split; [econstructor; eauto | exact Hv].
Qed.

Lemma evaluates_app_parts : forall f a r v,
  evaluates (tm_app f a r) v ->
  exists vf va,
    evaluates f vf /\ evaluates a va /\
    evaluates (tm_app vf va r) v.
Proof.
  intros f a r v [Hm Hv].
  remember (tm_app f a r) as t eqn:Et.
  revert f a r Et.
  induction Hm; intros f a r Et; subst.
  - inversion Hv.
  - inversion H; subst.
    + exists (tm_abs T body kappa), a.
      repeat split; try (apply evaluates_value; assumption).
      econstructor; eauto.
    + destruct (IHHm Hv _ _ _ eq_refl) as (vf & va & Hf & Ha & Happ).
      exists vf, va. split.
      * eapply evaluates_step_back; eauto.
      * split; assumption.
    + destruct (IHHm Hv _ _ _ eq_refl) as (vf & va & Hf & Ha & Happ).
      exists vf, va. split; [exact Hf |].
      split; [eapply evaluates_step_back; eauto | exact Happ].
Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof.
  destruct T; destruct s as [r i]; destruct r, i; reflexivity.
Qed.

Lemma related_value_high : forall T v1 v2,
  related_value (ty_protect High T) v1 v2.
Proof.
  destruct T; intros; destruct s as [r i];
    destruct r, i; simpl; exact I.
Qed.

Lemma related_app : forall A B k r f1 f2 a1 a2,
  related_term (Ty_Arrow A B k) f1 f2 ->
  related_term A a1 a2 ->
  flows_to k.(reader) r ->
  related_term (ty_protect k.(indirect_reader) B)
    (tm_app f1 a1 r) (tm_app f2 a2 r).
Proof.
  intros A B k r f1 f2 a1 a2 Hf Ha Hflow w1 w2 He1 He2.
  destruct (indirect_reader k) eqn:E.
  - rewrite ty_protect_low.
    destruct (evaluates_app_parts _ _ _ _ He1)
      as (vf1 & va1 & Hf1 & Ha1 & Happ1).
    destruct (evaluates_app_parts _ _ _ _ He2)
      as (vf2 & va2 & Hf2 & Ha2 & Happ2).
    specialize (Hf _ _ Hf1 Hf2).
    simpl in Hf. rewrite E in Hf.
    destruct Hf1 as [_ Hvf1], Hf2 as [_ Hvf2].
    destruct Ha1 as [Hm1 Hva1], Ha2 as [Hm2 Hva2].
    apply (Hf r va1 va2 w1 w2); auto.
    apply (Ha va1 va2); split; assumption.
  - apply related_value_high.
Qed.

Lemma evaluates_pair_parts : forall a b k v,
  evaluates (tm_pair a b k) v ->
  exists va vb,
    evaluates a va /\ evaluates b vb /\ v = tm_pair va vb k.
Proof.
  intros a b k v [Hm Hv].
  remember (tm_pair a b k) as t eqn:Et.
  revert a b k Et.
  induction Hm; intros a b k Et; subst.
  - inversion Hv; subst.
    exists a, b; repeat split; try (apply evaluates_value; assumption);
      reflexivity.
  - inversion H; subst.
    + destruct (IHHm Hv _ _ _ eq_refl) as (va & vb & Ha & Hb & Ev).
      exists va, vb. split; [eapply evaluates_step_back; eauto |].
      split; assumption.
    + destruct (IHHm Hv _ _ _ eq_refl) as (va & vb & Ha & Hb & Ev).
      exists va, vb. split; [exact Ha |].
      split; [eapply evaluates_step_back; eauto | exact Ev].
Qed.

Lemma related_pair : forall A B k a1 a2 b1 b2,
  related_term A a1 a2 -> related_term B b1 b2 ->
  related_term (Ty_Prod A B k)
    (tm_pair a1 b1 k) (tm_pair a2 b2 k).
Proof.
  intros A B k a1 a2 b1 b2 Ha Hb v1 v2 He1 He2.
  destruct (indirect_reader k) eqn:E;
    [|simpl; rewrite E; exact I].
  simpl; rewrite E.
  destruct (evaluates_pair_parts _ _ _ _ He1)
    as (va1 & vb1 & Ha1 & Hb1 & ->).
  destruct (evaluates_pair_parts _ _ _ _ He2)
    as (va2 & vb2 & Ha2 & Hb2 & ->).
  exists va1, va2, vb1, vb2, k, k.
  repeat split; auto.
Qed.

Lemma protect_value_low : forall t, protect_value t Low = t.
Proof.
  destruct t; simpl; try reflexivity;
    destruct s as [r i]; destruct r, i; reflexivity.
Qed.

Lemma evaluates_protect_low_inv : forall t v,
  evaluates (tm_protect Low t) v -> evaluates t v.
Proof.
  intros t v [Hm Hv].
  remember (tm_protect Low t) as q eqn:Eq.
  revert t Eq.
  induction Hm as [q | q q' q'' Hs Hm IH]; intros arg Eq; subst.
  - inversion Hv.
  - inversion Hs; subst.
    + rewrite protect_value_low in Hm.
      split; assumption.
    + apply evaluates_step_back with (u := t').
      * assumption.
      * apply IH; auto.
Qed.

Lemma related_protect : forall T l t1 t2,
  related_term T t1 t2 ->
  related_term (ty_protect l T) (tm_protect l t1) (tm_protect l t2).
Proof.
  intros T l t1 t2 Hr v1 v2 He1 He2.
  destruct l.
  - rewrite ty_protect_low.
    apply Hr; apply evaluates_protect_low_inv; assumption.
  - apply related_value_high.
Qed.

Lemma evaluates_inl_parts : forall a k v,
  evaluates (tm_inl a k) v ->
  exists va, evaluates a va /\ v = tm_inl va k.
Proof.
  intros a k v [Hm Hv].
  remember (tm_inl a k) as q eqn:Eq.
  revert a k Eq.
  induction Hm as [q | q q' q'' Hs Hm IH]; intros arg sec Eq; subst.
  - inversion Hv; subst. exists arg; split;
      [apply evaluates_value; assumption | reflexivity].
  - inversion Hs; subst.
    destruct (IH Hv _ _ eq_refl) as (va & Ha & ->).
    exists va; split; [eapply evaluates_step_back; eauto | reflexivity].
Qed.

Lemma evaluates_inr_parts : forall a k v,
  evaluates (tm_inr a k) v ->
  exists va, evaluates a va /\ v = tm_inr va k.
Proof.
  intros a k v [Hm Hv].
  remember (tm_inr a k) as q eqn:Eq.
  revert a k Eq.
  induction Hm as [q | q q' q'' Hs Hm IH]; intros arg sec Eq; subst.
  - inversion Hv; subst. exists arg; split;
      [apply evaluates_value; assumption | reflexivity].
  - inversion Hs; subst.
    destruct (IH Hv _ _ eq_refl) as (va & Ha & ->).
    exists va; split; [eapply evaluates_step_back; eauto | reflexivity].
Qed.

Lemma related_inl : forall A B k t1 t2,
  related_term A t1 t2 ->
  related_term (Ty_Sum A B k) (tm_inl t1 k) (tm_inl t2 k).
Proof.
  intros A B k t1 t2 Hr v1 v2 He1 He2.
  destruct (indirect_reader k) eqn:E;
    [|simpl; rewrite E; exact I].
  simpl; rewrite E.
  destruct (evaluates_inl_parts _ _ _ He1) as (a1 & Ha1 & ->).
  destruct (evaluates_inl_parts _ _ _ He2) as (a2 & Ha2 & ->).
  left. exists a1, a2, k, k. repeat split; auto.
Qed.

Lemma related_inr : forall A B k t1 t2,
  related_term B t1 t2 ->
  related_term (Ty_Sum A B k) (tm_inr t1 k) (tm_inr t2 k).
Proof.
  intros A B k t1 t2 Hr v1 v2 He1 He2.
  destruct (indirect_reader k) eqn:E;
    [|simpl; rewrite E; exact I].
  simpl; rewrite E.
  destruct (evaluates_inr_parts _ _ _ He1) as (a1 & Ha1 & ->).
  destruct (evaluates_inr_parts _ _ _ He2) as (a2 & Ha2 & ->).
  right. exists a1, a2, k, k. repeat split; auto.
Qed.

Lemma value_locally_closed : forall v,
  value v -> locally_closed v.
Proof.
  intros v Hv; induction Hv; unfold locally_closed in *; simpl in *; auto.
Qed.

Lemma related_value_as_term : forall T v1 v2,
  value v1 -> value v2 -> related_value T v1 v2 ->
  related_term T v1 v2.
Proof.
  intros T v1 v2 Hv1 Hv2 Hr w1 w2 He1 He2.
  assert (w1 = v1) by (eapply evaluates_unique; eauto using evaluates_value).
  assert (w2 = v2) by (eapply evaluates_unique; eauto using evaluates_value).
  subst; exact Hr.
Qed.

Lemma related_subst_extend : forall Gamma rho1 rho2 x T v1 v2,
  related_subst Gamma rho1 rho2 ->
  value v1 -> value v2 -> related_value T v1 v2 ->
  related_subst (update Gamma x T)
    (extend_subst rho1 x v1) (extend_subst rho2 x v2).
Proof.
  intros Gamma rho1 rho2 x T v1 v2 [Hlc Hr] Hv1 Hv2 Hrel.
  split.
  - intros y. unfold extend_subst.
    destruct (Nat.eqb x y); auto using value_locally_closed.
  - intros y U Hlookup.
    unfold update in Hlookup. simpl in Hlookup.
    rewrite Nat.eqb_sym in Hlookup.
    unfold extend_subst.
    destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst.
      eapply related_value_as_term; eauto.
    + apply Hr; exact Hlookup.
Qed.

Lemma protect_value_is_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l Hv; inversion Hv; subst; simpl;
    constructor; auto.
Qed.

Lemma evaluates_protect_value_result : forall l v w,
  value v -> evaluates (tm_protect l v) w ->
  w = protect_value v l.
Proof.
  intros l v w Hv He.
  eapply evaluates_unique; [exact He |].
  split.
  - eapply multi_step.
    + apply ST_ProtectValue; exact Hv.
    + constructor.
  - apply protect_value_is_value; assumption.
Qed.

Lemma evaluates_fst_part : forall t r v,
  evaluates (tm_fst t r) v ->
  exists w, evaluates t w /\ evaluates (tm_fst w r) v.
Proof.
  intros t r v [Hm Hv].
  remember (tm_fst t r) as q eqn:Eq.
  revert t r Eq.
  induction Hm as [q | q q' q'' Hs Hm IH]; intros arg lab Eq; subst.
  - inversion Hv.
  - inversion Hs; subst.
    + exists (tm_pair v1 v2 kappa).
      split; [apply evaluates_value; constructor; assumption |].
      split; [econstructor; eauto | exact Hv].
    + destruct (IH Hv _ _ eq_refl) as (w & He & Hfst).
      exists w. split; [eapply evaluates_step_back; eauto | exact Hfst].
Qed.

Lemma evaluates_snd_part : forall t r v,
  evaluates (tm_snd t r) v ->
  exists w, evaluates t w /\ evaluates (tm_snd w r) v.
Proof.
  intros t r v [Hm Hv].
  remember (tm_snd t r) as q eqn:Eq.
  revert t r Eq.
  induction Hm as [q | q q' q'' Hs Hm IH]; intros arg lab Eq; subst.
  - inversion Hv.
  - inversion Hs; subst.
    + exists (tm_pair v1 v2 kappa).
      split; [apply evaluates_value; constructor; assumption |].
      split; [econstructor; eauto | exact Hv].
    + destruct (IH Hv _ _ eq_refl) as (w & He & Hsnd).
      exists w. split; [eapply evaluates_step_back; eauto | exact Hsnd].
Qed.

Lemma evaluates_fst_pair_result : forall a b k r w,
  value a -> value b ->
  evaluates (tm_fst (tm_pair a b k) r) w ->
  w = protect_value a k.(indirect_reader).
Proof.
  intros a b k r w Ha Hb [Hm Hw].
  inversion Hm; subst; [inversion Hw |].
  inversion H; subst.
  - eapply evaluates_protect_value_result; eauto.
    split; assumption.
  - exfalso.
    assert (Hp : value (tm_pair a b k)) by (constructor; assumption).
    exact (value_no_step _ _ Hp H4).
Qed.

Lemma evaluates_snd_pair_result : forall a b k r w,
  value a -> value b ->
  evaluates (tm_snd (tm_pair a b k) r) w ->
  w = protect_value b k.(indirect_reader).
Proof.
  intros a b k r w Ha Hb [Hm Hw].
  inversion Hm; subst; [inversion Hw |].
  inversion H; subst.
  - eapply evaluates_protect_value_result; eauto.
    split; assumption.
  - exfalso.
    assert (Hp : value (tm_pair a b k)) by (constructor; assumption).
    exact (value_no_step _ _ Hp H4).
Qed.

Lemma related_fst : forall A B k r t1 t2,
  related_term (Ty_Prod A B k) t1 t2 ->
  related_term (ty_protect k.(indirect_reader) A)
    (tm_fst t1 r) (tm_fst t2 r).
Proof.
  intros A B k r t1 t2 Hr w1 w2 He1 He2.
  destruct (indirect_reader k) eqn:E; [|apply related_value_high].
  rewrite ty_protect_low.
  destruct (evaluates_fst_part _ _ _ He1) as (p1 & Hp1 & Hfst1).
  destruct (evaluates_fst_part _ _ _ He2) as (p2 & Hp2 & Hfst2).
  specialize (Hr _ _ Hp1 Hp2).
  simpl in Hr; rewrite E in Hr.
  destruct Hr as (a1 & a2 & b1 & b2 & k1 & k2 &
                  Ep1 & Ep2 & Hk1 & Hk2 & Ha & Hb).
  subst p1 p2.
  destruct Hp1 as [_ Vp1], Hp2 as [_ Vp2].
  inversion Vp1; subst; inversion Vp2; subst.
  pose proof (evaluates_fst_pair_result _ _ _ _ _ H1 H3 Hfst1) as Ew1.
  pose proof (evaluates_fst_pair_result _ _ _ _ _ H2 H5 Hfst2) as Ew2.
  rewrite Hk1 in Ew1; rewrite Hk2 in Ew2.
  rewrite protect_value_low in Ew1, Ew2.
  subst; exact Ha.
Qed.

Lemma related_snd : forall A B k r t1 t2,
  related_term (Ty_Prod A B k) t1 t2 ->
  related_term (ty_protect k.(indirect_reader) B)
    (tm_snd t1 r) (tm_snd t2 r).
Proof.
  intros A B k r t1 t2 Hr w1 w2 He1 He2.
  destruct (indirect_reader k) eqn:E; [|apply related_value_high].
  rewrite ty_protect_low.
  destruct (evaluates_snd_part _ _ _ He1) as (p1 & Hp1 & Hsnd1).
  destruct (evaluates_snd_part _ _ _ He2) as (p2 & Hp2 & Hsnd2).
  specialize (Hr _ _ Hp1 Hp2).
  simpl in Hr; rewrite E in Hr.
  destruct Hr as (a1 & a2 & b1 & b2 & k1 & k2 &
                  Ep1 & Ep2 & Hk1 & Hk2 & Ha & Hb).
  subst p1 p2.
  destruct Hp1 as [_ Vp1], Hp2 as [_ Vp2].
  inversion Vp1; subst; inversion Vp2; subst.
  pose proof (evaluates_snd_pair_result _ _ _ _ _ H1 H3 Hsnd1) as Ew1.
  pose proof (evaluates_snd_pair_result _ _ _ _ _ H2 H5 Hsnd2) as Ew2.
  rewrite Hk1 in Ew1; rewrite Hk2 in Ew2.
  rewrite protect_value_low in Ew1, Ew2.
  subst; exact Hb.
Qed.

Lemma related_unit : forall k,
  related_term (Ty_Unit k) (tm_unit k) (tm_unit k).
Proof.
  intros k v1 v2 He1 He2.
  assert (v1 = tm_unit k) by
    (eapply evaluates_unique; eauto using evaluates_value, v_unit).
  assert (v2 = tm_unit k) by
    (eapply evaluates_unique; eauto using evaluates_value, v_unit).
  subst. destruct (indirect_reader k) eqn:E; simpl; rewrite E; auto.
  exists k, k; repeat split; auto.
Qed.

Lemma related_nat : forall n k,
  related_term (Ty_Nat k) (tm_nat n k) (tm_nat n k).
Proof.
  intros n k v1 v2 He1 He2.
  assert (v1 = tm_nat n k) by
    (eapply evaluates_unique; eauto using evaluates_value, v_nat).
  assert (v2 = tm_nat n k) by
    (eapply evaluates_unique; eauto using evaluates_value, v_nat).
  subst. destruct (indirect_reader k) eqn:E; simpl; rewrite E; auto.
  exists n, k, k; repeat split; auto.
Qed.

Lemma evaluates_succ_part : forall t r v,
  evaluates (tm_succ t r) v ->
  exists w, evaluates t w /\ evaluates (tm_succ w r) v.
Proof.
  intros t r v [Hm Hv].
  remember (tm_succ t r) as q eqn:Eq.
  revert t r Eq.
  induction Hm as [q | q q' q'' Hs Hm IH]; intros arg lab Eq; subst.
  - inversion Hv.
  - inversion Hs; subst.
    + destruct (IH Hv _ _ eq_refl) as (w & He & Hsucc).
      exists w. split; [eapply evaluates_step_back; eauto | exact Hsucc].
    + exists (tm_nat n k).
      split; [apply evaluates_value; constructor |].
      split; [econstructor; eauto | exact Hv].
Qed.

Lemma evaluates_succ_nat_result : forall n k r w,
  evaluates (tm_succ (tm_nat n k) r) w ->
  w = protect_value (tm_nat (S n) public) k.(indirect_reader).
Proof.
  intros n k r w [Hm Hw].
  inversion Hm; subst; [inversion Hw |].
  inversion H; subst.
  - exfalso. eapply value_no_step; [constructor | eassumption].
  - eapply evaluates_protect_value_result; [constructor |].
    split; assumption.
Qed.

Lemma related_succ : forall k r t1 t2,
  related_term (Ty_Nat k) t1 t2 ->
  related_term (ty_protect k.(indirect_reader) (Ty_Nat public))
    (tm_succ t1 r) (tm_succ t2 r).
Proof.
  intros k r t1 t2 Hr w1 w2 He1 He2.
  destruct (indirect_reader k) eqn:E; [|apply related_value_high].
  rewrite ty_protect_low.
  destruct (evaluates_succ_part _ _ _ He1) as (n1 & Hn1 & Hs1).
  destruct (evaluates_succ_part _ _ _ He2) as (n2 & Hn2 & Hs2).
  specialize (Hr _ _ Hn1 Hn2).
  simpl in Hr; rewrite E in Hr.
  destruct Hr as (n & k1 & k2 & En1 & En2 & Hk1 & Hk2).
  subst n1 n2.
  pose proof (evaluates_succ_nat_result _ _ _ _ Hs1) as Ew1.
  pose proof (evaluates_succ_nat_result _ _ _ _ Hs2) as Ew2.
  rewrite Hk1 in Ew1; rewrite Hk2 in Ew2.
  rewrite protect_value_low in Ew1, Ew2.
  subst. simpl.
  exists (S n), public, public. repeat split; reflexivity.
Qed.

Lemma in_le_fold_max : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin]; [lia |].
    specialize (IH _ Hin); lia.
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (fold_right Nat.max 0 L)).
  intros Hin. pose proof (in_le_fold_max _ _ Hin). lia.
Qed.

Lemma evaluates_abs_canonical : forall T body k v,
  evaluates (tm_abs T body k) v ->
  v = tm_abs T body k /\ value (tm_abs T body k).
Proof.
  intros T body k v [Hm Hv].
  inversion Hm; subst; [split; auto |].
  inversion H.
Qed.

Lemma instantiate_open_extended : forall body rho x v,
  ~ In x (fv body) ->
  (forall y, locally_closed (extend_subst rho x v y)) ->
  instantiate (extend_subst rho x v) (open body (tm_fvar x)) =
  open (instantiate rho body) v.
Proof.
  intros body rho x v Hfresh Hlc.
  unfold open.
  rewrite instantiate_open_fvar by exact Hlc.
  unfold extend_subst at 1.
  rewrite Nat.eqb_refl.
  rewrite instantiate_extend_fresh by exact Hfresh.
  reflexivity.
Qed.

Lemma related_abs : forall L Gamma T1 body T2 k rho1 rho2,
  (forall x, ~ In x L ->
    forall sigma1 sigma2,
      related_subst (update Gamma x T1) sigma1 sigma2 ->
      related_term T2
        (instantiate sigma1 (open body (tm_fvar x)))
        (instantiate sigma2 (open body (tm_fvar x)))) ->
  related_subst Gamma rho1 rho2 ->
  related_term (Ty_Arrow T1 T2 k)
    (instantiate rho1 (tm_abs T1 body k))
    (instantiate rho2 (tm_abs T1 body k)).
Proof.
  intros L Gamma T1 body T2 k rho1 rho2 Hbody Henv.
  intros vf1 vf2 He1 He2.
  destruct (evaluates_abs_canonical _ _ _ _ He1) as [-> Vabs1].
  destruct (evaluates_abs_canonical _ _ _ _ He2) as [-> Vabs2].
  simpl.
  destruct (indirect_reader k) eqn:E; [|exact I].
  intros r a1 a2 w1 w2 Hflow Va1 Va2 Ha Happ1 Happ2.
  destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
  apply not_in_app_split in Hfresh.
  destruct Hfresh as [HxL Hxbody].
  pose proof (related_subst_extend _ _ _ x T1 a1 a2 Henv Va1 Va2 Ha)
    as Hext.
  pose proof (Hbody x HxL _ _ Hext) as Hterm.
  destruct Hext as [HlcExt _].
  rewrite (instantiate_open_extended body rho1 x a1 Hxbody
             (fun y => proj1 (HlcExt y))) in Hterm.
  rewrite (instantiate_open_extended body rho2 x a2 Hxbody
             (fun y => proj2 (HlcExt y))) in Hterm.
  apply (Hterm w1 w2).
  - apply evaluates_protect_low_inv.
    rewrite <- E.
    eapply evaluates_suffix.
    + eapply multi_step with
        (t2 := tm_protect k.(indirect_reader)
                  (open (instantiate rho1 body) a1)).
      * apply ST_AppAbs; eauto.
      * constructor.
    + exact Happ1.
  - apply evaluates_protect_low_inv.
    rewrite <- E.
    eapply evaluates_suffix.
    + eapply multi_step with
        (t2 := tm_protect k.(indirect_reader)
                  (open (instantiate rho2 body) a2)).
      * apply ST_AppAbs; eauto.
      * constructor.
    + exact Happ2.
Qed.

Lemma related_open_branch : forall L Gamma A body T rho1 rho2 v1 v2,
  (forall x, ~ In x L ->
    forall sigma1 sigma2,
      related_subst (update Gamma x A) sigma1 sigma2 ->
      related_term T
        (instantiate sigma1 (open body (tm_fvar x)))
        (instantiate sigma2 (open body (tm_fvar x)))) ->
  related_subst Gamma rho1 rho2 ->
  value v1 -> value v2 -> related_value A v1 v2 ->
  related_term T
    (open (instantiate rho1 body) v1)
    (open (instantiate rho2 body) v2).
Proof.
  intros L Gamma A body T rho1 rho2 v1 v2 Hbody Henv Hv1 Hv2 Hr.
  destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
  apply not_in_app_split in Hfresh.
  destruct Hfresh as [HxL Hxbody].
  pose proof (related_subst_extend _ _ _ x A v1 v2 Henv Hv1 Hv2 Hr)
    as Hext.
  pose proof (Hbody x HxL _ _ Hext) as Hterm.
  destruct Hext as [HlcExt _].
  rewrite (instantiate_open_extended body rho1 x v1 Hxbody
             (fun y => proj1 (HlcExt y))) in Hterm.
  rewrite (instantiate_open_extended body rho2 x v2 Hxbody
             (fun y => proj2 (HlcExt y))) in Hterm.
  exact Hterm.
Qed.

Lemma evaluates_case_part : forall t b1 b2 r v,
  evaluates (tm_case t b1 b2 r) v ->
  exists w, evaluates t w /\ evaluates (tm_case w b1 b2 r) v.
Proof.
  intros t b1 b2 r v [Hm Hv].
  remember (tm_case t b1 b2 r) as q eqn:Eq.
  revert t b1 b2 r Eq.
  induction Hm as [q | q q' q'' Hs Hm IH];
    intros arg left right lab Eq; subst.
  - inversion Hv.
  - inversion Hs; subst.
    + match goal with
      | Hc : step (tm_case (tm_inl ?u ?sec) _ _ _) _ |- _ =>
          exists (tm_inl u sec)
      end.
      split; [apply evaluates_value; constructor; assumption |].
      split; [econstructor; eauto | exact Hv].
    + match goal with
      | Hc : step (tm_case (tm_inr ?u ?sec) _ _ _) _ |- _ =>
          exists (tm_inr u sec)
      end.
      split; [apply evaluates_value; constructor; assumption |].
      split; [econstructor; eauto | exact Hv].
    + destruct (IH Hv _ _ _ _ eq_refl) as (w & He & Hcase).
      exists w. split; [eapply evaluates_step_back; eauto | exact Hcase].
Qed.

Lemma evaluates_case_inl_result : forall a k b1 b2 r w,
  value a ->
  evaluates (tm_case (tm_inl a k) b1 b2 r) w ->
  evaluates (tm_protect k.(indirect_reader) (open b1 a)) w.
Proof.
  intros a k b1 b2 r w Ha [Hm Hw].
  inversion Hm; subst; [inversion Hw |].
  inversion H; subst.
  - split; assumption.
  - exfalso.
    assert (Hi : value (tm_inl a k)) by (constructor; assumption).
    eapply value_no_step; eauto.
Qed.

Lemma evaluates_case_inr_result : forall a k b1 b2 r w,
  value a ->
  evaluates (tm_case (tm_inr a k) b1 b2 r) w ->
  evaluates (tm_protect k.(indirect_reader) (open b2 a)) w.
Proof.
  intros a k b1 b2 r w Ha [Hm Hw].
  inversion Hm; subst; [inversion Hw |].
  inversion H; subst.
  - split; assumption.
  - exfalso.
    assert (Hi : value (tm_inr a k)) by (constructor; assumption).
    eapply value_no_step; eauto.
Qed.

Lemma related_case : forall L Gamma A B T k r t b1 b2 rho1 rho2,
  related_term (Ty_Sum A B k) (instantiate rho1 t) (instantiate rho2 t) ->
  (forall x, ~ In x L ->
    forall sigma1 sigma2,
      related_subst (update Gamma x A) sigma1 sigma2 ->
      related_term T
        (instantiate sigma1 (open b1 (tm_fvar x)))
        (instantiate sigma2 (open b1 (tm_fvar x)))) ->
  (forall x, ~ In x L ->
    forall sigma1 sigma2,
      related_subst (update Gamma x B) sigma1 sigma2 ->
      related_term T
        (instantiate sigma1 (open b2 (tm_fvar x)))
        (instantiate sigma2 (open b2 (tm_fvar x)))) ->
  related_subst Gamma rho1 rho2 ->
  related_term (ty_protect k.(indirect_reader) T)
    (instantiate rho1 (tm_case t b1 b2 r))
    (instantiate rho2 (tm_case t b1 b2 r)).
Proof.
  intros L Gamma A B T k r t b1 b2 rho1 rho2 Hscr Hleft Hright Henv.
  intros w1 w2 He1 He2.
  destruct (indirect_reader k) eqn:E; [|apply related_value_high].
  rewrite ty_protect_low.
  simpl in He1, He2.
  destruct (evaluates_case_part _ _ _ _ _ He1)
    as (s1 & Hs1 & Hcase1).
  destruct (evaluates_case_part _ _ _ _ _ He2)
    as (s2 & Hs2 & Hcase2).
  specialize (Hscr _ _ Hs1 Hs2).
  simpl in Hscr; rewrite E in Hscr.
  destruct Hscr as
    [(a1 & a2 & k1 & k2 & Es1 & Es2 & Hk1 & Hk2 & Ha) |
     (a1 & a2 & k1 & k2 & Es1 & Es2 & Hk1 & Hk2 & Ha)];
    subst s1 s2.
  - destruct Hs1 as [_ Vs1], Hs2 as [_ Vs2].
    inversion Vs1; subst; inversion Vs2; subst.
    pose proof (evaluates_case_inl_result _ _ _ _ _ _ H0 Hcase1)
      as Hp1.
    pose proof (evaluates_case_inl_result _ _ _ _ _ _ H1 Hcase2)
      as Hp2.
    rewrite Hk1 in Hp1; rewrite Hk2 in Hp2.
    apply evaluates_protect_low_inv in Hp1.
    apply evaluates_protect_low_inv in Hp2.
    pose proof (related_open_branch L Gamma A b1 T rho1 rho2
                  a1 a2 Hleft Henv H0 H1 Ha) as Hbody.
    apply (Hbody w1 w2); assumption.
  - destruct Hs1 as [_ Vs1], Hs2 as [_ Vs2].
    inversion Vs1; subst; inversion Vs2; subst.
    pose proof (evaluates_case_inr_result _ _ _ _ _ _ H0 Hcase1)
      as Hp1.
    pose proof (evaluates_case_inr_result _ _ _ _ _ _ H1 Hcase2)
      as Hp2.
    rewrite Hk1 in Hp1; rewrite Hk2 in Hp2.
    apply evaluates_protect_low_inv in Hp1.
    apply evaluates_protect_low_inv in Hp2.
    pose proof (related_open_branch L Gamma B b2 T rho1 rho2
                  a1 a2 Hright Henv H0 H1 Ha) as Hbody.
    apply (Hbody w1 w2); assumption.
Qed.

Lemma related_natrec_unroll : forall n T b1 b2 s1 s2 r,
  related_term T b1 b2 ->
  related_term
    (Ty_Arrow (Ty_Nat public) (Ty_Arrow T T public) public) s1 s2 ->
  related_term T
    (natrec_unroll n b1 s1 r) (natrec_unroll n b2 s2 r).
Proof.
  induction n as [|n IH]; intros T b1 b2 s1 s2 r Hb Hs; simpl.
  - exact Hb.
  - rewrite <- (ty_protect_low T).
    apply (related_app T T public r
             (tm_app s1 (tm_nat n public) r)
             (tm_app s2 (tm_nat n public) r)
             (natrec_unroll n b1 s1 r)
             (natrec_unroll n b2 s2 r)).
    + change
        (related_term (Ty_Arrow T T public)
           (tm_app s1 (tm_nat n public) r)
           (tm_app s2 (tm_nat n public) r)).
      rewrite <- (ty_protect_low (Ty_Arrow T T public)).
      apply (related_app (Ty_Nat public) (Ty_Arrow T T public)
               public r s1 s2 (tm_nat n public) (tm_nat n public));
        eauto using related_nat.
      unfold flows_to; destruct r; exact I.
    + apply IH; assumption.
    + unfold flows_to; destruct r; exact I.
Qed.

Lemma evaluates_natrec_parts : forall n b s r v,
  evaluates (tm_natrec n b s r) v ->
  exists vn vb vs,
    evaluates n vn /\ evaluates b vb /\ evaluates s vs /\
    evaluates (tm_natrec vn vb vs r) v.
Proof.
  intros n b s r v [Hm Hv].
  remember (tm_natrec n b s r) as q eqn:Eq.
  revert n b s r Eq.
  induction Hm as [q | q q' q'' Hstep Hm IH];
    intros count base stepfun lab Eq; subst.
  - inversion Hv.
  - inversion Hstep; subst.
    + destruct (IH Hv _ _ _ _ eq_refl)
        as (vn & vb & vs & Hn & Hb & Hs & Hr).
      exists vn, vb, vs. split; [eapply evaluates_step_back; eauto |].
      split; [exact Hb |]. split; assumption.
    + destruct (IH Hv _ _ _ _ eq_refl)
        as (vn & vb & vs & Hn & Hb & Hs & Hr).
      exists vn, vb, vs. split; [exact Hn |].
      split; [eapply evaluates_step_back; eauto |].
      split; assumption.
    + destruct (IH Hv _ _ _ _ eq_refl)
        as (vn & vb & vs & Hn & Hb & Hs & Hr).
      exists vn, vb, vs. split; [exact Hn |].
      split; [exact Hb |].
      split; [eapply evaluates_step_back; eauto | exact Hr].
    + match goal with
      | Hu : step (tm_natrec (tm_nat ?num ?sec) ?bb ?ss ?rr) _ |- _ =>
          exists (tm_nat num sec), bb, ss
      end.
      split; [apply evaluates_value; constructor |].
      split; [apply evaluates_value; assumption |].
      split; [apply evaluates_value; assumption |].
      split; [econstructor; eauto | exact Hv].
Qed.

Lemma evaluates_natrec_unroll_result : forall n k b s r w,
  value b -> value s ->
  evaluates (tm_natrec (tm_nat n k) b s r) w ->
  evaluates (tm_protect k.(indirect_reader) (natrec_unroll n b s r)) w.
Proof.
  intros n k b s r w Hb Hs [Hm Hw].
  inversion Hm; subst; [inversion Hw |].
  inversion H; subst; try (split; assumption);
    exfalso;
    multimatch goal with Hst : step ?x _ |- _ =>
      eapply (value_no_step x _);
        [solve [eauto using value] | exact Hst]
    end.
Qed.

Lemma related_natrec : forall T k r n1 n2 b1 b2 s1 s2,
  related_term (Ty_Nat k) n1 n2 ->
  related_term T b1 b2 ->
  related_term
    (Ty_Arrow (Ty_Nat public) (Ty_Arrow T T public) public) s1 s2 ->
  related_term (ty_protect k.(indirect_reader) T)
    (tm_natrec n1 b1 s1 r) (tm_natrec n2 b2 s2 r).
Proof.
  intros T k r n1 n2 b1 b2 s1 s2 Hn Hb Hs w1 w2 He1 He2.
  destruct (indirect_reader k) eqn:E; [|apply related_value_high].
  rewrite ty_protect_low.
  destruct (evaluates_natrec_parts _ _ _ _ _ He1)
    as (vn1 & vb1 & vs1 & Hn1 & Hb1 & Hs1 & Hrec1).
  destruct (evaluates_natrec_parts _ _ _ _ _ He2)
    as (vn2 & vb2 & vs2 & Hn2 & Hb2 & Hs2 & Hrec2).
  specialize (Hn _ _ Hn1 Hn2).
  simpl in Hn; rewrite E in Hn.
  destruct Hn as (num & k1 & k2 & En1 & En2 & Hk1 & Hk2).
  subst vn1 vn2.
  pose proof (Hb _ _ Hb1 Hb2) as Hbv.
  pose proof (Hs _ _ Hs1 Hs2) as Hsv.
  destruct Hb1 as [_ Vb1], Hb2 as [_ Vb2].
  destruct Hs1 as [_ Vs1], Hs2 as [_ Vs2].
  pose proof (related_value_as_term T vb1 vb2 Vb1 Vb2 Hbv) as Hbt.
  pose proof (related_value_as_term
                (Ty_Arrow (Ty_Nat public) (Ty_Arrow T T public) public)
                vs1 vs2 Vs1 Vs2 Hsv) as Hst.
  pose proof (related_natrec_unroll num T vb1 vb2 vs1 vs2 r Hbt Hst)
    as Hunroll.
  pose proof (evaluates_natrec_unroll_result _ _ _ _ _ _ Vb1 Vs1 Hrec1)
    as Hu1.
  pose proof (evaluates_natrec_unroll_result _ _ _ _ _ _ Vb2 Vs2 Hrec2)
    as Hu2.
  rewrite Hk1 in Hu1; rewrite Hk2 in Hu2.
  apply evaluates_protect_low_inv in Hu1.
  apply evaluates_protect_low_inv in Hu2.
  apply (Hunroll w1 w2); assumption.
Qed.

Lemma related_term_subtype : forall T U t1 t2,
  subtype T U -> related_term T t1 t2 -> related_term U t1 t2.
Proof.
  intros T U t1 t2 Hsub Hr v1 v2 He1 He2.
  apply (related_value_subtype T U Hsub).
  apply (Hr v1 v2); assumption.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho1 rho2,
    related_subst Gamma rho1 rho2 ->
    related_term T (instantiate rho1 t) (instantiate rho2 t).
Proof.
  intros Gamma t T Hty.
  induction Hty; intros rho1 rho2 Henv; simpl.
  - apply (proj2 Henv x T); assumption.
  - apply related_unit.
  - eapply related_abs; eauto.
  - eapply related_app; eauto.
  - eapply related_pair; eauto.
  - eapply related_fst; eauto.
  - eapply related_snd; eauto.
  - eapply related_inl; eauto.
  - eapply related_inr; eauto.
  - eapply related_case; eauto.
  - eapply related_protect; eauto.
  - eapply related_term_subtype; eauto.
  - apply related_nat.
  - eapply related_succ; eauto.
  - eapply related_natrec; eauto.
Qed.

Lemma lc_open_fvar_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x Hlc; simpl in *;
    try exact I;
    try solve [destruct Hlc; split; eauto];
    try solve [destruct Hlc as [? [? ?]]; repeat split; eauto];
    try solve [eauto].
  destruct (Nat.eqb k n) eqn:E.
  - apply Nat.eqb_eq in E; lia.
  - simpl in Hlc; lia.
Qed.

Lemma typing_locally_closed : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty; induction Hty;
    unfold locally_closed in *; simpl in *;
    try exact I;
    try solve [repeat split; auto].
  - destruct (fresh_atom L) as [x Hfresh].
    apply lc_open_fvar_inv with (x := x).
    apply H2; assumption.
  - destruct (fresh_atom L) as [x Hfresh].
    repeat split; auto.
    + apply lc_open_fvar_inv with (x := x).
      apply H1; assumption.
    + apply lc_open_fvar_inv with (x := x).
      apply H3; assumption.
Qed.

Definition identity_subst : atom -> tm := tm_fvar.

Definition hole_subst (x : atom) (t : tm) : atom -> tm :=
  extend_subst identity_subst x t.

Lemma instantiate_identity : forall t,
  instantiate identity_subst t = t.
Proof.
  induction t; simpl; f_equal; auto.
Qed.

Lemma instantiate_hole_fresh : forall u x t,
  ~ In x (fv u) -> instantiate (hole_subst x t) u = u.
Proof.
  intros u x t Hfresh.
  unfold hole_subst.
  rewrite instantiate_extend_fresh by exact Hfresh.
  apply instantiate_identity.
Qed.

Lemma instantiate_plug_hole : forall C x t,
  ~ In x (fv (plug C (tm_unit public))) ->
  instantiate (hole_subst x t) (plug C (tm_fvar x)) = plug C t.
Proof.
  induction C; intros x u Hfresh; simpl in *.
  all: try solve [unfold hole_subst, extend_subst, identity_subst;
                  simpl; rewrite Nat.eqb_refl; reflexivity].
  all: repeat rewrite in_app_iff in Hfresh;
      simpl; f_equal;
      first [apply IHC; tauto |
             apply instantiate_hole_fresh; tauto |
             reflexivity].
Qed.

Lemma nonflow_labels : forall a b,
  ~ flows_to a b -> a = High /\ b = Low.
Proof. destruct a, b; simpl; tauto. Qed.

Lemma related_term_high : forall T t1 t2,
  (security_of T).(indirect_reader) = High ->
  related_term T t1 t2.
Proof.
  destruct T; intros t1 t2 Hhigh v1 v2 _ _;
    simpl in *; rewrite Hhigh; exact I.
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
  intros C t1 t2 T_secret T_result Hty1 Hty2 Hctx Hground Htrans Hnonflow.
  destruct (nonflow_labels _ _ Hnonflow) as [Hsecret Hresult].
  destruct Hctx as [L Hctx].
  destruct (fresh_atom (L ++ fv (plug C (tm_unit public))))
    as [x Hfresh].
  apply not_in_app_split in Hfresh.
  destruct Hfresh as [HxL HxC].
  pose proof (Hctx x HxL) as Hprogram.
  assert (Henv : related_subst (update empty x T_secret)
                   (hole_subst x t1) (hole_subst x t2)).
  { split.
    - intros y. unfold hole_subst, extend_subst, identity_subst.
      destruct (Nat.eqb x y).
      + split; [eapply typing_locally_closed; exact Hty1 |
                eapply typing_locally_closed; exact Hty2].
      + split; unfold locally_closed; simpl; exact I.
    - intros y U Hlookup.
      unfold update, empty in Hlookup; simpl in Hlookup.
      destruct (Nat.eqb y x) eqn:E; [|discriminate].
      apply Nat.eqb_eq in E; subst y.
      inversion Hlookup; subst U.
      unfold hole_subst, extend_subst.
      rewrite Nat.eqb_refl.
      apply related_term_high; exact Hsecret.
  }
  pose proof (fundamental _ _ _ Hprogram _ _ Henv) as Hrel.
  rewrite (instantiate_plug_hole C x t1 HxC) in Hrel.
  rewrite (instantiate_plug_hole C x t2 HxC) in Hrel.
  intros v1 v2 He1 He2.
  eapply related_ground_erases.
  - exact Hresult.
  - exact Hground.
  - exact Htrans.
  - apply (Hrel v1 v2); assumption.
Qed.
