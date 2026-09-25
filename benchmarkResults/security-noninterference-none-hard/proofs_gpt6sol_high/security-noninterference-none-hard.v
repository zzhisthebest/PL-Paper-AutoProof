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
  | tm_protect : label -> tm -> tm.

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
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_unit _ => []
  | tm_fvar x => [x]
  | tm_abs _ body _ => fv body
  | tm_app t1 t2 _ | tm_pair t1 t2 _ => fv t1 ++ fv t2
  | tm_fst t1 _ | tm_snd t1 _ | tm_inl t1 _ | tm_inr t1 _
  | tm_protect _ t1 => fv t1
  | tm_case t0 body1 body2 _ => fv t0 ++ fv body1 ++ fv body2
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
      has_type Gamma t T -> subtype T U -> has_type Gamma t U.

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
  | C_Protect : label -> program_context -> program_context.

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

(* A natural semantics is useful for the logical relation: its final-value
   clauses expose exactly the premises needed by each typing constructor. *)
Inductive eval : tm -> tm -> Prop :=
  | E_Unit : forall k, eval (tm_unit k) (tm_unit k)
  | E_Abs : forall A body k, eval (tm_abs A body k) (tm_abs A body k)
  | E_App : forall f a A body k v w r,
      eval f (tm_abs A body k) -> eval a v ->
      eval (open body v) w -> flows_to k.(reader) r ->
      eval (tm_app f a r) (protect_value w k.(indirect_reader))
  | E_Pair : forall a b v w k,
      eval a v -> eval b w ->
      eval (tm_pair a b k) (tm_pair v w k)
  | E_Fst : forall t v w k r,
      eval t (tm_pair v w k) -> flows_to k.(reader) r ->
      eval (tm_fst t r) (protect_value v k.(indirect_reader))
  | E_Snd : forall t v w k r,
      eval t (tm_pair v w k) -> flows_to k.(reader) r ->
      eval (tm_snd t r) (protect_value w k.(indirect_reader))
  | E_Inl : forall t v k,
      eval t v -> eval (tm_inl t k) (tm_inl v k)
  | E_Inr : forall t v k,
      eval t v -> eval (tm_inr t k) (tm_inr v k)
  | E_CaseL : forall t v k b1 b2 w r,
      eval t (tm_inl v k) -> eval (open b1 v) w ->
      flows_to k.(reader) r ->
      eval (tm_case t b1 b2 r) (protect_value w k.(indirect_reader))
  | E_CaseR : forall t v k b1 b2 w r,
      eval t (tm_inr v k) -> eval (open b2 v) w ->
      flows_to k.(reader) r ->
      eval (tm_case t b1 b2 r) (protect_value w k.(indirect_reader))
  | E_Protect : forall l t v,
      eval t v -> eval (tm_protect l t) (protect_value v l).

Fixpoint unary_value (T : ty) (v : tm) : Prop :=
  closed v /\ match T with
  | Ty_Unit _ => exists k, v = tm_unit k
  | Ty_Sum A B _ =>
      (exists u k, v = tm_inl u k /\ unary_value A u) \/
      (exists u k, v = tm_inr u k /\ unary_value B u)
  | Ty_Prod A B _ =>
      exists u w k, v = tm_pair u w k /\
        unary_value A u /\ unary_value B w
  | Ty_Arrow A B _ =>
      exists A' body k, v = tm_abs A' body k /\
        (forall u w, unary_value A u -> eval (open body u) w ->
          unary_value B w)
  end.

Definition unary_term (T : ty) (t : tm) : Prop :=
  forall v, eval t v -> unary_value T v.

Fixpoint related_value (T : ty) (v1 v2 : tm) : Prop :=
  unary_value T v1 /\ unary_value T v2 /\
  match (security_of T).(indirect_reader) with
  | High => True
  | Low =>
      match T with
      | Ty_Unit _ => True
      | Ty_Sum A B _ =>
          (exists u1 u2 k1 k2,
            v1 = tm_inl u1 k1 /\ v2 = tm_inl u2 k2 /\
            related_value A u1 u2) \/
          (exists u1 u2 k1 k2,
            v1 = tm_inr u1 k1 /\ v2 = tm_inr u2 k2 /\
            related_value B u1 u2)
      | Ty_Prod A B _ =>
          exists u1 u2 w1 w2 k1 k2,
            v1 = tm_pair u1 w1 k1 /\ v2 = tm_pair u2 w2 k2 /\
            related_value A u1 u2 /\ related_value B w1 w2
      | Ty_Arrow A B _ =>
          exists A1 body1 k1 A2 body2 k2,
            v1 = tm_abs A1 body1 k1 /\ v2 = tm_abs A2 body2 k2 /\
            (forall u1 u2 w1 w2,
              related_value A u1 u2 ->
              eval (open body1 u1) w1 -> eval (open body2 u2) w2 ->
              related_value B w1 w2)
      end
  end.

Definition related_term (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, eval t1 v1 -> eval t2 v2 -> related_value T v1 v2.

Lemma unary_subtype : forall A B v,
  subtype A B -> unary_value A v -> unary_value B v.
Proof.
  intros A B v H; revert v; induction H; intros v Hv; simpl in *.
  all: try (destruct Hv as [Hclosed Hv]; split; [exact Hclosed |]).
  - exact Hv.
  - destruct Hv as [[u [k [-> Hu]]] | [u [k [-> Hu]]]].
    + left. exists u, k. split; [reflexivity | eauto].
    + right. exists u, k. split; [reflexivity | eauto].
  - destruct Hv as [u [w [k [-> [Hu Hw]]]]].
    exists u, w, k. repeat split; eauto.
  - destruct Hv as [A' [body [k [-> Hbody]]]].
    exists A', body, k. split; [reflexivity |].
    intros u w Hu He. eapply IHsubtype2; eauto.
  - eauto.
Qed.

Lemma related_subtype : forall A B v1 v2,
  subtype A B -> related_value A v1 v2 -> related_value B v1 v2.
Proof.
  intros A B v1 v2 H; revert v1 v2; induction H; intros v1 v2 Hr.
  - destruct kappa1 as [r1 i1], kappa2 as [r2 i2].
    simpl in *. destruct Hr as [Hu1 [Hu2 _]].
    split; [exact Hu1 |]. split; [exact Hu2 |].
    unfold security_le in H1. destruct H1 as [_ Hflow].
    destruct i1, i2; simpl in *; tauto.
  - destruct kappa1 as [r1 i1], kappa2 as [r2 i2].
    simpl in *. destruct Hr as [Hu1 [Hu2 Hrel]].
    assert (HS : subtype (Ty_Sum T1 T2 {| reader := r1; indirect_reader := i1 |})
      (Ty_Sum U1 U2 {| reader := r2; indirect_reader := i2 |}))
      by (eapply S_Sum; eauto).
    pose proof (unary_subtype _ _ _ HS Hu1) as Hu1'.
    pose proof (unary_subtype _ _ _ HS Hu2) as Hu2'.
    split; [exact Hu1' |]. split; [exact Hu2' |].
    unfold security_le in H3. destruct H3 as [_ Hflow].
    destruct i1, i2; simpl in *; try tauto.
    destruct Hrel as [[u1 [u2 [k1 [k2 [-> [-> Huv]]]]]] |
                      [u1 [u2 [k1 [k2 [-> [-> Huv]]]]]]].
    + left. exists u1, u2, k1, k2. repeat split; eauto.
    + right. exists u1, u2, k1, k2. repeat split; eauto.
  - destruct kappa1 as [r1 i1], kappa2 as [r2 i2].
    simpl in *. destruct Hr as [Hu1 [Hu2 Hrel]].
    assert (HS : subtype (Ty_Prod T1 T2 {| reader := r1; indirect_reader := i1 |})
      (Ty_Prod U1 U2 {| reader := r2; indirect_reader := i2 |}))
      by (eapply S_Prod; eauto).
    pose proof (unary_subtype _ _ _ HS Hu1) as Hu1'.
    pose proof (unary_subtype _ _ _ HS Hu2) as Hu2'.
    split; [exact Hu1' |]. split; [exact Hu2' |].
    unfold security_le in H3. destruct H3 as [_ Hflow].
    destruct i1, i2; simpl in *; try tauto.
    destruct Hrel as [u1 [u2 [w1 [w2 [k1 [k2
      [-> [-> [Huv Hwv]]]]]]]]].
    exists u1, u2, w1, w2, k1, k2. repeat split; eauto.
  - destruct kappa1 as [r1 i1], kappa2 as [r2 i2].
    simpl in *. destruct Hr as [Hu1 [Hu2 Hrel]].
    assert (HS : subtype (Ty_Arrow T1 T2 {| reader := r1; indirect_reader := i1 |})
      (Ty_Arrow U1 U2 {| reader := r2; indirect_reader := i2 |}))
      by (eapply S_Arrow; eauto).
    pose proof (unary_subtype _ _ _ HS Hu1) as Hu1'.
    pose proof (unary_subtype _ _ _ HS Hu2) as Hu2'.
    split; [exact Hu1' |]. split; [exact Hu2' |].
    unfold security_le in H3. destruct H3 as [_ Hflow].
    destruct i1, i2; simpl in *; try tauto.
    destruct Hrel as [A1 [b1 [k1 [A2 [b2 [k2
      [-> [-> Hbody]]]]]]]].
    exists A1, b1, k1, A2, b2, k2. repeat split; try reflexivity.
    intros u1 u2 w1 w2 Hargs He1 He2.
    eapply IHsubtype2. eapply Hbody; eauto.
  - eauto.
Qed.

Lemma protect_value_closed : forall v l,
  closed v -> closed (protect_value v l).
Proof.
  intros v l H; destruct v; simpl in *; exact H.
Qed.

Lemma unary_protect : forall T v l,
  unary_value T v -> unary_value (ty_protect l T) (protect_value v l).
Proof.
  intros T v l H; destruct T; simpl in *.
  - destruct H as [Hc [k ->]]. split.
    + apply protect_value_closed. exact Hc.
    + exists (protect_security k l). reflexivity.
  - destruct H as [Hc [[u [k [-> Hu]]] | [u [k [-> Hu]]]]]; split.
    + apply protect_value_closed. exact Hc.
    + left. exists u, (protect_security k l). auto.
    + apply protect_value_closed. exact Hc.
    + right. exists u, (protect_security k l). auto.
  - destruct H as [Hc [u [w [k [-> [Hu Hw]]]]]]. split.
    + apply protect_value_closed. exact Hc.
    + exists u, w, (protect_security k l). auto.
  - destruct H as [Hc [A [body [k [-> Hbody]]]]]. split.
    + apply protect_value_closed. exact Hc.
    + exists A, body, (protect_security k l). auto.
Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof.
  intros T. destruct T; destruct s; destruct reader0, indirect_reader0;
    reflexivity.
Qed.

Lemma protect_value_low_sem : forall T v,
  unary_value T v -> protect_value v Low = v.
Proof.
  intros T v H; destruct T; simpl in H; destruct H as [_ H].
  - destruct H as [k ->]. destruct k as [r i]; destruct r, i; reflexivity.
  - destruct H as [[u [k [-> _]]] | [u [k [-> _]]]];
      destruct k as [r i]; destruct r, i; reflexivity.
  - destruct H as [u [w [k [-> _]]]].
    destruct k as [r i]; destruct r, i; reflexivity.
  - destruct H as [A [body [k [-> _]]]].
    destruct k as [r i]; destruct r, i; reflexivity.
Qed.

Lemma related_unary_left : forall T v1 v2,
  related_value T v1 v2 -> unary_value T v1.
Proof. intros T v1 v2 H; destruct T; simpl in *; tauto. Qed.

Lemma related_unary_right : forall T v1 v2,
  related_value T v1 v2 -> unary_value T v2.
Proof. intros T v1 v2 H; destruct T; simpl in *; tauto. Qed.

Lemma related_high_of_unary : forall T v1 v2,
  (security_of T).(indirect_reader) = High ->
  unary_value T v1 -> unary_value T v2 -> related_value T v1 v2.
Proof.
  intros T v1 v2 Hhigh Hu1 Hu2.
  destruct T; destruct s as [r i]; destruct r, i; simpl in *;
    try discriminate; tauto.
Qed.

Lemma indirect_protect_high : forall T,
  (security_of (ty_protect High T)).(indirect_reader) = High.
Proof.
  intros T; destruct T; destruct s as [r i]; destruct r, i;
    reflexivity.
Qed.

Lemma related_protect : forall T v1 v2 l,
  related_value T v1 v2 ->
  related_value (ty_protect l T) (protect_value v1 l) (protect_value v2 l).
Proof.
  intros T v1 v2 l H.
  pose proof (related_unary_left T v1 v2 H) as Hu1.
  pose proof (related_unary_right T v1 v2 H) as Hu2.
  destruct l.
  - rewrite ty_protect_low.
    rewrite (protect_value_low_sem T v1 Hu1).
    rewrite (protect_value_low_sem T v2 Hu2).
    exact H.
  - apply related_high_of_unary.
    + apply indirect_protect_high.
    + apply unary_protect. exact Hu1.
    + apply unary_protect. exact Hu2.
Qed.

Lemma protect_value_is_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l Hv; induction Hv; simpl.
  - constructor.
  - constructor. exact H.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma eval_value_self : forall v, value v -> eval v v.
Proof.
  intros v Hv; induction Hv; eauto using eval.
Qed.

Lemma eval_value_inv : forall v w,
  value v -> eval v w -> w = v.
Proof.
  intros v w Hv. revert w.
  induction Hv; intros w He; inversion He; subst; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma step_eval_back : forall t t' w,
  step t t' -> eval t' w -> eval t w.
Proof.
  intros t t' w Hs. revert w.
  induction Hs; intros w Hw;
    try solve [inversion Hw; subst; eauto using eval, eval_value_self].
  pose proof (eval_value_inv _ _ (protect_value_is_value v l H) Hw) as Heq.
  subst w. apply E_Protect. apply eval_value_self. exact H.
Qed.

Lemma multi_value_eval : forall t v,
  evaluates t v -> eval t v.
Proof.
  intros t v [Hm Hv]. induction Hm.
  - apply eval_value_self. exact Hv.
  - eapply step_eval_back; eauto.
Qed.

Lemma transparent_at_low : forall k T,
  transparent_at k T -> k.(indirect_reader) = Low ->
  (security_of T).(indirect_reader) = Low.
Proof.
  intros [r i] T Htr Hi. simpl in Hi. subst i.
  destruct T; simpl in *;
    destruct Htr as [Hle _];
    unfold security_le in Hle; destruct Hle as [_ Hflow];
    destruct s as [r' i']; destruct i'; simpl in *; auto; contradiction.
Qed.

Lemma related_ground_erasure : forall T k v1 v2,
  ground T -> transparent_at k T -> k.(indirect_reader) = Low ->
  related_value T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  induction T; intros k v1 v2 Hg Htr Hkl Hr.
  - pose proof (transparent_at_low k (Ty_Unit s) Htr Hkl) as Hlow.
    destruct s as [r i]; simpl in Hlow. subst i.
    simpl in Hr. destruct Hr as [[_ [k1 ->]] [[_ [k2 ->]] _]].
    reflexivity.
  - pose proof (transparent_at_low k (Ty_Sum T1 T2 s) Htr Hkl) as Hlow.
    destruct s as [r i]; simpl in Hlow. subst i.
    simpl in Hg, Htr, Hr.
    destruct Htr as [_ [Htr1 Htr2]].
    destruct Hg as [Hg1 Hg2].
    destruct Hr as [_ [_ [
      [u1 [u2 [k1 [k2 [-> [-> Huv]]]]]] |
      [u1 [u2 [k1 [k2 [-> [-> Huv]]]]]]]]].
    + simpl. f_equal. eapply IHT1; eauto.
    + simpl. f_equal. eapply IHT2; eauto.
  - pose proof (transparent_at_low k (Ty_Prod T1 T2 s) Htr Hkl) as Hlow.
    destruct s as [r i]; simpl in Hlow. subst i.
    simpl in Hg, Htr, Hr.
    destruct Htr as [_ [Htr1 Htr2]].
    destruct Hg as [Hg1 Hg2].
    destruct Hr as [_ [_ [u1 [u2 [w1 [w2 [k1 [k2
      [-> [-> [Huv Hwv]]]]]]]]]]].
    simpl. f_equal; [eapply IHT1 | eapply IHT2]; eauto.
  - contradiction.
Qed.

Definition replacement := list (atom * tm).

Fixpoint lookup_replacement (rho : replacement) (x : atom) : tm :=
  match rho with
  | [] => tm_unit public
  | (y, v) :: rho' =>
      if Nat.eqb x y then v else lookup_replacement rho' x
  end.

Fixpoint instantiate (rho : replacement) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => lookup_replacement rho x
  | tm_unit k => tm_unit k
  | tm_abs A body k => tm_abs A (instantiate rho body) k
  | tm_app f a r => tm_app (instantiate rho f) (instantiate rho a) r
  | tm_pair a b k => tm_pair (instantiate rho a) (instantiate rho b) k
  | tm_fst t r => tm_fst (instantiate rho t) r
  | tm_snd t r => tm_snd (instantiate rho t) r
  | tm_inl t k => tm_inl (instantiate rho t) k
  | tm_inr t k => tm_inr (instantiate rho t) k
  | tm_case t b1 b2 r =>
      tm_case (instantiate rho t) (instantiate rho b1) (instantiate rho b2) r
  | tm_protect l t => tm_protect l (instantiate rho t)
  end.

Definition replacement_closed (rho : replacement) : Prop :=
  forall x, closed (lookup_replacement rho x).

Definition unary_environment (Gamma : context) (rho : replacement) : Prop :=
  replacement_closed rho /\
  forall x T, lookup_context x Gamma = Some T ->
    unary_term T (lookup_replacement rho x).

Definition related_environment (Gamma : context)
    (rho1 rho2 : replacement) : Prop :=
  unary_environment Gamma rho1 /\ unary_environment Gamma rho2 /\
  forall x T, lookup_context x Gamma = Some T ->
    related_term T (lookup_replacement rho1 x) (lookup_replacement rho2 x).

Lemma related_environment_unary_left : forall Gamma rho1 rho2,
  related_environment Gamma rho1 rho2 -> unary_environment Gamma rho1.
Proof.
  intros Gamma rho1 rho2 [H _]. exact H.
Qed.

Lemma related_environment_unary_right : forall Gamma rho1 rho2,
  related_environment Gamma rho1 rho2 -> unary_environment Gamma rho2.
Proof.
  intros Gamma rho1 rho2 [_ [H _]]. exact H.
Qed.

Lemma lc_at_weaken : forall t k k',
  k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  induction t; intros k k' Hle Hlc; simpl in *;
    try tauto; try lia;
    try (eapply IHt; eauto; lia);
    try (split; [eapply IHt1; eauto; lia |
                 eapply IHt2; eauto; lia]).
  - apply (IHt (S k) (S k')); try lia. exact Hlc.
  - destruct Hlc as [H1 H2]. split.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - destruct Hlc as [H1 H2]. split.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - destruct Hlc as [H0 [H1 H2]]. repeat split.
    + eapply IHt1; eauto.
    + apply (IHt2 (S k) (S k')); try lia. exact H1.
    + apply (IHt3 (S k) (S k')); try lia. exact H2.
Qed.

Lemma open_rec_on_lc : forall t k u,
  lc_at k t -> open_rec k u t = t.
Proof.
  induction t; intros k u Hlc; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - f_equal. apply IHt. exact Hlc.
  - destruct Hlc as [H1 H2].
    rewrite (IHt1 _ _ H1), (IHt2 _ _ H2). reflexivity.
  - destruct Hlc as [H1 H2].
    rewrite (IHt1 _ _ H1), (IHt2 _ _ H2). reflexivity.
  - f_equal. apply IHt. exact Hlc.
  - f_equal. apply IHt. exact Hlc.
  - f_equal. apply IHt. exact Hlc.
  - f_equal. apply IHt. exact Hlc.
  - destruct Hlc as [H1 [H2 H3]].
    rewrite (IHt1 _ _ H1), (IHt2 _ _ H2), (IHt3 _ _ H3).
    reflexivity.
  - f_equal. apply IHt. exact Hlc.
Qed.

Lemma instantiate_lc_at : forall t rho k,
  replacement_closed rho -> lc_at k t -> lc_at k (instantiate rho t).
Proof.
  induction t; intros rho k Hrho Hlc; simpl in *; try tauto.
  - apply (lc_at_weaken (lookup_replacement rho a) 0 k).
    + lia.
    + exact (proj1 (Hrho a)).
  - apply IHt; assumption.
  - destruct Hlc as [H1 H2]. split;
      [apply IHt1 | apply IHt2]; assumption.
  - destruct Hlc as [H1 H2]. split;
      [apply IHt1 | apply IHt2]; assumption.
  - apply IHt; assumption.
  - apply IHt; assumption.
  - apply IHt; assumption.
  - apply IHt; assumption.
  - destruct Hlc as [H1 [H2 H3]]. repeat split;
      [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
  - apply IHt; assumption.
Qed.

Lemma instantiate_fv_nil : forall t rho,
  replacement_closed rho -> fv (instantiate rho t) = [].
Proof.
  induction t; intros rho Hrho; simpl; try reflexivity;
    try (apply IHt; assumption);
    try (rewrite IHt1, IHt2; auto; reflexivity).
  - exact (proj2 (Hrho a)).
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma instantiate_closed : forall t rho,
  locally_closed t -> replacement_closed rho -> closed (instantiate rho t).
Proof.
  intros t rho Hlc Hrho. split.
  - apply instantiate_lc_at; assumption.
  - apply instantiate_fv_nil; assumption.
Qed.

Lemma opened_lc_body : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x Hlc; simpl in *; try tauto.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + simpl in Hlc. lia.
  - apply IHt with (x := x). exact Hlc.
  - destruct Hlc as [H1 H2]. split;
      [apply (IHt1 k x) | apply (IHt2 k x)]; assumption.
  - destruct Hlc as [H1 H2]. split;
      [apply (IHt1 k x) | apply (IHt2 k x)]; assumption.
  - apply IHt with (x := x). exact Hlc.
  - apply IHt with (x := x). exact Hlc.
  - apply IHt with (x := x). exact Hlc.
  - apply IHt with (x := x). exact Hlc.
  - destruct Hlc as [H1 [H2 H3]]. repeat split;
      [apply (IHt1 k x) | apply (IHt2 (S k) x) |
       apply (IHt3 (S k) x)]; assumption.
  - apply IHt with (x := x). exact Hlc.
Qed.

Lemma list_bounded : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + lia.
    + specialize (IH x Hin). lia.
Qed.

Lemma fresh_atom : forall (L : list atom), exists x, ~ In x L.
Proof.
  intros L. exists (S (fold_right Nat.max 0 L)).
  intro Hin. pose proof (list_bounded L _ Hin). lia.
Qed.

Lemma has_type_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty; unfold locally_closed in *;
    simpl in *; auto.
  - destruct (fresh_atom L) as [x Hfresh].
    apply (opened_lc_body body 0 x). exact (H2 x Hfresh).
  - destruct (fresh_atom L) as [x Hfresh].
    repeat split.
    + exact IHHty.
    + apply (opened_lc_body body1 0 x).
      exact (H1 x Hfresh).
    + apply (opened_lc_body body2 0 x).
      exact (H3 x Hfresh).
Qed.

Lemma not_in_app_parts : forall (x : atom) A B,
  ~ In x (A ++ B) -> ~ In x A /\ ~ In x B.
Proof.
  intros x A B H. split; intro Hin; apply H; apply in_or_app; auto.
Qed.

Lemma instantiate_open : forall t rho x u k,
  replacement_closed rho -> ~ In x (fv t) ->
  instantiate ((x, u) :: rho) (open_rec k (tm_fvar x) t) =
  open_rec k u (instantiate rho t).
Proof.
  induction t; intros rho x u k Hrho Hfresh; simpl in *;
    try reflexivity.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (a <> x) as Hneq.
    { intro Heq. subst a. apply Hfresh. simpl. auto. }
    assert (E : Nat.eqb a x = false) by (apply Nat.eqb_neq; exact Hneq).
    rewrite E.
    symmetry. apply open_rec_on_lc.
    apply (lc_at_weaken (lookup_replacement rho a) 0 k).
    + lia.
    + exact (proj1 (Hrho a)).
  - f_equal. apply IHt; assumption.
  - apply not_in_app_parts in Hfresh as [Hfresh1 Hfresh2].
    rewrite (IHt1 rho x u k Hrho Hfresh1),
      (IHt2 rho x u k Hrho Hfresh2). reflexivity.
  - apply not_in_app_parts in Hfresh as [Hfresh1 Hfresh2].
    rewrite (IHt1 rho x u k Hrho Hfresh1),
      (IHt2 rho x u k Hrho Hfresh2). reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - apply not_in_app_parts in Hfresh as [Hfresh0 Hfresh12].
    apply not_in_app_parts in Hfresh12 as [Hfresh1 Hfresh2].
    rewrite (IHt1 rho x u k Hrho Hfresh0),
      (IHt2 rho x u (S k) Hrho Hfresh1),
      (IHt3 rho x u (S k) Hrho Hfresh2). reflexivity.
  - f_equal. apply IHt; assumption.
Qed.

Lemma unary_value_closed : forall T v,
  unary_value T v -> closed v.
Proof. intros T v H; destruct T; simpl in H; tauto. Qed.

Lemma unary_is_value : forall T v,
  unary_value T v -> value v.
Proof.
  induction T; intros v H; simpl in H.
  - destruct H as [_ [k ->]]. constructor.
  - destruct H as [_ [[u [k [-> Hu]]] | [u [k [-> Hu]]]]].
    + constructor. eauto.
    + constructor. eauto.
  - destruct H as [_ [u [w [k [-> [Hu Hw]]]]]].
    constructor; eauto.
  - destruct H as [Hc [A [body [k [-> _]]]]].
    constructor. exact (proj1 Hc).
Qed.

Lemma related_value_closed_left : forall T v1 v2,
  related_value T v1 v2 -> closed v1.
Proof.
  intros T v1 v2 H. apply unary_value_closed with (T := T).
  eapply related_unary_left; eauto.
Qed.

Lemma related_value_closed_right : forall T v1 v2,
  related_value T v1 v2 -> closed v2.
Proof.
  intros T v1 v2 H. apply unary_value_closed with (T := T).
  eapply related_unary_right; eauto.
Qed.

Lemma unary_value_term : forall T v,
  unary_value T v -> unary_term T v.
Proof.
  intros T v Hu w He.
  pose proof (eval_value_inv _ _ (unary_is_value T v Hu) He) as E.
  subst w. exact Hu.
Qed.

Lemma related_value_term : forall T v1 v2,
  related_value T v1 v2 -> related_term T v1 v2.
Proof.
  intros T v1 v2 Hr w1 w2 He1 He2.
  pose proof (eval_value_inv _ _
    (unary_is_value _ _ (related_unary_left _ _ _ Hr)) He1) as E1.
  pose proof (eval_value_inv _ _
    (unary_is_value _ _ (related_unary_right _ _ _ Hr)) He2) as E2.
  subst. exact Hr.
Qed.

Lemma unary_environment_extend : forall Gamma rho x T u,
  unary_environment Gamma rho -> unary_value T u ->
  unary_environment (update Gamma x T) ((x,u)::rho).
Proof.
  intros Gamma rho x T u [Hc Hr] Hu.
  split.
  - intro y. simpl. destruct (Nat.eqb y x); auto.
    apply unary_value_closed with (T := T). exact Hu.
  - intros y U Hlook. simpl in *.
    destruct (Nat.eqb y x) eqn:E.
    + inversion Hlook; subst. apply unary_value_term. exact Hu.
    + eapply Hr. exact Hlook.
Qed.

Lemma related_environment_extend : forall Gamma rho1 rho2 x T u1 u2,
  related_environment Gamma rho1 rho2 -> related_value T u1 u2 ->
  related_environment (update Gamma x T)
    ((x,u1)::rho1) ((x,u2)::rho2).
Proof.
  intros Gamma rho1 rho2 x T u1 u2 [Hun1 [Hun2 Hr]] Huv.
  split.
  - apply unary_environment_extend; [exact Hun1 |].
    eapply related_unary_left; eauto.
  - split.
    + apply unary_environment_extend; [exact Hun2 |].
      eapply related_unary_right; eauto.
    + intros y U Hlook. simpl in *.
      destruct (Nat.eqb y x) eqn:E.
      * inversion Hlook; subst. apply related_value_term. exact Huv.
      * eapply Hr. exact Hlook.
Qed.

Lemma unary_protect_type_irrel : forall T l1 l2 v,
  unary_value (ty_protect l1 T) v -> unary_value (ty_protect l2 T) v.
Proof.
  intros T l1 l2 v H. destruct T; simpl in *; exact H.
Qed.

Lemma unary_protect_any : forall T v l_value l_type,
  unary_value T v ->
  unary_value (ty_protect l_type T) (protect_value v l_value).
Proof.
  intros T v lv lt H.
  apply (unary_protect_type_irrel T lv lt).
  apply unary_protect. exact H.
Qed.

Lemma closed_pair : forall u w k,
  closed u -> closed w -> closed (tm_pair u w k).
Proof.
  intros u w k [Hlu Hfu] [Hlw Hfw].
  split; unfold locally_closed in *; simpl; auto.
  rewrite Hfu, Hfw. reflexivity.
Qed.

Lemma closed_inl : forall u k,
  closed u -> closed (tm_inl u k).
Proof. intros u k H; exact H. Qed.

Lemma closed_inr : forall u k,
  closed u -> closed (tm_inr u k).
Proof. intros u k H; exact H. Qed.

Theorem unary_fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho, unary_environment Gamma rho ->
    unary_term T (instantiate rho t).
Proof.
  intros Gamma t T Hty.
  induction Hty; intros rho Henv v He; simpl in He.
  - destruct Henv as [_ Hr].
    exact (Hr x T H v He).
  - inversion He; subst. simpl. split.
    + split; [unfold locally_closed; simpl; trivial | reflexivity].
    + exists kappa. reflexivity.
  - inversion He; subst. simpl. split.
    + eapply (instantiate_closed (tm_abs T1 body kappa) rho).
      * eapply has_type_lc. eapply T_Abs with (L := L); eauto.
      * exact (proj1 Henv).
    + exists T1, (instantiate rho body), kappa. split; [reflexivity |].
      intros u w Hu Hew.
      destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
      apply not_in_app_parts in Hfresh as [HfreshL HfreshBody].
      unfold open in Hew.
      rewrite <- (instantiate_open body rho x u 0 (proj1 Henv) HfreshBody)
        in Hew.
      eapply (H2 x HfreshL ((x,u)::rho)).
      * apply unary_environment_extend; assumption.
      * exact Hew.
  - inversion He; subst.
    pose proof (IHHty1 rho Henv _ H3) as Hfun.
    pose proof (IHHty2 rho Henv _ H4) as Harg.
    simpl in Hfun.
    destruct Hfun as [_ [A' [b' [k' [Heq Hbody]]]]].
    inversion Heq; subst.
    apply unary_protect_any.
    eapply Hbody; eauto.
  - inversion He; subst.
    pose proof (IHHty1 rho Henv _ H4) as Hu.
    pose proof (IHHty2 rho Henv _ H5) as Hw.
    simpl. split.
    + apply closed_pair; eapply unary_value_closed; eauto.
    + exists v0, w, kappa. repeat split; auto.
  - inversion He; subst.
    pose proof (IHHty rho Henv _ H2) as Hp.
    simpl in Hp.
    destruct Hp as [_ [u [w' [k' [Heq [Hu Hw]]]]]].
    inversion Heq; subst. apply unary_protect_any. exact Hu.
  - inversion He; subst.
    pose proof (IHHty rho Henv _ H2) as Hp.
    simpl in Hp.
    destruct Hp as [_ [u [w' [k' [Heq [Hu Hw]]]]]].
    inversion Heq; subst. apply unary_protect_any. exact Hw.
  - inversion He; subst.
    pose proof (IHHty rho Henv _ H4) as Hu.
    simpl. split.
    + apply closed_inl. eapply unary_value_closed; eauto.
    + left. exists v0, kappa. auto.
  - inversion He; subst.
    pose proof (IHHty rho Henv _ H4) as Hu.
    simpl. split.
    + apply closed_inr. eapply unary_value_closed; eauto.
    + right. exists v0, kappa. auto.
  - inversion He; subst.
    + pose proof (IHHty rho Henv _ H9) as Hsum.
      simpl in Hsum.
      destruct Hsum as [_ [[u [k' [Heq Hu]]] |
                           [u [k' [Heq Hu]]]]].
      * inversion Heq; subst.
        destruct (fresh_atom (L ++ fv body1)) as [x Hfresh].
        apply not_in_app_parts in Hfresh as [HfreshL HfreshBody].
        unfold open in H10.
        rewrite <- (instantiate_open body1 rho x u 0
          (proj1 Henv) HfreshBody) in H10.
        apply unary_protect_any.
        eapply (H1 x HfreshL ((x,u)::rho)).
        -- apply unary_environment_extend; assumption.
        -- exact H10.
      * discriminate.
    + pose proof (IHHty rho Henv _ H9) as Hsum.
      simpl in Hsum.
      destruct Hsum as [_ [[u [k' [Heq Hu]]] |
                           [u [k' [Heq Hu]]]]].
      * discriminate.
      * inversion Heq; subst.
        destruct (fresh_atom (L ++ fv body2)) as [x Hfresh].
        apply not_in_app_parts in Hfresh as [HfreshL HfreshBody].
        unfold open in H10.
        rewrite <- (instantiate_open body2 rho x u 0
          (proj1 Henv) HfreshBody) in H10.
        apply unary_protect_any.
        eapply (H3 x HfreshL ((x,u)::rho)).
        -- apply unary_environment_extend; assumption.
        -- exact H10.
  - inversion He; subst.
    apply unary_protect. eapply IHHty; eauto.
  - eapply unary_subtype; eauto.
    eapply IHHty; eauto.
Qed.

Lemma unary_annotation_irrel : forall T v l,
  unary_value T v -> unary_value T (protect_value v l).
Proof.
  intros T v l H.
  rewrite <- (ty_protect_low T).
  apply unary_protect_any. exact H.
Qed.

Lemma related_annotation_irrel : forall T v1 v2 l1 l2,
  related_value T v1 v2 ->
  related_value T (protect_value v1 l1) (protect_value v2 l2).
Proof.
  intros T v1 v2 l1 l2 H.
  pose proof (related_unary_left T v1 v2 H) as Hu1.
  pose proof (related_unary_right T v1 v2 H) as Hu2.
  pose proof (unary_annotation_irrel T v1 l1 Hu1) as Hv1.
  pose proof (unary_annotation_irrel T v2 l2 Hu2) as Hv2.
  destruct T; destruct s as [r i]; destruct i; simpl in *;
    refine (conj Hv1 (conj Hv2 _)); try exact I.
  - destruct H as [_ [_ Hr]].
    destruct Hr as [[u1 [u2 [k1 [k2 [-> [-> Huv]]]]]] |
                    [u1 [u2 [k1 [k2 [-> [-> Huv]]]]]]].
    + left. exists u1, u2, (protect_security k1 l1),
        (protect_security k2 l2). auto.
    + right. exists u1, u2, (protect_security k1 l1),
        (protect_security k2 l2). auto.
  - destruct H as [_ [_ Hr]].
    destruct Hr as [u1 [u2 [w1 [w2 [k1 [k2
      [-> [-> [Huv Hwv]]]]]]]]].
    exists u1, u2, w1, w2, (protect_security k1 l1),
      (protect_security k2 l2). auto.
  - destruct H as [_ [_ Hr]].
    destruct Hr as [A1 [b1 [k1 [A2 [b2 [k2 [-> [-> Hbody]]]]]]]].
    exists A1, b1, (protect_security k1 l1), A2, b2,
      (protect_security k2 l2). auto.
Qed.

Lemma related_sum_low_inl : forall A B k u1 u2 k1 k2,
  k.(indirect_reader) = Low ->
  related_value (Ty_Sum A B k) (tm_inl u1 k1) (tm_inl u2 k2) ->
  related_value A u1 u2.
Proof.
  intros A B k u1 u2 k1 k2 Hi H.
  simpl in H. rewrite Hi in H.
  destruct H as [_ [_ [
    [v1 [v2 [j1 [j2 [E1 [E2 Hr]]]]]] |
    [v1 [v2 [j1 [j2 [E1 [E2 Hr]]]]]]]]].
  - inversion E1; inversion E2; subst. exact Hr.
  - discriminate.
Qed.

Lemma related_sum_low_inr : forall A B k u1 u2 k1 k2,
  k.(indirect_reader) = Low ->
  related_value (Ty_Sum A B k) (tm_inr u1 k1) (tm_inr u2 k2) ->
  related_value B u1 u2.
Proof.
  intros A B k u1 u2 k1 k2 Hi H.
  simpl in H. rewrite Hi in H.
  destruct H as [_ [_ [
    [v1 [v2 [j1 [j2 [E1 [E2 Hr]]]]]] |
    [v1 [v2 [j1 [j2 [E1 [E2 Hr]]]]]]]]].
  - discriminate.
  - inversion E1; inversion E2; subst. exact Hr.
Qed.

Lemma related_sum_low_mismatch_l : forall A B k u1 u2 k1 k2,
  k.(indirect_reader) = Low ->
  related_value (Ty_Sum A B k) (tm_inl u1 k1) (tm_inr u2 k2) -> False.
Proof.
  intros A B k u1 u2 k1 k2 Hi H.
  simpl in H. rewrite Hi in H.
  destruct H as [_ [_ [
    [v1 [v2 [j1 [j2 [E1 [E2 _]]]]]] |
    [v1 [v2 [j1 [j2 [E1 [E2 _]]]]]]]]]; discriminate.
Qed.

Lemma related_sum_low_mismatch_r : forall A B k u1 u2 k1 k2,
  k.(indirect_reader) = Low ->
  related_value (Ty_Sum A B k) (tm_inr u1 k1) (tm_inl u2 k2) -> False.
Proof.
  intros A B k u1 u2 k1 k2 Hi H.
  simpl in H. rewrite Hi in H.
  destruct H as [_ [_ [
    [v1 [v2 [j1 [j2 [E1 [E2 _]]]]]] |
    [v1 [v2 [j1 [j2 [E1 [E2 _]]]]]]]]]; discriminate.
Qed.

Theorem related_fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho1 rho2, related_environment Gamma rho1 rho2 ->
    related_term T (instantiate rho1 t) (instantiate rho2 t).
Proof.
  intros Gamma t T Hty.
  pose proof Hty as Horig.
  induction Hty; intros rho1 rho2 Henv v1 v2 He1 He2; simpl in *.
  all: pose proof (unary_fundamental _ _ _ Horig rho1
    (related_environment_unary_left _ _ _ Henv) v1 He1) as Hu1.
  all: pose proof (unary_fundamental _ _ _ Horig rho2
    (related_environment_unary_right _ _ _ Henv) v2 He2) as Hu2.
  - destruct Henv as [_ [_ Hr]].
    exact (Hr x T H v1 v2 He1 He2).
  - destruct kappa as [r i]; destruct i; simpl in *;
      exact (conj Hu1 (conj Hu2 I)).
  - inversion He1; subst. inversion He2; subst.
    refine (conj Hu1 (conj Hu2 _)).
    destruct (indirect_reader kappa) eqn:Hi; [| exact I].
    exists T1, (instantiate rho1 body), kappa,
      T1, (instantiate rho2 body), kappa.
    repeat split; try reflexivity.
    intros u1 u2 w1 w2 Hargs Hew1 Hew2.
    destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
    apply not_in_app_parts in Hfresh as [HfreshL HfreshBody].
    unfold open in Hew1, Hew2.
    rewrite <- (instantiate_open body rho1 x u1 0
      (proj1 (proj1 Henv)) HfreshBody) in Hew1.
    rewrite <- (instantiate_open body rho2 x u2 0
      (proj1 (proj1 (proj2 Henv))) HfreshBody) in Hew2.
    eapply (H2 x HfreshL (H1 x HfreshL)
      ((x,u1)::rho1) ((x,u2)::rho2)).
    + apply related_environment_extend; assumption.
    + exact Hew1.
    + exact Hew2.
  - destruct (indirect_reader kappa) eqn:Hi.
    + rewrite ty_protect_low.
      inversion He1; subst. inversion He2; subst.
      pose proof (IHHty1 Hty1 rho1 rho2 Henv _ _ H3 H5) as Hfun.
      pose proof (IHHty2 Hty2 rho1 rho2 Henv _ _ H4 H8) as Harg.
      simpl in Hfun. destruct Hfun as [_ [_ Hfstruct]].
      rewrite Hi in Hfstruct.
      destruct Hfstruct as [A1 [b1 [k1 [A2 [b2 [k2
        [E1 [E2 Hbody]]]]]]]].
      inversion E1; subst. inversion E2; subst.
      apply related_annotation_irrel.
      eapply Hbody; eauto.
    + apply related_high_of_unary.
      * apply indirect_protect_high.
      * exact Hu1.
      * exact Hu2.
  - inversion He1; subst. inversion He2; subst.
    refine (conj Hu1 (conj Hu2 _)).
    destruct (indirect_reader kappa).
    + exists v, v0, w, w0, kappa, kappa.
      split; [reflexivity |]. split; [reflexivity |]. split.
      * eapply IHHty1; eauto.
      * eapply IHHty2; eauto.
    + exact I.
  - destruct (indirect_reader kappa) eqn:Hi.
    + rewrite ty_protect_low.
      inversion He1; subst. inversion He2; subst.
      pose proof (IHHty Hty rho1 rho2 Henv _ _ H2 H3) as Hp.
      simpl in Hp. destruct Hp as [_ [_ Hstruct]]. rewrite Hi in Hstruct.
      destruct Hstruct as [u1 [u2 [w1 [w2 [k1 [k2
        [E1 [E2 [Huv Hwv]]]]]]]]].
      inversion E1; subst. inversion E2; subst.
      apply related_annotation_irrel. exact Huv.
    + apply related_high_of_unary; [apply indirect_protect_high | exact Hu1 | exact Hu2].
  - destruct (indirect_reader kappa) eqn:Hi.
    + rewrite ty_protect_low.
      inversion He1; subst. inversion He2; subst.
      pose proof (IHHty Hty rho1 rho2 Henv _ _ H2 H3) as Hp.
      simpl in Hp. destruct Hp as [_ [_ Hstruct]]. rewrite Hi in Hstruct.
      destruct Hstruct as [u1 [u2 [w1 [w2 [k1 [k2
        [E1 [E2 [Huv Hwv]]]]]]]]].
      inversion E1; subst. inversion E2; subst.
      apply related_annotation_irrel. exact Hwv.
    + apply related_high_of_unary; [apply indirect_protect_high | exact Hu1 | exact Hu2].
  - inversion He1; subst. inversion He2; subst.
    refine (conj Hu1 (conj Hu2 _)).
    destruct (indirect_reader kappa).
    + left. exists v, v0, kappa, kappa.
      repeat split; try reflexivity. eapply IHHty; eauto.
    + exact I.
  - inversion He1; subst. inversion He2; subst.
    refine (conj Hu1 (conj Hu2 _)).
    destruct (indirect_reader kappa).
    + right. exists v, v0, kappa, kappa.
      repeat split; try reflexivity. eapply IHHty; eauto.
    + exact I.
  - destruct (indirect_reader kappa) eqn:Hi.
    + rewrite ty_protect_low.
      inversion He1; subst; inversion He2; subst.
      * pose proof (IHHty Hty rho1 rho2 Henv _ _ H9 H12) as Hsum.
        pose proof (related_sum_low_inl _ _ _ _ _ _ _ Hi Hsum) as Hargs.
        destruct (fresh_atom (L ++ fv body1)) as [x Hfresh].
        apply not_in_app_parts in Hfresh as [HfreshL HfreshBody].
        unfold open in H10, H13.
        rewrite <- (instantiate_open body1 rho1 x v 0
          (proj1 (proj1 Henv)) HfreshBody) in H10.
        rewrite <- (instantiate_open body1 rho2 x v0 0
          (proj1 (proj1 (proj2 Henv))) HfreshBody) in H13.
        apply related_annotation_irrel.
        eapply (H1 x HfreshL (H0 x HfreshL)
          ((x,v)::rho1) ((x,v0)::rho2)).
        -- apply related_environment_extend; assumption.
        -- exact H10.
        -- exact H13.
      * exfalso. eapply related_sum_low_mismatch_l; [exact Hi |].
        eapply IHHty; eauto.
      * exfalso. eapply related_sum_low_mismatch_r; [exact Hi |].
        eapply IHHty; eauto.
      * pose proof (IHHty Hty rho1 rho2 Henv _ _ H9 H12) as Hsum.
        pose proof (related_sum_low_inr _ _ _ _ _ _ _ Hi Hsum) as Hargs.
        destruct (fresh_atom (L ++ fv body2)) as [x Hfresh].
        apply not_in_app_parts in Hfresh as [HfreshL HfreshBody].
        unfold open in H10, H13.
        rewrite <- (instantiate_open body2 rho1 x v 0
          (proj1 (proj1 Henv)) HfreshBody) in H10.
        rewrite <- (instantiate_open body2 rho2 x v0 0
          (proj1 (proj1 (proj2 Henv))) HfreshBody) in H13.
        apply related_annotation_irrel.
        eapply (H3 x HfreshL (H2 x HfreshL)
          ((x,v)::rho1) ((x,v0)::rho2)).
        -- apply related_environment_extend; assumption.
        -- exact H10.
        -- exact H13.
    + apply related_high_of_unary; [apply indirect_protect_high | exact Hu1 | exact Hu2].
  - inversion He1; subst. inversion He2; subst.
    apply related_protect. eapply IHHty; eauto.
  - eapply related_subtype; eauto.
    eapply IHHty; eauto.
Qed.

Lemma fv_open_contains : forall t k x y,
  In y (fv t) -> In y (fv (open_rec k (tm_fvar x) t)).
Proof.
  induction t; intros k x y Hin; simpl in *; try contradiction;
    try exact Hin;
    try (apply IHt; exact Hin).
  - apply in_app_iff in Hin. apply in_app_iff.
    destruct Hin as [Hin | Hin].
    + left. eapply IHt1; eauto.
    + right. eapply IHt2; eauto.
  - apply in_app_iff in Hin. apply in_app_iff.
    destruct Hin as [Hin | Hin].
    + left. eapply IHt1; eauto.
    + right. eapply IHt2; eauto.
  - repeat rewrite in_app_iff in *.
    destruct Hin as [Hin | [Hin | Hin]].
    + left. eapply IHt1; eauto.
    + right. left. eapply IHt2; eauto.
    + right. right. eapply IHt3; eauto.
Qed.

Lemma typing_fv_lookup : forall Gamma t T,
  has_type Gamma t T ->
  forall y, In y (fv t) -> exists U, lookup_context y Gamma = Some U.
Proof.
  intros Gamma t T Hty.
  induction Hty; intros y Hin; simpl in Hin.
  - destruct Hin as [Heq | []]. subst y. eauto.
  - contradiction.
  - destruct (fresh_atom (L ++ [y])) as [x Hfresh].
    apply not_in_app_parts in Hfresh as [HL Hy].
    assert (E : Nat.eqb y x = false).
    { apply Nat.eqb_neq. intro Heq. subst y. apply Hy. simpl; auto. }
    pose proof (H2 x HL y (fv_open_contains body 0 x y Hin)) as [U Hlook].
    simpl in Hlook. rewrite E in Hlook. exists U. exact Hlook.
  - apply in_app_iff in Hin as [Hin | Hin]; eauto.
  - apply in_app_iff in Hin as [Hin | Hin]; eauto.
  - eapply IHHty; eauto.
  - eapply IHHty; eauto.
  - eapply IHHty; eauto.
  - eapply IHHty; eauto.
  - apply in_app_iff in Hin as [Ht | Hbs].
    + eapply IHHty; eauto.
    + apply in_app_iff in Hbs as [Hb1 | Hb2].
      * destruct (fresh_atom (L ++ [y])) as [x Hfresh].
        apply not_in_app_parts in Hfresh as [HL Hy].
        assert (E : Nat.eqb y x = false).
        { apply Nat.eqb_neq. intro Heq. subst y. apply Hy. simpl; auto. }
        pose proof (H1 x HL y (fv_open_contains body1 0 x y Hb1))
          as [U Hlook].
        simpl in Hlook. rewrite E in Hlook. exists U. exact Hlook.
      * destruct (fresh_atom (L ++ [y])) as [x Hfresh].
        apply not_in_app_parts in Hfresh as [HL Hy].
        assert (E : Nat.eqb y x = false).
        { apply Nat.eqb_neq. intro Heq. subst y. apply Hy. simpl; auto. }
        pose proof (H3 x HL y (fv_open_contains body2 0 x y Hb2))
          as [U Hlook].
        simpl in Hlook. rewrite E in Hlook. exists U. exact Hlook.
  - eapply IHHty; eauto.
  - eapply IHHty; eauto.
Qed.

Definition context_fv (C : program_context) : list atom :=
  fv (plug C (tm_unit public)).

Lemma fv_plug_split : forall C t y,
  In y (fv (plug C t)) <->
  In y (fv t) \/ In y (context_fv C).
Proof.
  intros C; induction C; intros arg y; unfold context_fv in *; simpl;
    repeat rewrite in_app_iff;
    try rewrite (IHC arg y);
    repeat rewrite in_app_iff; tauto.
Qed.

Lemma app_nil_parts : forall (A B : list atom),
  A ++ B = [] -> A = [] /\ B = [].
Proof.
  intros A B H. destruct A as [|a A]; simpl in H;
    [split; auto | discriminate].
Qed.

Lemma instantiate_fv_empty : forall t rho,
  fv t = [] -> instantiate rho t = t.
Proof.
  induction t; intros rho Hfv; simpl in *; try reflexivity;
    try (f_equal; apply IHt; exact Hfv).
  - discriminate.
  - apply app_nil_parts in Hfv as [H1 H2].
    rewrite (IHt1 _ H1), (IHt2 _ H2). reflexivity.
  - apply app_nil_parts in Hfv as [H1 H2].
    rewrite (IHt1 _ H1), (IHt2 _ H2). reflexivity.
  - apply app_nil_parts in Hfv as [H0 H12].
    apply app_nil_parts in H12 as [H1 H2].
    rewrite (IHt1 _ H0), (IHt2 _ H1), (IHt3 _ H2).
    reflexivity.
Qed.

Lemma context_fv_empty_from_type : forall C x T U,
  has_type (update empty x T) (plug C (tm_fvar x)) U ->
  ~ In x (context_fv C) -> context_fv C = [].
Proof.
  intros C x T U Hty Hfresh.
  destruct (context_fv C) as [|y ys] eqn:E; [reflexivity |].
  exfalso.
  assert (Hin : In y (context_fv C)).
  { rewrite E. simpl. auto. }
  assert (Hplug : In y (fv (plug C (tm_fvar x)))).
  { apply fv_plug_split. right. exact Hin. }
  destruct (typing_fv_lookup _ _ _ Hty y Hplug) as [V Hlook].
  simpl in Hlook.
  destruct (Nat.eqb y x) eqn:Ey.
  - apply Nat.eqb_eq in Ey. subst y. apply Hfresh. rewrite <- E. exact Hin.
  - discriminate.
Qed.

Lemma instantiate_plug : forall C rho t,
  context_fv C = [] ->
  instantiate rho (plug C t) = plug C (instantiate rho t).
Proof.
  induction C; intros rho arg Hcf; unfold context_fv in Hcf;
    simpl in *.
  - reflexivity.
  - f_equal. apply IHC. exact Hcf.
  - apply app_nil_parts in Hcf as [Hc Ht].
    rewrite (IHC rho arg Hc), (instantiate_fv_empty t rho Ht).
    reflexivity.
  - apply app_nil_parts in Hcf as [Ht Hc].
    rewrite (IHC rho arg Hc), (instantiate_fv_empty t rho Ht).
    reflexivity.
  - apply app_nil_parts in Hcf as [Hc Ht].
    rewrite (IHC rho arg Hc), (instantiate_fv_empty t rho Ht).
    reflexivity.
  - apply app_nil_parts in Hcf as [Ht Hc].
    rewrite (IHC rho arg Hc), (instantiate_fv_empty t rho Ht).
    reflexivity.
  - f_equal. apply IHC. exact Hcf.
  - f_equal. apply IHC. exact Hcf.
  - f_equal. apply IHC. exact Hcf.
  - f_equal. apply IHC. exact Hcf.
  - apply app_nil_parts in Hcf as [Hc Hts].
    apply app_nil_parts in Hts as [Ht1 Ht2].
    rewrite (IHC rho arg Hc), (instantiate_fv_empty t rho Ht1),
      (instantiate_fv_empty t0 rho Ht2). reflexivity.
  - apply app_nil_parts in Hcf as [Ht1 Hrest].
    apply app_nil_parts in Hrest as [Hc Ht2].
    rewrite (IHC rho arg Hc), (instantiate_fv_empty t rho Ht1),
      (instantiate_fv_empty t0 rho Ht2). reflexivity.
  - apply app_nil_parts in Hcf as [Ht1 Hrest].
    apply app_nil_parts in Hrest as [Ht2 Hc].
    rewrite (IHC rho arg Hc), (instantiate_fv_empty t rho Ht1),
      (instantiate_fv_empty t0 rho Ht2). reflexivity.
  - f_equal. apply IHC. exact Hcf.
Qed.

Lemma typed_empty_closed : forall t T,
  has_type empty t T -> closed t.
Proof.
  intros t T Hty. split.
  - eapply has_type_lc; eauto.
  - destruct (fv t) as [|x xs] eqn:E; [reflexivity |].
    exfalso.
    destruct (typing_fv_lookup _ _ _ Hty x) as [U Hlook].
    + rewrite E. simpl. auto.
    + discriminate.
Qed.

Lemma unary_environment_empty : unary_environment empty [].
Proof.
  split.
  - intro x. split; [unfold locally_closed; simpl; trivial | reflexivity].
  - intros x T Hlook. discriminate.
Qed.

Lemma related_environment_singleton : forall x T t1 t2,
  closed t1 -> closed t2 ->
  unary_term T t1 -> unary_term T t2 -> related_term T t1 t2 ->
  related_environment (update empty x T) [(x,t1)] [(x,t2)].
Proof.
  intros x T t1 t2 Hc1 Hc2 Hu1 Hu2 Hr.
  split.
  - split.
    + intro y. simpl. destruct (Nat.eqb y x); auto.
      split; [unfold locally_closed; simpl; trivial | reflexivity].
    + intros y U Hlook. simpl in *.
      destruct (Nat.eqb y x) eqn:E; [inversion Hlook; subst; exact Hu1 | discriminate].
  - split.
    + split.
      * intro y. simpl. destruct (Nat.eqb y x); auto.
        split; [unfold locally_closed; simpl; trivial | reflexivity].
      * intros y U Hlook. simpl in *.
        destruct (Nat.eqb y x) eqn:E; [inversion Hlook; subst; exact Hu2 | discriminate].
    + intros y U Hlook. simpl in *.
      destruct (Nat.eqb y x) eqn:E; [inversion Hlook; subst; exact Hr | discriminate].
Qed.

Lemma no_flow_high_low : forall a b,
  ~ flows_to a b -> a = High /\ b = Low.
Proof.
  destruct a, b; simpl; intros H; try contradiction; auto.
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
  intros C t1 t2 T_secret T_result Hty1 Hty2 Hctx Hground Htransparent Hnf.
  destruct (no_flow_high_low _ _ Hnf) as [HsecretHigh HresultLow].
  destruct Hctx as [L HL].
  destruct (fresh_atom (L ++ context_fv C)) as [x Hfresh].
  apply not_in_app_parts in Hfresh as [HfreshL HfreshC].
  pose proof (HL x HfreshL) as HctxTy.
  pose proof (context_fv_empty_from_type C x T_secret T_result
    HctxTy HfreshC) as HcontextEmpty.
  pose proof (typed_empty_closed _ _ Hty1) as Hclosed1.
  pose proof (typed_empty_closed _ _ Hty2) as Hclosed2.
  pose proof (unary_fundamental _ _ _ Hty1 [] unary_environment_empty)
    as Hunary1.
  pose proof (unary_fundamental _ _ _ Hty2 [] unary_environment_empty)
    as Hunary2.
  rewrite (instantiate_fv_empty t1 [] (proj2 Hclosed1)) in Hunary1.
  rewrite (instantiate_fv_empty t2 [] (proj2 Hclosed2)) in Hunary2.
  assert (HsecretRelated : related_term T_secret t1 t2).
  { intros u1 u2 He1 He2.
    apply related_high_of_unary.
    - exact HsecretHigh.
    - exact (Hunary1 u1 He1).
    - exact (Hunary2 u2 He2). }
  pose proof (related_environment_singleton x T_secret t1 t2
    Hclosed1 Hclosed2 Hunary1 Hunary2 HsecretRelated) as Henv.
  pose proof (related_fundamental _ _ _ HctxTy
    [(x,t1)] [(x,t2)] Henv) as Hrel.
  assert (E1 : instantiate [(x,t1)] (plug C (tm_fvar x)) = plug C t1).
  { rewrite instantiate_plug by exact HcontextEmpty.
    simpl. rewrite Nat.eqb_refl. reflexivity. }
  assert (E2 : instantiate [(x,t2)] (plug C (tm_fvar x)) = plug C t2).
  { rewrite instantiate_plug by exact HcontextEmpty.
    simpl. rewrite Nat.eqb_refl. reflexivity. }
  rewrite E1, E2 in Hrel.
  intros v1 v2 He1 He2.
  eapply related_ground_erasure.
  - exact Hground.
  - exact Htransparent.
  - exact HresultLow.
  - apply Hrel; apply multi_value_eval; assumption.
Qed.
