(** System F parametricity benchmark, Hard variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNondeterminismHardTask.

Definition atom := nat.

Declare Scope systemf_scope.
Delimit Scope systemf_scope with systemf.
Open Scope systemf_scope.

Declare Custom Entry systemf_ty.
Declare Custom Entry systemf_tm.

Inductive ty : Type :=
  | Ty_BVar : nat -> ty
  | Ty_FVar : atom -> ty

  | Ty_Arrow : ty -> ty -> ty

  | Ty_All : ty -> ty.

Notation "T" := T
  (in custom systemf_ty at level 0, T constr at level 0) : systemf_scope.
Notation "<{{ T }}>" := T
  (T custom systemf_ty at level 200) : systemf_scope.
Notation "( T )" := T
  (in custom systemf_ty at level 0, T custom systemf_ty) : systemf_scope.
Notation "$( T )" := T
  (in custom systemf_ty at level 0, T constr) : systemf_scope.
Notation "'fvar' X" := (Ty_FVar X)
  (in custom systemf_ty at level 0, X constr at level 0) : systemf_scope.
Notation "T1 '->' T2" := (Ty_Arrow T1 T2)
  (in custom systemf_ty at level 99, right associativity) : systemf_scope.
Notation "'forall' ',' T" := (Ty_All T)
  (in custom systemf_ty at level 200,
   T custom systemf_ty at level 200,
   right associativity) : systemf_scope.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_abs : ty -> tm -> tm
  | tm_app : tm -> tm -> tm

  | tm_tabs : tm -> tm

  | tm_tapp : tm -> ty -> tm
  | tm_choice : tm -> tm -> tm.

Notation "t" := t
  (in custom systemf_tm at level 0, t constr at level 0) : systemf_scope.
Notation "<{ t }>" := t
  (t custom systemf_tm at level 200) : systemf_scope.
Notation "( t )" := t
  (in custom systemf_tm at level 0, t custom systemf_tm) : systemf_scope.
Notation "$( t )" := t
  (in custom systemf_tm at level 0, t constr, only parsing) : systemf_scope.
Notation "'bvar' n" := (tm_bvar n)
  (in custom systemf_tm at level 0, n constr at level 0) : systemf_scope.
Notation "'fvar' x" := (tm_fvar x)
  (in custom systemf_tm at level 0, x constr at level 0) : systemf_scope.
Notation "t1 t2" := (tm_app t1 t2)
  (in custom systemf_tm at level 10, left associativity) : systemf_scope.
Notation "'lambda' ':' T ',' t" := (tm_abs T t)
  (in custom systemf_tm at level 200,
   T custom systemf_ty,
   t custom systemf_tm at level 200,
   left associativity) : systemf_scope.
Notation "'Lambda' ',' t" := (tm_tabs t)
  (in custom systemf_tm at level 200,
   t custom systemf_tm at level 200,
   left associativity) : systemf_scope.
Notation "t '[' T ']'" := (tm_tapp t T)
  (in custom systemf_tm at level 10,
   t custom systemf_tm,
   T custom systemf_ty) : systemf_scope.

Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  end.

Definition open_ty (T U : ty) : ty := open_ty_rec 0 U T.

Fixpoint open_tm_rec (k : nat) (u t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs T (open_tm_rec (S k) u t1)
  | tm_app t1 t2 => tm_app (open_tm_rec k u t1) (open_tm_rec k u t2)
  | tm_tabs t1 => tm_tabs (open_tm_rec k u t1)
  | tm_tapp t1 T => tm_tapp (open_tm_rec k u t1) T
  | tm_choice t1 t2 => tm_choice (open_tm_rec k u t1) (open_tm_rec k u t2)
  end.

Definition open_tm (t u : tm) : tm := open_tm_rec 0 u t.

Fixpoint open_tm_ty_rec (k : nat) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 =>
      tm_abs (open_ty_rec k U T) (open_tm_ty_rec k U t1)
  | tm_app t1 t2 =>
      tm_app (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  | tm_tabs t1 => tm_tabs (open_tm_ty_rec (S k) U t1)
  | tm_tapp t1 T =>
      tm_tapp (open_tm_ty_rec k U t1) (open_ty_rec k U T)
  | tm_choice t1 t2 => tm_choice (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  end.

Definition open_tm_ty (t : tm) (U : ty) : tm :=
  open_tm_ty_rec 0 U t.

Fixpoint ty_subst (X : atom) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then U else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst X U T1) (ty_subst X U T2)
  | Ty_All T1 => Ty_All (ty_subst X U T1)
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_choice t1 t2 => tm_choice (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
  | tm_choice t1 t2 => tm_choice (tm_subst x s t1) (tm_subst x s t2)
  end.

Inductive lc_ty_at : nat -> ty -> Prop :=
  | lc_ty_bvar : forall k i,
      i < k ->
      lc_ty_at k (Ty_BVar i)
  | lc_ty_fvar : forall k X,
      lc_ty_at k (Ty_FVar X)
  | lc_ty_arrow : forall k T1 T2,
      lc_ty_at k T1 ->
      lc_ty_at k T2 ->
      lc_ty_at k (Ty_Arrow T1 T2)
  | lc_ty_all : forall k T,
      lc_ty_at (S k) T ->
      lc_ty_at k (Ty_All T).

Definition locally_closed_ty (T : ty) : Prop := lc_ty_at 0 T.

Inductive lc_tm_at : nat -> nat -> tm -> Prop :=
  | lc_tm_bvar : forall K k i,
      i < k ->
      lc_tm_at K k (tm_bvar i)
  | lc_tm_fvar : forall K k x,
      lc_tm_at K k (tm_fvar x)
  | lc_tm_abs : forall K k T t,
      lc_ty_at K T ->
      lc_tm_at K (S k) t ->
      lc_tm_at K k (tm_abs T t)
  | lc_tm_app : forall K k t1 t2,
      lc_tm_at K k t1 ->
      lc_tm_at K k t2 ->
      lc_tm_at K k (tm_app t1 t2)
  | lc_tm_tabs : forall K k t,
      lc_tm_at (S K) k t ->
      lc_tm_at K k (tm_tabs t)
  | lc_tm_tapp : forall K k t T,
      lc_tm_at K k t ->
      lc_ty_at K T ->
      lc_tm_at K k (tm_tapp t T)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t).

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t v,
      locally_closed_tm (tm_abs T t) ->
      value v ->

      tm_app (tm_abs T t) v --> open_tm t v
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      locally_closed_tm t2 ->
      tm_app t1 t2 --> tm_app t1' t2

  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_app v1 t2 --> tm_app v1 t2'
  | ST_TAppTabs :

      forall t T,
      locally_closed_tm (tm_tabs t) ->
      locally_closed_ty T ->
      tm_tapp (tm_tabs t) T --> open_tm_ty t T
  | ST_TApp : forall t t' T,
      t --> t' ->
      locally_closed_ty T ->
      tm_tapp t T --> tm_tapp t' T
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_choice t1 t2 --> t2
where "t1 '-->' t2" := (step t1 t2).

Definition ty_context := list atom.

Definition context := list (atom * ty).

Fixpoint lookup_context (x : atom) (Gamma : context) : option ty :=
  match Gamma with
  | [] => None
  | (y, T) :: Gamma' =>
      if Nat.eqb x y then Some T else lookup_context x Gamma'
  end.

Definition empty : context := [].

Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  (x, T) :: Gamma.

Notation "x '|->' v ';' m" := (update m x v)
  (in custom systemf_tm at level 0,
   x constr at level 0,
   v custom systemf_ty,
   right associativity) : systemf_scope.
Notation "x '|->' v" := (update empty x v)
  (in custom systemf_tm at level 0,
   x constr at level 0,
   v custom systemf_ty) : systemf_scope.
Notation "'empty'" := empty
  (in custom systemf_tm) : systemf_scope.

Inductive wf_ty : ty_context -> ty -> Prop :=
  | WF_Var : forall Delta X,
      In X Delta ->
      wf_ty Delta (Ty_FVar X)
  | WF_Arrow : forall Delta T1 T2,
      wf_ty Delta T1 ->
      wf_ty Delta T2 ->
      wf_ty Delta (Ty_Arrow T1 T2)
  | WF_All :

      forall (L : list atom) Delta T,
      (forall X, ~ In X L ->
        wf_ty (X :: Delta) (open_ty T (Ty_FVar X))) ->
      wf_ty Delta (Ty_All T).

Inductive has_type : ty_context -> context -> tm -> ty -> Prop :=
  | T_Var : forall Delta Gamma x T,
      lookup_context x Gamma = Some T ->
      wf_ty Delta T ->
      has_type Delta Gamma (tm_fvar x) T
  | T_Abs : forall (L : list atom) Delta Gamma T1 t2 T2,
      wf_ty Delta T1 ->

      (forall x, ~ In x L ->
        has_type Delta <{ x |-> $(T1); Gamma }>
          (open_tm t2 (tm_fvar x)) T2) ->
      has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)
  | T_App : forall Delta Gamma t1 t2 T1 T2,
      has_type Delta Gamma t1 (Ty_Arrow T1 T2) ->
      has_type Delta Gamma t2 T1 ->
      has_type Delta Gamma (tm_app t1 t2) T2
  | T_TAbs : forall (L : list atom) Delta Gamma t T,
      (forall X, ~ In X L ->
        has_type (X :: Delta) Gamma
          (open_tm_ty t (Ty_FVar X))
          (open_ty T (Ty_FVar X))) ->
      has_type Delta Gamma (tm_tabs t) (Ty_All T)
  | T_TApp : forall Delta Gamma t T U,
      has_type Delta Gamma t (Ty_All T) ->
      wf_ty Delta U ->
      has_type Delta Gamma (tm_tapp t U) (open_ty T U)
  | T_Choice : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma (tm_choice t1 t2) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).


(* ============================================================ *)
(* Free variables and freshness                                 *)
(* ============================================================ *)

Fixpoint ty_fv (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_fv T1 ++ ty_fv T2
  | Ty_All T1 => ty_fv T1
  end.

Fixpoint tm_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => tm_fv t1
  | tm_app t1 t2 => tm_fv t1 ++ tm_fv t2
  | tm_tabs t1 => tm_fv t1
  | tm_tapp t1 _ => tm_fv t1
  | tm_choice t1 t2 => tm_fv t1 ++ tm_fv t2
  end.

Fixpoint tm_ty_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T t1 => ty_fv T ++ tm_ty_fv t1
  | tm_app t1 t2 => tm_ty_fv t1 ++ tm_ty_fv t2
  | tm_tabs t1 => tm_ty_fv t1
  | tm_tapp t1 T => tm_ty_fv t1 ++ ty_fv T
  | tm_choice t1 t2 => tm_ty_fv t1 ++ tm_ty_fv t2
  end.

Fixpoint ctx_ty_fv (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => ty_fv T ++ ctx_ty_fv Gamma'
  end.

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (max_list l')
  end.

Lemma max_list_ub : forall l x, In x l -> x <= max_list l.
Proof.
  induction l as [| y l IH]; simpl; intros x Hin.
  - contradiction.
  - destruct Hin as [<- | Hin].
    + apply Nat.le_max_l.
    + transitivity (max_list l); [apply IH; assumption | apply Nat.le_max_r].
Qed.

Definition fresh_atom (l : list atom) : atom := S (max_list l).

Lemma fresh_atom_notin : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l Hin. unfold fresh_atom in Hin.
  apply max_list_ub in Hin. lia.
Qed.

(* ============================================================ *)
(* Function-style type and term substitutions                   *)
(* ============================================================ *)

Fixpoint subst_ty_env (sub : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sub X
  | Ty_Arrow T1 T2 => Ty_Arrow (subst_ty_env sub T1) (subst_ty_env sub T2)
  | Ty_All T1 => Ty_All (subst_ty_env sub T1)
  end.

Fixpoint subst_tm_ty_env (sub : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (subst_ty_env sub T) (subst_tm_ty_env sub t1)
  | tm_app t1 t2 => tm_app (subst_tm_ty_env sub t1) (subst_tm_ty_env sub t2)
  | tm_tabs t1 => tm_tabs (subst_tm_ty_env sub t1)
  | tm_tapp t1 T => tm_tapp (subst_tm_ty_env sub t1) (subst_ty_env sub T)
  | tm_choice t1 t2 => tm_choice (subst_tm_ty_env sub t1) (subst_tm_ty_env sub t2)
  end.

Fixpoint subst_tm_env (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs T (subst_tm_env sigma t1)
  | tm_app t1 t2 => tm_app (subst_tm_env sigma t1) (subst_tm_env sigma t2)
  | tm_tabs t1 => tm_tabs (subst_tm_env sigma t1)
  | tm_tapp t1 T => tm_tapp (subst_tm_env sigma t1) T
  | tm_choice t1 t2 => tm_choice (subst_tm_env sigma t1) (subst_tm_env sigma t2)
  end.

Definition update_sub (sub : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb Y X then U else sub Y.

Definition update_tyenv (envF : atom -> tm -> tm -> Prop) (X : atom)
    (R : tm -> tm -> Prop) : atom -> tm -> tm -> Prop :=
  fun Y => if Nat.eqb Y X then R else envF Y.

Definition update_tmenv (sigma : atom -> tm) (x : atom) (a : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then a else sigma y.

(* ============================================================ *)
(* The logical relation                                          *)
(* ============================================================ *)

Definition RelTy := tm -> tm -> Prop.
Definition TyRelEnv := atom -> RelTy.
Definition BRelEnv := list RelTy.

Definition nth_rel (i : nat) (env : BRelEnv) : RelTy :=
  match nth_error env i with
  | Some R => R
  | None => fun _ _ => False
  end.

Definition set_at_rel (k : nat) (R : RelTy) (env : BRelEnv) : BRelEnv :=
  firstn k env ++ R :: skipn (S k) env.

(* [Sem true T envB envF] is the term relation at [T];
   [Sem false T envB envF] is the value relation at [T]. *)
Fixpoint Sem (mode : bool) (T : ty) : BRelEnv -> TyRelEnv -> tm -> tm -> Prop :=
  match T with
  | Ty_BVar i => fun envB envF t1 t2 =>
      if mode then
        (exists v1 v2, value v1 /\ value v2 /\ (t1 -->* v1) /\ (t2 -->* v2) /\
           nth_rel i envB v1 v2)
      else nth_rel i envB t1 t2
  | Ty_FVar X => fun envB envF t1 t2 =>
      if mode then
        (exists v1 v2, value v1 /\ value v2 /\ (t1 -->* v1) /\ (t2 -->* v2) /\
           envF X v1 v2)
      else envF X t1 t2
  | Ty_Arrow A B => fun envB envF t1 t2 =>
      if mode then
        (exists v1 v2, value v1 /\ value v2 /\ (t1 -->* v1) /\ (t2 -->* v2) /\
          (value v1 /\ value v2 /\
           forall a1 a2, value a1 -> value a2 -> Sem false A envB envF a1 a2 ->
             Sem true B envB envF (tm_app v1 a1) (tm_app v2 a2)))
      else
        (value t1 /\ value t2 /\
         forall a1 a2, value a1 -> value a2 -> Sem false A envB envF a1 a2 ->
           Sem true B envB envF (tm_app t1 a1) (tm_app t2 a2))
  | Ty_All B => fun envB envF t1 t2 =>
      if mode then
        (exists v1 v2, value v1 /\ value v2 /\ (t1 -->* v1) /\ (t2 -->* v2) /\
          (value v1 /\ value v2 /\
           forall (A : ty) (S : RelTy), lc_ty_at 0 A ->
             Sem true B (S :: envB) envF (tm_tapp v1 A) (tm_tapp v2 A)))
      else
        (value t1 /\ value t2 /\
         forall (A : ty) (S : RelTy), lc_ty_at 0 A ->
           Sem true B (S :: envB) envF (tm_tapp t1 A) (tm_tapp t2 A))
  end.

Definition RelSem (T : ty) (envB : BRelEnv) (envF : TyRelEnv) : tm -> tm -> Prop :=
  Sem true T envB envF.

Definition ValSem (T : ty) (envB : BRelEnv) (envF : TyRelEnv) : tm -> tm -> Prop :=
  Sem false T envB envF.


Hint Constructors lc_ty_at lc_tm_at value : core.

(* ============================================================ *)
(* Monotonicity and inversion lemmas for local closure          *)
(* ============================================================ *)

Lemma lc_ty_at_mono : forall k T, lc_ty_at k T -> forall j, lc_ty_at (k + j) T.
Proof.
  intros k T H. induction H.
  - intros j. constructor. lia.
  - intros j. constructor.
  - intros j. constructor; [apply IHlc_ty_at1 | apply IHlc_ty_at2].
  - intros j. apply lc_ty_all.
    replace (S k + j) with (S (k + j)) by lia.
    apply IHlc_ty_at.
Qed.

Lemma lc_ty_at_mono_le : forall k k' T, k <= k' -> lc_ty_at k T -> lc_ty_at k' T.
Proof.
  intros k k' T Hle H.
  destruct (Nat.le_exists_sub k k' Hle) as [d [Heq _]].
  subst k'. replace (d + k) with (k + d) by lia.
  apply lc_ty_at_mono with (j := d). assumption.
Qed.

Lemma lc_tm_at_mono : forall K k t, lc_tm_at K k t ->
  forall a b, lc_tm_at (K + a) (k + b) t.
Proof.
  intros K k t H. induction H.
  - intros a b. constructor. lia.
  - intros a b. constructor.
  - intros a b. constructor.
    + apply lc_ty_at_mono. assumption.
    + apply IHlc_tm_at.
  - intros a b. constructor; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
  - intros a b. apply lc_tm_tabs.
    replace (S K + a) with (S (K + a)) by lia.
    apply IHlc_tm_at.
  - intros a b. constructor.
    + apply IHlc_tm_at.
    + apply lc_ty_at_mono. assumption.
  - intros a b. constructor; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
Qed.

Lemma lc_tm_at_mono_K : forall K K' k t, K <= K' -> lc_tm_at K k t -> lc_tm_at K' k t.
Proof.
  intros K K' k t Hle H.
  destruct (Nat.le_exists_sub K K' Hle) as [d [Heq _]].
  subst K'. replace (d + K) with (K + d) by lia.
  pose proof (lc_tm_at_mono K k t H d 0) as X.
  replace (k + 0) with k in X by lia.
  exact X.
Qed.

(* Inversion of opening for types *)
Lemma lc_ty_open_inv : forall K j U T,
  lc_ty_at K (open_ty_rec j U T) ->
  lc_ty_at 0 U ->
  lc_ty_at (Nat.max K (S j)) T.
Proof.
  intros K j U T. revert K j. induction T; intros K j Hopened HU; cbn [open_ty_rec] in *.
  - destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. constructor. lia.
    + apply Nat.eqb_neq in E. constructor. inversion Hopened; lia.
  - constructor.
  - inversion Hopened as [| | K0 Ta Tb Ha Hb |]; subst.
    apply lc_ty_arrow.
    + apply IHT1 with (K := K) (j := j); assumption.
    + apply IHT2 with (K := K) (j := j); assumption.
  - inversion Hopened as [| | | K0 T0 H0]; subst.
    apply lc_ty_all.
    replace (S (Nat.max K (S j))) with (Nat.max (S K) (S (S j))) by lia.
    apply IHT with (K := S K) (j := S j); assumption.
Qed.

(* Forward local closure for type opening *)
Lemma lc_ty_open_fwd : forall K j U T,
  lc_ty_at K T ->
  lc_ty_at 0 U ->
  lc_ty_at K (open_ty_rec j U T).
Proof.
  intros K j U T. revert K j. induction T; intros K j HT HU; cbn [open_ty_rec] in *.
  - destruct (Nat.eqb j n) eqn:E.
    + pose proof (lc_ty_at_mono 0 U HU K) as X. simpl in X. exact X.
    + constructor. inversion HT; lia.
  - constructor.
  - inversion HT as [| | K0 Ta Tb Ha Hb |]; subst.
    apply lc_ty_arrow.
    + apply IHT1 with (K := K) (j := j); assumption.
    + apply IHT2 with (K := K) (j := j); assumption.
  - inversion HT as [| | | K0 T0 H0]; subst.
    apply lc_ty_all.
    apply IHT with (K := S K) (j := S j); assumption.
Qed.

(* Inversion of opening for terms by a term variable *)
Lemma lc_tm_open_tm_inv : forall K k j x t,
  lc_tm_at K k (open_tm_rec j (tm_fvar x) t) ->
  lc_tm_at K (Nat.max k (S j)) t.
Proof.
  intros K k j x t. revert K k j. induction t; intros K k j Hopened;
    cbn [open_tm_rec] in *.
  - destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. constructor. lia.
    + apply Nat.eqb_neq in E. constructor. inversion Hopened; lia.
  - constructor.
  - inversion Hopened; subst.
    apply lc_tm_abs.
    + assumption.
    + replace (S (Nat.max k (S j))) with (Nat.max (S k) (S (S j))) by lia.
      apply IHt. assumption.
  - inversion Hopened; subst.
    apply lc_tm_app.
    + apply IHt1. assumption.
    + apply IHt2. assumption.
  - inversion Hopened; subst.
    apply lc_tm_tabs.
    apply IHt. assumption.
  - inversion Hopened; subst.
    apply lc_tm_tapp.
    + apply IHt. assumption.
    + assumption.
  - inversion Hopened; subst.
    apply lc_tm_choice.
    + apply IHt1. assumption.
    + apply IHt2. assumption.
Qed.

(* Inversion of opening for terms by a type *)
Lemma lc_tm_open_ty_inv : forall K k j U t,
  lc_tm_at K k (open_tm_ty_rec j U t) ->
  lc_ty_at 0 U ->
  lc_tm_at (Nat.max K (S j)) k t.
Proof.
  intros K k j U t. revert K k j. induction t; intros K k j Hopened HU;
    cbn [open_tm_ty_rec] in *.
  - constructor. inversion Hopened; lia.
  - constructor.
  - inversion Hopened; subst.
    apply lc_tm_abs.
    + apply lc_ty_open_inv with (j := j) (U := U); assumption.
    + apply IHt; assumption.
  - inversion Hopened; subst.
    apply lc_tm_app; [apply IHt1 | apply IHt2]; assumption.
  - inversion Hopened; subst.
    apply lc_tm_tabs.
    replace (S (Nat.max K (S j))) with (Nat.max (S K) (S (S j))) by lia.
    apply IHt; assumption.
  - inversion Hopened; subst.
    apply lc_tm_tapp.
    + apply IHt; assumption.
    + apply lc_ty_open_inv with (j := j) (U := U); assumption.
  - inversion Hopened; subst.
    apply lc_tm_choice; [apply IHt1 | apply IHt2]; assumption.
Qed.

(* Forward local closure for term annotation opening *)
Lemma lc_tm_open_ty_fwd : forall K k j U t,
  lc_tm_at K k t ->
  lc_ty_at 0 U ->
  lc_tm_at K k (open_tm_ty_rec j U t).
Proof.
  intros K k j U t. revert K k j. induction t; intros K k j Hlc HU;
    cbn [open_tm_ty_rec].
  - constructor. inversion Hlc; lia.
  - constructor.
  - inversion Hlc; subst.
    apply lc_tm_abs.
    + apply lc_ty_open_fwd; assumption.
    + apply IHt; assumption.
  - inversion Hlc; subst.
    apply lc_tm_app; [apply IHt1 | apply IHt2]; assumption.
  - inversion Hlc; subst.
    apply lc_tm_tabs.
    apply IHt; assumption.
  - inversion Hlc; subst.
    apply lc_tm_tapp.
    + apply IHt; assumption.
    + apply lc_ty_open_fwd; assumption.
  - inversion Hlc; subst.
    apply lc_tm_choice; [apply IHt1 | apply IHt2]; assumption.
Qed.

(* ============================================================ *)
(* Well-formed and well-typed terms are locally closed          *)
(* ============================================================ *)

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H.
  - constructor.
  - constructor; assumption.
  - apply lc_ty_all.
    pose proof (H0 (fresh_atom L) (fresh_atom_notin L)) as Hlc.
    apply lc_ty_open_inv with (K := 0) (j := 0)
      (U := Ty_FVar (fresh_atom L)) in Hlc.
    + simpl in Hlc. exact Hlc.
    + constructor.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at 0 0 t.
Proof.
  intros Delta Gamma t T H. induction H.
  - constructor.
  - apply lc_tm_abs.
    + eapply wf_ty_lc. eassumption.
    + pose proof (H1 (fresh_atom L) (fresh_atom_notin L)) as Hbody.
      apply lc_tm_open_tm_inv with (K := 0) (k := 0) (j := 0)
        (x := fresh_atom L) in Hbody.
      simpl in Hbody. exact Hbody.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    pose proof (H0 (fresh_atom L) (fresh_atom_notin L)) as Hbody.
    apply lc_tm_open_ty_inv with (K := 0) (k := 0) (j := 0)
      (U := Ty_FVar (fresh_atom L)) in Hbody.
    + simpl in Hbody. exact Hbody.
    + constructor.
  - apply lc_tm_tapp.
    + assumption.
    + eapply wf_ty_lc. eassumption.
  - apply lc_tm_choice; assumption.
Qed.


(* ============================================================ *)
(* Opening is the identity on locally closed objects            *)
(* ============================================================ *)

Lemma open_ty_rec_lc_id : forall K T, lc_ty_at K T ->
  forall j U, K <= j -> open_ty_rec j U T = T.
Proof.
  intros K T H. induction H; intros j U Hle; cbn.
  - assert (Hneq : (j =? i) = false) by (apply Nat.eqb_neq; lia).
    rewrite Hneq. reflexivity.
  - reflexivity.
  - rewrite IHlc_ty_at1 by assumption. rewrite IHlc_ty_at2 by assumption. reflexivity.
  - rewrite IHlc_ty_at. reflexivity. lia.
Qed.

Lemma open_tm_rec_lc_id : forall K k t, lc_tm_at K k t ->
  forall j u, k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k t H. induction H; intros j u Hle; cbn.
  - assert (Hneq : (j =? i) = false) by (apply Nat.eqb_neq; lia).
    rewrite Hneq. reflexivity.
  - reflexivity.
  - rewrite IHlc_tm_at by lia. reflexivity.
  - rewrite IHlc_tm_at1 by assumption. rewrite IHlc_tm_at2 by assumption. reflexivity.
  - rewrite IHlc_tm_at by assumption. reflexivity.
  - rewrite IHlc_tm_at by assumption. reflexivity.
  - rewrite IHlc_tm_at1 by assumption. rewrite IHlc_tm_at2 by assumption. reflexivity.
Qed.

Lemma open_tm_ty_rec_lc_id : forall K k t, lc_tm_at K k t ->
  forall j U, K <= j -> open_tm_ty_rec j U t = t.
Proof.
  intros K k t H. induction H; intros j U Hle; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHlc_tm_at by assumption.
    erewrite open_ty_rec_lc_id; [reflexivity | eassumption | assumption].
  - rewrite IHlc_tm_at1 by assumption. rewrite IHlc_tm_at2 by assumption. reflexivity.
  - rewrite (IHlc_tm_at (S j) U) by lia. reflexivity.
  - rewrite IHlc_tm_at by assumption.
    erewrite open_ty_rec_lc_id; [reflexivity | eassumption | assumption].
  - rewrite IHlc_tm_at1 by assumption. rewrite IHlc_tm_at2 by assumption. reflexivity.
Qed.

(* ============================================================ *)
(* Agreement of substitutions                                   *)
(* ============================================================ *)

Lemma subst_ty_env_agree : forall sub1 sub2 T,
  (forall X, In X (ty_fv T) -> sub1 X = sub2 X) ->
  subst_ty_env sub1 T = subst_ty_env sub2 T.
Proof.
  intros sub1 sub2 T. revert sub1 sub2. induction T; intros sub1 sub2 Hagree;
    cbn [subst_ty_env ty_fv].
  - reflexivity.
  - apply Hagree. simpl. auto.
  - assert (E1 : subst_ty_env sub1 T1 = subst_ty_env sub2 T1).
    { apply IHT1. intros X Hin. apply Hagree. apply in_or_app. left. exact Hin. }
    assert (E2 : subst_ty_env sub1 T2 = subst_ty_env sub2 T2).
    { apply IHT2. intros X Hin. apply Hagree. apply in_or_app. right. exact Hin. }
    rewrite E1, E2. reflexivity.
  - assert (E : subst_ty_env sub1 T = subst_ty_env sub2 T).
    { apply IHT. intros X Hin. apply Hagree. exact Hin. }
    rewrite E. reflexivity.
Qed.

Lemma subst_tm_ty_env_agree : forall sub1 sub2 t,
  (forall X, In X (tm_ty_fv t) -> sub1 X = sub2 X) ->
  subst_tm_ty_env sub1 t = subst_tm_ty_env sub2 t.
Proof.
  intros sub1 sub2 t. revert sub1 sub2. induction t; intros sub1 sub2 Hagree;
    cbn [subst_tm_ty_env tm_ty_fv].
  - reflexivity.
  - reflexivity.
  - assert (E1 : subst_tm_ty_env sub1 t0 = subst_tm_ty_env sub2 t0).
    { apply IHt. intros X Hin. apply Hagree. apply in_or_app. right. exact Hin. }
    assert (E2 : subst_ty_env sub1 t = subst_ty_env sub2 t).
    { apply subst_ty_env_agree. intros X Hin. apply Hagree. apply in_or_app. left. exact Hin. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : subst_tm_ty_env sub1 t1 = subst_tm_ty_env sub2 t1).
    { apply IHt1. intros X Hin. apply Hagree. apply in_or_app. left. exact Hin. }
    assert (E2 : subst_tm_ty_env sub1 t2 = subst_tm_ty_env sub2 t2).
    { apply IHt2. intros X Hin. apply Hagree. apply in_or_app. right. exact Hin. }
    rewrite E1, E2. reflexivity.
  - assert (E : subst_tm_ty_env sub1 t = subst_tm_ty_env sub2 t).
    { apply IHt. intros X Hin. apply Hagree. exact Hin. }
    rewrite E. reflexivity.
  - assert (E1 : subst_tm_ty_env sub1 t = subst_tm_ty_env sub2 t).
    { apply IHt. intros X Hin. apply Hagree. apply in_or_app. left. exact Hin. }
    assert (E2 : subst_ty_env sub1 t0 = subst_ty_env sub2 t0).
    { apply subst_ty_env_agree. intros X Hin. apply Hagree. apply in_or_app. right. exact Hin. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : subst_tm_ty_env sub1 t1 = subst_tm_ty_env sub2 t1).
    { apply IHt1. intros X Hin. apply Hagree. apply in_or_app. left. exact Hin. }
    assert (E2 : subst_tm_ty_env sub1 t2 = subst_tm_ty_env sub2 t2).
    { apply IHt2. intros X Hin. apply Hagree. apply in_or_app. right. exact Hin. }
    rewrite E1, E2. reflexivity.
Qed.

Lemma subst_tm_env_agree : forall sigma1 sigma2 t,
  (forall x, In x (tm_fv t) -> sigma1 x = sigma2 x) ->
  subst_tm_env sigma1 t = subst_tm_env sigma2 t.
Proof.
  intros sigma1 sigma2 t. revert sigma1 sigma2. induction t; intros sigma1 sigma2 Hagree;
    cbn [subst_tm_env tm_fv].
  - reflexivity.
  - apply Hagree. simpl. auto.
  - assert (E : subst_tm_env sigma1 t0 = subst_tm_env sigma2 t0).
    { apply IHt. intros y Hin. apply Hagree. exact Hin. }
    rewrite E. reflexivity.
  - assert (E1 : subst_tm_env sigma1 t1 = subst_tm_env sigma2 t1).
    { apply IHt1. intros y Hin. apply Hagree. apply in_or_app. left. exact Hin. }
    assert (E2 : subst_tm_env sigma1 t2 = subst_tm_env sigma2 t2).
    { apply IHt2. intros y Hin. apply Hagree. apply in_or_app. right. exact Hin. }
    rewrite E1, E2. reflexivity.
  - assert (E : subst_tm_env sigma1 t = subst_tm_env sigma2 t).
    { apply IHt. intros y Hin. apply Hagree. exact Hin. }
    rewrite E. reflexivity.
  - assert (E : subst_tm_env sigma1 t = subst_tm_env sigma2 t).
    { apply IHt. intros y Hin. apply Hagree. exact Hin. }
    rewrite E. reflexivity.
  - assert (E1 : subst_tm_env sigma1 t1 = subst_tm_env sigma2 t1).
    { apply IHt1. intros y Hin. apply Hagree. apply in_or_app. left. exact Hin. }
    assert (E2 : subst_tm_env sigma1 t2 = subst_tm_env sigma2 t2).
    { apply IHt2. intros y Hin. apply Hagree. apply in_or_app. right. exact Hin. }
    rewrite E1, E2. reflexivity.
Qed.

Lemma subst_ty_env_id : forall T, subst_ty_env (fun X => Ty_FVar X) T = T.
Proof.
  induction T; cbn; [reflexivity | reflexivity | rewrite IHT1, IHT2; reflexivity | rewrite IHT; reflexivity].
Qed.

Lemma subst_tm_ty_env_id : forall t, subst_tm_ty_env (fun X => Ty_FVar X) t = t.
Proof.
  induction t; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHt, subst_ty_env_id. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt, subst_ty_env_id. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma subst_tm_env_id : forall t, subst_tm_env (fun x => tm_fvar x) t = t.
Proof.
  induction t; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

(* ============================================================ *)
(* Commutation lemmas                                           *)
(* ============================================================ *)

Lemma subst_ty_env_open_ty_rec : forall sub,
  (forall X, lc_ty_at 0 (sub X)) ->
  forall k X T,
  subst_ty_env sub (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k (sub X) (subst_ty_env sub T).
Proof.
  intros sub Hsub k X T. revert k.
  induction T; intros k; cbn [open_ty_rec subst_ty_env].
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_ty_rec_lc_id with (K := 0); [apply Hsub | lia].
  - rewrite IHT1, IHT2. reflexivity.
  - rewrite IHT. reflexivity.
Qed.

Lemma subst_tm_ty_env_open_tm_ty_rec : forall sub,
  (forall X, lc_ty_at 0 (sub X)) ->
  forall k X t,
  subst_tm_ty_env sub (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k (sub X) (subst_tm_ty_env sub t).
Proof.
  intros sub Hsub k X t. revert k.
  induction t; intros k; cbn [open_tm_ty_rec subst_tm_ty_env].
  - reflexivity.
  - reflexivity.
  - rewrite IHt. erewrite subst_ty_env_open_ty_rec; [reflexivity | exact Hsub].
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. erewrite subst_ty_env_open_ty_rec; [reflexivity | exact Hsub].
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma subst_tm_ty_env_open_tm_rec : forall sub k x t,
  subst_tm_ty_env sub (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (tm_fvar x) (subst_tm_ty_env sub t).
Proof.
  intros sub k x t. revert k. induction t; intros k; cbn [open_tm_rec subst_tm_ty_env].
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma subst_tm_env_open_tm_rec : forall sigma,
  (forall y, lc_tm_at 0 0 (sigma y)) ->
  forall k a t,
  subst_tm_env sigma (open_tm_rec k (tm_fvar a) t) =
  open_tm_rec k (sigma a) (subst_tm_env sigma t).
Proof.
  intros sigma Hlc k a t. revert k. induction t; intros k;
    cbn [open_tm_rec subst_tm_env].
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_tm_rec_lc_id with (K := 0) (k := 0); [apply Hlc | lia].
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma subst_tm_env_open_tm_ty_rec : forall sigma,
  (forall y, lc_tm_at 0 0 (sigma y)) ->
  forall k U t,
  subst_tm_env sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (subst_tm_env sigma t).
Proof.
  intros sigma Hlc k U t. revert k. induction t; intros k;
    cbn [open_tm_ty_rec subst_tm_env].
  - reflexivity.
  - symmetry. apply open_tm_ty_rec_lc_id with (K := 0) (k := 0); [apply Hlc | lia].
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

(* ============================================================ *)
(* Local closure is preserved by substitutions                  *)
(* ============================================================ *)

Lemma subst_ty_env_lc : forall sub,
  (forall X, lc_ty_at 0 (sub X)) ->
  forall T K, lc_ty_at K T -> lc_ty_at K (subst_ty_env sub T).
Proof.
  intros sub Hsub T. induction T; intros K H; cbn [subst_ty_env].
  - inversion H. constructor. assumption.
  - pose proof (lc_ty_at_mono 0 (sub a) (Hsub a) K) as X. simpl in X. exact X.
  - inversion H. constructor.
    + apply IHT1 with (K := K). assumption.
    + apply IHT2 with (K := K). assumption.
  - inversion H. apply lc_ty_all. apply IHT with (K := S K). assumption.
Qed.

Lemma subst_tm_ty_env_lc : forall sub,
  (forall X, lc_ty_at 0 (sub X)) ->
  forall t K k, lc_tm_at K k t -> lc_tm_at K k (subst_tm_ty_env sub t).
Proof.
  intros sub Hsub t. induction t; intros K k H; cbn [subst_tm_ty_env].
  - inversion H. constructor. assumption.
  - constructor.
  - inversion H. constructor.
    + eapply subst_ty_env_lc; [exact Hsub | eassumption].
    + apply IHt. assumption.
  - inversion H. constructor; [apply IHt1 | apply IHt2]; assumption.
  - inversion H. apply lc_tm_tabs. apply IHt. assumption.
  - inversion H. constructor.
    + apply IHt. assumption.
    + eapply subst_ty_env_lc; [exact Hsub | eassumption].
  - inversion H. constructor; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma subst_tm_env_lc : forall sigma,
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  forall t K k, lc_tm_at K k t -> lc_tm_at K k (subst_tm_env sigma t).
Proof.
  intros sigma Hsigma t. induction t; intros K k H; cbn [subst_tm_env].
  - inversion H. constructor. assumption.
  - pose proof (Hsigma a) as Hs.
    pose proof (lc_tm_at_mono 0 0 (sigma a) Hs K k) as Hm.
    simpl in Hm. exact Hm.
  - inversion H. constructor; [assumption | apply IHt]. assumption.
  - inversion H. constructor; [apply IHt1 | apply IHt2]; assumption.
  - inversion H. apply lc_tm_tabs. apply IHt. assumption.
  - inversion H. constructor; [apply IHt; assumption | assumption].
  - inversion H. constructor; [apply IHt1 | apply IHt2]; assumption.
Qed.

(* ============================================================ *)
(* Auxiliary lemmas about relations and environments            *)
(* ============================================================ *)

Definition rel_iff (R1 R2 : RelTy) : Prop := forall a b, R1 a b <-> R2 a b.

Definition envB_agree (K : nat) (e1 e2 : BRelEnv) : Prop :=
  forall i, i < K -> rel_iff (nth_rel i e1) (nth_rel i e2).

Lemma nth_rel_set_at_eq : forall k R env, k <= length env ->
  rel_iff (nth_rel k (set_at_rel k R env)) R.
Proof.
  intros k R env Hlen a b. unfold nth_rel, set_at_rel.
  rewrite nth_error_app2.
  - replace (k - length (firstn k env)) with 0 by (rewrite firstn_length_le; lia).
    reflexivity.
  - rewrite firstn_length_le; lia.
Qed.

Lemma nth_rel_set_at_lt : forall i k R env, i < k -> k <= length env ->
  rel_iff (nth_rel i (set_at_rel k R env)) (nth_rel i env).
Proof.
  intros i k R env Hlt Hlen a b. unfold nth_rel, set_at_rel.
  assert (Hkl : length (firstn k env) = k) by (rewrite firstn_length_le; lia).
  rewrite nth_error_app1 by (rewrite Hkl; lia).
  rewrite nth_error_firstn.
  assert (Hltb : (i <? k) = true) by (apply Nat.ltb_lt; lia).
  rewrite Hltb. reflexivity.
Qed.

Lemma set_at_rel_cons : forall k R Q env,
  set_at_rel (S k) R (Q :: env) = Q :: set_at_rel k R env.
Proof.
  intros k R Q env. unfold set_at_rel. simpl. reflexivity.
Qed.

Lemma nth_rel_cons : forall i R env,
  nth_rel (S i) (R :: env) = nth_rel i env.
Proof. intros. unfold nth_rel. simpl. reflexivity. Qed.

Lemma nth_rel_cons_0 : forall R env, nth_rel 0 (R :: env) = R.
Proof. intros. unfold nth_rel. simpl. reflexivity. Qed.

Lemma envB_agree_cons : forall K e1 e2 R1 R2,
  rel_iff R1 R2 ->
  envB_agree K e1 e2 ->
  envB_agree (S K) (R1 :: e1) (R2 :: e2).
Proof.
  intros K e1 e2 R1 R2 HR Hagree i Hi. destruct i.
  - rewrite !nth_rel_cons_0. apply HR.
  - rewrite !nth_rel_cons. apply Hagree. lia.
Qed.

Lemma envB_agree_set_at_cons : forall k (V1 V0 Q : RelTy) envB,
  k <= length envB ->
  rel_iff V1 V0 ->
  envB_agree (S (S k)) (Q :: set_at_rel k V1 envB)
                        (Q :: set_at_rel k V0 envB).
Proof.
  intros k V1 V0 Q envB Hlen HV i Hi a b.
  destruct i as [| i].
  - rewrite !nth_rel_cons_0. reflexivity.
  - rewrite !nth_rel_cons.
    assert (Hik : i <= k) by lia.
    destruct (Nat.lt_ge_cases i k) as [Hlt | Hge].
    + rewrite (nth_rel_set_at_lt i k V1 envB Hlt Hlen a b).
      rewrite (nth_rel_set_at_lt i k V0 envB Hlt Hlen a b).
      reflexivity.
    + assert (i = k) by lia. subst i.
      rewrite (nth_rel_set_at_eq k V1 envB Hlen a b).
      rewrite (nth_rel_set_at_eq k V0 envB Hlen a b).
      apply HV.
Qed.

(* ============================================================ *)
(* Reduction lemmas                                              *)
(* ============================================================ *)

Lemma value_lc : forall v, value v -> lc_tm_at 0 0 v.
Proof. intros v H. induction H; assumption. Qed.

Lemma value_no_step : forall v v', value v -> (v --> v') -> False.
Proof.
  intros v v' Hv Hs. induction Hv; inversion Hs.
Qed.

Lemma multi_value : forall v u, value v -> (v -->* u) -> u = v.
Proof.
  intros v u Hv Hm. revert Hv. induction Hm; intros Hv.
  - reflexivity.
  - exfalso. eapply value_no_step; eassumption.
Qed.

Lemma multi_trans : forall a b c, (a -->* b) -> (b -->* c) -> (a -->* c).
Proof.
  intros a b c H1 H2. induction H1.
  - assumption.
  - eapply multi_step; [eassumption | apply IHmulti; assumption].
Qed.

Lemma step_multi : forall t u, (t --> u) -> (t -->* u).
Proof. intros t u H. eapply multi_step; [exact H | apply multi_refl]. Qed.

Lemma multi_app_l : forall t1 t1' t2,
  lc_tm_at 0 0 t2 -> (t1 -->* t1') ->
  (tm_app t1 t2 -->* tm_app t1' t2).
Proof.
  intros t1 t1' t2 Hlc H. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + eapply ST_App1; eassumption.
    + apply IHmulti.
Qed.

Lemma multi_app_r : forall v1 t2 t2',
  value v1 -> (t2 -->* t2') ->
  (tm_app v1 t2 -->* tm_app v1 t2').
Proof.
  intros v1 t2 t2' Hv H. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + eapply ST_App2; eassumption.
    + apply IHmulti.
Qed.

Lemma multi_tapp : forall t t' T,
  lc_ty_at 0 T -> (t -->* t') ->
  (tm_tapp t T -->* tm_tapp t' T).
Proof.
  intros t t' T Hlc H. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + eapply ST_TApp; eassumption.
    + apply IHmulti.
Qed.

Lemma multi_choice_l : forall t1 t2 u,
  lc_tm_at 0 0 t1 -> lc_tm_at 0 0 t2 -> (t1 -->* u) ->
  (tm_choice t1 t2 -->* u).
Proof.
  intros t1 t2 u H1 H2 H. eapply multi_step.
  - eapply ST_ChoiceLeft; eassumption.
  - assumption.
Qed.

Lemma multi_choice_r : forall t1 t2 u,
  lc_tm_at 0 0 t1 -> lc_tm_at 0 0 t2 -> (t2 -->* u) ->
  (tm_choice t1 t2 -->* u).
Proof.
  intros t1 t2 u H1 H2 H. eapply multi_step.
  - eapply ST_ChoiceRight; eassumption.
  - assumption.
Qed.

(* ============================================================ *)
(* Basic properties of the term relation                        *)
(* ============================================================ *)

Lemma RelSem_def : forall T envB envF t1 t2,
  RelSem T envB envF t1 t2 <->
  (exists v1 v2, value v1 /\ value v2 /\ (t1 -->* v1) /\ (t2 -->* v2) /\
                 ValSem T envB envF v1 v2).
Proof.
  intros T envB envF t1 t2. destruct T; cbn [RelSem ValSem Sem]; reflexivity.
Qed.

Lemma RelSem_of_val : forall T envB envF v1 v2,
  value v1 -> value v2 -> ValSem T envB envF v1 v2 ->
  RelSem T envB envF v1 v2.
Proof.
  intros T envB envF v1 v2 Hv1 Hv2 HV.
  apply RelSem_def. exists v1, v2.
  split; [assumption|]. split; [assumption|].
  split; [apply multi_refl|]. split; [apply multi_refl|assumption].
Qed.

Lemma ValSem_of_RelSem : forall T envB envF v1 v2,
  value v1 -> value v2 -> RelSem T envB envF v1 v2 ->
  ValSem T envB envF v1 v2.
Proof.
  intros T envB envF v1 v2 Hv1 Hv2 HR.
  apply RelSem_def in HR. destruct HR as (w1 & w2 & _ & _ & M1 & M2 & HV).
  assert (w1 = v1) by (eapply multi_value; eassumption).
  assert (w2 = v2) by (eapply multi_value; eassumption).
  subst w1 w2. exact HV.
Qed.

Lemma RelSem_multi_l : forall T envB envF t1 t1' t2,
  (t1 -->* t1') -> RelSem T envB envF t1' t2 -> RelSem T envB envF t1 t2.
Proof.
  intros T envB envF t1 t1' t2 Hm HR.
  apply RelSem_def in HR. apply RelSem_def.
  destruct HR as (v1 & v2 & Hv1 & Hv2 & M1 & M2 & HV).
  exists v1, v2. split; [assumption|]. split; [assumption|].
  split; [| split; assumption].
  eapply multi_trans; eassumption.
Qed.

Lemma RelSem_multi_r : forall T envB envF t1 t2 t2',
  (t2 -->* t2') -> RelSem T envB envF t1 t2' -> RelSem T envB envF t1 t2.
Proof.
  intros T envB envF t1 t2 t2' Hm HR.
  apply RelSem_def in HR. apply RelSem_def.
  destruct HR as (v1 & v2 & Hv1 & Hv2 & M1 & M2 & HV).
  exists v1, v2. split; [assumption|]. split; [assumption|].
  split; [assumption|]. split.
  - eapply multi_trans; eassumption.
  - assumption.
Qed.

Lemma RelSem_val_l : forall T envB envF v1 t2,
  value v1 -> RelSem T envB envF v1 t2 ->
  exists v2, value v2 /\ (t2 -->* v2) /\ ValSem T envB envF v1 v2.
Proof.
  intros T envB envF v1 t2 Hv1 HR.
  apply RelSem_def in HR. destruct HR as (w1 & w2 & Hw1 & Hw2 & M1 & M2 & HV).
  assert (w1 = v1) by (eapply multi_value; eassumption).
  subst w1. exists w2. split; [assumption|]. split; assumption.
Qed.

Lemma RelSem_val_r : forall T envB envF t1 v2,
  value v2 -> RelSem T envB envF t1 v2 ->
  exists v1, value v1 /\ (t1 -->* v1) /\ ValSem T envB envF v1 v2.
Proof.
  intros T envB envF t1 v2 Hv2 HR.
  apply RelSem_def in HR. destruct HR as (w1 & w2 & Hw1 & Hw2 & M1 & M2 & HV).
  assert (w2 = v2) by (eapply multi_value; eassumption).
  subst w2. exists w1. split; [assumption|]. split; assumption.
Qed.

(* ============================================================ *)
(* Congruence and environment extension for the relations       *)
(* ============================================================ *)

Lemma RelSem_congr_gen : forall T1 T2 envB1 envB2 envF1 envF2 t1 t2,
  (forall v1 v2, ValSem T1 envB1 envF1 v1 v2 <-> ValSem T2 envB2 envF2 v1 v2) ->
  RelSem T1 envB1 envF1 t1 t2 <-> RelSem T2 envB2 envF2 t1 t2.
Proof.
  intros T1 T2 e1 e2 f1 f2 t1 t2 HV.
  rewrite !RelSem_def. split.
  - intros (v1 & v2 & H1 & H2 & H3 & H4 & H5). exists v1, v2.
    split. exact H1. split. exact H2. split. exact H3. split. exact H4.
    apply HV. assumption.
  - intros (v1 & v2 & H1 & H2 & H3 & H4 & H5). exists v1, v2.
    split. exact H1. split. exact H2. split. exact H3. split. exact H4.
    apply HV. assumption.
Qed.

Lemma ValSem_envB_ext : forall T K envB1 envB2 envF,
  lc_ty_at K T ->
  envB_agree K envB1 envB2 ->
  forall v1 v2, ValSem T envB1 envF v1 v2 <-> ValSem T envB2 envF v1 v2.
Proof.
  intros T. induction T; intros K e1 e2 envF Hlc Hag v1 v2.
  - cbn [ValSem Sem]. apply Hag. inversion Hlc; lia.
  - cbn [ValSem Sem]. split; auto.
  - cbn [ValSem Sem]. inversion Hlc as [| | K0 A0 B0 HlcA HlcB |]; subst.
    split; intros (Hv1 & Hv2 & Hf); repeat split; try assumption;
      intros a1 a2 Ha1 Ha2 HA.
    + assert (HA1 : ValSem T1 e1 envF a1 a2).
      { apply (proj2 ((IHT1 K e1 e2 envF HlcA Hag) a1 a2)). assumption. }
      assert (HR2 : RelSem T2 e1 envF (tm_app v1 a1) (tm_app v2 a2) <->
                   RelSem T2 e2 envF (tm_app v1 a1) (tm_app v2 a2)).
      { apply RelSem_congr_gen. intros u1 u2.
        apply (IHT2 K e1 e2 envF HlcB Hag). }
      apply (proj1 HR2). apply (Hf a1 a2 Ha1 Ha2 HA1).
    + assert (HA2 : ValSem T1 e2 envF a1 a2).
      { apply (proj1 ((IHT1 K e1 e2 envF HlcA Hag) a1 a2)). assumption. }
      assert (HR2 : RelSem T2 e1 envF (tm_app v1 a1) (tm_app v2 a2) <->
                   RelSem T2 e2 envF (tm_app v1 a1) (tm_app v2 a2)).
      { apply RelSem_congr_gen. intros u1 u2.
        apply (IHT2 K e1 e2 envF HlcB Hag). }
      apply (proj2 HR2). apply (Hf a1 a2 Ha1 Ha2 HA2).
  - cbn [ValSem Sem]. inversion Hlc as [| | | K0 C0 HlcC]; subst.
    split; intros (Hv1 & Hv2 & Hf); repeat split; try assumption;
      intros A0 Srel HA.
    + assert (Hag' : envB_agree (S K) (Srel :: e1) (Srel :: e2)).
      { apply envB_agree_cons; [intros a b; reflexivity | assumption]. }
      assert (HR : RelSem T (Srel :: e1) envF (tm_tapp v1 A0) (tm_tapp v2 A0) <->
                  RelSem T (Srel :: e2) envF (tm_tapp v1 A0) (tm_tapp v2 A0)).
      { apply RelSem_congr_gen. intros u1 u2.
        apply (IHT (S K) (Srel :: e1) (Srel :: e2) envF HlcC Hag'). }
      apply (proj1 HR). apply (Hf A0 Srel HA).
    + assert (Hag' : envB_agree (S K) (Srel :: e1) (Srel :: e2)).
      { apply envB_agree_cons; [intros a b; reflexivity | assumption]. }
      assert (HR : RelSem T (Srel :: e1) envF (tm_tapp v1 A0) (tm_tapp v2 A0) <->
                  RelSem T (Srel :: e2) envF (tm_tapp v1 A0) (tm_tapp v2 A0)).
      { apply RelSem_congr_gen. intros u1 u2.
        apply (IHT (S K) (Srel :: e1) (Srel :: e2) envF HlcC Hag'). }
      apply (proj2 HR). apply (Hf A0 Srel HA).
Qed.

Lemma RelSem_envB_ext : forall T K envB1 envB2 envF,
  lc_ty_at K T ->
  envB_agree K envB1 envB2 ->
  forall t1 t2, RelSem T envB1 envF t1 t2 <-> RelSem T envB2 envF t1 t2.
Proof.
  intros T K e1 e2 envF Hlc Hag t1 t2.
  apply RelSem_congr_gen. intros v1 v2.
  apply ValSem_envB_ext with (K := K); assumption.
Qed.

Lemma ValSem_envF_ext : forall T envB envF1 envF2,
  (forall X, In X (ty_fv T) -> forall a b, envF1 X a b <-> envF2 X a b) ->
  forall v1 v2, ValSem T envB envF1 v1 v2 <-> ValSem T envB envF2 v1 v2.
Proof.
  intros T. induction T; intros envB e1 e2 Hag v1 v2.
  - cbn [ValSem Sem]. split; auto.
  - cbn [ValSem Sem]. apply Hag. simpl; auto.
  - cbn [ValSem Sem]. split; intros (Hv1 & Hv2 & Hf); repeat split; try assumption;
      intros a1 a2 Ha1 Ha2 HA.
    + assert (HagA : forall X, In X (ty_fv T1) -> forall a b, e1 X a b <-> e2 X a b).
      { intros X Hin. apply Hag. apply in_or_app. left. exact Hin. }
      assert (HagB : forall X, In X (ty_fv T2) -> forall a b, e1 X a b <-> e2 X a b).
      { intros X Hin. apply Hag. apply in_or_app. right. exact Hin. }
      assert (HA1 : ValSem T1 envB e1 a1 a2).
      { apply (proj2 ((IHT1 envB e1 e2 HagA) a1 a2)). assumption. }
      assert (HR2 : RelSem T2 envB e1 (tm_app v1 a1) (tm_app v2 a2) <->
                   RelSem T2 envB e2 (tm_app v1 a1) (tm_app v2 a2)).
      { apply RelSem_congr_gen. intros u1 u2.
        apply (IHT2 envB e1 e2 HagB). }
      apply (proj1 HR2). apply (Hf a1 a2 Ha1 Ha2 HA1).
    + assert (HagA : forall X, In X (ty_fv T1) -> forall a b, e1 X a b <-> e2 X a b).
      { intros X Hin. apply Hag. apply in_or_app. left. exact Hin. }
      assert (HagB : forall X, In X (ty_fv T2) -> forall a b, e1 X a b <-> e2 X a b).
      { intros X Hin. apply Hag. apply in_or_app. right. exact Hin. }
      assert (HA2 : ValSem T1 envB e2 a1 a2).
      { apply (proj1 ((IHT1 envB e1 e2 HagA) a1 a2)). assumption. }
      assert (HR2 : RelSem T2 envB e1 (tm_app v1 a1) (tm_app v2 a2) <->
                   RelSem T2 envB e2 (tm_app v1 a1) (tm_app v2 a2)).
      { apply RelSem_congr_gen. intros u1 u2.
        apply (IHT2 envB e1 e2 HagB). }
      apply (proj2 HR2). apply (Hf a1 a2 Ha1 Ha2 HA2).
  - cbn [ValSem Sem]. split; intros (Hv1 & Hv2 & Hf); repeat split; try assumption;
      intros A0 Srel HA.
    + assert (HR : RelSem T (Srel :: envB) e1 (tm_tapp v1 A0) (tm_tapp v2 A0) <->
                  RelSem T (Srel :: envB) e2 (tm_tapp v1 A0) (tm_tapp v2 A0)).
      { apply RelSem_congr_gen. intros u1 u2.
        apply (IHT (Srel :: envB) e1 e2 Hag). }
      apply (proj1 HR). apply (Hf A0 Srel HA).
    + assert (HR : RelSem T (Srel :: envB) e1 (tm_tapp v1 A0) (tm_tapp v2 A0) <->
                  RelSem T (Srel :: envB) e2 (tm_tapp v1 A0) (tm_tapp v2 A0)).
      { apply RelSem_congr_gen. intros u1 u2.
        apply (IHT (Srel :: envB) e1 e2 Hag). }
      apply (proj2 HR). apply (Hf A0 Srel HA).
Qed.

Lemma RelSem_envF_ext : forall T envB envF1 envF2,
  (forall X, In X (ty_fv T) -> forall a b, envF1 X a b <-> envF2 X a b) ->
  forall t1 t2, RelSem T envB envF1 t1 t2 <-> RelSem T envB envF2 t1 t2.
Proof.
  intros T envB e1 e2 Hag t1 t2.
  apply RelSem_congr_gen. intros v1 v2.
  apply ValSem_envF_ext; assumption.
Qed.

Lemma ValSem_U_envB_indep : forall U envB1 envB2 envF,
  lc_ty_at 0 U -> forall v1 v2,
  ValSem U envB1 envF v1 v2 <-> ValSem U envB2 envF v1 v2.
Proof.
  intros U e1 e2 envF HU v1 v2.
  apply ValSem_envB_ext with (K := 0); [assumption | intros i Hi; lia].
Qed.

Lemma ValSem_set_at_cons : forall T k U Srel envB envF,
  lc_ty_at 0 U -> k <= length envB -> lc_ty_at (S (S k)) T ->
  forall v1 v2,
    ValSem T (set_at_rel (S k) (ValSem U (Srel :: envB) envF) (Srel :: envB)) envF v1 v2
    <->
    ValSem T (Srel :: set_at_rel k (ValSem U envB envF) envB) envF v1 v2.
Proof.
  intros T k U Srel envB envF HU Hlen Hlc v1 v2.
  rewrite set_at_rel_cons.
  apply ValSem_envB_ext with (K := S (S k)).
  - exact Hlc.
  - apply envB_agree_set_at_cons; [exact Hlen |].
    intros a b. apply ValSem_U_envB_indep. assumption.
Qed.

Lemma ValSem_open_ty : forall T k U envB envF,
  lc_ty_at 0 U -> k <= length envB -> lc_ty_at (S k) T ->
  forall v1 v2,
    ValSem (open_ty_rec k U T) envB envF v1 v2 <->
    ValSem T (set_at_rel k (ValSem U envB envF) envB) envF v1 v2.
Proof.
  intros T. induction T; intros k U envB envF HU Hlen Hlc v1 v2.
  - cbn [open_ty_rec]. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. cbn [ValSem Sem].
      specialize (nth_rel_set_at_eq k (ValSem U envB envF) envB Hlen v1 v2) as Hiff.
      tauto.
    + apply Nat.eqb_neq in E. cbn [ValSem Sem].
      assert (Hlt : n < k) by (inversion Hlc; lia).
      specialize (nth_rel_set_at_lt n k (ValSem U envB envF) envB Hlt Hlen v1 v2) as Hiff.
      tauto.
  - cbn [open_ty_rec ValSem Sem]. split; auto.
  - cbn [open_ty_rec]. inversion Hlc as [| | K0 A0 B0 HlcA HlcB |]; subst.
    set (V := ValSem U envB envF).
    set (env' := set_at_rel k V envB).
    cbn [ValSem Sem].
    split; intros (Hv1 & Hv2 & Hf); repeat split; try assumption;
      intros a1 a2 Ha1 Ha2 HA.
    + assert (HA1 : ValSem (open_ty_rec k U T1) envB envF a1 a2).
      { apply (proj2 ((IHT1 k U envB envF HU Hlen HlcA) a1 a2)). assumption. }
      assert (HR2 : RelSem (open_ty_rec k U T2) envB envF (tm_app v1 a1) (tm_app v2 a2) <->
                   RelSem T2 env' envF (tm_app v1 a1) (tm_app v2 a2)).
      { apply RelSem_congr_gen. intros u1 u2.
        apply (IHT2 k U envB envF HU Hlen HlcB). }
      apply (proj1 HR2). apply (Hf a1 a2 Ha1 Ha2 HA1).
    + assert (HA2 : ValSem T1 env' envF a1 a2).
      { apply (proj1 ((IHT1 k U envB envF HU Hlen HlcA) a1 a2)). assumption. }
      assert (HR2 : RelSem (open_ty_rec k U T2) envB envF (tm_app v1 a1) (tm_app v2 a2) <->
                   RelSem T2 env' envF (tm_app v1 a1) (tm_app v2 a2)).
      { apply RelSem_congr_gen. intros u1 u2.
        apply (IHT2 k U envB envF HU Hlen HlcB). }
      apply (proj2 HR2). apply (Hf a1 a2 Ha1 Ha2 HA2).
  - cbn [open_ty_rec]. inversion Hlc as [| | | K0 C0 HlcC]; subst.
    set (V := ValSem U envB envF).
    set (env' := set_at_rel k V envB).
    cbn [ValSem Sem].
    split; intros (Hv1 & Hv2 & Hf); repeat split; try assumption;
      intros A0 Srel HA.
    + assert (HR : RelSem (open_ty_rec (S k) U T) (Srel :: envB) envF (tm_tapp v1 A0) (tm_tapp v2 A0) <->
                  RelSem T (Srel :: env') envF (tm_tapp v1 A0) (tm_tapp v2 A0)).
      { eapply iff_trans.
        - apply RelSem_congr_gen. intros u1 u2.
          apply (IHT (S k) U (Srel :: envB) envF HU).
          + simpl; lia.
          + exact HlcC.
        - apply RelSem_congr_gen. intros u1 u2.
          unfold env'. unfold V.
          apply (ValSem_set_at_cons T k U Srel envB envF HU Hlen HlcC). }
      apply (proj1 HR). apply (Hf A0 Srel HA).
    + assert (HR : RelSem (open_ty_rec (S k) U T) (Srel :: envB) envF (tm_tapp v1 A0) (tm_tapp v2 A0) <->
                  RelSem T (Srel :: env') envF (tm_tapp v1 A0) (tm_tapp v2 A0)).
      { eapply iff_trans.
        - apply RelSem_congr_gen. intros u1 u2.
          apply (IHT (S k) U (Srel :: envB) envF HU).
          + simpl; lia.
          + exact HlcC.
        - apply RelSem_congr_gen. intros u1 u2.
          unfold env'. unfold V.
          apply (ValSem_set_at_cons T k U Srel envB envF HU Hlen HlcC). }
      apply (proj2 HR). apply (Hf A0 Srel HA).
Qed.

Lemma RelSem_open_ty : forall T k U envB envF,
  lc_ty_at 0 U -> k <= length envB -> lc_ty_at (S k) T ->
  forall t1 t2,
    RelSem (open_ty_rec k U T) envB envF t1 t2 <->
    RelSem T (set_at_rel k (ValSem U envB envF) envB) envF t1 t2.
Proof.
  intros T k U envB envF HU Hlen Hlc t1 t2.
  apply RelSem_congr_gen. intros v1 v2.
  apply ValSem_open_ty; assumption.
Qed.

(* ============================================================ *)
(* Well-typedness of the type of a term                        *)
(* ============================================================ *)

Lemma lc_ty_open_tight : forall K U T,
  lc_ty_at (S K) T -> lc_ty_at 0 U -> lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K U T. revert K. induction T; intros K HT HU; cbn [open_ty_rec].
  - inversion HT; subst. destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      pose proof (lc_ty_at_mono 0 U HU K) as X. simpl in X. exact X.
    + apply Nat.eqb_neq in E. constructor. lia.
  - constructor.
  - inversion HT; subst. constructor.
    + apply IHT1 with (K := K). assumption. assumption.
    + apply IHT2 with (K := K). assumption. assumption.
  - inversion HT; subst. apply lc_ty_all.
    apply IHT with (K := S K). assumption. assumption.
Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H. induction H.
  - eapply wf_ty_lc. eassumption.
  - apply lc_ty_arrow.
    + eapply wf_ty_lc. eassumption.
    + apply (H1 (fresh_atom L) (fresh_atom_notin L)).
  - inversion IHhas_type1. assumption.
  - apply lc_ty_all.
    pose proof (H0 (fresh_atom L) (fresh_atom_notin L)) as Hbody.
    apply lc_ty_open_inv with (K := 0) (j := 0) (U := Ty_FVar (fresh_atom L)) in Hbody.
    + simpl in Hbody. exact Hbody.
    + constructor.
  - inversion IHhas_type. subst.
    apply lc_ty_open_tight with (K := 0). assumption.
    eapply wf_ty_lc. eassumption.
  - assumption.
Qed.

Lemma has_type_All_lc : forall Delta Gamma t T,
  has_type Delta Gamma t (Ty_All T) -> lc_ty_at 1 T.
Proof.
  intros. pose proof (has_type_lc_ty _ _ _ _ H) as Hlc.
  inversion Hlc. assumption.
Qed.

(* ============================================================ *)
(* Small helpers for the fundamental theorem                    *)
(* ============================================================ *)

Lemma notin_app_l : forall (A : Type) (l1 l2 : list A) (x : A),
  ~ In x (l1 ++ l2) -> ~ In x l1.
Proof.
  intros A l1 l2 x H Hc. apply H. apply in_or_app. left. exact Hc.
Qed.

Lemma notin_app_r : forall (A : Type) (l1 l2 : list A) (x : A),
  ~ In x (l1 ++ l2) -> ~ In x l2.
Proof.
  intros A l1 l2 x H Hc. apply H. apply in_or_app. right. exact Hc.
Qed.

Lemma tm_fv_subst_tm_ty_env : forall sub t,
  tm_fv (subst_tm_ty_env sub t) = tm_fv t.
Proof.
  intros sub t. induction t; cbn [subst_tm_ty_env tm_fv].
  - reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma lookup_context_update_eq : forall x Gamma T,
  lookup_context x ((x, T) :: Gamma) = Some T.
Proof.
  intros. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_context_update_neq : forall y x Gamma T,
  y <> x -> lookup_context y ((x, T) :: Gamma) = lookup_context y Gamma.
Proof.
  intros y x Gamma T Hne. simpl.
  assert (He : (y =? x) = false) by (apply Nat.eqb_neq; exact Hne).
  rewrite He. reflexivity.
Qed.

Lemma lookup_context_ctx_ty_fv : forall Gamma x U,
  lookup_context x Gamma = Some U ->
  forall X, In X (ty_fv U) -> In X (ctx_ty_fv Gamma).
Proof.
  induction Gamma as [| [y T] Gamma IH]; intros x U Hlook X Hin.
  - simpl in Hlook. discriminate.
  - simpl in Hlook. simpl.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y.
      injection Hlook as HU. subst U.
      apply in_or_app. left. exact Hin.
    + apply in_or_app. right.
      apply (IH x U Hlook X Hin).
Qed.

(* ============================================================ *)
(* The fundamental theorem                                      *)
(* ============================================================ *)

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sub envF sigma1 sigma2,
    (forall X, lc_ty_at 0 (sub X)) ->
    (forall x, lc_tm_at 0 0 (sigma1 x)) ->
    (forall x, lc_tm_at 0 0 (sigma2 x)) ->
    (forall x U, lookup_context x Gamma = Some U ->
       RelSem U [] envF (sigma1 x) (sigma2 x)) ->
    RelSem T [] envF (subst_tm_env sigma1 (subst_tm_ty_env sub t))
                     (subst_tm_env sigma2 (subst_tm_ty_env sub t)).
Proof.
  intros Delta Gamma t T H.
  induction H; intros sub envF sigma1 sigma2 Hsub Hlc1 Hlc2 Henv.
  - (* T_Var *)
    cbn [subst_tm_env subst_tm_ty_env]. apply (Henv x T H).
  - (* T_Abs *)
    cbn [subst_tm_env subst_tm_ty_env].
    set (x0 := fresh_atom (L ++ tm_fv t2)).
    assert (Hx_all : ~ In x0 (L ++ tm_fv t2)) by (unfold x0; apply fresh_atom_notin).
    assert (HxL : ~ In x0 L) by (eapply notin_app_l; exact Hx_all).
    assert (Hx_t2 : ~ In x0 (tm_fv t2)) by (eapply notin_app_r; exact Hx_all).
    pose proof (has_type_lc _ _ _ _ (H0 x0 HxL)) as Hbody_lc.
    apply lc_tm_open_tm_inv with (K := 0) (k := 0) (j := 0) (x := x0) in Hbody_lc.
    simpl in Hbody_lc.
    set (T1s := subst_ty_env sub T1).
    set (body1 := subst_tm_env sigma1 (subst_tm_ty_env sub t2)).
    set (body2 := subst_tm_env sigma2 (subst_tm_ty_env sub t2)).
    assert (Hv1 : value (tm_abs T1s body1)).
    { apply v_abs. apply lc_tm_abs.
      - unfold T1s. apply subst_ty_env_lc with (K := 0);
          [exact Hsub | eapply wf_ty_lc; eassumption].
      - unfold body1. apply subst_tm_env_lc; [exact Hlc1 |].
        apply subst_tm_ty_env_lc; [exact Hsub | exact Hbody_lc]. }
    assert (Hv2 : value (tm_abs T1s body2)).
    { apply v_abs. apply lc_tm_abs.
      - unfold T1s. apply subst_ty_env_lc with (K := 0);
          [exact Hsub | eapply wf_ty_lc; eassumption].
      - unfold body2. apply subst_tm_env_lc; [exact Hlc2 |].
        apply subst_tm_ty_env_lc; [exact Hsub | exact Hbody_lc]. }
    apply RelSem_of_val; [exact Hv1 | exact Hv2 |].
    cbn [ValSem Sem].
    split; [exact Hv1 | split; [exact Hv2 |]].
    intros a1 a2 Ha1 Ha2 HA.
    pose proof (RelSem_of_val T1 [] envF a1 a2 Ha1 Ha2 HA) as HArel.
    set (sigma1' := update_tmenv sigma1 x0 a1).
    set (sigma2' := update_tmenv sigma2 x0 a2).
    assert (Hlc1' : forall y, lc_tm_at 0 0 (sigma1' y)).
    { intro y. unfold sigma1', update_tmenv.
      destruct (Nat.eqb y x0) eqn:E.
      - apply value_lc. exact Ha1.
      - apply Hlc1. }
    assert (Hlc2' : forall y, lc_tm_at 0 0 (sigma2' y)).
    { intro y. unfold sigma2', update_tmenv.
      destruct (Nat.eqb y x0) eqn:E.
      - apply value_lc. exact Ha2.
      - apply Hlc2. }
    assert (Henv' : forall y U, lookup_context y ((x0, T1) :: Gamma) = Some U ->
                     RelSem U [] envF (sigma1' y) (sigma2' y)).
    { intros y U Hlook.
      destruct (Nat.eqb y x0) eqn:E.
      - apply Nat.eqb_eq in E. subst y.
        assert (HlookT : lookup_context x0 ((x0, T1) :: Gamma) = Some T1)
          by apply lookup_context_update_eq.
        rewrite HlookT in Hlook. injection Hlook as HU. subst U.
        assert (Heq1' : sigma1' x0 = a1)
          by (unfold sigma1', update_tmenv; rewrite Nat.eqb_refl; reflexivity).
        assert (Heq2' : sigma2' x0 = a2)
          by (unfold sigma2', update_tmenv; rewrite Nat.eqb_refl; reflexivity).
        rewrite Heq1', Heq2'. exact HArel.
      - assert (Hyx : y <> x0) by (apply Nat.eqb_neq; exact E).
        assert (HlookG : lookup_context y Gamma = Some U).
        { rewrite (lookup_context_update_neq y x0 Gamma T1 Hyx) in Hlook. exact Hlook. }
        assert (Heq1' : sigma1' y = sigma1 y).
        { unfold sigma1', update_tmenv.
          assert (He : (y =? x0) = false) by (apply Nat.eqb_neq; exact Hyx).
          rewrite He. reflexivity. }
        assert (Heq2' : sigma2' y = sigma2 y).
        { unfold sigma2', update_tmenv.
          assert (He : (y =? x0) = false) by (apply Nat.eqb_neq; exact Hyx).
          rewrite He. reflexivity. }
        rewrite Heq1', Heq2'. apply (Henv y U HlookG). }
    pose proof (H1 x0 HxL sub envF sigma1' sigma2' Hsub Hlc1' Hlc2' Henv')
      as Hbody_rel.
    assert (Heq1 : subst_tm_env sigma1'
                     (subst_tm_ty_env sub (open_tm t2 (tm_fvar x0)))
                   = open_tm body1 a1).
    { unfold open_tm. rewrite (subst_tm_ty_env_open_tm_rec sub 0 x0 t2).
      rewrite (subst_tm_env_open_tm_rec sigma1' Hlc1' 0 x0
                 (subst_tm_ty_env sub t2)).
      replace (sigma1' x0) with a1
        by (unfold sigma1', update_tmenv; rewrite Nat.eqb_refl; reflexivity).
      erewrite (subst_tm_env_agree sigma1' sigma1 (subst_tm_ty_env sub t2)).
      - unfold body1, open_tm. reflexivity.
      - intros y Hy. rewrite tm_fv_subst_tm_ty_env in Hy.
        assert (Hyx : y <> x0) by (intro Hc; subst y; apply Hx_t2; exact Hy).
        unfold sigma1', update_tmenv.
        assert (He : (y =? x0) = false) by (apply Nat.eqb_neq; exact Hyx).
        rewrite He. reflexivity. }
    assert (Heq2 : subst_tm_env sigma2'
                     (subst_tm_ty_env sub (open_tm t2 (tm_fvar x0)))
                   = open_tm body2 a2).
    { unfold open_tm. rewrite (subst_tm_ty_env_open_tm_rec sub 0 x0 t2).
      rewrite (subst_tm_env_open_tm_rec sigma2' Hlc2' 0 x0
                 (subst_tm_ty_env sub t2)).
      replace (sigma2' x0) with a2
        by (unfold sigma2', update_tmenv; rewrite Nat.eqb_refl; reflexivity).
      erewrite (subst_tm_env_agree sigma2' sigma2 (subst_tm_ty_env sub t2)).
      - unfold body2, open_tm. reflexivity.
      - intros y Hy. rewrite tm_fv_subst_tm_ty_env in Hy.
        assert (Hyx : y <> x0) by (intro Hc; subst y; apply Hx_t2; exact Hy).
        unfold sigma2', update_tmenv.
        assert (He : (y =? x0) = false) by (apply Nat.eqb_neq; exact Hyx).
        rewrite He. reflexivity. }
    eapply RelSem_multi_l with (t1' := open_tm body1 a1).
    { apply step_multi. eapply ST_AppAbs; [apply value_lc; exact Hv1 | exact Ha1]. }
    eapply RelSem_multi_r with (t2' := open_tm body2 a2).
    { apply step_multi. eapply ST_AppAbs; [apply value_lc; exact Hv2 | exact Ha2]. }
    rewrite <- Heq1, <- Heq2. exact Hbody_rel.
  - (* T_App *)
    cbn [subst_tm_env subst_tm_ty_env].
    pose proof (IHhas_type1 sub envF sigma1 sigma2 Hsub Hlc1 Hlc2 Henv) as HR1.
    pose proof (IHhas_type2 sub envF sigma1 sigma2 Hsub Hlc1 Hlc2 Henv) as HR2.
    apply RelSem_def in HR1. destruct HR1 as (v1 & v2 & Hv1 & Hv2 & M1 & M2 & HV).
    apply RelSem_def in HR2. destruct HR2 as (w1 & w2 & Hw1 & Hw2 & N1 & N2 & HW).
    cbn [ValSem Sem] in HV. destruct HV as (HV1 & HV2 & Hf).
    assert (Hb1_lc : lc_tm_at 0 0 (subst_tm_env sigma1 (subst_tm_ty_env sub t2))).
    { apply subst_tm_env_lc; [exact Hlc1 |].
      apply subst_tm_ty_env_lc; [exact Hsub | exact (has_type_lc Delta Gamma t2 T1 H0)]. }
    assert (Hb2_lc : lc_tm_at 0 0 (subst_tm_env sigma2 (subst_tm_ty_env sub t2))).
    { apply subst_tm_env_lc; [exact Hlc2 |].
      apply subst_tm_ty_env_lc; [exact Hsub | exact (has_type_lc Delta Gamma t2 T1 H0)]. }
    assert (Mapp1 : (tm_app (subst_tm_env sigma1 (subst_tm_ty_env sub t1))
                            (subst_tm_env sigma1 (subst_tm_ty_env sub t2)))
                    -->* (tm_app v1 w1)).
    { eapply multi_trans.
      - apply multi_app_l; [exact Hb1_lc | exact M1].
      - apply multi_app_r; [exact Hv1 | exact N1]. }
    assert (Mapp2 : (tm_app (subst_tm_env sigma2 (subst_tm_ty_env sub t1))
                            (subst_tm_env sigma2 (subst_tm_ty_env sub t2)))
                    -->* (tm_app v2 w2)).
    { eapply multi_trans.
      - apply multi_app_l; [exact Hb2_lc | exact M2].
      - apply multi_app_r; [exact Hv2 | exact N2]. }
    eapply RelSem_multi_l with (t1' := tm_app v1 w1).
    { exact Mapp1. }
    eapply RelSem_multi_r with (t2' := tm_app v2 w2).
    { exact Mapp2. }
    apply (Hf w1 w2 Hw1 Hw2 HW).
  - (* T_TAbs *)
    cbn [subst_tm_env subst_tm_ty_env].
    set (X := fresh_atom (L ++ ty_fv T ++ tm_ty_fv t ++ ctx_ty_fv Gamma)).
    assert (HX_all : ~ In X (L ++ ty_fv T ++ tm_ty_fv t ++ ctx_ty_fv Gamma))
      by (unfold X; apply fresh_atom_notin).
    assert (HX_L : ~ In X L)
      by (intro Hc; apply HX_all; repeat rewrite in_app_iff; tauto).
    assert (HX_T : ~ In X (ty_fv T))
      by (intro Hc; apply HX_all; repeat rewrite in_app_iff; tauto).
    assert (HX_t : ~ In X (tm_ty_fv t))
      by (intro Hc; apply HX_all; repeat rewrite in_app_iff; tauto).
    assert (HX_ctx : ~ In X (ctx_ty_fv Gamma))
      by (intro Hc; apply HX_all; repeat rewrite in_app_iff; tauto).
    pose proof (H X HX_L) as Hbody_typing.
    pose proof (has_type_lc _ _ _ _ Hbody_typing) as Hbody_lc_tm0.
    pose proof (lc_tm_open_ty_inv 0 0 0 (Ty_FVar X) t Hbody_lc_tm0
                  (lc_ty_fvar 0 X)) as Hbody_lc_tm.
    simpl in Hbody_lc_tm.
    pose proof (has_type_lc_ty _ _ _ _ Hbody_typing) as Hbody_lc_ty0.
    pose proof (lc_ty_open_inv 0 0 (Ty_FVar X) T Hbody_lc_ty0
                  (lc_ty_fvar 0 X)) as Hbody_lc_ty.
    simpl in Hbody_lc_ty.
    set (u1 := subst_tm_env sigma1 (subst_tm_ty_env sub t)).
    set (u2 := subst_tm_env sigma2 (subst_tm_ty_env sub t)).
    assert (Hu1_lc : lc_tm_at 1 0 u1).
    { unfold u1. apply subst_tm_env_lc; [exact Hlc1 |].
      apply subst_tm_ty_env_lc; [exact Hsub | exact Hbody_lc_tm]. }
    assert (Hu2_lc : lc_tm_at 1 0 u2).
    { unfold u2. apply subst_tm_env_lc; [exact Hlc2 |].
      apply subst_tm_ty_env_lc; [exact Hsub | exact Hbody_lc_tm]. }
    assert (Hv1 : value (tm_tabs u1)).
    { apply v_tabs. apply lc_tm_tabs. exact Hu1_lc. }
    assert (Hv2 : value (tm_tabs u2)).
    { apply v_tabs. apply lc_tm_tabs. exact Hu2_lc. }
    apply RelSem_of_val; [exact Hv1 | exact Hv2 |].
    cbn [ValSem Sem].
    split; [exact Hv1 | split; [exact Hv2 |]].
    intros A0 Srel HA.
    set (sub' := update_sub sub X A0).
    set (envF' := update_tyenv envF X Srel).
    assert (Hsub' : forall Y, lc_ty_at 0 (sub' Y)).
    { intro Y. unfold sub', update_sub.
      destruct (Nat.eqb Y X) eqn:E.
      - exact HA.
      - apply Hsub. }
    assert (Henv' : forall y U, lookup_context y Gamma = Some U ->
                     RelSem U [] envF' (sigma1 y) (sigma2 y)).
    { intros y U Hlook.
      apply (RelSem_envF_ext U [] envF envF').
      - intros Y HY a b. unfold envF', update_tyenv.
        destruct (Nat.eqb Y X) eqn:E.
        + apply Nat.eqb_eq in E. subst Y.
          exfalso. apply HX_ctx.
          apply (lookup_context_ctx_ty_fv Gamma y U Hlook X HY).
        + reflexivity.
      - apply (Henv y U Hlook). }
    pose proof (H0 X HX_L sub' envF' sigma1 sigma2 Hsub' Hlc1 Hlc2 Henv')
      as Hbody_rel.
    assert (Heq1 : subst_tm_env sigma1
                     (subst_tm_ty_env sub' (open_tm_ty t (Ty_FVar X)))
                   = open_tm_ty u1 A0).
    { unfold open_tm_ty. rewrite (subst_tm_ty_env_open_tm_ty_rec sub' Hsub' 0 X t).
      replace (sub' X) with A0
        by (unfold sub', update_sub; rewrite Nat.eqb_refl; reflexivity).
      erewrite (subst_tm_ty_env_agree sub' sub t).
      - rewrite (subst_tm_env_open_tm_ty_rec sigma1 Hlc1 0 A0
                   (subst_tm_ty_env sub t)).
        unfold u1, open_tm_ty. reflexivity.
      - intros Y HY. unfold sub', update_sub.
        assert (HYX : Y <> X) by (intro Hc; subst Y; apply HX_t; exact HY).
        assert (He : (Y =? X) = false) by (apply Nat.eqb_neq; exact HYX).
        rewrite He. reflexivity. }
    assert (Heq2 : subst_tm_env sigma2
                     (subst_tm_ty_env sub' (open_tm_ty t (Ty_FVar X)))
                   = open_tm_ty u2 A0).
    { unfold open_tm_ty. rewrite (subst_tm_ty_env_open_tm_ty_rec sub' Hsub' 0 X t).
      replace (sub' X) with A0
        by (unfold sub', update_sub; rewrite Nat.eqb_refl; reflexivity).
      erewrite (subst_tm_ty_env_agree sub' sub t).
      - rewrite (subst_tm_env_open_tm_ty_rec sigma2 Hlc2 0 A0
                   (subst_tm_ty_env sub t)).
        unfold u2, open_tm_ty. reflexivity.
      - intros Y HY. unfold sub', update_sub.
        assert (HYX : Y <> X) by (intro Hc; subst Y; apply HX_t; exact HY).
        assert (He : (Y =? X) = false) by (apply Nat.eqb_neq; exact HYX).
        rewrite He. reflexivity. }
    assert (HR1 : RelSem (open_ty T (Ty_FVar X)) [] envF'
                        (open_tm_ty u1 A0) (open_tm_ty u2 A0) <->
                 RelSem T [Srel] envF'
                        (open_tm_ty u1 A0) (open_tm_ty u2 A0)).
    { pose proof (RelSem_open_ty T 0 (Ty_FVar X) [] envF'
                    ltac:(constructor) ltac:(simpl; lia) Hbody_lc_ty) as HIE.
      assert (Hset : set_at_rel 0 (ValSem (Ty_FVar X) [] envF') [] = [Srel]).
      { cbn [set_at_rel ValSem Sem]. unfold envF', update_tyenv.
        rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hset in HIE. exact (HIE (open_tm_ty u1 A0) (open_tm_ty u2 A0)). }
    assert (HR2 : RelSem T [Srel] envF' (open_tm_ty u1 A0) (open_tm_ty u2 A0) <->
                 RelSem T [Srel] envF (open_tm_ty u1 A0) (open_tm_ty u2 A0)).
    { apply RelSem_envF_ext. intros Y HY a b. unfold envF', update_tyenv.
      destruct (Nat.eqb Y X) eqn:E.
      - apply Nat.eqb_eq in E. subst Y.
        exfalso. apply HX_T. exact HY.
      - reflexivity. }
    assert (HR : RelSem (open_ty T (Ty_FVar X)) [] envF'
                        (open_tm_ty u1 A0) (open_tm_ty u2 A0) <->
                 RelSem T [Srel] envF
                        (open_tm_ty u1 A0) (open_tm_ty u2 A0))
      by (eapply iff_trans; eassumption).
    eapply RelSem_multi_l with (t1' := open_tm_ty u1 A0).
    { apply step_multi. eapply ST_TAppTabs.
      - apply lc_tm_tabs. exact Hu1_lc.
      - exact HA. }
    eapply RelSem_multi_r with (t2' := open_tm_ty u2 A0).
    { apply step_multi. eapply ST_TAppTabs.
      - apply lc_tm_tabs. exact Hu2_lc.
      - exact HA. }
    apply (proj1 HR).
    rewrite <- Heq1, <- Heq2. exact Hbody_rel.
  - (* T_TApp *)
    cbn [subst_tm_env subst_tm_ty_env].
    pose proof (IHhas_type sub envF sigma1 sigma2 Hsub Hlc1 Hlc2 Henv) as HR.
    apply RelSem_def in HR. destruct HR as (v1 & v2 & Hv1 & Hv2 & M1 & M2 & HV).
    cbn [ValSem Sem] in HV. destruct HV as (HV1 & HV2 & Hf).
    set (A0 := subst_ty_env sub U).
    assert (HA0 : lc_ty_at 0 A0).
    { unfold A0. apply subst_ty_env_lc with (K := 0);
        [exact Hsub | eapply wf_ty_lc; eassumption]. }
    pose proof (has_type_All_lc _ _ _ _ H) as HT_lc.
    pose proof (wf_ty_lc _ _ H0) as HU_lc.
    pose proof (Hf A0 (ValSem U [] envF) HA0) as HRbody.
    pose proof (RelSem_open_ty T 0 U [] envF HU_lc (Nat.le_0_l 0) HT_lc)
      as HIE.
    assert (HRrel : RelSem (open_ty T U) [] envF
                            (tm_tapp v1 A0) (tm_tapp v2 A0)).
    { apply (proj2 (HIE (tm_tapp v1 A0) (tm_tapp v2 A0))).
      cbn [set_at_rel]. exact HRbody. }
    assert (Mapp1 : tm_tapp (subst_tm_env sigma1 (subst_tm_ty_env sub t)) A0
                    -->* tm_tapp v1 A0).
    { apply multi_tapp; [exact HA0 | exact M1]. }
    assert (Mapp2 : tm_tapp (subst_tm_env sigma2 (subst_tm_ty_env sub t)) A0
                    -->* tm_tapp v2 A0).
    { apply multi_tapp; [exact HA0 | exact M2]. }
    eapply RelSem_multi_l with (t1' := tm_tapp v1 A0).
    { exact Mapp1. }
    eapply RelSem_multi_r with (t2' := tm_tapp v2 A0).
    { exact Mapp2. }
    exact HRrel.
  - (* T_Choice *)
    cbn [subst_tm_env subst_tm_ty_env].
    pose proof (IHhas_type1 sub envF sigma1 sigma2 Hsub Hlc1 Hlc2 Henv) as HR.
    apply RelSem_def in HR. destruct HR as (v1 & v2 & Hv1 & Hv2 & M1 & M2 & HV).
    apply RelSem_def. exists v1, v2.
    split; [exact Hv1 |]. split; [exact Hv2 |]. split.
    + apply multi_choice_l.
      * apply subst_tm_env_lc; [exact Hlc1 |].
        apply subst_tm_ty_env_lc; [exact Hsub | exact (has_type_lc Delta Gamma t1 T H)].
      * apply subst_tm_env_lc; [exact Hlc1 |].
        apply subst_tm_ty_env_lc; [exact Hsub | exact (has_type_lc Delta Gamma t2 T H0)].
      * exact M1.
    + split.
      * apply multi_choice_l.
        -- apply subst_tm_env_lc; [exact Hlc2 |].
           apply subst_tm_ty_env_lc; [exact Hsub | exact (has_type_lc Delta Gamma t1 T H)].
        -- apply subst_tm_env_lc; [exact Hlc2 |].
           apply subst_tm_ty_env_lc; [exact Hsub | exact (has_type_lc Delta Gamma t2 T H0)].
        -- exact M2.
      * exact HV.
Qed.

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t Ht U v HU Hv Hvty.
  assert (Hsub : forall X, lc_ty_at 0 ((fun X => Ty_FVar X) X))
    by (intro X; constructor).
  assert (Hlc : forall x, lc_tm_at 0 0 ((fun x => tm_fvar x) x))
    by (intro x; constructor).
  assert (Henv : forall x U0, lookup_context x empty = Some U0 ->
                RelSem U0 [] (fun _ _ _ => False)
                  ((fun x => tm_fvar x) x) ((fun x => tm_fvar x) x)).
  { intros x U0 Hlook. cbn [lookup_context] in Hlook. discriminate Hlook. }
  pose proof (fundamental [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
    (fun X => Ty_FVar X) (fun _ _ _ => False)
    (fun x => tm_fvar x) (fun x => tm_fvar x)
    Hsub Hlc Hlc Henv) as HR.
  rewrite subst_tm_ty_env_id in HR.
  rewrite subst_tm_env_id in HR.
  apply RelSem_def in HR.
  destruct HR as (v1 & v2 & Hv1 & Hv2 & Mt1 & Mt2 & HV).
  change (value v1 /\ value v2 /\
          forall (A0 : ty) (Srel : RelTy), lc_ty_at 0 A0 ->
            RelSem (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)) (Srel :: [])
              (fun _ _ _ => False) (tm_tapp v1 A0) (tm_tapp v2 A0)) in HV.
  destruct HV as (HV1 & HV2 & Hf).
  pose proof (wf_ty_lc [] U HU) as HU_lc.
  set (S := fun p q : tm => (p -->* v) /\ (q -->* v)).
  pose proof (Hf U S HU_lc) as HR2.
  apply RelSem_def in HR2.
  destruct HR2 as (w1 & w2 & Hw1 & Hw2 & Nt1 & Nt2 & HV2b).
  change (value w1 /\ value w2 /\
          forall a1 a2, value a1 -> value a2 ->
            ValSem (Ty_BVar 0) [S] (fun _ _ _ => False) a1 a2 ->
            RelSem (Ty_BVar 0) [S] (fun _ _ _ => False)
              (tm_app w1 a1) (tm_app w2 a2)) in HV2b.
  destruct HV2b as (HW1 & HW2 & Hf2).
  assert (HSvv : ValSem (Ty_BVar 0) [S] (fun _ _ _ => False) v v).
  { change (S v v). unfold S. split; apply multi_refl. }
  pose proof (Hf2 v v Hv Hv HSvv) as HR3.
  apply RelSem_def in HR3.
  destruct HR3 as (z1 & z2 & Hz1 & Hz2 & P1 & P2 & HV3).
  change (S z1 z2) in HV3.
  unfold S in HV3. destruct HV3 as (Rz1 & Rz2).
  assert (M1' : tm_tapp t U -->* tm_tapp v1 U).
  { apply multi_tapp; [exact HU_lc | exact Mt1]. }
  assert (M2' : tm_app (tm_tapp t U) v -->* tm_app (tm_tapp v1 U) v).
  { apply multi_app_l; [apply value_lc; exact Hv | exact M1']. }
  assert (M3' : tm_app (tm_tapp v1 U) v -->* tm_app w1 v).
  { apply multi_app_l; [apply value_lc; exact Hv | exact Nt1]. }
  eapply multi_trans; [exact M2' |].
  eapply multi_trans; [exact M3' |].
  eapply multi_trans; [exact P1 |].
  exact Rz1.
Qed.

End SystemFParametricityNondeterminismHardTask.
