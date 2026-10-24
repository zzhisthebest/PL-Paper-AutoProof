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


Hint Constructors lc_ty_at lc_tm_at value : core.

(* ============================================================ *)
(* Auxiliary definitions and metatheory for the logical relation *)
(* ============================================================ *)

Definition rel : Type := tm -> tm -> Prop.
Definition bvar_env : Type := nat -> rel.
Definition fvar_env : Type := atom -> rel.
Definition tm_env : Type := atom -> tm.
Definition ty_env : Type := atom -> ty.

Definition extend_b (R : rel) (delta : bvar_env) : bvar_env :=
  fun i => match i with 0 => R | S j => delta j end.

Definition upd_b (k : nat) (R : rel) (delta : bvar_env) : bvar_env :=
  fun i => if Nat.eqb k i then R else delta i.

Definition upd_f (rho : fvar_env) (X : atom) (R : rel) : fvar_env :=
  fun Y => if Nat.eqb Y X then R else rho Y.

Definition upd_ty (sigma : ty_env) (X : atom) (U : ty) : ty_env :=
  fun Y => if Nat.eqb Y X then U else sigma Y.

Definition upd_tm (gamma : tm_env) (x : atom) (u : tm) : tm_env :=
  fun y => if Nat.eqb y x then u else gamma y.

Fixpoint ty_subst_env (sigma : ty_env) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sigma X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst_env sigma T1) (ty_subst_env sigma T2)
  | Ty_All T1 => Ty_All (ty_subst_env sigma T1)
  end.

Fixpoint tm_ty_subst_env (sigma : ty_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst_env sigma T) (tm_ty_subst_env sigma t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst_env sigma t1) (tm_ty_subst_env sigma t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst_env sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst_env sigma t1) (ty_subst_env sigma T)
  | tm_choice t1 t2 => tm_choice (tm_ty_subst_env sigma t1) (tm_ty_subst_env sigma t2)
  end.

Fixpoint tm_subst_env (gamma : tm_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T t1 => tm_abs T (tm_subst_env gamma t1)
  | tm_app t1 t2 => tm_app (tm_subst_env gamma t1) (tm_subst_env gamma t2)
  | tm_tabs t1 => tm_tabs (tm_subst_env gamma t1)
  | tm_tapp t1 T => tm_tapp (tm_subst_env gamma t1) T
  | tm_choice t1 t2 => tm_choice (tm_subst_env gamma t1) (tm_subst_env gamma t2)
  end.

Definition close (sigma : ty_env) (gamma : tm_env) (t : tm) : tm :=
  tm_subst_env gamma (tm_ty_subst_env sigma t).

(* free type variables of a type *)
Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
  end.

(* free type variables occurring in a term's annotations *)
Fixpoint fv_tm_ty (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T t1 => fv_ty T ++ fv_tm_ty t1
  | tm_app t1 t2 => fv_tm_ty t1 ++ fv_tm_ty t2
  | tm_tabs t1 => fv_tm_ty t1
  | tm_tapp t1 T => fv_tm_ty t1 ++ fv_ty T
  | tm_choice t1 t2 => fv_tm_ty t1 ++ fv_tm_ty t2
  end.

(* free term variables of a term *)
Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T t1 => fv_tm t1
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t1 => fv_tm t1
  | tm_tapp t1 T => fv_tm t1
  | tm_choice t1 t2 => fv_tm t1 ++ fv_tm t2
  end.

Definition ctx_fv_ty (Gamma : context) : list atom :=
  flat_map (fun p => fv_ty (snd p)) Gamma.

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (max_list l')
  end.

Lemma max_list_ge : forall l x, In x l -> x <= max_list l.
Proof.
  induction l as [|y l IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto | apply Nat.le_max_r].
Qed.

Definition fresh (l : list atom) : atom := S (max_list l).

Lemma fresh_not_in : forall l, ~ In (fresh l) l.
Proof.
  intros l Hin. unfold fresh in Hin. apply max_list_ge in Hin. lia.
Qed.

Lemma not_in_app : forall (l1 l2 : list atom) x,
  ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros l1 l2 x H; split; intro H'; apply H; apply in_or_app; auto.
Qed.

Lemma eqb_neq : forall a b : nat, a <> b -> Nat.eqb a b = false.
Proof. intros; apply Nat.eqb_neq; auto. Qed.

Lemma eqb_eq_nat : forall a b : nat, a = b -> Nat.eqb a b = true.
Proof. intros; subst; apply Nat.eqb_refl. Qed.

(* ============================================================ *)
(* Locally-closedness lemmas                                    *)
(* ============================================================ *)

Lemma lc_ty_weaken : forall K K' T, K <= K' -> lc_ty_at K T -> lc_ty_at K' T.
Proof.
  intros K K' T Hle H. revert K' Hle.
  induction H; intros K' Hle.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow.
    + apply IHlc_ty_at1. lia.
    + apply IHlc_ty_at2. lia.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
Qed.

Lemma lc_tm_weaken_K : forall K K' k t, K <= K' -> lc_tm_at K k t -> lc_tm_at K' k t.
Proof.
  intros K K' k t Hle H. revert K' Hle.
  induction H; intros K' Hle.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_weaken with (K := K); auto.
    + apply IHlc_tm_at. auto.
  - apply lc_tm_app.
    + apply IHlc_tm_at1. auto.
    + apply IHlc_tm_at2. auto.
  - apply lc_tm_tabs. apply IHlc_tm_at. lia.
  - apply lc_tm_tapp.
    + apply IHlc_tm_at. auto.
    + apply lc_ty_weaken with (K := K); auto.
  - apply lc_tm_choice.
    + apply IHlc_tm_at1. auto.
    + apply IHlc_tm_at2. auto.
Qed.

Lemma lc_tm_weaken_k : forall K k k' t, k <= k' -> lc_tm_at K k t -> lc_tm_at K k' t.
Proof.
  intros K k k' t Hle H. revert k' Hle.
  induction H; intros k' Hle.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + auto.
    + apply IHlc_tm_at. lia.
  - apply lc_tm_app.
    + apply IHlc_tm_at1. auto.
    + apply IHlc_tm_at2. auto.
  - apply lc_tm_tabs. apply IHlc_tm_at. auto.
  - apply lc_tm_tapp.
    + apply IHlc_tm_at. auto.
    + auto.
  - apply lc_tm_choice.
    + apply IHlc_tm_at1. auto.
    + apply IHlc_tm_at2. auto.
Qed.

Lemma lc_tm_weaken : forall K K' k k' t,
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  intros; eapply lc_tm_weaken_k; [eauto | eapply lc_tm_weaken_K; eauto].
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; destruct H; auto. Qed.

(* inversion of typing-openings for locally closed types/terms *)

Lemma open_ty_rec_lc_inv : forall T K U,
  lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH]; intros K U Hlc; simpl in *.
  - destruct (Nat.eqb K i) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar; lia.
    + apply lc_ty_bvar. inversion Hlc; subst; lia.
  - apply lc_ty_fvar.
  - inversion Hlc; subst. apply lc_ty_arrow.
    + apply IH1 with (K := K) (U := U). assumption.
    + apply IH2 with (K := K) (U := U). assumption.
  - inversion Hlc; subst.
    apply lc_ty_all. apply IH with (K := S K) (U := U).
    assumption.
Qed.

Lemma open_ty_rec_lc : forall T K U,
  lc_ty_at (S K) T -> lc_ty_at K U -> lc_ty_at K (open_ty_rec K U T).
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH]; intros K U Hlc HU; simpl in *.
  - destruct (Nat.eqb K i) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact HU.
    + apply Nat.eqb_neq in E. apply lc_ty_bvar. inversion Hlc; subst; lia.
  - apply lc_ty_fvar.
  - inversion Hlc; subst. apply lc_ty_arrow.
    + apply IH1 with (K := K) (U := U); assumption.
    + apply IH2 with (K := K) (U := U); assumption.
  - inversion Hlc; subst. apply lc_ty_all.
    apply IH with (K := S K) (U := U).
    + assumption.
    + apply lc_ty_weaken with (K := K). lia. exact HU.
Qed.

Lemma open_tm_ty_rec_lc_inv : forall t K k U,
  lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros K k U Hlc; simpl in *.
  - inversion Hlc; subst. apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + apply open_ty_rec_lc_inv with (K := K) (U := U); assumption.
    + apply IH1 with (K := K) (U := U); assumption.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply IH1 with (K := K) (U := U); assumption.
    + apply IH2 with (K := K) (U := U); assumption.
  - inversion Hlc; subst. apply lc_tm_tabs.
    apply IH1 with (K := S K) (U := U); assumption.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply IH1 with (K := K) (U := U); assumption.
    + apply open_ty_rec_lc_inv with (K := K) (U := U); assumption.
  - inversion Hlc; subst. apply lc_tm_choice.
    + apply IH1 with (K := K) (U := U); assumption.
    + apply IH2 with (K := K) (U := U); assumption.
Qed.

Lemma open_tm_rec_lc_inv : forall t K k k' u,
  lc_tm_at K k (open_tm_rec k' u t) -> k' < k -> lc_tm_at K k t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros K k k' u Hlc Hlt; simpl in *.
  - destruct (Nat.eqb k' i) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar; auto.
    + inversion Hlc; subst. apply lc_tm_bvar; auto.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + assumption.
    + apply IH1 with (k' := S k') (u := u); auto. lia.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply IH1 with (k' := k') (u := u); auto.
    + apply IH2 with (k' := k') (u := u); auto.
  - inversion Hlc; subst. apply lc_tm_tabs.
    apply IH1 with (k' := k') (u := u); auto.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply IH1 with (k' := k') (u := u); auto.
    + assumption.
  - inversion Hlc; subst. apply lc_tm_choice.
    + apply IH1 with (k' := k') (u := u); auto.
    + apply IH2 with (k' := k') (u := u); auto.
Qed.

(* absorption: opening a closed term/type does nothing *)

Lemma open_ty_rec_absorb : forall T K k' U,
  lc_ty_at K T -> K <= k' -> open_ty_rec k' U T = T.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH]; intros K k' U Hlc Hle; simpl in *.
  - destruct (Nat.eqb k' i) eqn:E.
    + apply Nat.eqb_eq in E. subst. inversion Hlc; lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    rewrite IH1 with (K := K) (k' := k') (U := U); auto.
    rewrite IH2 with (K := K) (k' := k') (U := U); auto.
  - inversion Hlc; subst.
    rewrite IH with (K := S K) (k' := S k') (U := U); auto. lia.
Qed.

Lemma open_tm_ty_rec_absorb : forall t K k k' U,
  lc_tm_at K k t -> K <= k' -> open_tm_ty_rec k' U t = t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros K k k' U Hlc Hle; simpl in *.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    rewrite open_ty_rec_absorb with (K := K) (k' := k') (U := U); auto.
    rewrite IH1 with (K := K) (k := S k) (k' := k') (U := U); auto.
  - inversion Hlc; subst.
    rewrite IH1 with (K := K) (k := k) (k' := k') (U := U); auto.
    rewrite IH2 with (K := K) (k := k) (k' := k') (U := U); auto.
  - inversion Hlc; subst.
    rewrite IH1 with (K := S K) (k := k) (k' := S k') (U := U); auto. lia.
  - inversion Hlc; subst.
    rewrite IH1 with (K := K) (k := k) (k' := k') (U := U); auto.
    rewrite open_ty_rec_absorb with (K := K) (k' := k') (U := U); auto.
  - inversion Hlc; subst.
    rewrite IH1 with (K := K) (k := k) (k' := k') (U := U); auto.
    rewrite IH2 with (K := K) (k := k) (k' := k') (U := U); auto.
Qed.

Lemma open_tm_rec_lc : forall t K k,
  lc_tm_at K k t -> forall k' u, k <= k' -> open_tm_rec k' u t = t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros K k Hlc k' u Hle; simpl in *.
  - destruct (Nat.eqb k' i) eqn:E.
    + apply Nat.eqb_eq in E. subst. inversion Hlc; lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    rewrite IH1 with (K := K) (k := S k) (k' := S k') (u := u); auto. lia.
  - inversion Hlc; subst.
    rewrite IH1 with (K := K) (k := k) (k' := k') (u := u); auto.
    rewrite IH2 with (K := K) (k := k) (k' := k') (u := u); auto.
  - inversion Hlc; subst.
    rewrite IH1 with (K := S K) (k := k) (k' := k') (u := u); auto.
  - inversion Hlc; subst.
    rewrite IH1 with (K := K) (k := k) (k' := k') (u := u); auto.
  - inversion Hlc; subst.
    rewrite IH1 with (K := K) (k := k) (k' := k') (u := u); auto.
    rewrite IH2 with (K := K) (k := k) (k' := k') (u := u); auto.
Qed.

(* substitution preserves locally-closedness of types *)

Lemma ty_subst_env_lc : forall T K sigma,
  lc_ty_at K T -> (forall X, lc_ty_at K (sigma X)) ->
  lc_ty_at K (ty_subst_env sigma T).
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH]; intros K sigma Hlc Hs; simpl in *.
  - apply lc_ty_bvar. inversion Hlc; lia.
  - apply Hs.
  - inversion Hlc; subst. apply lc_ty_arrow.
    + apply IH1 with (K := K); assumption.
    + apply IH2 with (K := K); assumption.
  - inversion Hlc; subst. apply lc_ty_all.
    apply IH with (K := S K); auto.
    intros X; apply lc_ty_weaken with (K := K); [lia | apply Hs].
Qed.

(* ============================================================ *)
(* Commutation and agreement lemmas for substitutions           *)
(* ============================================================ *)

Lemma ty_subst_env_open_ty : forall T sigma k U,
  (forall X, lc_ty_at 0 (sigma X)) ->
  ty_subst_env sigma (open_ty_rec k U T) =
  open_ty_rec k (ty_subst_env sigma U) (ty_subst_env sigma T).
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH]; intros sigma k U Hsigma; simpl in *.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply open_ty_rec_absorb with (K := 0) (k' := k); auto. lia.
  - rewrite (IH1 sigma k U Hsigma). rewrite (IH2 sigma k U Hsigma). reflexivity.
  - rewrite (IH sigma (S k) U Hsigma). reflexivity.
Qed.

Lemma tm_ty_subst_env_open_tm : forall t sigma k u,
  tm_ty_subst_env sigma (open_tm_rec k u t) =
  open_tm_rec k (tm_ty_subst_env sigma u) (tm_ty_subst_env sigma t).
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros sigma k u; simpl in *.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - rewrite (IH1 sigma (S k) u); reflexivity.
  - rewrite (IH1 sigma k u), (IH2 sigma k u); reflexivity.
  - rewrite (IH1 sigma k u); reflexivity.
  - rewrite (IH1 sigma k u); reflexivity.
  - rewrite (IH1 sigma k u), (IH2 sigma k u); reflexivity.
Qed.

Lemma tm_subst_env_open_tm : forall t gamma k x,
  (forall y, locally_closed_tm (gamma y)) ->
  tm_subst_env gamma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (gamma x) (tm_subst_env gamma t).
Proof.
  induction t as [i|y|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros gamma k x Hlc; simpl in *.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply open_tm_rec_lc with (K := 0) (k := 0) (k' := k). apply Hlc. lia.
  - rewrite (IH1 gamma (S k) x Hlc); reflexivity.
  - rewrite (IH1 gamma k x Hlc), (IH2 gamma k x Hlc); reflexivity.
  - rewrite (IH1 gamma k x Hlc); reflexivity.
  - rewrite (IH1 gamma k x Hlc); reflexivity.
  - rewrite (IH1 gamma k x Hlc), (IH2 gamma k x Hlc); reflexivity.
Qed.

Lemma tm_ty_subst_env_open_tm_ty : forall t sigma k U,
  (forall X, lc_ty_at 0 (sigma X)) ->
  tm_ty_subst_env sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_subst_env sigma U) (tm_ty_subst_env sigma t).
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros sigma k U Hsigma; simpl in *.
  - reflexivity.
  - reflexivity.
  - rewrite (IH1 sigma k U Hsigma).
    rewrite (ty_subst_env_open_ty T sigma k U Hsigma). reflexivity.
  - rewrite (IH1 sigma k U Hsigma), (IH2 sigma k U Hsigma). reflexivity.
  - rewrite (IH1 sigma (S k) U Hsigma). reflexivity.
  - rewrite (IH1 sigma k U Hsigma).
    rewrite (ty_subst_env_open_ty T sigma k U Hsigma). reflexivity.
  - rewrite (IH1 sigma k U Hsigma), (IH2 sigma k U Hsigma). reflexivity.
Qed.

Lemma tm_subst_env_open_tm_ty : forall t gamma k U,
  (forall y, locally_closed_tm (gamma y)) ->
  tm_subst_env gamma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (tm_subst_env gamma t).
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros gamma k U Hlc; simpl in *.
  - reflexivity.
  - symmetry. apply open_tm_ty_rec_absorb with (K := 0) (k := 0) (k' := k). apply Hlc. lia.
  - rewrite (IH1 gamma k U Hlc); reflexivity.
  - rewrite (IH1 gamma k U Hlc), (IH2 gamma k U Hlc); reflexivity.
  - rewrite (IH1 gamma (S k) U Hlc); reflexivity.
  - rewrite (IH1 gamma k U Hlc); reflexivity.
  - rewrite (IH1 gamma k U Hlc), (IH2 gamma k U Hlc); reflexivity.
Qed.

Lemma ty_subst_env_agree : forall T sigma1 sigma2,
  (forall X, In X (fv_ty T) -> sigma1 X = sigma2 X) ->
  ty_subst_env sigma1 T = ty_subst_env sigma2 T.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH]; intros sigma1 sigma2 Hagree; simpl in *.
  - reflexivity.
  - apply Hagree. simpl. auto.
  - assert (H1 : forall X, In X (fv_ty T1) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hagree. apply in_or_app. auto. }
    assert (H2 : forall X, In X (fv_ty T2) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hagree. apply in_or_app. auto. }
    rewrite (IH1 sigma1 sigma2 H1). rewrite (IH2 sigma1 sigma2 H2). reflexivity.
  - assert (H1 : forall X, In X (fv_ty T') -> sigma1 X = sigma2 X).
    { intros X HX. apply Hagree. simpl. exact HX. }
    rewrite (IH sigma1 sigma2 H1). reflexivity.
Qed.

Lemma tm_ty_subst_env_agree : forall t sigma1 sigma2,
  (forall X, In X (fv_tm_ty t) -> sigma1 X = sigma2 X) ->
  tm_ty_subst_env sigma1 t = tm_ty_subst_env sigma2 t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros sigma1 sigma2 Hagree; simpl in *.
  - reflexivity.
  - reflexivity.
  - assert (H1 : forall X, In X (fv_tm_ty t1) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hagree. simpl. apply in_or_app. auto. }
    assert (H2 : forall X, In X (fv_ty T) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hagree. simpl. apply in_or_app. auto. }
    rewrite (IH1 sigma1 sigma2 H1). rewrite (ty_subst_env_agree T sigma1 sigma2 H2). reflexivity.
  - assert (H1 : forall X, In X (fv_tm_ty t1) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hagree. simpl. apply in_or_app. auto. }
    assert (H2 : forall X, In X (fv_tm_ty t2) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hagree. simpl. apply in_or_app. auto. }
    rewrite (IH1 sigma1 sigma2 H1). rewrite (IH2 sigma1 sigma2 H2). reflexivity.
  - assert (H1 : forall X, In X (fv_tm_ty t1) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hagree. simpl. exact HX. }
    rewrite (IH1 sigma1 sigma2 H1). reflexivity.
  - assert (H1 : forall X, In X (fv_tm_ty t1) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hagree. simpl. apply in_or_app. auto. }
    assert (H2 : forall X, In X (fv_ty T) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hagree. simpl. apply in_or_app. auto. }
    rewrite (IH1 sigma1 sigma2 H1). rewrite (ty_subst_env_agree T sigma1 sigma2 H2). reflexivity.
  - assert (H1 : forall X, In X (fv_tm_ty t1) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hagree. simpl. apply in_or_app. auto. }
    assert (H2 : forall X, In X (fv_tm_ty t2) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hagree. simpl. apply in_or_app. auto. }
    rewrite (IH1 sigma1 sigma2 H1). rewrite (IH2 sigma1 sigma2 H2). reflexivity.
Qed.

Lemma tm_subst_env_agree : forall t gamma1 gamma2,
  (forall x, In x (fv_tm t) -> gamma1 x = gamma2 x) ->
  tm_subst_env gamma1 t = tm_subst_env gamma2 t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros gamma1 gamma2 Hagree; simpl in *.
  - reflexivity.
  - apply Hagree. simpl. auto.
  - assert (H1 : forall x, In x (fv_tm t1) -> gamma1 x = gamma2 x).
    { intros y HY. apply Hagree. simpl. exact HY. }
    rewrite (IH1 gamma1 gamma2 H1). reflexivity.
  - assert (H1 : forall x, In x (fv_tm t1) -> gamma1 x = gamma2 x).
    { intros y HY. apply Hagree. simpl. apply in_or_app. auto. }
    assert (H2 : forall x, In x (fv_tm t2) -> gamma1 x = gamma2 x).
    { intros y HY. apply Hagree. simpl. apply in_or_app. auto. }
    rewrite (IH1 gamma1 gamma2 H1). rewrite (IH2 gamma1 gamma2 H2). reflexivity.
  - assert (H1 : forall x, In x (fv_tm t1) -> gamma1 x = gamma2 x).
    { intros y HY. apply Hagree. simpl. exact HY. }
    rewrite (IH1 gamma1 gamma2 H1). reflexivity.
  - assert (H1 : forall x, In x (fv_tm t1) -> gamma1 x = gamma2 x).
    { intros y HY. apply Hagree. simpl. exact HY. }
    rewrite (IH1 gamma1 gamma2 H1). reflexivity.
  - assert (H1 : forall x, In x (fv_tm t1) -> gamma1 x = gamma2 x).
    { intros y HY. apply Hagree. simpl. apply in_or_app. auto. }
    assert (H2 : forall x, In x (fv_tm t2) -> gamma1 x = gamma2 x).
    { intros y HY. apply Hagree. simpl. apply in_or_app. auto. }
    rewrite (IH1 gamma1 gamma2 H1). rewrite (IH2 gamma1 gamma2 H2). reflexivity.
Qed.

Lemma fv_tm_ty_subst_env : forall t sigma,
  fv_tm (tm_ty_subst_env sigma t) = fv_tm t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros sigma; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma upd_ty_agree : forall sigma X U,
  (forall Y, Y <> X -> upd_ty sigma X U Y = sigma Y) /\
  upd_ty sigma X U X = U.
Proof.
  intros; split.
  - intros Y Hne. unfold upd_ty. rewrite eqb_neq; auto.
  - unfold upd_ty. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma upd_tm_agree : forall gamma x u,
  (forall y, y <> x -> upd_tm gamma x u y = gamma y) /\
  upd_tm gamma x u x = u.
Proof.
  intros; split.
  - intros y Hne. unfold upd_tm. rewrite eqb_neq; auto.
  - unfold upd_tm. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma upd_f_agree : forall rho X R,
  (forall Y, Y <> X -> forall a b, upd_f rho X R Y a b <-> rho Y a b) /\
  (forall a b, upd_f rho X R X a b <-> R a b).
Proof.
  intros; split.
  - intros Y Hne a b. unfold upd_f. rewrite (eqb_neq Y X Hne). reflexivity.
  - intros a b. unfold upd_f. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma upd_ty_self : forall sigma X U, upd_ty sigma X U X = U.
Proof. intros. exact (proj2 (upd_ty_agree sigma X U)). Qed.

Lemma upd_ty_other : forall sigma X U Y, Y <> X -> upd_ty sigma X U Y = sigma Y.
Proof. intros. exact (proj1 (upd_ty_agree sigma X U) Y H). Qed.

Lemma upd_tm_self : forall gamma x u, upd_tm gamma x u x = u.
Proof. intros. exact (proj2 (upd_tm_agree gamma x u)). Qed.

Lemma upd_tm_other : forall gamma x u y, y <> x -> upd_tm gamma x u y = gamma y.
Proof. intros. exact (proj1 (upd_tm_agree gamma x u) y H). Qed.

Lemma upd_f_self : forall rho X R a b, upd_f rho X R X a b <-> R a b.
Proof. intros. exact (proj2 (upd_f_agree rho X R) a b). Qed.

Lemma upd_f_other : forall rho X R Y a b, Y <> X -> (upd_f rho X R Y a b <-> rho Y a b).
Proof. intros. exact (proj1 (upd_f_agree rho X R) Y H a b). Qed.

(* ============================================================ *)
(* The binary logical relation                                  *)
(* ============================================================ *)

Fixpoint V (T : ty) (delta : bvar_env) (rho : fvar_env) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_BVar i => delta i v1 v2
  | Ty_FVar X => rho X v1 v2
  | Ty_Arrow T1 T2 =>
      value v1 /\ value v2 /\
      (exists T1' b1, v1 = tm_abs T1' b1) /\
      (exists T2' b2, v2 = tm_abs T2' b2) /\
      (forall a1 a2, V T1 delta rho a1 a2 ->
         exists w1 w2,
           tm_app v1 a1 -->* w1 /\
           tm_app v2 a2 -->* w2 /\
           V T2 delta rho w1 w2)
  | Ty_All T' =>
      value v1 /\ value v2 /\
      (exists s1 s2,
         v1 = tm_tabs s1 /\ v2 = tm_tabs s2 /\
         forall U1 U2,
           lc_ty_at 0 U1 -> lc_ty_at 0 U2 ->
           forall R, (forall x1 x2, R x1 x2 -> value x1 /\ value x2) ->
             exists w1 w2,
               open_tm_ty s1 U1 -->* w1 /\
               open_tm_ty s2 U2 -->* w2 /\
               V T' (extend_b R delta) rho w1 w2)
  end.

Definition C (T : ty) (delta : bvar_env) (rho : fvar_env) (t1 t2 : tm) : Prop :=
  exists v1 v2, t1 -->* v1 /\ t2 -->* v2 /\ V T delta rho v1 v2.

Lemma V_delta_iff : forall T (delta1 delta2 : bvar_env) (rho : fvar_env) v1 v2,
  (forall i x1 x2, delta1 i x1 x2 <-> delta2 i x1 x2) ->
  V T delta1 rho v1 v2 <-> V T delta2 rho v1 v2.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH];
    intros delta1 delta2 rho v1 v2 Hagree; simpl.
  - apply Hagree.
  - reflexivity.
  - assert (E1 : forall a1 a2, V T1 delta1 rho a1 a2 <-> V T1 delta2 rho a1 a2).
    { intros; apply IH1; auto. }
    assert (E2 : forall w1 w2, V T2 delta1 rho w1 w2 <-> V T2 delta2 rho w1 w2).
    { intros; apply IH2; auto. }
    split.
    + intros (Hv1 & Hv2 & Hsh1 & Hsh2 & Hf). repeat split; auto.
      intros a1 a2 Ha. apply (proj2 (E1 a1 a2)) in Ha.
      destruct (Hf a1 a2 Ha) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj1 (E2 w1 w2) HB).
    + intros (Hv1 & Hv2 & Hsh1 & Hsh2 & Hf). repeat split; auto.
      intros a1 a2 Ha. apply (proj1 (E1 a1 a2)) in Ha.
      destruct (Hf a1 a2 Ha) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj2 (E2 w1 w2) HB).
  - assert (Hagree' : forall R i x1 x2,
      extend_b R delta1 i x1 x2 <-> extend_b R delta2 i x1 x2).
    { intros R [|j] x1 x2; simpl; [reflexivity | apply Hagree]. }
    assert (E : forall R w1 w2,
      V T' (extend_b R delta1) rho w1 w2 <-> V T' (extend_b R delta2) rho w1 w2).
    { intros; apply IH; auto. }
    split.
    + intros (Hv1 & Hv2 & s1 & s2 & Hs1 & Hs2 & Hf). repeat split; auto.
      exists s1, s2. repeat split; auto.
      intros U1 U2 Hl1 Hl2 R HR.
      destruct (Hf U1 U2 Hl1 Hl2 R HR) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj1 (E R w1 w2) HB).
    + intros (Hv1 & Hv2 & s1 & s2 & Hs1 & Hs2 & Hf). repeat split; auto.
      exists s1, s2. repeat split; auto.
      intros U1 U2 Hl1 Hl2 R HR.
      destruct (Hf U1 U2 Hl1 Hl2 R HR) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj2 (E R w1 w2) HB).
Qed.

Lemma V_rho_iff : forall T (delta : bvar_env) (rho1 rho2 : fvar_env) v1 v2,
  (forall X x1 x2, rho1 X x1 x2 <-> rho2 X x1 x2) ->
  V T delta rho1 v1 v2 <-> V T delta rho2 v1 v2.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH];
    intros delta rho1 rho2 v1 v2 Hagree; simpl.
  - reflexivity.
  - apply Hagree.
  - assert (E1 : forall a1 a2, V T1 delta rho1 a1 a2 <-> V T1 delta rho2 a1 a2).
    { intros; apply IH1; auto. }
    assert (E2 : forall w1 w2, V T2 delta rho1 w1 w2 <-> V T2 delta rho2 w1 w2).
    { intros; apply IH2; auto. }
    split.
    + intros (Hv1 & Hv2 & Hsh1 & Hsh2 & Hf). repeat split; auto.
      intros a1 a2 Ha. apply (proj2 (E1 a1 a2)) in Ha.
      destruct (Hf a1 a2 Ha) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj1 (E2 w1 w2) HB).
    + intros (Hv1 & Hv2 & Hsh1 & Hsh2 & Hf). repeat split; auto.
      intros a1 a2 Ha. apply (proj1 (E1 a1 a2)) in Ha.
      destruct (Hf a1 a2 Ha) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj2 (E2 w1 w2) HB).
  - assert (E : forall R w1 w2,
      V T' (extend_b R delta) rho1 w1 w2 <-> V T' (extend_b R delta) rho2 w1 w2).
    { intros; apply IH; auto. }
    split.
    + intros (Hv1 & Hv2 & s1 & s2 & Hs1 & Hs2 & Hf). repeat split; auto.
      exists s1, s2. repeat split; auto.
      intros U1 U2 Hl1 Hl2 R HR.
      destruct (Hf U1 U2 Hl1 Hl2 R HR) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj1 (E R w1 w2) HB).
    + intros (Hv1 & Hv2 & s1 & s2 & Hs1 & Hs2 & Hf). repeat split; auto.
      exists s1, s2. repeat split; auto.
      intros U1 U2 Hl1 Hl2 R HR.
      destruct (Hf U1 U2 Hl1 Hl2 R HR) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj2 (E R w1 w2) HB).
Qed.

Lemma V_delta_indep : forall T K (delta1 delta2 : bvar_env) (rho : fvar_env) v1 v2,
  lc_ty_at K T ->
  (forall i, i < K -> forall x1 x2, delta1 i x1 x2 <-> delta2 i x1 x2) ->
  V T delta1 rho v1 v2 <-> V T delta2 rho v1 v2.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH];
    intros K delta1 delta2 rho v1 v2 Hlc Hagree; simpl.
  - inversion Hlc; subst. apply Hagree; auto.
  - reflexivity.
  - inversion Hlc; subst.
    assert (E1 : forall a1 a2, V T1 delta1 rho a1 a2 <-> V T1 delta2 rho a1 a2).
    { intros; apply IH1 with (K := K); auto. }
    assert (E2 : forall w1 w2, V T2 delta1 rho w1 w2 <-> V T2 delta2 rho w1 w2).
    { intros; apply IH2 with (K := K); auto. }
    split.
    + intros (Hv1 & Hv2 & Hsh1 & Hsh2 & Hf). repeat split; auto.
      intros a1 a2 Ha. apply (proj2 (E1 a1 a2)) in Ha.
      destruct (Hf a1 a2 Ha) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj1 (E2 w1 w2) HB).
    + intros (Hv1 & Hv2 & Hsh1 & Hsh2 & Hf). repeat split; auto.
      intros a1 a2 Ha. apply (proj1 (E1 a1 a2)) in Ha.
      destruct (Hf a1 a2 Ha) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj2 (E2 w1 w2) HB).
  - inversion Hlc; subst.
    assert (E : forall R w1 w2,
      V T' (extend_b R delta1) rho w1 w2 <-> V T' (extend_b R delta2) rho w1 w2).
    { intros R w1 w2. apply IH with (K := S K).
      - assumption.
      - intros i Hi x1 x2. destruct i as [|j]; simpl.
        + reflexivity.
        + apply Hagree. lia. }
    split.
    + intros (Hv1 & Hv2 & s1 & s2 & Hs1 & Hs2 & Hf). repeat split; auto.
      exists s1, s2. repeat split; auto.
      intros U1 U2 Hl1 Hl2 R HR.
      destruct (Hf U1 U2 Hl1 Hl2 R HR) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj1 (E R w1 w2) HB).
    + intros (Hv1 & Hv2 & s1 & s2 & Hs1 & Hs2 & Hf). repeat split; auto.
      exists s1, s2. repeat split; auto.
      intros U1 U2 Hl1 Hl2 R HR.
      destruct (Hf U1 U2 Hl1 Hl2 R HR) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj2 (E R w1 w2) HB).
Qed.

Lemma V_rho_indep : forall T (delta : bvar_env) (rho1 rho2 : fvar_env) v1 v2,
  (forall X, In X (fv_ty T) -> forall x1 x2, rho1 X x1 x2 <-> rho2 X x1 x2) ->
  V T delta rho1 v1 v2 <-> V T delta rho2 v1 v2.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH];
    intros delta rho1 rho2 v1 v2 Hagree; simpl.
  - reflexivity.
  - apply Hagree. simpl. auto.
  - assert (E1 : forall a1 a2, V T1 delta rho1 a1 a2 <-> V T1 delta rho2 a1 a2).
    { intros. apply IH1. intros X HX. apply Hagree. simpl. apply in_or_app. auto. }
    assert (E2 : forall w1 w2, V T2 delta rho1 w1 w2 <-> V T2 delta rho2 w1 w2).
    { intros. apply IH2. intros X HX. apply Hagree. simpl. apply in_or_app. auto. }
    split.
    + intros (Hv1 & Hv2 & Hsh1 & Hsh2 & Hf). repeat split; auto.
      intros a1 a2 Ha. apply (proj2 (E1 a1 a2)) in Ha.
      destruct (Hf a1 a2 Ha) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj1 (E2 w1 w2) HB).
    + intros (Hv1 & Hv2 & Hsh1 & Hsh2 & Hf). repeat split; auto.
      intros a1 a2 Ha. apply (proj1 (E1 a1 a2)) in Ha.
      destruct (Hf a1 a2 Ha) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj2 (E2 w1 w2) HB).
  - assert (E : forall R w1 w2,
      V T' (extend_b R delta) rho1 w1 w2 <-> V T' (extend_b R delta) rho2 w1 w2).
    { intros. apply IH. intros X HX. apply Hagree. simpl. exact HX. }
    split.
    + intros (Hv1 & Hv2 & s1 & s2 & Hs1 & Hs2 & Hf). repeat split; auto.
      exists s1, s2. repeat split; auto.
      intros U1 U2 Hl1 Hl2 R HR.
      destruct (Hf U1 U2 Hl1 Hl2 R HR) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj1 (E R w1 w2) HB).
    + intros (Hv1 & Hv2 & s1 & s2 & Hs1 & Hs2 & Hf). repeat split; auto.
      exists s1, s2. repeat split; auto.
      intros U1 U2 Hl1 Hl2 R HR.
      destruct (Hf U1 U2 Hl1 Hl2 R HR) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj2 (E R w1 w2) HB).
Qed.

Lemma V_rho_upd_fresh : forall T (delta : bvar_env) (rho : fvar_env) X R v1 v2,
  ~ In X (fv_ty T) ->
  (V T delta (upd_f rho X R) v1 v2 <-> V T delta rho v1 v2).
Proof.
  intros. apply V_rho_indep.
  intros Y HY a b. assert (Hne : Y <> X).
  { intro Heq. subst. apply H. exact HY. }
  exact (proj1 (upd_f_agree rho X R) Y Hne a b).
Qed.

Lemma V_value : forall T (delta : bvar_env) (rho : fvar_env) v1 v2,
  (forall i x1 x2, delta i x1 x2 -> value x1 /\ value x2) ->
  (forall X x1 x2, rho X x1 x2 -> value x1 /\ value x2) ->
  V T delta rho v1 v2 -> value v1 /\ value v2.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH];
    intros delta rho v1 v2 Hd Hr HV; simpl in *.
  - apply Hd with (i := i); auto.
  - apply Hr with (X := X); auto.
  - destruct HV as (Hv1 & Hv2 & _). auto.
  - destruct HV as (Hv1 & Hv2 & _). auto.
Qed.

Lemma V_open_ty_rec : forall T k U (delta : bvar_env) (rho : fvar_env) v1 v2,
  lc_ty_at 0 U ->
  (V (open_ty_rec k U T) delta rho v1 v2 <->
   V T (upd_b k (V U delta rho) delta) rho v1 v2).
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH];
    intros k U delta rho v1 v2 Hlc; simpl.
  - unfold upd_b. simpl. destruct (Nat.eqb k i) eqn:E; simpl; reflexivity.
  - reflexivity.
  - assert (E1 : forall a1 a2,
      V (open_ty_rec k U T1) delta rho a1 a2 <->
      V T1 (upd_b k (V U delta rho) delta) rho a1 a2).
    { intros; apply IH1; auto. }
    assert (E2 : forall w1 w2,
      V (open_ty_rec k U T2) delta rho w1 w2 <->
      V T2 (upd_b k (V U delta rho) delta) rho w1 w2).
    { intros; apply IH2; auto. }
    split.
    + intros (Hv1 & Hv2 & Hsh1 & Hsh2 & Hf). repeat split; auto.
      intros a1 a2 Ha. apply (proj2 (E1 a1 a2)) in Ha.
      destruct (Hf a1 a2 Ha) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj1 (E2 w1 w2) HB).
    + intros (Hv1 & Hv2 & Hsh1 & Hsh2 & Hf). repeat split; auto.
      intros a1 a2 Ha. apply (proj1 (E1 a1 a2)) in Ha.
      destruct (Hf a1 a2 Ha) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj2 (E2 w1 w2) HB).
  - assert (Ebody : forall R w1 w2,
      V (open_ty_rec (S k) U T') (extend_b R delta) rho w1 w2 <->
      V T' (extend_b R (upd_b k (V U delta rho) delta)) rho w1 w2).
    { intros R w1 w2.
      assert (Hpt : forall i a b,
        upd_b (S k) (V U (extend_b R delta) rho) (extend_b R delta) i a b <->
        extend_b R (upd_b k (V U delta rho) delta) i a b).
      { intros [|j] a b; simpl.
        - reflexivity.
        - destruct (Nat.eqb k j) eqn:E.
          + unfold upd_b. simpl. rewrite E. simpl.
            apply V_delta_indep with (K := 0).
            * exact Hlc.
            * intros i Hi; lia.
          + unfold upd_b. simpl. rewrite E. simpl. reflexivity. }
      etransitivity.
      + apply IH; auto.
      + apply V_delta_iff; auto. }
    split.
    + intros (Hv1 & Hv2 & s1 & s2 & Hs1 & Hs2 & Hf). repeat split; auto.
      exists s1, s2. repeat split; auto.
      intros U1 U2 Hl1 Hl2 R HR.
      destruct (Hf U1 U2 Hl1 Hl2 R HR) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj1 (Ebody R w1 w2) HB).
    + intros (Hv1 & Hv2 & s1 & s2 & Hs1 & Hs2 & Hf). repeat split; auto.
      exists s1, s2. repeat split; auto.
      intros U1 U2 Hl1 Hl2 R HR.
      destruct (Hf U1 U2 Hl1 Hl2 R HR) as (w1 & w2 & Hr1 & Hr2 & HB).
      exists w1, w2. repeat split; auto. exact (proj2 (Ebody R w1 w2) HB).
Qed.

Lemma V_extend_upd0 : forall T (delta : bvar_env) (rho : fvar_env) R v1 v2,
  lc_ty_at 1 T ->
  (V T (upd_b 0 R delta) rho v1 v2 <-> V T (extend_b R delta) rho v1 v2).
Proof.
  intros. apply V_delta_indep with (K := 1); auto.
  intros i Hi x1 x2. destruct i as [|j]; simpl.
  - reflexivity.
  - lia.
Qed.

Lemma C_rho_indep : forall T (delta : bvar_env) (rho1 rho2 : fvar_env) t1 t2,
  (forall X, In X (fv_ty T) -> forall x1 x2, rho1 X x1 x2 <-> rho2 X x1 x2) ->
  C T delta rho1 t1 t2 <-> C T delta rho2 t1 t2.
Proof.
  intros. unfold C. split.
  - intros (v1 & v2 & H1 & H2 & HV). exists v1, v2. repeat split; auto.
    exact (proj1 (V_rho_indep T delta rho1 rho2 v1 v2 H) HV).
  - intros (v1 & v2 & H1 & H2 & HV). exists v1, v2. repeat split; auto.
    exact (proj2 (V_rho_indep T delta rho1 rho2 v1 v2 H) HV).
Qed.

Lemma C_rho_upd_fresh : forall T (delta : bvar_env) (rho : fvar_env) X R t1 t2,
  ~ In X (fv_ty T) ->
  (C T delta (upd_f rho X R) t1 t2 <-> C T delta rho t1 t2).
Proof.
  intros. apply C_rho_indep.
  intros Y HY a b. assert (Hne : Y <> X).
  { intro Heq. subst. apply H. exact HY. }
  exact (proj1 (upd_f_agree rho X R) Y Hne a b).
Qed.

Lemma C_of_V : forall T (delta : bvar_env) (rho : fvar_env) v1 v2,
  V T delta rho v1 v2 -> C T delta rho v1 v2.
Proof.
  intros. exists v1, v2. split; [apply multi_refl | split; [apply multi_refl | assumption]].
Qed.

(* ============================================================ *)
(* Multi-step lemmas                                            *)
(* ============================================================ *)

Lemma multi_trans : forall x y z, x -->* y -> y -->* z -> x -->* z.
Proof.
  intros x y z H. induction H; intros Hz.
  - exact Hz.
  - apply multi_step with y; auto.
Qed.

Lemma multi_app_l : forall t1 t1' t2,
  t1 -->* t1' -> locally_closed_tm t2 -> tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 H. induction H; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (tm_app y t2).
    + apply ST_App1; assumption.
    + apply IHmulti; assumption.
Qed.

Lemma multi_app_r : forall v1 t2 t2',
  value v1 -> t2 -->* t2' -> tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv H. induction H.
  - apply multi_refl.
  - apply multi_step with (tm_app v1 y).
    + apply ST_App2; assumption.
    + apply IHmulti.
Qed.

Lemma multi_tapp : forall t t' U,
  t -->* t' -> locally_closed_ty U -> tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H. induction H; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (tm_tapp y U).
    + apply ST_TApp; assumption.
    + apply IHmulti; assumption.
Qed.

Lemma step_multi : forall t t', t --> t' -> t -->* t'.
Proof. intros; apply multi_step with t'; auto; apply multi_refl. Qed.

(* ============================================================ *)
(* Well-formed types are bvar-free; typed terms substitute to   *)
(* locally closed terms.                                        *)
(* ============================================================ *)

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    pose (X := fresh L).
    assert (HX : ~ In X L) by apply fresh_not_in.
    apply open_ty_rec_lc_inv with (K := 0) (U := Ty_FVar X).
    change (lc_ty_at 0 (open_ty T (Ty_FVar X))).
    apply (H0 X HX).
Qed.

Lemma ctx_lc_extend : forall Gamma x T,
  (forall y Ty, lookup_context y Gamma = Some Ty -> lc_ty_at 0 Ty) ->
  lc_ty_at 0 T ->
  (forall y Ty, lookup_context y (update Gamma x T) = Some Ty -> lc_ty_at 0 Ty).
Proof.
  intros Gamma x T Hctx HT y Ty Hy.
  unfold update in Hy.
  destruct (Nat.eqb y x) eqn:E; simpl in Hy.
  - apply Nat.eqb_eq in E. subst. rewrite Nat.eqb_refl in Hy. inversion Hy. subst. exact HT.
  - rewrite E in Hy. simpl in Hy. apply (Hctx y Ty Hy).
Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  (forall x Tx, lookup_context x Gamma = Some Tx -> lc_ty_at 0 Tx) ->
  lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H. induction H; intros Hctx.
  - apply (Hctx x T H).
  - apply lc_ty_arrow.
    + eapply wf_ty_lc; eassumption.
    + pose (x := fresh L).
      assert (Hx : ~ In x L) by apply fresh_not_in.
      apply (H1 x Hx).
      apply ctx_lc_extend.
      * assumption.
      * eapply wf_ty_lc; eassumption.
  - pose proof (IHhas_type1 Hctx) as Hl. inversion Hl; subst. assumption.
  - apply lc_ty_all.
    pose (X := fresh L).
    assert (HX : ~ In X L) by apply fresh_not_in.
    apply open_ty_rec_lc_inv with (K := 0) (U := Ty_FVar X).
    change (lc_ty_at 0 (open_ty T (Ty_FVar X))).
    apply (H0 X HX Hctx).
  - pose proof (IHhas_type Hctx) as Hl. inversion Hl; subst.
    apply open_ty_rec_lc with (K := 0).
    + assumption.
    + eapply wf_ty_lc; eassumption.
  - apply IHhas_type1. assumption.
Qed.

Lemma has_type_close_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sigma gamma,
    (forall X, lc_ty_at 0 (sigma X)) ->
    (forall x, locally_closed_tm (gamma x)) ->
    locally_closed_tm (close sigma gamma t).
Proof.
  intros Delta Gamma t T H. induction H; intros sigma gamma Hsigma Hgamma.
  - unfold locally_closed_tm, close. simpl. apply Hgamma.
  - unfold locally_closed_tm, close. simpl. apply lc_tm_abs.
    + apply ty_subst_env_lc with (K := 0).
      * eapply wf_ty_lc; eassumption.
      * assumption.
    + pose (x := fresh (L ++ fv_tm t2)).
      assert (Hx : ~ In x (L ++ fv_tm t2)) by apply fresh_not_in.
      destruct (not_in_app L (fv_tm t2) x Hx) as [HxL Hxtm].
      pose (gamma' := upd_tm gamma x (tm_fvar x)).
      assert (Hgamma' : forall y, locally_closed_tm (gamma' y)).
      { intros y. unfold gamma', upd_tm. destruct (Nat.eqb y x); [apply lc_tm_fvar | apply Hgamma]. }
      assert (Hopen : lc_tm_at 0 0 (close sigma gamma' (open_tm t2 (tm_fvar x)))).
      { apply (H1 x HxL sigma gamma' Hsigma Hgamma'). }
      unfold close, open_tm in Hopen.
      rewrite (tm_ty_subst_env_open_tm t2 sigma 0 (tm_fvar x)) in Hopen.
      simpl in Hopen.
      rewrite (tm_subst_env_open_tm (tm_ty_subst_env sigma t2) gamma' 0 x Hgamma') in Hopen.
      assert (Hagree : forall y, In y (fv_tm (tm_ty_subst_env sigma t2)) -> gamma' y = gamma y).
      { intros y Hy. rewrite fv_tm_ty_subst_env in Hy.
        unfold gamma'. apply (proj1 (upd_tm_agree gamma x (tm_fvar x))).
        intro Heq. subst. apply Hxtm. exact Hy. }
      rewrite (tm_subst_env_agree (tm_ty_subst_env sigma t2) gamma' gamma Hagree) in Hopen.
      assert (HgammaX : gamma' x = tm_fvar x).
      { unfold gamma', upd_tm. rewrite Nat.eqb_refl. reflexivity. }
      rewrite HgammaX in Hopen.
      apply open_tm_rec_lc_inv with (K := 0) (k := 1) (k' := 0) (u := tm_fvar x).
      { apply lc_tm_weaken_k with (k := 0).
        { lia. }
        { exact Hopen. } }
      { lia. }
  - unfold locally_closed_tm, close. simpl. apply lc_tm_app.
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
  - unfold locally_closed_tm, close. simpl. apply lc_tm_tabs.
    pose (X := fresh (L ++ fv_tm_ty t)).
    assert (HX : ~ In X (L ++ fv_tm_ty t)) by apply fresh_not_in.
    destruct (not_in_app L (fv_tm_ty t) X HX) as [HXL HXtm].
    pose (sigma' := upd_ty sigma X (Ty_FVar X)).
    assert (Hsigma' : forall Y, lc_ty_at 0 (sigma' Y)).
    { intros Y. unfold sigma', upd_ty. destruct (Nat.eqb Y X); [apply lc_ty_fvar | apply Hsigma]. }
    assert (Hopen : lc_tm_at 0 0 (close sigma' gamma (open_tm_ty t (Ty_FVar X)))).
    { apply (H0 X HXL sigma' gamma Hsigma' Hgamma). }
    unfold close, open_tm_ty in Hopen.
    rewrite (tm_ty_subst_env_open_tm_ty t sigma' 0 (Ty_FVar X) Hsigma') in Hopen.
    assert (HsigmaX : ty_subst_env sigma' (Ty_FVar X) = Ty_FVar X).
    { unfold sigma', upd_ty. simpl. rewrite Nat.eqb_refl. reflexivity. }
    rewrite HsigmaX in Hopen.
    assert (Hagree : forall Y, In Y (fv_tm_ty t) -> sigma' Y = sigma Y).
    { intros Y HY. unfold sigma'. apply (proj1 (upd_ty_agree sigma X (Ty_FVar X))).
      intro Heq. subst. apply HXtm. exact HY. }
    rewrite (tm_ty_subst_env_agree t sigma' sigma Hagree) in Hopen.
    rewrite (tm_subst_env_open_tm_ty (tm_ty_subst_env sigma t) gamma 0 (Ty_FVar X) Hgamma) in Hopen.
    apply open_tm_ty_rec_lc_inv with (K := 0) (U := Ty_FVar X).
    exact Hopen.
  - unfold locally_closed_tm, close. simpl. apply lc_tm_tapp.
    + apply IHhas_type; assumption.
    + apply ty_subst_env_lc with (K := 0).
      * eapply wf_ty_lc; eassumption.
      * assumption.
  - unfold locally_closed_tm, close. simpl. apply lc_tm_choice.
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
Qed.

(* ============================================================ *)
(* Interaction of close with term formers and opening           *)
(* ============================================================ *)

Lemma close_fvar : forall sigma gamma x, close sigma gamma (tm_fvar x) = gamma x.
Proof. intros. unfold close. simpl. reflexivity. Qed.

Lemma close_abs : forall sigma gamma T1 t2,
  close sigma gamma (tm_abs T1 t2) = tm_abs (ty_subst_env sigma T1) (close sigma gamma t2).
Proof. intros. unfold close. simpl. reflexivity. Qed.

Lemma close_app : forall sigma gamma t1 t2,
  close sigma gamma (tm_app t1 t2) = tm_app (close sigma gamma t1) (close sigma gamma t2).
Proof. intros. unfold close. simpl. reflexivity. Qed.

Lemma close_tabs : forall sigma gamma t,
  close sigma gamma (tm_tabs t) = tm_tabs (close sigma gamma t).
Proof. intros. unfold close. simpl. reflexivity. Qed.

Lemma close_tapp : forall sigma gamma t U,
  close sigma gamma (tm_tapp t U) = tm_tapp (close sigma gamma t) (ty_subst_env sigma U).
Proof. intros. unfold close. simpl. reflexivity. Qed.

Lemma close_choice : forall sigma gamma t1 t2,
  close sigma gamma (tm_choice t1 t2) = tm_choice (close sigma gamma t1) (close sigma gamma t2).
Proof. intros. unfold close. simpl. reflexivity. Qed.

Lemma close_open_tm : forall sigma gamma gamma' x a t,
  (forall y, locally_closed_tm (gamma y)) ->
  (forall y, locally_closed_tm (gamma' y)) ->
  gamma' x = a ->
  (forall y, In y (fv_tm t) -> gamma' y = gamma y) ->
  close sigma gamma' (open_tm t (tm_fvar x)) = open_tm (close sigma gamma t) a.
Proof.
  intros sigma gamma gamma' x a t Hgam Hgam' Hx Hagree.
  unfold close, open_tm.
  rewrite (tm_ty_subst_env_open_tm t sigma 0 (tm_fvar x)).
  simpl.
  rewrite (tm_subst_env_open_tm (tm_ty_subst_env sigma t) gamma' 0 x Hgam').
  rewrite Hx.
  assert (Hag : forall y, In y (fv_tm (tm_ty_subst_env sigma t)) -> gamma' y = gamma y).
  { intros y Hy. rewrite fv_tm_ty_subst_env in Hy. apply Hagree; auto. }
  rewrite (tm_subst_env_agree (tm_ty_subst_env sigma t) gamma' gamma Hag).
  reflexivity.
Qed.

Lemma close_open_tm_ty : forall sigma sigma' gamma x U t,
  (forall X, lc_ty_at 0 (sigma X)) ->
  (forall X, lc_ty_at 0 (sigma' X)) ->
  sigma' x = U ->
  (forall X, In X (fv_tm_ty t) -> sigma' X = sigma X) ->
  (forall y, locally_closed_tm (gamma y)) ->
  close sigma' gamma (open_tm_ty t (Ty_FVar x)) = open_tm_ty (close sigma gamma t) U.
Proof.
  intros sigma sigma' gamma x U t Hsig Hsig' Hx Hagree Hgam.
  unfold close, open_tm_ty.
  rewrite (tm_ty_subst_env_open_tm_ty t sigma' 0 (Ty_FVar x) Hsig').
  simpl.
  rewrite Hx.
  assert (Hag : forall X, In X (fv_tm_ty t) -> sigma' X = sigma X) by auto.
  rewrite (tm_ty_subst_env_agree t sigma' sigma Hag).
  rewrite (tm_subst_env_open_tm_ty (tm_ty_subst_env sigma t) gamma 0 U Hgam).
  reflexivity.
Qed.

Lemma close_abs_value : forall Delta Gamma T1 t2 T2 L,
  wf_ty Delta T1 ->
  (forall x, ~ In x L ->
     has_type Delta (update Gamma x T1) (open_tm t2 (tm_fvar x)) T2) ->
  forall sigma gamma,
    (forall X, lc_ty_at 0 (sigma X)) ->
    (forall x, locally_closed_tm (gamma x)) ->
    value (tm_abs (ty_subst_env sigma T1) (close sigma gamma t2)) /\
    locally_closed_tm (tm_abs (ty_subst_env sigma T1) (close sigma gamma t2)).
Proof.
  intros Delta Gamma T1 t2 T2 L Hwf Hbody sigma gamma Hsig Hgam.
  assert (Hjudge : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)).
  { apply T_Abs with (L := L); assumption. }
  pose proof (has_type_close_lc Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)
                Hjudge sigma gamma Hsig Hgam) as Hlc.
  split.
  - apply v_abs. exact Hlc.
  - exact Hlc.
Qed.

Lemma close_tabs_value : forall Delta Gamma t T L,
  (forall X, ~ In X L ->
     has_type (X :: Delta) Gamma (open_tm_ty t (Ty_FVar X)) (open_ty T (Ty_FVar X))) ->
  forall sigma gamma,
    (forall X, lc_ty_at 0 (sigma X)) ->
    (forall x, locally_closed_tm (gamma x)) ->
    value (tm_tabs (close sigma gamma t)) /\
    locally_closed_tm (tm_tabs (close sigma gamma t)).
Proof.
  intros Delta Gamma t T L Hbody sigma gamma Hsig Hgam.
  assert (Hjudge : has_type Delta Gamma (tm_tabs t) (Ty_All T)).
  { apply T_TAbs with (L := L); assumption. }
  pose proof (has_type_close_lc Delta Gamma (tm_tabs t) (Ty_All T)
                Hjudge sigma gamma Hsig Hgam) as Hlc.
  split.
  - apply v_tabs. exact Hlc.
  - exact Hlc.
Qed.

Lemma in_ctx_fv_ty : forall Gamma y Ty,
  lookup_context y Gamma = Some Ty ->
  forall X, In X (fv_ty Ty) -> In X (ctx_fv_ty Gamma).
Proof.
  induction Gamma as [| [a Ta] Gamma IH]; intros y Ty Hlook X HX; simpl in *.
  - discriminate.
  - destruct (Nat.eqb y a) eqn:E.
    + apply Nat.eqb_eq in E. subst. inversion Hlook. subst.
      apply in_or_app. left. exact HX.
    + apply in_or_app. right. apply (IH y Ty Hlook X HX).
Qed.

Lemma ctx_lc_extend_apply : forall Gamma x T y Ty,
  (forall a Ta, lookup_context a Gamma = Some Ta -> lc_ty_at 0 Ta) ->
  lc_ty_at 0 T ->
  lookup_context y (update Gamma x T) = Some Ty ->
  lc_ty_at 0 Ty.
Proof.
  intros. exact (ctx_lc_extend Gamma x T H H0 y Ty H1).
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall (Hctx : forall x Tx, lookup_context x Gamma = Some Tx -> lc_ty_at 0 Tx)
         sigma1 sigma2 delta rho gamma1 gamma2,
    (forall X, lc_ty_at 0 (sigma1 X)) ->
    (forall X, lc_ty_at 0 (sigma2 X)) ->
    (forall x, locally_closed_tm (gamma1 x)) ->
    (forall x, locally_closed_tm (gamma2 x)) ->
    (forall i x1 x2, delta i x1 x2 -> value x1 /\ value x2) ->
    (forall X x1 x2, rho X x1 x2 -> value x1 /\ value x2) ->
    (forall x Tx, lookup_context x Gamma = Some Tx -> C Tx delta rho (gamma1 x) (gamma2 x)) ->
    C T delta rho (close sigma1 gamma1 t) (close sigma2 gamma2 t).
Proof.
  intros Delta Gamma t T H.
  induction H; intros Hctx sigma1 sigma2 delta rho gamma1 gamma2
    Hsig1 Hsig2 Hgam1 Hgam2 Hdelta Hrho Henv.
  - (* T_Var *)
    rewrite close_fvar. apply Henv. assumption.
  - (* T_Abs *)
    rewrite close_abs.
    destruct (close_abs_value Delta Gamma T1 t2 T2 L H H0 sigma1 gamma1 Hsig1 Hgam1) as [Hval1 Hlc1].
    destruct (close_abs_value Delta Gamma T1 t2 T2 L H H0 sigma2 gamma2 Hsig2 Hgam2) as [Hval2 Hlc2].
    unfold C.
    exists (tm_abs (ty_subst_env sigma1 T1) (close sigma1 gamma1 t2)).
    exists (tm_abs (ty_subst_env sigma2 T1) (close sigma2 gamma2 t2)).
    split; [apply multi_refl | split; [apply multi_refl |]].
    cbn [V].
    repeat split.
    + exact Hval1.
    + exact Hval2.
    + exists (ty_subst_env sigma1 T1), (close sigma1 gamma1 t2). reflexivity.
    + exists (ty_subst_env sigma2 T1), (close sigma2 gamma2 t2). reflexivity.
    + intros a1 a2 HVa.
      pose proof (V_value T1 delta rho a1 a2 Hdelta Hrho HVa) as [Hva1 Hva2].
      pose (x := fresh (L ++ fv_tm t2)).
      assert (Hx : ~ In x (L ++ fv_tm t2)) by apply fresh_not_in.
      destruct (not_in_app L (fv_tm t2) x Hx) as [HxL Hxtm].
      pose (gamma1' := upd_tm gamma1 x a1).
      pose (gamma2' := upd_tm gamma2 x a2).
      assert (Hgam1' : forall y, locally_closed_tm (gamma1' y)).
      { intros y. unfold gamma1', upd_tm. destruct (Nat.eqb y x).
        - apply value_lc. exact Hva1.
        - apply Hgam1. }
      assert (Hgam2' : forall y, locally_closed_tm (gamma2' y)).
      { intros y. unfold gamma2', upd_tm. destruct (Nat.eqb y x).
        - apply value_lc. exact Hva2.
        - apply Hgam2. }
      assert (Hctx' : forall y Ty, lookup_context y (update Gamma x T1) = Some Ty -> lc_ty_at 0 Ty).
      { intros y Ty Hy.
        apply (ctx_lc_extend_apply Gamma x T1 y Ty Hctx).
        - eapply wf_ty_lc; eassumption.
        - exact Hy. }
      assert (Henv' : forall y Ty, lookup_context y (update Gamma x T1) = Some Ty ->
                       C Ty delta rho (gamma1' y) (gamma2' y)).
      { intros y Ty Hlook.
        unfold update in Hlook.
        destruct (Nat.eqb y x) eqn:E; simpl in Hlook.
        - apply Nat.eqb_eq in E. subst y.
          rewrite Nat.eqb_refl in Hlook. simpl in Hlook. inversion Hlook. subst.
          unfold gamma1', gamma2'. rewrite upd_tm_self. rewrite upd_tm_self.
          apply C_of_V. exact HVa.
        - apply Nat.eqb_neq in E.
          rewrite (eqb_neq y x E) in Hlook. simpl in Hlook.
          unfold gamma1', gamma2'.
          rewrite (upd_tm_other gamma1 x a1 y E).
          rewrite (upd_tm_other gamma2 x a2 y E).
          apply Henv. exact Hlook. }
      assert (HIH : C T2 delta rho
        (close sigma1 gamma1' (open_tm t2 (tm_fvar x)))
        (close sigma2 gamma2' (open_tm t2 (tm_fvar x)))).
      { exact (H1 x HxL Hctx' sigma1 sigma2 delta rho gamma1' gamma2'
                 Hsig1 Hsig2 Hgam1' Hgam2' Hdelta Hrho Henv'). }
      assert (Hc1 : close sigma1 gamma1' (open_tm t2 (tm_fvar x)) =
                    open_tm (close sigma1 gamma1 t2) a1).
      { eapply close_open_tm.
        - exact Hgam1.
        - exact Hgam1'.
        - unfold gamma1'. apply upd_tm_self.
        - intros y Hy. assert (Hne : y <> x).
          { intro Heq. subst. apply Hxtm. exact Hy. }
          unfold gamma1'. apply upd_tm_other. auto. }
      assert (Hc2 : close sigma2 gamma2' (open_tm t2 (tm_fvar x)) =
                    open_tm (close sigma2 gamma2 t2) a2).
      { eapply close_open_tm.
        - exact Hgam2.
        - exact Hgam2'.
        - unfold gamma2'. apply upd_tm_self.
        - intros y Hy. assert (Hne : y <> x).
          { intro Heq. subst. apply Hxtm. exact Hy. }
          unfold gamma2'. apply upd_tm_other. auto. }
      rewrite Hc1 in HIH. rewrite Hc2 in HIH.
      destruct HIH as (w1 & w2 & Hred1 & Hred2 & HVw).
      exists w1, w2. split.
      * eapply multi_step.
        -- apply ST_AppAbs.
           ++ exact Hlc1.
           ++ exact Hva1.
        -- exact Hred1.
      * split.
        -- eapply multi_step.
           ++ apply ST_AppAbs.
              ** exact Hlc2.
              ** exact Hva2.
           ++ exact Hred2.
        -- exact HVw.
  - (* T_App *)
    rewrite close_app.
    unfold C.
    destruct (IHhas_type1 Hctx sigma1 sigma2 delta rho gamma1 gamma2
                Hsig1 Hsig2 Hgam1 Hgam2 Hdelta Hrho Henv) as (v1 & v2 & Hq1 & Hq2 & HVv).
    destruct (IHhas_type2 Hctx sigma1 sigma2 delta rho gamma1 gamma2
                Hsig1 Hsig2 Hgam1 Hgam2 Hdelta Hrho Henv) as (w1 & w2 & Hr1 & Hr2 & HVw).
    cbn [V] in HVv.
    destruct HVv as (Hval1 & Hval2 & Hsh1 & Hsh2 & Hfar).
    destruct (Hfar w1 w2 HVw) as (u1 & u2 & Hvu1 & Hvu2 & HVu).
    exists u1, u2. repeat split.
    + eapply multi_trans.
      * eapply multi_trans.
        -- apply multi_app_l. exact Hq1.
           eapply has_type_close_lc; [exact H0 | exact Hsig1 | exact Hgam1].
        -- apply multi_app_r. exact Hval1. exact Hr1.
      * exact Hvu1.
    + eapply multi_trans.
      * eapply multi_trans.
        -- apply multi_app_l. exact Hq2.
           eapply has_type_close_lc; [exact H0 | exact Hsig2 | exact Hgam2].
        -- apply multi_app_r. exact Hval2. exact Hr2.
      * exact Hvu2.
    + exact HVu.
  - (* T_TAbs *)
    rewrite close_tabs.
    destruct (close_tabs_value Delta Gamma t T L H sigma1 gamma1 Hsig1 Hgam1) as [Hval1 Hlc1].
    destruct (close_tabs_value Delta Gamma t T L H sigma2 gamma2 Hsig2 Hgam2) as [Hval2 Hlc2].
    unfold C.
    exists (tm_tabs (close sigma1 gamma1 t)).
    exists (tm_tabs (close sigma2 gamma2 t)).
    split; [apply multi_refl | split; [apply multi_refl |]].
    cbn [V].
    repeat split.
    + exact Hval1.
    + exact Hval2.
    + exists (close sigma1 gamma1 t), (close sigma2 gamma2 t).
      split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- intros U1 U2 HlcU1 HlcU2 R HR.
           pose (x := fresh (L ++ (fv_ty T ++ (ctx_fv_ty Gamma ++ fv_tm_ty t)))).
           assert (Hx : ~ In x (L ++ (fv_ty T ++ (ctx_fv_ty Gamma ++ fv_tm_ty t))))
             by apply fresh_not_in.
           destruct (not_in_app L (fv_ty T ++ (ctx_fv_ty Gamma ++ fv_tm_ty t)) x Hx)
             as [HxL Hx1].
           destruct (not_in_app (fv_ty T) (ctx_fv_ty Gamma ++ fv_tm_ty t) x Hx1)
             as [HxT Hx2].
           destruct (not_in_app (ctx_fv_ty Gamma) (fv_tm_ty t) x Hx2)
             as [Hxctx Hxtm_ty].
           pose (sigma1' := upd_ty sigma1 x U1).
           pose (sigma2' := upd_ty sigma2 x U2).
           pose (rho' := upd_f rho x R).
           assert (Hsig1' : forall X, lc_ty_at 0 (sigma1' X)).
           { intros Y. destruct (Nat.eqb Y x) eqn:E.
             - apply Nat.eqb_eq in E. subst Y. unfold sigma1'.
               rewrite upd_ty_self. exact HlcU1.
             - apply Nat.eqb_neq in E. unfold sigma1'.
               rewrite (upd_ty_other sigma1 x U1 Y E). apply Hsig1. }
           assert (Hsig2' : forall X, lc_ty_at 0 (sigma2' X)).
           { intros Y. destruct (Nat.eqb Y x) eqn:E.
             - apply Nat.eqb_eq in E. subst Y. unfold sigma2'.
               rewrite upd_ty_self. exact HlcU2.
             - apply Nat.eqb_neq in E. unfold sigma2'.
               rewrite (upd_ty_other sigma2 x U2 Y E). apply Hsig2. }
           assert (Hrho' : forall X a b, rho' X a b -> value a /\ value b).
           { intros Y a b HY. destruct (Nat.eqb Y x) eqn:E.
             - apply Nat.eqb_eq in E. subst Y. unfold rho' in HY.
               apply HR. exact (proj1 (upd_f_self rho x R a b) HY).
             - apply Nat.eqb_neq in E. unfold rho' in HY.
                exact (Hrho Y a b (proj1 (upd_f_other rho x R Y a b E) HY)). }
           assert (Henv' : forall y Ty, lookup_context y Gamma = Some Ty ->
                            C Ty delta rho' (gamma1 y) (gamma2 y)).
            { intros y Ty Hlook.
              assert (Hfresh : ~ In x (fv_ty Ty)).
              { intro Hin. apply Hxctx. apply (in_ctx_fv_ty Gamma y Ty Hlook x Hin). }
              apply (proj2 (C_rho_upd_fresh Ty delta rho x R (gamma1 y) (gamma2 y) Hfresh)).
              apply Henv. exact Hlook. }
           assert (HIH : C (open_ty T (Ty_FVar x)) delta rho'
             (close sigma1' gamma1 (open_tm_ty t (Ty_FVar x)))
             (close sigma2' gamma2 (open_tm_ty t (Ty_FVar x)))).
           { exact (H0 x HxL Hctx sigma1' sigma2' delta rho' gamma1 gamma2
                      Hsig1' Hsig2' Hgam1 Hgam2 Hdelta Hrho' Henv'). }
           assert (Hc1 : close sigma1' gamma1 (open_tm_ty t (Ty_FVar x)) =
                         open_tm_ty (close sigma1 gamma1 t) U1).
           { eapply close_open_tm_ty.
             - exact Hsig1.
             - exact Hsig1'.
             - unfold sigma1'. apply upd_ty_self.
             - intros Y HY. assert (Hne : Y <> x).
               { intro Heq. subst. apply Hxtm_ty. exact HY. }
               unfold sigma1'. apply upd_ty_other. auto.
             - exact Hgam1. }
           assert (Hc2 : close sigma2' gamma2 (open_tm_ty t (Ty_FVar x)) =
                         open_tm_ty (close sigma2 gamma2 t) U2).
           { eapply close_open_tm_ty.
             - exact Hsig2.
             - exact Hsig2'.
             - unfold sigma2'. apply upd_ty_self.
             - intros Y HY. assert (Hne : Y <> x).
               { intro Heq. subst. apply Hxtm_ty. exact HY. }
               unfold sigma2'. apply upd_ty_other. auto.
             - exact Hgam2. }
           rewrite Hc1 in HIH. rewrite Hc2 in HIH.
           destruct HIH as (w1 & w2 & Hred1 & Hred2 & HVw).
           assert (HlcT : lc_ty_at 1 T).
           { pose proof (has_type_lc_ty Delta Gamma (tm_tabs t) (Ty_All T)
                           (T_TAbs L Delta Gamma t T H) Hctx) as Hl.
             inversion Hl. subst. assumption. }
           assert (Hupd_iff : forall i a b,
             upd_b 0 (V (Ty_FVar x) delta rho') delta i a b <->
             upd_b 0 R delta i a b).
           { intros [|j] a b; cbn [upd_b V].
             - unfold rho'. apply upd_f_self.
             - reflexivity. }
           assert (HVfinal : V T (extend_b R delta) rho w1 w2).
           { pose proof (proj1 (V_open_ty_rec T 0 (Ty_FVar x) delta rho' w1 w2
                                  (lc_ty_fvar 0 x)) HVw) as HV1.
             pose proof (proj1 (V_delta_iff T
                            (upd_b 0 (V (Ty_FVar x) delta rho') delta)
                            (upd_b 0 R delta) rho' w1 w2 Hupd_iff) HV1) as HV2.
             pose proof (proj1 (V_extend_upd0 T delta rho' R w1 w2 HlcT) HV2) as HV3.
             exact (proj1 (V_rho_upd_fresh T (extend_b R delta) rho x R w1 w2 HxT) HV3). }
           exists w1, w2. split.
           { exact Hred1. }
           { split.
             { exact Hred2. }
             { exact HVfinal. } }
  - (* T_TApp *)
    rewrite close_tapp.
    unfold C.
    destruct (IHhas_type Hctx sigma1 sigma2 delta rho gamma1 gamma2
                Hsig1 Hsig2 Hgam1 Hgam2 Hdelta Hrho Henv) as (v1 & v2 & Hq1 & Hq2 & HVv).
    cbn [V] in HVv.
    destruct HVv as (Hval1 & Hval2 & s1 & s2 & Hs1 & Hs2 & Hfar).
    assert (HlcU1 : lc_ty_at 0 (ty_subst_env sigma1 U)).
    { apply ty_subst_env_lc with (K := 0).
      - eapply wf_ty_lc; eassumption.
      - exact Hsig1. }
    assert (HlcU2 : lc_ty_at 0 (ty_subst_env sigma2 U)).
    { apply ty_subst_env_lc with (K := 0).
      - eapply wf_ty_lc; eassumption.
      - exact Hsig2. }
    assert (HR : forall a b, V U delta rho a b -> value a /\ value b).
    { intros a b HVab. eapply V_value; [exact Hdelta | exact Hrho | exact HVab]. }
    destruct (Hfar (ty_subst_env sigma1 U) (ty_subst_env sigma2 U) HlcU1 HlcU2
                   (fun a b => V U delta rho a b) HR) as (w1 & w2 & Hred1 & Hred2 & HVw).
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (has_type_lc_ty Delta Gamma t (Ty_All T) H Hctx) as Hl.
      inversion Hl. subst. assumption. }
    assert (HVu : V (open_ty T U) delta rho w1 w2).
    { apply (proj2 (V_open_ty_rec T 0 U delta rho w1 w2 (wf_ty_lc Delta U H0))).
      apply (proj2 (V_extend_upd0 T delta rho (V U delta rho) w1 w2 HlcT)).
      exact HVw. }
    exists w1, w2. repeat split.
    + assert (Hchain : tm_tapp (close sigma1 gamma1 t) (ty_subst_env sigma1 U) -->*
                       tm_tapp (tm_tabs s1) (ty_subst_env sigma1 U)).
      { apply multi_tapp. rewrite <- Hs1. exact Hq1. exact HlcU1. }
      eapply multi_trans.
      * exact Hchain.
      * eapply multi_step.
        -- apply ST_TAppTabs.
           ++ apply value_lc. rewrite <- Hs1. exact Hval1.
           ++ exact HlcU1.
        -- exact Hred1.
    + assert (Hchain : tm_tapp (close sigma2 gamma2 t) (ty_subst_env sigma2 U) -->*
                       tm_tapp (tm_tabs s2) (ty_subst_env sigma2 U)).
      { apply multi_tapp. rewrite <- Hs2. exact Hq2. exact HlcU2. }
      eapply multi_trans.
      * exact Hchain.
      * eapply multi_step.
        -- apply ST_TAppTabs.
           ++ apply value_lc. rewrite <- Hs2. exact Hval2.
           ++ exact HlcU2.
        -- exact Hred2.
    + exact HVu.
  - (* T_Choice *)
    rewrite close_choice.
    unfold C.
    destruct (IHhas_type1 Hctx sigma1 sigma2 delta rho gamma1 gamma2
                Hsig1 Hsig2 Hgam1 Hgam2 Hdelta Hrho Henv) as (v1 & v2 & Hq1 & Hq2 & HVv).
    exists v1, v2. repeat split.
    + eapply multi_trans.
      * apply step_multi. apply ST_ChoiceLeft.
        -- eapply has_type_close_lc; [exact H | exact Hsig1 | exact Hgam1].
        -- eapply has_type_close_lc; [exact H0 | exact Hsig1 | exact Hgam1].
      * exact Hq1.
    + eapply multi_trans.
      * apply step_multi. apply ST_ChoiceLeft.
        -- eapply has_type_close_lc; [exact H | exact Hsig2 | exact Hgam2].
        -- eapply has_type_close_lc; [exact H0 | exact Hsig2 | exact Hgam2].
      * exact Hq2.
    + exact HVv.
Qed.

Lemma ty_subst_env_id : forall T, ty_subst_env (fun X => Ty_FVar X) T = T.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T' IH]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma tm_ty_subst_env_id : forall t, tm_ty_subst_env (fun X => Ty_FVar X) t = t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    simpl.
  - reflexivity.
  - reflexivity.
  - rewrite ty_subst_env_id, IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, ty_subst_env_id. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma tm_subst_env_id : forall t, tm_subst_env (fun x => tm_fvar x) t = t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma lookup_context_empty : forall x Tx, lookup_context x [] = Some Tx -> False.
Proof. intros x Tx H. simpl in H. discriminate H. Qed.

Lemma close_id : forall t,
  close (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  intros. unfold close. rewrite tm_ty_subst_env_id. apply tm_subst_env_id.
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
  intros t Ht U v Hwf Hv Hvt.
  pose proof (fundamental [] empty t
                (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
                (fun x Tx H => False_ind _ (lookup_context_empty x Tx H))
                (fun X => Ty_FVar X) (fun X => Ty_FVar X)
                (fun _ _ _ => False) (fun _ _ _ => False)
                (fun x => tm_fvar x) (fun x => tm_fvar x)
                (fun X => lc_ty_fvar 0 X)
                (fun X => lc_ty_fvar 0 X)
                (fun x => lc_tm_fvar 0 0 x)
                (fun x => lc_tm_fvar 0 0 x)
                (fun i x1 x2 Hf => match Hf with end)
                (fun X x1 x2 Hf => match Hf with end)
                (fun x Tx H => False_ind _ (lookup_context_empty x Tx H))) as HC.
  rewrite !close_id in HC.
  unfold C in HC.
  destruct HC as (v1 & v2 & Hred1 & Hred2 & HV).
  cbn [V] in HV.
  destruct HV as (Hval1 & Hval2 & s1 & s2 & Hs1 & Hs2 & Hfar).
  assert (HR : forall a b, (fun a b => a = v /\ b = v) a b -> value a /\ value b).
  { intros a b [Ha Hb]. subst. auto. }
  assert (HlcU : lc_ty_at 0 U) by (eapply wf_ty_lc; eassumption).
  destruct (Hfar U U HlcU HlcU (fun a b => a = v /\ b = v) HR)
    as (w1 & w2 & Ho1 & Ho2 & HVw).
  cbn [V] in HVw.
  destruct HVw as (Hwval1 & Hwval2 & Hsh1 & Hsh2 & HWfar).
  assert (HRvv : V (Ty_BVar 0) (extend_b (fun a b => a = v /\ b = v) (fun _ _ _ => False))
                    (fun _ _ _ => False) v v).
  { cbn [V extend_b]. auto. }
  destruct (HWfar v v HRvv) as (u1 & u2 & Hu1 & Hu2 & HVu).
  cbn [V] in HVu.
  destruct HVu as [Heq1 Heq2]. subst u1. subst u2.
  assert (Hstep : tm_tapp t U -->* w1).
  { eapply multi_trans.
    - apply multi_tapp. exact Hred1. exact HlcU.
    - eapply multi_trans.
      + apply step_multi. rewrite Hs1. apply ST_TAppTabs.
        * apply value_lc. rewrite <- Hs1. exact Hval1.
        * exact HlcU.
      + exact Ho1. }
  assert (Happ : tm_app (tm_tapp t U) v -->* tm_app w1 v).
  { apply multi_app_l. exact Hstep. apply value_lc. exact Hv. }
  eapply multi_trans.
  - exact Happ.
  - exact Hu1.
Qed.

End SystemFParametricityNondeterminismHardTask.
