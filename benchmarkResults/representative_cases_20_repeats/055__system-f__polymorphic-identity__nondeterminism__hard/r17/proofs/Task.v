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

Definition lc_ty (T : ty) : Prop := locally_closed_ty T.
Definition lc_tm (t : tm) : Prop := locally_closed_tm t.

(** ** Free variables of types and terms *)

Fixpoint free_ty_vars_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => free_ty_vars_ty T1 ++ free_ty_vars_ty T2
  | Ty_All T1 => free_ty_vars_ty T1
  end.

Fixpoint free_ty_vars_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T t1 => free_ty_vars_ty T ++ free_ty_vars_tm t1
  | tm_app t1 t2 => free_ty_vars_tm t1 ++ free_ty_vars_tm t2
  | tm_tabs t1 => free_ty_vars_tm t1
  | tm_tapp t1 T => free_ty_vars_tm t1 ++ free_ty_vars_ty T
  | tm_choice t1 t2 => free_ty_vars_tm t1 ++ free_ty_vars_tm t2
  end.

Fixpoint free_tm_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T t1 => free_tm_vars t1
  | tm_app t1 t2 => free_tm_vars t1 ++ free_tm_vars t2
  | tm_tabs t1 => free_tm_vars t1
  | tm_tapp t1 _ => free_tm_vars t1
  | tm_choice t1 t2 => free_tm_vars t1 ++ free_tm_vars t2
  end.

Definition context_free_ty_vars (Gamma : context) : list atom :=
  flat_map (fun p => free_ty_vars_ty (snd p)) Gamma.

Definition context_dom (Gamma : context) : list atom :=
  map fst Gamma.

Lemma in_context_free_ty_vars : forall Gamma x S X,
  In (x, S) Gamma -> In X (free_ty_vars_ty S) ->
  In X (context_free_ty_vars Gamma).
Proof.
  intros Gamma x S X Hin Hfv.
  unfold context_free_ty_vars.
  apply in_flat_map.
  exists (x, S). split; auto.
Qed.

Lemma in_context_dom : forall Gamma x S,
  In (x, S) Gamma -> In x (context_dom Gamma).
Proof.
  intros Gamma x S Hin. unfold context_dom.
  apply in_map_iff. exists (x, S); split; auto.
Qed.

(** Fresh atoms *)

Definition fresh_atom (l : list atom) : atom :=
  S (fold_right Nat.max 0 l).

Lemma le_fold_max : forall l x, In x l -> x <= fold_right Nat.max 0 l.
Proof.
  induction l as [|a l IH]; intros x Hx; simpl in *.
  - contradiction.
  - destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto | apply Nat.le_max_r].
Qed.

Lemma fresh_atom_notin : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l Hin. unfold fresh_atom in Hin.
  pose proof (le_fold_max l (S (fold_right Nat.max 0 l)) Hin). lia.
Qed.

Lemma notin_app_l : forall (x : atom) (a b : list atom),
  ~ In x (a ++ b) -> ~ In x a.
Proof.
  intros x a b H Hin. apply H. apply in_or_app. left. exact Hin.
Qed.

Lemma notin_app_r : forall (x : atom) (a b : list atom),
  ~ In x (a ++ b) -> ~ In x b.
Proof.
  intros x a b H Hin. apply H. apply in_or_app. right. exact Hin.
Qed.

(** ** Type substitution *)

Fixpoint ty_subst_env (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sigma X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst_env sigma T1) (ty_subst_env sigma T2)
  | Ty_All T1 => Ty_All (ty_subst_env sigma T1)
  end.

Fixpoint tm_ty_subst_env (sigma : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst_env sigma T) (tm_ty_subst_env sigma t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst_env sigma t1) (tm_ty_subst_env sigma t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst_env sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst_env sigma t1) (ty_subst_env sigma T)
  | tm_choice t1 t2 => tm_choice (tm_ty_subst_env sigma t1) (tm_ty_subst_env sigma t2)
  end.

Fixpoint tm_subst_env (eta : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => eta x
  | tm_abs T t1 => tm_abs T (tm_subst_env eta t1)
  | tm_app t1 t2 => tm_app (tm_subst_env eta t1) (tm_subst_env eta t2)
  | tm_tabs t1 => tm_tabs (tm_subst_env eta t1)
  | tm_tapp t1 T => tm_tapp (tm_subst_env eta t1) T
  | tm_choice t1 t2 => tm_choice (tm_subst_env eta t1) (tm_subst_env eta t2)
  end.

Definition inst (sigma : atom -> ty) (eta : atom -> tm) (t : tm) : tm :=
  tm_subst_env eta (tm_ty_subst_env sigma t).

Lemma ty_subst_env_id : forall T,
  ty_subst_env (fun X => Ty_FVar X) T = T.
Proof. induction T; simpl; congruence. Qed.

Lemma tm_ty_subst_env_id : forall t,
  tm_ty_subst_env (fun X => Ty_FVar X) t = t.
Proof. induction t; simpl; try rewrite ty_subst_env_id; congruence. Qed.

Lemma tm_subst_env_id : forall t,
  tm_subst_env (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; congruence. Qed.

Lemma inst_id_id : forall t,
  inst (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  intro t. unfold inst.
  rewrite tm_ty_subst_env_id, tm_subst_env_id. reflexivity.
Qed.

(** Agreement of substitutions on free variables *)

Lemma ty_subst_env_agree : forall T sigma1 sigma2,
  (forall X, In X (free_ty_vars_ty T) -> sigma1 X = sigma2 X) ->
  ty_subst_env sigma1 T = ty_subst_env sigma2 T.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T1 IH]; intros sigma1 sigma2 H; simpl in *.
  - reflexivity.
  - apply H; simpl; auto.
  - assert (H1 : ty_subst_env sigma1 T1 = ty_subst_env sigma2 T1).
    { apply IH1. intros X HX. apply H. apply in_app_iff. left; auto. }
    assert (H2 : ty_subst_env sigma1 T2 = ty_subst_env sigma2 T2).
    { apply IH2. intros X HX. apply H. apply in_app_iff. right; auto. }
    rewrite H1, H2. reflexivity.
  - assert (H1 : ty_subst_env sigma1 T1 = ty_subst_env sigma2 T1).
    { apply IH. intros X HX. apply H; auto. }
    rewrite H1. reflexivity.
Qed.

Lemma tm_ty_subst_env_agree : forall t sigma1 sigma2,
  (forall X, In X (free_ty_vars_tm t) -> sigma1 X = sigma2 X) ->
  tm_ty_subst_env sigma1 t = tm_ty_subst_env sigma2 t.
Proof.
  induction t as [i|x|T t1 IHt|t1 IH1 t2 IH2|t1 IHt|t1 IHt T|t1 IH1 t2 IH2];
    intros sigma1 sigma2 H; simpl in *.
  - reflexivity.
  - reflexivity.
  - assert (HT : ty_subst_env sigma1 T = ty_subst_env sigma2 T).
    { apply ty_subst_env_agree. intros X HX. apply H.
      apply in_app_iff. left; auto. }
    assert (Hb : tm_ty_subst_env sigma1 t1 = tm_ty_subst_env sigma2 t1).
    { apply IHt. intros X HX. apply H. apply in_app_iff. right; auto. }
    rewrite HT, Hb. reflexivity.
  - assert (H1 : tm_ty_subst_env sigma1 t1 = tm_ty_subst_env sigma2 t1).
    { apply IH1. intros X HX. apply H. apply in_app_iff. left; auto. }
    assert (H2 : tm_ty_subst_env sigma1 t2 = tm_ty_subst_env sigma2 t2).
    { apply IH2. intros X HX. apply H. apply in_app_iff. right; auto. }
    rewrite H1, H2. reflexivity.
  - assert (H1 : tm_ty_subst_env sigma1 t1 = tm_ty_subst_env sigma2 t1).
    { apply IHt. intros X HX. apply H; auto. }
    rewrite H1. reflexivity.
  - assert (H1 : tm_ty_subst_env sigma1 t1 = tm_ty_subst_env sigma2 t1).
    { apply IHt. intros X HX. apply H. apply in_app_iff. left; auto. }
    assert (H2 : ty_subst_env sigma1 T = ty_subst_env sigma2 T).
    { apply ty_subst_env_agree. intros X HX. apply H.
      apply in_app_iff. right; auto. }
    rewrite H1, H2. reflexivity.
  - assert (H1 : tm_ty_subst_env sigma1 t1 = tm_ty_subst_env sigma2 t1).
    { apply IH1. intros X HX. apply H. apply in_app_iff. left; auto. }
    assert (H2 : tm_ty_subst_env sigma1 t2 = tm_ty_subst_env sigma2 t2).
    { apply IH2. intros X HX. apply H. apply in_app_iff. right; auto. }
    rewrite H1, H2. reflexivity.
Qed.

Lemma tm_subst_env_agree : forall t eta1 eta2,
  (forall x, In x (free_tm_vars t) -> eta1 x = eta2 x) ->
  tm_subst_env eta1 t = tm_subst_env eta2 t.
Proof.
  induction t as [i|x|T t1 IHt|t1 IH1 t2 IH2|t1 IHt|t1 IHt T|t1 IH1 t2 IH2];
    intros eta1 eta2 H; simpl in *.
  - reflexivity.
  - apply H; simpl; auto.
  - assert (H1 : tm_subst_env eta1 t1 = tm_subst_env eta2 t1).
    { apply IHt. intros x Hx. apply H; auto. }
    rewrite H1. reflexivity.
  - assert (H1 : tm_subst_env eta1 t1 = tm_subst_env eta2 t1).
    { apply IH1. intros x Hx. apply H. apply in_app_iff. left; auto. }
    assert (H2 : tm_subst_env eta1 t2 = tm_subst_env eta2 t2).
    { apply IH2. intros x Hx. apply H. apply in_app_iff. right; auto. }
    rewrite H1, H2. reflexivity.
  - assert (H1 : tm_subst_env eta1 t1 = tm_subst_env eta2 t1).
    { apply IHt. intros x Hx. apply H; auto. }
    rewrite H1. reflexivity.
  - assert (H1 : tm_subst_env eta1 t1 = tm_subst_env eta2 t1).
    { apply IHt. intros x Hx. apply H; auto. }
    rewrite H1. reflexivity.
  - assert (H1 : tm_subst_env eta1 t1 = tm_subst_env eta2 t1).
    { apply IH1. intros x Hx. apply H. apply in_app_iff. left; auto. }
    assert (H2 : tm_subst_env eta1 t2 = tm_subst_env eta2 t2).
    { apply IH2. intros x Hx. apply H. apply in_app_iff. right; auto. }
    rewrite H1, H2. reflexivity.
Qed.

(** ** Monotonicity and opening identity for locally closed syntax *)

Lemma lc_ty_at_mono : forall k k' T,
  k <= k' -> lc_ty_at k T -> lc_ty_at k' T.
Proof.
  intros k k' T Hle H. revert k' Hle.
  induction H as [k0 i Hi | k0 X | k0 T1 T2 H1 IH1 H2 IH2 | k0 T1 H1 IH1];
    intros k' Hle; simpl.
  - constructor; lia.
  - constructor.
  - constructor; auto.
  - constructor. apply IH1. lia.
Qed.

Lemma lc_tm_at_mono : forall K K' k k' t,
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  intros K K' k k' t HK Hk H. revert K' k' HK Hk.
  induction H as [K0 k0 i Hi | K0 k0 x | K0 k0 T t Hty Hbody IHbody
                  | K0 k0 t1 t2 H1 IH1 H2 IH2 | K0 k0 t H0 IH0
                  | K0 k0 t T H0 IH0 Hty | K0 k0 t1 t2 H1 IH1 H2 IH2];
    intros K' k' HK Hk; simpl.
  - constructor; lia.
  - constructor.
  - constructor.
    + apply (lc_ty_at_mono K0 K'); auto.
    + apply IHbody; lia.
  - constructor; auto.
  - constructor. apply IH0; lia.
  - constructor.
    + apply IH0; auto.
    + apply (lc_ty_at_mono K0 K'); auto.
  - constructor; auto.
Qed.

Lemma lc_ty_open_id : forall k T,
  lc_ty_at k T -> forall U, open_ty_rec k U T = T.
Proof.
  intros k T H. induction H; intros U; simpl.
  - destruct (Nat.eqb k i) eqn:E. apply Nat.eqb_eq in E. lia. reflexivity.
  - reflexivity.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma lc_tm_open_ty_id : forall K k t,
  lc_tm_at K k t -> forall U, open_tm_ty_rec K U t = t.
Proof.
  intros K k t H.
  induction H as [K0 k0 i Hi | K0 k0 x | K0 k0 T t Hty Hbody IHbody
                 | K0 k0 t1 t2 H1 IH1 H2 IH2 | K0 k0 t H0 IH0
                 | K0 k0 t T H0 IH0 Hty | K0 k0 t1 t2 H1 IH1 H2 IH2];
    intros U; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + exact (lc_ty_open_id K0 T Hty U).
    + apply IHbody.
  - f_equal; auto.
  - f_equal. apply IH0.
  - f_equal.
    + apply IH0.
    + exact (lc_ty_open_id K0 T Hty U).
  - f_equal; auto.
Qed.

Lemma lc_tm_open_id : forall K k t,
  lc_tm_at K k t -> forall u, open_tm_rec k u t = t.
Proof.
  intros K k t H.
  induction H as [K0 k0 i Hi | K0 k0 x | K0 k0 T t Hty Hbody IHbody
                 | K0 k0 t1 t2 H1 IH1 H2 IH2 | K0 k0 t H0 IH0
                 | K0 k0 t T H0 IH0 Hty | K0 k0 t1 t2 H1 IH1 H2 IH2];
    intros u; simpl.
  - destruct (Nat.eqb k0 i) eqn:E. apply Nat.eqb_eq in E. lia. reflexivity.
  - reflexivity.
  - f_equal. apply IHbody.
  - f_equal; auto.
  - f_equal. apply IH0.
  - f_equal. apply IH0.
  - f_equal; auto.
Qed.

(** ** Commutation of substitutions and opening *)

Lemma ty_subst_env_open_ty_rec : forall sigma k U T,
  (forall Y, In Y (free_ty_vars_ty T) -> lc_ty (sigma Y)) ->
  ty_subst_env sigma (open_ty_rec k U T) =
  open_ty_rec k (ty_subst_env sigma U) (ty_subst_env sigma T).
Proof.
  intros sigma k U T Hlc. revert sigma k U Hlc.
  induction T as [i|X|T1 IH1 T2 IH2|T1 IH]; intros sigma k U Hlc; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply (lc_ty_open_id k (sigma X)).
    apply (lc_ty_at_mono 0 k (sigma X)); [lia | apply Hlc; simpl; auto].
  - f_equal.
    + apply IH1. intros Y HY. apply Hlc. apply in_app_iff. left; auto.
    + apply IH2. intros Y HY. apply Hlc. apply in_app_iff. right; auto.
  - f_equal. apply (IH sigma (S k) U). intros Y HY. apply Hlc; auto.
Qed.

Lemma tm_ty_subst_env_open_tm_ty_rec : forall sigma k U t,
  (forall Y, In Y (free_ty_vars_tm t) -> lc_ty (sigma Y)) ->
  tm_ty_subst_env sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_subst_env sigma U) (tm_ty_subst_env sigma t).
Proof.
  intros sigma k U t Hlc. revert sigma k U Hlc.
  induction t as [i|x|T t1 IHt|t1 IH1 t2 IH2|t1 IHt|t1 IHt T|t1 IH1 t2 IH2];
    intros sigma k U Hlc; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply ty_subst_env_open_ty_rec. intros Y HY. apply Hlc.
      apply in_app_iff. left; auto.
    + apply IHt. intros Y HY. apply Hlc. apply in_app_iff. right; auto.
  - f_equal.
    + apply IH1. intros Y HY. apply Hlc. apply in_app_iff. left; auto.
    + apply IH2. intros Y HY. apply Hlc. apply in_app_iff. right; auto.
  - f_equal. apply IHt. intros Y HY. apply Hlc. auto.
  - f_equal.
    + apply IHt. intros Y HY. apply Hlc. apply in_app_iff. left; auto.
    + apply ty_subst_env_open_ty_rec. intros Y HY. apply Hlc.
      apply in_app_iff. right; auto.
  - f_equal.
    + apply IH1. intros Y HY. apply Hlc. apply in_app_iff. left; auto.
    + apply IH2. intros Y HY. apply Hlc. apply in_app_iff. right; auto.
Qed.

Lemma tm_ty_subst_env_open_tm_rec : forall sigma k u t,
  tm_ty_subst_env sigma (open_tm_rec k u t) =
  open_tm_rec k (tm_ty_subst_env sigma u) (tm_ty_subst_env sigma t).
Proof.
  intros sigma k u t. revert k u.
  induction t as [i|x|T t1 IHt|t1 IH1 t2 IH2|t1 IHt|t1 IHt T|t1 IH1 t2 IH2];
    intros k u; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma tm_subst_env_open_tm_ty_rec : forall eta,
  (forall y, lc_tm (eta y)) ->
  forall k U t,
    tm_subst_env eta (open_tm_ty_rec k U t) =
    open_tm_ty_rec k U (tm_subst_env eta t).
Proof.
  intros eta Heta k U t. revert k U. induction t as [i|x|T t1 IHt|t1 IH1 t2 IH2|t1 IHt|t1 IHt T|t1 IH1 t2 IH2];
    intros k U; simpl.
  - reflexivity.
  - symmetry. apply (lc_tm_open_ty_id k 0 (eta x)).
    exact (lc_tm_at_mono 0 k 0 0 (eta x) (Nat.le_0_l _) (Nat.le_0_l _) (Heta x)).
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma tm_subst_env_open_tm_rec : forall eta,
  (forall y, lc_tm (eta y)) ->
  forall k u t,
    tm_subst_env eta (open_tm_rec k u t) =
    open_tm_rec k (tm_subst_env eta u) (tm_subst_env eta t).
Proof.
  intros eta Heta k U t. revert k U. induction t as [i|x|T t1 IHt|t1 IH1 t2 IH2|t1 IHt|t1 IHt T|t1 IH1 t2 IH2];
    intros k u; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply (lc_tm_open_id 0 k (eta x)).
    exact (lc_tm_at_mono 0 0 0 k (eta x) (Nat.le_0_l _) (Nat.le_0_l _) (Heta x)).
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

(** Reverse opening: a locally closed opened term was bound under one more
    binder. *)

Lemma lc_ty_open_fvar_rev : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T as [i|Y|T1 IH1 T2 IH2|T1 IH]; intros k X H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + apply lc_ty_bvar. inversion H. lia.
  - constructor.
  - inversion H. constructor.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
  - inversion H. constructor. eapply IH; eauto.
Qed.

Lemma lc_tm_open_fvar_rev : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t as [i|x0|T t1 IHt|t1 IH1 t2 IH2|t1 IHt|t1 IHt T|t1 IH1 t2 IH2];
    intros K k x H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H. constructor. lia.
  - constructor.
  - inversion H. constructor.
    + auto.
    + eapply IHt; eauto.
  - inversion H. constructor.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
  - inversion H. constructor. eapply IHt; eauto.
  - inversion H. constructor.
    + eapply IHt; eauto.
    + auto.
  - inversion H. constructor.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
Qed.

Lemma lc_tm_open_ty_fvar_rev : forall t j k X,
  lc_tm_at j k (open_tm_ty_rec j (Ty_FVar X) t) -> lc_tm_at (S j) k t.
Proof.
  induction t as [i|x|T t1 IHt|t1 IH1 t2 IH2|t1 IHt|t1 IHt T|t1 IH1 t2 IH2];
    intros j k X H; simpl in H.
  - inversion H. constructor. auto.
  - constructor.
  - inversion H. constructor.
    + eapply lc_ty_open_fvar_rev; eauto.
    + eapply IHt; eauto.
  - inversion H. constructor.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
  - inversion H. constructor. eapply IHt; eauto.
  - inversion H. constructor.
    + eapply IHt; eauto.
    + eapply lc_ty_open_fvar_rev; eauto.
  - inversion H. constructor.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
Qed.

(** ** Free variables and well-formedness *)

Lemma free_ty_vars_ty_open_mono : forall T U k X,
  In X (free_ty_vars_ty T) ->
  In X (free_ty_vars_ty (open_ty_rec k U T)).
Proof.
  intros T. induction T as [i|Y|T1 IH1 T2 IH2|T1 IH]; intros U k X HX; simpl in *.
  - destruct (Nat.eqb k i) eqn:E; simpl in *.
    + destruct HX.
    + exact HX.
  - auto.
  - apply in_app_iff in HX. apply in_app_iff. destruct HX; [left|right]; auto.
  - auto.
Qed.

Lemma free_ty_vars_open_ty_incl : forall T U k X,
  In X (free_ty_vars_ty (open_ty_rec k U T)) ->
  In X (free_ty_vars_ty T) \/ In X (free_ty_vars_ty U).
Proof.
  intros T. induction T as [i|Y|T1 IH1 T2 IH2|T1 IH]; intros U k X HX; simpl in *.
  - destruct (Nat.eqb k i) eqn:E; simpl in HX.
    + right; exact HX.
    + left; exact HX.
  - left; exact HX.
  - apply in_app_iff in HX. destruct HX as [HX|HX].
    + pose proof (IH1 U k X HX) as Hd. destruct Hd as [H|H].
      * left. apply in_app_iff. left. exact H.
      * right. exact H.
    + pose proof (IH2 U k X HX) as Hd. destruct Hd as [H|H].
      * left. apply in_app_iff. right. exact H.
      * right. exact H.
  - apply IH in HX. exact HX.
Qed.

Lemma free_ty_vars_tm_open_tm_mono : forall t u k X,
  In X (free_ty_vars_tm t) ->
  In X (free_ty_vars_tm (open_tm_rec k u t)).
Proof.
  intros t. induction t as [i|x|T t1 IHt|t1 IH1 t2 IH2|t1 IHt|t1 IHt T|t1 IH1 t2 IH2];
    intros u k X HX; simpl in *.
  - destruct (Nat.eqb k i) eqn:E; simpl in *.
    + destruct HX.
    + exact HX.
  - auto.
  - apply in_app_iff in HX. apply in_app_iff. destruct HX; [left|right]; auto.
  - apply in_app_iff in HX. apply in_app_iff. destruct HX; [left|right]; auto.
  - auto.
  - apply in_app_iff in HX. apply in_app_iff. destruct HX; [left|right]; auto.
  - apply in_app_iff in HX. apply in_app_iff. destruct HX; [left|right]; auto.
Qed.

Lemma free_ty_vars_tm_open_ty_mono : forall t U k X,
  In X (free_ty_vars_tm t) ->
  In X (free_ty_vars_tm (open_tm_ty_rec k U t)).
Proof.
  intros t. induction t as [i|x|T t1 IHt|t1 IH1 t2 IH2|t1 IHt|t1 IHt T|t1 IH1 t2 IH2];
    intros U k X HX; simpl in *.
  - auto.
  - auto.
  - apply in_app_iff in HX. apply in_app_iff. destruct HX as [HX|HX].
    + left. apply free_ty_vars_ty_open_mono. exact HX.
    + right. auto.
  - apply in_app_iff in HX. apply in_app_iff. destruct HX; [left|right]; auto.
  - auto.
  - apply in_app_iff in HX. apply in_app_iff. destruct HX as [HX|HX].
    + left. auto.
    + right. apply free_ty_vars_ty_open_mono. exact HX.
  - apply in_app_iff in HX. apply in_app_iff. destruct HX; [left|right]; auto.
Qed.

Lemma wf_ty_free_vars : forall Delta T,
  wf_ty Delta T -> forall X, In X (free_ty_vars_ty T) -> In X Delta.
Proof.
  intros Delta T H.
  induction H as [Delta0 X0 Hin | Delta0 T1 T2 H1 IH1 H2 IH2 | L Delta0 T0 Hpre IHpre].
  - intros X HX. simpl in HX. destruct HX as [-> | []]. exact Hin.
  - intros X HX. simpl in HX. apply in_app_iff in HX. destruct HX; auto.
  - intros X HX. simpl in HX.
    set (Y := fresh_atom (L ++ ([X] ++ Delta0))).
    assert (HfY : ~ In Y (L ++ ([X] ++ Delta0))) by apply fresh_atom_notin.
    assert (HYL : ~ In Y L) by apply (notin_app_l _ _ _ HfY).
    assert (HYX : Y <> X).
    { intro Heq. subst Y.
      apply (notin_app_l _ _ _ (notin_app_r _ _ _ HfY)). simpl. auto. }
    pose proof (IHpre Y HYL X (free_ty_vars_ty_open_mono T0 (Ty_FVar Y) 0 X HX))
      as Hin.
    destruct Hin as [Heq | Hin].
    + exfalso. exact (HYX Heq).
    + exact Hin.
Qed.

(** ** Local closure of substituted well-typed terms *)

Lemma wf_ty_subst_lc : forall Delta T,
  wf_ty Delta T ->
  forall sigma, (forall X, In X Delta -> lc_ty (sigma X)) ->
  lc_ty (ty_subst_env sigma T).
Proof.
  intros Delta T H.
  induction H as [Delta0 X0 Hin | Delta0 T1 T2 H1 IH1 H2 IH2 | L Delta0 T0 Hpre IHpre];
    intros sigma Hsig; simpl.
  - apply Hsig; exact Hin.
  - constructor; [apply IH1; auto | apply IH2; auto].
  - set (X := fresh_atom (L ++ (Delta0 ++ free_ty_vars_ty T0))).
    assert (HfX : ~ In X (L ++ (Delta0 ++ free_ty_vars_ty T0))) by apply fresh_atom_notin.
    assert (HXL : ~ In X L) by apply (notin_app_l _ _ _ HfX).
    assert (HXD : ~ In X Delta0) by apply (notin_app_l _ _ _ (notin_app_r _ _ _ HfX)).
    assert (HXT : ~ In X (free_ty_vars_ty T0))
      by apply (notin_app_r _ _ _ (notin_app_r _ _ _ HfX)).
    set (sigma' := fun Y => if Y =? X then Ty_FVar X else sigma Y).
    assert (Hsig' : forall Y, In Y (X :: Delta0) -> lc_ty (sigma' Y)).
    { intros Y HY. simpl in HY. destruct HY as [-> | HY].
      - unfold sigma'; simpl. rewrite Nat.eqb_refl. constructor.
      - unfold sigma'; simpl. destruct (Nat.eqb Y X) eqn:E. constructor. apply Hsig; exact HY. }
    specialize (IHpre X HXL sigma' Hsig').
    assert (Hlc' : forall Y, In Y (free_ty_vars_ty T0) -> lc_ty (sigma' Y)).
    { intros Y HY.
      assert (YinD : In Y Delta0).
      { set (Z := fresh_atom (L ++ ([Y] ++ Delta0))).
        assert (HfZ : ~ In Z (L ++ ([Y] ++ Delta0))) by apply fresh_atom_notin.
        assert (HZL : ~ In Z L) by apply (notin_app_l _ _ _ HfZ).
        assert (HZY : Z <> Y).
        { intro Heq. subst Z.
          apply (notin_app_l _ _ _ (notin_app_r _ _ _ HfZ)). simpl. auto. }
        pose proof (wf_ty_free_vars _ _ (Hpre Z HZL) Y
                      (free_ty_vars_ty_open_mono T0 (Ty_FVar Z) 0 Y HY)) as Hin2.
        destruct Hin2 as [Heq | Hin2].
        + exfalso. exact (HZY Heq).
        + exact Hin2. }
      unfold sigma'; simpl. destruct (Nat.eqb Y X) eqn:E.
      + constructor.
      + apply Hsig; exact YinD. }
    unfold open_ty in IHpre.
    rewrite (ty_subst_env_open_ty_rec sigma' 0 (Ty_FVar X) T0 Hlc') in IHpre.
    assert (HsigmaX : ty_subst_env sigma' (Ty_FVar X) = Ty_FVar X).
    { unfold sigma'; simpl. rewrite Nat.eqb_refl. reflexivity. }
    rewrite HsigmaX in IHpre.
    assert (Hag : ty_subst_env sigma' T0 = ty_subst_env sigma T0).
    { apply ty_subst_env_agree. intros Y HY.
      unfold sigma'; simpl. destruct (Nat.eqb Y X) eqn:E.
      + apply Nat.eqb_eq in E. subst Y. contradiction (HXT HY).
      + reflexivity. }
    rewrite Hag in IHpre.
    unfold lc_ty. apply lc_ty_all.
    exact (lc_ty_open_fvar_rev (ty_subst_env sigma T0) 0 X IHpre).
Qed.

Lemma has_type_free_ty_vars : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall X, In X (free_ty_vars_tm t) -> In X Delta.
Proof.
  intros Delta Gamma t T H.
  induction H as [Delta0 Gamma0 x T0 Hlook Hwf
                 | L Delta0 Gamma0 T1 t2 T2 Hwf Hpre IHpre
                 | Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta0 Gamma0 t T0 Hpre IHpre
                 | Delta0 Gamma0 t T U Ht IHt HwfU
                 | Delta0 Gamma0 t1 t2 T0 H1 IH1 H2 IH2].
  - intros X HX. simpl in HX. contradiction.
  - intros X HX. simpl in HX. apply in_app_iff in HX. destruct HX as [HX|HX].
    + eapply wf_ty_free_vars; eauto.
    + set (x := fresh_atom L).
      assert (HxL : ~ In x L).
      { apply fresh_atom_notin. }
      specialize (IHpre x HxL).
      apply IHpre. apply free_ty_vars_tm_open_tm_mono. exact HX.
  - intros X HX. simpl in HX. apply in_app_iff in HX. destruct HX; auto.
  - intros X HX. simpl in HX.
    set (Y := fresh_atom (L ++ free_ty_vars_tm t)).
    assert (HfY : ~ In Y (L ++ free_ty_vars_tm t)) by apply fresh_atom_notin.
    assert (HYL : ~ In Y L) by apply (notin_app_l _ _ _ HfY).
    assert (HYT : Y <> X).
    { intro Heq. apply (notin_app_r _ _ _ HfY). rewrite Heq. exact HX. }
    specialize (IHpre Y HYL).
    pose proof (IHpre X (free_ty_vars_tm_open_ty_mono t (Ty_FVar Y) 0 X HX)) as Hin.
    destruct Hin as [Heq | Hin].
    + exfalso. exact (HYT Heq).
    + exact Hin.
  - intros X HX. simpl in HX. apply in_app_iff in HX. destruct HX as [HX|HX].
    + auto.
    + eapply wf_ty_free_vars; eauto.
  - intros X HX. simpl in HX. apply in_app_iff in HX. destruct HX; auto.
Qed.

Lemma value_lc : forall v, value v -> lc_tm v.
Proof. intros v H. destruct H; assumption. Qed.

Lemma lc_tm_subst_env : forall t K k,
  lc_tm_at K k t ->
  forall eta, (forall y, lc_tm (eta y)) -> lc_tm_at K k (tm_subst_env eta t).
Proof.
  intros t. induction t as [i|x|T t1 IHt|t1 IH1 t2 IH2|t1 IHt|t1 IHt T|t1 IH1 t2 IH2];
    intros K k Hlk eta Heta; simpl.
  - inversion Hlk. constructor. lia.
  - apply (lc_tm_at_mono 0 K 0 k (eta x)); [lia | lia | apply Heta].
  - inversion Hlk. constructor.
    + assumption.
    + apply IHt; auto.
  - inversion Hlk. constructor.
    + apply IH1; auto.
    + apply IH2; auto.
  - inversion Hlk. constructor. apply IHt; auto.
  - inversion Hlk. constructor.
    + apply IHt; auto.
    + assumption.
  - inversion Hlk. constructor.
    + apply IH1; auto.
    + apply IH2; auto.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sigma, (forall X, In X Delta -> lc_ty (sigma X)) ->
  lc_tm (tm_ty_subst_env sigma t).
Proof.
  intros Delta Gamma t T H.
  induction H as [Delta0 Gamma0 x T0 Hlook Hwf
                 | L Delta0 Gamma0 T1 t2 T2 Hwf Hpre IHpre
                 | Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta0 Gamma0 t T0 Hpre IHpre
                 | Delta0 Gamma0 t T U Ht IHt HwfU
                 | Delta0 Gamma0 t1 t2 T0 H1 IH1 H2 IH2];
    intros sigma Hsig; simpl.
  - constructor.
  - unfold lc_tm. constructor.
    + apply (wf_ty_subst_lc Delta0 T1); auto.
    + set (x := fresh_atom L).
      assert (HxL : ~ In x L) by apply fresh_atom_notin.
      specialize (IHpre x HxL sigma Hsig).
      unfold lc_tm, open_tm in IHpre.
      rewrite tm_ty_subst_env_open_tm_rec in IHpre.
      exact (lc_tm_open_fvar_rev (tm_ty_subst_env sigma t2) 0 0 x IHpre).
  - unfold lc_tm. constructor.
    + apply IH1; auto.
    + apply IH2; auto.
  - unfold lc_tm. constructor.
    set (X := fresh_atom (L ++ (Delta0 ++ free_ty_vars_tm t))).
    assert (HfX : ~ In X (L ++ (Delta0 ++ free_ty_vars_tm t))) by apply fresh_atom_notin.
    assert (HXL : ~ In X L) by apply (notin_app_l _ _ _ HfX).
    assert (HXD : ~ In X Delta0) by apply (notin_app_l _ _ _ (notin_app_r _ _ _ HfX)).
    assert (HXT : ~ In X (free_ty_vars_tm t)) by apply (notin_app_r _ _ _ (notin_app_r _ _ _ HfX)).
    set (sigma' := fun Y => if Y =? X then Ty_FVar X else sigma Y).
    assert (Hsig' : forall Y, In Y (X :: Delta0) -> lc_ty (sigma' Y)).
    { intros Y HY. simpl in HY. destruct HY as [-> | HY].
      - unfold sigma'; simpl. rewrite Nat.eqb_refl. constructor.
      - unfold sigma'; simpl. destruct (Nat.eqb Y X) eqn:E. constructor. apply Hsig; exact HY. }
    assert (Hlc' : forall Y, In Y (free_ty_vars_tm t) -> lc_ty (sigma' Y)).
    { intros Y HY.
      assert (YinD : In Y Delta0).
      { specialize (Hpre X HXL).
        pose proof (has_type_free_ty_vars _ _ _ _ Hpre Y
                      (free_ty_vars_tm_open_ty_mono t (Ty_FVar X) 0 Y HY)) as Hin.
        destruct Hin as [Heq | Hin].
        + exfalso. apply HXT. rewrite Heq. exact HY.
        + exact Hin. }
      unfold sigma'; simpl. destruct (Nat.eqb Y X) eqn:E.
      + constructor.
      + apply Hsig; exact YinD. }
    specialize (IHpre X HXL sigma' Hsig').
    unfold lc_tm, open_tm_ty in IHpre.
    rewrite (tm_ty_subst_env_open_tm_ty_rec sigma' 0 (Ty_FVar X) t Hlc') in IHpre.
    assert (HsigmaX : ty_subst_env sigma' (Ty_FVar X) = Ty_FVar X).
    { unfold sigma'; simpl. rewrite Nat.eqb_refl. reflexivity. }
    rewrite HsigmaX in IHpre.
    assert (Hag : tm_ty_subst_env sigma' t = tm_ty_subst_env sigma t).
    { apply tm_ty_subst_env_agree. intros Y HY.
      unfold sigma'; simpl. destruct (Nat.eqb Y X) eqn:E.
      + apply Nat.eqb_eq in E. subst Y. contradiction (HXT HY).
      + reflexivity. }
    rewrite Hag in IHpre.
    exact (lc_tm_open_ty_fvar_rev (tm_ty_subst_env sigma t) 0 0 X IHpre).
  - unfold lc_tm. constructor.
    + apply IHt; auto.
    + apply (wf_ty_subst_lc Delta0 U); auto.
  - unfold lc_tm. constructor.
    + apply IH1; auto.
    + apply IH2; auto.
Qed.

(** ** The binary logical relation *)

Definition Rel := tm -> tm -> Prop.
Definition rel_env := list Rel.

Definition value_rel (R : Rel) : Prop :=
  forall t1 t2, R t1 t2 -> value t1 /\ value t2.

Definition env_value_rel (benv : rel_env) : Prop :=
  forall i, value_rel (nth i benv (fun _ _ => False)).

Fixpoint rel_val (T : ty) (benv : rel_env) (rho : atom -> Rel) : Rel :=
  match T with
  | Ty_BVar i => nth i benv (fun _ _ => False)
  | Ty_FVar X => rho X
  | Ty_Arrow T1 T2 =>
      fun t1 t2 =>
        value t1 /\ value t2 /\
        (forall a1 a2, rel_val T1 benv rho a1 a2 ->
           exists v1 v2,
             tm_app t1 a1 -->* v1 /\ tm_app t2 a2 -->* v2 /\
             rel_val T2 benv rho v1 v2)
  | Ty_All T1 =>
      fun t1 t2 =>
        value t1 /\ value t2 /\
        (forall (U1 U2 : ty) (R : Rel),
           locally_closed_ty U1 -> locally_closed_ty U2 -> value_rel R ->
           exists v1 v2,
             tm_tapp t1 U1 -->* v1 /\ tm_tapp t2 U2 -->* v2 /\
             rel_val T1 (R :: benv) rho v1 v2)
  end.

Definition erel (T : ty) (benv : rel_env) (rho : atom -> Rel) : Rel :=
  fun t1 t2 =>
    exists v1 v2,
      t1 -->* v1 /\ t2 -->* v2 /\ rel_val T benv rho v1 v2.

Definition env_equiv (b1 b2 : rel_env) : Prop :=
  forall i t1 t2,
    nth i b1 (fun _ _ => False) t1 t2 <->
    nth i b2 (fun _ _ => False) t1 t2.

Definition rho_equiv_on (T : ty) (r1 r2 : atom -> Rel) : Prop :=
  forall X, In X (free_ty_vars_ty T) ->
    forall t1 t2, r1 X t1 t2 <-> r2 X t1 t2.

Lemma env_value_rel_nil : env_value_rel nil.
Proof. intros i t1 t2 H. destruct i; simpl in H; destruct H. Qed.

Lemma env_value_rel_cons : forall R benv,
  value_rel R -> env_value_rel benv -> env_value_rel (R :: benv).
Proof.
  intros R benv HR Hb i. destruct i; simpl; auto.
Qed.

Lemma rel_val_value : forall T benv rho,
  env_value_rel benv ->
  (forall X, value_rel (rho X)) ->
  forall t1 t2, rel_val T benv rho t1 t2 -> value t1 /\ value t2.
Proof.
  intros T benv rho Hb Hr t1 t2 Hrel.
  destruct T; simpl in *.
  - apply (Hb n). exact Hrel.
  - apply (Hr a). exact Hrel.
  - destruct Hrel as [H1 [H2 H3]]. auto.
  - destruct Hrel as [H1 [H2 H3]]. auto.
Qed.

(** Extensionality of the logical relation *)

Lemma arrow_rel_ext : forall (A A' B B' : Rel),
  (forall t1 t2, A t1 t2 <-> A' t1 t2) ->
  (forall t1 t2, B t1 t2 <-> B' t1 t2) ->
  forall t1 t2,
    (value t1 /\ value t2 /\
     (forall a1 a2, A a1 a2 ->
        exists v1 v2,
          tm_app t1 a1 -->* v1 /\ tm_app t2 a2 -->* v2 /\ B v1 v2))
    <->
    (value t1 /\ value t2 /\
     (forall a1 a2, A' a1 a2 ->
        exists v1 v2,
          tm_app t1 a1 -->* v1 /\ tm_app t2 a2 -->* v2 /\ B' v1 v2)).
Proof.
  intros A A' B B' HA HB t1 t2.
  split; intros [Hv1 [Hv2 Hf]]; repeat split; auto; intros a1 a2 Ha.
  - assert (HaA : A a1 a2) by (apply (proj2 (HA a1 a2)); auto).
    destruct (Hf a1 a2 HaA) as (v1 & v2 & Hs1 & Hs2 & Hrel).
    exists v1, v2. repeat split; auto. apply (proj1 (HB v1 v2)); auto.
  - assert (HaA : A' a1 a2) by (apply (proj1 (HA a1 a2)); auto).
    destruct (Hf a1 a2 HaA) as (v1 & v2 & Hs1 & Hs2 & Hrel).
    exists v1, v2. repeat split; auto. apply (proj2 (HB v1 v2)); auto.
Qed.

Lemma all_rel_ext : forall (A A' : Rel -> Rel),
  (forall R t1 t2, A R t1 t2 <-> A' R t1 t2) ->
  forall t1 t2,
    (value t1 /\ value t2 /\
     (forall U1 U2 R,
        locally_closed_ty U1 -> locally_closed_ty U2 -> value_rel R ->
        exists v1 v2,
          tm_tapp t1 U1 -->* v1 /\ tm_tapp t2 U2 -->* v2 /\ A R v1 v2))
    <->
    (value t1 /\ value t2 /\
     (forall U1 U2 R,
        locally_closed_ty U1 -> locally_closed_ty U2 -> value_rel R ->
        exists v1 v2,
          tm_tapp t1 U1 -->* v1 /\ tm_tapp t2 U2 -->* v2 /\ A' R v1 v2)).
Proof.
  intros A A' HA t1 t2.
  split; intros [Hv1 [Hv2 Hf]]; repeat split; auto;
    intros U1 U2 R Hc1 Hc2 HR.
  - destruct (Hf U1 U2 R Hc1 Hc2 HR) as (v1 & v2 & Hs1 & Hs2 & Hrel).
    exists v1, v2. repeat split; auto. apply (proj1 (HA R v1 v2)); auto.
  - destruct (Hf U1 U2 R Hc1 Hc2 HR) as (v1 & v2 & Hs1 & Hs2 & Hrel).
    exists v1, v2. repeat split; auto. apply (proj2 (HA R v1 v2)); auto.
Qed.

Lemma rel_val_ext : forall T,
  forall b1 b2 r1 r2,
  env_equiv b1 b2 ->
  rho_equiv_on T r1 r2 ->
  forall t1 t2, rel_val T b1 r1 t1 t2 <-> rel_val T b2 r2 t1 t2.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T1 IH];
    intros b1 b2 r1 r2 He Hr t1 t2; simpl.
  - apply He.
  - apply Hr; simpl; auto.
  - apply arrow_rel_ext.
    + apply IH1; auto. intros Y HY. apply Hr. apply in_app_iff. left; auto.
    + apply IH2; auto. intros Y HY. apply Hr. apply in_app_iff. right; auto.
  - apply (all_rel_ext (fun R => rel_val T1 (R :: b1) r1)
                       (fun R => rel_val T1 (R :: b2) r2)).
    intros R s1 s2. apply IH.
    + intros i. destruct i; simpl; [reflexivity | apply He].
    + intros Y HY. apply Hr; auto.
Qed.

Lemma erel_ext : forall T b1 b2 r1 r2,
  env_equiv b1 b2 ->
  rho_equiv_on T r1 r2 ->
  forall t1 t2, erel T b1 r1 t1 t2 <-> erel T b2 r2 t1 t2.
Proof.
  intros T b1 b2 r1 r2 He Hr t1 t2. unfold erel.
  split; intros (v1 & v2 & Hs1 & Hs2 & Hrel); exists v1, v2;
    repeat split; auto.
  - apply (proj1 (rel_val_ext T b1 b2 r1 r2 He Hr v1 v2)); auto.
  - apply (proj2 (rel_val_ext T b1 b2 r1 r2 He Hr v1 v2)); auto.
Qed.

Lemma lc_ty_at_arrow_inv : forall k T1 T2,
  lc_ty_at k (Ty_Arrow T1 T2) -> lc_ty_at k T1 /\ lc_ty_at k T2.
Proof. intros k T1 T2 H. inversion H. auto. Qed.

Lemma lc_ty_at_all_inv : forall k T,
  lc_ty_at k (Ty_All T) -> lc_ty_at (S k) T.
Proof. intros k T H. inversion H. auto. Qed.

Lemma lc_env_irrel : forall k T,
  lc_ty_at k T ->
  forall b1 b2 r,
  (forall i, i < k ->
     forall t1 t2,
       nth i b1 (fun _ _ => False) t1 t2 <->
       nth i b2 (fun _ _ => False) t1 t2) ->
  forall t1 t2, rel_val T b1 r t1 t2 <-> rel_val T b2 r t1 t2.
Proof.
  intros k T. revert k.
  induction T as [i|X|T1 IH1 T2 IH2|T1 IH]; intros k Hlc b1 b2 r He t1 t2;
    simpl in *.
  - inversion Hlc. apply He. lia.
  - reflexivity.
  - assert (H1 : lc_ty_at k T1) by (apply (proj1 (lc_ty_at_arrow_inv k T1 T2 Hlc))).
    assert (H2 : lc_ty_at k T2) by (apply (proj2 (lc_ty_at_arrow_inv k T1 T2 Hlc))).
    apply arrow_rel_ext.
    + apply (IH1 k H1 b1 b2 r). intros j Hj; apply He; lia.
    + apply (IH2 k H2 b1 b2 r). intros j Hj; apply He; lia.
  - assert (H1 : lc_ty_at (S k) T1) by (apply (lc_ty_at_all_inv k T1 Hlc)).
    apply (all_rel_ext (fun R => rel_val T1 (R :: b1) r)
                       (fun R => rel_val T1 (R :: b2) r)).
    intros R s1 s2. apply (IH (S k) H1 (R :: b1) (R :: b2) r).
    intros i Hi. destruct i; simpl.
    + reflexivity.
    + apply He. lia.
Qed.

(** Substitution of a type into the relation *)

Fixpoint replace_at (k : nat) (R : Rel) (l : rel_env) : rel_env :=
  match k with
  | 0 => R :: l
  | S k' =>
      match l with
      | [] => [R]
      | b :: bs => b :: replace_at k' R bs
      end
  end.

Lemma replace_at_app : forall k R (l : rel_env),
  length l = k -> replace_at k R l = l ++ [R].
Proof.
  intros k. induction k as [|k IH]; intros R l Hlen.
  - destruct l; [reflexivity | simpl in Hlen; discriminate].
  - destruct l as [|b bs]; [simpl in Hlen; discriminate |].
    simpl. f_equal. apply IH. simpl in Hlen. lia.
Qed.

Lemma nth_app_l : forall (l m : rel_env) (d : Rel) i,
  i < length l -> nth i (l ++ m) d = nth i l d.
Proof.
  intros l. induction l as [|b bs IH]; intros m d i Hi; simpl in *.
  - lia.
  - destruct i; simpl; auto. apply IH. lia.
Qed.

Lemma nth_app_r : forall (l m : rel_env) (d : Rel) i,
  nth (length l + i) (l ++ m) d = nth i m d.
Proof.
  intros l. induction l as [|b bs IH]; intros m d i; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma nth_app_length : forall (l : rel_env) R d,
  nth (length l) (l ++ [R]) d = R.
Proof.
  intros l. induction l as [|b bs IH]; intros R d; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma rel_val_open_ty : forall T U k benv rho,
  length benv = k ->
  lc_ty_at (S k) T ->
  lc_ty U ->
  forall t1 t2,
    rel_val (open_ty_rec k U T) benv rho t1 t2 <->
    rel_val T (replace_at k (rel_val U nil rho) benv) rho t1 t2.
Proof.
  intros T. induction T as [i|X|T1 IH1 T2 IH2|T1 IH];
    intros U k benv rho Hlen Hsc HlcU t1 t2; simpl.
  - destruct (Nat.eqb k i) eqn:E; simpl.
    + apply Nat.eqb_eq in E. subst i.
      rewrite replace_at_app; auto.
      rewrite <- Hlen. rewrite nth_app_length.
      apply (lc_env_irrel 0 U HlcU benv nil rho).
      intros j Hj; lia.
    + apply Nat.eqb_neq in E.
      inversion Hsc. rewrite replace_at_app; auto.
      assert (Hi : i < length benv) by lia.
      rewrite nth_app_l; [reflexivity | exact Hi].
  - reflexivity.
  - apply lc_ty_at_arrow_inv in Hsc. destruct Hsc as [Hsc1 Hsc2].
    apply arrow_rel_ext.
    + apply IH1; auto.
    + apply IH2; auto.
  - apply lc_ty_at_all_inv in Hsc.
    apply (all_rel_ext (fun R => rel_val (open_ty_rec (S k) U T1) (R :: benv) rho)
                       (fun R => rel_val T1 (replace_at (S k) (rel_val U nil rho) (R :: benv)) rho)).
    intros R s1 s2. apply (IH U (S k) (R :: benv) rho).
    + simpl. rewrite Hlen. reflexivity.
    + exact Hsc.
    + exact HlcU.
Qed.

(** ** Local closure of types in typing derivations *)

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty T.
Proof.
  intros Delta T H.
  induction H as [Delta0 X0 Hin | Delta0 T1 T2 H1 IH1 H2 IH2 | L Delta0 T0 Hpre IHpre].
  - constructor.
  - unfold lc_ty. constructor; auto.
  - unfold lc_ty. apply lc_ty_all.
    set (X := fresh_atom L).
    assert (HXL : ~ In X L) by apply fresh_atom_notin.
    specialize (IHpre X HXL).
    unfold lc_ty, open_ty in IHpre.
    exact (lc_ty_open_fvar_rev T0 0 X IHpre).
Qed.

Lemma lc_ty_open : forall T U k,
  lc_ty_at (S k) T -> lc_ty U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  intros T. induction T as [i|X|T1 IH1 T2 IH2|T1 IH]; intros U k HT HU; simpl in *.
  - destruct (Nat.eqb k i) eqn:E; simpl.
    + apply Nat.eqb_eq in E. subst i.
      apply (lc_ty_at_mono 0 k U); [lia | exact HU].
    + apply Nat.eqb_neq in E. apply lc_ty_bvar. inversion HT. lia.
  - constructor.
  - apply lc_ty_at_arrow_inv in HT. destruct HT as [H1 H2].
    constructor; auto.
  - apply lc_ty_at_all_inv in HT. constructor. apply IH with (k := S k); auto.
Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_ty T.
Proof.
  intros Delta Gamma t T H.
  induction H as [Delta0 Gamma0 x T0 Hlook Hwf
                 | L Delta0 Gamma0 T1 t2 T2 Hwf Hpre IHpre
                 | Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta0 Gamma0 t T0 Hpre IHpre
                 | Delta0 Gamma0 t T U Ht IHt HwfU
                 | Delta0 Gamma0 t1 t2 T0 H1 IH1 H2 IH2].
  - apply (wf_ty_lc Delta0 T0); exact Hwf.
  - unfold lc_ty. constructor.
    + apply (wf_ty_lc Delta0 T1); exact Hwf.
    + exact (IHpre (fresh_atom L) (fresh_atom_notin L)).
  - apply (proj2 (lc_ty_at_arrow_inv 0 T1 T2 IH1)).
  - unfold lc_ty. apply lc_ty_all.
    set (X := fresh_atom L).
    assert (HXL : ~ In X L) by apply fresh_atom_notin.
    specialize (IHpre X HXL).
    unfold lc_ty, open_ty in IHpre.
    exact (lc_ty_open_fvar_rev T0 0 X IHpre).
  - apply lc_ty_at_all_inv in IHt.
    unfold lc_ty in *.
    exact (lc_ty_open T U 0 IHt (wf_ty_lc Delta0 U HwfU)).
  - exact IH1.
Qed.

(** ** Multi-step helpers *)

Lemma multi_trans : forall t1 t2 t3,
  t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H. induction H as [x | x y z Hxy Hyz IH]; intro H2.
  - exact H2.
  - eapply multi_step. exact Hxy. apply IH. exact H2.
Qed.

Lemma multi_app_l : forall t1 t1' t2,
  t1 -->* t1' -> lc_tm t2 -> tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 H. induction H as [x | x y z Hxy Hyz IH]; intro Hlc.
  - apply multi_refl.
  - eapply multi_step with (y := tm_app y t2).
    + apply ST_App1; auto.
    + apply IH. exact Hlc.
Qed.

Lemma multi_app_r : forall v1 t2 t2',
  value v1 -> t2 -->* t2' -> tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv H. induction H as [x | x y z Hxy Hyz IH].
  - apply multi_refl.
  - eapply multi_step with (y := tm_app v1 y).
    + apply ST_App2; auto.
    + apply IH.
Qed.

Lemma multi_tapp : forall t t' U,
  t -->* t' -> lc_ty U -> tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H. induction H as [x | x y z Hxy Hyz IH]; intro Hlc.
  - apply multi_refl.
  - eapply multi_step with (y := tm_tapp y U).
    + apply ST_TApp; auto.
    + apply IH. exact Hlc.
Qed.

Lemma multi_app_abs : forall T t v,
  lc_tm (tm_abs T t) -> value v -> tm_app (tm_abs T t) v -->* open_tm t v.
Proof.
  intros. eapply multi_step.
  - apply ST_AppAbs; auto.
  - apply multi_refl.
Qed.

Lemma multi_tapp_tabs : forall t T,
  lc_tm (tm_tabs t) -> lc_ty T -> tm_tapp (tm_tabs t) T -->* open_tm_ty t T.
Proof.
  intros. eapply multi_step.
  - apply ST_TAppTabs; auto.
  - apply multi_refl.
Qed.

Lemma multi_choice_l : forall t1 t2,
  lc_tm t1 -> lc_tm t2 -> tm_choice t1 t2 -->* t1.
Proof.
  intros. eapply multi_step.
  - apply ST_ChoiceLeft; auto.
  - apply multi_refl.
Qed.

Lemma multi_choice_r : forall t1 t2,
  lc_tm t1 -> lc_tm t2 -> tm_choice t1 t2 -->* t2.
Proof.
  intros. eapply multi_step.
  - apply ST_ChoiceRight; auto.
  - apply multi_refl.
Qed.

Lemma erel_multi_l : forall T benv rho t1 t1' t2,
  t1 -->* t1' -> erel T benv rho t1' t2 -> erel T benv rho t1 t2.
Proof.
  intros T benv rho t1 t1' t2 Hm H.
  destruct H as (v1 & v2 & Hs1 & Hs2 & Hr).
  exists v1, v2. repeat split; auto.
  eapply multi_trans; eauto.
Qed.

Lemma erel_multi_r : forall T benv rho t1 t2 t2',
  t2 -->* t2' -> erel T benv rho t1 t2' -> erel T benv rho t1 t2.
Proof.
  intros T benv rho t1 t2 t2' Hm H.
  destruct H as (v1 & v2 & Hs1 & Hs2 & Hr).
  exists v1, v2. repeat split; auto.
  eapply multi_trans; eauto.
Qed.

(** ** Helpers for the fundamental theorem *)

Lemma lookup_context_in : forall x Gamma T,
  lookup_context x Gamma = Some T -> In (x, T) Gamma.
Proof.
  intros x Gamma. induction Gamma as [| [y S] Gamma IH]; intros T H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y.
      injection H as HT. subst T. left. reflexivity.
    + right. apply IH. exact H.
Qed.

Lemma env_equiv_refl : forall b, env_equiv b b.
Proof. intros b i t1 t2. split; auto. Qed.

Lemma env_equiv_nil : env_equiv nil nil.
Proof. intros i t1 t2. destruct i; simpl; split; auto. Qed.

Lemma rel_val_rho_fresh : forall T rho1 rho2,
  rho_equiv_on T rho1 rho2 ->
  forall t1 t2, rel_val T nil rho1 t1 t2 <-> rel_val T nil rho2 t1 t2.
Proof.
  intros. apply (rel_val_ext T nil nil); auto.
  apply env_equiv_nil.
Qed.

Lemma eta_update_self : forall (x : atom) (a : tm) (eta : atom -> tm),
  (fun y : atom => if y =? x then a else eta y) x = a.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma eta_update_other : forall (x : atom) (a : tm) (eta : atom -> tm) (y : atom),
  y <> x -> (fun z : atom => if z =? x then a else eta z) y = eta y.
Proof.
  intros. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma rho_update_other : forall (X : atom) (R : Rel) (rho : atom -> Rel) (Z : atom),
  Z <> X -> (fun Y : atom => if Y =? X then R else rho Y) Z = rho Z.
Proof.
  intros. simpl. destruct (Nat.eqb Z X) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma ty_update_self : forall (x : atom) (U : ty) (sigma : atom -> ty),
  (fun Y : atom => if Y =? x then U else sigma Y) x = U.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma ty_update_other : forall (x : atom) (U : ty) (sigma : atom -> ty) (Y : atom),
  Y <> x -> (fun Z : atom => if Z =? x then U else sigma Z) Y = sigma Y.
Proof.
  intros. simpl. destruct (Nat.eqb Y x) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma free_tm_vars_ty_subst : forall sigma t,
  free_tm_vars (tm_ty_subst_env sigma t) = free_tm_vars t.
Proof.
  intros sigma t.
  induction t as [i|x|T t1 IHt|t1 IH1 t2 IH2|t1 IHt|t1 IHt T|t1 IH1 t2 IH2]; simpl.
  - reflexivity.
  - reflexivity.
  - apply IHt.
  - rewrite IH1, IH2. reflexivity.
  - apply IHt.
  - apply IHt.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma inst_open_tm_subst : forall sigma eta eta' x a t,
  (forall y, lc_tm (eta y)) ->
  (forall y, lc_tm (eta' y)) ->
  eta' x = a ->
  (forall y, In y (free_tm_vars t) -> eta' y = eta y) ->
  inst sigma eta' (open_tm t (tm_fvar x)) = open_tm (inst sigma eta t) a.
Proof.
  intros sigma eta eta' x a t Heta Heta' Hx Hagree.
  unfold inst. unfold open_tm.
  rewrite tm_ty_subst_env_open_tm_rec. simpl.
  rewrite (tm_subst_env_open_tm_rec eta' Heta' 0 (tm_fvar x) (tm_ty_subst_env sigma t)).
  assert (Hx' : tm_subst_env eta' (tm_fvar x) = a).
  { simpl. exact Hx. }
  rewrite Hx'.
  assert (Hag : tm_subst_env eta' (tm_ty_subst_env sigma t) =
                tm_subst_env eta (tm_ty_subst_env sigma t)).
  { apply tm_subst_env_agree. intros y Hy. apply Hagree.
    rewrite free_tm_vars_ty_subst in Hy. exact Hy. }
  rewrite Hag. reflexivity.
Qed.

Lemma inst_open_tm_ty_subst : forall sigma sigma' eta X U t,
  (forall Y, In Y (free_ty_vars_tm t) -> lc_ty (sigma' Y)) ->
  sigma' X = U ->
  (forall Y, In Y (free_ty_vars_tm t) -> sigma' Y = sigma Y) ->
  (forall y, lc_tm (eta y)) ->
  inst sigma' eta (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (inst sigma eta t) U.
Proof.
  intros sigma sigma' eta X U t Hlc HX Hagree Heta.
  unfold inst. unfold open_tm_ty.
  rewrite (tm_ty_subst_env_open_tm_ty_rec sigma' 0 (Ty_FVar X) t Hlc).
  assert (HsX : ty_subst_env sigma' (Ty_FVar X) = U).
  { simpl. exact HX. }
  rewrite HsX.
  assert (Hag : tm_ty_subst_env sigma' t = tm_ty_subst_env sigma t).
  { apply tm_ty_subst_env_agree. intros Y HY. apply Hagree; exact HY. }
  rewrite Hag.
  rewrite (tm_subst_env_open_tm_ty_rec eta Heta 0 U (tm_ty_subst_env sigma t)).
  reflexivity.
Qed.

Lemma has_type_inst_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sigma eta,
    (forall X, In X Delta -> lc_ty (sigma X)) ->
    (forall y, lc_tm (eta y)) ->
    lc_tm (inst sigma eta t).
Proof.
  intros Delta Gamma t T H sigma eta Hsig Heta.
  unfold inst. apply lc_tm_subst_env; auto.
  apply (has_type_lc Delta Gamma t T H sigma Hsig).
Qed.

(** ** The fundamental theorem *)

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho sigma1 sigma2 eta1 eta2,
    (forall X, value_rel (rho X)) ->
    (forall X, In X Delta -> lc_ty (sigma1 X)) ->
    (forall X, In X Delta -> lc_ty (sigma2 X)) ->
    (forall y, lc_tm (eta1 y)) ->
    (forall y, lc_tm (eta2 y)) ->
    (forall y S, In (y, S) Gamma ->
       rel_val S nil rho (eta1 y) (eta2 y)) ->
    erel T nil rho (inst sigma1 eta1 t) (inst sigma2 eta2 t).
Proof.
  intros Delta Gamma t T HT.
  induction HT as [Delta0 Gamma0 x0 T0 Hlook Hwf
                 | L Delta0 Gamma0 T1 t2 T2 Hwf Hpre IHpre
                 | Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta0 Gamma0 t T0 Hpre IHpre
                 | Delta0 Gamma0 t T U Ht IHt HwfU
                 | Delta0 Gamma0 t1 t2 T0 H1 IH1 H2 IH2];
    intros rho sigma1 sigma2 eta1 eta2 Hr Hsig1 Hsig2 Heta1 Heta2 Henv.
  - (* T_Var *)
    apply lookup_context_in in Hlook.
    pose proof (Henv x0 T0 Hlook) as Hrel.
    exists (eta1 x0), (eta2 x0). split.
    + apply multi_refl.
    + split.
      * apply multi_refl.
      * exact Hrel.
  - (* T_Abs *)
    change (erel (Ty_Arrow T1 T2) nil rho
              (tm_abs (ty_subst_env sigma1 T1) (inst sigma1 eta1 t2))
              (tm_abs (ty_subst_env sigma2 T1) (inst sigma2 eta2 t2))).
    assert (Hlc1 : lc_tm (tm_abs (ty_subst_env sigma1 T1) (inst sigma1 eta1 t2))).
    { apply (has_type_inst_lc _ _ _ _ (@T_Abs L Delta0 Gamma0 T1 t2 T2 Hwf Hpre)
               sigma1 eta1 Hsig1 Heta1). }
    assert (Hlc2 : lc_tm (tm_abs (ty_subst_env sigma2 T1) (inst sigma2 eta2 t2))).
    { apply (has_type_inst_lc _ _ _ _ (@T_Abs L Delta0 Gamma0 T1 t2 T2 Hwf Hpre)
               sigma2 eta2 Hsig2 Heta2). }
    exists (tm_abs (ty_subst_env sigma1 T1) (inst sigma1 eta1 t2)),
           (tm_abs (ty_subst_env sigma2 T1) (inst sigma2 eta2 t2)).
    split; [apply multi_refl | split; [apply multi_refl |]].
    split; [apply v_abs; exact Hlc1 | split; [apply v_abs; exact Hlc2 |]].
    intros a1 a2 Hrel12.
    pose proof (rel_val_value T1 nil rho env_value_rel_nil Hr a1 a2 Hrel12) as [Hva1 Hva2].
    set (x := fresh_atom (L ++ (context_dom Gamma0 ++ free_tm_vars t2))).
    assert (Hf : ~ In x (L ++ (context_dom Gamma0 ++ free_tm_vars t2)))
      by apply fresh_atom_notin.
    assert (HxL : ~ In x L) by apply (notin_app_l _ _ _ Hf).
    assert (Hxdom : ~ In x (context_dom Gamma0))
      by apply (notin_app_l _ _ _ (notin_app_r _ _ _ Hf)).
    assert (Hxfree : ~ In x (free_tm_vars t2))
      by apply (notin_app_r _ _ _ (notin_app_r _ _ _ Hf)).
    set (eta1' := fun y : atom => if y =? x then a1 else eta1 y).
    set (eta2' := fun y : atom => if y =? x then a2 else eta2 y).
    assert (Heta1' : forall y, lc_tm (eta1' y)).
    { intros y. unfold eta1'; simpl. destruct (Nat.eqb y x) eqn:E.
      - apply value_lc; exact Hva1.
      - apply Heta1. }
    assert (Heta2' : forall y, lc_tm (eta2' y)).
    { intros y. unfold eta2'; simpl. destruct (Nat.eqb y x) eqn:E.
      - apply value_lc; exact Hva2.
      - apply Heta2. }
    assert (Henv' : forall y S, In (y, S) ((x, T1) :: Gamma0) ->
              rel_val S nil rho (eta1' y) (eta2' y)).
    { intros y S Hin. simpl in Hin. destruct Hin as [Heq | Hin].
      - inversion Heq. subst y S.
        unfold eta1', eta2'.
        rewrite (eta_update_self x a1 eta1).
        rewrite (eta_update_self x a2 eta2).
        exact Hrel12.
      - assert (Hyx : y <> x).
        { intro Hxy. subst y. apply Hxdom.
          apply (in_context_dom Gamma0 x S). exact Hin. }
        unfold eta1', eta2'.
        rewrite (eta_update_other x a1 eta1 y Hyx).
        rewrite (eta_update_other x a2 eta2 y Hyx).
        apply Henv. exact Hin. }
    specialize (IHpre x HxL rho sigma1 sigma2 eta1' eta2'
                  Hr Hsig1 Hsig2 Heta1' Heta2' Henv').
    assert (Hinst1 : inst sigma1 eta1' (open_tm t2 (tm_fvar x)) =
                     open_tm (inst sigma1 eta1 t2) a1).
    { apply (inst_open_tm_subst sigma1 eta1 eta1' x a1 t2 Heta1 Heta1').
      - apply eta_update_self.
      - intros y Hy. apply eta_update_other.
        intro Heq. subst y. apply Hxfree. exact Hy. }
    assert (Hinst2 : inst sigma2 eta2' (open_tm t2 (tm_fvar x)) =
                     open_tm (inst sigma2 eta2 t2) a2).
    { apply (inst_open_tm_subst sigma2 eta2 eta2' x a2 t2 Heta2 Heta2').
      - apply eta_update_self.
      - intros y Hy. apply eta_update_other.
        intro Heq. subst y. apply Hxfree. exact Hy. }
    rewrite Hinst1, Hinst2 in IHpre.
    destruct IHpre as (w1 & w2 & Hm1 & Hm2 & Hrw).
    exists w1, w2. repeat split.
    + eapply multi_trans.
      { apply multi_app_abs; [exact Hlc1 | exact Hva1]. }
      exact Hm1.
    + eapply multi_trans.
      { apply multi_app_abs; [exact Hlc2 | exact Hva2]. }
      exact Hm2.
    + exact Hrw.
  - (* T_App *)
    change (erel T2 nil rho
              (tm_app (inst sigma1 eta1 t1) (inst sigma1 eta1 t2))
              (tm_app (inst sigma2 eta2 t1) (inst sigma2 eta2 t2))).
    destruct (IH1 rho sigma1 sigma2 eta1 eta2 Hr Hsig1 Hsig2 Heta1 Heta2 Henv)
      as (v1 & v1' & Hm1a & Hm1b & Hrel1).
    destruct (IH2 rho sigma1 sigma2 eta1 eta2 Hr Hsig1 Hsig2 Heta1 Heta2 Henv)
      as (v2 & v2' & Hm2a & Hm2b & Hrel2).
    destruct Hrel1 as [Hv1 [Hv1' Hf1]].
    destruct (Hf1 v2 v2' Hrel2) as (w1 & w2 & Happ1 & Happ2 & Hrelw).
    assert (Hlc2a : lc_tm (inst sigma1 eta1 t2))
      by (apply (has_type_inst_lc _ _ _ _ H2 sigma1 eta1 Hsig1 Heta1)).
    assert (Hlc2b : lc_tm (inst sigma2 eta2 t2))
      by (apply (has_type_inst_lc _ _ _ _ H2 sigma2 eta2 Hsig2 Heta2)).
    exists w1, w2. repeat split.
    + eapply multi_trans.
      { apply multi_app_l; [exact Hm1a | exact Hlc2a]. }
      eapply multi_trans.
      { apply multi_app_r; [exact Hv1 | exact Hm2a]. }
      exact Happ1.
    + eapply multi_trans.
      { apply multi_app_l; [exact Hm1b | exact Hlc2b]. }
      eapply multi_trans.
      { apply multi_app_r; [exact Hv1' | exact Hm2b]. }
      exact Happ2.
    + exact Hrelw.
  - (* T_TAbs *)
    change (erel (Ty_All T0) nil rho
              (tm_tabs (inst sigma1 eta1 t)) (tm_tabs (inst sigma2 eta2 t))).
    assert (Hlc1 : lc_tm (tm_tabs (inst sigma1 eta1 t))).
    { apply (has_type_inst_lc _ _ _ _ (@T_TAbs L Delta0 Gamma0 t T0 Hpre)
               sigma1 eta1 Hsig1 Heta1). }
    assert (Hlc2 : lc_tm (tm_tabs (inst sigma2 eta2 t))).
    { apply (has_type_inst_lc _ _ _ _ (@T_TAbs L Delta0 Gamma0 t T0 Hpre)
               sigma2 eta2 Hsig2 Heta2). }
    pose proof (has_type_lc_ty _ _ _ _ (@T_TAbs L Delta0 Gamma0 t T0 Hpre)) as HlcTyAll.
    apply lc_ty_at_all_inv in HlcTyAll.
    assert (HfvD : forall Y, In Y (free_ty_vars_tm t) -> In Y Delta0).
    { intros Y HY.
      apply (has_type_free_ty_vars _ _ _ _ (@T_TAbs L Delta0 Gamma0 t T0 Hpre) Y).
      simpl. exact HY. }
    exists (tm_tabs (inst sigma1 eta1 t)), (tm_tabs (inst sigma2 eta2 t)).
    split; [apply multi_refl | split; [apply multi_refl |]].
    split; [apply v_tabs; exact Hlc1 | split; [apply v_tabs; exact Hlc2 |]].
    intros U1 U2 R HlU1 HlU2 HR.
    set (X := fresh_atom (L ++ (Delta0 ++ (free_ty_vars_ty T0 ++
              (free_ty_vars_tm t ++ context_free_ty_vars Gamma0))))).
    assert (HfX : ~ In X (L ++ (Delta0 ++ (free_ty_vars_ty T0 ++
              (free_ty_vars_tm t ++ context_free_ty_vars Gamma0)))))
      by apply fresh_atom_notin.
    assert (HXL : ~ In X L) by apply (notin_app_l _ _ _ HfX).
    assert (HXD : ~ In X Delta0)
      by apply (notin_app_l _ _ _ (notin_app_r _ _ _ HfX)).
    assert (HXTy : ~ In X (free_ty_vars_ty T0))
      by apply (notin_app_l _ _ _ (notin_app_r _ _ _ (notin_app_r _ _ _ HfX))).
    assert (HXtm : ~ In X (free_ty_vars_tm t))
      by apply (notin_app_l _ _ _ (notin_app_r _ _ _ (notin_app_r _ _ _
                    (notin_app_r _ _ _ HfX)))).
    assert (HXctx : ~ In X (context_free_ty_vars Gamma0))
      by apply (notin_app_r _ _ _ (notin_app_r _ _ _ (notin_app_r _ _ _
                    (notin_app_r _ _ _ HfX)))).
    set (sigma1' := fun Y : atom => if Y =? X then U1 else sigma1 Y).
    set (sigma2' := fun Y : atom => if Y =? X then U2 else sigma2 Y).
    set (rho' := fun Y : atom => if Y =? X then R else rho Y).
    assert (Hsig1' : forall Y, In Y (X :: Delta0) -> lc_ty (sigma1' Y)).
    { intros Y HY. simpl in HY. destruct HY as [-> | HY].
      - unfold sigma1'. rewrite ty_update_self. exact HlU1.
      - unfold sigma1'; simpl. destruct (Nat.eqb Y X) eqn:E.
        + exact HlU1.
        + apply Hsig1; exact HY. }
    assert (Hsig2' : forall Y, In Y (X :: Delta0) -> lc_ty (sigma2' Y)).
    { intros Y HY. simpl in HY. destruct HY as [-> | HY].
      - unfold sigma2'. rewrite ty_update_self. exact HlU2.
      - unfold sigma2'; simpl. destruct (Nat.eqb Y X) eqn:E.
        + exact HlU2.
        + apply Hsig2; exact HY. }
    assert (Hr' : forall Y, value_rel (rho' Y)).
    { intros Y. unfold rho'; simpl. destruct (Nat.eqb Y X) eqn:E.
      - exact HR.
      - apply Hr. }
    assert (Henv' : forall y S, In (y, S) Gamma0 ->
              rel_val S nil rho' (eta1 y) (eta2 y)).
    { intros y S Hin.
      assert (HrEq : rho_equiv_on S rho' rho).
      { intros Z HZ t1 t2. split; intro HH.
        + assert (HZX : Z <> X).
          { intro Heq. subst Z. exfalso. apply HXctx.
            exact (in_context_free_ty_vars Gamma0 y S X Hin HZ). }
          unfold rho' in HH. rewrite (rho_update_other X R rho Z HZX) in HH.
          exact HH.
        + assert (HZX : Z <> X).
          { intro Heq. subst Z. exfalso. apply HXctx.
            exact (in_context_free_ty_vars Gamma0 y S X Hin HZ). }
          unfold rho'. rewrite (rho_update_other X R rho Z HZX). exact HH. }
      apply (proj2 (rel_val_ext S nil nil rho' rho env_equiv_nil HrEq
                      (eta1 y) (eta2 y))).
      apply Henv. exact Hin. }
    specialize (IHpre X HXL rho' sigma1' sigma2' eta1 eta2
                  Hr' Hsig1' Hsig2' Heta1 Heta2 Henv').
    assert (Hlc1' : forall Y, In Y (free_ty_vars_tm t) -> lc_ty (sigma1' Y)).
    { intros Y HY. assert (YinD : In Y Delta0) by (apply HfvD; exact HY).
      unfold sigma1'; simpl. destruct (Nat.eqb Y X) eqn:E.
      - exact HlU1.
      - apply Hsig1; exact YinD. }
    assert (Hlc2' : forall Y, In Y (free_ty_vars_tm t) -> lc_ty (sigma2' Y)).
    { intros Y HY. assert (YinD : In Y Delta0) by (apply HfvD; exact HY).
      unfold sigma2'; simpl. destruct (Nat.eqb Y X) eqn:E.
      - exact HlU2.
      - apply Hsig2; exact YinD. }
    assert (Hag1 : forall Y, In Y (free_ty_vars_tm t) -> sigma1' Y = sigma1 Y).
    { intros Y HY. unfold sigma1'; simpl. destruct (Nat.eqb Y X) eqn:E.
      - apply Nat.eqb_eq in E. subst Y. exfalso. apply HXtm. exact HY.
      - reflexivity. }
    assert (Hag2 : forall Y, In Y (free_ty_vars_tm t) -> sigma2' Y = sigma2 Y).
    { intros Y HY. unfold sigma2'; simpl. destruct (Nat.eqb Y X) eqn:E.
      - apply Nat.eqb_eq in E. subst Y. exfalso. apply HXtm. exact HY.
      - reflexivity. }
    assert (Hinst1 : inst sigma1' eta1 (open_tm_ty t (Ty_FVar X)) =
                     open_tm_ty (inst sigma1 eta1 t) U1).
    { apply (inst_open_tm_ty_subst sigma1 sigma1' eta1 X U1 t Hlc1').
      - unfold sigma1'. rewrite ty_update_self. reflexivity.
      - exact Hag1.
      - exact Heta1. }
    assert (Hinst2 : inst sigma2' eta2 (open_tm_ty t (Ty_FVar X)) =
                     open_tm_ty (inst sigma2 eta2 t) U2).
    { apply (inst_open_tm_ty_subst sigma2 sigma2' eta2 X U2 t Hlc2').
      - unfold sigma2'. rewrite ty_update_self. reflexivity.
      - exact Hag2.
      - exact Heta2. }
    rewrite Hinst1, Hinst2 in IHpre.
    destruct IHpre as (w1 & w2 & Hm1 & Hm2 & Hrw).
    unfold open_ty in Hrw.
    assert (Hrw1 : rel_val T0 (replace_at 0 (rel_val (Ty_FVar X) nil rho') nil)
                     rho' w1 w2).
    { apply (proj1 (rel_val_open_ty T0 (Ty_FVar X) 0 nil rho' eq_refl
                      HlcTyAll (lc_ty_fvar 0 X) w1 w2)). exact Hrw. }
    assert (HenvR : replace_at 0 (rel_val (Ty_FVar X) nil rho') nil = R :: nil).
    { simpl. f_equal. unfold rho'. simpl. rewrite Nat.eqb_refl. reflexivity. }
    rewrite HenvR in Hrw1.
    assert (Hrw2 : rel_val T0 (R :: nil) rho w1 w2).
    { assert (HrEq0 : rho_equiv_on T0 rho' rho).
      { intros Z HZ t1 t2. split; intro HH.
        + assert (HZX : Z <> X).
          { intro Heq. subst Z. exfalso. apply HXTy. exact HZ. }
          unfold rho' in HH. rewrite (rho_update_other X R rho Z HZX) in HH.
          exact HH.
        + assert (HZX : Z <> X).
          { intro Heq. subst Z. exfalso. apply HXTy. exact HZ. }
          unfold rho'. rewrite (rho_update_other X R rho Z HZX). exact HH. }
      apply (proj1 (rel_val_ext T0 (R :: nil) (R :: nil) rho' rho
                      (env_equiv_refl _) HrEq0 w1 w2)).
      exact Hrw1. }
    exists w1, w2. repeat split.
    + eapply multi_trans.
      { apply multi_tapp_tabs; [exact Hlc1 | exact HlU1]. }
      exact Hm1.
    + eapply multi_trans.
      { apply multi_tapp_tabs; [exact Hlc2 | exact HlU2]. }
      exact Hm2.
    + exact Hrw2.
  - (* T_TApp *)
    change (erel (open_ty T U) nil rho
              (tm_tapp (inst sigma1 eta1 t) (ty_subst_env sigma1 U))
              (tm_tapp (inst sigma2 eta2 t) (ty_subst_env sigma2 U))).
    destruct (IHt rho sigma1 sigma2 eta1 eta2 Hr Hsig1 Hsig2 Heta1 Heta2 Henv)
      as (v1 & v2 & Hm1 & Hm2 & Hrel).
    destruct Hrel as [Hv1 [Hv2 Hf]].
    pose proof (has_type_lc_ty _ _ _ _ Ht) as HlcAll.
    apply lc_ty_at_all_inv in HlcAll.
    pose proof (wf_ty_lc Delta0 U HwfU) as HlcU.
    assert (HlcU1 : locally_closed_ty (ty_subst_env sigma1 U))
      by (apply (wf_ty_subst_lc Delta0 U HwfU sigma1 Hsig1)).
    assert (HlcU2 : locally_closed_ty (ty_subst_env sigma2 U))
      by (apply (wf_ty_subst_lc Delta0 U HwfU sigma2 Hsig2)).
    assert (HRU : value_rel (rel_val U nil rho)).
    { intros t1 t2 Hvv. exact (rel_val_value U nil rho env_value_rel_nil Hr t1 t2 Hvv). }
    destruct (Hf (ty_subst_env sigma1 U) (ty_subst_env sigma2 U)
                 (rel_val U nil rho) HlcU1 HlcU2 HRU)
      as (w1 & w2 & Ht1 & Ht2 & Hrw).
    assert (Hrw' : rel_val (open_ty T U) nil rho w1 w2).
    { unfold open_ty.
      apply (proj2 (rel_val_open_ty T U 0 nil rho eq_refl HlcAll HlcU w1 w2)).
      change (rel_val T (rel_val U nil rho :: nil) rho w1 w2).
      exact Hrw. }
    exists w1, w2. repeat split.
    + eapply multi_trans.
      { apply multi_tapp; [exact Hm1 | exact HlcU1]. }
      exact Ht1.
    + eapply multi_trans.
      { apply multi_tapp; [exact Hm2 | exact HlcU2]. }
      exact Ht2.
    + exact Hrw'.
  - (* T_Choice *)
    change (erel T0 nil rho
              (tm_choice (inst sigma1 eta1 t1) (inst sigma1 eta1 t2))
              (tm_choice (inst sigma2 eta2 t1) (inst sigma2 eta2 t2))).
    destruct (IH1 rho sigma1 sigma2 eta1 eta2 Hr Hsig1 Hsig2 Heta1 Heta2 Henv)
      as (v1 & v2 & Hm1 & Hm2 & Hrel).
    assert (Hlc1a : lc_tm (inst sigma1 eta1 t1))
      by (apply (has_type_inst_lc _ _ _ _ H1 sigma1 eta1 Hsig1 Heta1)).
    assert (Hlc1b : lc_tm (inst sigma1 eta1 t2))
      by (apply (has_type_inst_lc _ _ _ _ H2 sigma1 eta1 Hsig1 Heta1)).
    assert (Hlc2a : lc_tm (inst sigma2 eta2 t1))
      by (apply (has_type_inst_lc _ _ _ _ H1 sigma2 eta2 Hsig2 Heta2)).
    assert (Hlc2b : lc_tm (inst sigma2 eta2 t2))
      by (apply (has_type_inst_lc _ _ _ _ H2 sigma2 eta2 Hsig2 Heta2)).
    exists v1, v2. repeat split.
    + eapply multi_trans.
      { apply multi_choice_l; [exact Hlc1a | exact Hlc1b]. }
      exact Hm1.
    + eapply multi_trans.
      { apply multi_choice_l; [exact Hlc2a | exact Hlc2b]. }
      exact Hm2.
    + exact Hrel.
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
  intros t Ht U v HwfU Hv HvU.
  set (rho := fun (_ : atom) (a b : tm) => a = v /\ b = v).
  assert (Hr : forall X, value_rel (rho X)).
  { intros X a b [Ha Hb]. subst a. subst b. split; exact Hv. }
  assert (Hsig : forall X, In X [] -> lc_ty (Ty_FVar X)).
  { intros X HX. simpl in HX. contradiction. }
  assert (Heta : forall y, lc_tm (tm_fvar y)).
  { intros y. unfold lc_tm. constructor. }
  assert (Henv : forall y S, In (y, S) [] ->
            rel_val S nil rho (tm_fvar y) (tm_fvar y)).
  { intros y S Hin. simpl in Hin. contradiction. }
  pose proof (fundamental [] empty t
                (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
                rho (fun X => Ty_FVar X) (fun X => Ty_FVar X)
                (fun x => tm_fvar x) (fun x => tm_fvar x)
                Hr Hsig Hsig Heta Heta Henv) as Herel.
  rewrite !inst_id_id in Herel.
  destruct Herel as (v1 & v2 & Hm1 & Hm2 & Hrel).
  simpl in Hrel.
  destruct Hrel as [Hval1 [Hval2 Hall]].
  assert (HlcU : locally_closed_ty U) by (apply (wf_ty_lc [] U HwfU)).
  assert (Hlcv : lc_tm v) by (apply value_lc; exact Hv).
  destruct (Hall U U (rho 0) HlcU HlcU (Hr 0))
    as (w1 & w2 & Ht1 & Ht2 & Hrel2).
  simpl in Hrel2.
  destruct Hrel2 as [Hw1 [Hw2 Hf]].
  assert (Hrelvv : rel_val (Ty_BVar 0) (rho 0 :: nil) rho v v).
  { simpl. unfold rho. simpl. split; reflexivity. }
  destruct (Hf v v Hrelvv) as (z1 & z2 & Happ1 & Happ2 & Hzrel).
  simpl in Hzrel. unfold rho in Hzrel. simpl in Hzrel.
  destruct Hzrel as [Hz1 Hz2].
  assert (Hstep1 : tm_app (tm_tapp t U) v -->* tm_app w1 v).
  { apply multi_app_l.
    - eapply multi_trans.
      + apply multi_tapp; [exact Hm1 | exact HlcU].
      + exact Ht1.
    - exact Hlcv. }
  rewrite Hz1 in Happ1.
  eapply multi_trans; [exact Hstep1 | exact Happ1].
Qed.

End SystemFParametricityNondeterminismHardTask.
