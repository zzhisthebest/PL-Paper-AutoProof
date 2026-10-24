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

(* ================================================================ *)
(* Infrastructure for the parametricity proof                       *)
(* ================================================================ *)

Notation Rel := (tm -> Prop).

Definition emp_rel : Rel := fun _ => False.

(* Simultaneous substitution of free type variables. *)
Fixpoint ty_apply (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sigma X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_apply sigma T1) (ty_apply sigma T2)
  | Ty_All T1 => Ty_All (ty_apply sigma T1)
  end.

(* Simultaneous substitution of free type and term variables. *)
Fixpoint tm_apply (sigma : atom -> ty) (gamma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T t1 => tm_abs (ty_apply sigma T) (tm_apply sigma gamma t1)
  | tm_app t1 t2 => tm_app (tm_apply sigma gamma t1) (tm_apply sigma gamma t2)
  | tm_tabs t1 => tm_tabs (tm_apply sigma gamma t1)
  | tm_tapp t1 T => tm_tapp (tm_apply sigma gamma t1) (ty_apply sigma T)
  | tm_choice t1 t2 => tm_choice (tm_apply sigma gamma t1) (tm_apply sigma gamma t2)
  end.

(* Free type atoms of a type. *)
Fixpoint free_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => free_ty T1 ++ free_ty T2
  | Ty_All T1 => free_ty T1
  end.

(* Free type atoms occurring in the annotations of a term. *)
Fixpoint free_ty_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T t1 => free_ty T ++ free_ty_tm t1
  | tm_app t1 t2 => free_ty_tm t1 ++ free_ty_tm t2
  | tm_tabs t1 => free_ty_tm t1
  | tm_tapp t1 T => free_ty_tm t1 ++ free_ty T
  | tm_choice t1 t2 => free_ty_tm t1 ++ free_ty_tm t2
  end.

(* Free term variables (atoms) of a term. *)
Fixpoint free_tm_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => free_tm_tm t1
  | tm_app t1 t2 => free_tm_tm t1 ++ free_tm_tm t2
  | tm_tabs t1 => free_tm_tm t1
  | tm_tapp t1 _ => free_tm_tm t1
  | tm_choice t1 t2 => free_tm_tm t1 ++ free_tm_tm t2
  end.

Fixpoint free_ty_ctx (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => free_ty T ++ free_ty_ctx Gamma'
  end.

Fixpoint max_list (l : list atom) : atom :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (max_list l')
  end.

Definition fresh (l : list atom) : atom := S (max_list l).

Lemma max_list_ge : forall l (x : atom), In x l -> x <= max_list l.
Proof.
  induction l as [| y l IH]; intros x Hin.
  - inversion Hin.
  - simpl. destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto | apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall l, ~ In (fresh l) l.
Proof.
  intros l Hin. pose proof (max_list_ge l (fresh l) Hin). unfold fresh in H. lia.
Qed.

Lemma fresh_notin_app1 : forall l1 l2, ~ In (fresh (l1 ++ l2)) l1.
Proof.
  intros l1 l2 H. apply (fresh_notin (l1 ++ l2)). apply in_app_iff. left. exact H.
Qed.

Lemma fresh_notin_app2 : forall l1 l2, ~ In (fresh (l1 ++ l2)) l2.
Proof.
  intros l1 l2 H. apply (fresh_notin (l1 ++ l2)). apply in_app_iff. right. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* Substitution lemmas                                                *)
(* ------------------------------------------------------------------ *)

Lemma lc_ty_mono : forall k T, lc_ty_at k T -> forall k', k <= k' -> lc_ty_at k' T.
Proof.
  intros k T H. induction H as [k i Hi | k X | k T1 T2 H1 IH1 H2 IH2 | k T1 H1 IH1];
    intros k' Hle.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; [apply IH1 | apply IH2]; lia.
  - apply lc_ty_all. apply IH1. lia.
Qed.

Lemma lc_tm_mono : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H. induction H as
    [K k i Hi | K k x | K k T t1 Hty Ht IHt | K k t1 t2 H1 IH1 H2 IH2
    | K k t1 Ht IHt | K k t1 T Ht IHt Hty | K k t1 t2 H1 IH1 H2 IH2];
    intros K' k' HK Hk.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_mono with (k := K); [assumption | lia].
    + apply IHt; lia.
  - apply lc_tm_app; [apply IH1 | apply IH2]; lia.
  - apply lc_tm_tabs. apply IHt; lia.
  - apply lc_tm_tapp.
    + apply IHt; lia.
    + apply lc_ty_mono with (k := K); [assumption | lia].
  - apply lc_tm_choice; [apply IH1 | apply IH2]; lia.
Qed.

Lemma open_ty_rec_lc : forall T k U, lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  intros T. induction T; intros k U Hlc; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exfalso. inversion Hlc. lia.
    + reflexivity.
  - reflexivity.
  - assert (H1 : lc_ty_at k T1) by (inversion Hlc; assumption).
    assert (H2 : lc_ty_at k T2) by (inversion Hlc; assumption).
    rewrite (IHT1 k U H1), (IHT2 k U H2). reflexivity.
  - assert (H1 : lc_ty_at (S k) T) by (inversion Hlc; assumption).
    rewrite (IHT (S k) U H1). reflexivity.
Qed.

Lemma ty_apply_open_rec : forall sigma,
  (forall X, lc_ty_at 0 (sigma X)) ->
  forall k U T,
  ty_apply sigma (open_ty_rec k U T) =
  open_ty_rec k (ty_apply sigma U) (ty_apply sigma T).
Proof.
  intros sigma Hsig k U T. revert k.
  induction T; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_ty_rec_lc.
    apply (lc_ty_mono 0 (sigma a) (Hsig a) k). lia.
  - rewrite IHT1, IHT2. reflexivity.
  - rewrite IHT. reflexivity.
Qed.

Lemma ty_apply_agree : forall sigma1 sigma2 T,
  (forall X, In X (free_ty T) -> sigma1 X = sigma2 X) ->
  ty_apply sigma1 T = ty_apply sigma2 T.
Proof.
  intros sigma1 sigma2 T.
  induction T; intros Hag; simpl.
  - reflexivity.
  - apply Hag. simpl. auto.
  - assert (H1 : forall X, In X (free_ty T1) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hag. simpl. apply in_app_iff. auto. }
    assert (H2 : forall X, In X (free_ty T2) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hag. simpl. apply in_app_iff. auto. }
    rewrite (IHT1 H1), (IHT2 H2). reflexivity.
  - assert (H1 : forall X, In X (free_ty T) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hag. simpl. auto. }
    rewrite (IHT H1). reflexivity.
Qed.

Lemma ty_apply_identity : forall T, ty_apply (fun X => Ty_FVar X) T = T.
Proof. intros T. induction T; simpl; congruence. Qed.

Lemma tm_apply_identity : forall t,
  tm_apply (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  intros t. induction t; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite ty_apply_identity, IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt, ty_apply_identity. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma open_tm_rec_lc : forall T K d, lc_tm_at K d T ->
  forall k V, d <= k -> open_tm_rec k V T = T.
Proof.
  intros X0. induction X0 as
    [ n | a | ty0 t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 ty0 | t1 IH1 t2 IH2 ];
    intros K d Hlc k V Hle; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exfalso. inversion Hlc. lia.
    + reflexivity.
  - reflexivity.
  - assert (H1 : lc_tm_at K (S d) t1) by (inversion Hlc; assumption).
    rewrite (IH1 K (S d) H1 (S k) V ltac:(lia)). reflexivity.
  - assert (H1 : lc_tm_at K d t1) by (inversion Hlc; assumption).
    assert (H2 : lc_tm_at K d t2) by (inversion Hlc; assumption).
    rewrite (IH1 K d H1 k V Hle), (IH2 K d H2 k V Hle). reflexivity.
  - assert (H1 : lc_tm_at (S K) d t1) by (inversion Hlc; assumption).
    rewrite (IH1 (S K) d H1 k V Hle). reflexivity.
  - assert (H1 : lc_tm_at K d t1) by (inversion Hlc; assumption).
    rewrite (IH1 K d H1 k V Hle). reflexivity.
  - assert (H1 : lc_tm_at K d t1) by (inversion Hlc; assumption).
    assert (H2 : lc_tm_at K d t2) by (inversion Hlc; assumption).
    rewrite (IH1 K d H1 k V Hle), (IH2 K d H2 k V Hle). reflexivity.
Qed.

Lemma tm_apply_open_tm_rec : forall sigma gamma,
  (forall x, locally_closed_tm (gamma x)) ->
  forall k u t,
  tm_apply sigma gamma (open_tm_rec k u t) =
  open_tm_rec k (tm_apply sigma gamma u) (tm_apply sigma gamma t).
Proof.
  intros sigma gamma Hglc k u t. revert k.
  induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply (open_tm_rec_lc (gamma a) 0 0); [apply Hglc | lia].
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma tm_apply_open_tm : forall sigma gamma,
  (forall x, locally_closed_tm (gamma x)) ->
  forall t u,
  tm_apply sigma gamma (open_tm t u) =
  open_tm (tm_apply sigma gamma t) (tm_apply sigma gamma u).
Proof. intros. apply tm_apply_open_tm_rec; assumption. Qed.

Lemma open_tm_ty_rec_lc : forall T K d, lc_tm_at K d T ->
  forall k U, K <= k -> open_tm_ty_rec k U T = T.
Proof.
  intros X0. induction X0 as
    [ n | a | ty0 t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 ty0 | t1 IH1 t2 IH2 ];
    intros K d Hlc k U Hle; simpl.
  - reflexivity.
  - reflexivity.
  - assert (Hty : lc_ty_at K ty0) by (inversion Hlc; assumption).
    assert (Ht : lc_tm_at K (S d) t1) by (inversion Hlc; assumption).
    rewrite (open_ty_rec_lc ty0 k U ltac:(apply (lc_ty_mono K ty0 Hty k); lia)).
    rewrite (IH1 K (S d) Ht k U Hle). reflexivity.
  - assert (H1 : lc_tm_at K d t1) by (inversion Hlc; assumption).
    assert (H2 : lc_tm_at K d t2) by (inversion Hlc; assumption).
    rewrite (IH1 K d H1 k U Hle), (IH2 K d H2 k U Hle). reflexivity.
  - assert (H1 : lc_tm_at (S K) d t1) by (inversion Hlc; assumption).
    rewrite (IH1 (S K) d H1 (S k) U ltac:(lia)). reflexivity.
  - assert (H1 : lc_tm_at K d t1) by (inversion Hlc; assumption).
    assert (Hty : lc_ty_at K ty0) by (inversion Hlc; assumption).
    rewrite (IH1 K d H1 k U Hle).
    rewrite (open_ty_rec_lc ty0 k U ltac:(apply (lc_ty_mono K ty0 Hty k); lia)).
    reflexivity.
  - assert (H1 : lc_tm_at K d t1) by (inversion Hlc; assumption).
    assert (H2 : lc_tm_at K d t2) by (inversion Hlc; assumption).
    rewrite (IH1 K d H1 k U Hle), (IH2 K d H2 k U Hle). reflexivity.
Qed.

Lemma tm_apply_open_tm_ty_rec : forall sigma gamma,
  (forall X, lc_ty_at 0 (sigma X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  forall k U t,
  tm_apply sigma gamma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_apply sigma U) (tm_apply sigma gamma t).
Proof.
  intros sigma gamma Hsig Hglc k U t. revert k.
  induction t as [ n | a | ty0 b IH1 | t1 IH1 t2 IH2 | b IH1 | t1 IH1 ty0 | t1 IH1 t2 IH2 ];
    intros k; simpl.
  - reflexivity.
  - symmetry. apply (open_tm_ty_rec_lc (gamma a) 0 0); [apply Hglc | lia].
  - rewrite (ty_apply_open_rec sigma Hsig k U ty0), IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, (ty_apply_open_rec sigma Hsig k U ty0). reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma tm_apply_open_tm_ty : forall sigma gamma,
  (forall X, lc_ty_at 0 (sigma X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  forall t U,
  tm_apply sigma gamma (open_tm_ty t U) =
  open_tm_ty (tm_apply sigma gamma t) (ty_apply sigma U).
Proof. intros. apply tm_apply_open_tm_ty_rec; assumption. Qed.

Lemma tm_apply_agree : forall sigma1 sigma2 gamma1 gamma2 t,
  (forall X, In X (free_ty_tm t) -> sigma1 X = sigma2 X) ->
  (forall x, In x (free_tm_tm t) -> gamma1 x = gamma2 x) ->
  tm_apply sigma1 gamma1 t = tm_apply sigma2 gamma2 t.
Proof.
  intros sigma1 sigma2 gamma1 gamma2 t.
  induction t as [ n | a | ty0 b IH1 | t1 IH1 t2 IH2 | b IH1 | t1 IH1 ty0 | t1 IH1 t2 IH2 ];
    intros Hs Hg; simpl.
  - reflexivity.
  - apply Hg. simpl. auto.
  - assert (Hs0 : forall X, In X (free_ty ty0) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hs. simpl. apply in_app_iff. auto. }
    assert (Hs1 : forall X, In X (free_ty_tm b) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hs. simpl. apply in_app_iff. auto. }
    assert (Hg1 : forall x, In x (free_tm_tm b) -> gamma1 x = gamma2 x).
    { intros x Hx. apply Hg. simpl. auto. }
    rewrite (ty_apply_agree _ _ _ Hs0), (IH1 Hs1 Hg1). reflexivity.
  - assert (Hs1 : forall X, In X (free_ty_tm t1) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hs. simpl. apply in_app_iff. auto. }
    assert (Hs2 : forall X, In X (free_ty_tm t2) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hs. simpl. apply in_app_iff. auto. }
    assert (Hg1 : forall x, In x (free_tm_tm t1) -> gamma1 x = gamma2 x).
    { intros x Hx. apply Hg. simpl. apply in_app_iff. auto. }
    assert (Hg2 : forall x, In x (free_tm_tm t2) -> gamma1 x = gamma2 x).
    { intros x Hx. apply Hg. simpl. apply in_app_iff. auto. }
    rewrite (IH1 Hs1 Hg1), (IH2 Hs2 Hg2). reflexivity.
  - assert (Hs1 : forall X, In X (free_ty_tm b) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hs. simpl. auto. }
    assert (Hg1 : forall x, In x (free_tm_tm b) -> gamma1 x = gamma2 x).
    { intros x Hx. apply Hg. simpl. auto. }
    rewrite (IH1 Hs1 Hg1). reflexivity.
  - assert (Hs1 : forall X, In X (free_ty_tm t1) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hs. simpl. apply in_app_iff. auto. }
    assert (Hg1 : forall x, In x (free_tm_tm t1) -> gamma1 x = gamma2 x).
    { intros x Hx. apply Hg. simpl. auto. }
    assert (Hs0 : forall X, In X (free_ty ty0) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hs. simpl. apply in_app_iff. auto. }
    rewrite (IH1 Hs1 Hg1), (ty_apply_agree _ _ _ Hs0). reflexivity.
  - assert (Hs1 : forall X, In X (free_ty_tm t1) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hs. simpl. apply in_app_iff. auto. }
    assert (Hs2 : forall X, In X (free_ty_tm t2) -> sigma1 X = sigma2 X).
    { intros X HX. apply Hs. simpl. apply in_app_iff. auto. }
    assert (Hg1 : forall x, In x (free_tm_tm t1) -> gamma1 x = gamma2 x).
    { intros x Hx. apply Hg. simpl. apply in_app_iff. auto. }
    assert (Hg2 : forall x, In x (free_tm_tm t2) -> gamma1 x = gamma2 x).
    { intros x Hx. apply Hg. simpl. apply in_app_iff. auto. }
    rewrite (IH1 Hs1 Hg1), (IH2 Hs2 Hg2). reflexivity.
Qed.

Lemma nth_app_below : forall (i : nat) (l1 l2 : list Rel) (d : Rel),
  i < length l1 -> nth i (l1 ++ l2) d = nth i l1 d.
Proof.
  intros i l1. revert i. induction l1 as [| x l1 IH]; intros i l2 d Hi.
  - simpl in Hi. lia.
  - destruct i as [|i]; simpl.
    + reflexivity.
    + apply IH. simpl in Hi. lia.
Qed.

Lemma nth_app_at : forall (l1 : list Rel) (x d : Rel),
  nth (length l1) (l1 ++ [x]) d = x.
Proof.
  intros l1. induction l1 as [| y l1 IH]; intros x d; simpl.
  - reflexivity.
  - apply IH.
Qed.

(* ------------------------------------------------------------------ *)
(* The logical relation                                               *)
(* ------------------------------------------------------------------ *)

(* [VR rho env T v]: the value [v] belongs to the interpretation of
   the type [T], where [rho] interprets free type variables and [env]
   interprets the enclosing (de Bruijn indexed) type binders,
   innermost binder first. *)

Fixpoint VR (rho : atom -> Rel) (env : list Rel) (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar i => nth i env emp_rel v
  | Ty_FVar X => rho X v
  | Ty_Arrow T1 T2 =>
      forall a, value a /\ VR rho env T1 a ->
        exists b, (tm_app v a -->* b) /\ value b /\ VR rho env T2 b
  | Ty_All T1 =>
      forall A, lc_ty_at 0 A ->
      forall S, exists b, (tm_tapp v A -->* b) /\ value b /\ VR rho (S :: env) T1 b
  end.

Definition VRV (rho : atom -> Rel) (env : list Rel) (T : ty) (v : tm) : Prop :=
  value v /\ VR rho env T v.

Definition TR (rho : atom -> Rel) (env : list Rel) (T : ty) (t : tm) : Prop :=
  exists v, (t -->* v) /\ VRV rho env T v.

(* The interpretation only depends on a prefix of [env], as long as the
   type has no free de Bruijn indices beyond that prefix. *)

Lemma VR_env_agree : forall T m rho env1 env2 v,
  lc_ty_at m T ->
  (forall i, i < m -> forall u, nth i env1 emp_rel u <-> nth i env2 emp_rel u) ->
  VR rho env1 T v <-> VR rho env2 T v.
Proof.
  intros T. induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1];
    intros m rho env1 env2 v Hlc Hag; simpl.
  - apply Hag. inversion Hlc. assumption.
  - reflexivity.
  - assert (Hlc1 : lc_ty_at m T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at m T2) by (inversion Hlc; assumption).
    assert (Hag' : forall i, i < m -> forall u, nth i env2 emp_rel u <-> nth i env1 emp_rel u).
    { intros i Hi u. symmetry. apply Hag. assumption. }
    split; intros H a [Hva Hra].
    + apply (proj1 (IH1 m rho env2 env1 a Hlc1 Hag')) in Hra.
      destruct (H a (conj Hva Hra)) as [b [Hs [Hvb Hrb]]].
      exists b. split; [assumption|]. split; [assumption|].
      apply (proj1 (IH2 m rho env1 env2 b Hlc2 Hag)). assumption.
    + apply (proj1 (IH1 m rho env1 env2 a Hlc1 Hag)) in Hra.
      destruct (H a (conj Hva Hra)) as [b [Hs [Hvb Hrb]]].
      exists b. split; [assumption|]. split; [assumption|].
      apply (proj1 (IH2 m rho env2 env1 b Hlc2 Hag')). assumption.
  - assert (Hlc1 : lc_ty_at (S m) T1) by (inversion Hlc; assumption).
    split; intros H A HA Srel.
    + assert (HagS : forall i, i < S m -> forall u,
        nth i (Srel :: env1) emp_rel u <-> nth i (Srel :: env2) emp_rel u).
      { intros i Hi u. destruct i as [|j]; simpl.
        - reflexivity.
        - apply Hag. lia. }
      destruct (H A HA Srel) as [b [Hs [Hvb Hrb]]].
      exists b. split; [assumption|]. split; [assumption|].
      apply (proj1 (IH1 (S m) rho (Srel :: env1) (Srel :: env2) b Hlc1 HagS)). assumption.
    + assert (HagS : forall i, i < S m -> forall u,
        nth i (Srel :: env1) emp_rel u <-> nth i (Srel :: env2) emp_rel u).
      { intros i Hi u. destruct i as [|j]; simpl.
        - reflexivity.
        - apply Hag. lia. }
      destruct (H A HA Srel) as [b [Hs [Hvb Hrb]]].
      exists b. split; [assumption|]. split; [assumption|].
      apply (proj2 (IH1 (S m) rho (Srel :: env1) (Srel :: env2) b Hlc1 HagS)). assumption.
Qed.

Lemma VR_rho_agree : forall T rho1 rho2 env v,
  (forall X, In X (free_ty T) -> forall u, rho1 X u <-> rho2 X u) ->
  VR rho1 env T v <-> VR rho2 env T v.
Proof.
  intros T. induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1];
    intros rho1 rho2 env v Hag; simpl.
  - reflexivity.
  - apply Hag. simpl. auto.
  - assert (Hag1 : forall Y, In Y (free_ty T1) -> forall u, rho1 Y u <-> rho2 Y u).
    { intros Y HY u. apply Hag. simpl. apply in_app_iff. auto. }
    assert (Hag2 : forall Y, In Y (free_ty T2) -> forall u, rho1 Y u <-> rho2 Y u).
    { intros Y HY u. apply Hag. simpl. apply in_app_iff. auto. }
    assert (Hag1' : forall Y, In Y (free_ty T1) -> forall u, rho2 Y u <-> rho1 Y u).
    { intros Y HY u. symmetry. apply Hag1. assumption. }
    assert (Hag2' : forall Y, In Y (free_ty T2) -> forall u, rho2 Y u <-> rho1 Y u).
    { intros Y HY u. symmetry. apply Hag2. assumption. }
    split; intros H a [Hva Hra].
    + apply (proj1 (IH1 rho2 rho1 env a Hag1')) in Hra.
      destruct (H a (conj Hva Hra)) as [b [Hs [Hvb Hrb]]].
      exists b. split; [assumption|]. split; [assumption|].
      apply (proj1 (IH2 rho1 rho2 env b Hag2)). assumption.
    + apply (proj1 (IH1 rho1 rho2 env a Hag1)) in Hra.
      destruct (H a (conj Hva Hra)) as [b [Hs [Hvb Hrb]]].
      exists b. split; [assumption|]. split; [assumption|].
      apply (proj1 (IH2 rho2 rho1 env b Hag2')). assumption.
  - assert (Hag1 : forall Y, In Y (free_ty T1) -> forall u, rho1 Y u <-> rho2 Y u).
    { intros Y HY u. apply Hag. simpl. auto. }
    split; intros H A HA S.
    + destruct (H A HA S) as [b [Hs [Hvb Hrb]]].
      exists b. split; [assumption|]. split; [assumption|].
      apply (proj1 (IH1 rho1 rho2 (S :: env) b Hag1)). assumption.
    + destruct (H A HA S) as [b [Hs [Hvb Hrb]]].
      exists b. split; [assumption|]. split; [assumption|].
      apply (proj2 (IH1 rho1 rho2 (S :: env) b Hag1)). assumption.
Qed.

(* Opening the body of a forall-type corresponds to pushing the
   interpretation of the instantiation type onto the [env] stack. *)

Lemma VR_open_ty_gen : forall T k U rho env v,
  length env = k ->
  lc_ty_at (S k) T ->
  lc_ty_at 0 U ->
  (VR rho (env ++ [fun w => VR rho [] U w]) T v <->
   VR rho env (open_ty_rec k U T) v).
Proof.
  intros T. induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1];
    intros k U rho env v Hlen Hlc HU; simpl.
  - (* Ty_BVar n *)
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. subst k.
      rewrite nth_app_at.
      split; intros H.
      * apply (proj1 (VR_env_agree U 0 rho [] env v HU ltac:(intros i Hi; lia))). exact H.
      * apply (proj2 (VR_env_agree U 0 rho [] env v HU ltac:(intros i Hi; lia))). exact H.
    + apply Nat.eqb_neq in E.
      assert (Hlt : n < S k) by (inversion Hlc; assumption).
      assert (Hn : n < length env) by lia.
      rewrite (nth_app_below n env [fun w => VR rho [] U w] emp_rel Hn).
      reflexivity.
  - (* Ty_FVar *) reflexivity.
  - (* Ty_Arrow *)
    assert (Hlc1 : lc_ty_at (S k) T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at (S k) T2) by (inversion Hlc; assumption).
    split; intros H a [Hva Hra].
    + apply (proj2 (IH1 k U rho env a Hlen Hlc1 HU)) in Hra.
      destruct (H a (conj Hva Hra)) as [b [Hs [Hvb Hrb]]].
      exists b. split; [assumption|]. split; [assumption|].
      apply (proj1 (IH2 k U rho env b Hlen Hlc2 HU)). assumption.
    + apply (proj1 (IH1 k U rho env a Hlen Hlc1 HU)) in Hra.
      destruct (H a (conj Hva Hra)) as [b [Hs [Hvb Hrb]]].
      exists b. split; [assumption|]. split; [assumption|].
      apply (proj2 (IH2 k U rho env b Hlen Hlc2 HU)). assumption.
  - (* Ty_All *)
    assert (Hlc1 : lc_ty_at (S (S k)) T1) by (inversion Hlc; assumption).
    split; intros H A HA Srel.
    + destruct (H A HA Srel) as [b [Hs [Hvb Hrb]]].
      exists b. split; [assumption|]. split; [assumption|].
      apply (proj1 (IH1 (S k) U rho (Srel :: env) b ltac:(simpl; lia) Hlc1 HU)).
      exact Hrb.
    + destruct (H A HA Srel) as [b [Hs [Hvb Hrb]]].
      exists b. split; [assumption|]. split; [assumption|].
      apply (proj2 (IH1 (S k) U rho (Srel :: env) b ltac:(simpl; lia) Hlc1 HU)).
      exact Hrb.
Qed.

(* ------------------------------------------------------------------ *)
(* Locally closed types and terms                                     *)
(* ------------------------------------------------------------------ *)

Lemma lc_ty_open_inv : forall T k U,
  lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  intros T. induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1];
    intros k U H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_ty_bvar. lia.
    + apply Nat.eqb_neq in E. apply lc_ty_bvar. inversion H. lia.
  - apply lc_ty_fvar.
  - inversion H. apply lc_ty_arrow.
    + apply (IH1 k U). assumption.
    + apply (IH2 k U). assumption.
  - inversion H. apply lc_ty_all. apply (IH1 (S k) U). assumption.
Qed.

Lemma lc_ty_open : forall T k U,
  lc_ty_at (S k) T -> lc_ty_at k U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  intros T. induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1];
    intros k U H HU; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact HU.
    + apply Nat.eqb_neq in E. apply lc_ty_bvar. inversion H. lia.
  - apply lc_ty_fvar.
  - inversion H. apply lc_ty_arrow.
    + apply (IH1 k U); assumption.
    + apply (IH2 k U); assumption.
  - inversion H. apply lc_ty_all.
    apply (IH1 (S k) U).
    + assumption.
    + apply lc_ty_mono with (k := k); [assumption | lia].
Qed.

Lemma lc_tm_open_inv : forall T K k u,
  lc_tm_at K k (open_tm_rec k u T) -> lc_tm_at K (S k) T.
Proof.
  intros X0. induction X0 as
    [ n | a | ty0 t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 ty0 | t1 IH1 t2 IH2 ];
    intros K k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_tm_bvar. lia.
    + apply Nat.eqb_neq in E. apply lc_tm_bvar. inversion H. lia.
  - apply lc_tm_fvar.
  - inversion H. apply lc_tm_abs.
    + assumption.
    + apply (IH1 K (S k) u). assumption.
  - inversion H. apply lc_tm_app.
    + apply (IH1 K k u). assumption.
    + apply (IH2 K k u). assumption.
  - inversion H. apply lc_tm_tabs. apply (IH1 (S K) k u). assumption.
  - inversion H. apply lc_tm_tapp.
    + apply (IH1 K k u). assumption.
    + assumption.
  - inversion H. apply lc_tm_choice.
    + apply (IH1 K k u). assumption.
    + apply (IH2 K k u). assumption.
Qed.

Lemma lc_tm_open_ty_inv : forall T K k U,
  lc_tm_at K k (open_tm_ty_rec K U T) -> lc_tm_at (S K) k T.
Proof.
  intros X0. induction X0 as
    [ n | a | ty0 t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 ty0 | t1 IH1 t2 IH2 ];
    intros K k U H; simpl in H.
  - apply lc_tm_bvar. inversion H. assumption.
  - apply lc_tm_fvar.
  - inversion H. apply lc_tm_abs.
    + apply (lc_ty_open_inv ty0 K U). assumption.
    + apply (IH1 K (S k) U). assumption.
  - inversion H. apply lc_tm_app.
    + apply (IH1 K k U). assumption.
    + apply (IH2 K k U). assumption.
  - inversion H. apply lc_tm_tabs. apply (IH1 (S K) k U). assumption.
  - inversion H. apply lc_tm_tapp.
    + apply (IH1 K k U). assumption.
    + apply (lc_ty_open_inv ty0 K U). assumption.
  - inversion H. apply lc_tm_choice.
    + apply (IH1 K k U). assumption.
    + apply (IH2 K k U). assumption.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H as
    [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T Hbody IHbody].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    pose (X := fresh L).
    assert (HX : ~ In X L) by apply fresh_notin.
    specialize (IHbody X HX).
    apply (lc_ty_open_inv T 0 (Ty_FVar X)). exact IHbody.
Qed.

Lemma wf_lc_ty_apply : forall Delta T, wf_ty Delta T ->
  forall sigma, (forall X, lc_ty_at 0 (sigma X)) -> lc_ty_at 0 (ty_apply sigma T).
Proof.
  intros Delta T H. induction H as
    [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T Hbody IHbody];
    intros sigma Hsig.
  - simpl. apply Hsig.
  - simpl. apply lc_ty_arrow; [apply IH1 | apply IH2]; assumption.
  - simpl. apply lc_ty_all.
    pose (X := fresh L).
    assert (HX : ~ In X L) by apply fresh_notin.
    specialize (IHbody X HX sigma Hsig).
    apply (lc_ty_open_inv (ty_apply sigma T) 0 (sigma X)).
    change (lc_ty_at 0 (open_ty_rec 0 (ty_apply sigma (Ty_FVar X)) (ty_apply sigma T))).
    rewrite <- (ty_apply_open_rec sigma Hsig 0 (Ty_FVar X) T).
    exact IHbody.
Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T, has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H. induction H as
    [ Delta Gamma x T Hlk Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IHt HU
    | Delta Gamma t1 t2 T H1 IH1 H2 IH2 ].
  - apply (wf_ty_lc Delta T). assumption.
  - apply lc_ty_arrow.
    + apply (wf_ty_lc Delta T1). assumption.
    + apply (IHbody (fresh L)). apply fresh_notin.
  - inversion IH1. assumption.
  - apply lc_ty_all.
    pose (X := fresh L).
    assert (HX : ~ In X L) by apply fresh_notin.
    specialize (IHbody X HX).
    apply (lc_ty_open_inv T 0 (Ty_FVar X)). exact IHbody.
  - apply (lc_ty_open T 0 U).
    + inversion IHt. assumption.
    + apply (wf_ty_lc Delta U). assumption.
  - assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Multi-step reductions                                              *)
(* ------------------------------------------------------------------ *)

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H. induction H as [x | x y z Hstep Hrest IH]; intros H2.
  - exact H2.
  - apply multi_step with (y := y); [exact Hstep | apply IH; exact H2].
Qed.

Lemma multi_app1 : forall t1 t1' t2,
  t1 -->* t1' -> locally_closed_tm t2 -> tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 Hs. induction Hs as [x | x y z Hstep Hrest IH]; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (y := tm_app y t2).
    + apply ST_App1; assumption.
    + apply IH. assumption.
Qed.

Lemma multi_app2 : forall v1 t2 t2',
  value v1 -> t2 -->* t2' -> tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv Hs. induction Hs as [x | x y z Hstep Hrest IH].
  - apply multi_refl.
  - apply multi_step with (y := tm_app v1 y).
    + apply ST_App2; assumption.
    + apply IH.
Qed.

Lemma multi_tapp : forall t t' T,
  t -->* t' -> locally_closed_ty T -> tm_tapp t T -->* tm_tapp t' T.
Proof.
  intros t t' T Hs. induction Hs as [x | x y z Hstep Hrest IH]; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (y := tm_tapp y T).
    + apply ST_TApp; assumption.
    + apply IH. assumption.
Qed.

Lemma multi_choice_left : forall t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 -> tm_choice t1 t2 -->* t1.
Proof.
  intros t1 t2 H1 H2.
  apply multi_step with (y := t1); [apply ST_ChoiceLeft; assumption | apply multi_refl].
Qed.

Lemma multi_choice_right : forall t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 -> tm_choice t1 t2 -->* t2.
Proof.
  intros t1 t2 H1 H2.
  apply multi_step with (y := t2); [apply ST_ChoiceRight; assumption | apply multi_refl].
Qed.

Lemma fresh_notin_2 : forall (l1 l2 : list atom) (x : atom),
  x = fresh (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros l1 l2 x Heq. subst x. split.
  - apply fresh_notin_app1.
  - apply fresh_notin_app2.
Qed.

Lemma fresh_notin_4 : forall (l1 l2 l3 l4 : list atom) (x : atom),
  x = fresh (l1 ++ l2 ++ l3 ++ l4) ->
  ~ In x l1 /\ ~ In x l2 /\ ~ In x l3 /\ ~ In x l4.
Proof.
  intros l1 l2 l3 l4 x Heq. subst x. repeat split.
  - intro H. apply (fresh_notin (l1 ++ l2 ++ l3 ++ l4)).
    apply in_app_iff. left. exact H.
  - intro H. apply (fresh_notin (l1 ++ l2 ++ l3 ++ l4)).
    apply in_app_iff. right. apply in_app_iff. left. exact H.
  - intro H. apply (fresh_notin (l1 ++ l2 ++ l3 ++ l4)).
    apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. exact H.
  - intro H. apply (fresh_notin (l1 ++ l2 ++ l3 ++ l4)).
    apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact H.
Qed.

Lemma lookup_free_ty_ctx : forall Gamma y T',
  lookup_context y Gamma = Some T' ->
  forall X, In X (free_ty T') -> In X (free_ty_ctx Gamma).
Proof.
  intros Gamma. induction Gamma as [| [z U] Gamma' IH]; intros y T' Hlk X HX.
  - simpl in Hlk. discriminate.
  - simpl in Hlk. destruct (Nat.eqb y z) eqn:E.
    + injection Hlk as HTeq. subst T'. simpl. apply in_app_iff. left. assumption.
    + simpl. apply in_app_iff. right. eapply IH; eauto.
Qed.

(* Substitution preserves local closedness. *)
Lemma lc_subst_tm : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sigma gamma,
    (forall X, lc_ty_at 0 (sigma X)) ->
    (forall x, locally_closed_tm (gamma x)) ->
    locally_closed_tm (tm_apply sigma gamma t).
Proof.
  intros Delta Gamma t T H. induction H as
    [ Delta Gamma x T Hlk Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IHt HU
    | Delta Gamma t1 t2 T H1 IH1 H2 IH2 ];
    intros sigma gamma Hsig Hglc.
  - simpl. apply Hglc.
  - simpl. apply lc_tm_abs.
    + apply (wf_lc_ty_apply Delta T1 Hwf sigma Hsig).
    + pose (x := fresh (L ++ free_tm_tm t2)).
      destruct (fresh_notin_2 L (free_tm_tm t2) x eq_refl) as [HxL HxT].
      set (c0 := tm_abs (Ty_FVar 0) (tm_bvar 0)).
      assert (Hc0 : locally_closed_tm c0).
      { unfold c0. apply lc_tm_abs. apply lc_ty_fvar. apply lc_tm_bvar. lia. }
      set (gamma' := fun y => if Nat.eqb y x then c0 else gamma y).
      assert (Hglc' : forall y, locally_closed_tm (gamma' y)).
      { intros y. unfold gamma'. destruct (Nat.eqb y x). apply Hc0. apply Hglc. }
      specialize (IHbody x HxL sigma gamma' Hsig Hglc').
      rewrite (tm_apply_open_tm sigma gamma' Hglc') in IHbody.
      assert (Hgx : tm_apply sigma gamma' (tm_fvar x) = c0).
      { simpl. unfold gamma'. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hgx in IHbody.
      assert (Hagree : tm_apply sigma gamma' t2 = tm_apply sigma gamma t2).
      { apply tm_apply_agree.
        - intros X HX. reflexivity.
        - intros y Hy. unfold gamma'. destruct (Nat.eqb y x) eqn:E.
          + apply Nat.eqb_eq in E. subst y. exfalso. apply HxT. assumption.
          + reflexivity. }
      rewrite Hagree in IHbody.
      apply (lc_tm_open_inv (tm_apply sigma gamma t2) 0 0 c0). exact IHbody.
  - simpl. apply lc_tm_app.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - simpl. apply lc_tm_tabs.
    pose (X := fresh (L ++ free_ty_tm t)).
    destruct (fresh_notin_2 L (free_ty_tm t) X eq_refl) as [HXL HXT].
    set (sigma' := fun Y => if Nat.eqb Y X then Ty_FVar 0 else sigma Y).
    assert (Hsig' : forall Y, lc_ty_at 0 (sigma' Y)).
    { intros Y. unfold sigma'. destruct (Nat.eqb Y X). apply lc_ty_fvar. apply Hsig. }
    specialize (IHbody X HXL sigma' gamma Hsig' Hglc).
    rewrite (tm_apply_open_tm_ty sigma' gamma Hsig' Hglc) in IHbody.
    assert (Hsx : ty_apply sigma' (Ty_FVar X) = Ty_FVar 0).
    { simpl. unfold sigma'. rewrite Nat.eqb_refl. reflexivity. }
    rewrite Hsx in IHbody.
    assert (Hagree : tm_apply sigma' gamma t = tm_apply sigma gamma t).
    { apply tm_apply_agree.
      - intros Y HY. unfold sigma'. destruct (Nat.eqb Y X) eqn:E.
        + apply Nat.eqb_eq in E. subst Y. exfalso. apply HXT. assumption.
        + reflexivity.
      - intros y Hy. reflexivity. }
    rewrite Hagree in IHbody.
    apply (lc_tm_open_ty_inv (tm_apply sigma gamma t) 0 0 (Ty_FVar 0)). exact IHbody.
  - simpl. apply lc_tm_tapp.
    + apply IHt; assumption.
    + apply (wf_lc_ty_apply Delta U HU sigma Hsig).
  - simpl. apply lc_tm_choice.
    + apply IH1; assumption.
    + apply IH2; assumption.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed_tm v.
Proof. intros v H. inversion H; assumption. Qed.

(* ------------------------------------------------------------------ *)
(* The fundamental theorem of the logical relation                    *)
(* ------------------------------------------------------------------ *)

Theorem fundamental_relation : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sigma rho gamma,
    (forall X, lc_ty_at 0 (sigma X)) ->
    (forall x, locally_closed_tm (gamma x)) ->
    (forall x T', lookup_context x Gamma = Some T' -> VRV rho [] T' (gamma x)) ->
    TR rho [] T (tm_apply sigma gamma t).
Proof.
  intros Delta Gamma t T H. induction H as
    [ Delta Gamma x T Hlk Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IHt HU
    | Delta Gamma t1 t2 T H1 IH1 H2 IH2 ];
    intros sigma rho gamma Hsig Hglc Henv.
  - (* T_Var *)
    simpl. unfold TR. exists (gamma x). split.
    + apply multi_refl.
    + apply Henv. exact Hlk.
  - (* T_Abs *)
    pose (body := tm_apply sigma gamma t2).
    pose (ty1 := ty_apply sigma T1).
    assert (Hjudge : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)).
    { apply T_Abs with (L := L); [exact Hwf | exact Hbody]. }
    pose proof (lc_subst_tm Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2) Hjudge sigma gamma Hsig Hglc) as Hlcabs.
    change (locally_closed_tm (tm_abs ty1 body)) in Hlcabs.
    unfold TR. exists (tm_abs ty1 body). split.
    + apply multi_refl.
    + split.
      * apply v_abs. exact Hlcabs.
      * intros a [Hvala Hra].
        pose (x := fresh (L ++ free_tm_tm t2)).
        destruct (fresh_notin_2 L (free_tm_tm t2) x eq_refl) as [HxL HxT].
        set (gamma' := fun y => if Nat.eqb y x then a else gamma y).
        assert (Hglc' : forall y, locally_closed_tm (gamma' y)).
        { intros y. unfold gamma'. destruct (Nat.eqb y x).
          - apply value_locally_closed. exact Hvala.
          - apply Hglc. }
        assert (Henv' : forall y T', lookup_context y ((x, T1) :: Gamma) = Some T' -> VRV rho [] T' (gamma' y)).
        { intros y T' Hlk. simpl in Hlk. destruct (Nat.eqb y x) eqn:E.
          - injection Hlk as HTeq. subst T'. unfold gamma'. rewrite E. exact (conj Hvala Hra).
          - unfold gamma'. rewrite E. apply Henv. exact Hlk. }
        destruct (IHbody x HxL sigma rho gamma' Hsig Hglc' Henv') as [b [Hstep Hvb]].
        rewrite (tm_apply_open_tm sigma gamma' Hglc') in Hstep.
        assert (Hgx : tm_apply sigma gamma' (tm_fvar x) = a).
        { simpl. unfold gamma'. rewrite Nat.eqb_refl. reflexivity. }
        rewrite Hgx in Hstep.
        assert (Hagree : tm_apply sigma gamma' t2 = body).
        { unfold body. apply tm_apply_agree.
          - intros X HX. reflexivity.
          - intros y Hy. unfold gamma'. destruct (Nat.eqb y x) eqn:E.
            + apply Nat.eqb_eq in E. subst y. exfalso. apply HxT. assumption.
            + reflexivity. }
        rewrite Hagree in Hstep.
        exists b. split.
        { apply multi_step with (y := open_tm body a).
          - apply ST_AppAbs; [exact Hlcabs | exact Hvala].
          - exact Hstep. }
        { exact Hvb. }
  - (* T_App *)
    simpl.
    destruct (IH1 sigma rho gamma Hsig Hglc Henv) as [v1 [Hs1 Hv1]].
    destruct (IH2 sigma rho gamma Hsig Hglc Henv) as [v2 [Hs2 Hv2]].
    destruct Hv1 as [Hval1 HR1]. destruct Hv2 as [Hval2 HR2].
    assert (Hjudge : has_type Delta Gamma (tm_app t1 t2) T2).
    { apply T_App with (T1 := T1); assumption. }
    pose proof (lc_subst_tm Delta Gamma (tm_app t1 t2) T2 Hjudge sigma gamma Hsig Hglc) as Hlc.
    assert (Hlc2 : locally_closed_tm (tm_apply sigma gamma t2)).
    { change (lc_tm_at 0 0 (tm_app (tm_apply sigma gamma t1) (tm_apply sigma gamma t2))) in Hlc.
      inversion Hlc. assumption. }
    destruct (HR1 v2 (conj Hval2 HR2)) as [b [Hstep [Hvalb HRb]]].
    exists b. split.
    + apply multi_trans with (b := tm_app v1 v2).
      * apply multi_trans with (b := tm_app v1 (tm_apply sigma gamma t2)).
        -- apply multi_app1; assumption.
        -- apply multi_app2; assumption.
      * exact Hstep.
    + split; [exact Hvalb | exact HRb].
  - (* T_TAbs *)
    pose (s := tm_apply sigma gamma t).
    assert (Hjudge : has_type Delta Gamma (tm_tabs t) (Ty_All T)).
    { apply T_TAbs with (L := L); exact Hbody. }
    pose proof (lc_subst_tm Delta Gamma (tm_tabs t) (Ty_All T) Hjudge sigma gamma Hsig Hglc) as Hlcabs.
    change (locally_closed_tm (tm_tabs s)) in Hlcabs.
    pose proof (has_type_lc_ty Delta Gamma (tm_tabs t) (Ty_All T) Hjudge) as Hlc0.
    assert (HlcT : lc_ty_at 1 T).
    { inversion Hlc0. assumption. }
    unfold TR. exists (tm_tabs s). split.
    + apply multi_refl.
    + split.
      * apply v_tabs. exact Hlcabs.
      * intros A HA Srel.
        pose (X := fresh (L ++ free_ty T ++ free_ty_ctx Gamma ++ free_ty_tm t)).
        destruct (fresh_notin_4 L (free_ty T) (free_ty_ctx Gamma) (free_ty_tm t) X eq_refl)
          as [HXL [HXF [HXG HXT]]].
        set (sigma' := fun Y => if Nat.eqb Y X then A else sigma Y).
        set (rho' := fun Y => if Nat.eqb Y X then Srel else rho Y).
        assert (Hsig' : forall Y, lc_ty_at 0 (sigma' Y)).
        { intros Y. unfold sigma'. destruct (Nat.eqb Y X). exact HA. apply Hsig. }
        assert (Henv' : forall y T', lookup_context y Gamma = Some T' -> VRV rho' [] T' (gamma y)).
        { intros y T' Hlk. destruct (Henv y T' Hlk) as [Hvaly HRy]. split; [assumption|].
          assert (Hag : forall Y, In Y (free_ty T') -> forall u, rho Y u <-> rho' Y u).
          { intros Y HY u. simpl. unfold rho'. destruct (Nat.eqb Y X) eqn:E.
            + apply Nat.eqb_eq in E. subst Y. exfalso. apply HXG.
              eapply lookup_free_ty_ctx; eauto.
            + reflexivity. }
          apply (proj1 (VR_rho_agree T' rho rho' [] (gamma y) Hag)). exact HRy. }
        destruct (IHbody X HXL sigma' rho' gamma Hsig' Hglc Henv') as [b' [Hstep' Hvb']].
        assert (Hsx : ty_apply sigma' (Ty_FVar X) = A).
        { simpl. unfold sigma'. rewrite Nat.eqb_refl. reflexivity. }
        assert (Hagree : tm_apply sigma' gamma t = s).
        { unfold s. apply tm_apply_agree.
          - intros Y HY. unfold sigma'. destruct (Nat.eqb Y X) eqn:E.
            + apply Nat.eqb_eq in E. subst Y. exfalso. apply HXT. assumption.
            + reflexivity.
          - intros y Hy. reflexivity. }
        rewrite (tm_apply_open_tm_ty sigma' gamma Hsig' Hglc) in Hstep'.
        rewrite Hsx in Hstep'.
        rewrite Hagree in Hstep'.
        destruct Hvb' as [Hvalb' HRb'].
        exists b'. split.
        { apply multi_step with (y := open_tm_ty s A).
          - apply ST_TAppTabs; [exact Hlcabs | exact HA].
          - exact Hstep'. }
        { split; [exact Hvalb'|].
          assert (Hag : forall Y, In Y (free_ty T) -> forall u, rho' Y u <-> rho Y u).
          { intros Y HY u. simpl. unfold rho'. destruct (Nat.eqb Y X) eqn:E.
            + apply Nat.eqb_eq in E. subst Y. exfalso. apply HXF. assumption.
            + reflexivity. }
          apply (proj1 (VR_rho_agree T rho' rho [Srel] b' Hag)).
          assert (Hag1 : forall i, i < 1 ->
            forall u, nth i [fun w => VR rho' [] (Ty_FVar X) w] emp_rel u <->
                      nth i [Srel] emp_rel u).
          { intros i Hi u. destruct i as [|j]; simpl.
            + change (rho' X u <-> Srel u). unfold rho'. rewrite Nat.eqb_refl. reflexivity.
            + reflexivity. }
          apply (proj1 (VR_env_agree T 1 rho' [fun w => VR rho' [] (Ty_FVar X) w] [Srel] b' HlcT Hag1)).
          apply (proj2 (VR_open_ty_gen T 0 (Ty_FVar X) rho' [] b' eq_refl HlcT (lc_ty_fvar 0 X))).
          exact HRb'. }
  - (* T_TApp *)
    simpl.
    destruct (IHt sigma rho gamma Hsig Hglc Henv) as [v1 [Hs1 Hv1]].
    destruct Hv1 as [Hval1 HR1].
    pose (A := ty_apply sigma U).
    pose (Srel := fun w => VR rho [] U w).
    assert (HA : lc_ty_at 0 A) by (apply (wf_lc_ty_apply Delta U HU sigma Hsig)).
    destruct (HR1 A HA Srel) as [b [Hstep [Hvalb HRb]]].
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (has_type_lc_ty Delta Gamma t (Ty_All T) Ht) as H0. inversion H0. assumption. }
    assert (HUlc : lc_ty_at 0 U) by (apply (wf_ty_lc Delta U HU)).
    exists b. split.
    + apply multi_trans with (b := tm_tapp v1 A).
      * apply multi_tapp; assumption.
      * exact Hstep.
    + split; [exact Hvalb|].
      apply (proj1 (VR_open_ty_gen T 0 U rho [] b eq_refl HlcT HUlc)).
      exact HRb.
  - (* T_Choice *)
    simpl.
    destruct (IH1 sigma rho gamma Hsig Hglc Henv) as [v1 [Hs1 Hv1]].
    assert (Hjudge : has_type Delta Gamma (tm_choice t1 t2) T).
    { apply T_Choice; assumption. }
    pose proof (lc_subst_tm Delta Gamma (tm_choice t1 t2) T Hjudge sigma gamma Hsig Hglc) as Hlc.
    assert (Hlc12 : locally_closed_tm (tm_apply sigma gamma t1) /\
                    locally_closed_tm (tm_apply sigma gamma t2)).
    { change (lc_tm_at 0 0 (tm_choice (tm_apply sigma gamma t1) (tm_apply sigma gamma t2))) in Hlc.
      inversion Hlc. split; assumption. }
    destruct Hlc12 as [Hlc1 Hlc2].
    exists v1. split.
    + apply multi_trans with (b := tm_apply sigma gamma t1).
      * apply multi_choice_left; assumption.
      * exact Hs1.
    + exact Hv1.
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
  intros t Ht U v Hwf Hval Hvty.
  assert (Hsig0 : forall X, lc_ty_at 0 (Ty_FVar X)) by (intro X; apply lc_ty_fvar).
  assert (Hglc0 : forall x, locally_closed_tm (tm_fvar x)) by (intro x; apply lc_tm_fvar).
  assert (Henv0 : forall x T',
    lookup_context x empty = Some T' -> VRV (fun (_ : atom) (_ : tm) => False) [] T' (tm_fvar x)).
  { intros x T' Hlk. simpl in Hlk. discriminate. }
  destruct (fundamental_relation [] empty t
              (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
              (fun X => Ty_FVar X) (fun (_ : atom) (_ : tm) => False) (fun x => tm_fvar x)
              Hsig0 Hglc0 Henv0) as [w [Hstw Hvw]].
  rewrite tm_apply_identity in Hstw.
  destruct Hvw as [Hvalw HRw].
  assert (HUlc : lc_ty_at 0 U) by (apply (wf_ty_lc [] U Hwf)).
  set (Sv := fun (a : tm) => a = v).
  destruct (HRw U HUlc Sv) as [b [Hstep [Hvalb HRb]]].
  assert (Hvv : value v /\ VR (fun (_ : atom) (_ : tm) => False) [Sv] (Ty_BVar 0) v).
  { split; [exact Hval|]. simpl. unfold Sv. reflexivity. }
  destruct (HRb v Hvv) as [c [Hstep2 [Hvalc HRc]]].
  simpl in HRc. unfold Sv in HRc. subst c.
  assert (Hlcv : locally_closed_tm v) by (apply value_locally_closed; exact Hval).
  apply multi_trans with (b := tm_app (tm_tapp w U) v).
  - apply multi_app1.
    + apply multi_tapp; assumption.
    + exact Hlcv.
  - apply multi_trans with (b := tm_app b v).
    + apply multi_app1; [exact Hstep | exact Hlcv].
    + exact Hstep2.
Qed.

End SystemFParametricityNondeterminismHardTask.
