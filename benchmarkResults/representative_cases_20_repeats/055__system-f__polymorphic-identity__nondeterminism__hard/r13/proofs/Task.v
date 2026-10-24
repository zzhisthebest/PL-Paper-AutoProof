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
(* Infrastructure for the free theorem proof.                   *)
(* ============================================================ *)

(* ---------------- fresh atoms ---------------- *)

Fixpoint max_list (l : list atom) : atom :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (max_list l')
  end.

Definition fresh (l : list atom) : atom := S (max_list l).

Lemma max_list_ge : forall l x, In x l -> x <= max_list l.
Proof.
  induction l as [|a l IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH, Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall l, ~ In (fresh l) l.
Proof.
  intros l Hin. unfold fresh in Hin.
  pose proof (max_list_ge l _ Hin). lia.
Qed.

Lemma not_in_app_l : forall (a : atom) (l1 l2 : list atom), ~ In a (l1 ++ l2) -> ~ In a l1.
Proof. intros a l1 l2 H Hin. apply H. apply in_or_app. left. assumption. Qed.

Lemma not_in_app_r : forall (a : atom) (l1 l2 : list atom), ~ In a (l1 ++ l2) -> ~ In a l2.
Proof. intros a l1 l2 H Hin. apply H. apply in_or_app. right. assumption. Qed.

Lemma fresh_not_in_app_l : forall a b, ~ In (fresh (a ++ b)) a.
Proof.
  intros a b H. apply (fresh_not_in (a ++ b)). apply in_or_app. left. assumption.
Qed.

Lemma fresh_not_in_app_r : forall a b, ~ In (fresh (a ++ b)) b.
Proof.
  intros a b H. apply (fresh_not_in (a ++ b)). apply in_or_app. right. assumption.
Qed.

(* ---------------- free variable collection ---------------- *)

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_fvars T1 ++ ty_fvars T2
  | Ty_All T1 => ty_fvars T1
  end.

Fixpoint tm_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => tm_fvars t1
  | tm_app t1 t2 => tm_fvars t1 ++ tm_fvars t2
  | tm_tabs t1 => tm_fvars t1
  | tm_tapp t1 _ => tm_fvars t1
  | tm_choice t1 t2 => tm_fvars t1 ++ tm_fvars t2
  end.

Fixpoint tm_ty_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T t1 => ty_fvars T ++ tm_ty_fvars t1
  | tm_app t1 t2 => tm_ty_fvars t1 ++ tm_ty_fvars t2
  | tm_tabs t1 => tm_ty_fvars t1
  | tm_tapp t1 T => tm_ty_fvars t1 ++ ty_fvars T
  | tm_choice t1 t2 => tm_ty_fvars t1 ++ tm_ty_fvars t2
  end.

Fixpoint ctx_ty_fvars (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: G => ty_fvars T ++ ctx_ty_fvars G
  end.

(* ---------------- simultaneous substitution ---------------- *)

Fixpoint tysubst (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sigma X
  | Ty_Arrow T1 T2 => Ty_Arrow (tysubst sigma T1) (tysubst sigma T2)
  | Ty_All T1 => Ty_All (tysubst sigma T1)
  end.

Fixpoint tsubst (theta : atom -> tm) (sigma : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => theta x
  | tm_abs T t1 => tm_abs (tysubst sigma T) (tsubst theta sigma t1)
  | tm_app t1 t2 => tm_app (tsubst theta sigma t1) (tsubst theta sigma t2)
  | tm_tabs t1 => tm_tabs (tsubst theta sigma t1)
  | tm_tapp t1 T => tm_tapp (tsubst theta sigma t1) (tysubst sigma T)
  | tm_choice t1 t2 => tm_choice (tsubst theta sigma t1) (tsubst theta sigma t2)
  end.

Definition id_ty : atom -> ty := fun X => Ty_FVar X.
Definition id_tm : atom -> tm := fun x => tm_fvar x.

Definition upd_ty (sigma : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb Y X then U else sigma Y.

Definition upd_tm (theta : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else theta y.

Definition upd_rel (rho : atom -> tm -> tm -> Prop) (X : atom)
    (R : tm -> tm -> Prop) : atom -> tm -> tm -> Prop :=
  fun Y => if Nat.eqb Y X then R else rho Y.

Lemma eqb_sym : forall n m, (n =? m) = (m =? n).
Proof.
  intros n m.
  destruct (Nat.eqb n m) eqn:E; destruct (Nat.eqb m n) eqn:E'.
  - reflexivity.
  - apply Nat.eqb_eq in E. apply Nat.eqb_neq in E'. subst. exfalso; apply E'; reflexivity.
  - apply Nat.eqb_eq in E'. apply Nat.eqb_neq in E. subst. exfalso; apply E; reflexivity.
  - reflexivity.
Qed.

(* ---------------- monotonicity of local closure ---------------- *)

Lemma lc_ty_bvar_inv : forall k n, lc_ty_at k (Ty_BVar n) -> n < k.
Proof. intros k n H. inversion H. assumption. Qed.

Lemma lc_ty_arrow_inv : forall k T1 T2,
  lc_ty_at k (Ty_Arrow T1 T2) -> lc_ty_at k T1 /\ lc_ty_at k T2.
Proof. intros k T1 T2 H. inversion H; subst; auto. Qed.

Lemma lc_ty_all_inv : forall k T, lc_ty_at k (Ty_All T) -> lc_ty_at (S k) T.
Proof. intros k T H. inversion H; subst; auto. Qed.

Lemma lc_ty_mono : forall T k m, k <= m -> lc_ty_at k T -> lc_ty_at m T.
Proof.
  induction T; intros k m Hle H.
  - inversion H. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion H; subst. apply lc_ty_arrow.
    + apply IHT1 with (k := k); [exact Hle | assumption].
    + apply IHT2 with (k := k); [exact Hle | assumption].
  - inversion H; subst. apply lc_ty_all.
    apply IHT with (k := S k); [lia | assumption].
Qed.

Lemma lc_tm_mono : forall t K K' k k',
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  induction t; intros K K' k k' HK Hk H.
  - inversion H. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + eapply lc_ty_mono; [exact HK | assumption].
    + apply IHt with (K := K) (k := S k); [exact HK | lia | assumption].
  - inversion H; subst. apply lc_tm_app.
    + apply IHt1 with (K := K) (k := k); assumption.
    + apply IHt2 with (K := K) (k := k); assumption.
  - inversion H; subst. apply lc_tm_tabs.
    apply IHt with (K := S K) (k := k); [lia | exact Hk | assumption].
  - inversion H; subst. apply lc_tm_tapp.
    + apply IHt with (K := K) (k := k); assumption.
    + eapply lc_ty_mono; [exact HK | assumption].
  - inversion H; subst. apply lc_tm_choice.
    + apply IHt1 with (K := K) (k := k); assumption.
    + apply IHt2 with (K := K) (k := k); assumption.
Qed.

(* ---------------- closure of substitution ---------------- *)

Lemma lc_ty_subst_gen : forall T k sigma,
  lc_ty_at k T ->
  (forall X, lc_ty_at 0 (sigma X)) ->
  lc_ty_at k (tysubst sigma T).
Proof.
  induction T; intros k sigma Hlc Hsig; simpl.
  - inversion Hlc. apply lc_ty_bvar. lia.
  - apply lc_ty_mono with (k := 0); [lia | apply Hsig].
  - inversion Hlc; subst; clear Hlc. apply lc_ty_arrow.
    + apply IHT1; assumption.
    + apply IHT2; assumption.
  - inversion Hlc; subst; clear Hlc. apply lc_ty_all.
    apply IHT; assumption.
Qed.

Lemma lc_tm_subst_gen : forall t K k theta sigma,
  lc_tm_at K k t ->
  (forall X, lc_ty_at 0 (sigma X)) ->
  (forall x, lc_tm_at 0 0 (theta x)) ->
  lc_tm_at K k (tsubst theta sigma t).
Proof.
  induction t; intros K k theta sigma Hlc Hsig Hth; simpl.
  - inversion Hlc. apply lc_tm_bvar. lia.
  - eapply lc_tm_mono; [| | apply Hth]; lia.
  - inversion Hlc; subst; clear Hlc. apply lc_tm_abs.
    + eapply lc_ty_subst_gen; [eassumption | apply Hsig].
    + apply IHt with (K := K) (k := S k); assumption.
  - inversion Hlc; subst; clear Hlc. apply lc_tm_app.
    + apply IHt1 with (K := K) (k := k); assumption.
    + apply IHt2 with (K := K) (k := k); assumption.
  - inversion Hlc; subst; clear Hlc. apply lc_tm_tabs.
    apply IHt with (K := S K) (k := k); assumption.
  - inversion Hlc; subst; clear Hlc. apply lc_tm_tapp.
    + apply IHt with (K := K) (k := k); assumption.
    + eapply lc_ty_subst_gen; [eassumption | apply Hsig].
  - inversion Hlc; subst; clear Hlc. apply lc_tm_choice.
    + apply IHt1 with (K := K) (k := k); assumption.
    + apply IHt2 with (K := K) (k := k); assumption.
Qed.

(* ---------------- opening of closed things is the identity ---------------- *)

Lemma open_ty_rec_lc : forall T k U, lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  induction T; intros k U Hlc; simpl.
  - inversion Hlc. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst; clear Hlc.
    rewrite IHT1; [| assumption].
    rewrite IHT2; [reflexivity | assumption].
  - inversion Hlc; subst; clear Hlc.
    rewrite IHT; [reflexivity | assumption].
Qed.

Lemma open_tm_rec_lc : forall t K k u, lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  induction t; intros K k u Hlc; simpl.
  - inversion Hlc. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst; clear Hlc.
    rewrite IHt with (K := K); [reflexivity | assumption].
  - inversion Hlc; subst; clear Hlc.
    rewrite IHt1 with (K := K); [| assumption].
    rewrite IHt2 with (K := K); [reflexivity | assumption].
  - inversion Hlc; subst; clear Hlc.
    rewrite IHt with (K := S K); [reflexivity | assumption].
  - inversion Hlc; subst; clear Hlc.
    rewrite IHt with (K := K); [reflexivity | assumption].
  - inversion Hlc; subst; clear Hlc.
    rewrite IHt1 with (K := K); [| assumption].
    rewrite IHt2 with (K := K); [reflexivity | assumption].
Qed.

Lemma open_tm_ty_rec_lc_gen : forall t K j k U,
  K <= k -> lc_tm_at K j t -> open_tm_ty_rec k U t = t.
Proof.
  induction t; intros K j k U HK Hlc; simpl.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst; clear Hlc. rewrite open_ty_rec_lc with (k := k).
    + rewrite IHt with (K := K) (j := S j); [reflexivity | exact HK | assumption].
    + apply lc_ty_mono with (k := K); [exact HK | assumption].
  - inversion Hlc; subst; clear Hlc. rewrite IHt1 with (K := K) (j := j); [| exact HK | assumption].
    rewrite IHt2 with (K := K) (j := j); [reflexivity | exact HK | assumption].
  - inversion Hlc; subst; clear Hlc.
    rewrite IHt with (K := S K) (j := j) (k := S k); [reflexivity | lia | assumption].
  - inversion Hlc; subst; clear Hlc. rewrite IHt with (K := K) (j := j); [| exact HK | assumption].
    rewrite open_ty_rec_lc with (k := k).
    + reflexivity.
    + apply lc_ty_mono with (k := K); [exact HK | assumption].
  - inversion Hlc; subst; clear Hlc. rewrite IHt1 with (K := K) (j := j); [| exact HK | assumption].
    rewrite IHt2 with (K := K) (j := j); [reflexivity | exact HK | assumption].
Qed.

(* ---------------- substitution commutes with opening ---------------- *)

Lemma tysubst_open_ty_rec : forall sigma k U T,
  (forall X, lc_ty_at 0 (sigma X)) ->
  tysubst sigma (open_ty_rec k U T) = open_ty_rec k (tysubst sigma U) (tysubst sigma T).
Proof.
  intros sigma k U T. revert k U.
  induction T; intros k U Hsig; simpl.
  - destruct (Nat.eqb k n) eqn:E; reflexivity.
  - rewrite open_ty_rec_lc with (k := k) (U := tysubst sigma U).
    + reflexivity.
    + apply lc_ty_mono with (k := 0); [lia | apply Hsig].
  - rewrite IHT1; [| assumption].
    rewrite IHT2; [reflexivity | assumption].
  - rewrite IHT; [reflexivity | assumption].
Qed.

Lemma tsubst_open_tm_rec : forall theta sigma k u t,
  (forall x, lc_tm_at 0 0 (theta x)) ->
  tsubst theta sigma (open_tm_rec k u t) =
  open_tm_rec k (tsubst theta sigma u) (tsubst theta sigma t).
Proof.
  intros theta sigma k u t. revert k u.
  induction t; intros k u Hth; simpl.
  - destruct (Nat.eqb k n) eqn:E; reflexivity.
  - rewrite open_tm_rec_lc with (K := 0) (k := k) (u := tsubst theta sigma u).
    + reflexivity.
    + apply lc_tm_mono with (K := 0) (k := 0); [lia | lia | apply Hth].
  - rewrite IHt; [reflexivity | assumption].
  - rewrite IHt1; [| assumption]. rewrite IHt2; [reflexivity | assumption].
  - rewrite IHt; [reflexivity | assumption].
  - rewrite IHt; [reflexivity | assumption].
  - rewrite IHt1; [| assumption]. rewrite IHt2; [reflexivity | assumption].
Qed.

Lemma tsubst_open_tm_ty_rec : forall theta sigma k U t,
  (forall X, lc_ty_at 0 (sigma X)) ->
  (forall x, lc_tm_at 0 0 (theta x)) ->
  tsubst theta sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (tysubst sigma U) (tsubst theta sigma t).
Proof.
  intros theta sigma k U t. revert k U.
  induction t; intros k U Hsig Hth; simpl.
  - reflexivity.
  - rewrite open_tm_ty_rec_lc_gen with (K := 0) (j := 0) (k := k).
    + reflexivity.
    + lia.
    + apply Hth.
  - rewrite IHt; [| assumption | assumption].
    rewrite tysubst_open_ty_rec; [reflexivity | assumption].
  - rewrite IHt1; [| assumption | assumption].
    rewrite IHt2; [reflexivity | assumption | assumption].
  - rewrite IHt; [reflexivity | assumption | assumption].
  - rewrite IHt; [| assumption | assumption].
    rewrite tysubst_open_ty_rec; [reflexivity | assumption].
  - rewrite IHt1; [| assumption | assumption].
    rewrite IHt2; [reflexivity | assumption | assumption].
Qed.

(* ---------------- agreement of substitutions ---------------- *)

Lemma tysubst_agree : forall sigma sigma' T,
  (forall X, In X (ty_fvars T) -> sigma X = sigma' X) ->
  tysubst sigma T = tysubst sigma' T.
Proof.
  induction T; intros Hag; simpl.
  - reflexivity.
  - apply Hag. simpl; auto.
  - rewrite IHT1.
    + rewrite IHT2.
      * reflexivity.
      * intros X Hin. apply Hag. simpl. apply in_or_app. right. assumption.
    + intros X Hin. apply Hag. simpl. apply in_or_app. left. assumption.
  - rewrite IHT.
    + reflexivity.
    + intros X Hin. apply Hag. simpl. assumption.
Qed.

Lemma tsubst_agree : forall theta theta' sigma sigma' t,
  (forall x, In x (tm_fvars t) -> theta x = theta' x) ->
  (forall X, In X (tm_ty_fvars t) -> sigma X = sigma' X) ->
  tsubst theta sigma t = tsubst theta' sigma' t.
Proof.
  induction t as [n | x | T1 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T1 | t1 IHt1 t2 IHt2];
    intros Ht Hs; simpl.
  - reflexivity.
  - apply Ht. simpl; auto.
  - f_equal.
    + apply (tysubst_agree sigma sigma' T1).
      intros X Hin. apply Hs. simpl. apply in_or_app. left. assumption.
    + apply IHt1.
      * intros y Hin. apply Ht. simpl. assumption.
      * intros X Hin. apply Hs. simpl. apply in_or_app. right. assumption.
  - f_equal.
    + apply IHt1.
      * intros y Hin. apply Ht. simpl. apply in_or_app. left. assumption.
      * intros X Hin. apply Hs. simpl. apply in_or_app. left. assumption.
    + apply IHt2.
      * intros y Hin. apply Ht. simpl. apply in_or_app. right. assumption.
      * intros X Hin. apply Hs. simpl. apply in_or_app. right. assumption.
  - f_equal.
    apply IHt1.
    + intros y Hin. apply Ht. simpl. assumption.
    + intros X Hin. apply Hs. simpl. assumption.
  - f_equal.
    + apply IHt1.
      * intros y Hin. apply Ht. simpl. assumption.
      * intros X Hin. apply Hs. simpl. apply in_or_app. left. assumption.
    + apply (tysubst_agree sigma sigma' T1).
      intros X Hin. apply Hs. simpl. apply in_or_app. right. assumption.
  - f_equal.
    + apply IHt1.
      * intros y Hin. apply Ht. simpl. apply in_or_app. left. assumption.
      * intros X Hin. apply Hs. simpl. apply in_or_app. left. assumption.
    + apply IHt2.
      * intros y Hin. apply Ht. simpl. apply in_or_app. right. assumption.
      * intros X Hin. apply Hs. simpl. apply in_or_app. right. assumption.
Qed.

Lemma tysubst_id : forall T, tysubst id_ty T = T.
Proof.
  induction T; simpl; [reflexivity | reflexivity | f_equal; assumption | f_equal; assumption].
Qed.

Lemma tsubst_id : forall t, tsubst id_tm id_ty t = t.
Proof.
  induction t as [n | x | T1 t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 | t1 IHt1 T1 | t1 IHt1 t2 IHt2]; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply tysubst_id | assumption].
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; [assumption | apply tysubst_id].
  - f_equal; assumption.
Qed.

(* ---------------- inversion of local closure under opening ---------------- *)

Lemma lc_ty_open_inv : forall T K U,
  lc_ty_at 0 U -> lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  induction T; intros K U HU H; simpl in *.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + inversion H. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion H; subst. apply lc_ty_arrow.
    + apply IHT1 with (K := K) (U := U); assumption.
    + apply IHT2 with (K := K) (U := U); assumption.
  - inversion H; subst; clear H. apply lc_ty_all.
    apply IHT with (K := S K) (U := U); assumption.
Qed.

Lemma lc_tm_open_inv : forall t K k u,
  lc_tm_at K 0 u -> lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k u Hu H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + inversion H. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + assumption.
    + apply IHt with (K := K) (k := S k) (u := u); assumption.
  - inversion H; subst. apply lc_tm_app.
    + apply IHt1 with (K := K) (k := k) (u := u); assumption.
    + apply IHt2 with (K := K) (k := k) (u := u); assumption.
  - inversion H; subst. apply lc_tm_tabs.
    apply IHt with (K := S K) (k := k) (u := u).
    + apply lc_tm_mono with (K := K) (k := 0); [lia | lia | assumption].
    + assumption.
  - inversion H; subst. apply lc_tm_tapp.
    + apply IHt with (K := K) (k := k) (u := u); assumption.
    + assumption.
  - inversion H; subst. apply lc_tm_choice.
    + apply IHt1 with (K := K) (k := k) (u := u); assumption.
    + apply IHt2 with (K := K) (k := k) (u := u); assumption.
Qed.

Lemma lc_tm_open_ty_inv : forall t K k U,
  lc_ty_at 0 U -> lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k U HU H; simpl in *.
  - apply lc_tm_mono with (K := K) (k := k); [lia | lia | assumption].
  - apply lc_tm_mono with (K := K) (k := k); [lia | lia | assumption].
  - inversion H; subst; clear H. apply lc_tm_abs.
    + apply lc_ty_open_inv with (K := K) (U := U); assumption.
    + apply IHt with (K := K) (k := S k) (U := U); assumption.
  - inversion H; subst; clear H. apply lc_tm_app.
    + apply IHt1 with (K := K) (k := k) (U := U); assumption.
    + apply IHt2 with (K := K) (k := k) (U := U); assumption.
  - inversion H; subst; clear H. apply lc_tm_tabs.
    apply IHt with (K := S K) (k := k) (U := U); assumption.
  - inversion H; subst; clear H. apply lc_tm_tapp.
    + apply IHt with (K := K) (k := k) (U := U); assumption.
    + apply lc_ty_open_inv with (K := K) (U := U); assumption.
  - inversion H; subst; clear H. apply lc_tm_choice.
    + apply IHt1 with (K := K) (k := k) (U := U); assumption.
    + apply IHt2 with (K := K) (k := k) (U := U); assumption.
Qed.

(* ---------------- well-formedness implies local closure ---------------- *)

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    apply lc_ty_open_inv with (K := 0) (U := Ty_FVar (fresh L)).
    + apply lc_ty_fvar.
    + apply H0. apply fresh_not_in.
Qed.

Lemma tsubst_open_tm : forall theta sigma t u,
  (forall x, lc_tm_at 0 0 (theta x)) ->
  tsubst theta sigma (open_tm t u) = open_tm (tsubst theta sigma t) (tsubst theta sigma u).
Proof.
  intros. unfold open_tm. apply tsubst_open_tm_rec. assumption.
Qed.

Lemma tsubst_open_tm_ty : forall theta sigma t U,
  (forall X, lc_ty_at 0 (sigma X)) ->
  (forall x, lc_tm_at 0 0 (theta x)) ->
  tsubst theta sigma (open_tm_ty t U) = open_tm_ty (tsubst theta sigma t) (tysubst sigma U).
Proof.
  intros. unfold open_tm_ty. apply tsubst_open_tm_ty_rec; assumption.
Qed.

(* ---------------- typing derivations yield locally closed terms ---------------- *)

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sigma theta,
  (forall X, lc_ty_at 0 (sigma X)) ->
  (forall x, lc_tm_at 0 0 (theta x)) ->
  lc_tm_at 0 0 (tsubst theta sigma t).
Proof.
  intros Delta Gamma t T H.
  induction H; intros sigma theta Hsig Hth; simpl.
  - (* T_Var *) apply Hth.
  - (* T_Abs *) apply lc_tm_abs.
    + apply lc_ty_subst_gen with (k := 0); [apply wf_ty_lc in H; assumption | assumption].
    + pose proof (H1 (fresh (L ++ tm_fvars t2)) (fresh_not_in_app_l L (tm_fvars t2))
                    sigma theta Hsig Hth) as Hbody.
      rewrite tsubst_open_tm in Hbody; [| apply Hth].
      apply lc_tm_open_inv with (K := 0) (k := 0) (u := theta (fresh (L ++ tm_fvars t2))).
      * apply Hth.
      * exact Hbody.
  - (* T_App *) apply lc_tm_app.
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
  - (* T_TAbs *) apply lc_tm_tabs.
    pose proof (H0 (fresh (L ++ tm_ty_fvars t)) (fresh_not_in_app_l L (tm_ty_fvars t))
                    sigma theta Hsig Hth) as Hbody.
    rewrite tsubst_open_tm_ty in Hbody; [| apply Hsig | apply Hth].
    apply lc_tm_open_ty_inv with (U := sigma (fresh (L ++ tm_ty_fvars t))); [apply Hsig | ].
    exact Hbody.
  - (* T_TApp *) apply lc_tm_tapp.
    + apply IHhas_type; assumption.
    + apply lc_ty_subst_gen with (k := 0); [apply wf_ty_lc in H0; assumption | assumption].
  - (* T_Choice *) apply lc_tm_choice.
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
Qed.

(* ============================================================ *)
(* The logical relation                                          *)
(* ============================================================ *)

Definition rel := tm -> tm -> Prop.

Definition rel_bot : rel := fun _ _ => False.

Definition E_def (R : rel) (s1 s2 : tm) : Prop :=
  exists v1 v2, value v1 /\ value v2 /\ s1 -->* v1 /\ s2 -->* v2 /\ R v1 v2.

Fixpoint V (Rs : list rel) (rho : atom -> rel) (T : ty) {struct T} : rel :=
  match T with
  | Ty_BVar i => nth i Rs rel_bot
  | Ty_FVar X => rho X
  | Ty_Arrow T1 T2 => fun s1 s2 =>
      forall v1 v2, value v1 -> value v2 -> V Rs rho T1 v1 v2 ->
        E_def (V Rs rho T2) (tm_app s1 v1) (tm_app s2 v2)
  | Ty_All T1 => fun s1 s2 =>
      forall U1 U2 R', lc_ty_at 0 U1 -> lc_ty_at 0 U2 ->
        E_def (V (R' :: Rs) rho T1) (tm_tapp s1 U1) (tm_tapp s2 U2)
  end.

Definition E (Rs : list rel) (rho : atom -> rel) (T : ty) : rel :=
  fun s1 s2 => E_def (V Rs rho T) s1 s2.

(* ---------------- basic lemmas about E_def ---------------- *)

Lemma E_def_congr : forall R R' s1 s2,
  (forall a b, R a b <-> R' a b) -> E_def R s1 s2 -> E_def R' s1 s2.
Proof.
  intros R R' s1 s2 Hag (v1 & v2 & Hv1 & Hv2 & Hm1 & Hm2 & HR).
  exists v1, v2. repeat split; auto. apply Hag; assumption.
Qed.

Lemma E_def_iff : forall R R' s1 s2,
  (forall a b, R a b <-> R' a b) -> (E_def R s1 s2 <-> E_def R' s1 s2).
Proof.
  intros R R' s1 s2 H. split.
  - apply E_def_congr. exact H.
  - apply E_def_congr. intros a b. split; intros Hab;
      [apply (proj2 (H a b)) | apply (proj1 (H a b))]; assumption.
Qed.

Lemma E_def_step_l : forall R s s' u, s --> s' -> E_def R s' u -> E_def R s u.
Proof.
  intros R s s' u Hstep (v1 & v2 & Hv1 & Hv2 & Hm1 & Hm2 & HR).
  exists v1, v2. repeat split; auto. apply multi_step with s'; assumption.
Qed.

Lemma E_def_step_r : forall R s u u', u --> u' -> E_def R s u' -> E_def R s u.
Proof.
  intros R s u u' Hstep (v1 & v2 & Hv1 & Hv2 & Hm1 & Hm2 & HR).
  exists v1, v2. repeat split; auto. apply multi_step with u'; assumption.
Qed.

Lemma E_def_multi_l : forall R s s' u, s -->* s' -> E_def R s' u -> E_def R s u.
Proof.
  intros R s s' u H. induction H; intros H'.
  - exact H'.
  - apply E_def_step_l with (s' := y); [exact H | apply IHmulti; exact H'].
Qed.

Lemma E_def_multi_r : forall R s u u', u -->* u' -> E_def R s u' -> E_def R s u.
Proof.
  intros R s u u' H. induction H; intros H'.
  - exact H'.
  - apply E_def_step_r with (u' := y); [exact H | apply IHmulti; exact H'].
Qed.

Lemma V_to_E : forall Rs rho T v1 v2,
  value v1 -> value v2 -> V Rs rho T v1 v2 -> E Rs rho T v1 v2.
Proof.
  intros. unfold E. exists v1, v2. repeat split; auto using multi_refl.
Qed.

(* ---------------- insertion into relation lists ---------------- *)

Lemma nth_insert_lt : forall (k i : nat) (Rs : list rel) (RU d : rel),
  i < k -> i < length Rs ->
  nth i (firstn k Rs ++ RU :: skipn k Rs) d = nth i Rs d.
Proof.
  induction k as [|k IH]; intros i Rs RU d Hik Hlen.
  - lia.
  - destruct Rs as [|R Rs'].
    + simpl in Hlen; lia.
    + destruct i as [|i].
      * reflexivity.
      * simpl. apply IH; [lia | simpl in Hlen; lia].
Qed.

Lemma nth_insert_eq : forall (k : nat) (Rs : list rel) (RU d : rel),
  k <= length Rs -> nth k (firstn k Rs ++ RU :: skipn k Rs) d = RU.
Proof.
  induction k as [|k IH]; intros Rs RU d Hle.
  - reflexivity.
  - destruct Rs as [|R Rs'].
    + simpl in Hle; lia.
    + simpl. apply IH. simpl in Hle; lia.
Qed.

(* ---------------- the type-substitution lemma for V ---------------- *)

Lemma V_list_agree : forall T, forall k, lc_ty_at k T ->
  forall Rs Rs' rho,
  (forall i, i < k -> nth i Rs rel_bot = nth i Rs' rel_bot) ->
  forall s1 s2, V Rs rho T s1 s2 <-> V Rs' rho T s1 s2.
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1];
    intros k Hlc Rs Rs' rho Hagree s1 s2; simpl.
  - pose proof (lc_ty_bvar_inv k n Hlc).
    rewrite (Hagree n H). reflexivity.
  - reflexivity.
  - destruct (lc_ty_arrow_inv k T1 T2 Hlc) as [H1 H2].
    split; intros H v1 v2 Hv1 Hv2 HV.
    + apply E_def_congr with (R := V Rs rho T2).
      * intros a b. apply (IH2 k H2 Rs Rs' rho Hagree a b).
      * apply H; auto. apply (proj2 (IH1 k H1 Rs Rs' rho Hagree v1 v2)); assumption.
    + apply E_def_congr with (R := V Rs' rho T2).
      * intros a b. split.
        -- apply (proj2 (IH2 k H2 Rs Rs' rho Hagree a b)).
        -- apply (proj1 (IH2 k H2 Rs Rs' rho Hagree a b)).
      * apply H; auto. apply (proj1 (IH1 k H1 Rs Rs' rho Hagree v1 v2)); assumption.
  - pose proof (lc_ty_all_inv k T1 Hlc) as H1.
    split.
    + intros H U1 U2 R' HU1 HU2.
      assert (Hag' : forall j, j < S k -> nth j (R' :: Rs) rel_bot = nth j (R' :: Rs') rel_bot)
        by (intros j Hj; destruct j as [|j]; [reflexivity | simpl; apply Hagree; lia]).
      apply E_def_congr with (R := V (R' :: Rs) rho T1).
      * intros a b. apply (IH1 (S k) H1 (R' :: Rs) (R' :: Rs') rho Hag' a b).
      * apply H; assumption.
    + intros H U1 U2 R' HU1 HU2.
      assert (Hag' : forall j, j < S k -> nth j (R' :: Rs) rel_bot = nth j (R' :: Rs') rel_bot)
        by (intros j Hj; destruct j as [|j]; [reflexivity | simpl; apply Hagree; lia]).
      apply E_def_congr with (R := V (R' :: Rs') rho T1).
      * intros a b. split.
        -- apply (proj2 (IH1 (S k) H1 (R' :: Rs) (R' :: Rs') rho Hag' a b)).
        -- apply (proj1 (IH1 (S k) H1 (R' :: Rs) (R' :: Rs') rho Hag' a b)).
      * apply H; assumption.
Qed.

Lemma V_lc_list : forall T, lc_ty_at 0 T ->
  forall Rs Rs' rho s1 s2, V Rs rho T s1 s2 <-> V Rs' rho T s1 s2.
Proof.
  intros T Hlc Rs Rs' rho s1 s2.
  apply V_list_agree with (k := 0); [exact Hlc | intros i Hi; lia].
Qed.

Lemma V_list_agree_all : forall T, forall Rs Rs' rho,
  (forall i, nth i Rs rel_bot = nth i Rs' rel_bot) ->
  forall s1 s2, V Rs rho T s1 s2 <-> V Rs' rho T s1 s2.
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1];
    intros Rs Rs' rho Hag s1 s2; simpl.
  - rewrite (Hag n). reflexivity.
  - reflexivity.
  - split; intros H v1 v2 Hv1 Hv2 HV.
    + apply E_def_congr with (R := V Rs rho T2).
      * intros a b. apply (IH2 Rs Rs' rho Hag a b).
      * apply H; auto. apply (proj2 (IH1 Rs Rs' rho Hag v1 v2)); assumption.
    + apply E_def_congr with (R := V Rs' rho T2).
      * intros a b. split; [apply (proj2 (IH2 Rs Rs' rho Hag a b)) |
                             apply (proj1 (IH2 Rs Rs' rho Hag a b))].
      * apply H; auto. apply (proj1 (IH1 Rs Rs' rho Hag v1 v2)); assumption.
  - split; intros H U1 U2 R' HU1 HU2.
    + apply E_def_congr with (R := V (R' :: Rs) rho T1).
      * intros a b.
        apply (IH1 (R' :: Rs) (R' :: Rs') rho).
        intros i. destruct i as [|i]; [reflexivity | simpl; apply Hag].
      * apply H; assumption.
    + apply E_def_congr with (R := V (R' :: Rs') rho T1).
      * intros a b.
        assert (Hag' : forall i, nth i (R' :: Rs) rel_bot = nth i (R' :: Rs') rel_bot)
          by (intros i; destruct i as [|i]; [reflexivity | simpl; apply Hag]).
        split.
        -- apply (proj2 (IH1 (R' :: Rs) (R' :: Rs') rho Hag' a b)).
        -- apply (proj1 (IH1 (R' :: Rs) (R' :: Rs') rho Hag' a b)).
      * apply H; assumption.
Qed.

Lemma E_list_agree_all : forall T Rs Rs' rho,
  (forall i, nth i Rs rel_bot = nth i Rs' rel_bot) ->
  forall s1 s2, E Rs rho T s1 s2 <-> E Rs' rho T s1 s2.
Proof.
  intros. unfold E. apply E_def_iff. intros a b. apply V_list_agree_all; assumption.
Qed.

Lemma V_subst_gen : forall T, forall k Rs U RU rho,
  lc_ty_at (S k) T ->
  k <= length Rs ->
  (forall s1 s2, RU s1 s2 <-> V [] rho U s1 s2) ->
  lc_ty_at 0 U ->
  forall s1 s2,
    V (firstn k Rs ++ RU :: skipn k Rs) rho T s1 s2 <->
    V Rs rho (open_ty_rec k U T) s1 s2.
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1];
    intros k Rs U RU rho Hlc Hle HRU HUlc s1 s2; simpl.
  - pose proof (lc_ty_bvar_inv (S k) n Hlc) as Hnk.
    destruct (Nat.eqb n k) eqn:E.
    + apply Nat.eqb_eq in E; subst n.
      rewrite nth_insert_eq by assumption.
      rewrite Nat.eqb_refl. simpl.
      split; intros H.
      * apply (proj2 (V_lc_list U HUlc Rs [] rho s1 s2)).
        apply (proj1 (HRU s1 s2)); assumption.
      * apply (proj2 (HRU s1 s2)).
        apply (proj1 (V_lc_list U HUlc Rs [] rho s1 s2)); assumption.
    + apply Nat.eqb_neq in E.
      assert (Hnk2 : n < k) by lia.
      assert (Hlen : n < length Rs) by lia.
      rewrite nth_insert_lt; [| exact Hnk2 | exact Hlen].
      destruct (Nat.eqb k n) eqn:E2.
      * apply Nat.eqb_eq in E2. subst. exfalso; apply E; reflexivity.
      * reflexivity.
  - reflexivity.
  - destruct (lc_ty_arrow_inv (S k) T1 T2 Hlc) as [H1 H2].
    split; intros H v1 v2 Hv1 Hv2 HV.
    + apply E_def_congr with (R := V (firstn k Rs ++ RU :: skipn k Rs) rho T2).
      * intros a b. apply (IH2 k Rs U RU rho H2 Hle HRU HUlc a b).
      * apply H; auto.
        apply (proj2 (IH1 k Rs U RU rho H1 Hle HRU HUlc v1 v2)); assumption.
    + apply E_def_congr with (R := V Rs rho (open_ty_rec k U T2)).
      * intros a b. split.
        -- apply (proj2 (IH2 k Rs U RU rho H2 Hle HRU HUlc a b)).
        -- apply (proj1 (IH2 k Rs U RU rho H2 Hle HRU HUlc a b)).
      * apply H; auto.
        apply (proj1 (IH1 k Rs U RU rho H1 Hle HRU HUlc v1 v2)); assumption.
  - pose proof (lc_ty_all_inv (S k) T1 Hlc) as H1.
    split; intros H U1 U2 R' H2 H3.
    + apply E_def_congr
        with (R := V (R' :: (firstn k Rs ++ RU :: skipn k Rs)) rho T1).
      * assert (Hle' : S k <= length (R' :: Rs)) by (simpl; apply le_n_S; assumption).
        intros a b.
        apply (IH1 (S k) (R' :: Rs) U RU rho H1 Hle' HRU HUlc a b).
      * apply H; assumption.
    + apply E_def_congr
        with (R := V (R' :: Rs) rho (open_ty_rec (S k) U T1)).
      * assert (Hle' : S k <= length (R' :: Rs)) by (simpl; apply le_n_S; assumption).
        intros a b. split.
        -- apply (proj2 (IH1 (S k) (R' :: Rs) U RU rho H1 Hle' HRU HUlc a b)).
        -- apply (proj1 (IH1 (S k) (R' :: Rs) U RU rho H1 Hle' HRU HUlc a b)).
      * apply H; assumption.
Qed.

(* ---------------- corollaries of the substitution lemma ---------------- *)

Lemma V_open_ty : forall Rs rho T U,
  lc_ty_at 1 T -> lc_ty_at 0 U ->
  forall s1 s2, V (V [] rho U :: Rs) rho T s1 s2 <-> V Rs rho (open_ty T U) s1 s2.
Proof.
  intros Rs rho T U Hlt HUlc s1 s2. unfold open_ty.
  apply (V_subst_gen T 0 Rs U (V [] rho U) rho).
  - exact Hlt.
  - simpl; lia.
  - intros a b; reflexivity.
  - exact HUlc.
Qed.

Lemma V_open_fvar : forall Rs rho T X,
  lc_ty_at 1 T ->
  forall s1 s2, V (rho X :: Rs) rho T s1 s2 <-> V Rs rho (open_ty T (Ty_FVar X)) s1 s2.
Proof.
  intros Rs rho T X Hlt s1 s2. unfold open_ty.
  apply (V_subst_gen T 0 Rs (Ty_FVar X) (rho X) rho).
  - exact Hlt.
  - simpl; lia.
  - intros a b; reflexivity.
  - apply lc_ty_fvar.
Qed.

Lemma E_open_ty : forall Rs rho T U,
  lc_ty_at 1 T -> lc_ty_at 0 U ->
  forall s1 s2, E (V [] rho U :: Rs) rho T s1 s2 <-> E Rs rho (open_ty T U) s1 s2.
Proof.
  intros. unfold E. apply E_def_iff. intros a b. apply V_open_ty; assumption.
Qed.

Lemma E_open_fvar : forall Rs rho T X,
  lc_ty_at 1 T ->
  forall s1 s2, E (rho X :: Rs) rho T s1 s2 <-> E Rs rho (open_ty T (Ty_FVar X)) s1 s2.
Proof.
  intros. unfold E. apply E_def_iff. intros a b. apply V_open_fvar; assumption.
Qed.

(* ---------------- agreement in the type-variable environment ---------------- *)

Lemma V_rho_agree : forall T rho rho',
  (forall X, In X (ty_fvars T) -> forall s1 s2, rho X s1 s2 <-> rho' X s1 s2) ->
  forall Rs s1 s2, V Rs rho T s1 s2 <-> V Rs rho' T s1 s2.
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1];
    intros rho rho' Hag Rs s1 s2; simpl.
  - reflexivity.
  - apply Hag. simpl; auto.
  - assert (Hag1 : forall X, In X (ty_fvars T1) ->
                    forall s1 s2, rho X s1 s2 <-> rho' X s1 s2).
    { intros X Hin. apply Hag. simpl. apply in_or_app. left. assumption. }
    assert (Hag2 : forall X, In X (ty_fvars T2) ->
                    forall s1 s2, rho X s1 s2 <-> rho' X s1 s2).
    { intros X Hin. apply Hag. simpl. apply in_or_app. right. assumption. }
    split; intros H v1 v2 Hv1 Hv2 HV.
    + apply E_def_congr with (R := V Rs rho T2).
      * intros a b. apply (IH2 rho rho' Hag2 Rs a b).
      * apply H; auto. apply (proj2 (IH1 rho rho' Hag1 Rs v1 v2)); assumption.
    + apply E_def_congr with (R := V Rs rho' T2).
      * intros a b. split.
        -- apply (proj2 (IH2 rho rho' Hag2 Rs a b)).
        -- apply (proj1 (IH2 rho rho' Hag2 Rs a b)).
      * apply H; auto. apply (proj1 (IH1 rho rho' Hag1 Rs v1 v2)); assumption.
  - assert (Hag1 : forall X, In X (ty_fvars T1) ->
                    forall s1 s2, rho X s1 s2 <-> rho' X s1 s2).
    { intros X Hin. apply Hag. simpl. assumption. }
    split; intros H U1 U2 R' HU1 HU2.
    + apply E_def_congr with (R := V (R' :: Rs) rho T1).
      * intros a b. apply (IH1 rho rho' Hag1 (R' :: Rs) a b).
      * apply H; assumption.
    + apply E_def_congr with (R := V (R' :: Rs) rho' T1).
      * intros a b. split.
        -- apply (proj2 (IH1 rho rho' Hag1 (R' :: Rs) a b)).
        -- apply (proj1 (IH1 rho rho' Hag1 (R' :: Rs) a b)).
      * apply H; assumption.
Qed.

Lemma E_rho_agree : forall T rho rho',
  (forall X, In X (ty_fvars T) -> forall s1 s2, rho X s1 s2 <-> rho' X s1 s2) ->
  forall Rs s1 s2, E Rs rho T s1 s2 <-> E Rs rho' T s1 s2.
Proof.
  intros. unfold E. apply E_def_iff. intros a b. apply V_rho_agree; assumption.
Qed.

(* ---------------- reduction lemmas ---------------- *)

Lemma value_no_step : forall v, value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv t Hstep. induction Hv; inversion Hstep.
Qed.

Lemma multi_value_inv : forall v t, value v -> v -->* t -> t = v.
Proof.
  intros v t Hv Hm. induction Hm.
  - reflexivity.
  - exfalso.
    match goal with
    | Hstep : ?a --> ?b, Hval : value ?a |- False => exact (value_no_step a Hval b Hstep)
    end.
Qed.

Lemma multi_trans : forall t1 t2 t3, t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H. induction H; intros H23.
  - exact H23.
  - apply multi_step with y; [exact H | apply IHmulti; exact H23].
Qed.

Lemma multi_tapp : forall t t' U,
  t -->* t' -> locally_closed_ty U -> tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H. induction H; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (tm_tapp y U); [apply ST_TApp; assumption | apply IHmulti; assumption].
Qed.

Lemma multi_app_l : forall t t' u,
  t -->* t' -> locally_closed_tm u -> tm_app t u -->* tm_app t' u.
Proof.
  intros t t' u H. induction H; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (tm_app y u); [apply ST_App1; assumption | apply IHmulti; assumption].
Qed.

Lemma multi_app_r : forall v t t',
  value v -> t -->* t' -> tm_app v t -->* tm_app v t'.
Proof.
  intros v t t' Hv H. induction H.
  - apply multi_refl.
  - apply multi_step with (tm_app v y); [apply ST_App2; assumption | apply IHmulti].
Qed.

Lemma value_lc : forall v, value v -> lc_tm_at 0 0 v.
Proof. intros v H. destruct H; assumption. Qed.

(* ---------------- update lemmas ---------------- *)

Lemma upd_tm_same : forall theta x w, upd_tm theta x w x = w.
Proof. intros. unfold upd_tm. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_tm_other : forall theta x y w, y <> x -> upd_tm theta x w y = theta y.
Proof.
  intros. unfold upd_tm. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. exact (H E).
  - reflexivity.
Qed.

Lemma upd_ty_same : forall sigma X U, upd_ty sigma X U X = U.
Proof. intros. unfold upd_ty. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_ty_other : forall sigma X Y U, Y <> X -> upd_ty sigma X U Y = sigma Y.
Proof.
  intros. unfold upd_ty. destruct (Nat.eqb Y X) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. exact (H E).
  - reflexivity.
Qed.

Lemma upd_rel_same : forall rho X R, upd_rel rho X R X = R.
Proof. intros. unfold upd_rel. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_rel_other : forall rho X Y R, Y <> X -> upd_rel rho X R Y = rho Y.
Proof.
  intros. unfold upd_rel. destruct (Nat.eqb Y X) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. exact (H E).
  - reflexivity.
Qed.

(* ---------------- context lookup lemmas ---------------- *)

Lemma lookup_context_cons_same : forall Gamma x T,
  lookup_context x ((x, T) :: Gamma) = Some T.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_context_cons_diff : forall Gamma x y T, x <> y ->
  lookup_context x ((y, T) :: Gamma) = lookup_context x Gamma.
Proof.
  intros. simpl. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply H. assumption.
  - reflexivity.
Qed.

Lemma lookup_ty_fvars : forall Gamma x A,
  lookup_context x Gamma = Some A ->
  forall X, In X (ty_fvars A) -> In X (ctx_ty_fvars Gamma).
Proof.
  induction Gamma as [| (y, B) Gamma IH]; intros x A Hlk X Hin.
  - simpl in Hlk. discriminate.
  - simpl in Hlk. simpl.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. inversion Hlk; subst A.
      apply in_or_app. left. assumption.
    + apply in_or_app. right. apply (IH x A Hlk X Hin).
Qed.

(* ---------------- opening preserves local closure of types ---------------- *)

Lemma lc_ty_open : forall T k U,
  lc_ty_at (S k) T -> lc_ty_at 0 U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1];
    intros k U Hlt HU; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst n.
      apply lc_ty_mono with (k := 0); [lia | exact HU].
    + apply Nat.eqb_neq in E.
      apply lc_ty_bvar. pose proof (lc_ty_bvar_inv (S k) n Hlt). lia.
  - apply lc_ty_fvar.
  - destruct (lc_ty_arrow_inv (S k) T1 T2 Hlt) as [H1 H2]. apply lc_ty_arrow.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - pose proof (lc_ty_all_inv (S k) T1 Hlt) as H1. apply lc_ty_all.
    apply IH1 with (k := S k) (U := U); assumption.
Qed.

(* ---------------- types in typing derivations are locally closed ---------------- *)

Lemma typing_ty_lc : forall Delta Gamma t T, has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H. induction H.
  - apply wf_ty_lc with (Delta := Delta). assumption.
  - apply lc_ty_arrow.
    + apply wf_ty_lc with (Delta := Delta). assumption.
    + exact (H1 (fresh L) (fresh_not_in L)).
  - destruct (lc_ty_arrow_inv 0 T1 T2 IHhas_type1) as [Hx Hy]. exact Hy.
  - apply lc_ty_all.
    apply lc_ty_open_inv with (K := 0) (U := Ty_FVar (fresh L)).
    + apply lc_ty_fvar.
    + exact (H0 (fresh L) (fresh_not_in L)).
  - apply lc_ty_open with (k := 0).
    + apply lc_ty_all_inv with (k := 0); exact IHhas_type.
    + apply wf_ty_lc with (Delta := Delta). assumption.
  - exact IHhas_type1.
Qed.

(* ============================================================ *)
(* Fundamental theorem                                            *)
(* ============================================================ *)

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sigma1 sigma2 rho theta1 theta2,
  (forall X, lc_ty_at 0 (sigma1 X)) ->
  (forall X, lc_ty_at 0 (sigma2 X)) ->
  (forall x, lc_tm_at 0 0 (theta1 x)) ->
  (forall x, lc_tm_at 0 0 (theta2 x)) ->
  (forall x A, lookup_context x Gamma = Some A -> E [] rho A (theta1 x) (theta2 x)) ->
  E [] rho T (tsubst theta1 sigma1 t) (tsubst theta2 sigma2 t).
Proof.
  intros Delta Gamma t T H.
  induction H; intros sigma1 sigma2 rho theta1 theta2 Hsig1 Hsig2 Hth1 Hth2 Henv.
  - (* T_Var *) simpl. apply Henv. assumption.
  - (* T_Abs *)
    assert (Hder : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2))
      by (apply T_Abs with (L := L); assumption).
    assert (Hlc1 : lc_tm_at 0 0 (tsubst theta1 sigma1 (tm_abs T1 t2)))
      by (apply typing_lc with (Delta := Delta) (Gamma := Gamma) (T := Ty_Arrow T1 T2);
          [exact Hder | exact Hsig1 | exact Hth1]).
    assert (Hlc2 : lc_tm_at 0 0 (tsubst theta2 sigma2 (tm_abs T1 t2)))
      by (apply typing_lc with (Delta := Delta) (Gamma := Gamma) (T := Ty_Arrow T1 T2);
          [exact Hder | exact Hsig2 | exact Hth2]).
    remember (fresh (L ++ tm_fvars t2)) as x eqn:Hx.
    assert (HxL : ~ In x L) by (rewrite Hx; apply fresh_not_in_app_l).
    assert (Hxfv : ~ In x (tm_fvars t2)) by (rewrite Hx; apply fresh_not_in_app_r).
    simpl. unfold E, E_def.
    exists (tm_abs (tysubst sigma1 T1) (tsubst theta1 sigma1 t2)),
           (tm_abs (tysubst sigma2 T1) (tsubst theta2 sigma2 t2)).
    repeat split.
    + apply v_abs. exact Hlc1.
    + apply v_abs. exact Hlc2.
    + apply multi_refl.
    + apply multi_refl.
    + intros w1 w2 Hv1 Hv2 HV.
      apply E_def_step_l with (s' := open_tm (tsubst theta1 sigma1 t2) w1).
      * apply ST_AppAbs; [exact Hlc1 | exact Hv1].
      * apply E_def_step_r with (u' := open_tm (tsubst theta2 sigma2 t2) w2).
        -- apply ST_AppAbs; [exact Hlc2 | exact Hv2].
        -- assert (Hth1' : forall y, lc_tm_at 0 0 (upd_tm theta1 x w1 y)).
           { intros y. unfold upd_tm. destruct (Nat.eqb y x) eqn:E.
             ++ apply lc_tm_mono with (K := 0) (k := 0);
                  [lia | lia | apply value_lc; exact Hv1].
             ++ apply Hth1. }
           assert (Hth2' : forall y, lc_tm_at 0 0 (upd_tm theta2 x w2 y)).
           { intros y. unfold upd_tm. destruct (Nat.eqb y x) eqn:E.
             ++ apply lc_tm_mono with (K := 0) (k := 0);
                  [lia | lia | apply value_lc; exact Hv2].
             ++ apply Hth2. }
           assert (Henv' : forall y A,
                     lookup_context y (update Gamma x T1) = Some A ->
                     E [] rho A (upd_tm theta1 x w1 y) (upd_tm theta2 x w2 y)).
           { intros y A Hlk. simpl in Hlk.
             destruct (Nat.eqb y x) eqn:E.
             - apply Nat.eqb_eq in E; subst y. inversion Hlk; subst A.
               rewrite upd_tm_same. rewrite upd_tm_same.
               apply V_to_E; assumption.
             - apply Nat.eqb_neq in E.
               rewrite (upd_tm_other theta1 x y w1) by (intro Hc; subst y; exact (E eq_refl)).
               rewrite (upd_tm_other theta2 x y w2) by (intro Hc; subst y; exact (E eq_refl)).
               apply Henv. exact Hlk. }
           assert (Hag1 : tsubst (upd_tm theta1 x w1) sigma1 t2 =
                          tsubst theta1 sigma1 t2).
           { apply tsubst_agree.
             - intros y Hy. apply upd_tm_other. intro Hxy. subst y. exact (Hxfv Hy).
             - intros X Hin. reflexivity. }
           assert (Hag2 : tsubst (upd_tm theta2 x w2) sigma2 t2 =
                          tsubst theta2 sigma2 t2).
           { apply tsubst_agree.
             - intros y Hy. apply upd_tm_other. intro Hxy. subst y. exact (Hxfv Hy).
             - intros X Hin. reflexivity. }
           pose proof (H1 x HxL sigma1 sigma2 rho
                         (upd_tm theta1 x w1) (upd_tm theta2 x w2)
                         Hsig1 Hsig2 Hth1' Hth2' Henv') as Hbody.
           rewrite tsubst_open_tm in Hbody; [| exact Hth1'].
           rewrite tsubst_open_tm in Hbody; [| exact Hth2'].
           simpl in Hbody.
           rewrite upd_tm_same in Hbody.
           rewrite upd_tm_same in Hbody.
           rewrite Hag1 in Hbody.
           rewrite Hag2 in Hbody.
           exact Hbody.
  - (* T_App *)
    pose proof (IHhas_type1 sigma1 sigma2 rho theta1 theta2
                  Hsig1 Hsig2 Hth1 Hth2 Henv) as E1.
    pose proof (IHhas_type2 sigma1 sigma2 rho theta1 theta2
                  Hsig1 Hsig2 Hth1 Hth2 Henv) as E2.
    unfold E, E_def in E1, E2.
    destruct E1 as (f1 & f2 & Hvf1 & Hvf2 & Hm1 & Hm2 & HV).
    destruct E2 as (a1 & a2 & Hva1 & Hva2 & Hn1 & Hn2 & HVA).
    apply E_def_multi_l with (s' := tm_app f1 (tsubst theta1 sigma1 t2)).
    + apply multi_app_l.
      * exact Hm1.
      * apply typing_lc with (Delta := Delta) (Gamma := Gamma) (T := T1);
          [exact H0 | exact Hsig1 | exact Hth1].
    + apply E_def_multi_l with (s' := tm_app f1 a1).
      * apply multi_app_r; assumption.
      * apply E_def_multi_r with (u' := tm_app f2 (tsubst theta2 sigma2 t2)).
        -- apply multi_app_l.
           ++ exact Hm2.
           ++ apply typing_lc with (Delta := Delta) (Gamma := Gamma) (T := T1);
                [exact H0 | exact Hsig2 | exact Hth2].
        -- apply E_def_multi_r with (u' := tm_app f2 a2).
           ++ apply multi_app_r; assumption.
           ++ apply HV; assumption.
  - (* T_TAbs *)
    assert (Hder : has_type Delta Gamma (tm_tabs t) (Ty_All T))
      by (apply T_TAbs with (L := L); assumption).
    assert (Hlt : lc_ty_at 1 T).
    { apply lc_ty_all_inv with (k := 0).
      apply typing_ty_lc with (Delta := Delta) (Gamma := Gamma) (t := tm_tabs t).
      exact Hder. }
    assert (Hlc1 : lc_tm_at 0 0 (tsubst theta1 sigma1 (tm_tabs t)))
      by (apply typing_lc with (Delta := Delta) (Gamma := Gamma) (T := Ty_All T);
          [exact Hder | exact Hsig1 | exact Hth1]).
    assert (Hlc2 : lc_tm_at 0 0 (tsubst theta2 sigma2 (tm_tabs t)))
      by (apply typing_lc with (Delta := Delta) (Gamma := Gamma) (T := Ty_All T);
          [exact Hder | exact Hsig2 | exact Hth2]).
    remember (fresh (L ++ tm_ty_fvars t ++ ctx_ty_fvars Gamma ++ ty_fvars T)) as a eqn:Ha.
    assert (HaL : ~ In a L)
      by (rewrite Ha; apply not_in_app_l with (l2 := tm_ty_fvars t ++ ctx_ty_fvars Gamma ++ ty_fvars T);
          apply fresh_not_in).
    assert (Ha_tmty : ~ In a (tm_ty_fvars t)).
    { rewrite Ha. intro Hin.
      apply (fresh_not_in (L ++ tm_ty_fvars t ++ ctx_ty_fvars Gamma ++ ty_fvars T)).
      apply in_or_app. right. apply in_or_app. left. assumption. }
    assert (Ha_ctx : ~ In a (ctx_ty_fvars Gamma)).
    { rewrite Ha. intro Hin.
      apply (fresh_not_in (L ++ tm_ty_fvars t ++ ctx_ty_fvars Gamma ++ ty_fvars T)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. assumption. }
    assert (Ha_T : ~ In a (ty_fvars T)).
    { rewrite Ha. intro Hin.
      apply (fresh_not_in (L ++ tm_ty_fvars t ++ ctx_ty_fvars Gamma ++ ty_fvars T)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. assumption. }
    simpl. unfold E, E_def.
    exists (tm_tabs (tsubst theta1 sigma1 t)), (tm_tabs (tsubst theta2 sigma2 t)).
    repeat split.
    + apply v_tabs. exact Hlc1.
    + apply v_tabs. exact Hlc2.
    + apply multi_refl.
    + apply multi_refl.
    + intros U1 U2 R' HU1 HU2.
      assert (Hsig1' : forall X, lc_ty_at 0 (upd_ty sigma1 a U1 X)).
      { intros X. unfold upd_ty. destruct (Nat.eqb X a) eqn:E.
        - exact HU1.
        - apply Hsig1. }
      assert (Hsig2' : forall X, lc_ty_at 0 (upd_ty sigma2 a U2 X)).
      { intros X. unfold upd_ty. destruct (Nat.eqb X a) eqn:E.
        - exact HU2.
        - apply Hsig2. }
      assert (Henv' : forall y A, lookup_context y Gamma = Some A ->
                      E [] (upd_rel rho a R') A (theta1 y) (theta2 y)).
      { intros y A Hlk.
        assert (Hnotin : ~ In a (ty_fvars A)).
        { intro Hin. exact (Ha_ctx (lookup_ty_fvars Gamma y A Hlk a Hin)). }
        apply (proj1 (E_rho_agree A rho (upd_rel rho a R')
                       ltac:(intros X Hin s1 s2; rewrite (upd_rel_other rho a X R');
                             [reflexivity | intro Hc; subst X; exact (Hnotin Hin)])
                       [] (theta1 y) (theta2 y))).
        apply Henv. exact Hlk. }
      pose proof (H0 a HaL (upd_ty sigma1 a U1) (upd_ty sigma2 a U2)
                    (upd_rel rho a R') theta1 theta2
                    Hsig1' Hsig2' Hth1 Hth2 Henv') as Hbody.
      rewrite tsubst_open_tm_ty in Hbody; [| exact Hsig1' | exact Hth1].
      rewrite tsubst_open_tm_ty in Hbody; [| exact Hsig2' | exact Hth2].
      simpl in Hbody.
      rewrite upd_ty_same in Hbody.
      rewrite upd_ty_same in Hbody.
      assert (Hag1 : tsubst theta1 (upd_ty sigma1 a U1) t = tsubst theta1 sigma1 t).
      { apply tsubst_agree.
        - intros y Hy. reflexivity.
        - intros X Hin. apply upd_ty_other. intro Hc. subst X. exact (Ha_tmty Hin). }
      assert (Hag2 : tsubst theta2 (upd_ty sigma2 a U2) t = tsubst theta2 sigma2 t).
      { apply tsubst_agree.
        - intros y Hy. reflexivity.
        - intros X Hin. apply upd_ty_other. intro Hc. subst X. exact (Ha_tmty Hin). }
      rewrite Hag1 in Hbody.
      rewrite Hag2 in Hbody.
      assert (Hconv : E (R' :: []) rho T
                        (open_tm_ty (tsubst theta1 sigma1 t) U1)
                        (open_tm_ty (tsubst theta2 sigma2 t) U2)).
      { apply (proj1 (E_rho_agree T (upd_rel rho a R') rho
                       ltac:(intros X Hin s1 s2; rewrite (upd_rel_other rho a X R');
                             [reflexivity | intro Hc; subst X; exact (Ha_T Hin)])
                       (R' :: []) (open_tm_ty (tsubst theta1 sigma1 t) U1)
                          (open_tm_ty (tsubst theta2 sigma2 t) U2))).
        apply (proj1 (E_list_agree_all T ((upd_rel rho a R') a :: []) (R' :: [])
                        (upd_rel rho a R')
                        ltac:(intros i; destruct i as [|i]; [simpl; apply upd_rel_same |
                              simpl; reflexivity])
                        (open_tm_ty (tsubst theta1 sigma1 t) U1)
                        (open_tm_ty (tsubst theta2 sigma2 t) U2))).
        apply (proj2 (E_open_fvar [] (upd_rel rho a R') T a Hlt
                        (open_tm_ty (tsubst theta1 sigma1 t) U1)
                        (open_tm_ty (tsubst theta2 sigma2 t) U2))).
        exact Hbody. }
      apply E_def_step_l with (s' := open_tm_ty (tsubst theta1 sigma1 t) U1).
      * apply ST_TAppTabs; [exact Hlc1 | exact HU1].
      * apply E_def_step_r with (u' := open_tm_ty (tsubst theta2 sigma2 t) U2).
        -- apply ST_TAppTabs; [exact Hlc2 | exact HU2].
        -- exact Hconv.
  - (* T_TApp *)
    assert (Hlt : lc_ty_at 1 T).
    { apply lc_ty_all_inv with (k := 0).
      apply typing_ty_lc with (Delta := Delta) (Gamma := Gamma) (t := t).
      exact H. }
    assert (HUlc : lc_ty_at 0 U)
      by (apply wf_ty_lc with (Delta := Delta); exact H0).
    assert (HlcU1 : lc_ty_at 0 (tysubst sigma1 U))
      by (apply lc_ty_subst_gen with (k := 0); [exact HUlc | exact Hsig1]).
    assert (HlcU2 : lc_ty_at 0 (tysubst sigma2 U))
      by (apply lc_ty_subst_gen with (k := 0); [exact HUlc | exact Hsig2]).
    pose proof (IHhas_type sigma1 sigma2 rho theta1 theta2
                  Hsig1 Hsig2 Hth1 Hth2 Henv) as E1.
    unfold E, E_def in E1.
    destruct E1 as (f1 & f2 & Hvf1 & Hvf2 & Hm1 & Hm2 & HV).
    apply E_def_multi_l with (s' := tm_tapp f1 (tysubst sigma1 U)).
    + apply multi_tapp; [exact Hm1 | exact HlcU1].
    + apply E_def_multi_r with (u' := tm_tapp f2 (tysubst sigma2 U)).
      * apply multi_tapp; [exact Hm2 | exact HlcU2].
      * apply (proj1 (E_open_ty [] rho T U Hlt HUlc
                       (tm_tapp f1 (tysubst sigma1 U))
                       (tm_tapp f2 (tysubst sigma2 U)))).
        apply HV; assumption.
  - (* T_Choice *)
    assert (Hder : has_type Delta Gamma (tm_choice t1 t2) T)
      by (apply T_Choice with (T := T); assumption).
    assert (Hlc1 : lc_tm_at 0 0 (tsubst theta1 sigma1 (tm_choice t1 t2)))
      by (apply typing_lc with (Delta := Delta) (Gamma := Gamma) (T := T);
          [exact Hder | exact Hsig1 | exact Hth1]).
    assert (Hlc2 : lc_tm_at 0 0 (tsubst theta2 sigma2 (tm_choice t1 t2)))
      by (apply typing_lc with (Delta := Delta) (Gamma := Gamma) (T := T);
          [exact Hder | exact Hsig2 | exact Hth2]).
    pose proof (IHhas_type1 sigma1 sigma2 rho theta1 theta2
                  Hsig1 Hsig2 Hth1 Hth2 Henv) as E1.
    unfold E, E_def in E1.
    apply E_def_step_l with (s' := tsubst theta1 sigma1 t1).
    + inversion Hlc1; subst. apply ST_ChoiceLeft; assumption.
    + apply E_def_step_r with (u' := tsubst theta2 sigma2 t1).
      * inversion Hlc2; subst. apply ST_ChoiceLeft; assumption.
      * exact E1.
Qed.

(* ============================================================ *)
(* The free theorem                                               *)
(* ============================================================ *)

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t Ht U v HU Hv HvU.
  assert (HUlc : lc_ty_at 0 U) by (apply wf_ty_lc with (Delta := []); exact HU).
  assert (Henv : forall x A, lookup_context x empty = Some A ->
                 E [] (fun _ _ _ => True) A (id_tm x) (id_tm x)).
  { intros x A Hlk. simpl in Hlk. discriminate Hlk. }
  pose proof (fundamental [] empty t (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
                id_ty id_ty (fun _ _ _ => True) id_tm id_tm
                (fun X => lc_ty_fvar 0 X) (fun X => lc_ty_fvar 0 X)
                (fun x => lc_tm_fvar 0 0 x) (fun x => lc_tm_fvar 0 0 x)
                Henv) as Hsem.
  rewrite tsubst_id in Hsem.
  unfold E, E_def in Hsem.
  destruct Hsem as (f1 & f2 & Hvf1 & Hvf2 & Hm1 & Hm2 & HV).
  pose proof (HV U U (fun a b => a = v /\ b = v) HUlc HUlc) as Hstep.
  destruct Hstep as (g1 & g2 & Hvg1 & Hvg2 & Hg1 & Hg2 & HVA).
  pose proof (HVA v v Hv Hv (conj eq_refl eq_refl)) as Hfin.
  destruct Hfin as (h1 & h2 & Hvh1 & Hvh2 & Hh1 & Hh2 & HR).
  simpl in HR. destruct HR as [Hh1v Hh2v].
  rewrite Hh1v in Hh1.
  apply multi_trans with (t2 := tm_app (tm_tapp f1 U) v).
  - apply multi_app_l.
    + apply multi_tapp; assumption.
    + apply value_lc; exact Hv.
  - apply multi_trans with (t2 := tm_app g1 v).
    + apply multi_app_l; [exact Hg1 | apply value_lc; exact Hv].
    + exact Hh1.
Qed.

End SystemFParametricityNondeterminismHardTask.
