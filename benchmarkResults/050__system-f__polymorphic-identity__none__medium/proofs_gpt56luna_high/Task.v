(** System F parametricity benchmark, Medium variant.
    Features: none. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNoneMediumTask.

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

  | tm_tapp : tm -> ty -> tm.

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
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
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
      lc_tm_at K k (tm_tapp t T).

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
      has_type Delta Gamma (tm_tapp t U) (open_ty T U).

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).


Hint Constructors lc_ty_at lc_tm_at value : core.

Inductive evaluates : tm -> tm -> Prop :=
  | EvalValue : forall v, value v -> evaluates v v
  | EvalApp : forall f arg U body v result,
      evaluates f (tm_abs U body) -> evaluates arg v ->
      evaluates (open_tm body v) result -> evaluates (tm_app f arg) result
  | EvalTApp : forall f U body result,
      evaluates f (tm_tabs body) -> locally_closed_ty U ->
      evaluates (open_tm_ty body U) result -> evaluates (tm_tapp f U) result.

Definition binary_relation := tm -> tm -> Prop.

Record binary_candidate := {
  candidate_relation : binary_relation;
  candidate_values : forall v1 v2, candidate_relation v1 v2 -> value v1 /\ value v2
}.

Definition binary_env := atom -> option binary_candidate.
Definition relation_update (rho : binary_env) (X : atom) (a : binary_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition results_match (R : binary_relation) (t1 t2 : tm) : Prop :=
  exists v1 v2,
    evaluates t1 v1 /\ evaluates t2 v2 /\ R v1 v2.

Definition expression_lifting (R : binary_relation) (t1 t2 : tm) : Prop :=
  locally_closed_tm t1 /\ locally_closed_tm t2 /\ results_match R t1 t2.

Fixpoint value_relation (eta : list binary_candidate) (rho : binary_env)
    (T : ty) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v1 v2 | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v1 v2 | None => False end
  | Ty_Arrow T1 T2 =>
      value v1 /\ value v2 /\
      exists U1 body1 U2 body2,
        v1 = tm_abs U1 body1 /\ v2 = tm_abs U2 body2 /\
        forall arg1 arg2, value_relation eta rho T1 arg1 arg2 ->
          expression_lifting (value_relation eta rho T2)
            (open_tm body1 arg1) (open_tm body2 arg2)
  | Ty_All T =>
      value v1 /\ value v2 /\
      exists body1 body2,
        v1 = tm_tabs body1 /\ v2 = tm_tabs body2 /\
        forall (U1 U2 : ty) (a : binary_candidate),
          locally_closed_ty U1 -> locally_closed_ty U2 ->
          expression_lifting (value_relation (a :: eta) rho T)
            (open_tm_ty body1 U1) (open_tm_ty body2 U2)
  end.

Definition expression_relation eta rho T t1 t2 :=
  expression_lifting (value_relation eta rho T) t1 t2.

(* The following is the (simultaneous) substitution used in the fundamental
   lemma.  It is deliberately total: variables not present in a typing
   context are mapped to themselves. *)
Definition tm_subst_env (th : atom -> tm) (t : tm) : tm :=
  let fix go (t : tm) : tm :=
    match t with
    | tm_bvar i => tm_bvar i
    | tm_fvar x => th x
    | tm_abs T t1 => tm_abs T (go t1)
    | tm_app t1 t2 => tm_app (go t1) (go t2)
    | tm_tabs t1 => tm_tabs (go t1)
    | tm_tapp t1 T => tm_tapp (go t1) T
    end in go t.

Fixpoint tm_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => tm_fv t1
  | tm_app t1 t2 => tm_fv t1 ++ tm_fv t2
  | tm_tabs t1 => tm_fv t1
  | tm_tapp t1 _ => tm_fv t1
  end.

Fixpoint list_max (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => max x (list_max xs')
  end.

Lemma in_le_list_max : forall x xs, In x xs -> x <= list_max xs.
Proof.
  intros x xs; induction xs as [|y xs IH]; simpl; intros H.
  - contradiction.
  - destruct H as [<-|H].
    + lia.
    + specialize (IH H); lia.
Qed.

Lemma fresh_not_in : forall xs, ~ In (S (list_max xs)) xs.
Proof.
  intros xs H; apply in_le_list_max in H; lia.
Qed.

Lemma in_app_inv : forall (x : atom) (xs ys : list atom),
  In x (xs ++ ys) -> In x xs \/ In x ys.
Proof.
  intros x xs; induction xs as [|a xs IH]; simpl; intros ys H.
  - right; exact H.
  - destruct H as [<-|H].
    + left; auto.
    + specialize (IH ys H); tauto.
Qed.

Lemma open_tm_rec_lc_gen : forall K k0 t,
  lc_tm_at K k0 t -> forall k s, k0 <= k -> open_tm_rec k s t = t.
Proof.
  intros K k0 t H; revert K k0 H.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros K k0 Hlc k' s Hk; inversion Hlc; subst; simpl.
  - destruct (Nat.eqb k' i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal. apply IH with (K:=K) (k0:=S k0); [assumption|lia].
  - f_equal.
    + apply IH1 with (K:=K) (k0:=k0); [assumption|lia].
    + apply IH2 with (K:=K) (k0:=k0); [assumption|lia].
  - f_equal. apply IH with (K:=S K) (k0:=k0); [assumption|lia].
  - f_equal. apply IH with (K:=K) (k0:=k0); [assumption|lia].
Qed.

Lemma open_tm_rec_lc : forall K k t s,
  lc_tm_at K 0 t -> open_tm_rec k s t = t.
Proof. intros K k t s H; apply (open_tm_rec_lc_gen K 0 t H k s); lia. Qed.

Lemma tm_subst_env_open_rec : forall th s x k t,
  (forall y, locally_closed_tm (th y)) ->
  ~ In x (tm_fv t) ->
  tm_subst_env (fun y => if Nat.eqb x y then s else th y)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k s (tm_subst_env th t).
Proof.
  intros th s x k t Hth; revert k.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros k H; simpl in *.
  - destruct (Nat.eqb k i) eqn:E; simpl.
    + rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - simpl in H. destruct (Nat.eqb x y) eqn:E.
    + exfalso. apply H. apply Nat.eqb_eq in E; subst; simpl; auto.
    + rewrite (open_tm_rec_lc 0 k (th y) s (Hth y)); reflexivity.
  - simpl. f_equal. apply IH. exact H.
  - simpl. f_equal.
    + apply IH1. intro H1; apply H. rewrite in_app_iff; auto.
    + apply IH2. intro H2; apply H. rewrite in_app_iff; auto.
  - simpl. f_equal. apply IH. exact H.
  - simpl. f_equal. apply IH. exact H.
Qed.

Lemma tm_subst_env_open : forall th s x t,
  (forall y, locally_closed_tm (th y)) ->
  ~ In x (tm_fv t) ->
  tm_subst_env (fun y => if Nat.eqb x y then s else th y)
    (open_tm t (tm_fvar x)) =
  open_tm (tm_subst_env th t) s.
Proof. intros; apply tm_subst_env_open_rec; assumption. Qed.

Lemma open_ty_rec_lc_gen : forall K T,
  lc_ty_at K T -> forall k U, K <= k -> open_ty_rec k U T = T.
Proof.
  intros K T H; induction H; intros k' U Hk; simpl.
  - destruct (Nat.eqb k' i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal; [apply IHlc_ty_at1|apply IHlc_ty_at2]; assumption.
  - f_equal. apply IHlc_ty_at. lia.
Qed.

Lemma open_tm_ty_rec_lc_gen : forall K t,
  lc_tm_at K 0 t -> forall k U, K <= k -> open_tm_ty_rec k U t = t.
Proof.
  intros K t H; induction H; intros k' U Hk; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply open_ty_rec_lc_gen with (K:=K); assumption.
    + apply IHlc_tm_at; assumption.
  - f_equal; [apply IHlc_tm_at1|apply IHlc_tm_at2]; assumption.
  - f_equal. apply IHlc_tm_at. lia.
  - f_equal; [apply IHlc_tm_at|apply open_ty_rec_lc_gen with (K:=K)]; assumption.
Qed.

Lemma open_tm_ty_lc : forall t U,
  locally_closed_tm t -> open_tm_ty t U = t.
Proof.
  intros t U H; unfold locally_closed_tm in H; unfold open_tm_ty.
  exact (open_tm_ty_rec_lc_gen 0 t H 0 U (le_n 0)).
Qed.

Lemma tm_subst_env_open_ty_rec : forall th U k t,
  (forall y, locally_closed_tm (th y)) ->
  tm_subst_env th (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (tm_subst_env th t).
Proof.
  intros th U k t Hth; revert k;
    induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T]; intros k; simpl.
  - reflexivity.
  - rewrite (open_tm_ty_rec_lc_gen 0 (th x) (Hth x) k U (le_0_n k)); reflexivity.
  - change (tm_abs (open_ty_rec k U T) (tm_subst_env th (open_tm_ty_rec k U t)) =
      tm_abs (open_ty_rec k U T) (open_tm_ty_rec k U (tm_subst_env th t))).
    f_equal; exact (IH k).
  - change (tm_app (tm_subst_env th (open_tm_ty_rec k U t1))
      (tm_subst_env th (open_tm_ty_rec k U t2)) =
      tm_app (open_tm_ty_rec k U (tm_subst_env th t1))
        (open_tm_ty_rec k U (tm_subst_env th t2))).
    rewrite (IH1 k), (IH2 k); reflexivity.
  - change (tm_tabs (tm_subst_env th (open_tm_ty_rec (S k) U t)) =
      tm_tabs (open_tm_ty_rec (S k) U (tm_subst_env th t))).
    f_equal; apply IH.
  - change (tm_tapp (tm_subst_env th (open_tm_ty_rec k U t))
      (open_ty_rec k U T) =
      tm_tapp (open_tm_ty_rec k U (tm_subst_env th t))
        (open_ty_rec k U T)).
    f_equal; apply IH.
Qed.

Lemma tm_subst_env_open_ty : forall th U t,
  (forall y, locally_closed_tm (th y)) ->
  tm_subst_env th (open_tm_ty t U) =
  open_tm_ty (tm_subst_env th t) U.
Proof. intros; apply tm_subst_env_open_ty_rec; assumption. Qed.

Lemma lc_tm_weaken : forall K k t,
  lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H; induction H; eauto using lc_ty_at.
Qed.

Lemma lc_tm_open_inv : forall K k s t,
  locally_closed_tm s ->
  lc_tm_at K k (open_tm_rec k s t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k s t; revert K k.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros K k Hs H; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + constructor; apply Nat.eqb_eq in E; lia.
    + inversion H; constructor; apply Nat.eqb_neq in E; lia.
  - constructor; lia.
  - inversion H; subst. constructor.
    + assumption.
    + apply IH with (K:=K) (k:=S k); auto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T -> lc_ty_at (S K) T.
Proof.
  intros K T H; induction H; eauto.
Qed.

Lemma lc_ty_raise : forall K T, locally_closed_ty T -> lc_ty_at K T.
Proof.
  intros K T H; induction K; [exact H|apply lc_ty_weaken; assumption].
Qed.

Lemma lc_ty_open_inv : forall K k U T,
  locally_closed_ty U ->
  lc_ty_at K (open_ty_rec (k + K) U T) ->
  lc_ty_at (S k + K) T.
Proof.
  intros K k U T HU; revert K k.
  induction T as [i|X|T1 IH1 T2 IH2|T IH];
    intros K k H; simpl in *.
  - destruct (Nat.eqb (k + K) i) eqn:E.
    + constructor. apply Nat.eqb_eq in E; lia.
    + inversion H; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst. constructor.
    replace (S (S (k + K))) with (S (k + S K)) by lia.
    eapply IH with (K:=S K) (k:=k).
    replace (k + S K) with (S (k + K)) by lia.
    exact H2.
Qed.

Lemma lc_tm_ty_open_inv : forall K k U t n,
  locally_closed_ty U ->
  lc_tm_at K n (open_tm_ty_rec (k + K) U t) ->
  lc_tm_at (S k + K) n t.
Proof.
  intros K k U t n HU; revert K k n.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros K k n H; simpl in *.
  - inversion H; constructor; assumption.
  - constructor.
  - inversion H; subst. constructor.
    + apply lc_ty_open_inv with (K:=K) (k:=k) (U:=U); [exact HU|exact H4].
    + apply IH with (K:=K) (k:=k) (n:=S n); exact H5.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor.
    replace (S (S (k + K))) with (S (k + S K)) by lia.
    eapply IH with (K:=S K) (k:=k) (n:=n).
    replace (k + S K) with (S (k + K)) by lia.
    exact H3.
  - inversion H; subst. constructor.
    + eapply IH; eauto.
    + eapply lc_ty_open_inv; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H as
    [Delta X Hin
    | Delta T1 T2 H1 IH1 H2 IH2
    | L Delta T H IH].
  - constructor.
  - constructor; assumption.
  - constructor.
    apply lc_ty_open_inv with (K:=0) (k:=0) (U:=Ty_FVar (S (list_max L))).
    + constructor.
    + exact (IH (S (list_max L)) (fresh_not_in L)).
Qed.

Lemma lc_ty_open_preserve : forall K T U,
  lc_ty_at (S K) T -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K T U; revert K.
  induction T as [i|X|T1 IH1 T2 IH2|T IH];
    intros K Hlc HU; simpl in *.
  - destruct (Nat.eqb K i) eqn:E.
    + exact HU.
    + inversion Hlc; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst. constructor.
    apply IH with (K:=S K).
    + assumption.
    + apply lc_ty_weaken; assumption.
Qed.

Lemma has_type_ty_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H as
    [Delta Gamma x T Hlookup Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 Hf IHf Ha IHa
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IHt Hwf].
  - apply wf_ty_lc with (Delta:=Delta); assumption.
  - constructor.
    + apply wf_ty_lc with (Delta:=Delta); assumption.
    + exact (IHbody (S (list_max L)) (fresh_not_in L)).
  - inversion IHf; assumption.
  - constructor.
    apply lc_ty_open_inv with (K:=0) (k:=0) (U:=Ty_FVar (S (list_max L))).
    + constructor.
    + exact (IHbody (S (list_max L)) (fresh_not_in L)).
  - apply lc_ty_open_preserve with (K:=0).
    + inversion IHt; assumption.
    + apply wf_ty_lc with (Delta:=Delta); assumption.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H as
    [Delta Gamma x T Hlookup Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 Hf IHf Ha IHa
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IHt Hwf].
  - constructor.
  - refine (lc_tm_abs 0 0 T1 t2 (wf_ty_lc Delta T1 Hwf) _).
    apply lc_tm_open_inv with (K:=0) (k:=0) (s:=tm_fvar (S (list_max L))).
    + constructor.
    + exact (IHbody (S (list_max L)) (fresh_not_in L)).
  - constructor; assumption.
  - constructor.
    apply lc_tm_ty_open_inv with (K:=0) (k:=0) (U:=Ty_FVar (S (list_max L))).
    * constructor.
    * exact (IHbody (S (list_max L)) (fresh_not_in L)).
  - apply (lc_tm_tapp 0 0 t U).
    + exact IHt.
    + apply wf_ty_lc with (Delta:=Delta); assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma lc_tm_ty_weaken : forall K k t,
  lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H; induction H; eauto using lc_ty_weaken.
Qed.

Lemma lc_tm_raise : forall K n k t,
  lc_tm_at K n t -> n <= k -> lc_tm_at K k t.
Proof.
  intros K n k t H Hle; induction Hle.
  - exact H.
  - apply lc_tm_weaken; exact IHHle.
Qed.

Lemma tm_subst_env_lc_gen : forall K k t th,
  lc_tm_at K k t ->
  (forall x, lc_tm_at K 0 (th x)) ->
  lc_tm_at K k (tm_subst_env th t).
Proof.
  intros K k t th; revert K k th.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros K k th H Hth; inversion H; subst; simpl.
  - constructor; assumption.
  - apply lc_tm_raise with (n:=0); [apply Hth|lia].
  - constructor.
    + assumption.
    + apply IH with (K:=K) (k:=S k) (th:=th).
      * exact H5.
      * intros y; apply lc_tm_raise with (n:=0); [exact (Hth y)|lia].
  - constructor.
    + apply IH1 with (K:=K) (k:=k); assumption.
    + apply IH2 with (K:=K) (k:=k); assumption.
  - constructor. apply IH with (K:=S K) (k:=k) (th:=th).
    + exact H3.
    + intros y; apply lc_tm_ty_weaken; exact (Hth y).
  - constructor.
    + apply IH with (K:=K) (k:=k); assumption.
    + assumption.
Qed.

Lemma tm_subst_env_lc : forall t th,
  locally_closed_tm t ->
  (forall x, locally_closed_tm (th x)) ->
  locally_closed_tm (tm_subst_env th t).
Proof.
  intros t th H Hth; unfold locally_closed_tm in *.
  apply tm_subst_env_lc_gen with (K:=0) (k:=0); assumption.
Qed.

Definition tm_env_rel (eta : list binary_candidate) (rho : binary_env)
    (Gamma : context) (th1 th2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation eta rho T (th1 x) (th2 x).

Definition tm_env_lc (th : atom -> tm) : Prop :=
  forall x, locally_closed_tm (th x).

Lemma tm_subst_env_fvar : forall th x, tm_subst_env th (tm_fvar x) = th x.
Proof. reflexivity. Qed.

Lemma tm_env_rel_update : forall eta rho Gamma th1 th2 x T arg1 arg2,
  tm_env_rel eta rho Gamma th1 th2 ->
  value_relation eta rho T arg1 arg2 ->
  tm_env_rel eta rho (update Gamma x T)
    (fun y => if Nat.eqb x y then arg1 else th1 y)
    (fun y => if Nat.eqb x y then arg2 else th2 y).
Proof.
  intros eta rho Gamma th1 th2 x T arg1 arg2 Hrel Harg y S Hlookup.
  simpl in Hlookup. destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. rewrite Nat.eqb_eq in E; subst.
    rewrite Nat.eqb_refl; exact Harg.
  - assert (E' : Nat.eqb x y = false).
    { apply Nat.eqb_neq; intro E'; apply Nat.eqb_neq in E; apply E; symmetry; exact E'. }
    rewrite E'. apply Hrel; exact Hlookup.
Qed.

Lemma tm_env_lc_update : forall th x a,
  tm_env_lc th -> locally_closed_tm a ->
  tm_env_lc (fun y => if Nat.eqb x y then a else th y).
Proof.
  intros th x a H lc y; destruct (Nat.eqb x y); auto.
Qed.

Lemma expr_intro : forall R t1 t2 v1 v2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  evaluates t1 v1 -> evaluates t2 v2 -> R v1 v2 ->
  expression_lifting R t1 t2.
Proof.
  intros R t1 t2 v1 v2 Hlc1 Hlc2 He1 He2 HR.
  unfold expression_lifting, results_match.
  split; [exact Hlc1|].
  split; [exact Hlc2|].
  exists v1, v2; repeat split; assumption.
Qed.

Lemma value_relation_values : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  intros eta rho T; induction T as [i|X|T1 IH1 T2 IH2|T IH]; simpl.
  - destruct (nth_error eta i) as [a|] eqn:E; [apply a.(candidate_values)|contradiction].
  - destruct (rho X) as [a|] eqn:E; [apply a.(candidate_values)|contradiction].
  - intuition.
  - intuition.
Qed.

Lemma expression_lifting_mono : forall R1 R2 t1 t2,
  (forall v1 v2, R1 v1 v2 -> R2 v1 v2) ->
  expression_lifting R1 t1 t2 -> expression_lifting R2 t1 t2.
Proof.
  intros R1 R2 t1 t2 Hmono Hrel.
  unfold expression_lifting, results_match in Hrel |-.
  destruct Hrel as [Hlc1 [Hlc2 Hres]].
  destruct Hres as [v1 [v2 [He1 [He2 HR]]]].
  repeat split; [exact Hlc1|exact Hlc2|].
  exists v1, v2; repeat split; try assumption; apply Hmono; exact HR.
Qed.

Fixpoint insert_candidate (k : nat) (a : binary_candidate)
    (eta : list binary_candidate) : list binary_candidate :=
  match k, eta with
  | 0, _ => a :: eta
  | S k', b :: eta' => b :: insert_candidate k' a eta'
  | S _, [] => []
  end.

Lemma nth_insert_lt : forall k a eta i,
  i < k -> nth_error (insert_candidate k a eta) i = nth_error eta i.
Proof.
  induction k as [|k IH]; intros a eta i Hi; [lia|].
  destruct eta as [|b eta].
  - simpl; reflexivity.
  - destruct i as [|i]; simpl.
    + reflexivity.
    + apply IH; lia.
Qed.

Lemma nth_insert_eq : forall k a eta,
  k <= length eta -> nth_error (insert_candidate k a eta) k = Some a.
Proof.
  induction k as [|k IH]; intros a eta Hlen; simpl; auto.
  destruct eta as [|b eta]; simpl in Hlen; [lia|].
  simpl. apply IH. lia.
Qed.

Lemma value_relation_open_rec : forall k eta rho U T a,
  k <= length eta ->
  locally_closed_ty U ->
  lc_ty_at (S k) T ->
  (forall v1 v2, a.(candidate_relation) v1 v2 <->
    value_relation eta rho U v1 v2) ->
  (forall v1 v2,
    value_relation (insert_candidate k a eta) rho T v1 v2 <->
    value_relation eta rho (open_ty_rec k U T) v1 v2).
Proof.
  (* This is proved by structural induction on the type.  The two small
     nth-error lemmas above are exactly the locally-nameless bookkeeping at
     the variable case. *)
  intros k eta rho U T a Hlen HU; revert k eta a Hlen.
  induction T as [i|X|T1 IH1 T2 IH2|T IH];
    intros k eta a Hlen Hlc Hopen; simpl in *.
  - inversion Hlc; subst.
    intro v1; intro v2.
    destruct (Nat.eqb k i) eqn:E.
    + rewrite Nat.eqb_eq in E; subst.
      rewrite (nth_insert_eq i a eta Hlen); simpl.
      exact (Hopen v1 v2).
    + rewrite (nth_insert_lt k a eta i).
      { reflexivity. }
      apply Nat.eqb_neq in E. lia.
  - intuition.
  - inversion Hlc; subst. simpl.
    intro v1; intro v2; split; intro H.
    + destruct H as [Hv1 [Hv2 Hrest]].
      destruct Hrest as [A [b1 [B [b2 [Heq1 [Heq2 Hfun]]]]]].
      split; [exact Hv1|].
      split; [exact Hv2|].
      exists A,b1,B,b2.
      split; [exact Heq1|].
      split; [exact Heq2|].
      intros p1 p2 Harg.
      apply expression_lifting_mono with
        (R1:=value_relation (insert_candidate k a eta) rho T2)
        (R2:=value_relation eta rho (open_ty_rec k U T2)).
      * intros z1 z2 Hz.
        apply (proj1 (IH2 k eta a Hlen H3 Hopen z1 z2)).
        exact Hz.
      * apply (Hfun p1 p2).
        apply (proj2 (IH1 k eta a Hlen H2 Hopen p1 p2)).
        exact Harg.
    + destruct H as [Hv1 [Hv2 Hrest]].
      destruct Hrest as [A [b1 [B [b2 [Heq1 [Heq2 Hfun]]]]]].
      split; [exact Hv1|].
      split; [exact Hv2|].
      exists A,b1,B,b2.
      split; [exact Heq1|].
      split; [exact Heq2|].
      intros p1 p2 Harg.
      apply expression_lifting_mono with
        (R1:=value_relation eta rho (open_ty_rec k U T2))
        (R2:=value_relation (insert_candidate k a eta) rho T2).
      * intros z1 z2 Hz.
        apply (proj2 (IH2 k eta a Hlen H3 Hopen z1 z2)).
        exact Hz.
      * apply (Hfun p1 p2).
        apply (proj1 (IH1 k eta a Hlen H2 Hopen p1 p2)).
        exact Harg.
  - inversion Hlc; subst. simpl. firstorder; eauto.
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
  (* Complete the proof of the free theorem. *)
Qed.

End SystemFParametricityNoneMediumTask.
