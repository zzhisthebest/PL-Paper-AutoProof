(** System F CBV strong-normalization benchmark, Medium variant.
    Features: none. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNoneMediumTask.

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

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

Definition type_substitution := atom -> ty.

Definition term_substitution := atom -> tm.

Fixpoint instantiate_ty (theta : type_substitution) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (instantiate_ty theta T1) (instantiate_ty theta T2)
  | Ty_All T1 => Ty_All (instantiate_ty theta T1)
  end.

Fixpoint instantiate
    (theta : type_substitution) (gamma : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T t1 => tm_abs (instantiate_ty theta T) (instantiate theta gamma t1)
  | tm_app t1 t2 => tm_app (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_tabs t1 => tm_tabs (instantiate theta gamma t1)
  | tm_tapp t1 T => tm_tapp (instantiate theta gamma t1) (instantiate_ty theta T)
  end.

Definition type_substitution_closed (theta : type_substitution) : Prop :=
  forall X : atom, locally_closed_ty (theta X).

Definition term_substitution_closed (gamma : term_substitution) : Prop :=
  forall x : atom, locally_closed_tm (gamma x).

Definition relation := tm -> Prop.
Record value_candidate := {
  candidate_relation : relation;
  candidate_values : forall v, candidate_relation v -> value v
}.
Definition relation_env := atom -> option value_candidate.
Definition relation_update (rho : relation_env) (X : atom) (a : value_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition expression_lifting (R : relation) (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t /\
  forall v, t -->* v -> value v -> R v.

Fixpoint value_relation (eta : list value_candidate) (rho : relation_env)
    (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v | None => False end
  | Ty_Arrow T1 T2 =>
      value v /\ exists U body, v = tm_abs U body /\
      forall arg, value_relation eta rho T1 arg ->
        expression_lifting (value_relation eta rho T2) (open_tm body arg)
  | Ty_All T =>
      value v /\ exists body, v = tm_tabs body /\
      forall (U : ty) (a : value_candidate), locally_closed_ty U ->
        expression_lifting (value_relation (a :: eta) rho T) (open_tm_ty body U)
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

(* A few elementary finite-support facts.  They are kept here, rather than
   hidden in the statement of the fundamental theorem, since the typing
   rules use the usual locally-nameless freshness convention. *)
Fixpoint tm_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => tm_vars t1
  | tm_app t1 t2 => tm_vars t1 ++ tm_vars t2
  | tm_tabs t1 => tm_vars t1
  | tm_tapp t1 _ => tm_vars t1
  end.

Fixpoint ty_vars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_vars T1 ++ ty_vars T2
  | Ty_All T1 => ty_vars T1
  end.

Fixpoint ctx_vars (G : context) : list atom :=
  match G with
  | [] => []
  | (x, _) :: G' => x :: ctx_vars G'
  end.

Fixpoint fresh (l : list atom) : atom :=
  match l with
  | [] => 0
  | x :: l' => S (Nat.max x (fresh l'))
  end.

Lemma In_fresh_lt : forall x l, In x l -> x < fresh l.
Proof.
  intros x l. revert x.
  induction l as [|a l IH].
  - simpl. contradiction.
  - simpl. intros x H. destruct H as [->|H].
    + lia.
    + specialize (IH x H). lia.
Qed.

Lemma fresh_not_In : forall l, ~ In (fresh l) l.
Proof.
  intros l H. pose proof (In_fresh_lt (fresh l) l H). lia.
Qed.

Lemma tm_subst_notin : forall x s t,
    ~ In x (tm_vars t) -> tm_subst x s t = t.
Proof.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    simpl; intros H; try reflexivity.
  - destruct (Nat.eqb x y) eqn:E; simpl in H; try reflexivity.
    exfalso. apply H. apply Nat.eqb_eq in E. now left.
  - f_equal. apply IH. exact H.
  - assert (H1 : ~ In x (tm_vars t1)).
    { intro K. apply H. apply in_app_iff. now left. }
    assert (H2 : ~ In x (tm_vars t2)).
    { intro K. apply H. apply in_app_iff. now right. }
    f_equal; [apply IH1 | apply IH2]; assumption.
  - f_equal. apply IH. exact H.
  - f_equal. apply IH. exact H.
Qed.

Lemma lookup_update_eq : forall x T G,
    lookup_context x ((x,T)::G) = Some T.
Proof. intros; simpl. now rewrite Nat.eqb_refl. Qed.

Lemma lookup_update_neq : forall x y T G,
    x <> y -> lookup_context x ((y,T)::G) = lookup_context x G.
Proof.
  intros x y T G H. simpl. destruct (Nat.eqb x y) eqn:E.
  - exfalso. apply H. now apply Nat.eqb_eq.
  - reflexivity.
Qed.

Lemma lookup_update_inv : forall x y T G U,
    lookup_context y ((x,T)::G) = Some U ->
    (y = x /\ U = T) \/ (y <> x /\ lookup_context y G = Some U).
Proof.
  intros. simpl in H. destruct (Nat.eqb y x) eqn:E.
  - left. split; [apply Nat.eqb_eq in E; auto | inversion H; auto].
  - right. split.
    + intro C. subst y. rewrite Nat.eqb_refl in E. discriminate.
    + exact H.
Qed.

Lemma tm_subst_open_rec : forall k x s t y,
    x <> y ->
    ~ In x (tm_vars t) ->
    tm_subst x s (open_tm_rec k (tm_fvar y) t) =
    open_tm_rec k (tm_fvar y) (tm_subst x s t).
Proof.
  intros k x s t. revert k.
  induction t as [i|z|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros k y Hxy Hfresh; simpl in *; try reflexivity.
  - destruct (Nat.eqb k i) eqn:E; simpl.
    + destruct (Nat.eqb x y) eqn:E2.
      * exfalso. apply Hxy. now apply Nat.eqb_eq.
      * reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x z) eqn:E; simpl.
    + exfalso. apply Hfresh. left. symmetry. now apply Nat.eqb_eq.
    + reflexivity.
  - rewrite (IH (S k) y Hxy Hfresh). reflexivity.
  - assert (H1 : ~ In x (tm_vars t1)).
    { intro K. apply Hfresh. apply in_app_iff. now left. }
    assert (H2 : ~ In x (tm_vars t2)).
    { intro K. apply Hfresh. apply in_app_iff. now right. }
    rewrite (IH1 k y Hxy H1). rewrite (IH2 k y Hxy H2). reflexivity.
  - rewrite (IH k y Hxy Hfresh). reflexivity.
  - rewrite (IH k y Hxy Hfresh). reflexivity.
Qed.

Lemma tm_subst_open : forall x s t y,
    x <> y ->
    ~ In x (tm_vars t) ->
    tm_subst x s (open_tm t (tm_fvar y)) =
    open_tm (tm_subst x s t) (tm_fvar y).
Proof. intros; apply tm_subst_open_rec; assumption. Qed.

Lemma open_tm_rec_lc : forall K n t s k,
    n <= k -> lc_tm_at K n t -> open_tm_rec k s t = t.
Proof.
  intros K n t s k Hkn Hlc. revert k Hkn.
  induction Hlc; intros q Hkn; simpl.
  - destruct (Nat.eqb q i) eqn:E; simpl.
    + exfalso. apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - f_equal. apply IHHlc. lia.
  - f_equal; [apply IHHlc1 | apply IHHlc2]; lia.
  - f_equal. apply IHHlc. exact Hkn.
  - f_equal. apply IHHlc. exact Hkn.
Qed.

Lemma instantiate_open_fresh_rec : forall k theta gamma x s t,
    ~ In x (tm_vars t) ->
    (forall y, locally_closed_tm (gamma y)) ->
    instantiate theta (fun y => if Nat.eqb x y then s else gamma y)
      (open_tm_rec k (tm_fvar x) t) =
    open_tm_rec k s (instantiate theta gamma t).
Proof.
  intros k theta gamma x s t H Hgamma. revert k.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    simpl in *; try reflexivity.
  - intros k. destruct (Nat.eqb k i) eqn:E; simpl.
    + destruct (Nat.eqb x x) eqn:E2; simpl.
      * reflexivity.
      * rewrite Nat.eqb_refl in E2. discriminate.
    + reflexivity.
  - intros k. destruct (Nat.eqb x y) eqn:E.
    + exfalso. apply H. apply Nat.eqb_eq in E. now left.
    + rewrite (open_tm_rec_lc 0 0 (gamma y) s k).
      * reflexivity.
      * lia.
      * exact (Hgamma y).
  - intros k. f_equal. apply IH. exact H.
  - assert (H1 : ~ In x (tm_vars t1)).
    { intro K. apply H. apply in_app_iff. now left. }
    assert (H2 : ~ In x (tm_vars t2)).
    { intro K. apply H. apply in_app_iff. now right. }
    intros k. rewrite (IH1 H1 k), (IH2 H2 k). reflexivity.
  - intros k. f_equal. apply IH. exact H.
  - intros k. f_equal. apply IH. exact H.
Qed.

Lemma instantiate_open_fresh : forall theta gamma x s t,
    ~ In x (tm_vars t) ->
    (forall y, locally_closed_tm (gamma y)) ->
    instantiate theta (fun y => if Nat.eqb x y then s else gamma y)
      (open_tm t (tm_fvar x)) =
    open_tm (instantiate theta gamma t) s.
Proof. intros; apply instantiate_open_fresh_rec; assumption. Qed.

Lemma lc_ty_open_inv : forall K U T,
    lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  intros K U T. revert K U.
  induction T as [i|X|T1 IH1 T2 IH2|T IH]; intros K U H; simpl in H.
  - destruct (Nat.eqb K i) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + inversion H. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion H. constructor; [apply IH1 with (K:=K) (U:=U) | apply IH2 with (K:=K) (U:=U)]; assumption.
  - inversion H. constructor. apply IH with (K:=S K) (U:=U). assumption.
Qed.

Lemma lc_tm_open_inv : forall K k u t,
    lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k u t. revert K k u.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros K k u H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + inversion H. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion H. constructor; [assumption | apply IH with (K:=K) (k:=S k) (u:=u); assumption].
  - inversion H. constructor; [apply IH1 with (K:=K) (k:=k) (u:=u) | apply IH2 with (K:=K) (k:=k) (u:=u)]; assumption.
  - inversion H. constructor. apply IH with (K:=S K) (k:=k) (u:=u). assumption.
  - inversion H. constructor.
    + apply IH with (K:=K) (k:=k) (u:=u). assumption.
    + assumption.
Qed.

Lemma lc_tm_ty_open_inv : forall K k U t,
    lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  intros K k U t. revert K k U.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros K k U H; simpl in H.
  - constructor; inversion H; assumption.
  - constructor.
  - inversion H. constructor.
    + apply lc_ty_open_inv with (K:=K) (U:=U). assumption.
    + apply IH with (K:=K) (k:=S k) (U:=U). assumption.
  - inversion H. constructor.
    + apply IH1 with (K:=K) (k:=k) (U:=U). assumption.
    + apply IH2 with (K:=K) (k:=k) (U:=U). assumption.
  - inversion H. constructor. apply IH with (K:=S K) (k:=k) (U:=U). assumption.
  - inversion H. constructor.
    + apply IH with (K:=K) (k:=k) (U:=U). assumption.
    + apply lc_ty_open_inv with (K:=K) (U:=U). assumption.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H.
  - constructor.
  - constructor; assumption.
  - constructor. specialize (H (fresh L)).
    assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_In.
    specialize (H Hfresh). apply lc_ty_open_inv with (K:=0) (U:=Ty_FVar (fresh L)).
    apply H0. exact Hfresh.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
    has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H as
    [Delta Gamma x T Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IHt Hwu].
  - constructor.
  - unfold locally_closed_tm. constructor.
    + apply (wf_ty_lc Delta T1). assumption.
    + specialize (IHbody (fresh L)).
      assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_In.
      specialize (IHbody Hfresh). apply lc_tm_open_inv with (K:=0) (k:=0) (u:=tm_fvar (fresh L)).
      exact IHbody.
  - constructor; assumption.
  - unfold locally_closed_tm. constructor.
    specialize (Hbody (fresh L)).
    assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_In.
    specialize (Hbody Hfresh). apply lc_tm_ty_open_inv with (K:=0) (k:=0) (U:=Ty_FVar (fresh L)).
    exact (IHbody (fresh L) Hfresh).
  - constructor; [assumption | apply (wf_ty_lc Delta U); assumption].
Qed.

Definition id_theta : type_substitution := fun X => Ty_FVar X.

Lemma instantiate_ty_id : forall T, instantiate_ty id_theta T = T.
Proof.
  induction T as [| |T1 IH1 T2 IH2|T IH]; simpl; try reflexivity.
  - now rewrite IH1, IH2.
  - now rewrite IH.
Qed.

Lemma lc_ty_any_gen : forall n T, lc_ty_at n T ->
    forall K, n <= K -> lc_ty_at K T.
Proof.
  intros n T H. revert n H.
  induction T as [i|X|T1 IH1 T2 IH2|T IH]; intros n H K HnK.
  - inversion H. constructor. lia.
  - constructor.
  - inversion H. constructor; [apply IH1 with (n:=n) | apply IH2 with (n:=n)]; assumption.
  - inversion H. constructor. apply IH with (n:=S n) (K:=S K).
    + exact H2.
    + exact (le_n_S n K HnK).
Qed.

Lemma lc_ty_any : forall T, lc_ty_at 0 T -> forall K, lc_ty_at K T.
Proof. intros T H K. eapply lc_ty_any_gen; [exact H | lia]. Qed.

Lemma lc_tm_any_gen : forall K0 n t, lc_tm_at K0 n t ->
    forall K m, K0 <= K -> n <= m -> lc_tm_at K m t.
Proof.
  intros K0 n t H. revert K0 n H.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros K0 n H K m HKK Hnm; simpl in H.
  - inversion H. constructor. lia.
  - constructor.
  - inversion H. constructor.
    + eapply lc_ty_any_gen; [exact H4 | exact HKK].
    + apply IH with (K0:=K0) (n:=S n) (K:=K) (m:=S m).
      * exact H5.
      * exact HKK.
      * exact (le_n_S n m Hnm).
  - inversion H. constructor.
    + apply IH1 with (K0:=K0) (n:=n) (K:=K) (m:=m); assumption.
    + apply IH2 with (K0:=K0) (n:=n) (K:=K) (m:=m); assumption.
  - inversion H. constructor. apply IH with (K0:=S K0) (n:=n) (K:=S K) (m:=m).
    + exact H3.
    + exact (le_n_S K0 K HKK).
    + exact Hnm.
  - inversion H. constructor.
    + apply IH with (K0:=K0) (n:=n) (K:=K) (m:=m); assumption.
    + eapply lc_ty_any_gen; [exact H5 | exact HKK].
Qed.

Lemma lc_tm_any : forall n t, lc_tm_at 0 n t ->
    forall K m, n <= m -> lc_tm_at K m t.
Proof. intros n t H K m Hnm. eapply lc_tm_any_gen; [exact H | lia | exact Hnm]. Qed.

Lemma instantiate_lc : forall gamma K k t,
    (forall x, locally_closed_tm (gamma x)) ->
    lc_tm_at K k t ->
    lc_tm_at K k (instantiate id_theta gamma t).
Proof.
  intros gamma K k t Hgamma Hlc. induction Hlc; simpl.
  - constructor; assumption.
  - apply (lc_tm_any 0 (gamma x) (Hgamma x) K k). lia.
  - constructor.
    + rewrite instantiate_ty_id. assumption.
    + apply IHHlc.
  - constructor; assumption.
  - constructor. apply IHHlc.
  - constructor; [apply IHHlc | rewrite instantiate_ty_id; assumption].
Qed.

Fixpoint insert_candidate (k : nat) (a : value_candidate)
    (eta : list value_candidate) : list value_candidate :=
  match k, eta with
  | 0, _ => a :: eta
  | S k', b :: eta' => b :: insert_candidate k' a eta'
  | S _, [] => []
  end.

Lemma insert_candidate_nth_lt : forall k eta a i,
    length eta = k -> i < k ->
    nth_error (insert_candidate k a eta) i = nth_error eta i.
Proof.
  induction k as [|k IH]; intros eta a i Hlen Hlt.
  - lia.
  - destruct eta as [|b eta].
    + simpl in Hlen. discriminate.
    + simpl in Hlen, Hlt. destruct i as [|i].
      * reflexivity.
      * simpl. apply IH; lia.
Qed.

Lemma insert_candidate_nth_eq : forall k eta a,
    length eta = k ->
    nth_error (insert_candidate k a eta) k = Some a.
Proof.
  induction k as [|k IH]; intros eta a Hlen.
  - reflexivity.
  - destruct eta as [|b eta].
    + simpl in Hlen. discriminate.
    + simpl in Hlen. simpl. apply IH. lia.
Qed.

Lemma expression_lifting_map : forall R S t,
    (forall v, value v -> R v -> S v) ->
    expression_lifting R t -> expression_lifting S t.
Proof.
  intros R S t Hmap [Hlc [Hsn Hlast]]. split; [exact Hlc | split; [exact Hsn |]].
  intros v Hmulti Hv. apply Hmap; [assumption | apply Hlast; assumption].
Qed.

Lemma value_relation_open_iff : forall k eta rho X a T v,
    length eta = k ->
    lc_ty_at (S k) T ->
    ~ In X (ty_vars T) ->
    (value_relation eta (relation_update rho X a)
       (open_ty_rec k (Ty_FVar X) T) v ->
       value_relation (insert_candidate k a eta) rho T v) /\
    (value_relation (insert_candidate k a eta) rho T v ->
       value_relation eta (relation_update rho X a)
         (open_ty_rec k (Ty_FVar X) T) v).
Proof.
  intros k eta rho X a T v Hlen Hlc Hfresh.
  revert k eta rho X a v Hlen Hlc Hfresh.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH];
    intros k eta rho X a v Hlen Hlc Hfresh; simpl in *.
  - inversion Hlc. split; intro Hrel.
    + destruct (Nat.eqb k i) eqn:E.
      * apply Nat.eqb_eq in E. rewrite <- E.
        cbn [value_relation] in Hrel.
        assert (Hupd : relation_update rho X a X = Some a).
        { unfold relation_update. rewrite Nat.eqb_refl. reflexivity. }
        rewrite Hupd in Hrel. simpl in Hrel.
        rewrite (insert_candidate_nth_eq k eta a Hlen).
        exact Hrel.
      * apply Nat.eqb_neq in E. assert (Hi : i < k) by lia.
        cbn [value_relation] in Hrel.
        rewrite (insert_candidate_nth_lt k eta a i Hlen Hi).
        exact Hrel.
    + destruct (Nat.eqb k i) eqn:E.
      * apply Nat.eqb_eq in E. rewrite <- E in Hrel.
        cbn [value_relation] in Hrel.
        rewrite (insert_candidate_nth_eq k eta a Hlen) in Hrel.
        cbn [value_relation].
        assert (Hupd : relation_update rho X a X = Some a).
        { unfold relation_update. rewrite Nat.eqb_refl. reflexivity. }
        rewrite Hupd. exact Hrel.
      * apply Nat.eqb_neq in E. assert (Hi : i < k) by lia.
        cbn [value_relation] in Hrel.
        rewrite (insert_candidate_nth_lt k eta a i Hlen Hi) in Hrel.
        exact Hrel.
  - destruct (Nat.eqb X Y) eqn:E; split; intro Hrel.
    + apply Nat.eqb_eq in E. subst Y. exfalso. apply Hfresh. simpl. now left.
    + apply Nat.eqb_eq in E. subst Y. exfalso. apply Hfresh. simpl. now left.
    + cbn [value_relation] in Hrel. cbn [value_relation].
      assert (Hupd : relation_update rho X a Y = rho Y).
      { unfold relation_update. rewrite E. reflexivity. }
      rewrite Hupd in Hrel. exact Hrel.
    + cbn [value_relation] in Hrel. cbn [value_relation].
      assert (Hupd : relation_update rho X a Y = rho Y).
      { unfold relation_update. rewrite E. reflexivity. }
      rewrite Hupd. exact Hrel.
  - inversion Hlc.
    assert (HF1 : ~ In X (ty_vars T1)).
    { intro Hin. apply Hfresh. apply in_app_iff. now left. }
    assert (HF2 : ~ In X (ty_vars T2)).
    { intro Hin. apply Hfresh. apply in_app_iff. now right. }
    split; intro Hrel.
    + destruct Hrel as [Hv [U [body [Heq Hfun]]]].
      split; [exact Hv |]. exists U, body. split; [exact Heq |]. intros arg Harg.
      apply expression_lifting_map with
        (R:=value_relation eta (relation_update rho X a) (open_ty_rec k (Ty_FVar X) T2))
        (S:=value_relation (insert_candidate k a eta) rho T2)
        (t:=open_tm body arg).
      * intros w Hw Hwrel.
        apply (proj1 (IH2 k eta rho X a w Hlen H3
          HF2)).
        exact Hwrel.
      * apply Hfun.
        apply (proj2 (IH1 k eta rho X a arg Hlen H2 HF1)).
        exact Harg.
    + destruct Hrel as [Hv [U [body [Heq Hfun]]]].
      split; [exact Hv |]. exists U, body. split; [exact Heq |]. intros arg Harg.
      apply expression_lifting_map with
        (R:=value_relation (insert_candidate k a eta) rho T2)
        (S:=value_relation eta (relation_update rho X a) (open_ty_rec k (Ty_FVar X) T2))
        (t:=open_tm body arg).
      * intros w Hw Hwrel.
        apply (proj2 (IH2 k eta rho X a w Hlen H3
          HF2)).
        exact Hwrel.
      * apply Hfun.
        apply (proj1 (IH1 k eta rho X a arg Hlen H2 HF1)).
        exact Harg.
  - inversion Hlc. split; intro Hrel.
    + destruct Hrel as [Hv [body [Heq Hfun]]].
      refine (conj Hv (ex_intro (fun body => v = tm_tabs body /\
        forall (U:ty) (c:value_candidate), locally_closed_ty U ->
          expression_lifting (value_relation (c :: insert_candidate k a eta) rho T)
            (open_tm_ty body U)) body (conj Heq (fun U c HU => _)))).
      assert (Hlen' : length (c :: eta) = S k).
      { simpl. lia. }
      apply expression_lifting_map with
        (R:=value_relation (c :: eta) (relation_update rho X a)
             (open_ty_rec (S k) (Ty_FVar X) T))
        (S:=value_relation (c :: insert_candidate k a eta) rho T)
        (t:=open_tm_ty body U).
      * intros w Hw Hwrel.
        apply (proj1 (IH (S k) (c::eta) rho X a w Hlen' H1 Hfresh)).
        exact Hwrel.
      * exact (Hfun U c HU).
    + destruct Hrel as [Hv [body [Heq Hfun]]].
      refine (conj Hv (ex_intro (fun body => v = tm_tabs body /\
        forall (U:ty) (c:value_candidate), locally_closed_ty U ->
          expression_lifting (value_relation (c :: eta) (relation_update rho X a)
            (open_ty_rec (S k) (Ty_FVar X) T)) (open_tm_ty body U)) body
        (conj Heq (fun U c HU => _)))).
      assert (Hlen' : length (c :: eta) = S k).
      { simpl. lia. }
      apply expression_lifting_map with
        (R:=value_relation (c :: insert_candidate k a eta) rho T)
        (S:=value_relation (c :: eta) (relation_update rho X a)
             (open_ty_rec (S k) (Ty_FVar X) T))
        (t:=open_tm_ty body U).
      * intros w Hw Hwrel.
        apply (proj2 (IH (S k) (c::eta) rho X a w Hlen' H1 Hfresh)).
        exact Hwrel.
      * exact (Hfun U c HU).
Qed.

Lemma value_relation_open : forall k eta rho X a T v,
    length eta = k ->
    lc_ty_at (S k) T ->
    ~ In X (ty_vars T) ->
    value_relation eta (relation_update rho X a)
      (open_ty_rec k (Ty_FVar X) T) v ->
    value_relation (insert_candidate k a eta) rho T v.
Proof.
  intros. apply (proj1 (value_relation_open_iff k eta rho X a T v H H0 H1)).
  assumption.
Qed.

Lemma value_relation_open_rev : forall k eta rho X a T v,
    length eta = k ->
    lc_ty_at (S k) T ->
    ~ In X (ty_vars T) ->
    value_relation (insert_candidate k a eta) rho T v ->
    value_relation eta (relation_update rho X a)
      (open_ty_rec k (Ty_FVar X) T) v.
Proof.
  intros. apply (proj2 (value_relation_open_iff k eta rho X a T v H H0 H1)).
  assumption.
Qed.

(* The following old duplicate proof blocks are retained only as comments. *)
(*
Lemma value_relation_open_rev_dup2 : forall k eta rho X a T v,
    length eta = k ->
    lc_ty_at (S k) T ->
    ~ In X (ty_vars T) ->
    value_relation (insert_candidate k a eta) rho T v ->
    value_relation eta (relation_update rho X a)
      (open_ty_rec k (Ty_FVar X) T) v.
Proof.
  intros k eta rho X a T v Hlen Hlc Hfresh.
  revert k eta rho X a v Hlen Hlc Hfresh.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH];
    intros k eta rho X a v Hlen Hlc Hfresh Hrel; simpl in *.
  - inversion Hlc. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. rewrite <- E in Hrel. cbn [value_relation] in Hrel.
      rewrite (insert_candidate_nth_eq k eta a Hlen) in Hrel.
      cbn [value_relation]. unfold relation_update. rewrite Nat.eqb_refl. exact Hrel.
    + apply Nat.eqb_neq in E. assert (Hi : i < k) by lia.
      cbn [value_relation] in Hrel.
      rewrite (insert_candidate_nth_lt k eta a i Hlen Hi) in Hrel.
      exact Hrel.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst Y. exfalso. apply Hfresh. simpl. now left.
    + cbn [value_relation] in Hrel. unfold relation_update. rewrite E. exact Hrel.
  - inversion Hlc. destruct Hrel as [Hv [U [body [Heq Hfun]]]].
    split; [exact Hv |]. exists U, body. split; [exact Heq |]. intros arg Harg.
    apply expression_lifting_map with
      (R:=value_relation (insert_candidate k a eta) rho T2)
      (S:=value_relation eta (relation_update rho X a) (open_ty_rec k (Ty_FVar X) T2))
      (t:=open_tm body arg).
    + intros w Hw Hwrel.
      apply IH2 with (k:=k) (eta:=eta) (rho:=rho) (X:=X) (a:=a).
      * exact Hlen. * exact H3.
      * intro Hin. apply Hfresh. apply in_app_iff. now right.
      * exact Hwrel.
    + apply Hfun.
      apply IH1 with (k:=k) (eta:=eta) (rho:=rho) (X:=X) (a:=a).
      * exact Hlen. * exact H2.
      * intro Hin. apply Hfresh. apply in_app_iff. now left.
      * exact Harg.
  - inversion Hlc. destruct Hrel as [Hv [body [Heq Hfun]]].
    split; [exact Hv |]. exists body. split; [exact Heq |]. intros U c HU Hc.
    apply expression_lifting_map with
      (R:=value_relation (c :: insert_candidate k a eta) rho T)
      (S:=value_relation (c :: eta) (relation_update rho X a)
             (open_ty_rec (S k) (Ty_FVar X) T))
      (t:=open_tm_ty body U).
    + intros w Hw Hwrel.
      apply IH with (k:=S k) (eta:=c::eta) (rho:=rho) (X:=X) (a:=a).
      * simpl. lia. * exact H0. * exact Hfresh. * exact Hwrel.
    + apply Hfun.
Qed.

Lemma value_relation_open_rev_dup3 : forall k eta rho X a T v,
    length eta = k ->
    lc_ty_at (S k) T ->
    ~ In X (ty_vars T) ->
    value_relation (insert_candidate k a eta) rho T v ->
    value_relation eta (relation_update rho X a)
      (open_ty_rec k (Ty_FVar X) T) v.
Proof.
  intros k eta rho X a T v Hlen Hlc Hfresh.
  revert k eta rho X a v Hlen Hlc Hfresh.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH];
    intros k eta rho X a v Hlen Hlc Hfresh Hrel; simpl in *.
  - inversion Hlc. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. rewrite insert_candidate_nth_eq in Hrel by assumption.
      cbn [value_relation]. unfold relation_update. rewrite Nat.eqb_refl. exact Hrel.
    + apply Nat.eqb_neq in E. assert (Hi : i < k) by lia.
      rewrite insert_candidate_nth_lt in Hrel by assumption.
      exact Hrel.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst Y. exfalso. apply Hfresh. simpl. now left.
    + cbn [value_relation] in Hrel. unfold relation_update. rewrite E. exact Hrel.
  - inversion Hlc. destruct Hrel as [Hv [U [body [Heq Hfun]]]].
    split; [exact Hv |]. exists U, body. split; [exact Heq |]. intros arg Harg.
    apply expression_lifting_map with
      (R:=value_relation (insert_candidate k a eta) rho T2)
      (S:=value_relation eta (relation_update rho X a) (open_ty_rec k (Ty_FVar X) T2))
      (t:=open_tm body arg).
    + intros w Hw Hwrel.
      apply IH2 with (k:=k) (eta:=eta) (rho:=rho) (X:=X) (a:=a).
      * exact Hlen. * exact H3.
      * intro Hin. apply Hfresh. apply in_app_iff. now right.
      * exact Hwrel.
    + apply Hfun. apply IH1 with (k:=k) (eta:=eta) (rho:=rho) (X:=X) (a:=a).
      * exact Hlen. * exact H2.
      * intro Hin. apply Hfresh. apply in_app_iff. now left.
      * exact Harg.
  - inversion Hlc. destruct Hrel as [Hv [body [Heq Hfun]]].
    split; [exact Hv |]. exists body. split; [exact Heq |]. intros U c HU Hc.
    apply expression_lifting_map with
      (R:=value_relation (c :: insert_candidate k a eta) rho T)
      (S:=value_relation (c :: eta) (relation_update rho X a)
             (open_ty_rec (S k) (Ty_FVar X) T))
      (t:=open_tm_ty body U).
    + intros w Hw Hwrel.
      apply IH with (k:=S k) (eta:=c::eta) (rho:=rho) (X:=X) (a:=a).
      * simpl. lia. * exact H0. * exact Hfresh. * exact Hwrel.
    + apply Hfun.
Qed.

Lemma value_relation_open : forall k eta rho X a T v,
    length eta = k ->
    lc_ty_at (S k) T ->
    ~ In X (ty_vars T) ->
    value_relation eta (relation_update rho X a)
      (open_ty_rec k (Ty_FVar X) T) v ->
    value_relation (insert_candidate k a eta) rho T v.
Proof.
  intros k eta rho X a T v Hlen Hlc Hfresh.
  revert k eta rho X a v Hlen Hlc Hfresh.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH];
    intros k eta rho X a v Hlen Hlc Hfresh Hrel; simpl in *.
  - inversion Hlc.
    destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i.
      cbn [value_relation] in Hrel.
      assert (Hupd : relation_update rho X a X = Some a).
      { unfold relation_update. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hupd in Hrel. simpl in Hrel.
      rewrite (insert_candidate_nth_eq k eta a Hlen). exact Hrel.
    + apply Nat.eqb_neq in E.
      assert (Hi : i < k) by lia.
      unfold relation_update in Hrel. simpl in Hrel.
      rewrite (insert_candidate_nth_lt k eta a i Hlen Hi). exact Hrel.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst Y. exfalso. apply Hfresh. simpl. now left.
    + cbn [value_relation] in Hrel.
      assert (Hupd : relation_update rho X a Y = rho Y).
      { unfold relation_update. rewrite E. reflexivity. }
      rewrite Hupd in Hrel. exact Hrel.
  - inversion Hlc.
    destruct Hrel as [Hv [U [body [Heq Hfun]]]].
    split; [exact Hv |].
    + exists U, body. split; [exact Heq |].
      intros arg Harg.
      apply expression_lifting_map with
        (R:=value_relation eta (relation_update rho X a) (open_ty_rec k (Ty_FVar X) T2))
        (S:=value_relation (insert_candidate k a eta) rho T2)
        (t:=open_tm body arg).
      * intros w Hw Hwrel.
        apply IH2 with (k:=k) (eta:=eta) (rho:=rho) (X:=X) (a:=a).
        -- exact Hlen.
        -- exact H3.
        -- intro Hin. apply Hfresh. apply in_app_iff. now right.
        -- exact Hwrel.
      * apply Hfun.
        apply value_relation_open_rev with (k:=k) (eta:=eta) (rho:=rho) (X:=X) (a:=a).
        -- exact Hlen.
        -- exact H2.
        -- intro Hin. apply Hfresh. apply in_app_iff. now left.
        -- exact Harg.
  - inversion Hlc.
    destruct Hrel as [Hv [body [Heq Hfun]]].
    split; [exact Hv |].
    + exists body. split; [exact Heq |].
      intros U c HU Hc.
      apply expression_lifting_map with
        (R:=value_relation (c :: eta) (relation_update rho X a)
             (open_ty_rec (S k) (Ty_FVar X) T))
        (S:=value_relation (c :: insert_candidate k a eta) rho T)
        (t:=open_tm_ty body U).
      * intros w Hw Hwrel.
        apply IH with (k:=S k) (eta:=c::eta) (rho:=rho) (X:=X) (a:=a).
        -- simpl. lia.
        -- exact H0.
        -- exact Hfresh.
        -- exact Hwrel.
      * apply Hfun.
Qed.

Lemma value_relation_open_rev : forall k eta rho X a T v,
    length eta = k ->
    lc_ty_at (S k) T ->
    ~ In X (ty_vars T) ->
    value_relation (insert_candidate k a eta) rho T v ->
    value_relation eta (relation_update rho X a)
      (open_ty_rec k (Ty_FVar X) T) v.
Proof.
  intros k eta rho X a T v Hlen Hlc Hfresh.
  revert k eta rho X a v Hlen Hlc Hfresh.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH];
    intros k eta rho X a v Hlen Hlc Hfresh Hrel; simpl in *.
  - inversion Hlc. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. rewrite insert_candidate_nth_eq in Hrel by assumption.
      cbn [value_relation]. unfold relation_update. rewrite Nat.eqb_refl. exact Hrel.
    + apply Nat.eqb_neq in E. assert (Hi : i < k) by lia.
      rewrite insert_candidate_nth_lt in Hrel by assumption.
      exact Hrel.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst Y. exfalso. apply Hfresh. simpl. now left.
    + cbn [value_relation] in Hrel. unfold relation_update. rewrite E. exact Hrel.
  - inversion Hlc. destruct Hrel as [Hv [U [body [Heq Hfun]]]].
    split; [exact Hv |]. exists U, body. split; [exact Heq |]. intros arg Harg.
    apply expression_lifting_map with
      (R:=value_relation (insert_candidate k a eta) rho T2)
      (S:=value_relation eta (relation_update rho X a) (open_ty_rec k (Ty_FVar X) T2))
      (t:=open_tm body arg).
    + intros w Hw Hwrel.
      apply IH2 with (k:=k) (eta:=eta) (rho:=rho) (X:=X) (a:=a).
      * exact Hlen. * exact H3.
      * intro Hin. apply Hfresh. apply in_app_iff. now right.
      * exact Hwrel.
    + apply Hfun. apply IH1 with (k:=k) (eta:=eta) (rho:=rho) (X:=X) (a:=a).
      * exact Hlen. * exact H2.
      * intro Hin. apply Hfresh. apply in_app_iff. now left.
      * exact Harg.
  - inversion Hlc. destruct Hrel as [Hv [body [Heq Hfun]]].
    split; [exact Hv |]. exists body. split; [exact Heq |]. intros U c HU Hc.
    apply expression_lifting_map with
      (R:=value_relation (c :: insert_candidate k a eta) rho T)
      (S:=value_relation (c :: eta) (relation_update rho X a)
             (open_ty_rec (S k) (Ty_FVar X) T))
      (t:=open_tm_ty body U).
    + intros w Hw Hwrel.
      apply IH with (k:=S k) (eta:=c::eta) (rho:=rho) (X:=X) (a:=a).
      * simpl. lia. * exact H0. * exact Hfresh. * exact Hwrel.
    + apply Hfun.
Qed.
*)

Definition rho_ok (Delta : ty_context) (rho : relation_env) : Prop :=
  forall X, In X Delta -> exists a, rho X = Some a.

Lemma rho_ok_update : forall Delta rho X a,
    rho_ok Delta rho ->
    rho_ok (X :: Delta) (relation_update rho X a).
Proof.
  intros Delta rho X a Hok Y HY. simpl in HY. destruct HY as [->|HY].
  - exists a. unfold relation_update. now rewrite Nat.eqb_refl.
  - destruct (Hok Y HY) as [b Hb]. destruct (Nat.eqb X Y) eqn:E.
    + exists a. unfold relation_update. rewrite E. reflexivity.
    + exists b. unfold relation_update. rewrite E. exact Hb.
Qed.

Lemma multi_abs_value : forall T t v,
    multi (tm_abs T t) v -> value v -> v = tm_abs T t.
Proof.
  intros T t v H. inversion H; subst; auto.
  inversion H0.
Qed.

Lemma multi_tabs_value : forall t v,
    multi (tm_tabs t) v -> value v -> v = tm_tabs t.
Proof.
  intros t v H. inversion H; subst; auto.
  inversion H0.
Qed.

Lemma sn_abs : forall T t, locally_closed_tm (tm_abs T t) ->
    strongly_normalizing (tm_abs T t).
Proof. intros Hlc. constructor. intros u Hstep. inversion Hstep. Qed.

Lemma sn_tabs : forall t, locally_closed_tm (tm_tabs t) ->
    strongly_normalizing (tm_tabs t).
Proof. intros Hlc. constructor. intros u Hstep. inversion Hstep. Qed.

Lemma lc_ty_mono : forall K T, lc_ty_at K T ->
    forall M, K <= M -> lc_ty_at M T.
Proof.
  intros K T H. revert K H.
  induction T as [i|X|T1 IH1 T2 IH2|T IH]; intros K Hlc M Hkm.
  - inversion Hlc. constructor. lia.
  - constructor.
  - inversion Hlc. constructor; [apply IH1 with (K:=K) | apply IH2 with (K:=K)]; assumption.
  - inversion Hlc. constructor. apply IH with (K:=S K) (M:=S M); [assumption | lia].
Qed.

Lemma lc_ty_open : forall K U T,
    lc_ty_at (S K) T -> lc_ty_at K U ->
    lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K U T. revert K U.
  induction T as [i|X|T1 IH1 T2 IH2|T IH]; intros K U Hlc HUc; simpl.
  - destruct (Nat.eqb K i) eqn:E.
    + exact HUc.
    + inversion Hlc. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Hlc. constructor; [apply IH1 with (K:=K) (U:=U) | apply IH2 with (K:=K) (U:=U)]; assumption.
  - inversion Hlc. constructor. apply IH with (K:=S K) (U:=U).
    + assumption.
    + apply lc_ty_mono with (K:=K) (M:=S K).
      * exact HUc.
      * lia.
Qed.

Lemma has_type_type_lc : forall Delta Gamma t T,
    has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H. induction H as
    [Delta Gamma x T Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IHt Hwu].
  - apply (wf_ty_lc Delta T). assumption.
  - apply lc_ty_arrow.
    + apply (wf_ty_lc Delta T1). exact Hwf.
    + exact (IHbody (fresh L) (fresh_not_In L)).
  - inversion IH1. assumption.
  - constructor. specialize (Hbody (fresh L)).
    assert (Hfresh : ~ In (fresh L) L) by apply fresh_not_In.
    specialize (Hbody Hfresh). apply lc_ty_open_inv with (K:=0) (U:=Ty_FVar (fresh L)).
    exact (IHbody (fresh L) Hfresh).
  - inversion IHt. apply lc_ty_open.
    + assumption.
    + apply (wf_ty_lc Delta U). exact Hwu.
Qed.

Lemma open_ty_rec_lc_at : forall K U T,
    lc_ty_at K T -> open_ty_rec K U T = T.
Proof.
  intros K U T H. induction H; simpl.
  - destruct (Nat.eqb K i) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
  - reflexivity.
  - now rewrite IHlc_ty_at1, IHlc_ty_at2.
  - now rewrite IHlc_ty_at.
Qed.

Lemma open_tm_ty_rec_lc_at : forall K k U t,
    lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  intros K k U t H. induction H; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (open_ty_rec_lc_at K U T), IHlc_tm_at. reflexivity.
  - now rewrite IHlc_tm_at1, IHlc_tm_at2.
  - now rewrite IHlc_tm_at.
  - now rewrite IHlc_tm_at, open_ty_rec_lc_at.
Qed.

Lemma instantiate_open_ty_id : forall K gamma U t,
    term_substitution_closed gamma ->
    instantiate id_theta gamma (open_tm_ty_rec K U t) =
    open_tm_ty_rec K U (instantiate id_theta gamma t).
Proof.
  intros K gamma U t Hclosed. revert K U.
  induction t as [|x|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros K U; simpl.
  - rewrite (open_tm_ty_rec_lc_at 0 0 U0 (gamma x)); reflexivity.
  - reflexivity.
  - rewrite instantiate_ty_id, instantiate_ty_id, IH. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH, instantiate_ty_id. reflexivity.
Qed.

Lemma instantiate_open_ty_id_0 : forall gamma U t,
    instantiate id_theta gamma (open_tm_ty t U) =
    open_tm_ty (instantiate id_theta gamma t) U.
Proof. intros; unfold open_tm_ty; apply instantiate_open_ty_id. Qed.

Lemma lc_tm_open : forall K k u t,
    lc_tm_at K (S k) t -> lc_tm_at K k u ->
    lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k u t. revert K k u.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros K k u Ht Hu; simpl in *.
  - inversion Ht. destruct (Nat.eqb k i) eqn:E.
    + exact Hu.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Ht. constructor; [assumption | apply IH with (K:=K) (k:=S k) (u:=u); assumption].
  - inversion Ht. constructor; [apply IH1 with (K:=K) (k:=k) (u:=u) | apply IH2 with (K:=K) (k:=k) (u:=u)]; assumption.
  - inversion Ht. constructor. apply IH with (K:=K) (k:=k) (u:=u). assumption.
  - inversion Ht. constructor; [apply IH with (K:=K) (k:=k) (u:=u) | assumption].
Qed.

Lemma lc_tm_ty_open : forall K k U t,
    lc_tm_at (S K) k t -> lc_ty_at K U ->
    lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k U t. revert K k U.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros K k U Ht HU; simpl in *.
  - constructor; inversion Ht; assumption.
  - constructor.
  - inversion Ht. constructor.
    + apply lc_ty_open; assumption.
    + apply IH with (K:=K) (k:=k) (U:=U); assumption.
  - inversion Ht. constructor; [apply IH1 with (K:=K) (k:=k) (U:=U) | apply IH2 with (K:=K) (k:=k) (U:=U)]; assumption.
  - inversion Ht. constructor. apply IH with (K:=S K) (k:=k) (U:=U); assumption.
  - inversion Ht. constructor.
    + apply IH with (K:=K) (k:=k) (U:=U); assumption.
    + apply lc_ty_open; assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma step_lc : forall t u, locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hstep. inversion Hstep.
  - apply lc_tm_open with (K:=0) (k:=0); [|apply value_lc; assumption].
    inversion Hlc. assumption.
  - inversion Hlc. constructor; [assumption | apply IHlc_tm_at1; assumption].
  - inversion Hlc. constructor; [assumption | apply IHlc_tm_at2; assumption].
  - apply lc_tm_ty_open with (K:=0) (k:=0); [inversion Hlc; assumption | assumption].
  - inversion Hlc. constructor; [apply IHlc_tm_at; assumption | assumption].
Qed.

Lemma sn_step : forall t u, strongly_normalizing t -> t --> u ->
    strongly_normalizing u.
Proof. intros t u H. inversion H. eauto. Qed.

Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
Proof.
  intros x y z Hxy Hyz. induction Hxy; eauto using multi.
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof. intros v H. constructor. intros u Hu. inversion Hu. Qed.

Lemma value_multi : forall v w, value v -> multi v w -> w = v.
Proof.
  intros v w Hv H. induction H; auto.
  exfalso. inversion Hv; inversion H.
Qed.

Lemma expression_step : forall R t u,
    expression_lifting R t -> t --> u -> expression_lifting R u.
Proof.
  intros R t u [Hlc [Hsn Hend]] Hstep. split; [|split].
  - apply step_lc with (t:=t); assumption.
  - eapply sn_step; eauto.
  - intros v Hmulti Hv. apply Hend with (v:=v).
    + eapply multi_step; eauto.
    + exact Hv.
Qed.

Lemma app_sn_right : forall v a R,
    value v -> strongly_normalizing a ->
    (forall w, multi v w -> value w -> R w) ->
    strongly_normalizing (tm_app v a).
Proof.
  intros v a R Hv Ha Hend. revert v Hend.
  induction Ha as [a Hnext IH]; intros v Hend.
  constructor. intros u Hu. inversion Hu.
  - destruct (Hend v (multi_refl v) Hv) as [|].
  - apply IH with (v:=v).
    + intros w Hmulti Hw. apply Hend w. eapply multi_step; eauto. exact Hw.
    + assumption.
Qed.

Lemma app_sn : forall f a R,
    strongly_normalizing f -> strongly_normalizing a ->
    (forall w, multi f w -> value w -> R w) ->
    strongly_normalizing (tm_app f a).
Proof.
  intros f a R Hf Ha Hend. revert a Ha Hend.
  induction Hf as [f Hnext IH]; intros a Ha Hend.
  constructor. intros u Hu. inversion Hu.
  - apply IH with (a:=a).
    + apply sn_step with (t:=f); assumption.
    + intros w Hmulti Hw. apply Hend w. eapply multi_step; eauto. exact Hw.
  - apply app_sn_right with (v:=v1) (a:=a) (R:=R); try assumption.
    intros w Hmulti Hw. apply Hend w. exact Hmulti. exact Hw.
  - destruct (Hend (tm_abs T t) (multi_refl _) (v_abs T t H)) as [Hv [body [Heq Hbody]]].
    apply Hbody with (arg:=v2).
    exact Hv.
Qed.

Lemma app_expression : forall eta rho A B f a,
    expression_lifting (value_relation eta rho (Ty_Arrow A B)) f ->
    expression_lifting (value_relation eta rho A) a ->
    expression_lifting (value_relation eta rho B) (tm_app f a).
Proof.
  intros eta rho A B f a Ef Ea. split; [|split].
  - constructor; [exact (proj1 Ef) | exact (proj1 Ea)].
  - apply app_sn with
      (R:=value_relation eta rho (Ty_Arrow A B))
      (f:=f) (a:=a) (proj2 (proj2 Ef)) (proj2 (proj2 Ea)).
    exact (proj2 (proj2 Ef) (multi_refl f)).
  - intros w Hmulti Hw.
    revert f a Ef Ea.
    induction Hmulti as [x|x y z Hxy Hyz IH]; intros f a Ef Ea.
    + inversion Hw.
    + inversion Hxy.
      * apply IH with (f:=t1') (a:=t2).
        -- apply expression_step with (t:=t1); assumption.
        -- exact Ea.
      * apply IH with (f:=v1) (a:=t2').
        -- exact Ef.
        -- apply expression_step with (t:=t2); assumption.
      * destruct (proj2 (proj2 Ef) (multi_refl f)
                    (v_abs T t H)) as [Hv [body [Heq Hbody]]].
        apply Hbody. exact Hyz. exact Hw.
Qed.

Definition gamma_update (gamma : term_substitution) (x : atom) (s : tm) : term_substitution :=
  fun y => if Nat.eqb x y then s else gamma y.

Lemma gamma_update_closed : forall gamma x s,
    term_substitution_closed gamma -> locally_closed_tm s ->
    term_substitution_closed (gamma_update gamma x s).
Proof.
  intros gamma x s Hclosed Hs y. unfold gamma_update.
  destruct (Nat.eqb x y); assumption.
Qed.

Lemma related_update : forall rho Gamma x T gamma s,
    x <> x -> related_substitution rho Gamma gamma ->
    value_relation [] rho T s ->
    related_substitution rho ((x,T)::Gamma) (gamma_update gamma x s).
Proof.
  intros rho Gamma x T gamma s Hbad Hrel Hs y U Hlookup.
  exfalso. apply Hbad. reflexivity.
Qed.

Lemma related_update_fresh : forall rho Gamma x T gamma s,
    x <> x -> related_substitution rho Gamma gamma ->
    value_relation [] rho T s ->
    related_substitution rho ((x,T)::Gamma) (gamma_update gamma x s).
Proof.
  intros rho Gamma x T gamma s Hx Hrel Hs y U Hlookup.
  destruct (lookup_update_inv x y T Gamma U Hlookup) as [[-> HU]|[Hneq Htail]].
  - subst U. unfold gamma_update. rewrite Nat.eqb_refl. exact Hs.
  - unfold gamma_update. destruct (Nat.eqb x y) eqn:E.
    + exfalso. apply Hneq. now apply Nat.eqb_eq.
    + apply Hrel with (x:=y) (T:=U). exact Htail.
Qed.

Theorem fundamental : forall Delta Gamma t T rho gamma,
    has_type Delta Gamma t T ->
    rho_ok Delta rho ->
    term_substitution_closed gamma ->
    related_substitution rho Gamma gamma ->
    expression_relation [] rho T (instantiate id_theta gamma t).
Proof.
  intros Delta Gamma t T rho gamma Htyping. revert rho gamma.
  induction Htyping as
    [Delta Gamma x T Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IHt Hwu];
    intros rho gamma Hrho Hclosed Hrel.
  - unfold expression_relation expression_lifting.
    repeat split.
    + apply value_lc. apply (candidate_values (match rho x with Some a => a | None => {| candidate_relation := fun _ => False; candidate_values := fun v H => False_rect _ H |} end)).
      (* The lookup relation already supplies the needed candidate relation. *)
      destruct (Hrel x T Hlook) as Hxrel.
      destruct (rho x) eqn:Er; simpl in Hxrel.
      * apply value_lc. destruct a; simpl in Hxrel. apply candidate_values; exact Hxrel.
      * rewrite Er in Hxrel. contradiction.
    + destruct (Hrel x T Hlook) as Hxrel.
      destruct (rho x) eqn:Er; simpl in Hxrel.
      * apply value_sn. destruct a; simpl in Hxrel. apply candidate_values; exact Hxrel.
      * rewrite Er in Hxrel. contradiction.
    + intros v Hmulti Hv.
      destruct (Hrel x T Hlook) as Hxrel.
      destruct (rho x) eqn:Er; simpl in Hxrel.
      * destruct (value_multi _ _ (candidate_values a Hxrel) Hmulti) as ->.
        exact Hxrel.
      * rewrite Er in Hxrel. contradiction.
  - unfold expression_relation expression_lifting.
    repeat split.
    + apply instantiate_lc with (gamma:=gamma). exact Hclosed.
      apply has_type_lc. exact (T_Abs L Delta Gamma T1 t2 T2 Hwf Hbody).
    + apply sn_abs. apply instantiate_lc with (gamma:=gamma); assumption.
    + intros v Hmulti Hv. subst v using (multi_abs_value (instantiate_ty id_theta T1)
        (instantiate id_theta gamma t2) v Hmulti Hv).
      split; [exact Hv |]. split.
      * exists (instantiate_ty id_theta T1), (instantiate id_theta gamma t2). repeat split; auto.
      * intros arg Harg.
        set (x := fresh (L ++ tm_vars t2 ++ ctx_vars Gamma)).
        assert (HxL : ~ In x L).
        { unfold x. intro Hin. apply fresh_not_In. apply in_app_iff. now left. }
        assert (HxT : ~ In x (tm_vars t2)).
        { unfold x. intro Hin. apply fresh_not_In. apply in_app_iff. right. apply in_app_iff. now left. }
        assert (HxG : ~ In x (ctx_vars Gamma)).
        { unfold x. intro Hin. apply fresh_not_In. apply in_app_iff. right. apply in_app_iff. now right. }
        specialize (IHbody x HxL (rho:=rho) (gamma:=gamma_update gamma x arg)).
        specialize (IHbody Hrho (gamma_update_closed gamma x arg Hclosed (value_lc _ (proj2 Harg))) ).
        apply (expression_lifting_map _ _ _ (fun w _ Hw => Hw) IHbody).
        (* The two terms are definitionally the same after the fresh choice. *)
        rewrite instantiate_open_fresh with (theta:=id_theta) (gamma:=gamma) (x:=x) (s:=arg) (t:=t2); auto.
        exact related_update_fresh rho Gamma x T1 gamma arg (fun H => HxG H) Hrel Harg.
  - apply app_expression; [apply IH1 | apply IH2]; assumption.
  - unfold expression_relation expression_lifting.
    repeat split.
    + apply instantiate_lc with (gamma:=gamma). exact Hclosed.
      apply has_type_lc. exact (T_TAbs L Delta Gamma t T Hbody).
    + apply sn_tabs. apply instantiate_lc with (gamma:=gamma); assumption.
    + intros v Hmulti Hv. subst v using (multi_tabs_value (instantiate id_theta gamma t) v Hmulti Hv).
      split; [exact Hv |]. split; [exists (instantiate id_theta gamma t); repeat split; auto |].
      intros U a HU Ha.
      set (X := fresh (L ++ ty_vars T)).
      assert (HX : ~ In X L).
      { unfold X. intro Hin. apply fresh_not_In. apply in_app_iff. now left. }
      assert (HXty : ~ In X (ty_vars T)).
      { unfold X. intro Hin. apply fresh_not_In. apply in_app_iff. right. exact Hin. }
      specialize (IHbody X HX (rho:=relation_update rho X a) (gamma:=gamma)).
      specialize (IHbody (rho_ok_update Delta rho X a Hrho) Hclosed).
      apply (expression_lifting_map _ _ _ (fun w _ Hw => Hw) IHbody).
      rewrite instantiate_open_ty_id_0. exact Hrel.
      exact Hrel.
  - apply app_expression; [apply IHt | apply Hwu]; assumption.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationNoneMediumTask.
