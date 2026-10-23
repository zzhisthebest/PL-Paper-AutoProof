(** System F parametricity benchmark, Hard variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Wellfounded Wf_nat.
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

(* Semantic environments used by the binary logical relation.  Type
   variables are interpreted by two (possibly different) closed types and
   an arbitrary relation between their values. *)
Record type_interp : Type := mk_type_interp {
  ti_left : ty;
  ti_right : ty;
  ti_rel : tm -> tm -> Prop
}.
Definition type_env := atom -> type_interp.
Definition bound_env := list (tm -> tm -> Prop).

Fixpoint ty_inst (rho : type_env) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => ti_left (rho X)
  | Ty_Arrow A B => Ty_Arrow (ty_inst rho A) (ty_inst rho B)
  | Ty_All A => Ty_All (ty_inst rho A)
  end.
Fixpoint ty_inst_r (rho : type_env) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => ti_right (rho X)
  | Ty_Arrow A B => Ty_Arrow (ty_inst_r rho A) (ty_inst_r rho B)
  | Ty_All A => Ty_All (ty_inst_r rho A)
  end.
Fixpoint tm_ty_inst (rho : type_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs A b => tm_abs (ty_inst rho A) (tm_ty_inst rho b)
  | tm_app f a => tm_app (tm_ty_inst rho f) (tm_ty_inst rho a)
  | tm_tabs b => tm_tabs (tm_ty_inst rho b)
  | tm_tapp f A => tm_tapp (tm_ty_inst rho f) (ty_inst rho A)
  | tm_choice a b => tm_choice (tm_ty_inst rho a) (tm_ty_inst rho b)
  end.
Fixpoint tm_ty_inst_r (rho : type_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs A b => tm_abs (ty_inst_r rho A) (tm_ty_inst_r rho b)
  | tm_app f a => tm_app (tm_ty_inst_r rho f) (tm_ty_inst_r rho a)
  | tm_tabs b => tm_tabs (tm_ty_inst_r rho b)
  | tm_tapp f A => tm_tapp (tm_ty_inst_r rho f) (ty_inst_r rho A)
  | tm_choice a b => tm_choice (tm_ty_inst_r rho a) (tm_ty_inst_r rho b)
  end.
Fixpoint tm_inst (theta : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => theta x
  | tm_abs A b => tm_abs A (tm_inst theta b)
  | tm_app f a => tm_app (tm_inst theta f) (tm_inst theta a)
  | tm_tabs b => tm_tabs (tm_inst theta b)
  | tm_tapp f A => tm_tapp (tm_inst theta f) A
  | tm_choice a b => tm_choice (tm_inst theta a) (tm_inst theta b)
  end.

Definition rho_set (rho : type_env) (X : atom) (i : type_interp) : type_env :=
  fun Y => if Nat.eqb X Y then i else rho Y.
Definition theta_set (theta : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else theta y.
Definition type_env_ok (rho : type_env) : Prop :=
  forall X, locally_closed_ty (ti_left (rho X)) /\
            locally_closed_ty (ti_right (rho X)).

Fixpoint ty_fv (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fv A ++ ty_fv B
  | Ty_All A => ty_fv A
  end.
Fixpoint tm_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => tm_fv b
  | tm_app f a => tm_fv f ++ tm_fv a
  | tm_tabs b => tm_fv b
  | tm_tapp f _ => tm_fv f
  | tm_choice a b => tm_fv a ++ tm_fv b
  end.
Fixpoint tm_ty_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs A b => ty_fv A ++ tm_ty_fv b
  | tm_app f a => tm_ty_fv f ++ tm_ty_fv a
  | tm_tabs b => tm_ty_fv b
  | tm_tapp f A => tm_ty_fv f ++ ty_fv A
  | tm_choice a b => tm_ty_fv a ++ tm_ty_fv b
  end.

Lemma ty_inst_set_fresh : forall rho X i T,
  ~ In X (ty_fv T) -> ty_inst (rho_set rho X i) T = ty_inst rho T.
Proof.
  intros rho X i T; induction T; simpl; intros Hfresh.
  - reflexivity.
  - simpl in Hfresh. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst a. exfalso; apply Hfresh; simpl; auto.
    + unfold rho_set; rewrite E; reflexivity.
  - assert (H1 : ~ In X (ty_fv T1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In X (ty_fv T2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
Qed.


Fixpoint context_ty_fv (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: G => ty_fv T ++ context_ty_fv G
  end.


Lemma ty_inst_r_set_fresh : forall rho X i T,
  ~ In X (ty_fv T) -> ty_inst_r (rho_set rho X i) T = ty_inst_r rho T.
Proof.
  intros rho X i T; induction T; simpl; intros Hfresh.
  - reflexivity.
  - simpl in Hfresh. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst a. exfalso; apply Hfresh; simpl; auto.
    + unfold rho_set; rewrite E; reflexivity.
  - assert (H1 : ~ In X (ty_fv T1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In X (ty_fv T2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
Qed.

Lemma tm_ty_inst_set_fresh : forall rho X i t,
  ~ In X (tm_ty_fv t) ->
  tm_ty_inst (rho_set rho X i) t = tm_ty_inst rho t.
Proof.
  intros rho X i t; induction t; simpl; intros Hfresh; try reflexivity.
  - assert (Ha : ~ In X (ty_fv t)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hb : ~ In X (tm_ty_fv t0)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite ty_inst_set_fresh by exact Ha.
    rewrite IHt by exact Hb. reflexivity.
  - assert (Ha : ~ In X (tm_ty_fv t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hb : ~ In X (tm_ty_fv t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - assert (Ha : ~ In X (tm_ty_fv t)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hb : ~ In X (ty_fv t0)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite IHt, ty_inst_set_fresh; auto.
  - assert (Ha : ~ In X (tm_ty_fv t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hb : ~ In X (tm_ty_fv t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite IHt1, IHt2; auto.
Qed.

Lemma tm_ty_inst_r_set_fresh : forall rho X i t,
  ~ In X (tm_ty_fv t) ->
  tm_ty_inst_r (rho_set rho X i) t = tm_ty_inst_r rho t.
Proof.
  intros rho X i t; induction t; simpl; intros Hfresh; try reflexivity.
  - assert (Ha : ~ In X (ty_fv t)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hb : ~ In X (tm_ty_fv t0)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite ty_inst_r_set_fresh by exact Ha.
    rewrite IHt by exact Hb. reflexivity.
  - assert (Ha : ~ In X (tm_ty_fv t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hb : ~ In X (tm_ty_fv t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - assert (Ha : ~ In X (tm_ty_fv t)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hb : ~ In X (ty_fv t0)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite IHt, ty_inst_r_set_fresh; auto.
  - assert (Ha : ~ In X (tm_ty_fv t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hb : ~ In X (tm_ty_fv t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite IHt1, IHt2; auto.
Qed.

Lemma open_ty_rec_lc_noop : forall K k U T,
  K <= k -> lc_ty_at K T -> open_ty_rec k U T = T.
Proof.
  intros K k U T Hle Hlc; revert K k Hle Hlc.
  induction T; intros K k Hle Hlc; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - inversion Hlc; subst. f_equal.
    eapply IHT with (K := S K) (k := S k).
    + lia.
    + assumption.
Qed.

Lemma open_tm_ty_rec_lc_noop : forall K k j U t,
  K <= j -> lc_tm_at K k t -> open_tm_ty_rec j U t = t.
Proof.
  intros K k j U t Hle Hlc; revert K k j Hle Hlc.
  induction t; intros K k j Hle Hlc; simpl.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply open_ty_rec_lc_noop; eauto; lia.
    + eapply IHt with (K:=K) (k:=S k) (j:=j); [exact Hle|exact H4].
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - inversion Hlc; subst. f_equal. eapply IHt with (K:=S K) (k:=k) (j:=S j).
    + lia.
    + assumption.
  - inversion Hlc; subst. f_equal.
    + eapply IHt with (K:=K) (k:=k) (j:=j); eauto.
    + eapply open_ty_rec_lc_noop; eauto; lia.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma ty_inst_open_rec : forall rho k U T,
  type_env_ok rho ->
  ty_inst rho (open_ty_rec k U T) =
  open_ty_rec k (ty_inst rho U) (ty_inst rho T).
Proof.
  intros rho k U T Hok; revert k U Hok; induction T; intros k U Hok; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Hok a) as [Hlc _]. rewrite open_ty_rec_lc_noop with (K:=0); auto; lia.
  - rewrite (IHT1 k U Hok), (IHT2 k U Hok); reflexivity.
  - rewrite (IHT (S k) U Hok); reflexivity.
Qed.

Lemma ty_inst_r_open_rec : forall rho k U T,
  type_env_ok rho ->
  ty_inst_r rho (open_ty_rec k U T) =
  open_ty_rec k (ty_inst_r rho U) (ty_inst_r rho T).
Proof.
  intros rho k U T Hok; revert k U Hok; induction T; intros k U Hok; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Hok a) as [_ Hlc]. rewrite open_ty_rec_lc_noop with (K:=0); auto; lia.
  - rewrite (IHT1 k U Hok), (IHT2 k U Hok); reflexivity.
  - rewrite (IHT (S k) U Hok); reflexivity.
Qed.

Lemma tm_ty_inst_open_rec : forall rho k U t,
  type_env_ok rho ->
  tm_ty_inst rho (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_inst rho U) (tm_ty_inst rho t).
Proof.
  intros rho k U t Hok; revert k U Hok; induction t; intros k U Hok; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (ty_inst_open_rec rho k U t Hok), (IHt k U Hok); reflexivity.
  - rewrite (IHt1 k U Hok), (IHt2 k U Hok); reflexivity.
  - rewrite (IHt (S k) U Hok); reflexivity.
  - rewrite (IHt k U Hok), (ty_inst_open_rec rho k U t0 Hok); reflexivity.
  - rewrite (IHt1 k U Hok), (IHt2 k U Hok); reflexivity.
Qed.

Lemma tm_ty_inst_r_open_rec : forall rho k U t,
  type_env_ok rho ->
  tm_ty_inst_r rho (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_inst_r rho U) (tm_ty_inst_r rho t).
Proof.
  intros rho k U t Hok; revert k U Hok; induction t; intros k U Hok; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (ty_inst_r_open_rec rho k U t Hok), (IHt k U Hok); reflexivity.
  - rewrite (IHt1 k U Hok), (IHt2 k U Hok); reflexivity.
  - rewrite (IHt (S k) U Hok); reflexivity.
  - rewrite (IHt k U Hok), (ty_inst_r_open_rec rho k U t0 Hok); reflexivity.
  - rewrite (IHt1 k U Hok), (IHt2 k U Hok); reflexivity.
Qed.

Lemma tm_ty_inst_tm_open_rec : forall rho k x t,
  tm_ty_inst rho (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (tm_fvar x) (tm_ty_inst rho t).
Proof.
  intros rho k x t; revert k x; induction t; intros k x; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma tm_ty_inst_r_tm_open_rec : forall rho k x t,
  tm_ty_inst_r rho (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (tm_fvar x) (tm_ty_inst_r rho t).
Proof.
  intros rho k x t; revert k x; induction t; intros k x; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma open_tm_rec_lc : forall K k t u,
  lc_tm_at K 0 u -> open_tm_rec k u t = t -> True.
Proof. auto. Qed.

Definition runs (R : tm -> tm -> Prop) (s t : tm) : Prop :=
  exists v w, multi s v /\ multi t w /\ value v /\ value w /\
    tm_fv v = [] /\ tm_fv w = [] /\ R v w.

Fixpoint vrel (rho : type_env) (bs : bound_env) (T : ty)
    {struct T} : tm -> tm -> Prop :=
  match T with
  | Ty_BVar i => fun v w =>
      match nth_error bs i with Some R => R v w | None => False end
  | Ty_FVar X => ti_rel (rho X)
  | Ty_Arrow A B => fun v w =>
      exists a b, v = tm_abs a b /\ value v /\ value w /\
        (exists c d, w = tm_abs c d) /\
        forall x y, runs (vrel rho bs A) x y ->
          runs (vrel rho bs B) (tm_app v x) (tm_app w y)
  | Ty_All A => fun v w =>
      exists b c, v = tm_tabs b /\ w = tm_tabs c /\ value v /\ value w /\
        forall (S T : ty), locally_closed_ty S -> locally_closed_ty T ->
          forall (R : tm -> tm -> Prop),
          runs (vrel rho (R :: bs) A)
            (open_tm_ty b S) (open_tm_ty c T)
  end.

Lemma runs_values : forall R v w,
  value v -> value w -> tm_fv v = [] -> tm_fv w = [] -> R v w -> runs R v w.
Proof. intros; exists v, w; repeat split; try constructor; assumption. Qed.

Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
Proof. intros x y z H; induction H; eauto using multi. Qed.

Lemma multi_app_left : forall f f' a,
  multi f f' -> locally_closed_tm a ->
  multi (tm_app f a) (tm_app f' a).
Proof.
  intros f f' a H; induction H; intros Ha.
  - constructor.
  - eapply multi_step; [eapply ST_App1; eauto|]. apply IHmulti; exact Ha.
Qed.

Lemma multi_app_right : forall v a a',
  value v -> multi a a' ->
  multi (tm_app v a) (tm_app v a').
Proof.
  intros v a a' Hv H; induction H.
  - constructor.
  - eapply multi_step; [eapply ST_App2; eauto|]. exact IHmulti.
Qed.

Lemma multi_tapp : forall f f' U,
  multi f f' -> locally_closed_ty U ->
  multi (tm_tapp f U) (tm_tapp f' U).
Proof.
  intros f f' U H; induction H; intros HU.
  - constructor.
  - eapply multi_step; [eapply ST_TApp; eauto|]. apply IHmulti; exact HU.
Qed.

Lemma multi_tapp_tabs : forall b U,
  locally_closed_tm (tm_tabs b) -> locally_closed_ty U ->
  multi (tm_tapp (tm_tabs b) U) (open_tm_ty b U).
Proof. intros; eapply multi_step; [eapply ST_TAppTabs; eauto|constructor]. Qed.

Lemma multi_app_abs : forall A b v,
  locally_closed_tm (tm_abs A b) -> value v ->
  multi (tm_app (tm_abs A b) v) (open_tm b v).
Proof. intros; eapply multi_step; [eapply ST_AppAbs; eauto|constructor]. Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma singleton_vrel : forall (v x y : tm),
  (x = v /\ y = v) -> (fun (a b : tm) => a = v /\ b = v) x y.
Proof. auto. Qed.

Lemma vrel_identity_value : forall rho t1 t2 U v,
  locally_closed_ty U -> value v -> tm_fv v = [] ->
  vrel rho [] (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) t1 t2 ->
  (exists w, multi (tm_app (tm_tapp t1 U) v) w /\ w = v).
Proof.
  intros rho t1 t2 U v HU Hv Hclosed Hrel.
  unfold vrel in Hrel; simpl in Hrel.
  destruct Hrel as [b [c [Ht1 [Ht2 [Hvt [Hvt' Hall]]]]]].
  subst t1 t2.
  specialize (Hall U U HU HU (fun x y => x = v /\ y = v)).
  simpl in Hall.
  destruct Hall as [f [g [Hbody1 [Hbody2 [Hfv [Hgv [Hcf [Hcg Hvrrel]]]]]]]].
  destruct Hvrrel as [A [b1 Hrest]].
  destruct Hrest as [Hf [Hfval [Hgval [Hex Hfn]]]].
  destruct Hex as [B [b2 Hg]].
  subst f g.
  assert (Harg : runs (fun x y => x = v /\ y = v) v v).
  { apply runs_values; auto using singleton_vrel. }
  specialize (Hfn v v Harg).
  destruct Hfn as [w1 [w2 [Hrun1 [Hrun2 [Hw1 [Hw2 [Hcw1 [Hcw2 Hout]]]]]]]].
  destruct Hout as [-> ->].
  exists v; split; [|reflexivity].
  eapply multi_trans.
  - apply multi_app_left.
    + eapply multi_tapp_tabs; [apply value_lc; exact Hvt|exact HU].
    + apply value_lc; exact Hv.
  - eapply multi_trans.
    + apply multi_app_left.
      * exact Hbody1.
      * apply value_lc; exact Hv.
    + exact Hrun1.
Qed.

Definition term_env_ok (rho : type_env) (Gamma : context)
    (th1 th2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    locally_closed_tm (th1 x) /\ locally_closed_tm (th2 x) /\
    runs (vrel rho [] T) (th1 x) (th2 x).

Lemma lookup_update_same : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros; simpl; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma lookup_update_neq : forall Gamma x y T,
  x <> y -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros; simpl. destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; congruence|reflexivity].
Qed.

Lemma term_env_ok_set : forall rho Gamma th1 th2 x T a b,
  term_env_ok rho Gamma th1 th2 ->
  locally_closed_tm a -> locally_closed_tm b ->
  runs (vrel rho [] T) a b ->
  term_env_ok rho (update Gamma x T)
    (theta_set th1 x a) (theta_set th2 x b).
Proof.
  intros rho Gamma th1 th2 x T a b Hok Hla Hlb Hab y S Hlookup.
  unfold theta_set. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst y. rewrite lookup_update_same in Hlookup.
    inversion Hlookup; subst; repeat split; assumption.
  - assert (x <> y) by (intro Heq; subst; rewrite Nat.eqb_refl in E; discriminate).
    rewrite lookup_update_neq in Hlookup by congruence.
    specialize (Hok y S Hlookup). exact Hok.
Qed.

Fixpoint ty_size (T : ty) : nat :=
  match T with
  | Ty_BVar _ | Ty_FVar _ => 1
  | Ty_Arrow A B => S (ty_size A + ty_size B)
  | Ty_All A => S (ty_size A)
  end.

Lemma ty_size_open_fvar_rec : forall T k X,
  ty_size (open_ty_rec k (Ty_FVar X) T) = ty_size T.
Proof.
  induction T; intros k X; simpl.
  - destruct (k =? n); reflexivity.
  - reflexivity.
  - rewrite IHT1, IHT2; reflexivity.
  - rewrite IHT; reflexivity.
Qed.
Lemma ty_size_open : forall T X, ty_size (open_ty T (Ty_FVar X)) = ty_size T.
Proof. intros; apply ty_size_open_fvar_rec. Qed.

Lemma lc_ty_open_inv : forall k T X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  intros k T; revert k. induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion H; subst. constructor; lia.
  - inversion H; constructor.
  - inversion H; subst. constructor; [eapply IHT1|eapply IHT2]; eassumption.
  - inversion H; subst. constructor. eapply IHT. exact H2.
Qed.

Lemma in_list_le_max : forall (L : list nat) x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; simpl; intros x H; [contradiction|].
  destruct H as [->|H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [eapply IH; eassumption|apply Nat.le_max_r].
Qed.

Lemma fresh_atom' : forall L : list atom, exists X, ~ In X L.
Proof.
  intro L. exists (S (fold_right Nat.max 0 L)).
  intro Hin. pose proof (in_list_le_max L _ Hin). lia.
Qed.

Lemma wf_ty_lc : forall T Delta, wf_ty Delta T -> locally_closed_ty T.
Proof.
  apply (well_founded_induction_type (well_founded_ltof ty ty_size)
    (fun T => forall Delta, wf_ty Delta T -> locally_closed_ty T)).
  intros T IH Delta Hwf.
  inversion Hwf; subst; simpl.
  - constructor.
  - constructor.
    + exact (IH T1 ltac:(unfold ltof; simpl; lia) Delta H).
    + exact (IH T2 ltac:(unfold ltof; simpl; lia) Delta H0).
  - destruct (fresh_atom' L) as [X HX].
    specialize (H X HX).
    assert (Hlt : ty_size (open_ty T0 (Ty_FVar X)) < ty_size (Ty_All T0))
      by (rewrite ty_size_open; simpl; lia).
    specialize (IH (open_ty T0 (Ty_FVar X)) Hlt (X :: Delta) H).
    unfold locally_closed_ty in IH.
    apply lc_ty_open_inv with (k := 0) (X := X) in IH.
    unfold locally_closed_ty. constructor. exact IH.
Qed.

Lemma lc_ty_mono : forall K K' T,
  K <= K' -> lc_ty_at K T -> lc_ty_at K' T.
Proof.
  intros K K' T Hle H; revert K' Hle.
  induction H; intros K' Hle.
  - constructor; lia.
  - constructor.
  - apply lc_ty_arrow; [eapply IHlc_ty_at1|eapply IHlc_ty_at2]; eauto.
  - apply lc_ty_all. eapply IHlc_ty_at; lia.
Qed.

Lemma lc_tm_mono : forall K K' k k' t,
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  intros K K' k k' t HK Hk H; revert K' k' HK Hk.
  induction H; intros K' k' HK Hk.
  - constructor; lia.
  - constructor.
  - constructor.
    + eapply lc_ty_mono; eauto.
    + eapply IHlc_tm_at; eauto; lia.
  - constructor; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto.
  - constructor. eapply IHlc_tm_at; eauto; lia.
  - constructor; [eapply IHlc_tm_at|]; eauto.
    eapply lc_ty_mono; eauto.
  - constructor; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto.
Qed.

Lemma ty_inst_lc : forall rho K T,
  type_env_ok rho -> lc_ty_at K T ->
  lc_ty_at K (ty_inst rho T) /\ lc_ty_at K (ty_inst_r rho T).
Proof.
  intros rho K T Hok H; revert rho Hok.
  induction H; intros rho Hok; simpl.
  - split; constructor; assumption.
  - destruct (Hok X) as [HL HR]. split; apply lc_ty_mono with (K:=0); try lia; assumption.
  - destruct (IHlc_ty_at1 rho Hok) as [H1 H1']; destruct (IHlc_ty_at2 rho Hok) as [H2 H2'];
      split; apply lc_ty_arrow; assumption.
  - destruct (IHlc_ty_at rho Hok) as [HL HR]. split; apply lc_ty_all; assumption.
Qed.

Lemma tm_ty_inst_lc : forall rho K k t,
  type_env_ok rho -> lc_tm_at K k t ->
  lc_tm_at K k (tm_ty_inst rho t) /\ lc_tm_at K k (tm_ty_inst_r rho t).
Proof.
  intros rho K k t Hok H; revert rho Hok.
  induction H; intros rho Hok; simpl.
  - split; constructor; assumption.
  - split; constructor.
  - destruct (ty_inst_lc rho K T Hok H) as [HL HR].
    destruct (IHlc_tm_at rho Hok) as [H1 H2]. split; constructor; assumption.
  - destruct (IHlc_tm_at1 rho Hok) as [H1 H1']; destruct (IHlc_tm_at2 rho Hok) as [H2 H2']; split; constructor; assumption.
  - destruct (IHlc_tm_at rho Hok) as [H1 H2]; split; constructor; assumption.
  - destruct (IHlc_tm_at rho Hok) as [H1 H2].
    destruct (ty_inst_lc rho K T Hok H0) as [HT HT']; split; constructor; assumption.
  - destruct (IHlc_tm_at1 rho Hok) as [H1 H1']; destruct (IHlc_tm_at2 rho Hok) as [H2 H2']; split; constructor; assumption.
Qed.

Lemma tm_inst_lc : forall theta K k t,
  (forall x, locally_closed_tm (theta x)) ->
  lc_tm_at K k t -> lc_tm_at K k (tm_inst theta t).
Proof.
  intros theta K k t Hok H; revert theta Hok.
  induction H; intros theta Hok; simpl.
  - constructor; assumption.
  - apply lc_tm_mono with (K:=0) (k:=0); try lia. apply Hok.
  - constructor.
    + assumption.
    + eapply IHlc_tm_at; eauto.
  - constructor; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto.
  - constructor. eapply IHlc_tm_at; eauto.
  - constructor; [eapply IHlc_tm_at|]; eauto.
  - constructor; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto.
Qed.

Lemma lc_ty_open_preserve : forall K k U T,
  k < K -> lc_ty_at K U -> lc_ty_at K T ->
  lc_ty_at K (open_ty_rec k U T).
Proof.
  intros K k U T Hgap HU HT; revert K k Hgap HU HT.
  induction T; intros K k Hgap HU HT; simpl in *.
  - inversion HT; subst. destruct (Nat.eqb k n) eqn:E.
    + exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E. lia.
  - inversion HT; constructor.
  - inversion HT; subst. constructor.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - inversion HT; subst. constructor.
    eapply IHT with (K:=S K) (k:=S k).
    + lia.
    + apply lc_ty_mono with (K:=K); [lia|exact HU].
    + eassumption.
Qed.

Lemma lc_tm_ty_open_preserve : forall K j k U t,
  j < K -> lc_ty_at K U -> lc_tm_at K k t ->
  lc_tm_at K k (open_tm_ty_rec j U t).
Proof.
  intros K j k U t Hgap HU H; revert K j k U Hgap HU H.
  induction t; intros K j k U Hgap HU H; simpl in *.
  - inversion H; constructor; assumption.
  - inversion H; constructor.
  - inversion H; subst. constructor.
    + eapply lc_ty_open_preserve; eauto.
    + eapply IHt with (j:=j) (k:=S k); eauto.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eauto.
  - inversion H; subst. constructor.
    eapply IHt with (K:=S K) (j:=S j) (k:=k).
    + lia.
    + apply lc_ty_mono with (K:=K); [lia|exact HU].
    + eassumption.
  - inversion H; subst. constructor.
    + eapply IHt; eauto.
    + eapply lc_ty_open_preserve; eauto.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma lc_tm_open_preserve : forall K k t u,
  lc_tm_at K k u -> lc_tm_at K (S k) t ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t u Hu Ht; revert K k u Hu Ht.
  induction t; intros K k u Hu Ht; simpl in *.
  - inversion Ht; subst. destruct (Nat.eqb k n) eqn:E.
    + exact Hu.
    + apply lc_tm_bvar. apply Nat.eqb_neq in E. lia.
  - inversion Ht; constructor.
  - inversion Ht; subst. constructor; [assumption|].
    eapply IHt with (K:=K) (k:=S k) (u:=u); eauto.
    apply lc_tm_mono with (K:=K) (k:=k); [lia|lia|exact Hu].
  - inversion Ht; subst. constructor; [eapply IHt1|eapply IHt2]; eauto.
  - inversion Ht; subst. constructor.
    eapply IHt with (K:=S K) (k:=k) (u:=u); eauto.
    apply lc_tm_mono with (K:=K) (k:=k); [lia|lia|exact Hu].
  - inversion Ht; subst. constructor; [eapply IHt|assumption]; eauto.
  - inversion Ht; subst. constructor; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma type_env_ok_set : forall rho X i,
  type_env_ok rho -> locally_closed_ty (ti_left i) -> locally_closed_ty (ti_right i) ->
  type_env_ok (rho_set rho X i).
Proof.
  intros rho X i Hok HL HR Y. unfold rho_set.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma runs_ext : forall R S t u,
  (forall v w, R v w <-> S v w) -> (runs R t u <-> runs S t u).
Proof.
  intros R S t u Heq; split; intros [v [w [H1 [H2 [Hv [Hw [Hcv [Hcw HR]]]]]]]];
    exists v, w; repeat split; try assumption; apply Heq; assumption.
Qed.

Definition rel_env_agree (k : nat) (bs1 bs2 : bound_env) : Prop :=
  forall i, i < k -> nth_error bs1 i = nth_error bs2 i.

Lemma vrel_lc_env_irrel : forall rho bs1 bs2 k T,
  rel_env_agree k bs1 bs2 -> lc_ty_at k T ->
  forall v w, vrel rho bs1 T v w <-> vrel rho bs2 T v w.
Proof.
  intros rho bs1 bs2 k T Hagree Hlc; revert rho bs1 bs2 Hagree.
  induction Hlc as [k i Hi|k X|k T1 T2 H1 H2|k T1 H1 IH];
    intros rho bs1 bs2 Hagree v w; simpl.
  - rewrite Hagree by assumption. reflexivity.
  - reflexivity.
  - split; intros [A [b [Hv [Hvv [Hww [Hex Hfun]]]]]]; exists A, b;
      repeat split; try assumption; intros x y Hrun.
    + apply (proj2 (@runs_ext (vrel rho bs1 T1) (vrel rho bs2 T1) x y
        (fun a b => H2 rho bs1 bs2 Hagree a b))) in Hrun.
      specialize (Hfun x y Hrun).
      apply (proj1 (@runs_ext (vrel rho bs1 T2) (vrel rho bs2 T2) _ _
        (fun a b => IHHlc1 rho bs1 bs2 Hagree a b))). exact Hfun.
    + apply (proj1 (@runs_ext (vrel rho bs1 T1) (vrel rho bs2 T1) x y
        (fun a b => H2 rho bs1 bs2 Hagree a b))) in Hrun.
      specialize (Hfun x y Hrun).
      apply (proj2 (@runs_ext (vrel rho bs1 T2) (vrel rho bs2 T2) _ _
        (fun a b => IHHlc1 rho bs1 bs2 Hagree a b))). exact Hfun.
  - split; intros [b [c [Hv [Hw [Hvb [Hwc Hall]]]]]]; exists b, c;
      repeat split; try assumption; intros ST1 ST2 HS HT Q.
    + assert (Hagree' : rel_env_agree (Datatypes.S k) (Q :: bs1) (Q :: bs2)).
      { intros i Hi. destruct i; simpl; [reflexivity|]. apply Hagree. lia. }
      apply (proj1 (@runs_ext (vrel rho (Q :: bs1) T1) (vrel rho (Q :: bs2) T1) _ _
        (fun a b => IH rho (Q :: bs1) (Q :: bs2) Hagree' a b))).
      apply Hall; assumption.
    + assert (Hagree' : rel_env_agree (Datatypes.S k) (Q :: bs1) (Q :: bs2)).
      { intros i Hi. destruct i; simpl; [reflexivity|]. apply Hagree. lia. }
      apply (proj2 (@runs_ext (vrel rho (Q :: bs1) T1) (vrel rho (Q :: bs2) T1) _ _
        (fun a b => IH rho (Q :: bs1) (Q :: bs2) Hagree' a b))).
      apply Hall; assumption.
Qed.

Lemma vrel_open_stable : forall rho bs U R,
  locally_closed_ty U ->
  (forall pre v w, R v w <-> vrel rho (pre ++ bs) U v w) ->
  bs = [] -> forall pre T,
  forall v w,
    vrel rho (pre ++ R :: bs) T v w <->
    vrel rho (pre ++ bs) (open_ty_rec (length pre) U T) v w.
Proof.
  intros rho bs U R HU HR Hbs. subst bs.
  intros pre T; revert pre.
  induction T as [i|X|A IHA B IHB|A IHA]; intros pre v w; simpl.
  - destruct (Nat.lt_trichotomy i (length pre)) as [Hlt|[Heq|Hgt]].
    + assert (E : (length pre =? i) = false) by (apply Nat.eqb_neq; lia).
      rewrite E. unfold vrel; simpl.
      rewrite nth_error_app1 by lia. rewrite nth_error_app1 by lia. reflexivity.
    + subst i. rewrite Nat.eqb_refl. unfold vrel; simpl.
      rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. simpl. apply HR.
    + assert (E : (length pre =? i) = false) by (apply Nat.eqb_neq; lia).
      rewrite E. unfold vrel; simpl.
      rewrite nth_error_app2 by lia. rewrite nth_error_app2 by lia.
      replace (i - length pre) with (S (i - S (length pre))) by lia.
      simpl. rewrite nth_error_nil. reflexivity.
  - reflexivity.
  - pose proof (IHA pre) as HA.
    pose proof (IHB pre) as HB. split.
    + intros [C [b [Hv [Hvv [Hww [Hex Hfun]]]]]]. exists C, b. repeat split; try assumption.
      intros x y Hrun.
      apply (proj1 (@runs_ext (vrel rho (pre ++ R :: []) B)
        (vrel rho (pre ++ []) (open_ty_rec (length pre) U B)) _ _ HB)).
      apply Hfun. apply (proj2 (@runs_ext
        (vrel rho (pre ++ R :: []) A)
        (vrel rho (pre ++ []) (open_ty_rec (length pre) U A)) x y HA)). exact Hrun.
    + intros [C [b [Hv [Hvv [Hww [Hex Hfun]]]]]]. exists C, b. repeat split; try assumption.
      intros x y Hrun.
      apply (proj2 (@runs_ext (vrel rho (pre ++ R :: []) B)
        (vrel rho (pre ++ []) (open_ty_rec (length pre) U B)) _ _ HB)).
      apply Hfun. apply (proj1 (@runs_ext
        (vrel rho (pre ++ R :: []) A)
        (vrel rho (pre ++ []) (open_ty_rec (length pre) U A)) x y HA)). exact Hrun.
  - split.
    + intros [b [c [Hv [Hw [Hvb [Hwc Hall]]]]]]. exists b, c. repeat split; try assumption.
      intros S T HS HT Q. pose proof (IHA (Q :: pre)) as HA.
      apply (proj1 (@runs_ext
        (vrel rho (Q :: pre ++ R :: []) A)
        (vrel rho (Q :: pre ++ []) (open_ty_rec (Datatypes.S (length pre)) U A)) _ _
        HA)). apply Hall; assumption.
    + intros [b [c [Hv [Hw [Hvb [Hwc Hall]]]]]]. exists b, c. repeat split; try assumption.
      intros S T HS HT Q. pose proof (IHA (Q :: pre)) as HA.
      apply (proj2 (@runs_ext
        (vrel rho (Q :: pre ++ R :: []) A)
        (vrel rho (Q :: pre ++ []) (open_ty_rec (Datatypes.S (length pre)) U A)) _ _
        HA)). apply Hall; assumption.
Qed.

Lemma vrel_set_fresh : forall rho X i T bs,
  ~ In X (ty_fv T) ->
  forall v w, vrel (rho_set rho X i) bs T v w <-> vrel rho bs T v w.
Proof.
  intros rho X i T; induction T as [n|Y|A IHA B IHB|A IHA]; intros bs Hfresh v w; simpl.
  - reflexivity.
  - simpl in Hfresh. destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E; subst Y. exfalso; apply Hfresh; simpl; auto.
    + unfold rho_set. rewrite E. tauto.
  - assert (H1 : ~ In X (ty_fv A)) by (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (H2 : ~ In X (ty_fv B)) by (intro H; apply Hfresh; apply in_or_app; right; exact H).
    simpl. split.
    + intros [C [b [Hv [Hvv [Hww [Hex Hfun]]]]]]. exists C, b. repeat split; try assumption.
      intros x y Hrun.
      apply (proj2 (@runs_ext (vrel (rho_set rho X i) bs A) (vrel rho bs A) x y (fun z w => IHA bs H1 z w))) in Hrun.
      specialize (Hfun x y Hrun).
      apply (proj1 (@runs_ext (vrel (rho_set rho X i) bs B) (vrel rho bs B) _ _ (fun z w => IHB bs H2 z w))). exact Hfun.
    + intros [C [b [Hv [Hvv [Hww [Hex Hfun]]]]]]. exists C, b. repeat split; try assumption.
      intros x y Hrun.
      apply (proj1 (@runs_ext (vrel (rho_set rho X i) bs A) (vrel rho bs A) x y (fun z w => IHA bs H1 z w))) in Hrun.
      specialize (Hfun x y Hrun).
      apply (proj2 (@runs_ext (vrel (rho_set rho X i) bs B) (vrel rho bs B) _ _ (fun z w => IHB bs H2 z w))). exact Hfun.
  - simpl. split.
    + intros [b [c [Hv [Hw [Hvb [Hwc Hall]]]]]]. exists b, c. repeat split; try assumption.
      intros S T HS HT R. apply (proj1 (@runs_ext (vrel (rho_set rho X i) (R :: bs) A) (vrel rho (R :: bs) A) _ _ (fun x y => IHA (R :: bs) Hfresh x y))).
      apply Hall; assumption.
    + intros [b [c [Hv [Hw [Hvb [Hwc Hall]]]]]]. exists b, c. repeat split; try assumption.
      intros S T HS HT R. apply (proj2 (@runs_ext (vrel (rho_set rho X i) (R :: bs) A) (vrel rho (R :: bs) A) _ _ (fun x y => IHA (R :: bs) Hfresh x y))).
      apply Hall; assumption.
Qed.

Lemma lookup_context_type_fv : forall x Gamma T,
  lookup_context x Gamma = Some T -> incl (ty_fv T) (context_ty_fv Gamma).
Proof.
  intros x Gamma; induction Gamma as [|[y A] G IH]; simpl; intros T H; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion H; subst. intros Z Hin. apply in_or_app; left; exact Hin.
  - intros Z Hin. apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma term_env_ok_rho_set_fresh : forall rho Gamma th1 th2 X i,
  term_env_ok rho Gamma th1 th2 ->
  ~ In X (context_ty_fv Gamma) ->
  term_env_ok (rho_set rho X i) Gamma th1 th2.
Proof.
  intros rho Gamma th1 th2 X i Hok Hfresh y T Hlookup.
  destruct (Hok y T Hlookup) as [Hlc1 [Hlc2 Hrun]].
  repeat split; try assumption.
  apply (proj1 (@runs_ext (vrel rho [] T)
    (vrel (rho_set rho X i) [] T) (th1 y) (th2 y)
    (fun a b => iff_sym (vrel_set_fresh rho X i T []
      (fun Hin => Hfresh (lookup_context_type_fv y Gamma T Hlookup X Hin)) a b)))).
  exact Hrun.
Qed.

Lemma tm_ty_inst_set_open : forall rho X i t,
  type_env_ok rho ->
  locally_closed_ty (ti_left i) -> locally_closed_ty (ti_right i) ->
  ~ In X (tm_ty_fv t) ->
  tm_ty_inst (rho_set rho X i) (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (tm_ty_inst rho t) (ti_left i).
Proof.
  intros rho X i t Hok Hleft Hright Hfresh.
  unfold open_tm_ty.
  rewrite (tm_ty_inst_open_rec (rho_set rho X i) 0 (Ty_FVar X) t
    (type_env_ok_set rho X i Hok Hleft Hright)).
  simpl. replace (ti_left (rho_set rho X i X)) with (ti_left i).
  2: { unfold rho_set. rewrite Nat.eqb_refl; reflexivity. }
  rewrite (tm_ty_inst_set_fresh rho X i t Hfresh).
  reflexivity.
Qed.

Lemma tm_ty_inst_r_set_open : forall rho X i t,
  type_env_ok rho ->
  locally_closed_ty (ti_left i) -> locally_closed_ty (ti_right i) ->
  ~ In X (tm_ty_fv t) ->
  tm_ty_inst_r (rho_set rho X i) (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (tm_ty_inst_r rho t) (ti_right i).
Proof.
  intros rho X i t Hok Hleft Hright Hfresh.
  unfold open_tm_ty.
  rewrite (tm_ty_inst_r_open_rec (rho_set rho X i) 0 (Ty_FVar X) t
    (type_env_ok_set rho X i Hok Hleft Hright)).
  simpl. replace (ti_right (rho_set rho X i X)) with (ti_right i).
  2: { unfold rho_set. rewrite Nat.eqb_refl; reflexivity. }
  rewrite (tm_ty_inst_r_set_fresh rho X i t Hfresh).
  reflexivity.
Qed.

Fixpoint erase_tm_vars (t : tm) : tm :=
  match t with
  | tm_bvar _ | tm_fvar _ => tm_fvar 0
  | tm_abs A b => tm_abs A (erase_tm_vars b)
  | tm_app f a => tm_app (erase_tm_vars f) (erase_tm_vars a)
  | tm_tabs b => tm_tabs (erase_tm_vars b)
  | tm_tapp f A => tm_tapp (erase_tm_vars f) A
  | tm_choice a b => tm_choice (erase_tm_vars a) (erase_tm_vars b)
  end.

Lemma erase_tm_vars_open : forall k x t,
  erase_tm_vars (open_tm_rec k (tm_fvar x) t) = erase_tm_vars t.
Proof.
  intros k x t; revert k x; induction t; intros k x; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma erase_tm_vars_ty_open_rec : forall j t U,
  erase_tm_vars (open_tm_ty_rec j U t) = open_tm_ty_rec j U (erase_tm_vars t).
Proof.
  intros j t; revert j; induction t; intros j U; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt with (j:=S j); reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.
Lemma erase_tm_vars_ty_open : forall t U,
  erase_tm_vars (open_tm_ty t U) = open_tm_ty (erase_tm_vars t) U.
Proof. intros; apply erase_tm_vars_ty_open_rec. Qed.

Inductive typed_ann_wf : ty_context -> tm -> Prop :=
| TAW_bvar : forall Delta n, typed_ann_wf Delta (tm_bvar n)
| TAW_fvar : forall Delta x, typed_ann_wf Delta (tm_fvar x)
| TAW_abs : forall Delta A b,
    wf_ty Delta A -> typed_ann_wf Delta b -> typed_ann_wf Delta (tm_abs A b)
| TAW_app : forall Delta f a,
    typed_ann_wf Delta f -> typed_ann_wf Delta a -> typed_ann_wf Delta (tm_app f a)
| TAW_tabs : forall (L : list atom) Delta b,
    (forall X, ~ In X L -> typed_ann_wf (X :: Delta) (open_tm_ty b (Ty_FVar X))) ->
    typed_ann_wf Delta (tm_tabs b)
| TAW_tapp : forall Delta f A,
    typed_ann_wf Delta f -> wf_ty Delta A -> typed_ann_wf Delta (tm_tapp f A)
| TAW_choice : forall Delta a b,
    typed_ann_wf Delta a -> typed_ann_wf Delta b -> typed_ann_wf Delta (tm_choice a b).

Lemma has_type_typed_ann_wf : forall Delta Gamma t T,
  has_type Delta Gamma t T -> typed_ann_wf Delta (erase_tm_vars t).
Proof.
  intros Delta Gamma t T H; induction H; simpl.
  - constructor.
  - apply TAW_abs; [assumption|].
    destruct (fresh_atom' L) as [x Hx].
    pose proof (H1 x Hx) as Hbody.
    change (typed_ann_wf Delta (erase_tm_vars (open_tm_rec 0 (tm_fvar x) t2))) in Hbody.
    rewrite erase_tm_vars_open in Hbody. exact Hbody.
  - apply TAW_app; assumption.
  - eapply TAW_tabs with (L:=L). intros X HX.
    pose proof (H0 X HX) as Hbody.
    rewrite erase_tm_vars_ty_open in Hbody. exact Hbody.
  - apply TAW_tapp; assumption.
  - apply TAW_choice; assumption.
Qed.

Fixpoint context_names (Gamma : context) : list atom :=
  match Gamma with [] => [] | (x, _) :: G => x :: context_names G end.

Lemma lookup_context_names : forall x Gamma T,
  lookup_context x Gamma = Some T -> In x (context_names Gamma).
Proof.
  intros x Gamma; induction Gamma as [|[y A] G IH]; simpl; intros T H; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y. left; reflexivity.
  - right. eapply IH; exact H.
Qed.

Lemma tm_fv_open_incl : forall k x t,
  incl (tm_fv t) (tm_fv (open_tm_rec k (tm_fvar x) t)).
Proof.
  intros k x t; revert k x; induction t; intros k x y Hin; simpl in *.
  - contradiction.
  - exact Hin.
  - eapply IHt; exact Hin.
  - apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; eapply IHt1|right; eapply IHt2]; eauto.
  - eapply IHt; exact Hin.
  - eapply IHt; exact Hin.
  - apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; eapply IHt1|right; eapply IHt2]; eauto.
Qed.

Lemma tm_fv_ty_open_rec : forall j t U, tm_fv (open_tm_ty_rec j U t) = tm_fv t.
Proof.
  intros j t; revert j; induction t; intros j U; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.
Lemma tm_fv_ty_open : forall t U, tm_fv (open_tm_ty t U) = tm_fv t.
Proof. intros; apply tm_fv_ty_open_rec. Qed.

Lemma has_type_fv_in_context : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall x, In x (tm_fv t) -> lookup_context x Gamma <> None.
Proof.
  intros Delta Gamma t T H; induction H; intros y Hin; simpl in *.
  - destruct Hin as [E|[]]. subst y. rewrite H. discriminate.
  - destruct (fresh_atom' (L ++ context_names Gamma ++ tm_fv t2)) as [x Hx].
    assert (HxL : ~ In x L) by (intro HinL; apply Hx; apply in_or_app; left; exact HinL).
    assert (HxG : ~ In x (context_names Gamma)).
    { intro HinG; apply Hx; apply in_or_app; right; apply in_or_app; left; exact HinG. }
    assert (HxT : ~ In x (tm_fv t2)).
    { intro HinT; apply Hx; apply in_or_app; right; apply in_or_app; right; exact HinT. }
    specialize (H0 x HxL).
    assert (Hin' : In y (tm_fv (open_tm t2 (tm_fvar x))))
      by (eapply tm_fv_open_incl; exact Hin).
    specialize (H1 x HxL y Hin').
    destruct (Nat.eq_dec x y) as [->|Hneq].
    + apply HxT in Hin; contradiction.
    + change (lookup_context y (update Gamma x T1) <> None) in H1.
      rewrite lookup_update_neq in H1 by congruence. exact H1.
  - apply in_app_iff in Hin as [Hin|Hin].
    + eapply IHhas_type1; exact Hin.
    + eapply IHhas_type2; exact Hin.
  - destruct (fresh_atom' L) as [X HX].
    pose proof (H0 X HX) as Hfv.
    rewrite tm_fv_ty_open in Hfv. apply Hfv; exact Hin.
  - apply IHhas_type; exact Hin.
  - apply in_app_iff in Hin as [H1|H2].
    + eapply IHhas_type1; exact H1.
    + eapply IHhas_type2; exact H2.
Qed.

Lemma has_type_empty_fv_nil : forall t T,
  has_type [] empty t T -> tm_fv t = [].
Proof.
  intros t T H. destruct (tm_fv t) as [|x xs] eqn:E; [reflexivity|].
  exfalso. pose proof (has_type_fv_in_context _ _ _ _ H x) as Hlook.
  assert (Hin : In x (tm_fv t)) by (rewrite E; simpl; auto).
  specialize (Hlook Hin). simpl in Hlook. contradiction.
Qed.

Lemma lc_tm_open_inv : forall K k x t,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  intros K k x t; revert K k x; induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_tm_bvar. apply Nat.eqb_eq in E. lia.
    + inversion H; subst. apply lc_tm_bvar. lia.
  - inversion H; constructor.
  - inversion H; subst. constructor; [assumption|]. eapply IHt; eassumption.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. constructor. eapply IHt; eassumption.
  - inversion H; subst. constructor; [eapply IHt|assumption]; eassumption.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
Qed.

Lemma lc_tm_ty_open_inv : forall K k X t,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k X t; revert K k; induction t; intros K k H; simpl in H.
  - inversion H; constructor; assumption.
  - inversion H; constructor.
  - inversion H; subst. constructor; eauto using lc_ty_open_inv.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto using lc_ty_open_inv.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T HT.
  refine (@has_type_ind
    (fun Delta Gamma t T => locally_closed_tm t)
    _ _ _ _ _ _ Delta Gamma t T HT).
  - intros. constructor.
  - intros L D G A b B Hwf Htyping Hih.
    constructor.
    + eapply (wf_ty_lc A D); eassumption.
    + destruct (fresh_atom' L) as [x Hx].
      pose proof (Hih x Hx) as Hlc.
      change (lc_tm_at 0 0 (open_tm_rec 0 (tm_fvar x) b)) in Hlc.
      eapply lc_tm_open_inv; exact Hlc.
  - intros. constructor; assumption.
  - intros L D G b B Htyping Hih.
    constructor.
    destruct (fresh_atom' L) as [X HX].
    pose proof (Hih X HX) as Hlc.
    change (lc_tm_at 0 0 (open_tm_ty_rec 0 (Ty_FVar X) b)) in Hlc.
    eapply lc_tm_ty_open_inv; exact Hlc.
  - intros D G f B U Htyping Hih Hwf.
    constructor; [exact Hih|eapply (wf_ty_lc U D); eassumption].
  - intros. constructor; assumption.
Qed.


Lemma lc_tm_open_noop : forall K k j u arg,
  k <= j -> lc_tm_at K k u -> open_tm_rec j arg u = u.
Proof.
  intros K k j u arg Hle Hlc; revert K k j Hle Hlc.
  induction u; intros K k j Hle Hlc; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb j n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHu with (K:=K) (k:=S k) (j:=S j); eauto; lia.
  - inversion Hlc; subst. f_equal; [eapply IHu1|eapply IHu2]; eauto.
  - inversion Hlc; subst. f_equal. eapply IHu with (K:=S K) (k:=k) (j:=j); eauto.
  - inversion Hlc; subst. f_equal. eapply IHu; eauto.
  - inversion Hlc; subst. f_equal; [eapply IHu1|eapply IHu2]; eauto.
Qed.

Lemma tm_inst_closed_identity : forall theta t,
  tm_fv t = [] -> tm_inst theta t = t.
Proof.
  intros theta t; induction t; simpl; intros Hclosed; try reflexivity.
  - discriminate.
  - rewrite IHt; auto.
  - apply app_eq_nil in Hclosed as [H1 H2]. rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - apply app_eq_nil in Hclosed as [H1 H2]. rewrite IHt1, IHt2; auto.
Qed.

Lemma tm_inst_open_fresh : forall theta x arg k t,
  (forall y, locally_closed_tm (theta y)) ->
  tm_fv arg = [] ->
  ~ In x (tm_fv t) ->
  tm_inst (theta_set theta x arg) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k arg (tm_inst theta t).
Proof.
  intros theta x arg k t; revert x arg k; induction t as
    [n|y|A b IHb|f IHf a IHa|b IHb|f IHf A|a IHa b IHb];
    intros x arg k Htheta Hclosed Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold theta_set. rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - simpl in Hfresh. unfold theta_set.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; subst y. exfalso; apply Hfresh; simpl; auto.
    + rewrite (lc_tm_open_noop 0 0 k (theta y) arg (Nat.le_0_l k) (Htheta y)). reflexivity.
  - assert (Hf : ~ In x (tm_fv b)) by (intro Hin; apply Hfresh; simpl; exact Hin).
    rewrite IHb with (x:=x) (arg:=arg) (k:=S k); auto.
  - assert (Hf : ~ In x (tm_fv f)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Ha : ~ In x (tm_fv a)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite IHf with (x:=x) (arg:=arg) (k:=k), IHa with (x:=x) (arg:=arg) (k:=k); auto.
  - rewrite IHb with (x:=x) (arg:=arg) (k:=k); auto.
  - assert (Hf : ~ In x (tm_fv f)) by (intro Hin; apply Hfresh; simpl; exact Hin).
    rewrite IHf with (x:=x) (arg:=arg) (k:=k); auto.
  - assert (Hf : ~ In x (tm_fv a)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hb : ~ In x (tm_fv b)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite IHa with (x:=x) (arg:=arg) (k:=k), IHb with (x:=x) (arg:=arg) (k:=k); auto.
Qed.

Lemma sem_tm_lc : forall rho theta t,
  type_env_ok rho ->
  (forall x, locally_closed_tm (theta x)) ->
  locally_closed_tm t ->
  locally_closed_tm (tm_inst theta (tm_ty_inst rho t)).
Proof.
  intros rho theta t Hok Htheta Hlc.
  destruct (tm_ty_inst_lc rho 0 0 t Hok Hlc) as [Hleft _].
  eapply tm_inst_lc; eauto.
Qed.

Lemma sem_tm_r_lc : forall rho theta t,
  type_env_ok rho ->
  (forall x, locally_closed_tm (theta x)) ->
  locally_closed_tm t ->
  locally_closed_tm (tm_inst theta (tm_ty_inst_r rho t)).
Proof.
  intros rho theta t Hok Htheta Hlc.
  destruct (tm_ty_inst_lc rho 0 0 t Hok Hlc) as [_ Hright].
  eapply tm_inst_lc; eauto.
Qed.

Lemma tm_fv_ty_inst : forall rho t,
  tm_fv (tm_ty_inst rho t) = tm_fv t.
Proof.
  intros rho t; induction t; simpl; try reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma tm_fv_ty_inst_r : forall rho t,
  tm_fv (tm_ty_inst_r rho t) = tm_fv t.
Proof.
  intros rho t; induction t; simpl; try reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma tm_inst_open_tm_ty_rec : forall theta k U t,
  (forall x, locally_closed_tm (theta x)) ->
  tm_inst theta (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (tm_inst theta t).
Proof.
  intros theta k U t Htheta; revert k U Htheta; induction t; intros k U Htheta; simpl.
  - reflexivity.
  - symmetry. eapply open_tm_ty_rec_lc_noop with (K:=0) (k:=0) (j:=k) (U:=U).
    + lia.
    + apply Htheta.
  - rewrite IHt by exact Htheta. reflexivity.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
Qed.

Lemma tm_inst_open_tm_ty : forall theta t U,
  (forall x, locally_closed_tm (theta x)) ->
  tm_inst theta (open_tm_ty t U) = open_tm_ty (tm_inst theta t) U.
Proof. intros; apply tm_inst_open_tm_ty_rec; assumption. Qed.

Lemma tm_inst_fv_closed : forall theta t,
  (forall x, tm_fv (theta x) = []) -> tm_fv (tm_inst theta t) = [].
Proof.
  intros theta t Htheta; induction t; simpl; try reflexivity.
  - apply Htheta.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma theta_set_fv_closed : forall theta x a,
  (forall y, tm_fv (theta y) = []) -> tm_fv a = [] ->
  forall y, tm_fv (theta_set theta x a y) = [].
Proof.
  intros theta x a Htheta Ha y. unfold theta_set.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma theta_set_lc : forall theta x a,
  (forall y, locally_closed_tm (theta y)) -> locally_closed_tm a ->
  forall y, locally_closed_tm (theta_set theta x a y).
Proof.
  intros theta x a Htheta Ha y. unfold theta_set.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma fundamental_relation : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho th1 th2,
    type_env_ok rho ->
    (forall x, locally_closed_tm (th1 x)) ->
    (forall x, locally_closed_tm (th2 x)) ->
    (forall x, tm_fv (th1 x) = []) ->
    (forall x, tm_fv (th2 x) = []) ->
    term_env_ok rho Gamma th1 th2 ->
    runs (vrel rho [] T) (tm_inst th1 (tm_ty_inst rho t))
                         (tm_inst th2 (tm_ty_inst_r rho t)).
Proof.
  intros Delta Gamma t T HT.
  induction HT using has_type_ind; intros rho th1 th2 Hok Hth1 Hth2 Hth1c Hth2c Henv.
  - unfold term_env_ok in Henv. specialize (Henv x T H).
    destruct Henv as [_ [_ Hrun]]. exact Hrun.
  - assert (HlcAbs : locally_closed_tm (tm_abs T1 t2)).
    { eapply has_type_lc. econstructor; eauto. }
    assert (HlcL : locally_closed_tm (tm_inst th1 (tm_ty_inst rho (tm_abs T1 t2))))
      by (eapply sem_tm_lc; eauto).
    assert (HlcR : locally_closed_tm (tm_inst th2 (tm_ty_inst_r rho (tm_abs T1 t2))))
      by (eapply sem_tm_r_lc; eauto).
    unfold tm_ty_inst, tm_ty_inst_r, tm_inst in HlcL, HlcR; simpl in HlcL, HlcR.
    apply runs_values.
    + constructor; exact HlcL.
    + constructor; exact HlcR.
    + apply tm_inst_fv_closed; exact Hth1c.
    + apply tm_inst_fv_closed; exact Hth2c.
    + unfold vrel; simpl. exists (ty_inst rho T1),
      (tm_inst th1 (tm_ty_inst rho t2)). split; [reflexivity|].
      split; [constructor; exact HlcL|].
      split; [constructor; exact HlcR|].
      split; [exists (ty_inst_r rho T1), (tm_inst th2 (tm_ty_inst_r rho t2)); reflexivity|].
      intros x y Hxy.
      destruct Hxy as [a [b [Hma [Hmb [Hva [Hvb [Hca [Hcb Hab]]]]]]]].
      pose proof (fresh_atom' (L ++ tm_fv t2)) as [z Hz].
      assert (HzL : ~ In z L) by (intro Hfreshx; apply Hz; apply in_or_app; left; exact Hfreshx).
      assert (Hzb : ~ In z (tm_fv t2)) by (intro Hfreshx; apply Hz; apply in_or_app; right; exact Hfreshx).
      assert (HabRun : runs (vrel rho [] T1) a b).
      { apply runs_values; assumption. }
      specialize (H1 z HzL rho (theta_set th1 z a) (theta_set th2 z b)
        Hok (theta_set_lc th1 z a Hth1 (value_lc a Hva))
        (theta_set_lc th2 z b Hth2 (value_lc b Hvb))
        (theta_set_fv_closed th1 z a Hth1c Hca)
        (theta_set_fv_closed th2 z b Hth2c Hcb)
        (term_env_ok_set rho Gamma th1 th2 z T1 a b Henv
           (value_lc a Hva) (value_lc b Hvb) HabRun)).
      assert (HfreshSemL : ~ In z (tm_fv (tm_ty_inst rho t2))).
      { rewrite tm_fv_ty_inst. exact Hzb. }
      assert (HfreshSemR : ~ In z (tm_fv (tm_ty_inst_r rho t2))).
      { rewrite tm_fv_ty_inst_r. exact Hzb. }
      change (runs (vrel rho [] T2)
        (tm_inst (theta_set th1 z a)
          (tm_ty_inst rho (open_tm t2 (tm_fvar z))))
        (tm_inst (theta_set th2 z b)
          (tm_ty_inst_r rho (open_tm t2 (tm_fvar z))))) in H1.
      unfold open_tm in H1.
      rewrite tm_ty_inst_tm_open_rec in H1.
      rewrite tm_ty_inst_r_tm_open_rec in H1.
      rewrite (tm_inst_open_fresh th1 z a 0 (tm_ty_inst rho t2) Hth1 Hca HfreshSemL) in H1.
      rewrite (tm_inst_open_fresh th2 z b 0 (tm_ty_inst_r rho t2) Hth2 Hcb HfreshSemR) in H1.
      destruct H1 as [r [s [Hr [Hs [Hvr [Hvs [Hcr [Hcs Hrel]]]]]]]].
      exists r, s. repeat split; try assumption.
      * eapply multi_trans.
        -- apply multi_app_right; [constructor; exact HlcL|exact Hma].
        -- eapply multi_trans; [apply multi_app_abs; eauto|exact Hr].
      * eapply multi_trans.
        -- apply multi_app_right; [constructor; exact HlcR|exact Hmb].
        -- eapply multi_trans; [apply multi_app_abs; eauto|exact Hs].
  - assert (Hlc2 : locally_closed_tm t2) by (eapply has_type_lc; eauto).
    assert (Hlc2L : locally_closed_tm (tm_inst th1 (tm_ty_inst rho t2)))
      by (eapply sem_tm_lc; eauto).
    assert (Hlc2R : locally_closed_tm (tm_inst th2 (tm_ty_inst_r rho t2)))
      by (eapply sem_tm_r_lc; eauto).
    specialize (IHHT1 rho th1 th2 Hok Hth1 Hth2 Hth1c Hth2c Henv) as Hfun.
    specialize (IHHT2 rho th1 th2 Hok Hth1 Hth2 Hth1c Hth2c Henv) as Harg.
    destruct Hfun as [f [g [Hmf [Hmg [Hfv [Hgv [Hcf [Hcg Hfr]]]]]]]].
    destruct Harg as [a [b [Hma [Hmb [Hva [Hvb [Hca [Hcb Hab]]]]]]]].
    assert (HabRun : runs (vrel rho [] T1) a b).
    { apply runs_values; assumption. }
    destruct Hfr as [Af [bf [Hf [Hfval [Hgval [Hex Hfn]]]]]].
    destruct Hex as [Ag [bg Hg]]. subst f g.
    specialize (Hfn a b HabRun).
    destruct Hfn as [r [s [HrunL [HrunR [Hvr [Hvs [Hcr [Hcs Hrel]]]]]]]].
    exists r, s. repeat split; try assumption.
    + eapply multi_trans.
      * eapply multi_trans.
        -- apply multi_app_left; [exact Hmf|exact Hlc2L].
        -- apply multi_app_right; [exact Hfval|exact Hma].
      * exact HrunL.
    + eapply multi_trans.
      * eapply multi_trans.
        -- apply multi_app_left; [exact Hmg|exact Hlc2R].
        -- apply multi_app_right; [exact Hgval|exact Hmb].
      * exact HrunR.
  - assert (HlcTabs : locally_closed_tm (tm_tabs t)).
    { eapply has_type_lc. econstructor; eauto. }
    assert (HlcL : locally_closed_tm (tm_inst th1 (tm_ty_inst rho (tm_tabs t))))
      by (eapply sem_tm_lc; eauto).
    assert (HlcR : locally_closed_tm (tm_inst th2 (tm_ty_inst_r rho (tm_tabs t))))
      by (eapply sem_tm_r_lc; eauto).
    unfold tm_ty_inst, tm_ty_inst_r, tm_inst in HlcL, HlcR; simpl in HlcL, HlcR.
    apply runs_values.
    + constructor; exact HlcL.
    + constructor; exact HlcR.
    + apply tm_inst_fv_closed; exact Hth1c.
    + apply tm_inst_fv_closed; exact Hth2c.
    + unfold vrel; simpl. exists (tm_inst th1 (tm_ty_inst rho t)),
        (tm_inst th2 (tm_ty_inst_r rho t)). split; [reflexivity|].
      split; [reflexivity|]. split; [constructor; exact HlcL|].
      split; [constructor; exact HlcR|].
      intros SL SR HSL HSR Rel.
    pose proof (fresh_atom' (L ++ context_ty_fv Gamma ++ tm_ty_fv t ++ ty_fv T)) as [X HX].
    assert (HXL : ~ In X L).
    { intro HinX; apply HX; apply in_or_app; left; exact HinX. }
    assert (HXG : ~ In X (context_ty_fv Gamma)).
    { intro HinX; apply HX; apply in_or_app; right; apply in_or_app; left; exact HinX. }
    assert (HXt : ~ In X (tm_ty_fv t)).
    { intro HinX; apply HX; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact HinX. }
    assert (HXT : ~ In X (ty_fv T)).
    { intro HinX; apply HX; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact HinX. }
    set (i := mk_type_interp SL SR Rel).
    assert (Hok' : type_env_ok (rho_set rho X i))
      by (eapply type_env_ok_set; eauto).
    assert (Henv' : term_env_ok (rho_set rho X i) Gamma th1 th2)
      by (eapply term_env_ok_rho_set_fresh; eauto).
    pose proof (H0 X HXL (rho_set rho X i) th1 th2 Hok' Hth1 Hth2 Hth1c Hth2c Henv') as Hbody.
    rewrite (tm_ty_inst_set_open rho X i t Hok HSL HSR HXt) in Hbody.
    rewrite (tm_ty_inst_r_set_open rho X i t Hok HSL HSR HXt) in Hbody.
    unfold i in Hbody; simpl in Hbody.
    rewrite (tm_inst_open_tm_ty th1 (tm_ty_inst rho t) SL Hth1) in Hbody.
    rewrite (tm_inst_open_tm_ty th2 (tm_ty_inst_r rho t) SR Hth2) in Hbody.
    assert (Htypeeq : forall a b,
      vrel (rho_set rho X i) [] (open_ty T (Ty_FVar X)) a b <->
      vrel rho [Rel] T a b).
    { intros a b.
      assert (HRstable : forall pre p q,
        Rel p q <-> vrel (rho_set rho X i) (pre ++ []) (Ty_FVar X) p q).
      { intros pre p q. simpl. unfold rho_set, i. rewrite Nat.eqb_refl. reflexivity. }
      pose proof (vrel_open_stable (rho_set rho X i) [] (Ty_FVar X) Rel
        (lc_ty_fvar 0 X) HRstable eq_refl [] T a b) as Hop.
      pose proof (vrel_set_fresh rho X i T [Rel] HXT a b) as Hset.
      tauto. }
    apply (proj2 (@runs_ext (vrel rho [Rel] T)
      (vrel (rho_set rho X i) [] (open_ty T (Ty_FVar X))) _ _
      (fun a b => iff_sym (Htypeeq a b)))).
    exact Hbody.
  - specialize (IHHT rho th1 th2 Hok Hth1 Hth2 Hth1c Hth2c Henv) as Hfun.
    destruct Hfun as [f [g [Hmf [Hmg [Hfv [Hgv [Hcf [Hcg Hrel]]]]]]]].
    destruct Hrel as [b [c [Hfb [Hgc [Hbval [Hcval Hall]]]]]]. subst f g.
    destruct (ty_inst_lc rho 0 U Hok (wf_ty_lc U Delta H)) as [HUL HUR].
    set (RU := vrel rho [] U).
    specialize (Hall (ty_inst rho U) (ty_inst_r rho U) HUL HUR RU) as Hbody.
    assert (Hout : forall a b,
      vrel rho [RU] T a b <-> vrel rho [] (open_ty T U) a b).
    { intros x y. eapply vrel_open_stable with (bs:=[]) (U:=U) (R:=RU) (pre:=[]).
      - exact (wf_ty_lc U Delta H).
      - intros pre p q. unfold RU. apply vrel_lc_env_irrel with (k:=0).
        + intros n Hn; lia.
        + exact (wf_ty_lc U Delta H).
      - reflexivity. }
    apply (proj1 (@runs_ext (vrel rho [RU] T)
      (vrel rho [] (open_ty T U)) _ _ Hout)) in Hbody.
    destruct Hbody as [r [s [HbodyL [HbodyR [Hvr [Hvs [Hcr [Hcs Hrel]]]]]]]].
    exists r, s. repeat split; try assumption.
    + eapply multi_trans.
      * eapply multi_trans.
        -- apply multi_tapp; [exact Hmf|exact HUL].
        -- apply multi_tapp_tabs; [apply value_lc; exact Hfv|exact HUL].
      * exact HbodyL.
    + eapply multi_trans.
      * eapply multi_trans.
        -- apply multi_tapp; [exact Hmg|exact HUR].
        -- apply multi_tapp_tabs; [apply value_lc; exact Hgv|exact HUR].
      * exact HbodyR.
  - assert (Hlc1 : locally_closed_tm t1) by (eapply has_type_lc; eauto).
    assert (Hlc2 : locally_closed_tm t2) by (eapply has_type_lc; eauto).
    assert (Hlc1L : locally_closed_tm (tm_inst th1 (tm_ty_inst rho t1)))
      by (eapply sem_tm_lc; eauto).
    assert (Hlc2L : locally_closed_tm (tm_inst th1 (tm_ty_inst rho t2)))
      by (eapply sem_tm_lc; eauto).
    assert (Hlc1R : locally_closed_tm (tm_inst th2 (tm_ty_inst_r rho t1)))
      by (eapply sem_tm_r_lc; eauto).
    assert (Hlc2R : locally_closed_tm (tm_inst th2 (tm_ty_inst_r rho t2)))
      by (eapply sem_tm_r_lc; eauto).
    specialize (IHHT1 rho th1 th2 Hok Hth1 Hth2 Hth1c Hth2c Henv) as Hleft.
    destruct Hleft as [r [s [Hmr [Hms [Hvr [Hvs [Hcr [Hcs Hrel]]]]]]]].
    exists r, s. repeat split; try assumption.
    + eapply multi_trans.
      * eapply multi_step.
        -- apply ST_ChoiceLeft; assumption.
        -- constructor.
      * exact Hmr.
    + eapply multi_trans.
      * eapply multi_step.
        -- apply ST_ChoiceLeft; assumption.
        -- constructor.
      * exact Hms.
Qed.

Lemma ty_fv_open_rec_incl : forall T k X,
  incl (ty_fv T) (ty_fv (open_ty_rec k (Ty_FVar X) T)).
Proof.
  intros T; induction T; intros k X Y Hin; simpl in *.
  - contradiction.
  - exact Hin.
  - apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff;
      [left; eapply IHT1|right; eapply IHT2]; eauto.
  - eapply IHT; exact Hin.
Qed.

Lemma tm_ty_fv_open_rec_incl : forall t k X,
  incl (tm_ty_fv t) (tm_ty_fv (open_tm_ty_rec k (Ty_FVar X) t)).
Proof.
  intros t; induction t; intros k X Y Hin; simpl in *.
  - contradiction.
  - contradiction.
  - apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff.
    + left. eapply ty_fv_open_rec_incl; exact Hin.
    + right. eapply IHt; exact Hin.
  - apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff;
      [left; eapply IHt1|right; eapply IHt2]; eauto.
  - eapply IHt; exact Hin.
  - apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff.
    + left. eapply IHt; exact Hin.
    + right. eapply ty_fv_open_rec_incl; exact Hin.
  - apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff;
      [left; eapply IHt1|right; eapply IHt2]; eauto.
Qed.

Lemma wf_ty_fv_in_context : forall Delta T,
  wf_ty Delta T -> forall X, In X (ty_fv T) -> In X Delta.
Proof.
  intros Delta T H; induction H; intros Y Hin; simpl in *.
  - destruct Hin as [->|[]]; assumption.
  - apply in_app_iff in Hin as [Hin|Hin]; [eapply IHwf_ty1|eapply IHwf_ty2]; eassumption.
  - destruct (fresh_atom' (L ++ [Y])) as [Z HZ].
    assert (HZL : ~ In Z L) by (intro Hx; apply HZ; apply in_or_app; left; exact Hx).
    assert (HZY : Z <> Y).
    { intro Heq; subst Z. apply HZ. apply in_or_app; right. simpl; auto. }
    specialize (H Z HZL).
    assert (HYopen : In Y (ty_fv (open_ty T (Ty_FVar Z)))).
    { unfold open_ty. eapply ty_fv_open_rec_incl; exact Hin. }
    specialize (H0 Z HZL Y HYopen).
    simpl in H0. destruct H0 as [Heq|HinD].
    + contradiction.
    + exact HinD.
Qed.

Lemma typed_ann_wf_ty_fv_in_context : forall Delta t,
  typed_ann_wf Delta t -> forall X, In X (tm_ty_fv t) -> In X Delta.
Proof.
  intros Delta t H; induction H; intros Y Hin; simpl in *.
  - contradiction.
  - contradiction.
  - apply in_app_iff in Hin as [Hin|Hin].
    + eapply wf_ty_fv_in_context; eauto.
    + eapply IHtyped_ann_wf; eauto.
  - apply in_app_iff in Hin as [Hin|Hin].
    + eapply IHtyped_ann_wf1; eauto.
    + eapply IHtyped_ann_wf2; eauto.
  - destruct (fresh_atom' (L ++ [Y])) as [Z HZ].
    assert (HZL : ~ In Z L) by (intro Hx; apply HZ; apply in_or_app; left; exact Hx).
    assert (HZY : Z <> Y).
    { intro Heq; subst Z. apply HZ. apply in_or_app; right. simpl; auto. }
    specialize (H Z HZL).
    assert (HYopen : In Y (tm_ty_fv (open_tm_ty b (Ty_FVar Z)))).
    { unfold open_tm_ty. eapply tm_ty_fv_open_rec_incl; exact Hin. }
    specialize (H0 Z HZL Y HYopen).
    simpl in H0. destruct H0 as [Heq|HinD].
    + contradiction.
    + exact HinD.
  - apply in_app_iff in Hin as [Hin|Hin].
    + eapply IHtyped_ann_wf; eauto.
    + eapply wf_ty_fv_in_context; eauto.
  - apply in_app_iff in Hin as [Hin|Hin].
    + eapply IHtyped_ann_wf1; eauto.
    + eapply IHtyped_ann_wf2; eauto.
Qed.

Lemma tm_ty_fv_erase : forall t,
  tm_ty_fv (erase_tm_vars t) = tm_ty_fv t.
Proof.
  induction t; simpl; try reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma has_type_empty_tm_ty_fv_nil : forall t T,
  has_type [] empty t T -> tm_ty_fv t = [].
Proof.
  intros t T H. pose proof (has_type_typed_ann_wf [] empty t T H) as Htyped.
  destruct (tm_ty_fv t) as [|X xs] eqn:E; [reflexivity|].
  exfalso. pose proof (typed_ann_wf_ty_fv_in_context [] (erase_tm_vars t) Htyped X) as Hfv.
  rewrite tm_ty_fv_erase in Hfv.
  rewrite E in Hfv. apply Hfv. left; reflexivity.
Qed.

Lemma ty_inst_closed_identity : forall rho T,
  ty_fv T = [] -> ty_inst rho T = T /\ ty_inst_r rho T = T.
Proof.
  intros rho T; induction T; simpl; intros Hclosed.
  - split; reflexivity.
  - discriminate.
  - apply app_eq_nil in Hclosed as [H1 H2].
    destruct (IHT1 H1) as [E1 E1']; destruct (IHT2 H2) as [E2 E2'];
      rewrite E1, E1', E2, E2'; auto.
  - destruct (IHT Hclosed) as [E E']; rewrite E, E'; auto.
Qed.

Lemma tm_ty_inst_closed_identity : forall rho t,
  tm_ty_fv t = [] -> tm_ty_inst rho t = t /\ tm_ty_inst_r rho t = t.
Proof.
  intros rho t; induction t; simpl; intros Hclosed.
  - split; reflexivity.
  - split; reflexivity.
  - apply app_eq_nil in Hclosed as [HA Hb].
    destruct (ty_inst_closed_identity rho t HA) as [EA EA'].
    destruct (IHt Hb) as [Eb Eb']; rewrite EA, EA', Eb, Eb'; auto.
  - apply app_eq_nil in Hclosed as [Hf Ha].
    destruct (IHt1 Hf) as [Ef Ef']; destruct (IHt2 Ha) as [Ea Ea'];
      rewrite Ef, Ef', Ea, Ea'; auto.
  - destruct (IHt Hclosed) as [E E']; rewrite E, E'; auto.
  - apply app_eq_nil in Hclosed as [Hf HA].
    destruct (IHt Hf) as [Ef Ef']; destruct (ty_inst_closed_identity rho t0 HA) as [EA EA'];
      rewrite Ef, Ef', EA, EA'; auto.
  - apply app_eq_nil in Hclosed as [H1 H2].
    destruct (IHt1 H1) as [E1 E1']; destruct (IHt2 H2) as [E2 E2'];
      rewrite E1, E1', E2, E2'; auto.
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
  intros t Ht U v HU Hv Hvt.
  assert (Hfv : tm_fv t = []) by (eapply has_type_empty_fv_nil; eauto).
  assert (Htyfv : tm_ty_fv t = []) by (eapply has_type_empty_tm_ty_fv_nil; eauto).
  assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
  set (rho0 := (fun _ : atom =>
    mk_type_interp (Ty_All (Ty_BVar 0)) (Ty_All (Ty_BVar 0)) (fun _ _ => False))).
  assert (Hrho0 : type_env_ok rho0).
  { intros X; unfold rho0, locally_closed_ty; simpl; split; apply lc_ty_all; constructor; lia. }
  set (theta := (fun _ : atom => v)).
  assert (Htheta_lc : forall x, locally_closed_tm (theta x)).
  { intros; unfold theta; apply value_lc; exact Hv. }
  assert (Htheta_fv : forall x, tm_fv (theta x) = []).
  { intros; unfold theta; exact (has_type_empty_fv_nil v U Hvt). }
  assert (Henv : term_env_ok rho0 empty theta theta).
  { intros x A Hlook. discriminate. }
  pose proof (fundamental_relation [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
    rho0 theta theta Hrho0 Htheta_lc Htheta_lc Htheta_fv Htheta_fv Henv) as Hrun.
  destruct (tm_ty_inst_closed_identity rho0 t Htyfv) as [HinstL HinstR].
  rewrite HinstL, HinstR in Hrun.
  rewrite (tm_inst_closed_identity theta t Hfv) in Hrun.
  destruct Hrun as [w1 [w2 [Hm1 [Hm2 [Hw1 [Hw2 [Hc1 [Hc2 Hrel]]]]]]]].
  destruct (vrel_identity_value rho0 w1 w2 U v HUlc Hv (has_type_empty_fv_nil v U Hvt) Hrel)
    as [out [Hident ->]].
  eapply multi_trans.
  - eapply multi_app_left.
    + apply multi_tapp; [exact Hm1|exact HUlc].
    + apply value_lc; exact Hv.
  - exact Hident.
Qed.

End SystemFParametricityNondeterminismHardTask.
