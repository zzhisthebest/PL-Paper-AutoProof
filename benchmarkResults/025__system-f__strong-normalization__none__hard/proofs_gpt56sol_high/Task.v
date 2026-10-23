(** System F CBV strong-normalization benchmark, Hard variant.
    Features: none. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNoneHardTask.

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

(* Construct the logical relation and supporting proofs here. *)

Record candidate : Type := {
  cand_holds : tm -> Prop;
  cand_is_value : forall v, cand_holds v -> value v
}.

Definition value_candidate : candidate.
Proof.
  refine {| cand_holds := value |}; auto.
Defined.

Definition cand_at (rho : list candidate) (i : nat) : candidate :=
  nth i rho value_candidate.

Fixpoint val_rel (T : ty) (eta : atom -> candidate)
    (rho : list candidate) (v : tm) : Prop :=
  match T with
  | Ty_BVar i => cand_holds (cand_at rho i) v
  | Ty_FVar X => cand_holds (eta X) v
  | Ty_Arrow T1 T2 =>
      value v /\
      forall u,
        (locally_closed_tm u /\
         exists w, u -->* w /\ val_rel T1 eta rho w) ->
        locally_closed_tm (tm_app v u) /\
        exists w, tm_app v u -->* w /\ val_rel T2 eta rho w
  | Ty_All T1 =>
      value v /\
      forall U (C : candidate), locally_closed_ty U ->
        locally_closed_tm (tm_tapp v U) /\
        exists w, tm_tapp v U -->* w /\ val_rel T1 eta (C :: rho) w
  end.

Definition exp_rel (T : ty) (eta : atom -> candidate)
    (rho : list candidate) (t : tm) : Prop :=
  locally_closed_tm t /\
  exists v, t -->* v /\ val_rel T eta rho v.

Lemma val_rel_is_value : forall T eta rho v,
  val_rel T eta rho v -> value v.
Proof.
  induction T; simpl; intros eta rho v H.
  - eapply cand_is_value; eauto.
  - eapply cand_is_value; eauto.
  - exact (proj1 H).
  - exact (proj1 H).
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; auto. Qed.

Definition rel_candidate (T : ty) (eta : atom -> candidate)
    (rho : list candidate) : candidate.
Proof.
  refine {| cand_holds := val_rel T eta rho |}.
  exact (val_rel_is_value T eta rho).
Defined.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v Htu Huv. induction Htu.
  - exact Huv.
  - econstructor; eauto.
Qed.

Lemma multi_app1 : forall t t' u,
  t -->* t' -> locally_closed_tm u -> tm_app t u -->* tm_app t' u.
Proof.
  intros t t' u H; induction H; intros Hu.
  - constructor.
  - econstructor. apply ST_App1; eauto. auto.
Qed.

Lemma multi_app2 : forall v u u',
  value v -> u -->* u' -> tm_app v u -->* tm_app v u'.
Proof.
  intros v u u' Hv H; induction H.
  - constructor.
  - econstructor. apply ST_App2; eauto. auto.
Qed.

Lemma multi_tapp : forall t t' U,
  t -->* t' -> locally_closed_ty U -> tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H; induction H; intros HU.
  - constructor.
  - econstructor. apply ST_TApp; eauto. auto.
Qed.

Lemma exp_rel_back : forall T eta rho t u,
  locally_closed_tm t -> t -->* u -> exp_rel T eta rho u ->
  exp_rel T eta rho t.
Proof.
  unfold exp_rel. intros T eta rho t u Hlc Htu [Hulc [v [Huv Hv]]].
  split; auto. exists v. split; eauto using multi_trans.
Qed.

Lemma exp_rel_app : forall eta rho T1 T2 t1 t2,
  exp_rel (Ty_Arrow T1 T2) eta rho t1 ->
  exp_rel T1 eta rho t2 ->
  exp_rel T2 eta rho (tm_app t1 t2).
Proof.
  intros eta rho T1 T2 t1 t2
    [Hlc1 [v [Hred [Hv Hfun]]]] Ht2.
  specialize (Hfun t2 Ht2).
  eapply exp_rel_back.
  - constructor; eauto using value_lc. exact (proj1 Ht2).
  - exact (multi_app1 _ _ _ Hred (proj1 Ht2)).
  - exact Hfun.
Qed.

Lemma exp_rel_tapp : forall eta rho T t U,
  exp_rel (Ty_All T) eta rho t -> locally_closed_ty U ->
  forall C, exp_rel T eta (C :: rho) (tm_tapp t U).
Proof.
  intros eta rho T t U [Hlct [v [Hred [Hv Hall]]]] HU C.
  specialize (Hall U C HU).
  eapply exp_rel_back.
  - constructor; eauto using value_lc.
  - exact (multi_tapp _ _ _ Hred HU).
  - exact Hall.
Qed.

Lemma value_no_step : forall v t, value v -> ~ v --> t.
Proof.
  intros v t Hv Hs. inversion Hv; subst; inversion Hs.
Qed.

Lemma step_deterministic : forall t u v, t --> u -> t --> v -> u = v.
Proof.
  intros t u v Hu. generalize dependent v.
  induction Hu; intros w Hw; inversion Hw; subst; try reflexivity;
    try solve [f_equal; eauto].
  all: match goal with
  | Hval : value ?q, Hstep : step ?q _ |- _ =>
      exfalso; exact (value_no_step _ _ Hval Hstep)
  | Hlc : locally_closed_tm (tm_abs ?A ?b),
    Hstep : step (tm_abs ?A ?b) _ |- _ =>
      exfalso; eapply value_no_step; [constructor; exact Hlc | exact Hstep]
  | Hlc : locally_closed_tm (tm_tabs ?b),
    Hstep : step (tm_tabs ?b) _ |- _ =>
      exfalso; eapply value_no_step; [constructor; exact Hlc | exact Hstep]
  end.
Qed.

Lemma multi_value_SN : forall t v,
  t -->* v -> value v -> strongly_normalizing t.
Proof.
  intros t v Hm. induction Hm; intros Hv.
  - constructor. intros u Hu. exfalso. eapply value_no_step; eauto.
  - constructor. intros u Hu.
    assert (u = y) by (eapply step_deterministic; eauto).
    subst. apply IHHm; auto.
Qed.

Lemma exp_rel_SN : forall T eta rho t,
  exp_rel T eta rho t -> strongly_normalizing t.
Proof.
  intros T eta rho t [_ [v [Hred Hv]]].
  eapply multi_value_SN; eauto using val_rel_is_value.
Qed.

Definition update_fun {A : Type} (f : atom -> A) (x : atom) (a : A) :=
  fun y => if Nat.eqb x y then a else f y.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => fv_ty A ++ fv_ty B
  | Ty_All A => fv_ty A
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => fv_tm b
  | tm_app a b => fv_tm a ++ fv_tm b
  | tm_tabs b => fv_tm b
  | tm_tapp a _ => fv_tm a
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T b => fv_ty T ++ ftv_tm b
  | tm_app a b => ftv_tm a ++ ftv_tm b
  | tm_tabs b => ftv_tm b
  | tm_tapp a T => ftv_tm a ++ fv_ty T
  end.

Fixpoint ty_fsubst (th : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => th X
  | Ty_Arrow A B => Ty_Arrow (ty_fsubst th A) (ty_fsubst th B)
  | Ty_All A => Ty_All (ty_fsubst th A)
  end.

Fixpoint tm_ty_fsubst (th : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (ty_fsubst th T) (tm_ty_fsubst th b)
  | tm_app a b => tm_app (tm_ty_fsubst th a) (tm_ty_fsubst th b)
  | tm_tabs b => tm_tabs (tm_ty_fsubst th b)
  | tm_tapp a T => tm_tapp (tm_ty_fsubst th a) (ty_fsubst th T)
  end.

Fixpoint tm_fsubst (s : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => s x
  | tm_abs T b => tm_abs T (tm_fsubst s b)
  | tm_app a b => tm_app (tm_fsubst s a) (tm_fsubst s b)
  | tm_tabs b => tm_tabs (tm_fsubst s b)
  | tm_tapp a T => tm_tapp (tm_fsubst s a) T
  end.

Lemma fv_tm_ty_fsubst : forall th t,
  fv_tm (tm_ty_fsubst th t) = fv_tm t.
Proof.
  intros th t; induction t; simpl; rewrite ?IHt, ?IHt1, ?IHt2; reflexivity.
Qed.

Lemma in_max_list : forall x L, In x L -> x <= fold_right Nat.max 0 L.
Proof.
  intros x L; induction L as [|a L IH]; simpl; intros H.
  - contradiction.
  - destruct H as [->|H]; [apply Nat.le_max_l|].
    eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma exists_fresh : forall L : list atom, exists x, ~ In x L.
Proof.
  intro L. exists (S (fold_right Nat.max 0 L)). intro H.
  pose proof (in_max_list _ _ H). lia.
Qed.

Lemma lc_open_ty_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; simpl; intros k X H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; [eapply IHT1|eapply IHT2]; eauto.
  - inversion H; subst. constructor. eapply IHT; eauto.
Qed.

Lemma wf_ty_lc : forall D T, wf_ty D T -> locally_closed_ty T.
Proof.
  intros D T H; induction H.
  - constructor.
  - constructor; auto.
  - destruct (exists_fresh L) as [X HX].
    specialize (H0 X HX). unfold locally_closed_ty in *.
    constructor. exact (lc_open_ty_inv T 0 X H0).
Qed.

Lemma lc_open_tm_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; simpl; intros K k x H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; auto. eapply IHt; eauto.
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eauto.
  - inversion H; subst. constructor. eapply IHt; eauto.
  - inversion H; subst. constructor; auto. eapply IHt; eauto.
Qed.

Lemma lc_open_tm_ty_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; simpl; intros K k X H; inversion H; subst.
  - constructor; auto.
  - constructor.
  - constructor. eapply lc_open_ty_inv; eauto. eapply IHt; eauto.
  - constructor; [eapply IHt1|eapply IHt2]; eauto.
  - constructor. eapply IHt; eauto.
  - constructor. eapply IHt; eauto. eapply lc_open_ty_inv; eauto.
Qed.

Lemma typing_lc : forall D G t T, has_type D G t T -> locally_closed_tm t.
Proof.
  intros D G t T H; induction H.
  - constructor.
  - constructor; [apply wf_ty_lc with Delta; auto|].
    destruct (exists_fresh L) as [x Hx].
    apply (lc_open_tm_inv t2 0 0 x). apply H1; auto.
  - constructor; auto.
  - constructor. destruct (exists_fresh L) as [X HX].
    apply (lc_open_tm_ty_inv t 0 0 X). apply H0; auto.
  - constructor; auto. apply wf_ty_lc with Delta; auto.
Qed.

Lemma lc_ty_weaken : forall T K K',
  lc_ty_at K T -> K <= K' -> lc_ty_at K' T.
Proof.
  induction T; intros K K' H W; inversion H; subst.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; [eapply IHT1|eapply IHT2]; eauto.
  - apply lc_ty_all. eapply IHT; eauto; lia.
Qed.

Lemma lc_tm_weaken : forall t K k K' k',
  lc_tm_at K k t -> K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  induction t; intros K k K' k' H WK Wk; inversion H; subst.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs. eapply lc_ty_weaken; eauto. eapply IHt; eauto; lia.
  - apply lc_tm_app; [eapply IHt1|eapply IHt2]; eauto.
  - apply lc_tm_tabs. eapply IHt; eauto; lia.
  - apply lc_tm_tapp. eapply IHt; eauto. eapply lc_ty_weaken; eauto.
Qed.

Lemma lc_ty_fsubst : forall T K th,
  lc_ty_at K T -> (forall X, locally_closed_ty (th X)) ->
  lc_ty_at K (ty_fsubst th T).
Proof.
  induction T; simpl; intros K th Hlc Hth; inversion Hlc; subst.
  - constructor; auto.
  - eapply lc_ty_weaken; [apply Hth|lia].
  - constructor; [eapply IHT1|eapply IHT2]; eauto.
  - constructor. eapply IHT; eauto.
Qed.

Lemma lc_tm_ty_fsubst : forall t K k th,
  lc_tm_at K k t -> (forall X, locally_closed_ty (th X)) ->
  lc_tm_at K k (tm_ty_fsubst th t).
Proof.
  induction t; simpl; intros K k th Hlc Hth; inversion Hlc; subst; constructor; eauto using lc_ty_fsubst.
Qed.

Lemma lc_tm_fsubst : forall t K k s,
  lc_tm_at K k t -> (forall x, locally_closed_tm (s x)) ->
  lc_tm_at K k (tm_fsubst s t).
Proof.
  induction t; simpl; intros K k s Hlc Hs; inversion Hlc; subst.
  - apply lc_tm_bvar; auto.
  - eapply lc_tm_weaken; [apply Hs|lia|lia].
  - apply lc_tm_abs.
    + assumption.
    + eapply IHt; eauto.
  - apply lc_tm_app; [eapply IHt1|eapply IHt2]; eauto.
  - apply lc_tm_tabs. eapply IHt; eauto.
  - apply lc_tm_tapp.
    + eapply IHt; eauto.
    + assumption.
Qed.

Lemma tm_ty_fsubst_open_tm : forall t th k u,
  tm_ty_fsubst th (open_tm_rec k u t) =
  open_tm_rec k (tm_ty_fsubst th u) (tm_ty_fsubst th t).
Proof.
  induction t; simpl; intros; try rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma open_ty_lc_id : forall T K U,
  lc_ty_at K T -> open_ty_rec K U T = T.
Proof.
  induction T; simpl; intros K U H; inversion H; subst; try (f_equal; eauto).
  destruct (Nat.eqb K n) eqn:E; auto. apply Nat.eqb_eq in E; lia.
Qed.

Lemma open_tm_ty_lc_id : forall t K k U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  induction t; simpl; intros K k U H; inversion H; subst; try (f_equal; eauto using open_ty_lc_id).
Qed.

Lemma tm_fsubst_open_tm_ty : forall t s k U,
  (forall x, locally_closed_tm (s x)) ->
  tm_fsubst s (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (tm_fsubst s t).
Proof.
  induction t; simpl; intros s k U Hs; try rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity; auto.
  symmetry. apply open_tm_ty_lc_id with (k := 0).
  eapply lc_tm_weaken; [apply Hs|lia|lia].
Qed.

Lemma open_tm_lc_id : forall t K k u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  induction t; simpl; intros K k u H; inversion H; subst; try (f_equal; eauto).
  destruct (Nat.eqb k n) eqn:E; auto. apply Nat.eqb_eq in E; lia.
Qed.

Lemma tm_fsubst_open_tm : forall t s k x u,
  (forall y, locally_closed_tm (s y)) ->
  ~ In x (fv_tm t) ->
  tm_fsubst (update_fun s x u) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (tm_fsubst s t).
Proof.
  induction t; simpl; intros s k x u Hs Hfresh.
  - destruct (Nat.eqb k n).
    + change ((if Nat.eqb x x then u else s x) = u). rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - unfold update_fun. simpl in Hfresh.
    destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. left; reflexivity.
    + symmetry. apply open_tm_lc_id with (K := 0).
      eapply lc_tm_weaken; [apply Hs|lia|lia].
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt1|apply IHt2]; auto; intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
Qed.

Lemma ty_fsubst_open : forall T th k X U,
  (forall Y, locally_closed_ty (th Y)) ->
  ~ In X (fv_ty T) ->
  ty_fsubst (update_fun th X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (ty_fsubst th T).
Proof.
  induction T; simpl; intros th k X U Hth Hfresh.
  - destruct (Nat.eqb k n).
    + change ((if Nat.eqb X X then U else th X) = U). rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - unfold update_fun. simpl in Hfresh.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. left; reflexivity.
    + symmetry. apply open_ty_lc_id.
      eapply lc_ty_weaken; [apply Hth|lia].
  - f_equal; [apply IHT1|apply IHT2]; auto; intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal. apply IHT; auto.
Qed.

Lemma tm_ty_fsubst_open_ty : forall t th k X U,
  (forall Y, locally_closed_ty (th Y)) ->
  ~ In X (ftv_tm t) ->
  tm_ty_fsubst (update_fun th X U)
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (tm_ty_fsubst th t).
Proof.
  induction t; simpl; intros th k X U Hth Hfresh; try reflexivity.
  - f_equal.
    + apply ty_fsubst_open; auto. intro H; apply Hfresh; apply in_or_app; auto.
    + apply IHt; auto. intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal; [apply IHt1|apply IHt2]; auto; intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt; auto. intro H; apply Hfresh; apply in_or_app; auto.
    + apply ty_fsubst_open; auto. intro H; apply Hfresh; apply in_or_app; auto.
Qed.

Definition rho_agree (K : nat) (r r' : list candidate) : Prop :=
  forall i, i < K -> forall v,
    cand_holds (cand_at r i) v <-> cand_holds (cand_at r' i) v.

Lemma val_rel_rho : forall T K eta r r' v,
  lc_ty_at K T -> rho_agree K r r' ->
  (val_rel T eta r v <-> val_rel T eta r' v).
Proof.
  induction T; simpl; intros K eta r r' v Hlc Hag; inversion Hlc; subst.
  - apply Hag; auto.
  - tauto.
  - split; intros [Hv Hf]; split; auto; intros u Hu.
    + destruct Hu as [Hulc [w [Huw Hw]]].
      assert (Hu : exp_rel T1 eta r u).
      { split; auto. exists w; split; auto.
        apply (proj2 (IHT1 K eta r r' w H2 Hag)); auto. }
      destruct (Hf u Hu) as [Hout [z [Hrz Hz]]].
      split; auto. exists z; split; auto.
      apply (proj1 (IHT2 K eta r r' z H3 Hag)); auto.
    + destruct Hu as [Hulc [w [Huw Hw]]].
      assert (Hu : exp_rel T1 eta r' u).
      { split; auto. exists w; split; auto.
        apply (proj1 (IHT1 K eta r r' w H2 Hag)); auto. }
      destruct (Hf u Hu) as [Hout [z [Hrz Hz]]].
      split; auto. exists z; split; auto.
      apply (proj2 (IHT2 K eta r r' z H3 Hag)); auto.
  - split; intros [Hv Hf]; split; auto; intros U C HU.
    + destruct (Hf U C HU) as [Hout [z [Hrz Hz]]]. split; auto.
      exists z; split; auto.
      assert (HC : rho_agree (S K) (C :: r) (C :: r')).
      { unfold rho_agree in *. intros [|i] Hi q.
        - unfold cand_at; simpl; tauto.
        - unfold cand_at; simpl. apply Hag. lia. }
      apply (proj1 (IHT (S K) eta (C :: r) (C :: r') z H1 HC)); exact Hz.
    + destruct (Hf U C HU) as [Hout [z [Hrz Hz]]]. split; auto.
      exists z; split; auto.
      assert (HC : rho_agree (S K) (C :: r) (C :: r')).
      { unfold rho_agree in *. intros [|i] Hi q.
        - unfold cand_at; simpl; tauto.
        - unfold cand_at; simpl. apply Hag. lia. }
      apply (proj2 (IHT (S K) eta (C :: r) (C :: r') z H1 HC)); exact Hz.
Qed.

Lemma exp_rel_rho : forall T K eta r r' t,
  lc_ty_at K T -> rho_agree K r r' ->
  (exp_rel T eta r t <-> exp_rel T eta r' t).
Proof.
  unfold exp_rel. intros. split; intros [Hlc [v [Hr Hv]]];
    split; auto; exists v; split; auto;
    [apply (proj1 (val_rel_rho T K eta r r' v H H0))|
     apply (proj2 (val_rel_rho T K eta r r' v H H0))]; auto.
Qed.

Lemma val_rel_eta : forall T eta eta' rho v,
  (forall X, In X (fv_ty T) -> eta X = eta' X) ->
  (val_rel T eta rho v <-> val_rel T eta' rho v).
Proof.
  induction T; simpl; intros eta eta' rho v Hag.
  - tauto.
  - rewrite (Hag a (or_introl eq_refl)); tauto.
  - assert (HA1 : forall X, In X (fv_ty T1) -> eta X = eta' X).
    { intros X HX; apply Hag; apply in_or_app; auto. }
    assert (HA2 : forall X, In X (fv_ty T2) -> eta X = eta' X).
    { intros X HX; apply Hag; apply in_or_app; auto. }
    split; intros [Hv Hf]; split; auto; intros u Hu.
    + destruct Hu as [Hulc [w [Huw Hw]]].
      assert (Hu : exp_rel T1 eta rho u).
      { split; auto. exists w; split; auto. apply (proj2 (IHT1 eta eta' rho w HA1)); auto. }
      destruct (Hf u Hu) as [Hout [z [Hrz Hz]]]. split; auto.
      exists z; split; auto. apply (proj1 (IHT2 eta eta' rho z HA2)); auto.
    + destruct Hu as [Hulc [w [Huw Hw]]].
      assert (Hu : exp_rel T1 eta' rho u).
      { split; auto. exists w; split; auto. apply (proj1 (IHT1 eta eta' rho w HA1)); auto. }
      destruct (Hf u Hu) as [Hout [z [Hrz Hz]]]. split; auto.
      exists z; split; auto. apply (proj2 (IHT2 eta eta' rho z HA2)); auto.
  - split; intros [Hv Hf]; split; auto; intros U C HU.
    + destruct (Hf U C HU) as [Hout [z [Hrz Hz]]]. split; auto.
      exists z; split; auto. apply (proj1 (IHT eta eta' (C :: rho) z Hag)); auto.
    + destruct (Hf U C HU) as [Hout [z [Hrz Hz]]]. split; auto.
      exists z; split; auto. apply (proj2 (IHT eta eta' (C :: rho) z Hag)); auto.
Qed.

Lemma exp_rel_eta : forall T eta eta' rho t,
  (forall X, In X (fv_ty T) -> eta X = eta' X) ->
  (exp_rel T eta rho t <-> exp_rel T eta' rho t).
Proof.
  unfold exp_rel. intros. split; intros [Hlc [v [Hr Hv]]];
    split; auto; exists v; split; auto;
    [apply (proj1 (val_rel_eta T eta eta' rho v H))|
     apply (proj2 (val_rel_eta T eta eta' rho v H))]; auto.
Qed.

Lemma cand_at_app_lt : forall pre C i,
  i < length pre -> cand_at (pre ++ C :: nil) i = cand_at pre i.
Proof.
  unfold cand_at. induction pre; simpl; intros C i H; [lia|].
  destruct i; simpl; auto. apply IHpre; lia.
Qed.

Lemma cand_at_app_eq : forall pre C,
  cand_at (pre ++ C :: nil) (length pre) = C.
Proof. unfold cand_at. induction pre; simpl; auto. Qed.

Lemma val_rel_open_rec : forall T k eta pre U v,
  length pre = k -> lc_ty_at (S k) T -> locally_closed_ty U ->
  (val_rel (open_ty_rec k U T) eta pre v <->
   val_rel T eta (pre ++ rel_candidate U eta [] :: nil) v).
Proof.
  induction T; simpl; intros k eta pre U v Hlen Hlc HU; inversion Hlc; subst.
  - destruct (Nat.eqb (length pre) n) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      rewrite cand_at_app_eq.
      unfold rel_candidate; simpl.
      apply val_rel_rho with (K := 0) (r := pre) (r' := []);
        auto; unfold rho_agree; intros; lia.
    + apply Nat.eqb_neq in E.
      assert (n < length pre) by lia.
      rewrite cand_at_app_lt; auto. reflexivity.
  - tauto.
  - split; intros [Hv Hf]; split; auto; intros u Hu.
    + destruct Hu as [Hulc [w [Huw Hw]]].
      assert (Hu : exp_rel (open_ty_rec (length pre) U T1) eta pre u).
      { split; auto. exists w; split; auto.
        apply (proj2 (IHT1 (length pre) eta pre U w eq_refl H2 HU)); auto. }
      destruct (Hf u Hu) as [Hout [z [Hrz Hz]]]. split; auto.
      exists z; split; auto.
      apply (proj1 (IHT2 (length pre) eta pre U z eq_refl H3 HU)); auto.
    + destruct Hu as [Hulc [w [Huw Hw]]].
      assert (Hu : exp_rel T1 eta (pre ++ [rel_candidate U eta []]) u).
      { split; auto. exists w; split; auto.
        apply (proj1 (IHT1 (length pre) eta pre U w eq_refl H2 HU)); auto. }
      destruct (Hf u Hu) as [Hout [z [Hrz Hz]]]. split; auto.
      exists z; split; auto.
      apply (proj2 (IHT2 (length pre) eta pre U z eq_refl H3 HU)); auto.
  - split; intros [Hv Hf]; split; auto; intros V C HV.
    + change (exp_rel T eta (C :: (pre ++ rel_candidate U eta [] :: nil))
        (tm_tapp v V)).
      change (exp_rel T eta ((C :: pre) ++ rel_candidate U eta [] :: nil)
        (tm_tapp v V)).
      destruct (Hf V C HV) as [Hout [z [Hrz Hz]]]. split; auto.
      exists z; split; auto.
      apply (proj1 (IHT (S (length pre)) eta (C :: pre) U z eq_refl H1 HU)); auto.
    + destruct (Hf V C HV) as [Hout [z [Hrz Hz]]]. split; auto.
      exists z; split; auto.
      apply (proj2 (IHT (S (length pre)) eta (C :: pre) U z eq_refl H1 HU)); auto.
Qed.

Lemma exp_rel_open : forall T eta U t,
  lc_ty_at 1 T -> locally_closed_ty U ->
  (exp_rel (open_ty T U) eta [] t <->
   exp_rel T eta [rel_candidate U eta []] t).
Proof.
  unfold exp_rel, open_ty. intros. split; intros [Hlc [v [Hr Hv]]];
    split; auto; exists v; split; auto;
    [apply (proj1 (val_rel_open_rec T 0 eta [] U v eq_refl H H0))|
     apply (proj2 (val_rel_open_rec T 0 eta [] U v eq_refl H H0))]; auto.
Qed.

Lemma lc_open_ty : forall T k U,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; simpl; intros k U HT HU; inversion HT; subst.
  - destruct (Nat.eqb k n) eqn:E.
    + eapply lc_ty_weaken; [exact HU|lia].
    + constructor. apply Nat.eqb_neq in E; lia.
  - constructor.
  - constructor; [eapply IHT1|eapply IHT2]; eauto.
  - constructor. eapply IHT; eauto.
Qed.

Lemma typing_type_lc : forall D G t T,
  has_type D G t T -> locally_closed_ty T.
Proof.
  intros D G t T H; induction H.
  - apply wf_ty_lc with Delta; auto.
  - apply lc_ty_arrow.
    + apply wf_ty_lc with Delta; auto.
    + destruct (exists_fresh L) as [x Hx]. exact (H1 x Hx).
  - inversion IHhas_type1; subst; assumption.
  - apply lc_ty_all. destruct (exists_fresh L) as [X HX].
    apply (lc_open_ty_inv T 0 X). exact (H0 X HX).
  - unfold locally_closed_ty, open_ty. eapply lc_open_ty.
    + inversion IHhas_type; subst; assumption.
    + apply wf_ty_lc with Delta; auto.
Qed.

Fixpoint fv_context (G : context) : list atom :=
  match G with
  | [] => []
  | (_, T) :: G' => fv_ty T ++ fv_context G'
  end.

Definition good_ty_sub (th : atom -> ty) : Prop :=
  forall X, locally_closed_ty (th X).

Definition good_tm_sub (G : context) (eta : atom -> candidate)
    (s : atom -> tm) : Prop :=
  (forall x, locally_closed_tm (s x)) /\
  forall x T, lookup_context x G = Some T -> exp_rel T eta [] (s x).

Lemma lookup_update_eq : forall G x T,
  lookup_context x (update G x T) = Some T.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_update_neq : forall G x y T,
  x <> y -> lookup_context y (update G x T) = lookup_context y G.
Proof.
  intros G x y T Hneq. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply Hneq. symmetry; exact E.
  - reflexivity.
Qed.

Lemma good_tm_extend : forall G eta s x T v,
  good_tm_sub G eta s -> exp_rel T eta [] v ->
  good_tm_sub (update G x T) eta (update_fun s x v).
Proof.
  intros G eta s x T v [Hlc Hrel] Hv. split.
  - intro y. unfold update_fun. destruct (Nat.eqb x y); auto. exact (proj1 Hv).
  - intros y A Hlook. unfold update_fun.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; subst. rewrite lookup_update_eq in Hlook.
      inversion Hlook; subst; exact Hv.
    + apply Nat.eqb_neq in E. rewrite lookup_update_neq in Hlook; auto.
Qed.

Lemma context_fresh_type : forall G x T X,
  lookup_context x G = Some T -> ~ In X (fv_context G) -> ~ In X (fv_ty T).
Proof.
  induction G as [|[y A] G IH]; simpl; intros x T X Hlook Hfresh; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst. intro H. apply Hfresh. apply in_or_app; auto.
  - apply IH with (x := x) (T := T); auto. intro H. apply Hfresh. apply in_or_app; auto.
Qed.

Lemma good_tm_eta_update : forall G eta s X C,
  good_tm_sub G eta s -> ~ In X (fv_context G) ->
  good_tm_sub G (update_fun eta X C) s.
Proof.
  intros G eta s X C [Hlc Hrel] Hfresh. split; auto.
  intros x T Hlook.
  assert (HA : forall Y, In Y (fv_ty T) -> eta Y = update_fun eta X C Y).
  { intros Y HY. unfold update_fun. destruct (Nat.eqb X Y) eqn:E; auto.
    apply Nat.eqb_eq in E. exfalso.
    apply (context_fresh_type G x T X Hlook Hfresh). rewrite E. exact HY. }
  apply (proj1 (exp_rel_eta T eta (update_fun eta X C) [] (s x) HA)).
  exact (Hrel x T Hlook).
Qed.

Theorem fundamental : forall D G t T,
  has_type D G t T ->
  forall th eta s,
    good_ty_sub th -> good_tm_sub G eta s ->
    exp_rel T eta [] (tm_fsubst s (tm_ty_fsubst th t)).
Proof.
  intros D G t T Hty. induction Hty; intros th eta s Hth Hs; simpl.
  - destruct Hs as [Hslc Hsrel]. exact (Hsrel x T H).
  - destruct (exists_fresh (L ++ fv_tm t2)) as [x Hfresh].
    assert (HxL : ~ In x L).
    { intro Hx. apply Hfresh. apply in_or_app; auto. }
    assert (Hxt : ~ In x (fv_tm t2)).
    { intro Hx. apply Hfresh. apply in_or_app; auto. }
    destruct Hs as [Hslc Hsrel].
    assert (Horig : locally_closed_tm (tm_abs T1 t2)).
    { eapply typing_lc. eapply T_Abs with (L := L); eauto. }
    assert (Hclosed : locally_closed_tm
      (tm_fsubst s (tm_ty_fsubst th (tm_abs T1 t2)))).
    { eapply lc_tm_fsubst.
      - eapply lc_tm_ty_fsubst; eauto.
      - exact Hslc. }
    split; [exact Hclosed|].
    exists (tm_fsubst s (tm_ty_fsubst th (tm_abs T1 t2))). split; [constructor|].
    simpl. split.
    + constructor. exact Hclosed.
    + intros u [Hulc [v [Huv Hv]]].
      assert (Hvr : exp_rel T1 eta [] v).
      { split; [eauto using value_lc, val_rel_is_value|].
        exists v; split; [constructor|exact Hv]. }
      assert (Hs' : good_tm_sub (update Gamma x T1) eta (update_fun s x v)).
      { apply good_tm_extend; auto. split; auto. }
      specialize (H1 x HxL th eta (update_fun s x v) Hth Hs').
      unfold open_tm in H1.
      rewrite tm_ty_fsubst_open_tm in H1.
      change (exp_rel T2 eta []
        (tm_fsubst (update_fun s x v)
          (open_tm_rec 0 (tm_fvar x) (tm_ty_fsubst th t2)))) in H1.
      rewrite (tm_fsubst_open_tm (tm_ty_fsubst th t2) s 0 x v Hslc) in H1.
      2: rewrite fv_tm_ty_fsubst; exact Hxt.
      eapply exp_rel_back.
      * constructor; [eauto using value_lc|exact Hulc].
      * eapply multi_trans.
        -- apply multi_app2; [constructor; exact Hclosed|exact Huv].
        -- apply multi_step with
             (y := open_tm (tm_fsubst s (tm_ty_fsubst th t2)) v).
           { apply ST_AppAbs; [exact Hclosed|eauto using val_rel_is_value]. }
           constructor.
      * exact H1.
  - eapply exp_rel_app; [apply IHHty1|apply IHHty2]; eauto.
  - destruct (exists_fresh
      (L ++ ftv_tm t ++ fv_ty T ++ fv_context Gamma)) as [X Hfresh].
    assert (HXL : ~ In X L).
    { intro HX. apply Hfresh. apply in_or_app; auto. }
    assert (HXtm : ~ In X (ftv_tm t)).
    { intro HX. apply Hfresh. apply in_or_app; right; apply in_or_app; auto. }
    assert (HXT : ~ In X (fv_ty T)).
    { intro HX. apply Hfresh. apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; auto. }
    assert (HXG : ~ In X (fv_context Gamma)).
    { intro HX. apply Hfresh. apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; auto. }
    destruct Hs as [Hslc Hsrel].
    assert (Horig : locally_closed_tm (tm_tabs t)).
    { eapply typing_lc. eapply T_TAbs with (L := L); eauto. }
    assert (Hclosed : locally_closed_tm
      (tm_fsubst s (tm_ty_fsubst th (tm_tabs t)))).
    { eapply lc_tm_fsubst.
      - eapply lc_tm_ty_fsubst; eauto.
      - exact Hslc. }
    assert (HTbody : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _
        (T_TAbs L Delta Gamma t T H)) as Hall.
      inversion Hall; subst; assumption. }
    split; [exact Hclosed|].
    exists (tm_fsubst s (tm_ty_fsubst th (tm_tabs t))). split; [constructor|].
    simpl. split.
    + constructor. exact Hclosed.
    + intros U C HU.
      assert (Hth' : good_ty_sub (update_fun th X U)).
      { intro Y. unfold update_fun. destruct (Nat.eqb X Y); auto. }
      assert (Hs' : good_tm_sub Gamma (update_fun eta X C) s).
      { apply good_tm_eta_update; auto. split; auto. }
      specialize (H0 X HXL (update_fun th X U) (update_fun eta X C) s Hth' Hs').
      unfold open_tm_ty in H0.
      rewrite (tm_ty_fsubst_open_ty t th 0 X U Hth HXtm) in H0.
      rewrite (tm_fsubst_open_tm_ty (tm_ty_fsubst th t) s 0 U Hslc) in H0.
      assert (Hbody : exp_rel T eta [C]
        (open_tm_ty (tm_fsubst s (tm_ty_fsubst th t)) U)).
      { assert (Hopen : exp_rel T (update_fun eta X C)
            [rel_candidate (Ty_FVar X) (update_fun eta X C) []]
            (open_tm_ty (tm_fsubst s (tm_ty_fsubst th t)) U)).
        { apply (proj1 (exp_rel_open T (update_fun eta X C) (Ty_FVar X) _
            HTbody (lc_ty_fvar 0 X))). exact H0. }
        assert (HR : rho_agree 1
          [rel_candidate (Ty_FVar X) (update_fun eta X C) []] [C]).
        { unfold rho_agree. intros [|i] Hi q; [|lia].
          unfold rel_candidate, cand_at, update_fun. simpl.
          rewrite Nat.eqb_refl. tauto. }
        apply (proj1 (exp_rel_rho T 1 (update_fun eta X C)
          [rel_candidate (Ty_FVar X) (update_fun eta X C) []] [C] _
          HTbody HR)) in Hopen.
        assert (HA : forall Y, In Y (fv_ty T) ->
          update_fun eta X C Y = eta Y).
        { intros Y HY. unfold update_fun. destruct (Nat.eqb X Y) eqn:E; auto.
          apply Nat.eqb_eq in E. exfalso. apply HXT. rewrite E. exact HY. }
        apply (proj1 (exp_rel_eta T (update_fun eta X C) eta [C] _ HA)).
        exact Hopen. }
      eapply exp_rel_back.
      * constructor; eauto using value_lc.
      * apply multi_step with
          (y := open_tm_ty (tm_fsubst s (tm_ty_fsubst th t)) U).
        { apply ST_TAppTabs; auto. }
        constructor.
      * exact Hbody.
  - assert (HUlc : locally_closed_ty U) by (apply wf_ty_lc with Delta; auto).
    assert (HsubU : locally_closed_ty (ty_fsubst th U)).
    { eapply lc_ty_fsubst; eauto. }
    specialize (IHHty th eta s Hth Hs).
    pose proof (exp_rel_tapp eta [] T
      (tm_fsubst s (tm_ty_fsubst th t)) (ty_fsubst th U)
      IHHty HsubU (rel_candidate U eta [])) as Happ.
    assert (HTbody : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Hty) as Hall.
      inversion Hall; subst; assumption. }
    apply (proj2 (exp_rel_open T eta U _ HTbody HUlc)). exact Happ.
Qed.

Lemma ty_fsubst_id : forall T,
  ty_fsubst (fun X => Ty_FVar X) T = T.
Proof. induction T; simpl; f_equal; auto. Qed.

Lemma tm_ty_fsubst_id : forall t,
  tm_ty_fsubst (fun X => Ty_FVar X) t = t.
Proof.
  induction t; simpl; rewrite ?IHt, ?IHt1, ?IHt2, ?ty_fsubst_id; reflexivity.
Qed.

Lemma tm_fsubst_id : forall t,
  tm_fsubst (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; f_equal; auto. Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose (th := fun X : atom => Ty_FVar X).
  pose (eta := fun _ : atom => value_candidate).
  pose (s := fun x : atom => tm_fvar x).
  assert (Hth : good_ty_sub th).
  { intro X. unfold th, locally_closed_ty. constructor. }
  assert (Hs : good_tm_sub empty eta s).
  { split.
    - intro x. unfold s, locally_closed_tm. constructor.
    - intros x A Hlook. discriminate. }
  pose proof (fundamental [] empty t T Hty th eta s Hth Hs) as Hr.
  unfold th, s in Hr. rewrite tm_ty_fsubst_id, tm_fsubst_id in Hr.
  exact (exp_rel_SN T eta [] t Hr).
Qed.

End SystemFNormalizationNoneHardTask.
