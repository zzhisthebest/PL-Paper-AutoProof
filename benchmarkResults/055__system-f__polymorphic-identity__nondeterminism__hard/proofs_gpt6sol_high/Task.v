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

(* A binary, may-convergence logical relation.  [bs 0] interprets the
   innermost bound type variable. *)
Definition rel := tm -> tm -> Prop.
Definition bound_env := nat -> rel.
Definition push_rel (R : rel) (bs : bound_env) : bound_env :=
  fun i => match i with 0 => R | S j => bs j end.
Definition replace_rel (k : nat) (R : rel) (bs : bound_env) : bound_env :=
  fun i => if Nat.eqb k i then R else bs i.

Fixpoint vrel (T : ty) (bs : bound_env) (eta : atom -> rel)
    (v1 v2 : tm) : Prop :=
  value v1 /\ value v2 /\
  match T with
  | Ty_BVar i => bs i v1 v2
  | Ty_FVar X => eta X v1 v2
  | Ty_Arrow A B =>
      forall w1 w2, vrel A bs eta w1 w2 ->
        exists z1 z2,
          tm_app v1 w1 -->* z1 /\ tm_app v2 w2 -->* z2 /\
          vrel B bs eta z1 z2
  | Ty_All A =>
      forall U1 U2 (R : rel),
        locally_closed_ty U1 -> locally_closed_ty U2 ->
        (forall a b, R a b -> value a /\ value b) ->
        exists z1 z2,
          tm_tapp v1 U1 -->* z1 /\ tm_tapp v2 U2 -->* z2 /\
          vrel A (push_rel R bs) eta z1 z2
  end.

Definition erel (T : ty) (bs : bound_env) (eta : atom -> rel)
    (t1 t2 : tm) : Prop :=
  exists v1 v2, t1 -->* v1 /\ t2 -->* v2 /\ vrel T bs eta v1 v2.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T ->
  forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H; induction H; intros K' Hle.
  - constructor; lia.
  - constructor.
  - constructor; eauto.
  - constructor. apply IHlc_ty_at. lia.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H; induction H; intros K' k' HK Hk.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_weaken; eauto.
    + apply IHlc_tm_at; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
  - apply lc_tm_tapp; eauto using lc_ty_weaken.
  - apply lc_tm_choice; eauto.
Qed.

Lemma lc_ty_open_inv : forall T K U,
  lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  induction T; intros K U H; simpl in H.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor. apply IHT with (U := U). exact H2.
Qed.

Lemma lc_tm_open_inv : forall t K k u,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inv : forall t K k U,
  lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k U H; simpl in H.
  - inversion H; subst; constructor; assumption.
  - constructor.
  - inversion H; subst; constructor.
    + eapply lc_ty_open_inv; eauto.
    + eapply IHt; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto using lc_ty_open_inv.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma in_max_bound : forall L x, In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [<- | H]; [lia|]. specialize (IH _ H). lia.
Qed.

Lemma fresh_atom : forall L, ~ In (S (fold_right Nat.max 0 L)) L.
Proof.
  intros L H. pose proof (in_max_bound L _ H). lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    pose (X := S (fold_right Nat.max 0 L)).
    assert (HF : ~ In X L) by (unfold X; apply fresh_atom).
    eapply lc_ty_open_inv. exact (H0 X HF).
Qed.

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply wf_ty_lc; eassumption.
    + pose (x := S (fold_right Nat.max 0 L)).
      assert (HF : ~ In x L) by (unfold x; apply fresh_atom).
      eapply lc_tm_open_inv. exact (H1 x HF).
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    pose (X := S (fold_right Nat.max 0 L)).
    assert (HF : ~ In X L) by (unfold X; apply fresh_atom).
    eapply lc_tm_ty_open_inv. exact (H0 X HF).
  - apply lc_tm_tapp.
    + exact IHhas_type.
    + eapply wf_ty_lc; eassumption.
  - apply lc_tm_choice; assumption.
Qed.

Fixpoint inst_ty (rho : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => rho X
  | Ty_Arrow A B => Ty_Arrow (inst_ty rho A) (inst_ty rho B)
  | Ty_All A => Ty_All (inst_ty rho A)
  end.

Fixpoint inst_tm (rho : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t => tm_abs (inst_ty rho T) (inst_tm rho sigma t)
  | tm_app a b => tm_app (inst_tm rho sigma a) (inst_tm rho sigma b)
  | tm_tabs t => tm_tabs (inst_tm rho sigma t)
  | tm_tapp t T => tm_tapp (inst_tm rho sigma t) (inst_ty rho T)
  | tm_choice a b => tm_choice (inst_tm rho sigma a) (inst_tm rho sigma b)
  end.

Definition put_ty (rho : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else rho Y.
Definition put_tm (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.
Definition put_rel (eta : atom -> rel) (X : atom) (R : rel) : atom -> rel :=
  fun Y => if Nat.eqb X Y then R else eta Y.

Fixpoint ftv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ftv_ty A ++ ftv_ty B
  | Ty_All A => ftv_ty A
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t | tm_tabs t => fv_tm t
  | tm_app a b | tm_choice a b => fv_tm a ++ fv_tm b
  | tm_tapp t _ => fv_tm t
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t => ftv_ty T ++ ftv_tm t
  | tm_app a b | tm_choice a b => ftv_tm a ++ ftv_tm b
  | tm_tabs t => ftv_tm t
  | tm_tapp t T => ftv_tm t ++ ftv_ty T
  end.

Definition dom_context (Gamma : context) : list atom := map fst Gamma.
Definition ftv_context (Gamma : context) : list atom :=
  flat_map (fun p => ftv_ty (snd p)) Gamma.

Lemma inst_ty_lc : forall T K rho,
  lc_ty_at K T -> (forall X, locally_closed_ty (rho X)) ->
  lc_ty_at K (inst_ty rho T).
Proof.
  intros T K rho H; induction H; intros HR; simpl.
  - constructor; assumption.
  - eapply lc_ty_weaken; [apply HR|lia].
  - constructor; auto.
  - constructor. apply IHlc_ty_at; assumption.
Qed.

Lemma inst_tm_lc : forall t K k rho sigma,
  lc_tm_at K k t ->
  (forall X, locally_closed_ty (rho X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (inst_tm rho sigma t).
Proof.
  intros t K k rho sigma H; induction H; intros HR HS; simpl.
  - constructor; assumption.
  - eapply lc_tm_weaken; [apply HS|lia|lia].
  - constructor; eauto using inst_ty_lc.
  - constructor; auto.
  - constructor; auto.
  - constructor; eauto using inst_ty_lc.
  - constructor; auto.
Qed.

Lemma put_ty_lc : forall rho X U,
  (forall Y, locally_closed_ty (rho Y)) -> locally_closed_ty U ->
  forall Y, locally_closed_ty (put_ty rho X U Y).
Proof.
  intros rho X U HR HU Y; unfold put_ty.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma put_tm_lc : forall sigma x v,
  (forall y, locally_closed_tm (sigma y)) -> locally_closed_tm v ->
  forall y, locally_closed_tm (put_tm sigma x v y).
Proof.
  intros sigma x v HS HV y; unfold put_tm.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma open_ty_rec_lc : forall T K U,
  lc_ty_at K T -> open_ty_rec K U T = T.
Proof.
  intros T K U H; induction H; simpl.
  - destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - now rewrite IHlc_ty_at1, IHlc_ty_at2.
  - now rewrite IHlc_ty_at.
Qed.

Lemma open_tm_rec_lc : forall t K k u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros t K k u H; induction H; simpl.
  - destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - now rewrite IHlc_tm_at.
  - now rewrite IHlc_tm_at1, IHlc_tm_at2.
  - now rewrite IHlc_tm_at.
  - now rewrite IHlc_tm_at.
  - now rewrite IHlc_tm_at1, IHlc_tm_at2.
Qed.

Lemma open_tm_ty_rec_lc : forall t K k U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  intros t K k U H; induction H; simpl; try reflexivity.
  - now rewrite (open_ty_rec_lc _ _ _ H), IHlc_tm_at.
  - now rewrite IHlc_tm_at1, IHlc_tm_at2.
  - now rewrite IHlc_tm_at.
  - now rewrite IHlc_tm_at, (open_ty_rec_lc _ _ _ H0).
  - now rewrite IHlc_tm_at1, IHlc_tm_at2.
Qed.

Lemma inst_ty_open_rec : forall T k U rho,
  (forall X, locally_closed_ty (rho X)) ->
  inst_ty rho (open_ty_rec k U T) =
  open_ty_rec k (inst_ty rho U) (inst_ty rho T).
Proof.
  induction T; intros k U rho HR; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_ty_rec_lc.
    eapply lc_ty_weaken; [apply HR|lia].
  - now rewrite IHT1, IHT2 by assumption.
  - now rewrite IHT by assumption.
Qed.

Lemma inst_tm_open_rec : forall t k u rho sigma,
  (forall x, locally_closed_tm (sigma x)) ->
  inst_tm rho sigma (open_tm_rec k u t) =
  open_tm_rec k (inst_tm rho sigma u) (inst_tm rho sigma t).
Proof.
  induction t; intros k u rho sigma HS; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_tm_rec_lc with (K := 0).
    eapply lc_tm_weaken; [apply HS|lia|lia].
  - now rewrite IHt by assumption.
  - now rewrite IHt1, IHt2 by assumption.
  - now rewrite IHt by assumption.
  - now rewrite IHt by assumption.
  - now rewrite IHt1, IHt2 by assumption.
Qed.

Lemma inst_tm_ty_open_rec : forall t K U rho sigma,
  (forall X, locally_closed_ty (rho X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  inst_tm rho sigma (open_tm_ty_rec K U t) =
  open_tm_ty_rec K (inst_ty rho U) (inst_tm rho sigma t).
Proof.
  induction t; intros K U rho sigma HR HS; simpl; try reflexivity.
  - symmetry. apply open_tm_ty_rec_lc with (k := 0).
    eapply lc_tm_weaken; [apply HS|lia|lia].
  - now rewrite inst_ty_open_rec, IHt by assumption.
  - now rewrite IHt1, IHt2 by assumption.
  - now rewrite IHt by assumption.
  - now rewrite IHt, inst_ty_open_rec by assumption.
  - now rewrite IHt1, IHt2 by assumption.
Qed.

Lemma inst_ty_put_fresh : forall T rho X U,
  ~ In X (ftv_ty T) -> inst_ty (put_ty rho X U) T = inst_ty rho T.
Proof.
  induction T; intros rho X U H; simpl in *; auto.
  - unfold put_ty. destruct (Nat.eqb X a) eqn:E; auto.
    apply Nat.eqb_eq in E; subst; contradiction H; auto.
  - rewrite IHT1, IHT2; auto; intro C; apply H; apply in_or_app; auto.
  - rewrite IHT; auto.
Qed.

Lemma inst_tm_put_fresh : forall t rho sigma x v,
  ~ In x (fv_tm t) ->
  inst_tm rho (put_tm sigma x v) t = inst_tm rho sigma t.
Proof.
  induction t; intros rho sigma x v H; simpl in *; auto.
  - unfold put_tm. destruct (Nat.eqb x a) eqn:E; auto.
    apply Nat.eqb_eq in E; subst; contradiction H; auto.
  - now rewrite IHt by assumption.
  - rewrite IHt1, IHt2; auto; intro C; apply H; apply in_or_app; auto.
  - now rewrite IHt by assumption.
  - now rewrite IHt by assumption.
  - rewrite IHt1, IHt2; auto; intro C; apply H; apply in_or_app; auto.
Qed.

Lemma inst_tm_ty_put_fresh : forall t rho sigma X U,
  ~ In X (ftv_tm t) ->
  inst_tm (put_ty rho X U) sigma t = inst_tm rho sigma t.
Proof.
  induction t; intros rho sigma X U H; simpl in *; auto.
  - rewrite inst_ty_put_fresh, IHt; auto;
      intro C; apply H; apply in_or_app; auto.
  - rewrite IHt1, IHt2; auto; intro C; apply H; apply in_or_app; auto.
  - now rewrite IHt by assumption.
  - rewrite IHt, inst_ty_put_fresh; auto;
      intro C; apply H; apply in_or_app; auto.
  - rewrite IHt1, IHt2; auto; intro C; apply H; apply in_or_app; auto.
Qed.

Lemma inst_tm_open_fresh : forall t rho sigma x v,
  ~ In x (fv_tm t) ->
  (forall y, locally_closed_tm (sigma y)) -> locally_closed_tm v ->
  inst_tm rho (put_tm sigma x v) (open_tm t (tm_fvar x)) =
  open_tm (inst_tm rho sigma t) v.
Proof.
  intros t rho sigma x v HF HS HV.
  unfold open_tm. rewrite inst_tm_open_rec by
    (eapply put_tm_lc; eauto).
  simpl. rewrite inst_tm_put_fresh by assumption.
  unfold put_tm. now rewrite Nat.eqb_refl.
Qed.

Lemma inst_ty_open_fresh : forall T rho X U,
  ~ In X (ftv_ty T) ->
  (forall Y, locally_closed_ty (rho Y)) -> locally_closed_ty U ->
  inst_ty (put_ty rho X U) (open_ty T (Ty_FVar X)) =
  open_ty (inst_ty rho T) U.
Proof.
  intros T rho X U HF HR HU.
  unfold open_ty. rewrite inst_ty_open_rec by
    (eapply put_ty_lc; eauto).
  simpl. rewrite inst_ty_put_fresh by assumption.
  unfold put_ty. now rewrite Nat.eqb_refl.
Qed.

Lemma inst_tm_ty_open_fresh : forall t rho sigma X U,
  ~ In X (ftv_tm t) ->
  (forall Y, locally_closed_ty (rho Y)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  locally_closed_ty U ->
  inst_tm (put_ty rho X U) sigma
    (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (inst_tm rho sigma t) U.
Proof.
  intros t rho sigma X U HF HR HS HU.
  unfold open_tm_ty. rewrite inst_tm_ty_open_rec by
    (auto using put_ty_lc).
  simpl. rewrite inst_tm_ty_put_fresh by assumption.
  unfold put_ty. now rewrite Nat.eqb_refl.
Qed.

Lemma vrel_scoped_congr : forall K T,
  lc_ty_at K T ->
  forall bs bs' eta eta' v1 v2,
    (forall i a b, i < K -> bs i a b <-> bs' i a b) ->
    (forall X a b, eta X a b <-> eta' X a b) ->
    (vrel T bs eta v1 v2 <-> vrel T bs' eta' v1 v2).
Proof.
  intros K T H; induction H; intros bs bs' eta eta' v1 v2 HB HE; simpl.
  - split; intros [V1 [V2 R]]; repeat split; auto;
      apply (HB i); assumption.
  - split; intros [V1 [V2 R]]; repeat split; auto;
      apply (HE X); assumption.
  - split; intros [V1 [V2 F]]; repeat split; auto;
      intros w1 w2 RW.
    + apply (proj2 (IHlc_ty_at1 _ _ _ _ _ _ HB HE)) in RW.
      destruct (F _ _ RW) as [z1 [z2 [P [Q R]]]].
      exists z1, z2; repeat split; auto.
      apply (proj1 (IHlc_ty_at2 _ _ _ _ _ _ HB HE)); assumption.
    + apply (proj1 (IHlc_ty_at1 _ _ _ _ _ _ HB HE)) in RW.
      destruct (F _ _ RW) as [z1 [z2 [P [Q R]]]].
      exists z1, z2; repeat split; auto.
      apply (proj2 (IHlc_ty_at2 _ _ _ _ _ _ HB HE)); assumption.
  - split; intros [V1 [V2 F]]; repeat split; auto;
      intros U1 U2 R HU1 HU2 HG;
      destruct (F U1 U2 R HU1 HU2 HG) as [z1 [z2 [P [Q RR]]]];
      exists z1, z2; repeat split; auto.
    + assert (HP : forall i a b, i < S k ->
          push_rel R bs i a b <-> push_rel R bs' i a b).
      { intros [|i] a b Hi; simpl; [tauto|apply HB; lia]. }
      apply (proj1 (IHlc_ty_at (push_rel R bs) (push_rel R bs')
        eta eta' z1 z2 HP HE)); exact RR.
    + assert (HP : forall i a b, i < S k ->
          push_rel R bs i a b <-> push_rel R bs' i a b).
      { intros [|i] a b Hi; simpl; [tauto|apply HB; lia]. }
      apply (proj2 (IHlc_ty_at (push_rel R bs) (push_rel R bs')
        eta eta' z1 z2 HP HE)); exact RR.
Qed.

Lemma vrel_closed_stack : forall T bs bs' eta v1 v2,
  locally_closed_ty T ->
  (vrel T bs eta v1 v2 <-> vrel T bs' eta v1 v2).
Proof.
  intros T bs bs' eta v1 v2 H.
  eapply vrel_scoped_congr; eauto.
  - intros i a b Hi; lia.
  - intros; tauto.
Qed.

Lemma vrel_eta_fresh : forall T bs eta X R v1 v2,
  ~ In X (ftv_ty T) ->
  (vrel T bs (put_rel eta X R) v1 v2 <-> vrel T bs eta v1 v2).
Proof.
  induction T; intros bs eta X R v1 v2 HF; simpl in *.
  - tauto.
  - unfold put_rel. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst; contradiction HF; auto.
    + tauto.
  - split; intros [V1 [V2 F]]; repeat split; auto;
      intros w1 w2 RW.
    + assert (HA : ~ In X (ftv_ty T1)) by
        (intro C; apply HF; apply in_or_app; auto).
      assert (HB : ~ In X (ftv_ty T2)) by
        (intro C; apply HF; apply in_or_app; auto).
      apply (proj2 (IHT1 bs eta X R w1 w2 HA)) in RW.
      destruct (F _ _ RW) as [z1 [z2 [P [Q RR]]]].
      exists z1, z2; repeat split; auto.
      apply (proj1 (IHT2 bs eta X R z1 z2 HB)); exact RR.
    + assert (HA : ~ In X (ftv_ty T1)) by
        (intro C; apply HF; apply in_or_app; auto).
      assert (HB : ~ In X (ftv_ty T2)) by
        (intro C; apply HF; apply in_or_app; auto).
      apply (proj1 (IHT1 bs eta X R w1 w2 HA)) in RW.
      destruct (F _ _ RW) as [z1 [z2 [P [Q RR]]]].
      exists z1, z2; repeat split; auto.
      apply (proj2 (IHT2 bs eta X R z1 z2 HB)); exact RR.
  - split; intros [V1 [V2 F]]; repeat split; auto;
      intros U1 U2 S HU1 HU2 HG;
      destruct (F U1 U2 S HU1 HU2 HG) as [z1 [z2 [P [Q RR]]]];
      exists z1, z2; repeat split; auto.
    + apply (proj1 (IHT (push_rel S bs) eta X R z1 z2 HF)); exact RR.
    + apply (proj2 (IHT (push_rel S bs) eta X R z1 z2 HF)); exact RR.
Qed.

Fixpoint max_bvar (T : ty) : nat :=
  match T with
  | Ty_BVar i => S i
  | Ty_FVar _ => 0
  | Ty_Arrow A B => Nat.max (max_bvar A) (max_bvar B)
  | Ty_All A => max_bvar A
  end.

Lemma lc_ty_large : forall T, lc_ty_at (S (max_bvar T)) T.
Proof.
  induction T; simpl.
  - constructor; lia.
  - constructor.
  - constructor; eapply lc_ty_weaken; eauto; lia.
  - constructor. eapply lc_ty_weaken; eauto; lia.
Qed.

Lemma vrel_env_congr : forall T bs bs' eta eta' v1 v2,
  (forall i a b, bs i a b <-> bs' i a b) ->
  (forall X a b, eta X a b <-> eta' X a b) ->
  (vrel T bs eta v1 v2 <-> vrel T bs' eta' v1 v2).
Proof.
  intros T bs bs' eta eta' v1 v2 HB HE.
  eapply vrel_scoped_congr; eauto using lc_ty_large.
Qed.

Lemma replace_push_pointwise : forall k R Q bs i,
  replace_rel (S k) R (push_rel Q bs) i =
  push_rel Q (replace_rel k R bs) i.
Proof.
  intros k R Q bs [|i]; reflexivity.
Qed.

Lemma vrel_replace_push : forall T k R Q bs eta v1 v2,
  vrel T (replace_rel (S k) R (push_rel Q bs)) eta v1 v2 <->
  vrel T (push_rel Q (replace_rel k R bs)) eta v1 v2.
Proof.
  intros. apply vrel_env_congr.
  - intros i a b. rewrite replace_push_pointwise. tauto.
  - intros; tauto.
Qed.

Lemma vrel_values : forall T bs eta v1 v2,
  vrel T bs eta v1 v2 -> value v1 /\ value v2.
Proof.
  intros T bs eta v1 v2 H; destruct T; simpl in H; tauto.
Qed.

Lemma vrel_open_rec : forall T k U bs eta R v1 v2,
  locally_closed_ty U ->
  (forall a b, R a b <-> vrel U bs eta a b) ->
  (vrel (open_ty_rec k U T) bs eta v1 v2 <->
   vrel T (replace_rel k R bs) eta v1 v2).
Proof.
  induction T; intros k U bs eta R v1 v2 HU HR; simpl.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold replace_rel. rewrite E. split.
      * intro H. destruct (vrel_values _ _ _ _ _ H) as [V1 V2].
        repeat split; auto. apply (proj2 (HR _ _)); exact H.
      * intros [_ [_ H]]. apply (proj1 (HR _ _)); exact H.
    + unfold replace_rel. rewrite E. tauto.
  - tauto.
  - split; intros [V1 [V2 F]]; repeat split; auto;
      intros w1 w2 RW.
    + apply (proj2 (IHT1 k U bs eta R w1 w2 HU HR)) in RW.
      destruct (F _ _ RW) as [z1 [z2 [P [Q RR]]]].
      exists z1, z2; repeat split; auto.
      apply (proj1 (IHT2 k U bs eta R z1 z2 HU HR)); exact RR.
    + apply (proj1 (IHT1 k U bs eta R w1 w2 HU HR)) in RW.
      destruct (F _ _ RW) as [z1 [z2 [P [Q RR]]]].
      exists z1, z2; repeat split; auto.
      apply (proj2 (IHT2 k U bs eta R z1 z2 HU HR)); exact RR.
  - split; intros [V1 [V2 F]]; repeat split; auto;
      intros U1 U2 Q0 HU1 HU2 HG;
      destruct (F U1 U2 Q0 HU1 HU2 HG) as [z1 [z2 [P [Q RR]]]];
      exists z1, z2; repeat split; auto.
    + assert (HR' : forall a b, R a b <->
          vrel U (push_rel Q0 bs) eta a b).
      { intros a b. transitivity (vrel U bs eta a b).
        - apply HR.
        - apply vrel_closed_stack; exact HU. }
      apply (proj1 (vrel_replace_push T k R Q0 bs eta z1 z2)).
      apply (proj1 (IHT (S k) U (push_rel Q0 bs) eta R z1 z2 HU HR')).
      exact RR.
    + assert (HR' : forall a b, R a b <->
          vrel U (push_rel Q0 bs) eta a b).
      { intros a b. transitivity (vrel U bs eta a b).
        - apply HR.
        - apply vrel_closed_stack; exact HU. }
      apply (proj2 (IHT (S k) U (push_rel Q0 bs) eta R z1 z2 HU HR')).
      apply (proj2 (vrel_replace_push T k R Q0 bs eta z1 z2)).
      exact RR.
Qed.

Definition empty_bound : bound_env := fun _ _ _ => False.

Lemma vrel_open0 : forall T U eta R v1 v2,
  locally_closed_ty U ->
  (forall a b, R a b <-> vrel U empty_bound eta a b) ->
  (vrel (open_ty T U) empty_bound eta v1 v2 <->
   vrel T (push_rel R empty_bound) eta v1 v2).
Proof.
  intros T U eta R v1 v2 HU HR.
  unfold open_ty.
  transitivity (vrel T (replace_rel 0 R empty_bound) eta v1 v2).
  - apply vrel_open_rec; assumption.
  - apply vrel_env_congr.
    + intros [|i] a b; unfold replace_rel, push_rel, empty_bound;
        simpl; try rewrite Nat.eqb_refl; tauto.
    + intros; tauto.
Qed.

Lemma vrel_open_fresh : forall T eta X R v1 v2,
  ~ In X (ftv_ty T) ->
  (forall a b, R a b -> value a /\ value b) ->
  (vrel (open_ty T (Ty_FVar X)) empty_bound
      (put_rel eta X R) v1 v2 <->
   vrel T (push_rel R empty_bound) eta v1 v2).
Proof.
  intros T eta X R v1 v2 HF HG.
  transitivity (vrel T (push_rel R empty_bound)
    (put_rel eta X R) v1 v2).
  - apply vrel_open0.
    + constructor.
    + intros a b; simpl. unfold put_rel. rewrite Nat.eqb_refl.
      split.
      * intro H. destruct (HG _ _ H); repeat split; assumption.
      * intros [_ [_ H]]; exact H.
  - apply vrel_eta_fresh; exact HF.
Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H; induction H; intros Hbc; eauto using multi.
Qed.

Lemma multi_app1 : forall t u s,
  t -->* u -> locally_closed_tm s ->
  tm_app t s -->* tm_app u s.
Proof.
  intros t u s H; induction H; intros HS; eauto using multi, step.
Qed.

Lemma multi_app2 : forall v t u,
  value v -> t -->* u -> tm_app v t -->* tm_app v u.
Proof.
  intros v t u HV H; induction H; eauto using multi, step.
Qed.

Lemma multi_tapp : forall t u U,
  t -->* u -> locally_closed_ty U ->
  tm_tapp t U -->* tm_tapp u U.
Proof.
  intros t u U H; induction H; intros HU; eauto using multi, step.
Qed.

Lemma erel_pre : forall T eta t1 t2 s1 s2,
  t1 -->* s1 -> t2 -->* s2 ->
  erel T empty_bound eta s1 s2 ->
  erel T empty_bound eta t1 t2.
Proof.
  intros T eta t1 t2 s1 s2 P Q [v1 [v2 [A [B R]]]].
  exists v1, v2; repeat split; eauto using multi_trans.
Qed.

Definition sem_context (Gamma : context) (eta : atom -> rel)
    (sigma1 sigma2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    vrel T empty_bound eta (sigma1 x) (sigma2 x).

Lemma sem_context_put : forall Gamma eta sigma1 sigma2 x T w1 w2,
  sem_context Gamma eta sigma1 sigma2 ->
  vrel T empty_bound eta w1 w2 ->
  sem_context (update Gamma x T) eta
    (put_tm sigma1 x w1) (put_tm sigma2 x w2).
Proof.
  intros Gamma eta sigma1 sigma2 x T w1 w2 HC HW y S HL.
  simpl in HL. unfold put_tm.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst.
    rewrite Nat.eqb_refl in HL. inversion HL; subst; exact HW.
  - rewrite Nat.eqb_sym in HL. rewrite E in HL.
    apply HC; exact HL.
Qed.

Lemma lookup_ftv_context : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (ftv_ty T) ->
  In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros x T X HL HF;
    simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion HL; subst. apply in_or_app; auto.
  - apply in_or_app; right. eapply IH; eauto.
Qed.

Lemma sem_context_eta_put : forall Gamma eta sigma1 sigma2 X R,
  ~ In X (ftv_context Gamma) ->
  sem_context Gamma eta sigma1 sigma2 ->
  sem_context Gamma (put_rel eta X R) sigma1 sigma2.
Proof.
  intros Gamma eta sigma1 sigma2 X R HF HC x T HL.
  assert (HT : ~ In X (ftv_ty T)).
  { intro C. apply HF. eapply lookup_ftv_context; eauto. }
  apply (proj2 (vrel_eta_fresh T empty_bound eta X R
    (sigma1 x) (sigma2 x) HT)).
  apply HC; exact HL.
Qed.

Lemma erel_app : forall A B eta f1 f2 a1 a2,
  erel (Ty_Arrow A B) empty_bound eta f1 f2 ->
  erel A empty_bound eta a1 a2 ->
  locally_closed_tm a1 -> locally_closed_tm a2 ->
  erel B empty_bound eta (tm_app f1 a1) (tm_app f2 a2).
Proof.
  intros A B eta f1 f2 a1 a2
    [g1 [g2 [P1 [P2 [V1 [V2 F]]]]]]
    [w1 [w2 [Q1 [Q2 RW]]]] HC1 HC2.
  destruct (F _ _ RW) as [z1 [z2 [S1 [S2 RZ]]]].
  exists z1, z2; repeat split; auto.
  - eapply multi_trans. apply multi_app1; eauto.
    eapply multi_trans. apply multi_app2; eauto.
    exact S1.
  - eapply multi_trans. apply multi_app1; eauto.
    eapply multi_trans. apply multi_app2; eauto.
    exact S2.
Qed.

Lemma erel_choice_left : forall T eta a1 a2 b1 b2,
  erel T empty_bound eta a1 b1 ->
  locally_closed_tm a1 -> locally_closed_tm a2 ->
  locally_closed_tm b1 -> locally_closed_tm b2 ->
  erel T empty_bound eta (tm_choice a1 a2) (tm_choice b1 b2).
Proof.
  intros T eta a1 a2 b1 b2 HR HA1 HA2 HB1 HB2.
  eapply erel_pre; [| |exact HR].
  - eapply multi_step; [apply ST_ChoiceLeft; eauto|constructor].
  - eapply multi_step; [apply ST_ChoiceLeft; eauto|constructor].
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; assumption.
Qed.

Lemma inst_typing_lc : forall Delta Gamma t T rho sigma,
  has_type Delta Gamma t T ->
  (forall X, locally_closed_ty (rho X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  locally_closed_tm (inst_tm rho sigma t).
Proof.
  intros. eapply inst_tm_lc; eauto.
  eapply typing_lc; eassumption.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho1 rho2 sigma1 sigma2 eta,
    (forall X, locally_closed_ty (rho1 X)) ->
    (forall X, locally_closed_ty (rho2 X)) ->
    (forall x, locally_closed_tm (sigma1 x)) ->
    (forall x, locally_closed_tm (sigma2 x)) ->
    sem_context Gamma eta sigma1 sigma2 ->
    erel T empty_bound eta
      (inst_tm rho1 sigma1 t) (inst_tm rho2 sigma2 t).
Proof.
  intros Delta Gamma t T HT.
  induction HT as
    [Delta Gamma x T HL HW
    | L Delta Gamma T1 t2 T2 HW HB IHB
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T HB IHB
    | Delta Gamma t T U Ht IH HW
    | Delta Gamma t1 t2 T H1 IH1 H2 IH2];
    intros rho1 rho2 sigma1 sigma2 eta HR1 HR2 HS1 HS2 HC; simpl.
  - exists (sigma1 x), (sigma2 x).
    split; [constructor|]. split; [constructor|].
    apply HC; exact HL.
  - assert (HTabs : has_type Delta Gamma (tm_abs T1 t2)
        (Ty_Arrow T1 T2)).
    { eapply T_Abs with (L := L); eauto. }
    assert (VA1 : value (tm_abs (inst_ty rho1 T1)
        (inst_tm rho1 sigma1 t2))).
    { apply v_abs. change (locally_closed_tm
        (inst_tm rho1 sigma1 (tm_abs T1 t2))).
      eapply inst_typing_lc; eauto. }
    assert (VA2 : value (tm_abs (inst_ty rho2 T1)
        (inst_tm rho2 sigma2 t2))).
    { apply v_abs. change (locally_closed_tm
        (inst_tm rho2 sigma2 (tm_abs T1 t2))).
      eapply inst_typing_lc; eauto. }
    exists (tm_abs (inst_ty rho1 T1) (inst_tm rho1 sigma1 t2)),
      (tm_abs (inst_ty rho2 T1) (inst_tm rho2 sigma2 t2)).
    split; [constructor|]. split; [constructor|].
    simpl; split; [exact VA1|]. split; [exact VA2|].
    intros w1 w2 RW.
    destruct (vrel_values _ _ _ _ _ RW) as [VW1 VW2].
    pose (x := S (fold_right Nat.max 0 (L ++ fv_tm t2))).
    assert (HF : ~ In x (L ++ fv_tm t2)) by
      (unfold x; apply fresh_atom).
    assert (HXL : ~ In x L) by
      (intro C; apply HF; apply in_or_app; auto).
    assert (HXT : ~ In x (fv_tm t2)) by
      (intro C; apply HF; apply in_or_app; auto).
    assert (HS1' : forall y, locally_closed_tm
        (put_tm sigma1 x w1 y)) by
      (eapply put_tm_lc; eauto using value_lc).
    assert (HS2' : forall y, locally_closed_tm
        (put_tm sigma2 x w2 y)) by
      (eapply put_tm_lc; eauto using value_lc).
    pose proof (IHB x HXL rho1 rho2
      (put_tm sigma1 x w1) (put_tm sigma2 x w2) eta
      HR1 HR2 HS1' HS2'
      (sem_context_put _ _ _ _ _ _ _ _ HC RW)) as HE.
    rewrite (inst_tm_open_fresh t2 rho1 sigma1 x w1 HXT HS1
      (value_lc _ VW1)) in HE.
    rewrite (inst_tm_open_fresh t2 rho2 sigma2 x w2 HXT HS2
      (value_lc _ VW2)) in HE.
    destruct HE as [z1 [z2 [P [Q RZ]]]].
    exists z1, z2; repeat split; auto.
    + eapply multi_step; [apply ST_AppAbs; eauto using value_lc|exact P].
    + eapply multi_step; [apply ST_AppAbs; eauto using value_lc|exact Q].
  - eapply erel_app; eauto using inst_typing_lc.
  - assert (HTtabs : has_type Delta Gamma (tm_tabs t) (Ty_All T)).
    { eapply T_TAbs with (L := L); eauto. }
    assert (VT1 : value (tm_tabs (inst_tm rho1 sigma1 t))).
    { apply v_tabs. change (locally_closed_tm
        (inst_tm rho1 sigma1 (tm_tabs t))).
      eapply inst_typing_lc; eauto. }
    assert (VT2 : value (tm_tabs (inst_tm rho2 sigma2 t))).
    { apply v_tabs. change (locally_closed_tm
        (inst_tm rho2 sigma2 (tm_tabs t))).
      eapply inst_typing_lc; eauto. }
    exists (tm_tabs (inst_tm rho1 sigma1 t)),
      (tm_tabs (inst_tm rho2 sigma2 t)).
    split; [constructor|]. split; [constructor|].
    simpl; split; [exact VT1|]. split; [exact VT2|].
    intros U1 U2 R HU1 HU2 HG.
    pose (X := S (fold_right Nat.max 0
      (L ++ ftv_tm t ++ ftv_ty T ++ ftv_context Gamma))).
    assert (HF : ~ In X
      (L ++ ftv_tm t ++ ftv_ty T ++ ftv_context Gamma)) by
      (unfold X; apply fresh_atom).
    assert (HXL : ~ In X L) by
      (intro C; apply HF; apply in_or_app; auto).
    assert (HXT : ~ In X (ftv_tm t)) by
      (intro C; apply HF; apply in_or_app; right;
       apply in_or_app; auto).
    assert (HXF : ~ In X (ftv_ty T)) by
      (intro C; apply HF; apply in_or_app; right;
       apply in_or_app; right; apply in_or_app; auto).
    assert (HXG : ~ In X (ftv_context Gamma)) by
      (intro C; apply HF; apply in_or_app; right;
       apply in_or_app; right; apply in_or_app; auto).
    pose proof (IHB X HXL
      (put_ty rho1 X U1) (put_ty rho2 X U2)
      sigma1 sigma2 (put_rel eta X R)
      (put_ty_lc _ _ _ HR1 HU1)
      (put_ty_lc _ _ _ HR2 HU2)
      HS1 HS2
      (sem_context_eta_put _ _ _ _ _ _ HXG HC)) as HE.
    rewrite (inst_tm_ty_open_fresh t rho1 sigma1 X U1
      HXT HR1 HS1 HU1) in HE.
    rewrite (inst_tm_ty_open_fresh t rho2 sigma2 X U2
      HXT HR2 HS2 HU2) in HE.
    destruct HE as [z1 [z2 [P [Q RZ]]]].
    exists z1, z2; repeat split.
    + eapply multi_step; [apply ST_TAppTabs; eauto using value_lc|exact P].
    + eapply multi_step; [apply ST_TAppTabs; eauto using value_lc|exact Q].
    + apply (proj1 (vrel_open_fresh T eta X R z1 z2 HXF HG));
        exact RZ.
  - destruct (IH rho1 rho2 sigma1 sigma2 eta
      HR1 HR2 HS1 HS2 HC) as
      [f1 [f2 [P [Q [VF1 [VF2 F]]]]]].
    set (U1 := inst_ty rho1 U).
    set (U2 := inst_ty rho2 U).
    assert (HU : locally_closed_ty U) by
      (eapply wf_ty_lc; eauto).
    assert (HU1 : locally_closed_ty U1) by
      (unfold U1; eapply inst_ty_lc; eauto).
    assert (HU2 : locally_closed_ty U2) by
      (unfold U2; eapply inst_ty_lc; eauto).
    set (R := vrel U empty_bound eta).
    assert (HG : forall a b, R a b -> value a /\ value b) by
      (intros a b H; apply (vrel_values U empty_bound eta a b H)).
    destruct (F U1 U2 R HU1 HU2 HG) as
      [z1 [z2 [S1 [S2 RZ]]]].
    exists z1, z2; repeat split.
    + eapply multi_trans; [apply multi_tapp; eauto|exact S1].
    + eapply multi_trans; [apply multi_tapp; eauto|exact S2].
    + assert (HEq : forall a b,
          R a b <-> vrel U empty_bound eta a b) by
          (intros; tauto).
      apply (proj2 (vrel_open0 T U eta R z1 z2 HU HEq));
        exact RZ.
  - eapply erel_choice_left.
    + apply IH1; assumption.
    + eapply inst_typing_lc; eauto.
    + eapply inst_typing_lc; eauto.
    + eapply inst_typing_lc; eauto.
    + eapply inst_typing_lc; eauto.
Qed.

Lemma ftv_ty_open_contains : forall T k U X,
  In X (ftv_ty T) -> In X (ftv_ty (open_ty_rec k U T)).
Proof.
  induction T; intros k U X H; simpl in *; try contradiction.
  - exact H.
  - apply in_app_or in H. apply in_or_app.
    destruct H as [H|H]; [left|right]; eauto.
  - eauto.
Qed.

Lemma fv_tm_open_contains : forall t k u x,
  In x (fv_tm t) -> In x (fv_tm (open_tm_rec k u t)).
Proof.
  induction t; intros k u x H; simpl in *; try contradiction; auto.
  - apply in_app_or in H. apply in_or_app.
    destruct H as [H|H]; [left|right]; eauto.
  - apply in_app_or in H. apply in_or_app.
    destruct H as [H|H]; [left|right]; eauto.
Qed.

Lemma fv_tm_ty_open : forall t K U,
  fv_tm (open_tm_ty_rec K U t) = fv_tm t.
Proof.
  induction t; intros K U; simpl; auto;
    try rewrite IHt; try rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma ftv_tm_open_contains : forall t k u X,
  In X (ftv_tm t) -> In X (ftv_tm (open_tm_rec k u t)).
Proof.
  induction t; intros k u X H; simpl in *; try contradiction; auto.
  - apply in_app_or in H. apply in_or_app.
    destruct H as [H|H]; [left; exact H|right; eauto].
  - apply in_app_or in H. apply in_or_app.
    destruct H as [H|H]; [left|right]; eauto.
  - apply in_app_or in H. apply in_or_app.
    destruct H as [H|H]; [left; eauto|right; exact H].
  - apply in_app_or in H. apply in_or_app.
    destruct H as [H|H]; [left|right]; eauto.
Qed.

Lemma ftv_tm_ty_open_contains : forall t K U X,
  In X (ftv_tm t) -> In X (ftv_tm (open_tm_ty_rec K U t)).
Proof.
  induction t; intros K U X H; simpl in *; try contradiction; auto.
  - apply in_app_or in H. apply in_or_app.
    destruct H as [H|H].
    + left. eapply ftv_ty_open_contains; eauto.
    + right. eauto.
  - apply in_app_or in H. apply in_or_app.
    destruct H as [H|H]; [left|right]; eauto.
  - apply in_app_or in H. apply in_or_app.
    destruct H as [H|H].
    + left; eauto.
    + right; eapply ftv_ty_open_contains; eauto.
  - apply in_app_or in H. apply in_or_app.
    destruct H as [H|H]; [left|right]; eauto.
Qed.

Lemma lookup_dom : forall Gamma x T,
  lookup_context x Gamma = Some T -> In x (dom_context Gamma).
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros x T H;
    simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - left. apply Nat.eqb_eq in E; symmetry; exact E.
  - right. eapply IH; eauto.
Qed.

Lemma wf_ftv_support : forall Delta T,
  wf_ty Delta T -> forall X, In X (ftv_ty T) -> In X Delta.
Proof.
  intros Delta T H; induction H; intros Y HY; simpl in *.
  - destruct HY as [<-|[]]; assumption.
  - apply in_app_or in HY. destruct HY; eauto.
  - pose (X := S (fold_right Nat.max 0 (L ++ [Y]))).
    assert (HF : ~ In X (L ++ [Y])) by
      (unfold X; apply fresh_atom).
    assert (HXL : ~ In X L) by
      (intro C; apply HF; apply in_or_app; auto).
    assert (HXY : X <> Y) by
      (intro E; apply HF; rewrite E; apply in_or_app; right; simpl; auto).
    pose proof (H0 X HXL Y
      (ftv_ty_open_contains T 0 (Ty_FVar X) Y HY)) as Hsup.
    simpl in Hsup. destruct Hsup as [E|Hsup]; [contradiction|exact Hsup].
Qed.

Lemma typing_fv_support : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall x, In x (fv_tm t) -> In x (dom_context Gamma).
Proof.
  intros Delta Gamma t T H; induction H; intros y HY; simpl in *.
  - destruct HY as [<-|[]]. eapply lookup_dom; eauto.
  - pose (x := S (fold_right Nat.max 0 (L ++ [y]))).
    assert (HF : ~ In x (L ++ [y])) by
      (unfold x; apply fresh_atom).
    assert (HXL : ~ In x L) by
      (intro C; apply HF; apply in_or_app; auto).
    assert (HXY : x <> y) by
      (intro E; apply HF; rewrite E; apply in_or_app; right; simpl; auto).
    pose proof (H1 x HXL y
      (fv_tm_open_contains t2 0 (tm_fvar x) y HY)) as HS.
    simpl in HS. destruct HS as [E|HS]; [contradiction|exact HS].
  - apply in_app_or in HY. destruct HY; eauto.
  - pose (X := S (fold_right Nat.max 0 L)).
    assert (HF : ~ In X L) by (unfold X; apply fresh_atom).
    pose proof (H0 X HF y) as HS.
    unfold open_tm_ty in HS. rewrite fv_tm_ty_open in HS.
    apply HS; exact HY.
  - eauto.
  - apply in_app_or in HY. destruct HY; eauto.
Qed.

Lemma typing_ftv_support : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall X, In X (ftv_tm t) -> In X Delta.
Proof.
  intros Delta Gamma t T H; induction H; intros Y HY; simpl in *;
    try contradiction.
  - apply in_app_or in HY. destruct HY as [HY|HY].
    + eapply wf_ftv_support; eauto.
    + pose (x := S (fold_right Nat.max 0 L)).
      assert (HF : ~ In x L) by (unfold x; apply fresh_atom).
      apply (H1 x HF Y).
      eapply ftv_tm_open_contains; eauto.
  - apply in_app_or in HY. destruct HY; eauto.
  - pose (X := S (fold_right Nat.max 0 (L ++ [Y]))).
    assert (HF : ~ In X (L ++ [Y])) by
      (unfold X; apply fresh_atom).
    assert (HXL : ~ In X L) by
      (intro C; apply HF; apply in_or_app; auto).
    assert (HXY : X <> Y) by
      (intro E; apply HF; rewrite E; apply in_or_app; right; simpl; auto).
    pose proof (H0 X HXL Y
      (ftv_tm_ty_open_contains t 0 (Ty_FVar X) Y HY)) as HS.
    simpl in HS. destruct HS as [E|HS]; [contradiction|exact HS].
  - apply in_app_or in HY. destruct HY as [HY|HY].
    + eauto.
    + eapply wf_ftv_support; eauto.
  - apply in_app_or in HY. destruct HY; eauto.
Qed.

Lemma inst_ty_no_ftv : forall T rho,
  (forall X, In X (ftv_ty T) -> False) -> inst_ty rho T = T.
Proof.
  induction T; intros rho HF; simpl in *; auto.
  - exfalso. apply (HF a); simpl; auto.
  - rewrite IHT1.
    + rewrite IHT2.
      * reflexivity.
      * intros X HX. apply (HF X). apply in_or_app; right; exact HX.
    + intros X HX. apply (HF X). apply in_or_app; left; exact HX.
  - rewrite IHT; auto.
Qed.

Lemma inst_tm_no_free : forall t rho sigma,
  (forall x, In x (fv_tm t) -> False) ->
  (forall X, In X (ftv_tm t) -> False) ->
  inst_tm rho sigma t = t.
Proof.
  induction t; intros rho sigma HF HG; simpl in *; auto.
  - exfalso. apply (HF a); simpl; auto.
  - assert (GT : forall X, In X (ftv_ty t) -> False).
    { intros X HX. apply (HG X). apply in_or_app; left; exact HX. }
    assert (GB : forall X, In X (ftv_tm t0) -> False).
    { intros X HX. apply (HG X). apply in_or_app; right; exact HX. }
    rewrite (inst_ty_no_ftv t rho GT).
    rewrite (IHt rho sigma HF GB). reflexivity.
  - assert (F1 : forall x, In x (fv_tm t1) -> False).
    { intros x HX. apply (HF x). apply in_or_app; left; exact HX. }
    assert (F2 : forall x, In x (fv_tm t2) -> False).
    { intros x HX. apply (HF x). apply in_or_app; right; exact HX. }
    assert (G1 : forall X, In X (ftv_tm t1) -> False).
    { intros X HX. apply (HG X). apply in_or_app; left; exact HX. }
    assert (G2 : forall X, In X (ftv_tm t2) -> False).
    { intros X HX. apply (HG X). apply in_or_app; right; exact HX. }
    rewrite (IHt1 rho sigma F1 G1), (IHt2 rho sigma F2 G2).
    reflexivity.
  - rewrite (IHt rho sigma HF HG). reflexivity.
  - assert (GB : forall X, In X (ftv_tm t) -> False).
    { intros X HX. apply (HG X). apply in_or_app; left; exact HX. }
    assert (GT : forall X, In X (ftv_ty t0) -> False).
    { intros X HX. apply (HG X). apply in_or_app; right; exact HX. }
    rewrite (IHt rho sigma HF GB).
    rewrite (inst_ty_no_ftv t0 rho GT). reflexivity.
  - assert (F1 : forall x, In x (fv_tm t1) -> False).
    { intros x HX. apply (HF x). apply in_or_app; left; exact HX. }
    assert (F2 : forall x, In x (fv_tm t2) -> False).
    { intros x HX. apply (HF x). apply in_or_app; right; exact HX. }
    assert (G1 : forall X, In X (ftv_tm t1) -> False).
    { intros X HX. apply (HG X). apply in_or_app; left; exact HX. }
    assert (G2 : forall X, In X (ftv_tm t2) -> False).
    { intros X HX. apply (HG X). apply in_or_app; right; exact HX. }
    rewrite (IHt1 rho sigma F1 G1), (IHt2 rho sigma F2 G2).
    reflexivity.
Qed.

Definition dummy_ty : ty := Ty_All (Ty_BVar 0).
Definition dummy_tm : tm := tm_abs dummy_ty (tm_bvar 0).

Lemma dummy_ty_lc : locally_closed_ty dummy_ty.
Proof.
  unfold dummy_ty. apply lc_ty_all. apply lc_ty_bvar. lia.
Qed.

Lemma dummy_tm_lc : locally_closed_tm dummy_tm.
Proof.
  unfold dummy_tm. apply lc_tm_abs.
  - apply dummy_ty_lc.
  - apply lc_tm_bvar. lia.
Qed.

Definition singleton_rel (v : tm) : rel :=
  fun a b => a = v /\ b = v.

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t HT U v HU HV _.
  assert (HC : forall rho sigma, inst_tm rho sigma t = t).
  { intros rho sigma. apply inst_tm_no_free.
    - intros x HX. pose proof (typing_fv_support _ _ _ _ HT x HX) as H.
      simpl in H. contradiction.
    - intros X HX. pose proof (typing_ftv_support _ _ _ _ HT X HX) as H.
      contradiction. }
  pose proof (fundamental [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) HT
    (fun _ => dummy_ty) (fun _ => dummy_ty)
    (fun _ => dummy_tm) (fun _ => dummy_tm)
    (fun _ _ _ => False)
    (fun _ => dummy_ty_lc) (fun _ => dummy_ty_lc)
    (fun _ => dummy_tm_lc) (fun _ => dummy_tm_lc)) as HE.
  assert (HSC : sem_context empty (fun _ _ _ => False)
      (fun _ => dummy_tm) (fun _ => dummy_tm)).
  { intros x T H; discriminate. }
  specialize (HE HSC).
  rewrite (HC (fun _ => dummy_ty) (fun _ => dummy_tm)) in HE.
  destruct HE as [f1 [f2 [P [Q [VF1 [VF2 F]]]]]].
  set (R := singleton_rel v).
  assert (HG : forall a b, R a b -> value a /\ value b).
  { intros a b [-> ->]; auto. }
  assert (HULC : locally_closed_ty U) by
    (eapply wf_ty_lc; eauto).
  destruct (F U U R HULC HULC HG) as
    [g1 [g2 [P1 [P2 RG]]]].
  destruct RG as [VG1 [VG2 GA]].
  assert (RV : vrel (Ty_BVar 0)
      (push_rel R empty_bound) (fun _ _ _ => False) v v).
  { simpl. repeat split; auto. }
  destruct (GA v v RV) as [z1 [z2 [Q1 [Q2 RZ]]]].
  simpl in RZ. destruct RZ as [_ [_ [EZ1 EZ2]]].
  subst z1.
  assert (HTapp : tm_tapp t U -->* g1).
  { eapply multi_trans.
    - apply multi_tapp; [exact P|exact HULC].
    - exact P1. }
  eapply multi_trans.
  - apply multi_app1; eauto using value_lc.
  - exact Q1.
Qed.

End SystemFParametricityNondeterminismHardTask.
