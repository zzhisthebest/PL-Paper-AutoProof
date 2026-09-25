(** System F parametricity benchmark, Hard variant.
    Features: none. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNoneHardTask.

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

Fixpoint ty_names (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => [] | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_names A ++ ty_names B
  | Ty_All A => ty_names A
  end.

Fixpoint tm_type_names (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T u => ty_names T ++ tm_type_names u
  | tm_app u w => tm_type_names u ++ tm_type_names w
  | tm_tabs u => tm_type_names u
  | tm_tapp u T => tm_type_names u ++ ty_names T
  end.

Fixpoint tm_names (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_abs _ u | tm_tabs u => tm_names u
  | tm_app u w => tm_names u ++ tm_names w
  | tm_tapp u _ => tm_names u
  end.

Fixpoint close_ty (rho : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar n => Ty_BVar n | Ty_FVar X => rho X
  | Ty_Arrow A B => Ty_Arrow (close_ty rho A) (close_ty rho B)
  | Ty_All A => Ty_All (close_ty rho A)
  end.

Fixpoint close_tm (rho : atom -> ty) (gamma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar n => tm_bvar n | tm_fvar x => gamma x
  | tm_abs T u => tm_abs (close_ty rho T) (close_tm rho gamma u)
  | tm_app u w => tm_app (close_tm rho gamma u) (close_tm rho gamma w)
  | tm_tabs u => tm_tabs (close_tm rho gamma u)
  | tm_tapp u T => tm_tapp (close_tm rho gamma u) (close_ty rho T)
  end.

Definition change {A} (f : atom -> A) (x : atom) (a : A) : atom -> A :=
  fun y => if Nat.eqb x y then a else f y.

Lemma lc_ty_monotone : forall K T, lc_ty_at K T ->
  forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H; induction H; intros K' HK.
  - constructor; lia.
  - constructor.
  - constructor; eauto.
  - constructor; apply IHlc_ty_at; lia.
Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at 0 T -> lc_ty_at K T.
Proof. intros; eapply lc_ty_monotone; eauto; lia. Qed.

Lemma lc_tm_monotone : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H; induction H; intros K' k' HK Hk.
  - constructor; lia.
  - constructor.
  - constructor.
    + eapply lc_ty_monotone; eauto.
    + apply IHlc_tm_at; lia.
  - constructor; eauto.
  - constructor; apply IHlc_tm_at; lia.
  - constructor; eauto using lc_ty_monotone.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at 0 0 t -> lc_tm_at K k t.
Proof. intros; eapply lc_tm_monotone; eauto; lia. Qed.

Lemma close_ty_lc : forall K T rho,
  lc_ty_at K T -> (forall X, lc_ty_at 0 (rho X)) ->
  lc_ty_at K (close_ty rho T).
Proof.
  intros K T rho H; induction H; intros HC; simpl; eauto using lc_ty_weaken with core.
Qed.

Lemma close_tm_lc : forall K k t rho gamma,
  lc_tm_at K k t ->
  (forall X, lc_ty_at 0 (rho X)) ->
  (forall x, lc_tm_at 0 0 (gamma x)) ->
  lc_tm_at K k (close_tm rho gamma t).
Proof.
  intros K k t rho gamma H; induction H; intros HR HG; simpl;
    eauto using lc_tm_weaken, close_ty_lc with core.
Qed.

Lemma open_ty_lc_inverse : forall K T X,
  lc_ty_at K (open_ty_rec K (Ty_FVar X) T) ->
  lc_ty_at (S K) T.
Proof.
  intros K T; revert K; induction T; intros K X H; simpl in *.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma open_tm_lc_inverse : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k; induction t; intros K k x H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma open_tm_ty_lc_inverse : forall K k t X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k t; revert K k; induction t; intros K k X H; simpl in *;
    inversion H; subst; eauto with core.
  - constructor; eauto using open_ty_lc_inverse.
  - constructor; eauto using open_ty_lc_inverse.
Qed.

Lemma list_max_bound : forall L n, In n L -> n <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; simpl; intros n H.
  - contradiction.
  - destruct H as [->|H]; [lia|]. specialize (IH _ H); lia.
Qed.

Lemma fresh : forall L, ~ In (S (fold_right Nat.max 0 L)) L.
Proof. intros L H; pose proof (list_max_bound L _ H); lia. Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - constructor.
  - constructor; assumption.
  - apply lc_ty_all.
  eapply open_ty_lc_inverse.
  apply (H0 (S (fold_right Nat.max 0 L))).
  apply fresh.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - constructor.
  - constructor.
    + apply wf_ty_lc in H; exact H.
    + eapply open_tm_lc_inverse.
      apply (H1 (S (fold_right Nat.max 0 L))); apply fresh.
  - constructor; assumption.
  - constructor. eapply open_tm_ty_lc_inverse.
    apply (H0 (S (fold_right Nat.max 0 L))); apply fresh.
  - constructor; [exact IHhas_type | eapply wf_ty_lc; eassumption].
Qed.

Definition relation := tm -> tm -> Prop.
Definition type_relations := atom -> relation.

Fixpoint value_rel (T : ty) (eta : type_relations)
    (bounds : list relation) (v1 v2 : tm) : Prop :=
  value v1 /\ value v2 /\
  match T with
  | Ty_BVar n => match nth_error bounds n with
                 | Some R => R v1 v2 | None => False end
  | Ty_FVar X => eta X v1 v2
  | Ty_Arrow A B =>
      forall a1 a2, value_rel A eta bounds a1 a2 ->
        exists b1 b2,
          tm_app v1 a1 -->* b1 /\ tm_app v2 a2 -->* b2 /\
          value_rel B eta bounds b1 b2
  | Ty_All A =>
      forall U1 U2 (R : relation),
        locally_closed_ty U1 -> locally_closed_ty U2 ->
        exists b1 b2,
          tm_tapp v1 U1 -->* b1 /\ tm_tapp v2 U2 -->* b2 /\
          value_rel A eta (R :: bounds) b1 b2
  end.

Definition expression_rel (T : ty) (eta : type_relations)
    (bounds : list relation) (t1 t2 : tm) : Prop :=
  locally_closed_tm t1 /\ locally_closed_tm t2 /\
  exists v1 v2, t1 -->* v1 /\ t2 -->* v2 /\
                value_rel T eta bounds v1 v2.

Definition interprets_type_variables (rho1 rho2 : atom -> ty) : Prop :=
  (forall X, locally_closed_ty (rho1 X)) /\
  (forall X, locally_closed_ty (rho2 X)).

Definition interprets_term_variables (Gamma : context) (eta : type_relations)
    (gamma1 gamma2 : atom -> tm) : Prop :=
  (forall x, locally_closed_tm (gamma1 x)) /\
  (forall x, locally_closed_tm (gamma2 x)) /\
  (forall x S, lookup_context x Gamma = Some S ->
    expression_rel S eta [] (gamma1 x) (gamma2 x)).

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H; induction H; intros G; eauto using multi.
Qed.

Lemma multi_app_left : forall a b u,
  a -->* b -> locally_closed_tm u -> tm_app a u -->* tm_app b u.
Proof.
  intros a b u H; induction H; intros HU; eauto using multi.
  eapply multi_step; [apply ST_App1; eassumption|auto].
Qed.

Lemma multi_app_right : forall a u w,
  value a -> u -->* w -> tm_app a u -->* tm_app a w.
Proof.
  intros a u w HA H; induction H; eauto using multi.
  eapply multi_step; [apply ST_App2; eassumption|auto].
Qed.

Lemma multi_tapp : forall a b U,
  a -->* b -> locally_closed_ty U -> tm_tapp a U -->* tm_tapp b U.
Proof.
  intros a b U H; induction H; intros HU; eauto using multi.
  eapply multi_step; [apply ST_TApp; eassumption|auto].
Qed.

Lemma value_rel_lc : forall T eta bounds a b,
  value_rel T eta bounds a b -> locally_closed_tm a /\ locally_closed_tm b.
Proof.
  intros T eta bounds a b H; destruct T; simpl in H;
    destruct H as [HA [HB _]]; auto using value_lc.
Qed.

Lemma value_rel_values : forall T eta bounds a b,
  value_rel T eta bounds a b -> value a /\ value b.
Proof.
  intros T eta bounds a b H; destruct T; simpl in H; tauto.
Qed.

Lemma open_ty_noop : forall K U V,
  lc_ty_at K U -> forall j, K <= j -> open_ty_rec j V U = U.
Proof.
  intros K U V H; induction H; intros j Hj; simpl.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal; auto.
  - f_equal; apply IHlc_ty_at; lia.
Qed.

Lemma open_ty_closed : forall K U V,
  lc_ty_at 0 U -> open_ty_rec K V U = U.
Proof. intros; eapply open_ty_noop; eauto; lia. Qed.

Lemma open_tm_noop : forall K k u t,
  lc_tm_at K k t -> forall j, k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k u t H; induction H; intros j Hj; simpl.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal; apply IHlc_tm_at; lia.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma open_tm_closed : forall K u t,
  lc_tm_at 0 0 t -> open_tm_rec K u t = t.
Proof. intros; eapply open_tm_noop; eauto; lia. Qed.

Lemma open_tm_ty_noop : forall K k U t,
  lc_tm_at K k t -> forall j, K <= j -> open_tm_ty_rec j U t = t.
Proof.
  intros K k U t H; induction H; intros j Hj; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; [eapply open_ty_noop; eauto | auto].
  - f_equal; auto.
  - f_equal; apply IHlc_tm_at; lia.
  - f_equal; [auto | eapply open_ty_noop; eauto].
Qed.

Lemma open_tm_ty_closed : forall K U t,
  lc_tm_at 0 0 t -> open_tm_ty_rec K U t = t.
Proof. intros; eapply open_tm_ty_noop; eauto; lia. Qed.

Lemma close_ty_open : forall T K rho X,
  (forall Y, locally_closed_ty (rho Y)) ->
  close_ty rho (open_ty_rec K (Ty_FVar X) T) =
    open_ty_rec K (rho X) (close_ty rho T).
Proof.
  induction T; intros K rho X HR; simpl.
  - destruct (Nat.eqb K n); reflexivity.
  - symmetry; apply open_ty_closed; exact (HR a).
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma close_tm_open : forall t K rho gamma x,
  (forall y, locally_closed_tm (gamma y)) ->
  close_tm rho gamma (open_tm_rec K (tm_fvar x) t) =
    open_tm_rec K (gamma x) (close_tm rho gamma t).
Proof.
  induction t; intros K rho gamma x HG; simpl.
  - destruct (Nat.eqb K n); reflexivity.
  - symmetry; apply open_tm_closed; exact (HG a).
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma close_tm_ty_open : forall t K rho gamma X,
  (forall Y, locally_closed_ty (rho Y)) ->
  (forall y, locally_closed_tm (gamma y)) ->
  close_tm rho gamma (open_tm_ty_rec K (Ty_FVar X) t) =
    open_tm_ty_rec K (rho X) (close_tm rho gamma t).
Proof.
  induction t; intros K rho gamma X HR HG; simpl.
  - reflexivity.
  - symmetry; apply open_tm_ty_closed; exact (HG a).
  - f_equal; [apply close_ty_open | apply IHt]; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; [apply IHt | apply close_ty_open]; auto.
Qed.

Lemma not_in_app : forall (A : Type) (x : A) l r,
  ~ In x (l ++ r) -> ~ In x l /\ ~ In x r.
Proof.
  intros A x l r H; split; intros Hin; apply H; apply in_or_app; auto.
Qed.

Lemma close_ty_change : forall T rho X U,
  ~ In X (ty_names T) ->
  close_ty (change rho X U) T = close_ty rho T.
Proof.
  induction T; intros rho X U H; simpl in *; auto.
  - unfold change; destruct (Nat.eqb X a) eqn:E; auto.
    apply Nat.eqb_eq in E; subst; contradiction H; auto.
  - apply not_in_app in H; destruct H; f_equal; auto.
  - f_equal; auto.
Qed.

Lemma close_tm_change : forall t rho gamma x a,
  ~ In x (tm_names t) ->
  close_tm rho (change gamma x a) t = close_tm rho gamma t.
Proof.
  induction t; intros rho gamma x replacement H; simpl in *; auto.
  - unfold change; destruct (Nat.eqb x a) eqn:E; auto.
    apply Nat.eqb_eq in E; subst; contradiction H; auto.
  - f_equal; auto.
  - apply not_in_app in H; destruct H; f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma close_tm_type_change : forall t rho gamma X U,
  ~ In X (tm_type_names t) ->
  close_tm (change rho X U) gamma t = close_tm rho gamma t.
Proof.
  induction t; intros rho gamma X U H; simpl in *; auto.
  - apply not_in_app in H; destruct H; f_equal;
      auto using close_ty_change.
  - apply not_in_app in H; destruct H; f_equal; auto.
  - f_equal; auto.
  - apply not_in_app in H; destruct H; f_equal;
      auto using close_ty_change.
Qed.

Lemma close_tm_open_change : forall t rho gamma x a,
  ~ In x (tm_names t) ->
  (forall y, locally_closed_tm (gamma y)) ->
  locally_closed_tm a ->
  close_tm rho (change gamma x a) (open_tm t (tm_fvar x)) =
    open_tm (close_tm rho gamma t) a.
Proof.
  intros t rho gamma x a H HG HA.
  unfold open_tm.
  rewrite close_tm_open.
  - replace (change gamma x a x) with a
      by (unfold change; now rewrite Nat.eqb_refl).
    rewrite close_tm_change by assumption; reflexivity.
  - intros y; unfold change; destruct (Nat.eqb x y); auto.
Qed.

Lemma close_tm_ty_open_change : forall t rho gamma X U,
  ~ In X (tm_type_names t) ->
  (forall Y, locally_closed_ty (rho Y)) ->
  (forall y, locally_closed_tm (gamma y)) ->
  locally_closed_ty U ->
  close_tm (change rho X U) gamma (open_tm_ty t (Ty_FVar X)) =
    open_tm_ty (close_tm rho gamma t) U.
Proof.
  intros t rho gamma X U H HR HG HU.
  unfold open_tm_ty.
  rewrite close_tm_ty_open.
  - replace (change rho X U X) with U
      by (unfold change; now rewrite Nat.eqb_refl).
    rewrite close_tm_type_change by assumption; reflexivity.
  - intros Y; unfold change; destruct (Nat.eqb X Y); auto.
  - exact HG.
Qed.

Lemma close_ty_open_change : forall T rho X U,
  ~ In X (ty_names T) ->
  (forall Y, locally_closed_ty (rho Y)) ->
  locally_closed_ty U ->
  close_ty (change rho X U) (open_ty T (Ty_FVar X)) =
    open_ty (close_ty rho T) U.
Proof.
  intros T rho X U H HR HU.
  unfold open_ty.
  rewrite close_ty_open.
  - replace (change rho X U X) with U
      by (unfold change; now rewrite Nat.eqb_refl).
    rewrite close_ty_change by assumption; reflexivity.
  - intros Y; unfold change; destruct (Nat.eqb X Y); auto.
Qed.

Lemma value_rel_open : forall T K eta R bounds X a b,
  length bounds = K -> ~ In X (ty_names T) ->
  (value_rel (open_ty_rec K (Ty_FVar X) T)
     (change eta X R) bounds a b <->
   value_rel T eta (bounds ++ [R]) a b).
Proof.
  induction T; intros K eta R bounds X left right Hlen Hfresh;
    simpl in Hfresh; simpl.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst n.
      rewrite nth_error_app2 by lia.
      replace (K - length bounds) with 0 by lia; simpl.
      unfold change; rewrite Nat.eqb_refl; tauto.
    + apply Nat.eqb_neq in E; destruct (Nat.lt_ge_cases n K) as [Hlt|Hgt].
      * simpl; rewrite nth_error_app1 by lia; tauto.
      * assert (K < n) by lia.
        simpl; rewrite nth_error_app2 by lia.
        replace (nth_error bounds n) with (@None relation).
        2: { symmetry; apply nth_error_None; lia. }
        destruct (n - length bounds) as [|m] eqn:En; [lia|].
        destruct m; simpl; tauto.
  - unfold change; destruct (Nat.eqb X a) eqn:E; [|tauto].
    apply Nat.eqb_eq in E; subst; contradiction Hfresh; auto.
  - apply not_in_app in Hfresh; destruct Hfresh as [HA HB].
    assert (HRA : forall v w,
      value_rel (open_ty_rec K (Ty_FVar X) T1) (change eta X R) bounds v w
        <-> value_rel T1 eta (bounds ++ [R]) v w).
    { intros; eapply IHT1; eauto. }
    assert (HRB : forall v w,
      value_rel (open_ty_rec K (Ty_FVar X) T2) (change eta X R) bounds v w
        <-> value_rel T2 eta (bounds ++ [R]) v w).
    { intros; eapply IHT2; eauto. }
    simpl; split; intros [VL [VR HF]]; repeat split; try assumption;
      intros v w HV.
    + apply (proj2 (HRA v w)) in HV.
      destruct (HF v w HV) as [u [z [HL [HR HZ]]]].
      exists u, z; repeat split; auto.
      apply (proj1 (HRB u z)); assumption.
    + apply (proj1 (HRA v w)) in HV.
      destruct (HF v w HV) as [u [z [HL [HR HZ]]]].
      exists u, z; repeat split; auto.
      apply (proj2 (HRB u z)); assumption.
  - assert (HR : forall Q v w,
      value_rel (open_ty_rec (S K) (Ty_FVar X) T)
        (change eta X R) (Q :: bounds) v w <->
      value_rel T eta ((Q :: bounds) ++ [R]) v w).
    { intros; eapply IHT; eauto. simpl; lia. }
    simpl; split; intros [VL [VR HF]]; repeat split; try assumption;
      intros U1 U2 Q HU1 HU2.
    + destruct (HF U1 U2 Q HU1 HU2) as [u [z [HL [HRR HZ]]]].
      exists u, z; repeat split; auto.
      apply (proj1 (HR Q u z)); assumption.
    + destruct (HF U1 U2 Q HU1 HU2) as [u [z [HL [HRR HZ]]]].
      exists u, z; repeat split; auto.
      apply (proj2 (HR Q u z)); assumption.
Qed.

Lemma value_rel_bounds : forall U K,
  lc_ty_at K U -> forall eta bs1 bs2 a b,
  (forall i, i < K -> nth_error bs1 i = nth_error bs2 i) ->
  (value_rel U eta bs1 a b <-> value_rel U eta bs2 a b).
Proof.
  intros U K HL; induction HL; intros eta bs1 bs2 left right HE; simpl.
  - rewrite (HE i H); tauto.
  - tauto.
  - assert (HA : forall v w, value_rel T1 eta bs1 v w <->
                            value_rel T1 eta bs2 v w).
    { intros; apply IHHL1; exact HE. }
    assert (HB : forall v w, value_rel T2 eta bs1 v w <->
                            value_rel T2 eta bs2 v w).
    { intros; apply IHHL2; exact HE. }
    split; intros [VL [VR HF]]; repeat split; try assumption;
      intros v w HV.
    + apply (proj2 (HA v w)) in HV.
      destruct (HF v w HV) as [u [z [HL' [HR' HZ]]]].
      exists u, z; repeat split; auto; apply (proj1 (HB u z)); assumption.
    + apply (proj1 (HA v w)) in HV.
      destruct (HF v w HV) as [u [z [HL' [HR' HZ]]]].
      exists u, z; repeat split; auto; apply (proj2 (HB u z)); assumption.
  - assert (HA : forall Q v w,
       value_rel T eta (Q :: bs1) v w <-> value_rel T eta (Q :: bs2) v w).
    { intros; apply IHHL; intros [|i] Hi; simpl; auto.
      apply HE; lia. }
    split; intros [VL [VR HF]]; repeat split; try assumption;
      intros U1 U2 Q HU1 HU2.
    + destruct (HF U1 U2 Q HU1 HU2) as [u [z [HL' [HR' HZ]]]].
      exists u, z; repeat split; auto; apply (proj1 (HA Q u z)); assumption.
    + destruct (HF U1 U2 Q HU1 HU2) as [u [z [HL' [HR' HZ]]]].
      exists u, z; repeat split; auto; apply (proj2 (HA Q u z)); assumption.
Qed.

Lemma value_rel_open_type : forall T K eta R bounds U a b,
  length bounds = K -> locally_closed_ty U ->
  (forall v w, R v w <-> value_rel U eta [] v w) ->
  (value_rel (open_ty_rec K U T) eta bounds a b <->
   value_rel T eta (bounds ++ [R]) a b).
Proof.
  induction T; intros K eta R bounds U left right Hlen HU HRel; simpl.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst n.
      rewrite nth_error_app2 by lia.
      replace (K - length bounds) with 0 by lia; simpl.
      transitivity (value_rel U eta [] left right).
      * apply value_rel_bounds with (K := 0); auto. intros; lia.
      * destruct U; simpl in *; destruct (HRel left right); tauto.
    + apply Nat.eqb_neq in E; destruct (Nat.lt_ge_cases n K) as [Hlt|Hgt].
      * simpl; rewrite nth_error_app1 by lia; tauto.
      * assert (K < n) by lia.
        simpl; rewrite nth_error_app2 by lia.
        replace (nth_error bounds n) with (@None relation).
        2: { symmetry; apply nth_error_None; lia. }
        destruct (n - length bounds) as [|m] eqn:En; [lia|].
        destruct m; simpl; tauto.
  - tauto.
  - assert (HA : forall v w,
      value_rel (open_ty_rec K U T1) eta bounds v w <->
      value_rel T1 eta (bounds ++ [R]) v w).
    { intros; eapply IHT1; eauto. }
    assert (HB : forall v w,
      value_rel (open_ty_rec K U T2) eta bounds v w <->
      value_rel T2 eta (bounds ++ [R]) v w).
    { intros; eapply IHT2; eauto. }
    split; intros [VL [VR HF]]; repeat split; try assumption;
      intros v w HV.
    + apply (proj2 (HA v w)) in HV.
      destruct (HF v w HV) as [u [z [HL' [HR' HZ]]]].
      exists u, z; repeat split; auto; apply (proj1 (HB u z)); assumption.
    + apply (proj1 (HA v w)) in HV.
      destruct (HF v w HV) as [u [z [HL' [HR' HZ]]]].
      exists u, z; repeat split; auto; apply (proj2 (HB u z)); assumption.
  - assert (HA : forall Q v w,
      value_rel (open_ty_rec (S K) U T) eta (Q :: bounds) v w <->
      value_rel T eta ((Q :: bounds) ++ [R]) v w).
    { intros; eapply IHT; eauto. simpl; lia. }
    split; intros [VL [VR HF]]; repeat split; try assumption;
      intros U1 U2 Q HU1 HU2.
    + destruct (HF U1 U2 Q HU1 HU2) as [u [z [HL' [HR' HZ]]]].
      exists u, z; repeat split; auto; apply (proj1 (HA Q u z)); assumption.
    + destruct (HF U1 U2 Q HU1 HU2) as [u [z [HL' [HR' HZ]]]].
      exists u, z; repeat split; auto; apply (proj2 (HA Q u z)); assumption.
Qed.

Lemma value_rel_change : forall T eta R bounds X a b,
  ~ In X (ty_names T) ->
  (value_rel T (change eta X R) bounds a b <->
   value_rel T eta bounds a b).
Proof.
  induction T; intros eta R bounds X left right HF; simpl in *.
  - tauto.
  - unfold change; destruct (Nat.eqb X a) eqn:E; [|tauto].
    apply Nat.eqb_eq in E; subst; contradiction HF; auto.
  - apply not_in_app in HF; destruct HF as [HA HB].
    assert (HRA : forall v w, value_rel T1 (change eta X R) bounds v w
                            <-> value_rel T1 eta bounds v w).
    { intros; apply IHT1; assumption. }
    assert (HRB : forall v w, value_rel T2 (change eta X R) bounds v w
                            <-> value_rel T2 eta bounds v w).
    { intros; apply IHT2; assumption. }
    split; intros [VL [VR HFn]]; repeat split; try assumption;
      intros v w HV.
    + apply (proj2 (HRA v w)) in HV.
      destruct (HFn v w HV) as [u [z [HL [HR' HZ]]]].
      exists u, z; repeat split; auto; apply (proj1 (HRB u z)); assumption.
    + apply (proj1 (HRA v w)) in HV.
      destruct (HFn v w HV) as [u [z [HL [HR' HZ]]]].
      exists u, z; repeat split; auto; apply (proj2 (HRB u z)); assumption.
  - assert (HA : forall Q v w, value_rel T (change eta X R) (Q :: bounds) v w
                       <-> value_rel T eta (Q :: bounds) v w).
    { intros; apply IHT; assumption. }
    split; intros [VL [VR HFn]]; repeat split; try assumption;
      intros U1 U2 Q HU1 HU2.
    + destruct (HFn U1 U2 Q HU1 HU2) as [u [z [HL [HR' HZ]]]].
      exists u, z; repeat split; auto; apply (proj1 (HA Q u z)); assumption.
    + destruct (HFn U1 U2 Q HU1 HU2) as [u [z [HL [HR' HZ]]]].
      exists u, z; repeat split; auto; apply (proj2 (HA Q u z)); assumption.
Qed.

Lemma expression_rel_change : forall T eta R bounds X a b,
  ~ In X (ty_names T) ->
  expression_rel T (change eta X R) bounds a b <->
  expression_rel T eta bounds a b.
Proof.
  intros T eta R bounds X a b HF; unfold expression_rel.
  split; intros [HA [HB [v [w [HL [HR HV]]]]]];
    repeat split; try assumption; exists v, w; repeat split; auto.
  - apply (proj1 (value_rel_change T eta R bounds X v w HF)); assumption.
  - apply (proj2 (value_rel_change T eta R bounds X v w HF)); assumption.
Qed.

Fixpoint context_type_names (Gamma : context) : list atom :=
  match Gamma with
  | [] => [] | (_, T) :: rest => ty_names T ++ context_type_names rest
  end.

Lemma lookup_type_names : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (ty_names T) ->
  In X (context_type_names Gamma).
Proof.
  induction Gamma as [|[y S] Gamma IH]; simpl; intros x T X HL HI.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion HL; subst; apply in_or_app; auto.
    + apply in_or_app; right; eapply IH; eauto.
Qed.

Lemma typed_close_lc : forall Delta Gamma t T rho gamma,
  has_type Delta Gamma t T ->
  (forall X, locally_closed_ty (rho X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  locally_closed_tm (close_tm rho gamma t).
Proof.
  intros; eapply close_tm_lc; eauto.
  eapply has_type_lc; eassumption.
Qed.

Lemma value_expression : forall T eta bounds a b,
  value_rel T eta bounds a b -> expression_rel T eta bounds a b.
Proof.
  intros T eta bounds a b H.
  destruct (value_rel_lc _ _ _ _ _ H) as [HA HB].
  unfold expression_rel; repeat split; auto.
  exists a, b; repeat split; auto using multi_refl.
Qed.

Lemma expression_application : forall A B eta bounds f1 f2 a1 a2,
  expression_rel (Ty_Arrow A B) eta bounds f1 f2 ->
  expression_rel A eta bounds a1 a2 ->
  expression_rel B eta bounds (tm_app f1 a1) (tm_app f2 a2).
Proof.
  intros A B eta bounds f1 f2 a1 a2
    [HF1 [HF2 [v1 [v2 [HS1 [HS2 [HV1 [HV2 HF]]]]]]]]
    [HA1 [HA2 [w1 [w2 [HT1 [HT2 HW]]]]]].
  destruct (HF w1 w2 HW) as [z1 [z2 [HU1 [HU2 HZ]]]].
  unfold expression_rel; split; [constructor; assumption|].
  split; [constructor; assumption|].
  exists z1, z2; repeat split; auto.
  - eapply multi_trans; [apply multi_app_left; eauto|].
    eapply multi_trans; [apply multi_app_right; eauto|exact HU1].
  - eapply multi_trans; [apply multi_app_left; eauto|].
    eapply multi_trans; [apply multi_app_right; eauto|exact HU2].
Qed.

Lemma close_ty_identity : forall T, close_ty Ty_FVar T = T.
Proof. induction T; simpl; f_equal; auto. Qed.

Lemma close_tm_identity : forall t, close_tm Ty_FVar tm_fvar t = t.
Proof.
  induction t; simpl; f_equal; auto using close_ty_identity.
Qed.

Lemma expression_type_application : forall A eta f1 f2 U1 U2 R,
  expression_rel (Ty_All A) eta [] f1 f2 ->
  locally_closed_ty U1 -> locally_closed_ty U2 ->
  expression_rel A eta [R] (tm_tapp f1 U1) (tm_tapp f2 U2).
Proof.
  intros A eta f1 f2 U1 U2 R
    [HF1 [HF2 [v1 [v2 [HS1 [HS2 [HV1 [HV2 HF]]]]]]]] HU1 HU2.
  destruct (HF U1 U2 R HU1 HU2) as [w1 [w2 [HT1 [HT2 HW]]]].
  unfold expression_rel; split; [constructor; assumption|].
  split; [constructor; assumption|].
  exists w1, w2; repeat split; auto.
  - eapply multi_trans; [apply multi_tapp; eauto|exact HT1].
  - eapply multi_trans; [apply multi_tapp; eauto|exact HT2].
Qed.

Lemma expression_open_free : forall T eta R X a b,
  ~ In X (ty_names T) ->
  expression_rel (open_ty T (Ty_FVar X)) (change eta X R) [] a b ->
  expression_rel T eta [R] a b.
Proof.
  intros T eta R X a b HF [HA [HB [v [w [HL [HR HV]]]]]].
  unfold expression_rel; repeat split; auto.
  exists v, w; repeat split; auto.
  apply (proj1 (value_rel_open T 0 eta R [] X v w eq_refl HF));
    exact HV.
Qed.

Lemma expression_open_type : forall T U eta a b,
  locally_closed_ty U ->
  expression_rel T eta [value_rel U eta []] a b ->
  expression_rel (open_ty T U) eta [] a b.
Proof.
  intros T U eta a b HU [HA [HB [v [w [HL [HR HV]]]]]].
  unfold expression_rel; repeat split; auto.
  exists v, w; repeat split; auto.
  apply (proj2 (value_rel_open_type T 0 eta (value_rel U eta []) [] U v w
    eq_refl HU (fun left right => iff_refl _))); exact HV.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho1 rho2 eta gamma1 gamma2,
  (forall X, locally_closed_ty (rho1 X)) ->
  (forall X, locally_closed_ty (rho2 X)) ->
  (forall x, locally_closed_tm (gamma1 x)) ->
  (forall x, locally_closed_tm (gamma2 x)) ->
  (forall x S, lookup_context x Gamma = Some S ->
    expression_rel S eta [] (gamma1 x) (gamma2 x)) ->
  expression_rel T eta []
    (close_tm rho1 gamma1 t) (close_tm rho2 gamma2 t).
Proof.
  intros Delta Gamma t T HT; induction HT;
    intros rho1 rho2 eta gamma1 gamma2 HR1 HR2 HG1 HG2 HC; simpl.
  - apply HC; assumption.
  - set (x := S (fold_right Nat.max 0 (L ++ tm_names t2))).
    assert (Hfresh : ~ In x (L ++ tm_names t2))
      by (unfold x; apply fresh).
    apply not_in_app in Hfresh as [Havoid Hnames].
    assert (HAbs1 : locally_closed_tm
       (tm_abs (close_ty rho1 T1) (close_tm rho1 gamma1 t2))).
    { change (locally_closed_tm (close_tm rho1 gamma1 (tm_abs T1 t2))).
      eapply typed_close_lc; [exact (T_Abs L Delta Gamma T1 t2 T2 H H0)
      | exact HR1 | exact HG1]. }
    assert (HAbs2 : locally_closed_tm
       (tm_abs (close_ty rho2 T1) (close_tm rho2 gamma2 t2))).
    { change (locally_closed_tm (close_tm rho2 gamma2 (tm_abs T1 t2))).
      eapply typed_close_lc; [exact (T_Abs L Delta Gamma T1 t2 T2 H H0)
      | exact HR2 | exact HG2]. }
    apply value_expression; simpl; repeat split;
      try (constructor; assumption).
    intros a1 a2 HA.
    destruct (value_rel_values _ _ _ _ _ HA) as [VA1 VA2].
    assert (HG1' : forall y, locally_closed_tm (change gamma1 x a1 y)).
    { intros y; unfold change; destruct (Nat.eqb x y); auto using value_lc. }
    assert (HG2' : forall y, locally_closed_tm (change gamma2 x a2 y)).
    { intros y; unfold change; destruct (Nat.eqb x y); auto using value_lc. }
    assert (HC' : forall y S,
      lookup_context y ((x, T1) :: Gamma) = Some S ->
      expression_rel S eta [] (change gamma1 x a1 y) (change gamma2 x a2 y)).
    { intros y S HS; simpl in HS.
      destruct (Nat.eqb x y) eqn:E.
      - apply Nat.eqb_eq in E; subst y; rewrite Nat.eqb_refl in HS.
        inversion HS; subst S.
        unfold change; rewrite Nat.eqb_refl.
        apply value_expression; assumption.
      - rewrite Nat.eqb_sym in E; rewrite E in HS.
        unfold change; rewrite Nat.eqb_sym; rewrite E.
        apply HC; assumption. }
    pose proof (H1 x Havoid rho1 rho2 eta
      (change gamma1 x a1) (change gamma2 x a2)
      HR1 HR2 HG1' HG2' HC') as HB.
    rewrite (close_tm_open_change t2 rho1 gamma1 x a1 Hnames HG1)
      in HB by (apply value_lc; exact VA1).
    rewrite (close_tm_open_change t2 rho2 gamma2 x a2 Hnames HG2)
      in HB by (apply value_lc; exact VA2).
    destruct HB as [_ [_ [b1 [b2 [HS1 [HS2 HV]]]]]].
    exists b1, b2; repeat split; auto.
    + eapply multi_step; [apply ST_AppAbs; eauto|exact HS1].
    + eapply multi_step; [apply ST_AppAbs; eauto|exact HS2].
  - eapply expression_application; [apply IHHT1 | apply IHHT2];
      eauto.
  - set (X := S (fold_right Nat.max 0
      (L ++ tm_type_names t ++ ty_names T ++ context_type_names Gamma))).
    assert (Hfresh : ~ In X
      (L ++ tm_type_names t ++ ty_names T ++ context_type_names Gamma))
      by (unfold X; apply fresh).
    apply not_in_app in Hfresh as [Havoid Hrest].
    apply not_in_app in Hrest as [Hterm Hrest].
    apply not_in_app in Hrest as [Htype Hctx].
    assert (HTabs1 : locally_closed_tm (tm_tabs (close_tm rho1 gamma1 t))).
    { change (locally_closed_tm (close_tm rho1 gamma1 (tm_tabs t))).
      eapply typed_close_lc; [exact (T_TAbs L Delta Gamma t T H)
      | exact HR1 | exact HG1]. }
    assert (HTabs2 : locally_closed_tm (tm_tabs (close_tm rho2 gamma2 t))).
    { change (locally_closed_tm (close_tm rho2 gamma2 (tm_tabs t))).
      eapply typed_close_lc; [exact (T_TAbs L Delta Gamma t T H)
      | exact HR2 | exact HG2]. }
    apply value_expression; simpl; repeat split;
      try (constructor; assumption).
    intros U1 U2 R HU1 HU2.
    assert (HR1' : forall Y, locally_closed_ty (change rho1 X U1 Y)).
    { intros Y; unfold change; destruct (Nat.eqb X Y); auto. }
    assert (HR2' : forall Y, locally_closed_ty (change rho2 X U2 Y)).
    { intros Y; unfold change; destruct (Nat.eqb X Y); auto. }
    assert (HC' : forall y S, lookup_context y Gamma = Some S ->
      expression_rel S (change eta X R) [] (gamma1 y) (gamma2 y)).
    { intros y S HS.
      assert (HF : ~ In X (ty_names S)).
      { intro Hin; apply Hctx; eapply lookup_type_names; eauto. }
      apply (proj2 (expression_rel_change S eta R [] X
        (gamma1 y) (gamma2 y) HF)); apply HC; assumption. }
    pose proof (H0 X Havoid (change rho1 X U1) (change rho2 X U2)
      (change eta X R) gamma1 gamma2 HR1' HR2' HG1 HG2 HC') as HB.
    rewrite (close_tm_ty_open_change t rho1 gamma1 X U1
      Hterm HR1 HG1 HU1) in HB.
    rewrite (close_tm_ty_open_change t rho2 gamma2 X U2
      Hterm HR2 HG2 HU2) in HB.
    apply (expression_open_free T eta R X _ _ Htype) in HB.
    destruct HB as [_ [_ [b1 [b2 [HS1 [HS2 HV]]]]]].
    exists b1, b2; repeat split; auto.
    + eapply multi_step; [apply ST_TAppTabs; eauto|exact HS1].
    + eapply multi_step; [apply ST_TAppTabs; eauto|exact HS2].
  - eapply expression_open_type; [eapply wf_ty_lc; eassumption|].
    eapply expression_type_application.
    + apply IHHT; eauto.
    + eapply close_ty_lc; [eapply wf_ty_lc; exact H | exact HR1].
    + eapply close_ty_lc; [eapply wf_ty_lc; exact H | exact HR2].
Qed.

Corollary fundamental_for_contexts : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho1 rho2 eta gamma1 gamma2,
  interprets_type_variables rho1 rho2 ->
  interprets_term_variables Gamma eta gamma1 gamma2 ->
  expression_rel T eta []
    (close_tm rho1 gamma1 t) (close_tm rho2 gamma2 t).
Proof.
  intros Delta Gamma t T HT rho1 rho2 eta gamma1 gamma2
    [HR1 HR2] [HG1 [HG2 HC]].
  eapply fundamental; eauto.
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
  intros t HT U v HU HV HVT.
  set (eta := (fun _ : atom => (fun _ _ : tm => False))).
  set (singleton := (fun left right : tm => left = v /\ right = v)).
  assert (Hfund : expression_rel
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) eta [] t t).
  { rewrite <- (close_tm_identity t) at 1.
    rewrite <- (close_tm_identity t) at 2.
    eapply fundamental; [exact HT| | | | |].
    - intro X; constructor.
    - intro X; constructor.
    - intro x; constructor.
    - intro x; constructor.
    - intros x S Hlookup; discriminate Hlookup. }
  pose proof (expression_type_application _ eta t t U U singleton
    Hfund (wf_ty_lc _ _ HU) (wf_ty_lc _ _ HU)) as Hinst.
  assert (Harg : expression_rel (Ty_BVar 0) eta [singleton] v v).
  { apply value_expression; simpl; repeat split; auto. }
  pose proof (expression_application (Ty_BVar 0) (Ty_BVar 0)
    eta [singleton] (tm_tapp t U) (tm_tapp t U) v v Hinst Harg)
    as Hresult.
  destruct Hresult as [_ [_ [answer1 [answer2 [Hpath1 [_ Hrelated]]]]]].
  simpl in Hrelated.
  destruct Hrelated as [_ [_ [Heq _]]].
  subst answer1; exact Hpath1.
Qed.

End SystemFParametricityNoneHardTask.
