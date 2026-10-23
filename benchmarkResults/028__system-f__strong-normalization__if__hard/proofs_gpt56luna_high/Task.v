(** System F CBV strong-normalization benchmark, Hard variant.
    Features: if. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfHardTask.

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

  | Ty_All : ty -> ty
  | Ty_Bool : ty.

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
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

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

Notation "'Bool'" := Ty_Bool (in custom systemf_ty at level 0) : systemf_scope.
Notation "'true'" := tm_true (in custom systemf_tm at level 0) : systemf_scope.
Notation "'false'" := tm_false (in custom systemf_tm at level 0) : systemf_scope.
Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm, t3 custom systemf_tm at level 200) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_rec k u t1) (open_tm_rec k u t2) (open_tm_rec k u t3)
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2) (open_tm_ty_rec k U t3)
  end.

Definition open_tm_ty (t : tm) (U : ty) : tm :=
  open_tm_ty_rec 0 U t.

Fixpoint ty_subst (X : atom) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then U else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst X U T1) (ty_subst X U T2)
  | Ty_All T1 => Ty_All (ty_subst X U T1)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_ty_subst X U t1) (tm_ty_subst X U t2) (tm_ty_subst X U t3)
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst x s t1) (tm_subst x s t2) (tm_subst x s t3)
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
      lc_ty_at k (Ty_All T)
  | lc_ty_bool : forall k, lc_ty_at k Ty_Bool.

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
  | lc_tm_true : forall K k, lc_tm_at K k tm_true
  | lc_tm_false : forall K k, lc_tm_at K k tm_false
  | lc_tm_if : forall K k t1 t2 t3,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 -> lc_tm_at K k (tm_if t1 t2 t3).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_true : value tm_true
  | v_false : value tm_false.

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
  | ST_IfTrue : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      locally_closed_tm t2 ->
      locally_closed_tm t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
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
      wf_ty Delta (Ty_All T)
  | WF_Bool : forall Delta, wf_ty Delta Ty_Bool.

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
  | T_True : forall Delta Gamma, has_type Delta Gamma tm_true Ty_Bool
  | T_False : forall Delta Gamma, has_type Delta Gamma tm_false Ty_Bool
  | T_If : forall Delta Gamma t1 t2 t3 T,
      has_type Delta Gamma t1 Ty_Bool ->
      has_type Delta Gamma t2 T -> has_type Delta Gamma t3 T ->
      has_type Delta Gamma (tm_if t1 t2 t3) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* Construct the logical relation and supporting proofs here. *)

(* A few elementary facts about the (inductive) normalization predicate. *)
Lemma sn_step : forall t u, strongly_normalizing t -> t --> u ->
  strongly_normalizing u.
Proof.
  intros t u H; induction H as [t Hrec].
  apply Hrec; assumption.
Qed.

Lemma sn_of_all_steps : forall t,
  (forall u, t --> u -> strongly_normalizing u) ->
  strongly_normalizing t.
Proof. eauto using SN_intro. Qed.

Lemma lc_ty_weaken_gen : forall k1 T, lc_ty_at k1 T ->
  forall k2, k1 <= k2 -> lc_ty_at k2 T.
Proof.
  intros k1 T H; induction H; intros k2 Hk.
  - constructor; lia.
  - constructor.
  - constructor.
    + eapply IHlc_ty_at1; lia.
    + eapply IHlc_ty_at2; lia.
  - constructor; eapply IHlc_ty_at; lia.
  - constructor.
Qed.

Lemma lc_ty_weaken : forall k T, lc_ty_at 0 T -> lc_ty_at k T.
Proof. intros k T H; eapply lc_ty_weaken_gen; eauto using le_0_n. Qed.

Lemma lc_tm_weaken_gen : forall K k1 t, lc_tm_at K k1 t ->
  forall k2, k1 <= k2 -> lc_tm_at K k2 t.
Proof.
  intros K k1 t H; induction H; intros k2 Hk.
  - constructor; lia.
  - constructor.
  - constructor; eauto using lc_ty_weaken.
    eapply IHlc_tm_at; lia.
  - constructor; eauto.
  - constructor; eapply IHlc_tm_at; lia.
  - constructor; eauto.
  - constructor.
  - constructor.
  - constructor; eauto.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K 0 t -> lc_tm_at K k t.
Proof. intros K k t H; eapply lc_tm_weaken_gen; eauto using le_0_n. Qed.

Lemma lc_tm_type_weaken : forall K k t,
  lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H; revert K k H; induction t; intros K0 k0 H0; simpl in *.
  - inversion H0; constructor; assumption.
  - constructor.
  - inversion H0. constructor.
    + eapply lc_ty_weaken_gen; eauto; lia.
    + apply IHt; eauto.
  - inversion H0. constructor; eauto.
  - inversion H0. constructor; apply IHt; eauto.
  - inversion H0. constructor; eauto.
    eapply lc_ty_weaken_gen; eauto; lia.
  - constructor.
  - constructor.
  - inversion H0. constructor; eauto.
Qed.

Lemma lc_ty_open_diag : forall k U T,
  lc_ty_at k U -> lc_ty_at (S k) T ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k U T HU HT. revert k U HU HT; induction T;
    intros k0 U0 HU0 HT0; simpl in *.
  - destruct (Nat.eqb k0 n) eqn:E.
    + apply lc_ty_weaken_gen with (k1 := k0); eauto.
    + inversion HT0; constructor. apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion HT0. constructor.
    + apply IHT1; eauto.
    + apply IHT2; eauto.
  - inversion HT0. constructor.
    apply IHT; eauto.
    all: eapply lc_ty_weaken_gen; eauto; lia.
  - constructor.
Qed.

Lemma lc_ty_open : forall U T,
  lc_ty_at 0 U -> lc_ty_at 1 T ->
  lc_ty_at 0 (open_ty T U).
Proof. intros; unfold open_ty; eapply lc_ty_open_diag; eauto. Qed.

Lemma lc_tm_open : forall K k u t,
  lc_tm_at K k u -> lc_tm_at K (S k) t ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k u t Hu Ht. revert K k u Hu Ht; induction t;
    intros K0 k0 u0 Hu0 Ht0; simpl in *.
  - destruct (Nat.eqb k0 n) eqn:E.
    + apply Hu0.
    + inversion Ht0; constructor. apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion Ht0. constructor.
    + assumption.
    + apply IHt; eauto using lc_tm_weaken.
      all: eapply lc_tm_weaken_gen; eauto; lia.
  - inversion Ht0. constructor.
    + apply IHt1; eauto using lc_tm_weaken.
    + apply IHt2; eauto using lc_tm_weaken.
  - inversion Ht0. constructor.
    apply IHt; eauto using lc_tm_weaken.
    all: apply lc_tm_type_weaken; exact Hu0.
  - inversion Ht0. constructor; eauto.
  - constructor.
  - constructor.
  - inversion Ht0. constructor.
    + apply IHt1; eauto.
    + apply IHt2; eauto.
    + apply IHt3; eauto.
Qed.

Lemma lc_tm_ty_open : forall k j U t,
  lc_ty_at k U -> lc_tm_at (S k) j t ->
  lc_tm_at k j (open_tm_ty_rec k U t).
Proof.
  intros k j U t HU HT. revert k j U HU HT; induction t;
    intros k0 j0 U0 HU0 HT0; simpl in *.
  - constructor. inversion HT0; lia.
  - constructor.
  - inversion HT0. constructor.
    + eapply lc_ty_open_diag; eauto.
    + apply IHt; eauto.
  - inversion HT0. constructor; eauto.
  - inversion HT0. constructor.
    apply IHt; eauto.
    all: eapply lc_ty_weaken_gen; eauto; lia.
  - inversion HT0. constructor.
    + apply IHt; eauto.
      all: match goal with |- ?G => idtac G end.
    + eapply lc_ty_open_diag; eauto.
  - constructor.
  - constructor.
  - inversion HT0. constructor; eauto.
Qed.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
  | Ty_Bool => []
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T t1 => fv_ty T ++ fv_tm t1
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t1 => fv_tm t1
  | tm_tapp t1 T => fv_tm t1 ++ fv_ty T
  | tm_true | tm_false => []
  | tm_if t1 t2 t3 => fv_tm t1 ++ fv_tm t2 ++ fv_tm t3
  end.

Lemma lc_tm_open_inv : forall K k t x,
  ~ In x (fv_tm t) ->
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t x N H. revert K k H N; induction t;
    intros K0 k0 H0 N0; simpl in *.
  - destruct (Nat.eqb k0 n) eqn:E.
    + inversion H0. constructor; apply Nat.eqb_eq in E; lia.
    + inversion H0. constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H0. constructor.
    + assumption.
    + apply IHt; eauto. intro Hin; apply N0; apply in_or_app; right; exact Hin.
  - inversion H0. constructor.
    + apply IHt1; eauto. intro Hin; apply N0; apply in_or_app; left; exact Hin.
    + apply IHt2; eauto. intro Hin; apply N0; apply in_or_app; right; exact Hin.
  - inversion H0. constructor. apply IHt; eauto.
  - inversion H0. constructor.
    + apply IHt; eauto. intro Hin; apply N0; apply in_or_app; left; exact Hin.
    + assumption.
  - constructor.
  - constructor.
  - inversion H0. constructor.
    + apply IHt1; eauto. intro Hin; apply N0; apply in_or_app; left; exact Hin.
    + apply IHt2; eauto. intro Hin; apply N0; apply in_or_app; right; apply in_or_app; left; exact Hin.
    + apply IHt3; eauto. intro Hin; apply N0; apply in_or_app; right; apply in_or_app; right; exact Hin.
Qed.

Lemma lc_ty_open_inv_diag : forall k T X,
  ~ In X (fv_ty T) ->
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) ->
  lc_ty_at (S k) T.
Proof.
  intros k T X N H. revert k H N; induction T;
    intros k0 H0 N0; simpl in *.
  - destruct (Nat.eqb k0 n) eqn:E.
    + constructor; apply Nat.eqb_eq in E; lia.
    + inversion H0; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H0. constructor.
    + apply IHT1; eauto. intro Hin; apply N0; apply in_or_app; left; exact Hin.
    + apply IHT2; eauto. intro Hin; apply N0; apply in_or_app; right; exact Hin.
  - inversion H0. constructor. apply IHT; eauto.
  - constructor.
Qed.

Lemma lc_tm_ty_open_inv : forall K j t X,
  ~ In X (fv_tm t) ->
  lc_tm_at K j (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) j t.
Proof.
  intros K j t X N H. revert K j H N; induction t;
    intros K0 j0 H0 N0; simpl in *.
  - constructor. inversion H0; lia.
  - constructor.
  - inversion H0. constructor.
    + eapply lc_ty_open_inv_diag; eauto.
      intro Hin; apply N0; apply in_or_app; left; exact Hin.
    + apply IHt; eauto. intro Hin; apply N0; apply in_or_app; right; exact Hin.
  - inversion H0. constructor.
    + apply IHt1; eauto. intro Hin; apply N0; apply in_or_app; left; exact Hin.
    + apply IHt2; eauto. intro Hin; apply N0; apply in_or_app; right; exact Hin.
  - inversion H0. constructor; apply IHt; eauto.
  - inversion H0. constructor.
    + apply IHt; eauto. intro Hin; apply N0; apply in_or_app; left; exact Hin.
    + eapply lc_ty_open_inv_diag; eauto.
      intro Hin; apply N0; apply in_or_app; right; exact Hin.
  - constructor.
  - constructor.
  - inversion H0. constructor.
    + apply IHt1; eauto. intro Hin; apply N0; apply in_or_app; left; exact Hin.
    + apply IHt2; eauto. intro Hin; apply N0; apply in_or_app; right; apply in_or_app; left; exact Hin.
    + apply IHt3; eauto. intro Hin; apply N0; apply in_or_app; right; apply in_or_app; right; exact Hin.
Qed.

Lemma in_le_max : forall x l, In x l -> x <= fold_right Nat.max 0 l.
Proof.
  intros x l H; induction l as [|a l IH].
  - inversion H.
  - simpl in H; destruct H as [<-|H].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (m := fold_right Nat.max 0 l).
      * apply IH; exact H.
      * apply Nat.le_max_r.
Qed.

Lemma fresh_notin : forall l,
  ~ In (S (fold_right Nat.max 0 l)) l.
Proof.
  intros l Hin; eapply in_le_max in Hin; lia.
Qed.

Lemma wf_ty_lc : forall D T, wf_ty D T -> lc_ty_at 0 T.
Proof.
  intros D T H; induction H.
  - constructor.
  - constructor; assumption.
  - constructor.
    set (X := S (fold_right Nat.max 0 (L ++ fv_ty T))).
    assert (HXall : ~ In X (L ++ fv_ty T)) by
      (unfold X; intro Hin; eapply in_le_max in Hin; lia).
    assert (HX : ~ In X L) by
      (intro Hin; apply HXall; apply in_or_app; left; exact Hin).
    specialize (H X HX).
    apply lc_ty_open_inv_diag with (X := X); eauto.
    intro Hin; apply HXall; apply in_or_app; right; exact Hin.
  - constructor.
Qed.

Lemma typing_lc : forall D G t T, has_type D G t T -> locally_closed_tm t.
Proof.
  intros D G t T H; induction H.
  - constructor.
  - constructor.
    + eapply wf_ty_lc; eauto.
    +
    set (L' := L ++ fv_tm t2 ++ fv_ty T1).
    assert (Hx' : ~ In (S (fold_right Nat.max 0 L')) L') by apply fresh_notin.
    assert (Hx : ~ In (S (fold_right Nat.max 0 L')) L) by
      (intro Hin; apply Hx'; unfold L'; apply in_or_app; left; exact Hin).
    specialize (H0 (S (fold_right Nat.max 0 L')) Hx).
    apply lc_tm_open_inv with (x := S (fold_right Nat.max 0 L')); eauto.
    intro Hin; apply Hx'; unfold L'; apply in_or_app; right; apply in_or_app; left; exact Hin.
    all: match goal with
      Hih : forall _, _ -> locally_closed_tm _ |- _ => eapply Hih; eauto
    end.
  - constructor; eauto.
  - constructor.
    set (L' := L ++ fv_tm t ++ fv_ty T).
    assert (HX' : ~ In (S (fold_right Nat.max 0 L')) L') by apply fresh_notin.
    assert (HX : ~ In (S (fold_right Nat.max 0 L')) L) by
      (intro Hin; apply HX'; unfold L'; apply in_or_app; left; exact Hin).
    specialize (H0 (S (fold_right Nat.max 0 L')) HX).
    apply lc_tm_ty_open_inv with (X := S (fold_right Nat.max 0 L')); eauto.
    intro Hin; apply HX'; unfold L'; apply in_or_app; right; apply in_or_app; left; exact Hin.
  - constructor; eauto using wf_ty_lc.
  - constructor.
  - constructor.
  - constructor; eauto.
Qed.

(* Type-erasure is useful here because the candidates quantify over arbitrary
   predicates, while type substitution only changes annotations. *)
Fixpoint erase (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs _ t1 => tm_abs Ty_Bool (erase t1)
  | tm_app t1 t2 => tm_app (erase t1) (erase t2)
  | tm_tabs t1 => tm_tabs (erase t1)
  | tm_tapp t1 _ => tm_tapp (erase t1) Ty_Bool
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (erase t1) (erase t2) (erase t3)
  end.

Fixpoint subst_env (s : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => s x
  | tm_abs T t1 => tm_abs T (subst_env s t1)
  | tm_app t1 t2 => tm_app (subst_env s t1) (subst_env s t2)
  | tm_tabs t1 => tm_tabs (subst_env s t1)
  | tm_tapp t1 T => tm_tapp (subst_env s t1) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst_env s t1) (subst_env s t2) (subst_env s t3)
  end.

Definition env_up (s : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else s y.

Definition candidate (P : tm -> Prop) : Prop :=
  (forall t, P t -> locally_closed_tm t) /\
  (forall t, P t -> strongly_normalizing t) /\
  (forall t u, P t -> t --> u -> P u).

Fixpoint red (rho : atom -> tm -> Prop) (bs : list (tm -> Prop))
    (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_BVar i => match nth_error bs i with Some P => P t | None => False end
  | Ty_FVar X => rho X t
  | Ty_Arrow A B => locally_closed_tm t /\ strongly_normalizing t /\
      (forall u, red rho bs A u -> red rho bs B (tm_app t u))
  | Ty_All T1 => locally_closed_tm t /\ strongly_normalizing t /\
      (forall P, candidate P -> forall U, locally_closed_ty U ->
        red rho (P :: bs) T1 (tm_tapp t Ty_Bool))
  | Ty_Bool => locally_closed_tm t /\ strongly_normalizing t
  end.

Definition rho_ok (rho : atom -> tm -> Prop) : Prop :=
  forall X, candidate (rho X).

Definition stack_ok (bs : list (tm -> Prop)) : Prop :=
  forall P, In P bs -> candidate P.

Lemma red_lc : forall rho bs T t, rho_ok rho -> stack_ok bs ->
  red rho bs T t -> locally_closed_tm t.
Proof.
  intros rho bs T t OK R H; induction T in bs,t,H,R |- *; simpl in *.
  - destruct (nth_error bs n) as [P|] eqn:E.
    + apply (proj1 (R P (nth_error_In bs n E))); exact H.
    + contradiction.
  - eapply (proj1 (OK _)); exact H.
  - destruct H as [H _]; exact H.
  - destruct H as [H _]; exact H.
  - destruct H as [H _]; exact H.
Qed.

Lemma red_sn : forall rho bs T t, rho_ok rho -> stack_ok bs ->
  red rho bs T t -> strongly_normalizing t.
Proof.
  intros rho bs T t OK R H; induction T in bs,t,H,R |- *; simpl in *.
  - destruct (nth_error bs n) as [P|] eqn:E.
    + apply (proj2 (R P (nth_error_In bs n E))); exact H.
    + contradiction.
  - eapply (proj2 (OK _)); exact H.
  - destruct H as [_ [H _]]; exact H.
  - destruct H as [_ [H _]]; exact H.
  - destruct H as [_ H]; exact H.
Qed.

Lemma erase_lc_at : forall K k t,
  lc_tm_at K k t -> lc_tm_at K k (erase t).
Proof.
  intros K k t H; revert K k H; induction t; intros K0 k0 H0; simpl in *.
  - inversion H0; constructor; assumption.
  - constructor.
  - inversion H0. constructor.
    + constructor.
    + apply IHt; eauto.
  - inversion H0. constructor; eauto.
  - inversion H0. constructor; eauto.
  - inversion H0. constructor; eauto.
  - constructor.
  - constructor.
  - inversion H0. constructor; eauto.
Qed.

Lemma erase_lc : forall t, locally_closed_tm t -> locally_closed_tm (erase t).
Proof. intros; eapply erase_lc_at; eauto. Qed.

Lemma erase_open_tm_rec : forall k t u,
  erase (open_tm_rec k u t) = open_tm_rec k (erase u) (erase t).
Proof.
  intros k t u. revert k u; induction t; intros k0 u0; simpl.
  - destruct (Nat.eqb k0 n) eqn:E; simpl; reflexivity.
  - reflexivity.
  - f_equal; apply IHt.
  - f_equal.
    + apply IHt1.
    + apply IHt2.
  - f_equal; apply IHt.
  - f_equal; apply IHt.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1.
    + apply IHt2.
    + apply IHt3.
Qed.

Lemma erase_open_tm : forall t u,
  erase (open_tm t u) = open_tm (erase t) (erase u).
Proof. intros; unfold open_tm; apply erase_open_tm_rec. Qed.

Lemma erase_open_tm_ty_rec : forall k t U,
  erase (open_tm_ty_rec k U t) = open_tm_ty_rec k Ty_Bool (erase t).
Proof.
  intros k t U. revert k U; induction t; intros k0 U0; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; apply IHt.
  - f_equal.
    + apply IHt1.
    + apply IHt2.
  - f_equal; apply IHt.
  - f_equal; apply IHt.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1.
    + apply IHt2.
    + apply IHt3.
Qed.

Lemma erase_open_tm_ty : forall t U,
  erase (open_tm_ty t U) = open_tm_ty (erase t) Ty_Bool.
Proof. intros; unfold open_tm_ty; apply erase_open_tm_ty_rec. Qed.

Lemma erase_value : forall t, value t -> value (erase t).
Proof.
  intros t H; inversion H; subst t; simpl.
  - apply v_abs. change (locally_closed_tm (erase (tm_abs T t0))).
    apply erase_lc; assumption.
  - apply v_tabs. change (locally_closed_tm (erase (tm_tabs t0))).
    apply erase_lc; assumption.
  - apply v_true.
  - apply v_false.
Qed.

Lemma erase_step : forall t u, t --> u -> erase t --> erase u.
Proof.
  intros t u H; induction H; simpl.
  - rewrite erase_open_tm. constructor.
    + change (locally_closed_tm (erase (tm_abs T t))). apply erase_lc; assumption.
    + apply erase_value; assumption.
  - constructor.
    + apply IHstep.
    + change (locally_closed_tm (erase t2)). apply erase_lc; assumption.
  - constructor.
    + apply erase_value; assumption.
    + apply IHstep.
  - rewrite erase_open_tm_ty. constructor.
    + change (locally_closed_tm (erase (tm_tabs t))). apply erase_lc; assumption.
    + constructor.
  - constructor.
    + apply IHstep.
    + constructor.
  - constructor.
    + change (locally_closed_tm (erase t1)). apply erase_lc; assumption.
    + change (locally_closed_tm (erase t2)). apply erase_lc; assumption.
  - constructor.
    + change (locally_closed_tm (erase t1)). apply erase_lc; assumption.
    + change (locally_closed_tm (erase t2)). apply erase_lc; assumption.
  - constructor.
    + apply IHstep.
    + change (locally_closed_tm (erase t2)). apply erase_lc; assumption.
    + change (locally_closed_tm (erase t3)). apply erase_lc; assumption.
Qed.

Lemma sn_erase_back_gen : forall q, strongly_normalizing q ->
  forall t, erase t = q -> strongly_normalizing t.
Proof.
  intros q H; induction H as [q Hrec IH]; intros t Et.
  constructor; intros u Hu.
  eapply IH.
  - rewrite <- Et. apply erase_step; exact Hu.
  - reflexivity.
Qed.

Lemma sn_erase_back : forall t, strongly_normalizing (erase t) ->
  strongly_normalizing t.
Proof. intros; eapply sn_erase_back_gen; eauto. Qed.

Lemma value_lc : forall t, value t -> locally_closed_tm t.
Proof.
  intros t H; inversion H.
  - assumption.
  - assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_abs_body : forall T t, locally_closed_tm (tm_abs T t) ->
  lc_tm_at 0 1 t.
Proof. intros; inversion H; assumption. Qed.

Lemma lc_tabs_body : forall t, locally_closed_tm (tm_tabs t) ->
  lc_tm_at 1 0 t.
Proof. intros; inversion H; assumption. Qed.

Lemma lc_step : forall t u, locally_closed_tm t -> t --> u ->
  locally_closed_tm u.
Proof.
  intros t u L H; induction H.
  - inversion L. eapply lc_tm_open.
    + eauto using value_lc.
    + eauto using lc_abs_body.
  - inversion L. constructor.
    + apply IHstep; assumption.
    + assumption.
  - inversion L. constructor.
    + apply value_lc; assumption.
    + apply IHstep; assumption.
  - inversion L. eapply lc_tm_ty_open with (k := 0) (j := 0); eauto.
    all: eauto using lc_tabs_body.
  - inversion L. constructor.
    + apply IHstep; assumption.
    + assumption.
  - inversion L; assumption.
  - inversion L; assumption.
  - inversion L. constructor.
    + apply IHstep; assumption.
    + assumption.
    + assumption.
Qed.

Lemma stack_cons_ok : forall P bs, candidate P -> stack_ok bs ->
  stack_ok (P :: bs).
Proof.
  intros P bs HP HB Q [<-|H]; eauto.
Qed.

Lemma red_candidate : forall rho bs T,
  rho_ok rho -> stack_ok bs -> candidate (red rho bs T).
Proof.
  intros rho bs T OK SB; induction T in bs,SB |- *; unfold candidate; simpl.
  - destruct (nth_error bs n) as [P|] eqn:E.
    + change (candidate P). exact (SB P (nth_error_In bs n E)).
    + split.
      * intros; contradiction.
      * split.
        -- intros; contradiction.
        -- intros; contradiction.
  - change (candidate (rho a)). exact (OK a).
  - repeat split.
    + intros t H; exact (proj1 H).
    + intros t H; exact (proj2 H).
    + intros t u H St.
      destruct H as [HL [HS HB]].
      split; [apply lc_step with t | apply sn_step with t].
      * exact HL. * exact St.
      * intros v Hv.
        apply (proj2 (IH2 (bs := bs) SB)) with (t := tm_app t v).
        apply HB; exact Hv.
        apply ST_App1; [exact St | apply red_lc with (rho := rho) (bs := bs) (T := _) OK SB; exact Hv].
  - repeat split.
    + intros t H; exact (proj1 H).
    + intros t H; exact (proj2 H).
    + intros t u H St.
      destruct H as [HL [HS HB]].
      split; [apply lc_step with t | apply sn_step with t].
      * exact HL. * exact St.
      * intros P CP U HU.
        apply (proj2 (IH (bs := P :: bs) (stack_cons_ok P bs CP SB))) with
          (t := tm_tapp t Ty_Bool).
        apply HB; assumption.
        apply ST_TApp; [exact St | constructor].
  - repeat split.
    + intros t H; exact (proj1 H).
    + intros t H; exact (proj2 H).
    + intros t u H St.
      split; [apply lc_step with t | apply sn_step with t].
      * exact (proj1 H). * exact St.
      * exact St.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationIfHardTask.
