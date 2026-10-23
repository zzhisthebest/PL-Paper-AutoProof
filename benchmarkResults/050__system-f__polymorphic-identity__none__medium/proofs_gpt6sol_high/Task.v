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

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof. intros t v H; induction H; auto. Qed.

Lemma evaluates_lc : forall t v, evaluates t v -> locally_closed_tm t.
Proof.
  intros t v H; induction H.
  - now apply value_lc.
  - now constructor.
  - now constructor.
Qed.

Lemma multi_trans : forall x y z, x -->* y -> y -->* z -> x -->* z.
Proof.
  intros x y z H; induction H; intros H2; eauto using multi.
Qed.

Lemma multi_app1 : forall f f' arg,
  f -->* f' -> locally_closed_tm arg ->
  tm_app f arg -->* tm_app f' arg.
Proof.
  intros f f' arg H; induction H; intros Hlc.
  - constructor.
  - eapply multi_step; [eapply ST_App1; eauto|eauto].
Qed.

Lemma multi_app2 : forall f arg arg',
  value f -> arg -->* arg' -> tm_app f arg -->* tm_app f arg'.
Proof.
  intros f arg arg' Hv H; induction H.
  - constructor.
  - eapply multi_step; [eapply ST_App2; eauto|eauto].
Qed.

Lemma multi_tapp : forall f f' U,
  f -->* f' -> locally_closed_ty U ->
  tm_tapp f U -->* tm_tapp f' U.
Proof.
  intros f f' U H; induction H; intros Hlc.
  - constructor.
  - eapply multi_step; [eapply ST_TApp; eauto|eauto].
Qed.

Lemma evaluates_multi : forall t v, evaluates t v -> t -->* v.
Proof.
  intros t v H; induction H as
    [v Hv
    |f arg U body v result Hf IHf Ha IHa Hb IHb
    |f U body result Hf IHf HU Hb IHb].
  - constructor.
  - eapply multi_trans.
    + eapply multi_app1; [exact IHf|eapply evaluates_lc; eauto].
    + eapply multi_trans.
      * eapply multi_app2; [eapply evaluates_value; exact Hf|exact IHa].
      * eapply multi_step; [eapply ST_AppAbs; eauto using value_lc, evaluates_value|exact IHb].
  - eapply multi_trans.
    + eapply multi_tapp; eauto.
    + eapply multi_step; [eapply ST_TAppTabs; eauto using value_lc, evaluates_value|exact IHb].
Qed.

Lemma lc_ty_open_inv : forall k T X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  intros k T; revert k; induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst. apply Nat.eqb_neq in E. constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_open_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  intros t K k; revert K k; induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst. apply Nat.eqb_neq in E. constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  intros t K k; revert K k; induction t; intros K k X H; simpl in H.
  - inversion H; subst; constructor; assumption.
  - constructor.
  - inversion H; subst; constructor; eauto using lc_ty_open_inv.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto using lc_ty_open_inv.
Qed.

Lemma in_fold_max : forall L x, In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [->|Hin]; [lia|specialize (IH x Hin); lia].
Qed.

Lemma fresh_nat : forall L : list nat, exists x, ~ In x L.
Proof.
  intros L. exists (S (fold_right Nat.max 0 L)).
  intros Hin. apply in_fold_max in Hin. lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H as
    [Delta X Hin|Delta T1 T2 H1 IH1 H2 IH2|L Delta T H IH].
  - constructor.
  - constructor; assumption.
  - destruct (fresh_nat L) as [X HX].
    apply lc_ty_all. eapply lc_ty_open_inv. exact (IH X HX).
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H as
    [Delta Gamma x T Hlook Hw
    |L Delta Gamma T1 t2 T2 Hw Hbody IHbody
    |Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    |L Delta Gamma t T Hbody IHbody
    |Delta Gamma t T U Ht IHt HU].
  - constructor.
  - destruct (fresh_nat L) as [x Hx].
    apply lc_tm_abs; [apply wf_ty_lc with Delta; assumption|].
    eapply lc_tm_open_inv. exact (IHbody x Hx).
  - constructor; assumption.
  - destruct (fresh_nat L) as [X HX].
    apply lc_tm_tabs. eapply lc_tm_ty_open_inv. exact (IHbody X HX).
  - constructor; [assumption|eapply wf_ty_lc; eauto].
Qed.

Lemma value_relation_values : forall T eta rho v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  induction T; intros eta rho v1 v2 H; simpl in H.
  - destruct (nth_error eta n) as [a|] eqn:E; [exact (candidate_values a _ _ H)|contradiction].
  - destruct (rho a) as [b|] eqn:E; [exact (candidate_values b _ _ H)|contradiction].
  - tauto.
  - tauto.
Qed.

Lemma expression_of_values : forall T eta rho v1 v2,
  value_relation eta rho T v1 v2 -> expression_relation eta rho T v1 v2.
Proof.
  intros T eta rho v1 v2 H.
  unfold expression_relation, expression_lifting, results_match.
  destruct (value_relation_values T eta rho v1 v2 H) as [H1 H2].
  split; [now apply value_lc|].
  split; [now apply value_lc|].
  exists v1, v2. repeat split; eauto using EvalValue.
Qed.

Lemma expression_app : forall eta rho A B f1 f2 x1 x2,
  expression_relation eta rho (Ty_Arrow A B) f1 f2 ->
  expression_relation eta rho A x1 x2 ->
  expression_relation eta rho B (tm_app f1 x1) (tm_app f2 x2).
Proof.
  intros eta rho A B f1 f2 x1 x2
    [Hfc1 [Hfc2 [fv1 [fv2 [Hfe1 [Hfe2 Hfr]]]]]]
    [Hxc1 [Hxc2 [xv1 [xv2 [Hxe1 [Hxe2 Hxr]]]]]].
  simpl in Hfr. destruct Hfr as [_ [_ [U1 [body1 [U2 [body2
    [-> [-> Hbody]]]]]]]].
  pose proof (Hbody xv1 xv2 Hxr) as
    [Hbc1 [Hbc2 [bv1 [bv2 [Hbe1 [Hbe2 Hbr]]]]]].
  unfold expression_relation, expression_lifting, results_match.
  repeat split; try (constructor; assumption).
  exists bv1, bv2. repeat split; auto.
  - eapply EvalApp; eauto.
  - eapply EvalApp; eauto.
Qed.

Lemma expression_tapp : forall eta rho T f1 f2 U1 U2 a,
  expression_relation eta rho (Ty_All T) f1 f2 ->
  locally_closed_ty U1 -> locally_closed_ty U2 ->
  expression_lifting (value_relation (a :: eta) rho T)
    (tm_tapp f1 U1) (tm_tapp f2 U2).
Proof.
  intros eta rho T f1 f2 U1 U2 a
    [Hfc1 [Hfc2 [fv1 [fv2 [Hfe1 [Hfe2 Hfr]]]]]] HU1 HU2.
  simpl in Hfr. destruct Hfr as [_ [_ [body1 [body2 [-> [-> Hbody]]]]]].
  pose proof (Hbody U1 U2 a HU1 HU2) as
    [Hbc1 [Hbc2 [bv1 [bv2 [Hbe1 [Hbe2 Hbr]]]]]].
  unfold expression_lifting, results_match.
  split; [now constructor|].
  split; [now constructor|].
  exists bv1, bv2. repeat split; auto.
  - eapply EvalTApp; eauto.
  - eapply EvalTApp; eauto.
Qed.

Fixpoint instantiate_ty (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (instantiate_ty theta A) (instantiate_ty theta B)
  | Ty_All A => Ty_All (instantiate_ty theta A)
  end.

Fixpoint instantiate_tm (theta : atom -> ty) (sigma : atom -> tm)
    (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T b => tm_abs (instantiate_ty theta T) (instantiate_tm theta sigma b)
  | tm_app f x => tm_app (instantiate_tm theta sigma f) (instantiate_tm theta sigma x)
  | tm_tabs b => tm_tabs (instantiate_tm theta sigma b)
  | tm_tapp f T => tm_tapp (instantiate_tm theta sigma f) (instantiate_ty theta T)
  end.

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
  | tm_app f x => fv_tm f ++ fv_tm x
  | tm_tabs b => fv_tm b
  | tm_tapp f _ => fv_tm f
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T b => fv_ty T ++ ftv_tm b
  | tm_app f x => ftv_tm f ++ ftv_tm x
  | tm_tabs b => ftv_tm b
  | tm_tapp f T => ftv_tm f ++ fv_ty T
  end.

Definition update_ty (theta : atom -> ty) X U :=
  fun Y => if Nat.eqb X Y then U else theta Y.
Definition update_tm (sigma : atom -> tm) x v :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma open_ty_lc_id : forall K T U,
  lc_ty_at K T -> open_ty_rec K U T = T.
Proof.
  intros K T U H; induction H; simpl; f_equal; auto.
  - assert (k <> i) as Hneq by lia.
    apply Nat.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Lemma open_tm_lc_id : forall K k t u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros K k t u H; induction H; simpl; f_equal; auto.
  - assert (k <> i) as Hneq by lia.
    apply Nat.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Lemma open_tm_ty_lc_id : forall K k t U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  intros K k t U H; induction H; simpl; f_equal; auto using open_ty_lc_id.
Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T -> forall n, lc_ty_at (K+n) T.
Proof.
  intros K T H; induction H; intros n; constructor; eauto; lia.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
  forall K' k', lc_tm_at (K+K') (k+k') t.
Proof.
  intros K k t H; induction H; intros K' k'; constructor; eauto using lc_ty_weaken; try lia.
Qed.

Lemma lc_ty_any : forall T K, locally_closed_ty T -> lc_ty_at K T.
Proof.
  intros T K H. replace K with (0+K) by lia. now apply lc_ty_weaken.
Qed.

Lemma lc_tm_any : forall t K k, locally_closed_tm t -> lc_tm_at K k t.
Proof.
  intros t K k H. replace K with (0+K) by lia.
  replace k with (0+k) by lia. now apply lc_tm_weaken.
Qed.

Lemma instantiate_open_tm : forall t k x theta sigma v,
  ~ In x (fv_tm t) ->
  (forall y, locally_closed_tm (sigma y)) ->
  instantiate_tm theta (update_tm sigma x v)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (instantiate_tm theta sigma t).
Proof.
  induction t; intros k x theta sigma v Hfresh Hclosed; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold update_tm. now rewrite Nat.eqb_refl.
    + reflexivity.
  - assert (x <> a) as Hneq by (intros ->; apply Hfresh; auto).
    unfold update_tm. apply Nat.eqb_neq in Hneq. rewrite Hneq.
    symmetry. apply (open_tm_lc_id 0 k (sigma a) v).
    apply lc_tm_any. apply Hclosed.
  - f_equal. apply IHt; auto.
  - assert (~ In x (fv_tm t1) /\ ~ In x (fv_tm t2)) as [Hf Hx].
    { split; intro Hin; apply Hfresh; apply in_or_app; auto. }
    f_equal; [apply IHt1|apply IHt2]; auto.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
Qed.

Lemma instantiate_open_ty : forall T k X theta U,
  ~ In X (fv_ty T) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  instantiate_ty (update_ty theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k X theta U Hfresh Hclosed; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold update_ty. now rewrite Nat.eqb_refl.
    + reflexivity.
  - assert (X <> a) as Hneq by (intros ->; apply Hfresh; auto).
    unfold update_ty. apply Nat.eqb_neq in Hneq. rewrite Hneq.
    symmetry. apply (open_ty_lc_id k (theta a) U).
    apply lc_ty_any. apply Hclosed.
  - assert (~ In X (fv_ty T1) /\ ~ In X (fv_ty T2)) as [H1 H2].
    { split; intro Hin; apply Hfresh; apply in_or_app; auto. }
    f_equal; [apply IHT1|apply IHT2]; auto.
  - f_equal. apply IHT; auto.
Qed.

Lemma instantiate_open_tm_ty : forall t k X theta sigma U,
  ~ In X (ftv_tm t) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  (forall y, locally_closed_tm (sigma y)) ->
  instantiate_tm (update_ty theta X U) sigma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate_tm theta sigma t).
Proof.
  induction t; intros k X theta sigma U Hfresh Hty Htm; simpl in *.
  - reflexivity.
  - symmetry. apply (open_tm_ty_lc_id k 0 (sigma a) U).
    apply lc_tm_any. apply Htm.
  - assert (~ In X (fv_ty t) /\ ~ In X (ftv_tm t0)) as [H1 H2].
    { split; intro Hin; apply Hfresh; apply in_or_app; auto. }
    f_equal; [apply instantiate_open_ty|apply IHt]; auto.
  - assert (~ In X (ftv_tm t1) /\ ~ In X (ftv_tm t2)) as [H1 H2].
    { split; intro Hin; apply Hfresh; apply in_or_app; auto. }
    f_equal; [apply IHt1|apply IHt2]; auto.
  - f_equal. apply IHt; auto.
  - assert (~ In X (ftv_tm t) /\ ~ In X (fv_ty t0)) as [H1 H2].
    { split; intro Hin; apply Hfresh; apply in_or_app; auto. }
    f_equal; [apply IHt|apply instantiate_open_ty]; auto.
Qed.

Lemma instantiate_ty_lc : forall K T theta,
  lc_ty_at K T ->
  (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros K T theta H; induction H; intros Htheta; simpl.
  - constructor; assumption.
  - apply lc_ty_any. apply Htheta.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma instantiate_tm_lc : forall K k t theta sigma,
  lc_tm_at K k t ->
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (instantiate_tm theta sigma t).
Proof.
  intros K k t theta sigma H; induction H; intros Htheta Hsigma; simpl.
  - constructor; assumption.
  - apply lc_tm_any. apply Hsigma.
  - constructor; eauto using instantiate_ty_lc.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto using instantiate_ty_lc.
Qed.

Lemma lifting_iff : forall R S t1 t2,
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  expression_lifting R t1 t2 <-> expression_lifting S t1 t2.
Proof.
  intros R S t1 t2 H.
  unfold expression_lifting, results_match.
  split; intros [H1 [H2 [v1 [v2 [E1 [E2 Hr]]]]]];
    repeat split; auto; exists v1, v2; repeat split; auto;
    apply H; assumption.
Qed.

Lemma nth_error_prefix : forall k (xs ys : list binary_candidate) i,
  firstn k xs = firstn k ys -> i < k ->
  nth_error xs i = nth_error ys i.
Proof.
  induction k as [|k IH]; intros xs ys i Heq Hi; [lia|].
  destruct xs as [|x xs], ys as [|y ys]; simpl in Heq;
    try discriminate; destruct i as [|i]; simpl; auto.
  - now inversion Heq.
  - inversion Heq; subst. apply IH; auto; lia.
Qed.

Lemma value_relation_eta_prefix : forall T k eta1 eta2 rho v1 v2,
  lc_ty_at k T -> firstn k eta1 = firstn k eta2 ->
  (value_relation eta1 rho T v1 v2 <->
   value_relation eta2 rho T v1 v2).
Proof.
  induction T; intros k eta1 eta2 rho v1 v2 Hlc Hprefix;
    inversion Hlc; subst; simpl.
  - erewrite nth_error_prefix by eauto. reflexivity.
  - reflexivity.
  - assert (Hdom : forall p q,
        value_relation eta1 rho T1 p q <->
        value_relation eta2 rho T1 p q).
    { intros; eapply IHT1; eauto. }
    assert (Hcod : forall p q,
        value_relation eta1 rho T2 p q <->
        value_relation eta2 rho T2 p q).
    { intros; eapply IHT2; eauto. }
    split.
    + intros [Hv1 [Hv2 [U1 [b1 [U2 [b2 [E1 [E2 Hbody]]]]]]]].
      refine (conj Hv1 (conj Hv2 _)).
      exists U1, b1, U2, b2.
      refine (conj E1 (conj E2 _)). intros a1 a2 Ha.
      apply (lifting_iff _ _ _ _ Hcod).
      apply Hbody. apply Hdom. exact Ha.
    + intros [Hv1 [Hv2 [U1 [b1 [U2 [b2 [E1 [E2 Hbody]]]]]]]].
      refine (conj Hv1 (conj Hv2 _)).
      exists U1, b1, U2, b2.
      refine (conj E1 (conj E2 _)). intros a1 a2 Ha.
      apply (lifting_iff _ _ _ _ Hcod).
      apply Hbody. apply Hdom. exact Ha.
  - assert (Hrel : forall a p q,
        value_relation (a :: eta1) rho T p q <->
        value_relation (a :: eta2) rho T p q).
    { intros. eapply IHT; eauto. simpl. now f_equal. }
    split.
    + intros [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hbody]]]]]].
      refine (conj Hv1 (conj Hv2 _)). exists b1, b2.
      refine (conj E1 (conj E2 _)). intros U1 U2 a HU1 HU2.
      apply (lifting_iff _ _ _ _ (Hrel a)). apply Hbody; assumption.
    + intros [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hbody]]]]]].
      refine (conj Hv1 (conj Hv2 _)). exists b1, b2.
      refine (conj E1 (conj E2 _)). intros U1 U2 a HU1 HU2.
      apply (lifting_iff _ _ _ _ (Hrel a)). apply Hbody; assumption.
Qed.

Lemma value_relation_eta_irrelevant : forall T eta1 eta2 rho v1 v2,
  locally_closed_ty T ->
  (value_relation eta1 rho T v1 v2 <->
   value_relation eta2 rho T v1 v2).
Proof.
  intros. eapply value_relation_eta_prefix; eauto.
Qed.

Definition candidate_for (rho : binary_env) (U : ty) : binary_candidate :=
  {| candidate_relation := value_relation [] rho U;
     candidate_values := value_relation_values U [] rho |}.

Fixpoint insert_at (k : nat) (a : binary_candidate)
    (eta : list binary_candidate) : list binary_candidate :=
  match k, eta with
  | 0, _ => a :: eta
  | S k', b :: eta' => b :: insert_at k' a eta'
  | S _, [] => []
  end.

Lemma nth_error_insert_lt : forall k eta a i,
  i < k -> nth_error (insert_at k a eta) i = nth_error eta i.
Proof.
  induction k as [|k IH]; intros eta a i Hi; [lia|].
  destruct eta as [|b eta]; simpl; [reflexivity|].
  destruct i as [|i]; simpl; [reflexivity|apply IH; lia].
Qed.

Lemma nth_error_insert_eq : forall k eta a,
  k <= length eta -> nth_error (insert_at k a eta) k = Some a.
Proof.
  induction k as [|k IH]; intros eta a Hlen; simpl.
  - reflexivity.
  - destruct eta as [|b eta]; simpl in *; [lia|].
    apply IH. lia.
Qed.

Lemma value_relation_open_ty : forall T k eta rho U v1 v2,
  lc_ty_at (S k) T -> locally_closed_ty U -> k <= length eta ->
  (value_relation eta rho (open_ty_rec k U T) v1 v2 <->
   value_relation (insert_at k (candidate_for rho U) eta) rho T v1 v2).
Proof.
  induction T; intros k eta rho U v1 v2 Hlc HU Hlen;
    inversion Hlc; subst; simpl.
  - destruct (Nat.lt_trichotomy n k) as [Hlt|[Heq|Hgt]].
    + assert (E : Nat.eqb k n = false) by (apply Nat.eqb_neq; lia).
      rewrite E. simpl. rewrite nth_error_insert_lt by assumption.
      reflexivity.
    + subst n. rewrite Nat.eqb_refl. simpl.
      rewrite nth_error_insert_eq by assumption.
      unfold candidate_for; simpl.
      apply value_relation_eta_irrelevant; assumption.
    + lia.
  - reflexivity.
  - assert (Hdom : forall p q,
        value_relation eta rho (open_ty_rec k U T1) p q <->
        value_relation (insert_at k (candidate_for rho U) eta) rho T1 p q).
    { intros; eapply IHT1; eauto. }
    assert (Hcod : forall p q,
        value_relation eta rho (open_ty_rec k U T2) p q <->
        value_relation (insert_at k (candidate_for rho U) eta) rho T2 p q).
    { intros; eapply IHT2; eauto. }
    split.
    + intros [Hv1 [Hv2 [A [b1 [B [b2 [E1 [E2 Hbody]]]]]]]].
      refine (conj Hv1 (conj Hv2 _)). exists A, b1, B, b2.
      refine (conj E1 (conj E2 _)). intros x1 x2 Hx.
      apply (lifting_iff _ _ _ _ Hcod).
      apply Hbody. apply Hdom. exact Hx.
    + intros [Hv1 [Hv2 [A [b1 [B [b2 [E1 [E2 Hbody]]]]]]]].
      refine (conj Hv1 (conj Hv2 _)). exists A, b1, B, b2.
      refine (conj E1 (conj E2 _)). intros x1 x2 Hx.
      apply (lifting_iff _ _ _ _ Hcod).
      apply Hbody. apply Hdom. exact Hx.
  - assert (Hrel : forall a p q,
        value_relation (a :: eta) rho (open_ty_rec (S k) U T) p q <->
        value_relation (a :: insert_at k (candidate_for rho U) eta) rho T p q).
    { intros. change (a :: insert_at k (candidate_for rho U) eta)
        with (insert_at (S k) (candidate_for rho U) (a :: eta)).
      apply IHT; eauto. simpl; lia. }
    split.
    + intros [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hbody]]]]]].
      refine (conj Hv1 (conj Hv2 _)). exists b1, b2.
      refine (conj E1 (conj E2 _)). intros U1 U2 a HU1 HU2.
      apply (lifting_iff _ _ _ _ (Hrel a)). exact (Hbody U1 U2 a HU1 HU2).
    + intros [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hbody]]]]]].
      refine (conj Hv1 (conj Hv2 _)). exists b1, b2.
      refine (conj E1 (conj E2 _)). intros U1 U2 a HU1 HU2.
      apply (lifting_iff _ _ _ _ (Hrel a)). exact (Hbody U1 U2 a HU1 HU2).
Qed.

Lemma open_ty_lc : forall k T U,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k T; revert k. induction T; intros k U HT HU;
    inversion HT; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_ty_any. exact HU.
    + apply Nat.eqb_neq in E. constructor. lia.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma has_type_result_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H as
    [Delta Gamma x T Hlook Hw
    |L Delta Gamma T1 t2 T2 Hw Hbody IHbody
    |Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    |L Delta Gamma t T Hbody IHbody
    |Delta Gamma t T U Ht IHt HU].
  - now apply wf_ty_lc with Delta.
  - destruct (fresh_nat L) as [x Hx].
    constructor; [now apply wf_ty_lc with Delta|exact (IHbody x Hx)].
  - inversion IH1; subst; assumption.
  - destruct (fresh_nat L) as [X HX].
    constructor. eapply lc_ty_open_inv. exact (IHbody X HX).
  - inversion IHt; subst. eapply open_ty_lc; eauto using wf_ty_lc.
Qed.

Lemma value_relation_open_fvar : forall T k eta rho X cand v1 v2,
  lc_ty_at (S k) T -> ~ In X (fv_ty T) -> k <= length eta ->
  (value_relation eta (relation_update rho X cand)
      (open_ty_rec k (Ty_FVar X) T) v1 v2 <->
   value_relation (insert_at k cand eta) rho T v1 v2).
Proof.
  induction T; intros k eta rho X cand v1 v2 Hlc Hfresh Hlen;
    inversion Hlc; subst; simpl in *.
  - destruct (Nat.lt_trichotomy n k) as [Hlt|[Heq|Hgt]].
    + assert (E : Nat.eqb k n = false) by (apply Nat.eqb_neq; lia).
      rewrite E. simpl. rewrite nth_error_insert_lt by assumption.
      reflexivity.
    + subst n. rewrite Nat.eqb_refl. simpl.
      rewrite nth_error_insert_eq by assumption.
      unfold relation_update. now rewrite Nat.eqb_refl.
    + lia.
  - assert (X <> a) as Hneq by (intros ->; apply Hfresh; auto).
    unfold relation_update. apply Nat.eqb_neq in Hneq.
    now rewrite Hneq.
  - assert (~ In X (fv_ty T1) /\ ~ In X (fv_ty T2)) as [Hf1 Hf2].
    { split; intro Hin; apply Hfresh; apply in_or_app; auto. }
    assert (Hdom : forall p q,
        value_relation eta (relation_update rho X cand)
          (open_ty_rec k (Ty_FVar X) T1) p q <->
        value_relation (insert_at k cand eta) rho T1 p q).
    { intros; eapply IHT1; eauto. }
    assert (Hcod : forall p q,
        value_relation eta (relation_update rho X cand)
          (open_ty_rec k (Ty_FVar X) T2) p q <->
        value_relation (insert_at k cand eta) rho T2 p q).
    { intros; eapply IHT2; eauto. }
    split.
    + intros [Hv1 [Hv2 [A [b1 [B [b2 [E1 [E2 Hbody]]]]]]]].
      refine (conj Hv1 (conj Hv2 _)). exists A, b1, B, b2.
      refine (conj E1 (conj E2 _)). intros x1 x2 Hx.
      apply (lifting_iff _ _ _ _ Hcod).
      apply Hbody. apply Hdom. exact Hx.
    + intros [Hv1 [Hv2 [A [b1 [B [b2 [E1 [E2 Hbody]]]]]]]].
      refine (conj Hv1 (conj Hv2 _)). exists A, b1, B, b2.
      refine (conj E1 (conj E2 _)). intros x1 x2 Hx.
      apply (lifting_iff _ _ _ _ Hcod).
      apply Hbody. apply Hdom. exact Hx.
  - assert (Hrel : forall b p q,
        value_relation (b :: eta) (relation_update rho X cand)
          (open_ty_rec (S k) (Ty_FVar X) T) p q <->
        value_relation (b :: insert_at k cand eta) rho T p q).
    { intros. change (b :: insert_at k cand eta)
        with (insert_at (S k) cand (b :: eta)).
      apply IHT; eauto. simpl; lia. }
    split.
    + intros [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hbody]]]]]].
      refine (conj Hv1 (conj Hv2 _)). exists b1, b2.
      refine (conj E1 (conj E2 _)). intros U1 U2 b HU1 HU2.
      apply (lifting_iff _ _ _ _ (Hrel b)). exact (Hbody U1 U2 b HU1 HU2).
    + intros [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hbody]]]]]].
      refine (conj Hv1 (conj Hv2 _)). exists b1, b2.
      refine (conj E1 (conj E2 _)). intros U1 U2 b HU1 HU2.
      apply (lifting_iff _ _ _ _ (Hrel b)). exact (Hbody U1 U2 b HU1 HU2).
Qed.

Lemma value_relation_rho_fresh : forall T eta rho X a v1 v2,
  locally_closed_ty T -> ~ In X (fv_ty T) ->
  (value_relation eta (relation_update rho X a) T v1 v2 <->
   value_relation eta rho T v1 v2).
Proof.
  intros T eta rho X a v1 v2 HT Hfresh.
  pose proof (value_relation_open_fvar T 0 eta rho X a v1 v2
    (lc_ty_any T 1 HT) Hfresh (Nat.le_0_l _)) as Hopen.
  simpl in Hopen. rewrite (open_ty_lc_id 0 T (Ty_FVar X) HT) in Hopen.
  eapply iff_trans; [exact Hopen|].
  apply value_relation_eta_irrelevant; assumption.
Qed.

Fixpoint fv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fv_ty T ++ fv_context Gamma'
  end.

Lemma lookup_fv_context : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  In X (fv_ty T) -> In X (fv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlook Hin;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst. apply in_or_app; auto.
  - apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma not_in_app_parts : forall (A B : list atom) x,
  ~ In x (A ++ B) -> ~ In x A /\ ~ In x B.
Proof.
  intros A B x H; split; intro Hin; apply H; apply in_or_app; auto.
Qed.

Theorem fundamental_relation : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall eta rho theta1 theta2 sigma1 sigma2,
    (forall X, locally_closed_ty (theta1 X)) ->
    (forall X, locally_closed_ty (theta2 X)) ->
    (forall x, locally_closed_tm (sigma1 x)) ->
    (forall x, locally_closed_tm (sigma2 x)) ->
    (forall x U, lookup_context x Gamma = Some U -> locally_closed_ty U) ->
    (forall x U, lookup_context x Gamma = Some U ->
       value_relation eta rho U (sigma1 x) (sigma2 x)) ->
    expression_relation eta rho T
      (instantiate_tm theta1 sigma1 t)
      (instantiate_tm theta2 sigma2 t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [Delta Gamma x T Hlook Hw
    |L Delta Gamma T1 t2 T2 Hw Hbody IHbody
    |Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    |L Delta Gamma t T Hbody IHbody
    |Delta Gamma t T U Ht IHt HU];
    intros eta rho theta1 theta2 sigma1 sigma2
      Htheta1 Htheta2 Hsigma1 Hsigma2 Hctxlc Hctxrel;
    simpl.
  - apply expression_of_values. apply Hctxrel; assumption.
  - assert (Hlc : locally_closed_tm (tm_abs T1 t2)).
    { eapply has_type_lc. eapply T_Abs; eauto. }
    assert (Hvl : value (tm_abs (instantiate_ty theta1 T1)
                                (instantiate_tm theta1 sigma1 t2))).
    { constructor. change (locally_closed_tm
        (instantiate_tm theta1 sigma1 (tm_abs T1 t2))).
      eapply instantiate_tm_lc; eauto. }
    assert (Hvr : value (tm_abs (instantiate_ty theta2 T1)
                                (instantiate_tm theta2 sigma2 t2))).
    { constructor. change (locally_closed_tm
        (instantiate_tm theta2 sigma2 (tm_abs T1 t2))).
      eapply instantiate_tm_lc; eauto. }
    apply expression_of_values. simpl.
    refine (conj Hvl (conj Hvr _)).
    exists (instantiate_ty theta1 T1), (instantiate_tm theta1 sigma1 t2),
      (instantiate_ty theta2 T1), (instantiate_tm theta2 sigma2 t2).
    refine (conj eq_refl (conj eq_refl _)).
    intros arg1 arg2 Harg.
    destruct (value_relation_values T1 eta rho arg1 arg2 Harg) as [Ha1 Ha2].
    destruct (fresh_nat (L ++ fv_tm t2)) as [x Hfresh].
    destruct (not_in_app_parts L (fv_tm t2) x Hfresh) as [HxL Hxt].
    pose proof (IHbody x HxL eta rho theta1 theta2
      (update_tm sigma1 x arg1) (update_tm sigma2 x arg2)
      Htheta1 Htheta2) as Hsem.
    assert (Hs1 : forall y, locally_closed_tm (update_tm sigma1 x arg1 y)).
    { intro y. unfold update_tm. destruct (Nat.eqb x y);
        auto using value_lc. }
    assert (Hs2 : forall y, locally_closed_tm (update_tm sigma2 x arg2 y)).
    { intro y. unfold update_tm. destruct (Nat.eqb x y);
        auto using value_lc. }
    specialize (Hsem Hs1 Hs2).
    assert (Hcl : forall y V,
      lookup_context y (update Gamma x T1) = Some V -> locally_closed_ty V).
    { intros y V Hlookup. unfold update in Hlookup; simpl in Hlookup.
      destruct (Nat.eqb y x) eqn:E; [inversion Hlookup; subst;
        now apply wf_ty_lc with Delta|eauto]. }
    assert (Hcr : forall y V,
      lookup_context y (update Gamma x T1) = Some V ->
      value_relation eta rho V (update_tm sigma1 x arg1 y)
        (update_tm sigma2 x arg2 y)).
    { intros y V Hlookup. unfold update in Hlookup; simpl in Hlookup.
      destruct (Nat.eqb y x) eqn:E.
      - inversion Hlookup; subst. apply Nat.eqb_eq in E; subst y.
        unfold update_tm. now rewrite Nat.eqb_refl.
      - apply Nat.eqb_neq in E. unfold update_tm.
        assert (Ex : Nat.eqb x y = false) by (apply Nat.eqb_neq; lia).
        rewrite Ex. apply Hctxrel. exact Hlookup. }
    specialize (Hsem Hcl Hcr).
    unfold expression_relation in Hsem.
    unfold open_tm in Hsem.
    rewrite (instantiate_open_tm t2 0 x theta1 sigma1 arg1 Hxt Hsigma1) in Hsem.
    rewrite (instantiate_open_tm t2 0 x theta2 sigma2 arg2 Hxt Hsigma2) in Hsem.
    exact Hsem.
  - eapply expression_app; [eapply IH1|eapply IH2]; eauto.
  - (* Type abstraction. *)
    assert (Hlc : locally_closed_tm (tm_tabs t)).
    { eapply has_type_lc. eapply T_TAbs; eauto. }
    assert (Hvl : value (tm_tabs (instantiate_tm theta1 sigma1 t))).
    { constructor. change (locally_closed_tm
        (instantiate_tm theta1 sigma1 (tm_tabs t))).
      eapply instantiate_tm_lc; eauto. }
    assert (Hvr : value (tm_tabs (instantiate_tm theta2 sigma2 t))).
    { constructor. change (locally_closed_tm
        (instantiate_tm theta2 sigma2 (tm_tabs t))).
      eapply instantiate_tm_lc; eauto. }
    apply expression_of_values. simpl.
    refine (conj Hvl (conj Hvr _)).
    exists (instantiate_tm theta1 sigma1 t), (instantiate_tm theta2 sigma2 t).
    refine (conj eq_refl (conj eq_refl _)).
    intros U1 U2 cand HU1 HU2.
    destruct (fresh_nat
      (L ++ ftv_tm t ++ fv_ty T ++ fv_context Gamma)) as [X Hfresh].
    destruct (not_in_app_parts L
      (ftv_tm t ++ fv_ty T ++ fv_context Gamma) X Hfresh) as [HXL Hrest].
    destruct (not_in_app_parts (ftv_tm t)
      (fv_ty T ++ fv_context Gamma) X Hrest) as [HXt Hrest2].
    destruct (not_in_app_parts (fv_ty T) (fv_context Gamma) X Hrest2)
      as [HXT HXGamma].
    assert (Ht1 : forall Y, locally_closed_ty (update_ty theta1 X U1 Y)).
    { intro Y. unfold update_ty. destruct (Nat.eqb X Y); auto. }
    assert (Ht2 : forall Y, locally_closed_ty (update_ty theta2 X U2 Y)).
    { intro Y. unfold update_ty. destruct (Nat.eqb X Y); auto. }
    assert (Hcr : forall y V, lookup_context y Gamma = Some V ->
      value_relation eta (relation_update rho X cand) V
        (sigma1 y) (sigma2 y)).
    { intros y V Hlookup.
      apply (value_relation_rho_fresh V eta rho X cand (sigma1 y) (sigma2 y)).
      - apply Hctxlc with y; assumption.
      - intro Hin. apply HXGamma. eapply lookup_fv_context; eauto.
      - apply Hctxrel; assumption. }
    pose proof (IHbody X HXL eta (relation_update rho X cand)
      (update_ty theta1 X U1) (update_ty theta2 X U2)
      sigma1 sigma2 Ht1 Ht2 Hsigma1 Hsigma2 Hctxlc Hcr) as Hsem.
    unfold expression_relation, open_tm_ty in Hsem.
    rewrite (instantiate_open_tm_ty t 0 X theta1 sigma1 U1 HXt
      Htheta1 Hsigma1) in Hsem.
    rewrite (instantiate_open_tm_ty t 0 X theta2 sigma2 U2 HXt
      Htheta2 Hsigma2) in Hsem.
    unfold open_ty in Hsem.
    assert (HTlc : lc_ty_at 1 T).
    { apply lc_ty_open_inv with X.
      eapply has_type_result_lc. apply Hbody. exact HXL. }
    apply (lifting_iff _ _ _ _
      (fun p q => value_relation_open_fvar T 0 eta rho X cand p q
        HTlc HXT (Nat.le_0_l _))).
    exact Hsem.
  - (* Type application. *)
    assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
    assert (HU1 : locally_closed_ty (instantiate_ty theta1 U)).
    { eapply instantiate_ty_lc; eauto. }
    assert (HU2 : locally_closed_ty (instantiate_ty theta2 U)).
    { eapply instantiate_ty_lc; eauto. }
    pose proof (IHt eta rho theta1 theta2 sigma1 sigma2
      Htheta1 Htheta2 Hsigma1 Hsigma2 Hctxlc Hctxrel) as Hfun.
    pose proof (expression_tapp eta rho T
      (instantiate_tm theta1 sigma1 t)
      (instantiate_tm theta2 sigma2 t)
      (instantiate_ty theta1 U) (instantiate_ty theta2 U)
      (candidate_for rho U) Hfun HU1 HU2) as Hres.
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (has_type_result_lc Delta Gamma t (Ty_All T) Ht)
        as Htylc. inversion Htylc; assumption. }
    unfold expression_relation, open_ty.
    apply (lifting_iff _ _ _ _
      (fun p q => value_relation_open_ty T 0 eta rho U p q
        HTlc HUlc (Nat.le_0_l _))).
    exact Hres.
Qed.

Lemma instantiate_identity_ty : forall T,
  instantiate_ty (fun X => Ty_FVar X) T = T.
Proof. induction T; simpl; f_equal; auto. Qed.

Lemma instantiate_identity_tm : forall t,
  instantiate_tm (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; f_equal; auto using instantiate_identity_ty.
Qed.

Definition singleton_candidate (v : tm) (Hv : value v) : binary_candidate.
Proof.
  refine {| candidate_relation := fun p q => p = v /\ q = v |}.
  intros p q [-> ->]. split; exact Hv.
Defined.

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
  pose proof (fundamental_relation [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
    [] (fun _ => None)
    (fun X => Ty_FVar X) (fun X => Ty_FVar X)
    (fun x => tm_fvar x) (fun x => tm_fvar x)) as Hfund.
  assert (Htheta : forall X, locally_closed_ty (Ty_FVar X)).
  { intro X; constructor. }
  assert (Hsigma : forall x, locally_closed_tm (tm_fvar x)).
  { intro x; constructor. }
  specialize (Hfund Htheta Htheta Hsigma Hsigma).
  assert (Hemptylc : forall x V,
    lookup_context x empty = Some V -> locally_closed_ty V).
  { intros x V H; discriminate. }
  assert (Hemptyrel : forall x V,
    lookup_context x empty = Some V ->
    value_relation [] (fun _ => None) V (tm_fvar x) (tm_fvar x)).
  { intros x V H; discriminate. }
  specialize (Hfund Hemptylc Hemptyrel).
  repeat rewrite instantiate_identity_tm in Hfund.
  assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
  pose (cand := singleton_candidate v Hv).
  pose proof (expression_tapp [] (fun _ => None)
    (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)) t t U U cand
    Hfund HUlc HUlc) as Htap.
  assert (Hvrel : expression_relation [cand] (fun _ => None)
    (Ty_BVar 0) v v).
  { apply expression_of_values. simpl. split; reflexivity. }
  pose proof (expression_app [cand] (fun _ => None)
    (Ty_BVar 0) (Ty_BVar 0)
    (tm_tapp t U) (tm_tapp t U) v v Htap Hvrel) as Happ.
  destruct Happ as [_ [_ [r1 [r2 [Heval [_ Hr]]]]]].
  simpl in Hr. destruct Hr as [-> _].
  now apply evaluates_multi.
Qed.

End SystemFParametricityNoneMediumTask.
