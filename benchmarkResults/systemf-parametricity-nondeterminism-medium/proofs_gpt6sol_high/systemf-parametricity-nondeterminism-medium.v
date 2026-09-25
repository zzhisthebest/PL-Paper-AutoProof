(** System F parametricity benchmark, Medium variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNondeterminismMediumTask.

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

Inductive evaluates : tm -> tm -> Prop :=
  | EvalValue : forall v, value v -> evaluates v v
  | EvalApp : forall f arg U body v result,
      evaluates f (tm_abs U body) -> evaluates arg v ->
      evaluates (open_tm body v) result -> evaluates (tm_app f arg) result
  | EvalTApp : forall f U body result,
      evaluates f (tm_tabs body) -> locally_closed_ty U ->
      evaluates (open_tm_ty body U) result -> evaluates (tm_tapp f U) result
  | EvalChoiceLeft : forall t1 t2 v,
      evaluates t1 v -> locally_closed_tm t2 -> evaluates (tm_choice t1 t2) v
  | EvalChoiceRight : forall t1 t2 v,
      locally_closed_tm t1 -> evaluates t2 v -> evaluates (tm_choice t1 t2) v.

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

Fixpoint instantiate_ty (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (instantiate_ty theta A) (instantiate_ty theta B)
  | Ty_All A => Ty_All (instantiate_ty theta A)
  end.

Fixpoint instantiate_tm (theta : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T body => tm_abs (instantiate_ty theta T) (instantiate_tm theta sigma body)
  | tm_app f a => tm_app (instantiate_tm theta sigma f) (instantiate_tm theta sigma a)
  | tm_tabs body => tm_tabs (instantiate_tm theta sigma body)
  | tm_tapp f U => tm_tapp (instantiate_tm theta sigma f) (instantiate_ty theta U)
  | tm_choice l r => tm_choice (instantiate_tm theta sigma l) (instantiate_tm theta sigma r)
  end.

Fixpoint ty_names (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_names A ++ ty_names B
  | Ty_All A => ty_names A
  end.

Fixpoint term_names (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ body | tm_tabs body => term_names body
  | tm_app f a | tm_choice f a => term_names f ++ term_names a
  | tm_tapp f _ => term_names f
  end.

Fixpoint term_type_names (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T body => ty_names T ++ term_type_names body
  | tm_app f a | tm_choice f a => term_type_names f ++ term_type_names a
  | tm_tabs body => term_type_names body
  | tm_tapp f U => term_type_names f ++ ty_names U
  end.

Definition fresh (L : list atom) := S (fold_right Nat.max 0 L).

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  assert (Hbound : forall L x, In x L -> x <= fold_right Nat.max 0 L).
  { induction L as [|y L IH]; intros x H; simpl in *.
    - contradiction.
    - destruct H as [->|H]; [lia|]. specialize (IH x H); lia. }
  intros L H; specialize (Hbound L (fresh L) H); unfold fresh in *; lia.
Qed.

Lemma not_in_append : forall (A B : list atom) x,
  ~ In x (A ++ B) -> ~ In x A /\ ~ In x B.
Proof. intros A B x H; split; intro Hin; apply H; apply in_or_app; auto. Qed.

Lemma lc_ty_raise : forall k K T, lc_ty_at k T -> k <= K -> lc_ty_at K T.
Proof.
  intros k K T H; revert K; induction H; intros K' Hle.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all; apply IHlc_ty_at; lia.
Qed.

Lemma lc_ty_weaken : forall k T, lc_ty_at 0 T -> lc_ty_at k T.
Proof. intros; eapply lc_ty_raise; eauto; lia. Qed.

Lemma lc_tm_raise : forall K k K' k' t, lc_tm_at K k t ->
  K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k K' k' t H; revert K' k'; induction H; intros K' k' HK Hk.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_raise; eauto.
    + apply IHlc_tm_at; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs; apply IHlc_tm_at; lia.
  - apply lc_tm_tapp; eauto using lc_ty_raise.
  - apply lc_tm_choice; eauto.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at 0 0 t -> lc_tm_at K k t.
Proof. intros; eapply lc_tm_raise; eauto; lia. Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma instantiate_ty_lc : forall theta k T,
  (forall X, locally_closed_ty (theta X)) -> lc_ty_at k T ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  intros theta k T Htheta H; induction H; simpl.
  - apply lc_ty_bvar; auto.
  - apply lc_ty_weaken; exact (Htheta X).
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all; auto.
Qed.

Lemma instantiate_tm_lc : forall theta sigma K k t,
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate_tm theta sigma t).
Proof.
  intros theta sigma K k t Htheta Hsigma H; induction H; simpl.
  - apply lc_tm_bvar; auto.
  - apply lc_tm_weaken; exact (Hsigma x).
  - apply lc_tm_abs; eauto using instantiate_ty_lc.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs; auto.
  - apply lc_tm_tapp; eauto using instantiate_ty_lc.
  - apply lc_tm_choice; auto.
Qed.

Lemma lc_ty_close : forall k T X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  intros k T; revert k; induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; apply lc_ty_bvar; lia.
    + inversion H; subst; apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - inversion H; subst; apply lc_ty_arrow; eauto.
  - inversion H; subst; apply lc_ty_all; eauto.
Qed.

Lemma lc_tm_close : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k; induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; apply lc_tm_bvar; lia.
    + inversion H; subst; apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - inversion H; subst; apply lc_tm_abs; eauto.
  - inversion H; subst; apply lc_tm_app; eauto.
  - inversion H; subst; apply lc_tm_tabs; eauto.
  - inversion H; subst; apply lc_tm_tapp; eauto.
  - inversion H; subst; apply lc_tm_choice; eauto.
Qed.

Lemma lc_tm_ty_close : forall K k t X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  intros K k t; revert K k; induction t; intros K k X H; simpl in H.
  - inversion H; subst; apply lc_tm_bvar; auto.
  - apply lc_tm_fvar.
  - inversion H; subst; apply lc_tm_abs.
    + eapply lc_ty_close; eauto.
    + eauto.
  - inversion H; subst; apply lc_tm_app; eauto.
  - inversion H; subst; apply lc_tm_tabs; eauto.
  - inversion H; subst; apply lc_tm_tapp; eauto using lc_ty_close.
  - inversion H; subst; apply lc_tm_choice; eauto.
Qed.

Lemma wf_ty_closed : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all. pose (X := fresh L).
    apply (lc_ty_close 0 T X). apply H0.
    apply fresh_not_in.
Qed.

Lemma has_type_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply wf_ty_closed with (Delta := Delta); auto.
    + pose (x := fresh L). apply (lc_tm_close 0 0 t2 x).
      apply H1. apply fresh_not_in.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. pose (X := fresh L).
    apply (lc_tm_ty_close 0 0 t X). apply H0. apply fresh_not_in.
  - apply lc_tm_tapp; [assumption|eapply wf_ty_closed; eauto].
  - apply lc_tm_choice; auto.
Qed.

Lemma relation_values : forall T eta rho v1 v2,
  (forall a, In a eta -> forall w1 w2, candidate_relation a w1 w2 -> value w1 /\ value w2) ->
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  induction T; intros eta rho v1 v2 Heta H; simpl in H.
  - destruct (nth_error eta n) as [a|] eqn:E; [|contradiction].
    apply Heta with (a := a).
    + eapply nth_error_In; eauto.
    + exact H.
  - destruct (rho a) as [c|] eqn:E; [|contradiction].
    exact (candidate_values c _ _ H).
  - tauto.
  - tauto.
Qed.

Lemma eval_closed : forall t v, evaluates t v -> locally_closed_tm t /\ value v.
Proof.
  intros t v H; induction H.
  - split; auto using value_closed.
  - destruct IHevaluates1 as [Hf _]. destruct IHevaluates2 as [Ha _].
    destruct IHevaluates3 as [_ Hv]; split; [apply lc_tm_app; assumption|assumption].
  - destruct IHevaluates1 as [Hf _]. destruct IHevaluates2 as [_ Hv];
      split; [apply lc_tm_tapp; assumption|assumption].
  - destruct IHevaluates as [Ht Hv]; split; [apply lc_tm_choice; assumption|assumption].
  - destruct IHevaluates as [Ht Hv]; split; [apply lc_tm_choice; assumption|assumption].
Qed.

Lemma open_ty_closed : forall k U T,
  lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  intros k U T H; induction H; simpl; auto.
  - destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - now rewrite IHlc_ty_at1, IHlc_ty_at2.
  - now rewrite IHlc_ty_at.
Qed.

Lemma open_tm_closed : forall K k u t,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros K k u t H; induction H; simpl; auto.
  - destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - now rewrite IHlc_tm_at.
  - now rewrite IHlc_tm_at1, IHlc_tm_at2.
  - now rewrite IHlc_tm_at.
  - now rewrite IHlc_tm_at.
  - now rewrite IHlc_tm_at1, IHlc_tm_at2.
Qed.

Lemma open_tm_ty_closed : forall K k U t,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  intros K k U t H; induction H; simpl; auto.
  - rewrite (open_ty_closed _ _ _ H), IHlc_tm_at; reflexivity.
  - now rewrite IHlc_tm_at1, IHlc_tm_at2.
  - now rewrite IHlc_tm_at.
  - rewrite IHlc_tm_at, (open_ty_closed _ _ _ H0); reflexivity.
  - now rewrite IHlc_tm_at1, IHlc_tm_at2.
Qed.

Definition ty_override (theta : atom -> ty) X U :=
  fun Y => if Nat.eqb X Y then U else theta Y.
Definition tm_override (sigma : atom -> tm) x v :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma instantiate_ty_open : forall T theta X U k,
  ~ In X (ty_names T) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  locally_closed_ty U ->
  instantiate_ty (ty_override theta X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros theta X U k Hfresh Htheta HU; simpl in *.
  - destruct (Nat.eqb k n); simpl; auto.
    unfold ty_override; now rewrite Nat.eqb_refl.
  - assert (X <> a) by (intro E; subst; apply Hfresh; auto).
    unfold ty_override; destruct (Nat.eqb X a) eqn:E;
      [apply Nat.eqb_eq in E; contradiction|].
    symmetry; apply open_ty_closed; apply lc_ty_weaken; apply Htheta.
  - apply not_in_append in Hfresh as [H1 H2].
    now rewrite IHT1, IHT2 by auto.
  - now rewrite IHT by auto.
Qed.

Lemma instantiate_tm_open : forall t theta sigma x v k,
  ~ In x (term_names t) ->
  (forall y, locally_closed_tm (sigma y)) ->
  locally_closed_tm v ->
  instantiate_tm theta (tm_override sigma x v)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (instantiate_tm theta sigma t).
Proof.
  induction t; intros theta sigma x v k Hfresh Hsigma Hv; simpl in *.
  - destruct (Nat.eqb k n); simpl; auto.
    unfold tm_override; now rewrite Nat.eqb_refl.
  - assert (x <> a) by (intro E; subst; apply Hfresh; auto).
    unfold tm_override; destruct (Nat.eqb x a) eqn:E;
      [apply Nat.eqb_eq in E; contradiction|].
    symmetry; rewrite (open_tm_closed 0 k v (sigma a)).
    + reflexivity.
    + apply lc_tm_weaken; apply Hsigma.
  - f_equal; eauto.
  - apply not_in_append in Hfresh as [H1 H2]; f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - apply not_in_append in Hfresh as [H1 H2]; f_equal; eauto.
Qed.

Lemma instantiate_tm_ty_open : forall t theta sigma X U k,
  ~ In X (term_type_names t) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  (forall y, locally_closed_tm (sigma y)) ->
  locally_closed_ty U ->
  instantiate_tm (ty_override theta X U) sigma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate_tm theta sigma t).
Proof.
  induction t; intros theta sigma X U k Hfresh Htheta Hsigma HU; simpl in *; auto.
  - symmetry; rewrite (open_tm_ty_closed k 0 U (sigma a)).
    + reflexivity.
    + apply lc_tm_weaken; apply Hsigma.
  - apply not_in_append in Hfresh as [H1 H2]; f_equal;
      eauto using instantiate_ty_open.
  - apply not_in_append in Hfresh as [H1 H2]; f_equal; eauto.
  - f_equal; eauto.
  - apply not_in_append in Hfresh as [H1 H2]; f_equal;
      eauto using instantiate_ty_open.
  - apply not_in_append in Hfresh as [H1 H2]; f_equal; eauto.
Qed.

Lemma lifting_equiv : forall R S,
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  forall t1 t2, expression_lifting R t1 t2 <-> expression_lifting S t1 t2.
Proof.
  intros R S H t1 t2; unfold expression_lifting, results_match.
  split; intros [H1 [H2 [v1 [v2 [He1 [He2 HR]]]]]];
    repeat split; auto; exists v1, v2; repeat split; auto; apply H; auto.
Qed.

Lemma relation_update_fresh : forall T X eta rho a v1 v2,
  ~ In X (ty_names T) ->
  value_relation eta (relation_update rho X a) T v1 v2 <->
  value_relation eta rho T v1 v2.
Proof.
  induction T; intros X eta rho c v1 v2 Hfresh; simpl in *.
  - tauto.
  - assert (X <> a) by (intro E; subst; apply Hfresh; auto).
    unfold relation_update; destruct (Nat.eqb X a) eqn:E;
      [apply Nat.eqb_eq in E; contradiction|tauto].
  - apply not_in_append in Hfresh as [Hleft Hright].
    split.
    + intros (Hv1 & Hv2 & U1 & body1 & U2 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists U1, body1, U2, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros arg1 arg2 Harg.
      apply (proj1 (lifting_equiv _ _
        (fun w1 w2 => IHT2 X eta rho c w1 w2 Hright) _ _)).
      apply Hbody. apply (proj2 (IHT1 X eta rho c _ _ Hleft)); exact Harg.
    + intros (Hv1 & Hv2 & U1 & body1 & U2 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists U1, body1, U2, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros arg1 arg2 Harg.
      apply (proj2 (lifting_equiv _ _
        (fun w1 w2 => IHT2 X eta rho c w1 w2 Hright) _ _)).
      apply Hbody. apply (proj1 (IHT1 X eta rho c _ _ Hleft)); exact Harg.
  - split.
    + intros (Hv1 & Hv2 & body1 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros U1 U2 b HU1 HU2.
      apply (proj1 (lifting_equiv _ _
        (fun w1 w2 => IHT X (b :: eta) rho c w1 w2 Hfresh) _ _)).
      apply Hbody; auto.
    + intros (Hv1 & Hv2 & body1 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros U1 U2 b HU1 HU2.
      apply (proj2 (lifting_equiv _ _
        (fun w1 w2 => IHT X (b :: eta) rho c w1 w2 Hfresh) _ _)).
      apply Hbody; auto.
Qed.

Fixpoint context_type_names (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: rest => ty_names T ++ context_type_names rest
  end.

Lemma lookup_fresh_type : forall Gamma X x T,
  ~ In X (context_type_names Gamma) -> lookup_context x Gamma = Some T ->
  ~ In X (ty_names T).
Proof.
  induction Gamma as [|[y A] Gamma IH]; intros X x T Hfresh Hlookup;
    simpl in *; try discriminate.
  apply not_in_append in Hfresh as [HA HG].
  destruct (Nat.eqb x y); inversion Hlookup; subst; auto.
  eapply IH; eauto.
Qed.

Lemma lookup_override : forall Gamma x y T A,
  lookup_context y (update Gamma x T) = Some A ->
  (y = x /\ A = T) \/ (y <> x /\ lookup_context y Gamma = Some A).
Proof.
  intros; unfold update in H; simpl in H.
  destruct (Nat.eqb y x) eqn:E.
  - left; split; [now apply Nat.eqb_eq|now inversion H].
  - right; split; [now apply Nat.eqb_neq|exact H].
Qed.

Lemma relation_open_bvar : forall prefix rho X a i v1 v2,
  value_relation (prefix ++ [a]) rho (Ty_BVar i) v1 v2 <->
  value_relation prefix (relation_update rho X a)
    (open_ty_rec (length prefix) (Ty_FVar X) (Ty_BVar i)) v1 v2.
Proof.
  intros prefix rho X a i v1 v2; simpl.
  destruct (Nat.eq_dec i (length prefix)) as [E|E].
  - subst i. rewrite Nat.eqb_refl.
    rewrite nth_error_app2 by lia. replace (length prefix - length prefix) with 0 by lia.
    simpl. unfold relation_update; rewrite Nat.eqb_refl; tauto.
  - destruct (Nat.eqb (length prefix) i) eqn:Eb;
      [apply Nat.eqb_eq in Eb; lia|].
    destruct (Nat.lt_ge_cases i (length prefix)) as [Hlt|Hge].
    + rewrite nth_error_app1 by lia; tauto.
    + rewrite nth_error_app2 by lia.
      simpl.
      rewrite (proj2 (nth_error_None prefix i)) by lia.
      rewrite (proj2 (nth_error_None [a] (i - length prefix))) by (simpl; lia).
      tauto.
Qed.

Lemma relation_open_prefix : forall T prefix rho X a v1 v2,
  ~ In X (ty_names T) ->
  value_relation (prefix ++ [a]) rho T v1 v2 <->
  value_relation prefix (relation_update rho X a)
    (open_ty_rec (length prefix) (Ty_FVar X) T) v1 v2.
Proof.
  induction T; intros prefix rho X c v1 v2 Hfresh; simpl in *.
  - apply relation_open_bvar.
  - assert (X <> a) by (intro E; subst; apply Hfresh; auto).
    unfold relation_update; destruct (Nat.eqb X a) eqn:E;
      [apply Nat.eqb_eq in E; contradiction|tauto].
  - apply not_in_append in Hfresh as [Hleft Hright].
    split.
    + intros (Hv1 & Hv2 & U1 & body1 & U2 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists U1, body1, U2, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros arg1 arg2 Harg.
      apply (proj1 (lifting_equiv _ _
        (fun w1 w2 => IHT2 prefix rho X c w1 w2 Hright) _ _)).
      apply Hbody. apply (proj2 (IHT1 prefix rho X c _ _ Hleft)); exact Harg.
    + intros (Hv1 & Hv2 & U1 & body1 & U2 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists U1, body1, U2, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros arg1 arg2 Harg.
      apply (proj2 (lifting_equiv _ _
        (fun w1 w2 => IHT2 prefix rho X c w1 w2 Hright) _ _)).
      apply Hbody. apply (proj1 (IHT1 prefix rho X c _ _ Hleft)); exact Harg.
  - split.
    + intros (Hv1 & Hv2 & body1 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros U1 U2 b HU1 HU2.
      apply (proj1 (lifting_equiv _ _
        (fun w1 w2 => IHT (b :: prefix) rho X c w1 w2 Hfresh) _ _)).
      apply Hbody; auto.
    + intros (Hv1 & Hv2 & body1 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros U1 U2 b HU1 HU2.
      apply (proj2 (lifting_equiv _ _
        (fun w1 w2 => IHT (b :: prefix) rho X c w1 w2 Hfresh) _ _)).
      apply Hbody; auto.
Qed.

Lemma relation_open : forall T rho X a v1 v2,
  ~ In X (ty_names T) ->
  value_relation [a] rho T v1 v2 <->
  value_relation [] (relation_update rho X a) (open_ty T (Ty_FVar X)) v1 v2.
Proof.
  intros; apply (relation_open_prefix T [] rho X a v1 v2); auto.
Qed.

Lemma relation_eta_lc : forall T prefix tail1 tail2 rho v1 v2,
  lc_ty_at (length prefix) T ->
  value_relation (prefix ++ tail1) rho T v1 v2 <->
  value_relation (prefix ++ tail2) rho T v1 v2.
Proof.
  induction T; intros prefix tail1 tail2 rho v1 v2 Hlc; simpl in *.
  - inversion Hlc; subst.
    rewrite !nth_error_app1 by assumption; tauto.
  - tauto.
  - inversion Hlc; subst. split.
    + intros (Hv1 & Hv2 & U1 & body1 & U2 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists U1, body1, U2, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros arg1 arg2 Harg.
      apply (proj1 (lifting_equiv _ _
        (fun w1 w2 => IHT2 prefix tail1 tail2 rho w1 w2 H3) _ _)).
      apply Hbody. apply (proj2 (IHT1 prefix tail1 tail2 rho _ _ H2)); exact Harg.
    + intros (Hv1 & Hv2 & U1 & body1 & U2 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists U1, body1, U2, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros arg1 arg2 Harg.
      apply (proj2 (lifting_equiv _ _
        (fun w1 w2 => IHT2 prefix tail1 tail2 rho w1 w2 H3) _ _)).
      apply Hbody. apply (proj1 (IHT1 prefix tail1 tail2 rho _ _ H2)); exact Harg.
  - inversion Hlc; subst. split.
    + intros (Hv1 & Hv2 & body1 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros U1 U2 b HU1 HU2.
      apply (proj1 (lifting_equiv _ _
        (fun w1 w2 => IHT (b :: prefix) tail1 tail2 rho w1 w2 H1) _ _)).
      apply Hbody; auto.
    + intros (Hv1 & Hv2 & body1 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros U1 U2 b HU1 HU2.
      apply (proj2 (lifting_equiv _ _
        (fun w1 w2 => IHT (b :: prefix) tail1 tail2 rho w1 w2 H1) _ _)).
      apply Hbody; auto.
Qed.

Definition relation_candidate rho U : binary_candidate :=
  {| candidate_relation := value_relation [] rho U;
     candidate_values := fun v1 v2 H =>
       relation_values U [] rho v1 v2 (fun a Hnil => False_rect _ Hnil) H |}.

Lemma relation_subst_bvar : forall prefix rho U i v1 v2,
  locally_closed_ty U ->
  value_relation (prefix ++ [relation_candidate rho U]) rho (Ty_BVar i) v1 v2 <->
  value_relation prefix rho (open_ty_rec (length prefix) U (Ty_BVar i)) v1 v2.
Proof.
  intros prefix rho U i v1 v2 HU; simpl.
  destruct (Nat.eq_dec i (length prefix)) as [E|E].
  - subst i. rewrite Nat.eqb_refl.
    rewrite nth_error_app2 by lia. replace (length prefix - length prefix) with 0 by lia.
    simpl. unfold relation_candidate; simpl.
    apply (relation_eta_lc U [] [] prefix rho v1 v2 HU).
  - destruct (Nat.eqb (length prefix) i) eqn:Eb;
      [apply Nat.eqb_eq in Eb; lia|].
    destruct (Nat.lt_ge_cases i (length prefix)) as [Hlt|Hge].
    + rewrite nth_error_app1 by lia; tauto.
    + rewrite nth_error_app2 by lia; simpl.
      rewrite (proj2 (nth_error_None prefix i)) by lia.
      rewrite (proj2 (nth_error_None [relation_candidate rho U] (i - length prefix)))
        by (simpl; lia); tauto.
Qed.

Lemma relation_subst_prefix : forall T prefix rho U v1 v2,
  locally_closed_ty U ->
  value_relation (prefix ++ [relation_candidate rho U]) rho T v1 v2 <->
  value_relation prefix rho (open_ty_rec (length prefix) U T) v1 v2.
Proof.
  induction T; intros prefix rho U v1 v2 HU; simpl in *.
  - apply relation_subst_bvar; exact HU.
  - tauto.
  - split.
    + intros (Hv1 & Hv2 & A1 & body1 & A2 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists A1, body1, A2, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros arg1 arg2 Harg.
      apply (proj1 (lifting_equiv _ _
        (fun w1 w2 => IHT2 prefix rho U w1 w2 HU) _ _)).
      apply Hbody. apply (proj2 (IHT1 prefix rho U _ _ HU)); exact Harg.
    + intros (Hv1 & Hv2 & A1 & body1 & A2 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists A1, body1, A2, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros arg1 arg2 Harg.
      apply (proj2 (lifting_equiv _ _
        (fun w1 w2 => IHT2 prefix rho U w1 w2 HU) _ _)).
      apply Hbody. apply (proj1 (IHT1 prefix rho U _ _ HU)); exact Harg.
  - split.
    + intros (Hv1 & Hv2 & body1 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros U1 U2 b HU1 HU2.
      apply (proj1 (lifting_equiv _ _
        (fun w1 w2 => IHT (b :: prefix) rho U w1 w2 HU) _ _)).
      apply Hbody; auto.
    + intros (Hv1 & Hv2 & body1 & body2 & Eq1 & Eq2 & Hbody).
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact Eq1|]; split; [exact Eq2|].
      intros U1 U2 b HU1 HU2.
      apply (proj2 (lifting_equiv _ _
        (fun w1 w2 => IHT (b :: prefix) rho U w1 w2 HU) _ _)).
      apply Hbody; auto.
Qed.

Definition semantic_context (Gamma : context) (rho : binary_env)
    (sigma1 sigma2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation [] rho T (sigma1 x) (sigma2 x).

Theorem fundamental_relation : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta1 theta2 sigma1 sigma2 rho,
    (forall X, locally_closed_ty (theta1 X) /\ locally_closed_ty (theta2 X)) ->
    (forall x, value (sigma1 x) /\ value (sigma2 x)) ->
    semantic_context Gamma rho sigma1 sigma2 ->
    expression_relation [] rho T
      (instantiate_tm theta1 sigma1 t) (instantiate_tm theta2 sigma2 t).
Proof.
  intros Delta Gamma t T Htyping; induction Htyping;
    intros theta1 theta2 sigma1 sigma2 rho Htheta Hsigma Henv.
  - simpl. specialize (Henv x T H).
    unfold expression_relation, expression_lifting, results_match.
    pose proof (relation_values T [] rho _ _ (fun a Hnil => False_rect _ Hnil) Henv)
      as [Hv1 Hv2].
    split; [apply value_closed; exact Hv1|].
    split; [apply value_closed; exact Hv2|].
    exists (sigma1 x), (sigma2 x); repeat split; auto using EvalValue.
  - simpl.
    assert (HC1 : locally_closed_tm (tm_abs (instantiate_ty theta1 T1)
      (instantiate_tm theta1 sigma1 t2))).
    { change (locally_closed_tm (instantiate_tm theta1 sigma1 (tm_abs T1 t2))).
      eapply instantiate_tm_lc.
      + intros; apply Htheta.
      + intros; apply value_closed; apply Hsigma.
      + eapply has_type_closed; eapply T_Abs; eauto. }
    assert (HC2 : locally_closed_tm (tm_abs (instantiate_ty theta2 T1)
      (instantiate_tm theta2 sigma2 t2))).
    { change (locally_closed_tm (instantiate_tm theta2 sigma2 (tm_abs T1 t2))).
      eapply instantiate_tm_lc.
      + intros; apply Htheta.
      + intros; apply value_closed; apply Hsigma.
      + eapply has_type_closed; eapply T_Abs; eauto. }
    unfold expression_relation, expression_lifting, results_match.
    split; [exact HC1|]; split; [exact HC2|].
    exists (tm_abs (instantiate_ty theta1 T1) (instantiate_tm theta1 sigma1 t2)),
      (tm_abs (instantiate_ty theta2 T1) (instantiate_tm theta2 sigma2 t2)).
    split; [apply EvalValue; now constructor|].
    split; [apply EvalValue; now constructor|].
    simpl; split; [constructor; exact HC1|].
    split; [constructor; exact HC2|].
    exists (instantiate_ty theta1 T1), (instantiate_tm theta1 sigma1 t2),
      (instantiate_ty theta2 T1), (instantiate_tm theta2 sigma2 t2).
    split; [reflexivity|]; split; [reflexivity|].
    intros arg1 arg2 Harg.
    pose proof (relation_values T1 [] rho _ _
      (fun a Hnil => False_rect _ Hnil) Harg) as [Harg1 Harg2].
    set (x := fresh (L ++ term_names t2)).
    assert (HxL : ~ In x L) by (unfold x; intro Hin; apply (fresh_not_in (L ++ term_names t2)); apply in_or_app; auto).
    assert (Hxt : ~ In x (term_names t2)) by (unfold x; intro Hin; apply (fresh_not_in (L ++ term_names t2)); apply in_or_app; auto).
    pose proof (H1 x HxL (theta1) (theta2)
      (tm_override sigma1 x arg1) (tm_override sigma2 x arg2) rho) as Hbody.
    assert (Hsig' : forall y, value (tm_override sigma1 x arg1 y) /\
      value (tm_override sigma2 x arg2 y)).
    { intros y; unfold tm_override; destruct (Nat.eqb x y); auto. }
    assert (Henv' : semantic_context (update Gamma x T1) rho
      (tm_override sigma1 x arg1) (tm_override sigma2 x arg2)).
    { intros y A Hy; apply lookup_override in Hy as [[-> ->]|[Hneq Hy]].
      - unfold tm_override; now rewrite Nat.eqb_refl.
      - unfold tm_override; destruct (Nat.eqb x y) eqn:E;
          [apply Nat.eqb_eq in E; congruence|apply Henv; exact Hy]. }
    specialize (Hbody Htheta Hsig' Henv').
    unfold open_tm in Hbody.
    rewrite (instantiate_tm_open t2 theta1 sigma1 x arg1 0 Hxt)
      in Hbody by (auto using value_closed; intros y; apply value_closed; apply Hsigma).
    rewrite (instantiate_tm_open t2 theta2 sigma2 x arg2 0 Hxt)
      in Hbody by (auto using value_closed; intros y; apply value_closed; apply Hsigma).
    exact Hbody.
  - simpl.
    specialize (IHHtyping1 theta1 theta2 sigma1 sigma2 rho Htheta Hsigma Henv).
    specialize (IHHtyping2 theta1 theta2 sigma1 sigma2 rho Htheta Hsigma Henv).
    destruct IHHtyping1 as [Hf1 [Hf2 [f1 [f2 [He1 [He2 Hrel]]]]]].
    destruct IHHtyping2 as [Ha1 [Ha2 [a1 [a2 [Hea1 [Hea2 Harg]]]]]].
    destruct Hrel as [_ [_ [U1 [body1 [U2 [body2 [Ef1 [Ef2 Hfun]]]]]]]].
    subst f1 f2.
    specialize (Hfun a1 a2 Harg).
    destruct Hfun as [_ [_ [r1 [r2 [Hr1 [Hr2 Hres]]]]]].
    unfold expression_relation, expression_lifting, results_match.
    split; [apply lc_tm_app; assumption|].
    split; [apply lc_tm_app; assumption|].
    exists r1, r2; split; [eapply EvalApp; eauto|].
    split; [eapply EvalApp; eauto|exact Hres].
  - simpl.
    assert (HC1 : locally_closed_tm (tm_tabs (instantiate_tm theta1 sigma1 t))).
    { change (locally_closed_tm (instantiate_tm theta1 sigma1 (tm_tabs t))).
      eapply instantiate_tm_lc.
      + intros; apply Htheta.
      + intros; apply value_closed; apply Hsigma.
      + eapply has_type_closed; eapply T_TAbs; eauto. }
    assert (HC2 : locally_closed_tm (tm_tabs (instantiate_tm theta2 sigma2 t))).
    { change (locally_closed_tm (instantiate_tm theta2 sigma2 (tm_tabs t))).
      eapply instantiate_tm_lc.
      + intros; apply Htheta.
      + intros; apply value_closed; apply Hsigma.
      + eapply has_type_closed; eapply T_TAbs; eauto. }
    unfold expression_relation, expression_lifting, results_match.
    split; [exact HC1|]; split; [exact HC2|].
    exists (tm_tabs (instantiate_tm theta1 sigma1 t)),
      (tm_tabs (instantiate_tm theta2 sigma2 t)).
    split; [apply EvalValue; now constructor|].
    split; [apply EvalValue; now constructor|].
    simpl; split; [now constructor|]; split; [now constructor|].
    exists (instantiate_tm theta1 sigma1 t), (instantiate_tm theta2 sigma2 t).
    split; [reflexivity|]; split; [reflexivity|].
    intros U1 U2 a HU1 HU2.
    set (X := fresh (L ++ term_type_names t ++ ty_names T ++ context_type_names Gamma)).
    assert (HXall : ~ In X (L ++ term_type_names t ++ ty_names T ++ context_type_names Gamma))
      by (unfold X; apply fresh_not_in).
    apply not_in_append in HXall as [HXL HXrest].
    apply not_in_append in HXrest as [HXt HXrest].
    apply not_in_append in HXrest as [HXT HXG].
    pose proof (H0 X HXL (ty_override theta1 X U1) (ty_override theta2 X U2)
      sigma1 sigma2 (relation_update rho X a)) as Hbody.
    assert (Htheta' : forall Y, locally_closed_ty (ty_override theta1 X U1 Y) /\
      locally_closed_ty (ty_override theta2 X U2 Y)).
    { intro Y; unfold ty_override; destruct (Nat.eqb X Y); auto. }
    assert (Henv' : semantic_context Gamma (relation_update rho X a) sigma1 sigma2).
    { intros y A Hy; apply (proj2 (relation_update_fresh A X [] rho a _ _
        (lookup_fresh_type Gamma X y A HXG Hy))); apply Henv; exact Hy. }
    specialize (Hbody Htheta' Hsigma Henv').
    unfold open_tm_ty in Hbody.
    rewrite (instantiate_tm_ty_open t theta1 sigma1 X U1 0 HXt
      (fun y => proj1 (Htheta y)) (fun y => value_closed _ (proj1 (Hsigma y))) HU1)
      in Hbody.
    rewrite (instantiate_tm_ty_open t theta2 sigma2 X U2 0 HXt
      (fun y => proj2 (Htheta y)) (fun y => value_closed _ (proj2 (Hsigma y))) HU2)
      in Hbody.
    apply (proj2 (lifting_equiv _ _
      (fun w1 w2 => relation_open T rho X a w1 w2 HXT) _ _)); exact Hbody.
  - simpl.
    specialize (IHHtyping theta1 theta2 sigma1 sigma2 rho Htheta Hsigma Henv).
    destruct IHHtyping as [Hf1 [Hf2 [f1 [f2 [He1 [He2 Hrel]]]]]].
    destruct Hrel as [_ [_ [body1 [body2 [Ef1 [Ef2 Hpoly]]]]]].
    subst f1 f2.
    pose proof (wf_ty_closed Delta U H) as HU.
    pose proof (instantiate_ty_lc theta1 0 U (fun X => proj1 (Htheta X)) HU) as HU1.
    pose proof (instantiate_ty_lc theta2 0 U (fun X => proj2 (Htheta X)) HU) as HU2.
    specialize (Hpoly (instantiate_ty theta1 U) (instantiate_ty theta2 U)
      (relation_candidate rho U) HU1 HU2).
    pose proof (proj1 (lifting_equiv _ _
      (fun w1 w2 => relation_subst_prefix T [] rho U w1 w2 HU) _ _) Hpoly)
      as Hresult.
    destruct Hresult as [_ [_ [r1 [r2 [Hr1 [Hr2 Hres]]]]]].
    unfold expression_relation, expression_lifting, results_match.
    split; [apply lc_tm_tapp; assumption|].
    split; [apply lc_tm_tapp; assumption|].
    exists r1, r2; split; [eapply EvalTApp; eauto|].
    split; [eapply EvalTApp; eauto|exact Hres].
  - simpl.
    specialize (IHHtyping1 theta1 theta2 sigma1 sigma2 rho Htheta Hsigma Henv).
    specialize (IHHtyping2 theta1 theta2 sigma1 sigma2 rho Htheta Hsigma Henv).
    destruct IHHtyping1 as [Hl1 [Hl2 [v1 [v2 [Ev1 [Ev2 Hrel]]]]]].
    destruct IHHtyping2 as [Hr1 [Hr2 _]].
    unfold expression_relation, expression_lifting, results_match.
    split; [apply lc_tm_choice; assumption|].
    split; [apply lc_tm_choice; assumption|].
    exists v1, v2; split; [eapply EvalChoiceLeft; eauto|].
    split; [eapply EvalChoiceLeft; eauto|exact Hrel].
Qed.

Lemma term_names_open_rec : forall t k u x,
  In x (term_names t) -> In x (term_names (open_tm_rec k u t)).
Proof.
  induction t; intros k u x Hin; simpl in *.
  - contradiction.
  - exact Hin.
  - eapply IHt; eauto.
  - apply in_app_iff in Hin as [Hleft|Hright]; apply in_app_iff;
      [left; eapply IHt1|right; eapply IHt2]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - apply in_app_iff in Hin as [Hleft|Hright]; apply in_app_iff;
      [left; eapply IHt1|right; eapply IHt2]; eauto.
Qed.

Lemma term_names_open_ty_rec : forall t k U,
  term_names (open_tm_ty_rec k U t) = term_names t.
Proof.
  induction t; intros k U; simpl; auto; f_equal; eauto.
Qed.

Lemma typed_free_terms : forall Delta Gamma t T x,
  has_type Delta Gamma t T -> In x (term_names t) ->
  exists A, lookup_context x Gamma = Some A.
Proof.
  intros Delta Gamma t T x Htyping; induction Htyping; simpl; intros Hin.
  - exists T; destruct Hin as [->|[]]; exact H.
  - set (y := fresh (x :: L)).
    assert (HyL : ~ In y L).
    { unfold y; intro HH; apply (fresh_not_in (x :: L)); right; exact HH. }
    assert (Hyx : y <> x).
    { unfold y; intro HH; apply (fresh_not_in (x :: L)); left; symmetry; exact HH. }
    specialize (H1 y HyL).
    assert (Hopen : In x (term_names (open_tm t2 (tm_fvar y)))).
    { unfold open_tm; eapply term_names_open_rec; exact Hin. }
    apply H1 in Hopen as [A HA].
    exists A; simpl in HA; destruct (Nat.eqb x y) eqn:E;
      [apply Nat.eqb_eq in E; congruence|exact HA].
  - apply in_app_iff in Hin as [Hleft|Hright].
    + eapply IHHtyping1; eauto.
    + eapply IHHtyping2; eauto.
  - set (X := fresh L). specialize (H0 X (fresh_not_in L)).
    unfold open_tm_ty in H0.
    rewrite term_names_open_ty_rec in H0; eauto.
  - eapply IHHtyping; eauto.
  - apply in_app_iff in Hin as [Hleft|Hright].
    + eapply IHHtyping1; eauto.
    + eapply IHHtyping2; eauto.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty (fun X => Ty_FVar X) T = T.
Proof. induction T; simpl; congruence. Qed.

Lemma instantiate_closed_term : forall Delta t T sigma,
  has_type Delta empty t T ->
  instantiate_tm (fun X => Ty_FVar X) sigma t = t.
Proof.
  intros Delta t T sigma Htyping.
  assert (Hnames : forall x, ~ In x (term_names t)).
  { intros x Hin; pose proof (typed_free_terms _ _ _ _ x Htyping Hin)
      as [A HA]; discriminate. }
  clear Htyping Delta T; induction t; simpl in *.
  - reflexivity.
  - exfalso; apply (Hnames a); simpl; auto.
  - rewrite instantiate_ty_identity; f_equal; apply IHt; exact Hnames.
  - f_equal.
    + apply IHt1; intros x Hin; apply (Hnames x); apply in_app_iff; left; exact Hin.
    + apply IHt2; intros x Hin; apply (Hnames x); apply in_app_iff; right; exact Hin.
  - f_equal; apply IHt; exact Hnames.
  - rewrite instantiate_ty_identity; f_equal; apply IHt; exact Hnames.
  - f_equal.
    + apply IHt1; intros x Hin; apply (Hnames x); apply in_app_iff; left; exact Hin.
    + apply IHt2; intros x Hin; apply (Hnames x); apply in_app_iff; right; exact Hin.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; intros Hnext; auto.
  eapply multi_step; eauto.
Qed.

Lemma multi_app_left : forall f g arg,
  f -->* g -> locally_closed_tm arg -> tm_app f arg -->* tm_app g arg.
Proof.
  intros f g arg H; induction H; intros Harg; [constructor|].
  eapply multi_step; [apply ST_App1; eauto|apply IHmulti; exact Harg].
Qed.

Lemma multi_app_right : forall f arg arg',
  value f -> arg -->* arg' -> tm_app f arg -->* tm_app f arg'.
Proof.
  intros f arg arg' Hf H; induction H; [constructor|].
  eapply multi_step; [apply ST_App2; eauto|exact IHmulti].
Qed.

Lemma multi_tapp : forall t t' U,
  t -->* t' -> locally_closed_ty U -> tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H; induction H; intros HU; [constructor|].
  eapply multi_step; [apply ST_TApp; eauto|apply IHmulti; exact HU].
Qed.

Lemma eval_multi : forall t v, evaluates t v -> t -->* v.
Proof.
  intros t v H; induction H.
  - constructor.
  - eapply multi_trans.
    + apply multi_app_left; [exact IHevaluates1|].
      apply (proj1 (eval_closed _ _ H0)).
    + eapply multi_trans.
      * apply multi_app_right; [apply (proj2 (eval_closed _ _ H))|exact IHevaluates2].
      * eapply multi_step; [apply ST_AppAbs; [apply (value_closed _ (proj2 (eval_closed _ _ H)))|
          apply (proj2 (eval_closed _ _ H0))]|exact IHevaluates3].
  - eapply multi_trans.
    + apply multi_tapp; eauto.
    + eapply multi_step; [apply ST_TAppTabs; [apply (value_closed _ (proj2 (eval_closed _ _ H)))|assumption]|
        exact IHevaluates2].
  - eapply multi_step; [apply ST_ChoiceLeft; [apply (proj1 (eval_closed _ _ H))|assumption]|
      exact IHevaluates].
  - eapply multi_step; [apply ST_ChoiceRight; [assumption|apply (proj1 (eval_closed _ _ H0))]|
      exact IHevaluates].
Qed.

Definition singleton_candidate (v : tm) (Hv : value v) : binary_candidate.
Proof.
  refine {| candidate_relation := fun v1 v2 => v1 = v /\ v2 = v |}.
  intros v1 v2 [-> ->]; split; exact Hv.
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
  intros t Htyped U v HU Hv Htypedv.
  set (default := tm_abs (Ty_FVar 0) (tm_bvar 0)).
  assert (Hdefault : value default).
  { unfold default; apply v_abs; apply lc_tm_abs;
      [apply lc_ty_fvar|apply lc_tm_bvar; lia]. }
  set (sigma := fun _ : atom => default).
  pose proof (fundamental_relation _ _ _ _ Htyped
    (fun X => Ty_FVar X) (fun X => Ty_FVar X) sigma sigma
    (fun _ => None)) as Hfund.
  assert (Htheta : forall X, locally_closed_ty (Ty_FVar X) /\
    locally_closed_ty (Ty_FVar X)) by (intros; split; apply lc_ty_fvar).
  assert (Hsigma : forall x, value (sigma x) /\ value (sigma x))
    by (intros; split; exact Hdefault).
  assert (Henv : semantic_context empty (fun _ => None) sigma sigma).
  { intros x T Hlookup; discriminate. }
  specialize (Hfund Htheta Hsigma Henv).
  rewrite (instantiate_closed_term [] t _ sigma Htyped) in Hfund.
  destruct Hfund as [_ [_ [p1 [p2 [Hp1 [_ Hpoly]]]]]].
  destruct Hpoly as [_ [_ [body1 [body2 [Eq1 [Eq2 Hall]]]]]].
  subst p1 p2.
  set (candidate := singleton_candidate v Hv).
  specialize (Hall U U candidate (wf_ty_closed [] U HU) (wf_ty_closed [] U HU)).
  destruct Hall as [_ [_ [f1 [f2 [Hf1 [_ Harrow]]]]]].
  simpl in Harrow.
  destruct Harrow as [_ [_ [A1 [b1 [A2 [b2 [Ef1 [_ Hbody]]]]]]]].
  subst f1.
  specialize (Hbody v v).
  assert (Hvv : value_relation [candidate] (fun _ => None) (Ty_BVar 0) v v).
  { simpl; unfold candidate, singleton_candidate; simpl; auto. }
  specialize (Hbody Hvv).
  destruct Hbody as [_ [_ [r1 [r2 [Hr1 [_ Hr]]]]]].
  simpl in Hr; destruct Hr as [Er _]; subst r1.
  apply eval_multi.
  eapply EvalApp.
  - eapply EvalTApp; [exact Hp1|exact (wf_ty_closed [] U HU)|exact Hf1].
  - apply EvalValue; exact Hv.
  - exact Hr1.
Qed.

End SystemFParametricityNondeterminismMediumTask.
