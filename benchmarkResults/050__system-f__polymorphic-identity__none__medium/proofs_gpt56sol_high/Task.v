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

(** Simultaneous instantiations of the free variables.  Options are useful here:
    the empty instantiation is literally the identity. *)
Definition ty_instantiation := atom -> option ty.
Definition tm_instantiation := atom -> option tm.

Definition option_update {A} (s : atom -> option A) (x : atom) (a : A) :=
  fun y => if Nat.eqb x y then Some a else s y.

Fixpoint instantiate_ty (s : ty_instantiation) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => match s X with Some U => U | None => Ty_FVar X end
  | Ty_Arrow T1 T2 => Ty_Arrow (instantiate_ty s T1) (instantiate_ty s T2)
  | Ty_All T => Ty_All (instantiate_ty s T)
  end.

Fixpoint instantiate_tm (s : ty_instantiation) (g : tm_instantiation)
    (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => match g x with Some u => u | None => tm_fvar x end
  | tm_abs T t => tm_abs (instantiate_ty s T) (instantiate_tm s g t)
  | tm_app t1 t2 => tm_app (instantiate_tm s g t1) (instantiate_tm s g t2)
  | tm_tabs t => tm_tabs (instantiate_tm s g t)
  | tm_tapp t T => tm_tapp (instantiate_tm s g t) (instantiate_ty s T)
  end.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T => fv_ty T
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t => fv_tm t
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t => fv_tm t
  | tm_tapp t _ => fv_tm t
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t => fv_ty T ++ ftv_tm t
  | tm_app t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | tm_tabs t => ftv_tm t
  | tm_tapp t T => ftv_tm t ++ fv_ty T
  end.

Definition fresh_atom (L : list atom) : atom :=
  S (fold_right Nat.max 0 L).

Lemma in_fold_max : forall x L, In x L -> x <= fold_right Nat.max 0 L.
Proof.
  intros x L; induction L as [|a L IH]; simpl; intros H.
  - contradiction.
  - destruct H as [->|H]; [apply Nat.le_max_l|].
    eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_atom_not_in : forall L, ~ In (fresh_atom L) L.
Proof.
  intros L H. unfold fresh_atom in H.
  pose proof (in_fold_max _ _ H). lia.
Qed.

Lemma lc_ty_open_rec_id : forall T k U,
  lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  intros T k U H; induction H; simpl.
  - destruct (k =? i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - now rewrite IHlc_ty_at1, IHlc_ty_at2.
  - now rewrite IHlc_ty_at.
Qed.

Lemma lc_tm_open_rec_id : forall t K k u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros t K k u H; induction H; simpl.
  - destruct (k =? i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - now rewrite IHlc_tm_at.
  - now rewrite IHlc_tm_at1, IHlc_tm_at2.
  - now rewrite IHlc_tm_at.
  - now rewrite IHlc_tm_at.
Qed.

Lemma lc_tm_ty_open_rec_id : forall t K k U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  intros t K k U H; induction H; simpl; try reflexivity.
  - rewrite (lc_ty_open_rec_id _ _ U H). now rewrite IHlc_tm_at.
  - now rewrite IHlc_tm_at1, IHlc_tm_at2.
  - now rewrite IHlc_tm_at.
  - rewrite IHlc_tm_at, (lc_ty_open_rec_id _ _ U H0). reflexivity.
Qed.

Lemma lc_ty_open_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in H.
  - destruct (k =? n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; [eapply IHT1|eapply IHT2]; eauto.
  - inversion H; subst. constructor. eapply IHT; eauto.
Qed.

Lemma lc_tm_open_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H.
  - destruct (k =? n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; [assumption|eapply IHt; eauto].
  - inversion H; subst. constructor; [eapply IHt1|eapply IHt2]; eauto.
  - inversion H; subst. constructor. eapply IHt; eauto.
  - inversion H; subst. constructor; [eapply IHt|]; eauto.
Qed.

Lemma lc_tm_ty_open_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H; inversion H; subst.
  - constructor; assumption.
  - constructor.
  - constructor; [eapply lc_ty_open_inv|eapply IHt]; eauto.
  - constructor; [eapply IHt1|eapply IHt2]; eauto.
  - constructor. eapply IHt; eauto.
  - constructor; [eapply IHt|eapply lc_ty_open_inv]; eauto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma value_relation_values : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  intros eta rho T; revert eta; induction T; intros eta v1 v2 H; simpl in H.
  - destruct (nth_error eta n) as [a|] eqn:E; [apply candidate_values with a|contradiction]; exact H.
  - destruct (rho a) as [c|] eqn:E; [apply candidate_values with c|contradiction]; exact H.
  - tauto.
  - tauto.
Qed.

Lemma wf_ty_lc : forall D T, wf_ty D T -> locally_closed_ty T.
Proof.
  intros D T H; induction H.
  - constructor.
  - constructor; assumption.
  - constructor. specialize (H (fresh_atom L) (fresh_atom_not_in L)).
    specialize (H0 (fresh_atom L) (fresh_atom_not_in L)).
    apply lc_ty_open_inv with (X := fresh_atom L). exact H0.
Qed.

Lemma typing_lc : forall D G t T, has_type D G t T -> locally_closed_tm t.
Proof.
  intros D G t T H; induction H.
  - constructor.
  - constructor; [eapply wf_ty_lc; exact H|].
    specialize (H0 (fresh_atom L) (fresh_atom_not_in L)).
    specialize (H1 (fresh_atom L) (fresh_atom_not_in L)).
    apply lc_tm_open_inv with (x := fresh_atom L).
    exact H1.
  - constructor; assumption.
  - constructor. specialize (H (fresh_atom L) (fresh_atom_not_in L)).
    specialize (H0 (fresh_atom L) (fresh_atom_not_in L)).
    apply lc_tm_ty_open_inv with (X := fresh_atom L).
    exact H0.
  - constructor; [assumption|eapply wf_ty_lc; exact H0].
Qed.

Definition type_environment (D : ty_context) (s1 s2 : ty_instantiation)
    (rho : binary_env) : Prop :=
  (forall X U, s1 X = Some U -> locally_closed_ty U) /\
  (forall X U, s2 X = Some U -> locally_closed_ty U) /\
  (forall X, In X D ->
     exists U1 U2 a, s1 X = Some U1 /\ s2 X = Some U2 /\ rho X = Some a).

Definition term_environment (G : context) (g1 g2 : tm_instantiation)
    eta rho : Prop :=
  (forall x u, g1 x = Some u -> locally_closed_tm u) /\
  (forall x u, g2 x = Some u -> locally_closed_tm u) /\
  (forall x T, lookup_context x G = Some T ->
     exists v1 v2, g1 x = Some v1 /\ g2 x = Some v2 /\
       value_relation eta rho T v1 v2).

Lemma lc_ty_weaken : forall k T, lc_ty_at k T -> forall j, k <= j -> lc_ty_at j T.
Proof.
  intros k T H; induction H; intros j Hle.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
Qed.

Lemma instantiate_ty_lc : forall k T s,
  lc_ty_at k T ->
  (forall X U, s X = Some U -> locally_closed_ty U) ->
  lc_ty_at k (instantiate_ty s T).
Proof.
  intros k T s H; induction H; intros HC; simpl.
  - constructor; assumption.
  - destruct (s X) as [U|] eqn:E.
    + eapply lc_ty_weaken; [eapply HC; exact E|lia].
    + constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma instantiate_wf_lc : forall D T,
  wf_ty D T -> forall s1 s2 rho,
  type_environment D s1 s2 rho ->
  locally_closed_ty (instantiate_ty s1 T) /\
  locally_closed_ty (instantiate_ty s2 T).
Proof.
  intros D T HT s1 s2 rho HE. destruct HE as [HC1 [HC2 HM]].
  pose proof (wf_ty_lc _ _ HT) as HL.
  split.
  - eapply instantiate_ty_lc; [exact HL|exact HC1].
  - eapply instantiate_ty_lc; [exact HL|exact HC2].
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H; induction H; intros K' k' HK Hk.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_weaken; eauto.
    + apply IHlc_tm_at; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
  - apply lc_tm_tapp; [apply IHlc_tm_at; lia|eapply lc_ty_weaken; eauto].
Qed.

Lemma instantiate_tm_lc : forall K k t s g,
  lc_tm_at K k t ->
  (forall X U, s X = Some U -> locally_closed_ty U) ->
  (forall x u, g x = Some u -> locally_closed_tm u) ->
  lc_tm_at K k (instantiate_tm s g t).
Proof.
  intros K k t s g H; induction H; intros HS HG; simpl.
  - constructor; assumption.
  - destruct (g x) as [u|] eqn:E.
    + eapply lc_tm_weaken; [eapply HG; exact E|lia|lia].
    + constructor.
  - constructor; [eapply instantiate_ty_lc|eapply IHlc_tm_at]; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; [eauto|eapply instantiate_ty_lc]; eauto.
Qed.

Lemma option_update_eq : forall A (s : atom -> option A) x a,
  option_update s x a x = Some a.
Proof. intros; unfold option_update; now rewrite Nat.eqb_refl. Qed.

Lemma option_update_neq : forall A (s : atom -> option A) x y a,
  x <> y -> option_update s x a y = s y.
Proof.
  intros A s x y a H; unfold option_update.
  destruct (x =? y) eqn:E; [apply Nat.eqb_eq in E; contradiction|reflexivity].
Qed.

Lemma relation_update_eq : forall rho X a,
  relation_update rho X a X = Some a.
Proof. intros; unfold relation_update; now rewrite Nat.eqb_refl. Qed.

Lemma relation_update_neq : forall rho X Y a,
  X <> Y -> relation_update rho X a Y = rho Y.
Proof.
  intros rho X Y a H; unfold relation_update.
  destruct (X =? Y) eqn:E; [apply Nat.eqb_eq in E; contradiction|reflexivity].
Qed.

Lemma not_in_app : forall (A : Type) (x : A) l1 l2,
  ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros A x l1 l2 H. split; intros Hin; apply H; apply in_app_iff; auto.
Qed.

Lemma instantiate_open_tm : forall t k s g x u,
  ~ In x (fv_tm t) -> locally_closed_tm u ->
  (forall y w, g y = Some w -> locally_closed_tm w) ->
  instantiate_tm s (option_update g x u)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (instantiate_tm s g t).
Proof.
  induction t; intros k s g x u Hfresh Hu Hg; simpl in *.
  - destruct (k =? n); simpl; [rewrite option_update_eq|]; reflexivity.
  - assert (x <> a) by (intros ->; apply Hfresh; simpl; auto).
    rewrite option_update_neq by assumption.
    destruct (g a) as [w|] eqn:E; simpl.
    + symmetry. apply (lc_tm_open_rec_id w 0 k u).
      eapply lc_tm_weaken; [eapply Hg; exact E|lia|lia].
    + reflexivity.
  - f_equal. eapply IHt; eauto.
  - apply not_in_app in Hfresh as [H1 H2].
    f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
Qed.

Lemma instantiate_open_ty : forall T k s X U,
  ~ In X (fv_ty T) -> locally_closed_ty U ->
  (forall Y V, s Y = Some V -> locally_closed_ty V) ->
  instantiate_ty (option_update s X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty s T).
Proof.
  induction T; intros k s X U Hfresh HU HS; simpl in *.
  - destruct (k =? n); simpl; [rewrite option_update_eq|]; reflexivity.
  - assert (X <> a) by (intros ->; apply Hfresh; simpl; auto).
    rewrite option_update_neq by assumption.
    destruct (s a) as [V|] eqn:E; simpl.
    + symmetry. eapply lc_ty_open_rec_id.
      eapply lc_ty_weaken; [eapply HS; exact E|lia].
    + reflexivity.
  - apply not_in_app in Hfresh as [H1 H2].
    f_equal; [eapply IHT1|eapply IHT2]; eauto.
  - f_equal. eapply IHT; eauto.
Qed.

Lemma instantiate_open_tm_ty : forall t K s g X U,
  ~ In X (ftv_tm t) -> locally_closed_ty U ->
  (forall Y V, s Y = Some V -> locally_closed_ty V) ->
  (forall y w, g y = Some w -> locally_closed_tm w) ->
  instantiate_tm (option_update s X U) g
    (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K U (instantiate_tm s g t).
Proof.
  induction t; intros K s g X U Hfresh HU HS HG; simpl in *.
  - reflexivity.
  - destruct (g a) as [w|] eqn:E; simpl.
    + symmetry. apply (lc_tm_ty_open_rec_id w K 0 U).
      eapply lc_tm_weaken; [eapply HG; exact E|lia|lia].
    + reflexivity.
  - apply not_in_app in Hfresh as [H1 H2]. f_equal.
    + eapply instantiate_open_ty; eauto.
    + eapply IHt; eauto.
  - apply not_in_app in Hfresh as [H1 H2].
    f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - f_equal. eapply IHt; eauto.
  - apply not_in_app in Hfresh as [H1 H2]. f_equal.
    + eapply IHt; eauto.
    + eapply instantiate_open_ty; eauto.
Qed.

Lemma expression_lifting_iff : forall R S,
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  forall t1 t2, expression_lifting R t1 t2 <-> expression_lifting S t1 t2.
Proof.
  intros R S HRS t1 t2. unfold expression_lifting, results_match.
  split.
  - intros [Hlc1 [Hlc2 (v1 & v2 & A & B & C)]].
    split; [exact Hlc1|]. split; [exact Hlc2|].
    exists v1, v2. repeat split; try assumption. apply (proj1 (HRS _ _)); assumption.
  - intros [Hlc1 [Hlc2 (v1 & v2 & A & B & C)]].
    split; [exact Hlc1|]. split; [exact Hlc2|].
    exists v1, v2. repeat split; try assumption. apply (proj2 (HRS _ _)); assumption.
Qed.

Lemma nth_error_app_last_eq : forall A (l : list A) a,
  nth_error (l ++ [a]) (length l) = Some a.
Proof. intros; rewrite nth_error_app2 by lia. replace (length l - length l) with 0 by lia. reflexivity. Qed.

Lemma lc_ty_arrow_inv : forall k A B,
  lc_ty_at k (Ty_Arrow A B) -> lc_ty_at k A /\ lc_ty_at k B.
Proof. intros; inversion H; subst; auto. Qed.

Lemma lc_ty_all_inv : forall k T,
  lc_ty_at k (Ty_All T) -> lc_ty_at (S k) T.
Proof. intros; inversion H; subst; auto. Qed.

Lemma value_relation_open : forall T k eta rho X c,
  length eta = k -> lc_ty_at (S k) T -> ~ In X (fv_ty T) ->
  forall v1 v2,
  value_relation eta (relation_update rho X c)
    (open_ty_rec k (Ty_FVar X) T) v1 v2 <->
  value_relation (eta ++ [c]) rho T v1 v2.
Proof.
  induction T; intros k eta rho X c Hlen Hlc Hfresh v1 v2; simpl in *.
  - assert (Hnk : n < S k) by (inversion Hlc; assumption).
    destruct (k =? n) eqn:E.
    + apply Nat.eqb_eq in E; subst. cbn [value_relation].
      rewrite relation_update_eq, nth_error_app_last_eq. reflexivity.
    + apply Nat.eqb_neq in E. assert (n < k) by lia.
      rewrite nth_error_app1 by lia. reflexivity.
  - assert (X <> a) by (intros ->; apply Hfresh; simpl; auto).
    unfold relation_update. destruct (X =? a) eqn:E; [apply Nat.eqb_eq in E; contradiction|reflexivity].
  - destruct (lc_ty_arrow_inv _ _ _ Hlc) as [HL1 HL2].
    apply not_in_app in Hfresh as [HF1 HF2].
    specialize (IHT1 k eta rho X c Hlen HL1 HF1).
    specialize (IHT2 k eta rho X c Hlen HL2 HF2).
    simpl. split.
    + intros [V1 [V2 (U1 & b1 & U2 & b2 & E1 & E2 & Hfun)]].
      split; [exact V1|]. split; [exact V2|].
      exists U1, b1, U2, b2. split; [exact E1|]. split; [exact E2|].
      intros p q HR. apply (proj1 (expression_lifting_iff _ _ IHT2 _ _)).
      apply Hfun. apply (proj2 (IHT1 _ _)); exact HR.
    + intros [V1 [V2 (U1 & b1 & U2 & b2 & E1 & E2 & Hfun)]].
      split; [exact V1|]. split; [exact V2|].
      exists U1, b1, U2, b2. split; [exact E1|]. split; [exact E2|].
      intros p q HR. apply (proj2 (expression_lifting_iff _ _ IHT2 _ _)).
      apply Hfun. apply (proj1 (IHT1 _ _)); exact HR.
  - pose proof (lc_ty_all_inv _ _ Hlc) as Hbody.
    specialize (IHT (S k)). simpl in IHT.
    split.
    + intros [V1 [V2 (b1 & b2 & E1 & E2 & Hfun)]].
      split; [exact V1|]. split; [exact V2|]. exists b1, b2.
      split; [exact E1|]. split; [exact E2|]. intros U1 U2 d HU1 HU2.
      specialize (IHT (d :: eta) rho X c ltac:(simpl; lia) Hbody Hfresh).
      apply (proj1 (expression_lifting_iff _ _ IHT _ _)).
      apply Hfun; assumption.
    + intros [V1 [V2 (b1 & b2 & E1 & E2 & Hfun)]].
      split; [exact V1|]. split; [exact V2|]. exists b1, b2.
      split; [exact E1|]. split; [exact E2|]. intros U1 U2 d HU1 HU2.
      specialize (IHT (d :: eta) rho X c ltac:(simpl; lia) Hbody Hfresh).
      apply (proj2 (expression_lifting_iff _ _ IHT _ _)).
      apply Hfun; assumption.
Qed.

Lemma lc_ty_open : forall T k U,
  lc_ty_at (S k) T -> lc_ty_at k U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; simpl.
  - inversion HT; subst. destruct (k =? n) eqn:E; [exact HU|constructor; apply Nat.eqb_neq in E; lia].
  - constructor.
  - destruct (lc_ty_arrow_inv _ _ _ HT). constructor; eauto.
  - constructor. apply IHT; [apply lc_ty_all_inv with (k := S k); exact HT|].
    eapply lc_ty_weaken; [exact HU|lia].
Qed.

Lemma typing_type_lc : forall D G t T,
  has_type D G t T -> locally_closed_ty T.
Proof.
  intros D G t T H; induction H.
  - apply wf_ty_lc with Delta; assumption.
  - constructor; [apply wf_ty_lc with Delta; assumption|].
    specialize (H1 (fresh_atom L) (fresh_atom_not_in L)). exact H1.
  - inversion IHhas_type1; subst; assumption.
  - constructor. specialize (H0 (fresh_atom L) (fresh_atom_not_in L)).
    apply lc_ty_open_inv with (X := fresh_atom L). exact H0.
  - apply lc_ty_open.
    + apply lc_ty_all_inv with (k := 0). exact IHhas_type.
    + apply wf_ty_lc with Delta; assumption.
Qed.

Lemma value_relation_update_fresh : forall T eta rho X c,
  ~ In X (fv_ty T) -> forall v1 v2,
  value_relation eta (relation_update rho X c) T v1 v2 <->
  value_relation eta rho T v1 v2.
Proof.
  induction T; intros eta rho X c HF v1 v2; simpl in *.
  - reflexivity.
  - assert (X <> a) by (intros ->; apply HF; simpl; auto).
    rewrite relation_update_neq by assumption. reflexivity.
  - apply not_in_app in HF as [HF1 HF2].
    specialize (IHT1 eta rho X c HF1). specialize (IHT2 eta rho X c HF2).
    split.
    + intros [V1 [V2 (U1 & b1 & U2 & b2 & E1 & E2 & F)]].
      split; [exact V1|]. split; [exact V2|]. exists U1, b1, U2, b2.
      split; [exact E1|]. split; [exact E2|]. intros p q HR.
      apply (proj1 (expression_lifting_iff _ _ IHT2 _ _)). apply F.
      apply (proj2 (IHT1 _ _)); exact HR.
    + intros [V1 [V2 (U1 & b1 & U2 & b2 & E1 & E2 & F)]].
      split; [exact V1|]. split; [exact V2|]. exists U1, b1, U2, b2.
      split; [exact E1|]. split; [exact E2|]. intros p q HR.
      apply (proj2 (expression_lifting_iff _ _ IHT2 _ _)). apply F.
      apply (proj1 (IHT1 _ _)); exact HR.
  - split.
    + intros [V1 [V2 (b1 & b2 & E1 & E2 & F)]].
      split; [exact V1|]. split; [exact V2|]. exists b1, b2.
      split; [exact E1|]. split; [exact E2|]. intros U1 U2 d H1 H2.
      apply (proj1 (expression_lifting_iff _ _ (IHT (d :: eta) rho X c HF) _ _)). apply F; assumption.
    + intros [V1 [V2 (b1 & b2 & E1 & E2 & F)]].
      split; [exact V1|]. split; [exact V2|]. exists b1, b2.
      split; [exact E1|]. split; [exact E2|]. intros U1 U2 d H1 H2.
      apply (proj2 (expression_lifting_iff _ _ (IHT (d :: eta) rho X c HF) _ _)). apply F; assumption.
Qed.

Fixpoint ftv_context (G : context) : list atom :=
  match G with
  | [] => []
  | (_, T) :: G => fv_ty T ++ ftv_context G
  end.

Lemma lookup_ftv : forall G x T X,
  lookup_context x G = Some T -> In X (fv_ty T) -> In X (ftv_context G).
Proof.
  induction G as [|[y U] G IH]; intros x T X Hlook Hin; simpl in *; [discriminate|].
  destruct (x =? y) eqn:E.
  - inversion Hlook; subst. apply in_app_iff; auto.
  - apply in_app_iff; right. eapply IH; eauto.
Qed.

Lemma type_environment_update : forall D s1 s2 rho X U1 U2 c,
  type_environment D s1 s2 rho -> locally_closed_ty U1 -> locally_closed_ty U2 ->
  type_environment (X :: D) (option_update s1 X U1) (option_update s2 X U2)
    (relation_update rho X c).
Proof.
  intros D s1 s2 rho X U1 U2 c [HC1 [HC2 HM]] HU1 HU2.
  split.
  - intros Y V E. unfold option_update in E. destruct (X =? Y) eqn:EY.
    + inversion E; subst; exact HU1.
    + eapply HC1; exact E.
  - split.
    + intros Y V E. unfold option_update in E. destruct (X =? Y) eqn:EY.
      * inversion E; subst; exact HU2.
      * eapply HC2; exact E.
    + intros Y [EY|HY].
      * subst. exists U1, U2, c. repeat split; apply option_update_eq || apply relation_update_eq.
      * destruct (HM Y HY) as (V1 & V2 & d & E1 & E2 & E3).
        destruct (Nat.eq_dec X Y) as [->|Hneq].
        -- exists U1, U2, c. repeat split; apply option_update_eq || apply relation_update_eq.
        -- exists V1, V2, d. split.
           ++ rewrite option_update_neq by exact Hneq. exact E1.
           ++ split.
              ** rewrite option_update_neq by exact Hneq. exact E2.
              ** rewrite relation_update_neq by exact Hneq. exact E3.
Qed.

Lemma term_environment_update : forall G g1 g2 eta rho x v1 v2 T,
  term_environment G g1 g2 eta rho -> value_relation eta rho T v1 v2 ->
  term_environment (update G x T) (option_update g1 x v1) (option_update g2 x v2) eta rho.
Proof.
  intros G g1 g2 eta rho x v1 v2 T [HC1 [HC2 HM]] HR.
  destruct (value_relation_values _ _ _ _ _ HR) as [HV1 HV2].
  split.
  - intros y u E. unfold option_update in E. destruct (x =? y) eqn:EY.
    + inversion E; subst; apply value_lc; exact HV1.
    + eapply HC1; exact E.
  - split.
    + intros y u E. unfold option_update in E. destruct (x =? y) eqn:EY.
      * inversion E; subst; apply value_lc; exact HV2.
      * eapply HC2; exact E.
    + intros y U Hlook. simpl in Hlook. destruct (y =? x) eqn:E.
      * apply Nat.eqb_eq in E; subst. inversion Hlook; subst.
        exists v1, v2. repeat split; try apply option_update_eq; assumption.
      * apply Nat.eqb_neq in E.
        destruct (HM y U Hlook) as (w1 & w2 & E1 & E2 & Hrel).
        exists w1, w2. split.
        -- rewrite option_update_neq by congruence. exact E1.
        -- split; [rewrite option_update_neq by congruence; exact E2|exact Hrel].
Qed.

Lemma term_environment_rho_update : forall G g1 g2 eta rho X c,
  ~ In X (ftv_context G) -> term_environment G g1 g2 eta rho ->
  term_environment G g1 g2 eta (relation_update rho X c).
Proof.
  intros G g1 g2 eta rho X c HF [HC1 [HC2 HM]].
  split; [exact HC1|]. split; [exact HC2|]. intros x T Hlook.
  destruct (HM x T Hlook) as (v1 & v2 & E1 & E2 & HR).
  exists v1, v2. repeat split; try assumption.
  assert (HFt : ~ In X (fv_ty T)).
  { intros Hin. apply HF. eapply lookup_ftv; eauto. }
  apply (proj2 (value_relation_update_fresh T eta rho X c HFt v1 v2)); exact HR.
Qed.

Definition eta_agree (k : nat) (e1 e2 : list binary_candidate) : Prop :=
  forall i, i < k -> nth_error e1 i = nth_error e2 i.

Lemma value_relation_eta_agree : forall T k,
  lc_ty_at k T -> forall e1 e2 rho,
  eta_agree k e1 e2 -> forall v1 v2,
  value_relation e1 rho T v1 v2 <-> value_relation e2 rho T v1 v2.
Proof.
  intros T k Hlc; induction Hlc; intros e1 e2 rho HA v1 v2; simpl.
  - rewrite (HA i H). reflexivity.
  - reflexivity.
  - specialize (IHHlc1 e1 e2 rho HA). specialize (IHHlc2 e1 e2 rho HA).
    split.
    + intros [V1 [V2 (U1 & b1 & U2 & b2 & E1 & E2 & F)]].
      split; [exact V1|]. split; [exact V2|]. exists U1, b1, U2, b2.
      split; [exact E1|]. split; [exact E2|]. intros p q HR.
      apply (proj1 (expression_lifting_iff _ _ IHHlc2 _ _)). apply F.
      apply (proj2 (IHHlc1 _ _)); exact HR.
    + intros [V1 [V2 (U1 & b1 & U2 & b2 & E1 & E2 & F)]].
      split; [exact V1|]. split; [exact V2|]. exists U1, b1, U2, b2.
      split; [exact E1|]. split; [exact E2|]. intros p q HR.
      apply (proj2 (expression_lifting_iff _ _ IHHlc2 _ _)). apply F.
      apply (proj1 (IHHlc1 _ _)); exact HR.
  - split.
    + intros [V1 [V2 (b1 & b2 & E1 & E2 & F)]].
      split; [exact V1|]. split; [exact V2|]. exists b1, b2.
      split; [exact E1|]. split; [exact E2|]. intros U1 U2 d H1 H2.
      assert (HAd : eta_agree (S k) (d :: e1) (d :: e2)).
      { intros [|j] Hj; simpl; [reflexivity|apply HA; lia]. }
      apply (proj1 (expression_lifting_iff _ _
        (IHHlc (d :: e1) (d :: e2) rho HAd) _ _)). apply F; assumption.
    + intros [V1 [V2 (b1 & b2 & E1 & E2 & F)]].
      split; [exact V1|]. split; [exact V2|]. exists b1, b2.
      split; [exact E1|]. split; [exact E2|]. intros U1 U2 d H1 H2.
      assert (HAd : eta_agree (S k) (d :: e1) (d :: e2)).
      { intros [|j] Hj; simpl; [reflexivity|apply HA; lia]. }
      apply (proj2 (expression_lifting_iff _ _
        (IHHlc (d :: e1) (d :: e2) rho HAd) _ _)). apply F; assumption.
Qed.

Definition semantic_candidate eta rho U (HU : locally_closed_ty U) : binary_candidate :=
  {| candidate_relation := value_relation eta rho U;
     candidate_values := value_relation_values eta rho U |}.

Lemma value_relation_open_closed : forall T k eta rho U (HU : locally_closed_ty U),
  length eta = k -> lc_ty_at (S k) T -> forall v1 v2,
  value_relation eta rho (open_ty_rec k U T) v1 v2 <->
  value_relation (eta ++ [semantic_candidate [] rho U HU]) rho T v1 v2.
Proof.
  induction T; intros k eta rho U HU Hlen Hlc v1 v2; simpl in *.
  - assert (Hnk : n < S k) by (inversion Hlc; assumption).
    destruct (k =? n) eqn:E.
    + apply Nat.eqb_eq in E; subst. rewrite nth_error_app_last_eq. simpl.
      apply value_relation_eta_agree with (k := 0) (T := U); [exact HU|].
      intros i Hi; lia.
    + apply Nat.eqb_neq in E. assert (n < k) by lia.
      rewrite nth_error_app1 by lia. reflexivity.
  - reflexivity.
  - destruct (lc_ty_arrow_inv _ _ _ Hlc) as [HL1 HL2].
    specialize (IHT1 k eta rho U HU Hlen HL1).
    specialize (IHT2 k eta rho U HU Hlen HL2).
    split.
    + intros [V1 [V2 (A1 & b1 & A2 & b2 & E1 & E2 & F)]].
      split; [exact V1|]. split; [exact V2|]. exists A1, b1, A2, b2.
      split; [exact E1|]. split; [exact E2|]. intros p q HR.
      apply (proj1 (expression_lifting_iff _ _ IHT2 _ _)). apply F.
      apply (proj2 (IHT1 _ _)); exact HR.
    + intros [V1 [V2 (A1 & b1 & A2 & b2 & E1 & E2 & F)]].
      split; [exact V1|]. split; [exact V2|]. exists A1, b1, A2, b2.
      split; [exact E1|]. split; [exact E2|]. intros p q HR.
      apply (proj2 (expression_lifting_iff _ _ IHT2 _ _)). apply F.
      apply (proj1 (IHT1 _ _)); exact HR.
  - pose proof (lc_ty_all_inv _ _ Hlc) as HB. split.
    + intros [V1 [V2 (b1 & b2 & E1 & E2 & F)]].
      split; [exact V1|]. split; [exact V2|]. exists b1, b2.
      split; [exact E1|]. split; [exact E2|]. intros A1 A2 d H1 H2.
      apply (proj1 (expression_lifting_iff _ _
        (IHT (S k) (d :: eta) rho U HU ltac:(simpl; lia) HB) _ _)). apply F; assumption.
    + intros [V1 [V2 (b1 & b2 & E1 & E2 & F)]].
      split; [exact V1|]. split; [exact V2|]. exists b1, b2.
      split; [exact E1|]. split; [exact E2|]. intros A1 A2 d H1 H2.
      apply (proj2 (expression_lifting_iff _ _
        (IHT (S k) (d :: eta) rho U HU ltac:(simpl; lia) HB) _ _)). apply F; assumption.
Qed.

Theorem fundamental_theorem : forall D G t T,
  has_type D G t T -> forall s1 s2 g1 g2 rho,
  type_environment D s1 s2 rho ->
  term_environment G g1 g2 [] rho ->
  expression_relation [] rho T
    (instantiate_tm s1 g1 t) (instantiate_tm s2 g2 t).
Proof.
  intros D G t T HT; induction HT; intros s1 s2 g1 g2 rho HTE HGE; simpl.
  - destruct HGE as [HC1 [HC2 HM]].
    destruct (HM x T H) as (v1 & v2 & E1 & E2 & HR).
    rewrite E1, E2. destruct (value_relation_values _ _ _ _ _ HR) as [HV1 HV2].
    split; [apply value_lc; exact HV1|]. split; [apply value_lc; exact HV2|].
    exists v1, v2. repeat split; try constructor; assumption.
  - destruct HTE as [TS1 [TS2 TM]]. destruct HGE as [GS1 [GS2 GM]].
    assert (HTE0 : type_environment Delta s1 s2 rho) by (repeat split; assumption).
    assert (HGE0 : term_environment Gamma g1 g2 [] rho) by (repeat split; assumption).
    assert (Horig : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)).
    { eapply T_Abs with (L := L); eauto. }
    assert (LC1 : locally_closed_tm (instantiate_tm s1 g1 (tm_abs T1 t2))).
    { eapply instantiate_tm_lc; [eapply typing_lc; exact Horig|exact TS1|exact GS1]. }
    assert (LC2 : locally_closed_tm (instantiate_tm s2 g2 (tm_abs T1 t2))).
    { eapply instantiate_tm_lc; [eapply typing_lc; exact Horig|exact TS2|exact GS2]. }
    assert (V1 : value (tm_abs (instantiate_ty s1 T1) (instantiate_tm s1 g1 t2)))
      by (constructor; exact LC1).
    assert (V2 : value (tm_abs (instantiate_ty s2 T1) (instantiate_tm s2 g2 t2)))
      by (constructor; exact LC2).
    split; [exact LC1|]. split; [exact LC2|].
    exists (tm_abs (instantiate_ty s1 T1) (instantiate_tm s1 g1 t2)),
      (tm_abs (instantiate_ty s2 T1) (instantiate_tm s2 g2 t2)).
    split; [constructor; exact V1|]. split; [constructor; exact V2|].
    split; [exact V1|]. split; [exact V2|].
    exists (instantiate_ty s1 T1), (instantiate_tm s1 g1 t2),
      (instantiate_ty s2 T1), (instantiate_tm s2 g2 t2).
    split; [reflexivity|]. split; [reflexivity|]. intros arg1 arg2 Harg.
    set (x := fresh_atom (L ++ fv_tm t2)).
    assert (Hx : ~ In x (L ++ fv_tm t2)) by (apply fresh_atom_not_in).
    apply not_in_app in Hx as [HxL Hxfv].
    specialize (H1 x HxL s1 s2 (option_update g1 x arg1)
      (option_update g2 x arg2) rho HTE0).
    assert (HGE' : term_environment <{ x |-> $(T1); Gamma }>
      (option_update g1 x arg1) (option_update g2 x arg2) [] rho).
    { apply term_environment_update; [exact HGE0|exact Harg]. }
    specialize (H1 HGE'). unfold expression_relation, open_tm in H1.
    rewrite (instantiate_open_tm t2 0 s1 g1 x arg1 Hxfv
      (value_lc _ (proj1 (value_relation_values _ _ _ _ _ Harg))) GS1) in H1.
    rewrite (instantiate_open_tm t2 0 s2 g2 x arg2 Hxfv
      (value_lc _ (proj2 (value_relation_values _ _ _ _ _ Harg))) GS2) in H1.
    exact H1.
  - specialize (IHHT1 s1 s2 g1 g2 rho HTE HGE).
    specialize (IHHT2 s1 s2 g1 g2 rho HTE HGE).
    unfold expression_relation, expression_lifting, results_match in *.
    destruct IHHT1 as [LCf1 [LCf2 (f1 & f2 & EF1 & EF2 & HRf)]].
    destruct IHHT2 as [LCa1 [LCa2 (a1 & a2 & EA1 & EA2 & HRa)]].
    destruct HRf as [VF1 [VF2 (U1 & b1 & U2 & b2 & E1 & E2 & F)]].
    subst f1 f2. specialize (F a1 a2 HRa).
    destruct F as [LCb1 [LCb2 (r1 & r2 & EB1 & EB2 & HR)]].
    split; [constructor; assumption|]. split; [constructor; assumption|].
    exists r1, r2. repeat split; try assumption.
    + eapply EvalApp; eauto.
    + eapply EvalApp; eauto.
  - destruct HTE as [TS1 [TS2 TM]]. destruct HGE as [GS1 [GS2 GM]].
    assert (HTE0 : type_environment Delta s1 s2 rho) by (repeat split; assumption).
    assert (HGE0 : term_environment Gamma g1 g2 [] rho) by (repeat split; assumption).
    assert (Horig : has_type Delta Gamma (tm_tabs t) (Ty_All T)).
    { eapply T_TAbs with (L := L); eauto. }
    assert (LC1 : locally_closed_tm (instantiate_tm s1 g1 (tm_tabs t))).
    { eapply instantiate_tm_lc; [eapply typing_lc; exact Horig|exact TS1|exact GS1]. }
    assert (LC2 : locally_closed_tm (instantiate_tm s2 g2 (tm_tabs t))).
    { eapply instantiate_tm_lc; [eapply typing_lc; exact Horig|exact TS2|exact GS2]. }
    assert (V1 : value (tm_tabs (instantiate_tm s1 g1 t))) by (constructor; exact LC1).
    assert (V2 : value (tm_tabs (instantiate_tm s2 g2 t))) by (constructor; exact LC2).
    split; [exact LC1|]. split; [exact LC2|].
    exists (tm_tabs (instantiate_tm s1 g1 t)), (tm_tabs (instantiate_tm s2 g2 t)).
    split; [constructor; exact V1|]. split; [constructor; exact V2|].
    split; [exact V1|]. split; [exact V2|].
    exists (instantiate_tm s1 g1 t), (instantiate_tm s2 g2 t).
    split; [reflexivity|]. split; [reflexivity|]. intros U1 U2 a HU1 HU2.
    set (X := fresh_atom (L ++ Delta ++ ftv_context Gamma ++ ftv_tm t ++ fv_ty T)).
    assert (HXall : ~ In X (L ++ Delta ++ ftv_context Gamma ++ ftv_tm t ++ fv_ty T))
      by (apply fresh_atom_not_in).
    repeat rewrite in_app_iff in HXall.
    assert (HXL : ~ In X L) by (intros Q; apply HXall; tauto).
    assert (HXD : ~ In X Delta) by (intros Q; apply HXall; tauto).
    assert (HXG : ~ In X (ftv_context Gamma)) by (intros Q; apply HXall; tauto).
    assert (HXt : ~ In X (ftv_tm t)) by (intros Q; apply HXall; tauto).
    assert (HXT : ~ In X (fv_ty T)) by (intros Q; apply HXall; tauto).
    specialize (H0 X HXL (option_update s1 X U1) (option_update s2 X U2)
      g1 g2 (relation_update rho X a)).
    assert (HTE' : type_environment (X :: Delta) (option_update s1 X U1)
      (option_update s2 X U2) (relation_update rho X a)).
    { apply type_environment_update; assumption. }
    specialize (H0 HTE').
    assert (HGE' : term_environment Gamma g1 g2 [] (relation_update rho X a)).
    { apply term_environment_rho_update; [exact HXG|exact HGE0]. }
    specialize (H0 HGE'). unfold expression_relation, open_tm_ty, open_ty in H0.
    rewrite (instantiate_open_tm_ty t 0 s1 g1 X U1 HXt HU1 TS1 GS1) in H0.
    rewrite (instantiate_open_tm_ty t 0 s2 g2 X U2 HXt HU2 TS2 GS2) in H0.
    assert (HLT : lc_ty_at 1 T).
    { apply lc_ty_all_inv with (k := 0). eapply typing_type_lc; exact Horig. }
    apply (proj1 (expression_lifting_iff _ _
      (value_relation_open T 0 [] rho X a eq_refl HLT HXT) _ _)). exact H0.
  - specialize (IHHT s1 s2 g1 g2 rho HTE HGE).
    unfold expression_relation, expression_lifting, results_match in *.
    destruct IHHT as [LCf1 [LCf2 (f1 & f2 & EF1 & EF2 & HRf)]].
    destruct HRf as [VF1 [VF2 (b1 & b2 & E1 & E2 & F)]]. subst f1 f2.
    assert (HWU : wf_ty Delta U) by assumption.
    assert (HAll : has_type Delta Gamma t (Ty_All T)) by assumption.
    destruct (instantiate_wf_lc _ _ HWU _ _ _ HTE) as [HU1 HU2].
    set (a := semantic_candidate [] rho U (wf_ty_lc _ _ HWU)).
    specialize (F (instantiate_ty s1 U) (instantiate_ty s2 U) a HU1 HU2).
    destruct F as [LCb1 [LCb2 (r1 & r2 & EB1 & EB2 & HR)]].
    assert (HLT : lc_ty_at 1 T).
    { apply lc_ty_all_inv with (k := 0). eapply typing_type_lc; exact HAll. }
    split; [constructor; assumption|]. split; [constructor; assumption|].
    exists r1, r2. repeat split.
    + eapply EvalTApp; eauto.
    + eapply EvalTApp; eauto.
    + apply (proj2 (value_relation_open_closed T 0 [] rho U (wf_ty_lc _ _ HWU)
        eq_refl HLT r1 r2)). exact HR.
Qed.

Lemma instantiate_none_ty : forall T,
  instantiate_ty (fun _ => None) T = T.
Proof. induction T; simpl; congruence. Qed.

Lemma instantiate_none_tm : forall t,
  instantiate_tm (fun _ => None) (fun _ => None) t = t.
Proof.
  induction t; simpl; try rewrite instantiate_none_ty; congruence.
Qed.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof. intros t v H; induction H; assumption. Qed.

Lemma evaluates_lc : forall t v, evaluates t v -> locally_closed_tm t.
Proof.
  intros t v H; induction H.
  - apply value_lc; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma multi_trans : forall x y z, x -->* y -> y -->* z -> x -->* z.
Proof.
  intros x y z H; induction H; intros H2; [exact H2|econstructor; eauto].
Qed.

Lemma multi_app1 : forall f f' a,
  f -->* f' -> locally_closed_tm a -> tm_app f a -->* tm_app f' a.
Proof.
  intros f f' a H; induction H; intros Ha; [constructor|].
  econstructor; [apply ST_App1; eauto|apply IHmulti; exact Ha].
Qed.

Lemma multi_app2 : forall f a a',
  value f -> a -->* a' -> tm_app f a -->* tm_app f a'.
Proof.
  intros f a a' Hf H; induction H; [constructor|].
  econstructor; [apply ST_App2; eauto|exact IHmulti].
Qed.

Lemma multi_tapp : forall f f' U,
  f -->* f' -> locally_closed_ty U -> tm_tapp f U -->* tm_tapp f' U.
Proof.
  intros f f' U H; induction H; intros HU; [constructor|].
  econstructor; [apply ST_TApp; eauto|apply IHmulti; exact HU].
Qed.

Lemma evaluates_multi : forall t v, evaluates t v -> t -->* v.
Proof.
  intros t v H; induction H.
  - constructor.
  - eapply multi_trans.
    + apply multi_app1; [exact IHevaluates1|eapply evaluates_lc; exact H0].
    + eapply multi_trans.
      * apply multi_app2; [eapply evaluates_value; exact H|exact IHevaluates2].
      * eapply multi_step.
        -- apply ST_AppAbs; [apply value_lc; eapply evaluates_value; exact H|eapply evaluates_value; exact H0].
        -- exact IHevaluates3.
  - eapply multi_trans.
    + apply multi_tapp; [exact IHevaluates1|exact H0].
    + eapply multi_step.
      * apply ST_TAppTabs; [apply value_lc; eapply evaluates_value; exact H|exact H0].
      * exact IHevaluates2.
Qed.

Definition singleton_candidate (v : tm) (Hv : value v) : binary_candidate :=
  {| candidate_relation := fun x y => x = v /\ y = v;
     candidate_values := fun x y H =>
       match H with conj Hx Hy =>
         conj (eq_ind_r value Hv Hx) (eq_ind_r value Hv Hy)
       end |}.

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t HT U v HU Hv HTv.
  pose proof (fundamental_theorem _ _ _ _ HT
    (fun _ => None) (fun _ => None) (fun _ => None) (fun _ => None)
    (fun _ => None)) as FUND.
  assert (TE : type_environment [] (fun _ => None) (fun _ => None) (fun _ => None)).
  { repeat split; intros; try discriminate; contradiction. }
  assert (GE : term_environment empty (fun _ => None) (fun _ => None) [] (fun _ => None)).
  { split; [intros x u E; discriminate|].
    split; [intros x u E; discriminate|].
    intros x T E. simpl in E. discriminate. }
  specialize (FUND TE GE).
  repeat rewrite instantiate_none_tm in FUND.
  unfold expression_relation, expression_lifting, results_match in FUND.
  destruct FUND as [LCt1 [LCt2 (w1 & w2 & Et1 & Et2 & HRall)]].
  destruct HRall as [Vw1 [Vw2 (b1 & b2 & Ew1 & Ew2 & Fall)]].
  subst w1 w2.
  set (c := singleton_candidate v Hv).
  specialize (Fall U U c (wf_ty_lc _ _ HU) (wf_ty_lc _ _ HU)).
  destruct Fall as [LCB1 [LCB2 (f1 & f2 & EB1 & EB2 & HRarr)]].
  destruct HRarr as [Vf1 [Vf2 (A1 & d1 & A2 & d2 & Ef1 & Ef2 & Farr)]].
  subst f1 f2.
  assert (Hcv : value_relation [c] (fun _ => None) (Ty_BVar 0) v v).
  { simpl. split; reflexivity. }
  specialize (Farr v v Hcv).
  destruct Farr as [LCD1 [LCD2 (r1 & r2 & ED1 & ED2 & HRc)]].
  simpl in HRc. destruct HRc as [-> Hr2].
  apply evaluates_multi.
  eapply EvalApp.
  - eapply EvalTApp; [exact Et1|apply wf_ty_lc with (D := []); exact HU|exact EB1].
  - constructor; exact Hv.
  - exact ED1.
Qed.

End SystemFParametricityNoneMediumTask.
