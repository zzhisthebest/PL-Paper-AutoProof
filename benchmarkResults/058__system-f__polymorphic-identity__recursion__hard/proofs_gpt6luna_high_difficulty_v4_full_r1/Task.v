(** System F parametricity benchmark, Hard variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityRecursionHardTask.

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
  | Ty_Nat : ty.

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
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_natrec : tm -> tm -> tm -> tm.

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

Notation "'Nat'" := Ty_Nat (in custom systemf_ty at level 0) : systemf_scope.
Notation "'zero'" := tm_zero (in custom systemf_tm at level 0) : systemf_scope.
Notation "'succ' t" := (tm_succ t) (in custom systemf_tm at level 9, t custom systemf_tm at level 0) : systemf_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom systemf_tm at level 9, n custom systemf_tm at level 0, b custom systemf_tm at level 0, s custom systemf_tm at level 0) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  | Ty_Nat => Ty_Nat
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_rec k u t1)
  | tm_natrec n b f => tm_natrec (open_tm_rec k u n) (open_tm_rec k u b) (open_tm_rec k u f)
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_ty_rec k U t1)
  | tm_natrec n b f => tm_natrec (open_tm_ty_rec k U n) (open_tm_ty_rec k U b) (open_tm_ty_rec k U f)
  end.

Definition open_tm_ty (t : tm) (U : ty) : tm :=
  open_tm_ty_rec 0 U t.

Fixpoint ty_subst (X : atom) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then U else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst X U T1) (ty_subst X U T2)
  | Ty_All T1 => Ty_All (ty_subst X U T1)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_ty_subst X U t1)
  | tm_natrec n b f => tm_natrec (tm_ty_subst X U n) (tm_ty_subst X U b) (tm_ty_subst X U f)
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst x s t1)
  | tm_natrec n b f => tm_natrec (tm_subst x s n) (tm_subst x s b) (tm_subst x s f)
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
  | lc_ty_nat : forall k, lc_ty_at k Ty_Nat.

Definition locally_closed_ty (T : ty) : Prop := lc_ty_at 0 T.

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fvars A ++ ty_fvars B
  | Ty_All A => ty_fvars A
  | Ty_Nat => []
  end.

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
  | lc_tm_zero : forall K k, lc_tm_at K k tm_zero
  | lc_tm_succ : forall K k t, lc_tm_at K k t -> lc_tm_at K k (tm_succ t)
  | lc_tm_rec : forall K k n b s,
      lc_tm_at K k n -> lc_tm_at K k b -> lc_tm_at K k s -> lc_tm_at K k (tm_natrec n b s).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Fixpoint tm_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T b => ty_fvars T ++ tm_fvars b
  | tm_app a b => tm_fvars a ++ tm_fvars b
  | tm_tabs b => tm_fvars b
  | tm_tapp a T => tm_fvars a ++ ty_fvars T
  | tm_zero => []
  | tm_succ a => tm_fvars a
  | tm_natrec n b s => tm_fvars n ++ tm_fvars b ++ tm_fvars s
  end.

Fixpoint tm_term_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => tm_term_fvars b
  | tm_app a b => tm_term_fvars a ++ tm_term_fvars b
  | tm_tabs b => tm_term_fvars b
  | tm_tapp a _ => tm_term_fvars a
  | tm_zero => []
  | tm_succ a => tm_term_fvars a
  | tm_natrec n b s => tm_term_fvars n ++ (tm_term_fvars b ++ tm_term_fvars s)
  end.

Lemma tm_term_fvars_open_ty_rec : forall k U t,
  tm_term_fvars (open_tm_ty_rec k U t) = tm_term_fvars t.
Proof.
  intros k U t. revert k. induction t; intros k; simpl.
  - reflexivity.
  - reflexivity.
  - apply IHt.
  - rewrite IHt1, IHt2. reflexivity.
  - apply IHt.
  - apply IHt.
  - reflexivity.
  - apply IHt.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma term_fvars_open_inv : forall k t z x,
  In x (tm_term_fvars (open_tm_rec k (tm_fvar z) t)) ->
  x = z \/ In x (tm_term_fvars t).
Proof.
  intros k t. revert k. induction t; intros k z x H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl in H.
    + destruct H as [<-|[]]. left. reflexivity.
    + contradiction.
  - simpl in H. destruct H as [<-|[]]. auto.
  - eapply IHt. exact H.
  - apply in_app_iff in H as [H|H].
    + destruct (IHt1 k z x H) as [->|Hin].
      * left. reflexivity.
      * right. apply in_or_app. left. exact Hin.
    + destruct (IHt2 k z x H) as [->|Hin].
      * left. reflexivity.
      * right. apply in_or_app. right. exact Hin.
  - eapply IHt. exact H.
  - eapply IHt. exact H.
  - contradiction.
  - eapply IHt. exact H.
  - apply in_app_iff in H as [H|H].
    + destruct (IHt1 k z x H) as [->|Hin].
      * left. reflexivity.
      * right. apply in_or_app. left. exact Hin.
    + apply in_app_iff in H as [H|H].
      * destruct (IHt2 k z x H) as [->|Hin].
        -- left. reflexivity.
        -- right. apply in_or_app. right. apply in_or_app. left. exact Hin.
      * destruct (IHt3 k z x H) as [->|Hin].
        -- left. reflexivity.
        -- right. apply in_or_app. right. apply in_or_app. right. exact Hin.
Qed.

Lemma term_fvars_open_preserve : forall k t z x,
  In x (tm_term_fvars t) -> x <> z ->
  In x (tm_term_fvars (open_tm_rec k (tm_fvar z) t)).
Proof.
  intros k t. revert k. induction t; intros k z x H Hneq; simpl in *.
  - destruct (Nat.eqb k n); simpl in H; contradiction.
  - simpl in *. destruct H as [<-|[]]. simpl. auto.
  - eapply IHt; eauto.
  - apply in_app_iff in H as [H|H]; apply in_app_iff; [left|right]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - contradiction.
  - eapply IHt; eauto.
  - apply in_app_iff in H as [H|H].
    + apply in_or_app. left. eapply IHt1; eauto.
    + apply in_app_iff in H as [H|H].
      * apply in_or_app. right. apply in_or_app. left. eapply IHt2; eauto.
      * apply in_or_app. right. apply in_or_app. right. eapply IHt3; eauto.
Qed.



Lemma ty_fvars_open_rec_in : forall k U T X,
  In X (ty_fvars T) -> In X (ty_fvars (open_ty_rec k U T)).
Proof.
  intros k U T. revert k. induction T; intros k X H; simpl in *.
  - contradiction.
  - assumption.
  - apply in_app_iff in H as [H|H]; apply in_app_iff; [left|right];
      [eapply IHT1|eapply IHT2]; eauto.
  - eapply IHT; eauto.
  - contradiction.
Qed.

Inductive numeric_value : tm -> Prop :=
  | nv_zero : numeric_value tm_zero
  | nv_succ : forall (n : tm), numeric_value n -> numeric_value (tm_succ n).

Fixpoint numeral (n : nat) : tm :=
  match n with O => tm_zero | S m => tm_succ (numeral m) end.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_nat : forall n, numeric_value n -> value n.

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
  | ST_Succ : forall t t',
      t --> t' -> tm_succ t --> tm_succ t'
  | ST_RecArg : forall n n' b s,

      n --> n' -> locally_closed_tm b -> locally_closed_tm s ->
      tm_natrec n b s --> tm_natrec n' b s
  | ST_RecBase : forall n b b' s,

      numeric_value n -> b --> b' -> locally_closed_tm s ->
      tm_natrec n b s --> tm_natrec n b' s
  | ST_RecStep : forall n b s s',

      numeric_value n -> value b -> s --> s' ->
      tm_natrec n b s --> tm_natrec n b s'
  | ST_RecZero : forall b s,

      value b -> value s -> tm_natrec tm_zero b s --> b
  | ST_RecSucc : forall n b s,

      numeric_value n -> value b -> value s ->
      tm_natrec (tm_succ n) b s -->
        tm_app (tm_app s n) (tm_natrec n b s)
where "t1 '-->' t2" := (step t1 t2).

Definition ty_context := list atom.

Definition context := list (atom * ty).

Fixpoint context_vars (Gamma : context) : list atom :=
  match Gamma with [] => [] | (x, _) :: Gamma' => x :: context_vars Gamma' end.

Fixpoint context_ty_fvars (Gamma : context) : list atom :=
  match Gamma with [] => [] | (_, T) :: Gamma' => ty_fvars T ++ context_ty_fvars Gamma' end.

Fixpoint lookup_context (x : atom) (Gamma : context) : option ty :=
  match Gamma with
  | [] => None
  | (y, T) :: Gamma' =>
      if Nat.eqb x y then Some T else lookup_context x Gamma'
  end.

Lemma lookup_context_in : forall x Gamma T,
  lookup_context x Gamma = Some T -> In x (context_vars Gamma).
Proof.
  intros x Gamma. induction Gamma as [|[y U] Gamma IH]; intros T H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. left. reflexivity.
    + right. eapply IH; eauto.
Qed.

Lemma lookup_context_notin : forall x Gamma,
  ~ In x (context_vars Gamma) -> lookup_context x Gamma = None.
Proof.
  intros x Gamma. induction Gamma as [|[y U] Gamma IH]; intros H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + exfalso. apply H. left. apply Nat.eqb_eq in E. symmetry. exact E.
    + apply IH. intro Hin. apply H. right. exact Hin.
Qed.

Definition empty : context := [].

Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  (x, T) :: Gamma.

Lemma lookup_context_update_same : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros; simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_context_update_other : forall Gamma x y T,
  x <> y -> lookup_context x (update Gamma y T) = lookup_context x Gamma.
Proof.
  intros Gamma x y T Hneq. simpl. assert (Nat.eqb x y = false) by (apply Nat.eqb_neq; exact Hneq).
  rewrite H. reflexivity.
Qed.

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
  | WF_Nat : forall Delta, wf_ty Delta Ty_Nat.

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
  | T_Zero : forall Delta Gamma, has_type Delta Gamma tm_zero Ty_Nat
  | T_Succ : forall Delta Gamma n,
      has_type Delta Gamma n Ty_Nat -> has_type Delta Gamma (tm_succ n) Ty_Nat
  | T_Rec : forall Delta Gamma n b s T,
      has_type Delta Gamma n Ty_Nat -> has_type Delta Gamma b T ->
      has_type Delta Gamma s (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ->
      has_type Delta Gamma (tm_natrec n b s) T.



Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).


Hint Constructors lc_ty_at lc_tm_at value : core.

(* A call-by-value, binary logical relation.  The relation on expressions
   observes their final values; the relation on values is indexed by types. *)
Definition term_closed (t : tm) : Prop := forall x, ~ In x (tm_term_fvars t).



Definition evaluates_to (t v : tm) : Prop := multi t v /\ value v /\ term_closed v.

Definition rel_exp (R : tm -> tm -> Prop) (t1 t2 : tm) : Prop :=
  locally_closed_tm t1 /\ locally_closed_tm t2 /\
  exists v1 v2, evaluates_to t1 v1 /\ evaluates_to t2 v2 /\ R v1 v2.

Definition singleton_rel (v : tm) : tm -> tm -> Prop :=
  fun a b => a = v /\ b = v.

Lemma rel_exp_singleton_left : forall v t1 t2,
  rel_exp (singleton_rel v) t1 t2 -> multi t1 v.
Proof.
  intros v t1 t2 H. unfold rel_exp, evaluates_to, singleton_rel in H.
  destruct H as [_ H]. destruct H as [_ H]. destruct H as [v1 H].
  destruct H as [v2 H]. destruct H as [Ev1 H]. destruct H as [Ev2 H]. destruct H as [E1 E2].
  destruct Ev1 as [H1 _]. subst. exact H1.
Qed.

Lemma rel_exp_singleton_right : forall v t1 t2,
  rel_exp (singleton_rel v) t1 t2 -> multi t2 v.
Proof.
  intros v t1 t2 H. unfold rel_exp, evaluates_to, singleton_rel in H.
  destruct H as [_ H]. destruct H as [_ H]. destruct H as [v1 H].
  destruct H as [v2 H]. destruct H as [Ev1 H]. destruct H as [Ev2 H]. destruct H as [E1 E2].
  destruct Ev2 as [H2 _]. subst. exact H2.
Qed.

Definition rel_env := list (atom * (ty * ty * (tm -> tm -> Prop))).

Fixpoint rel_env_keys (E : rel_env) : list atom :=
  match E with [] => [] | (X, _) :: E' => X :: rel_env_keys E' end.

Fixpoint lookup_rel (X : atom) (E : rel_env) : option (ty * ty * (tm -> tm -> Prop)) :=
  match E with
  | [] => None
  | (Y, A) :: E' => if Nat.eqb X Y then Some A else lookup_rel X E'
  end.

Lemma lookup_rel_insert_same : forall X Q E,
  lookup_rel X ((X,Q)::E) = Some Q.
Proof. intros; simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_rel_insert_neq : forall X Y Q E,
  X <> Y -> lookup_rel X ((Y,Q)::E) = lookup_rel X E.
Proof.
  intros X Y Q E Hneq. simpl. assert (Nat.eqb X Y = false) by (apply Nat.eqb_neq; exact Hneq).
  rewrite H. reflexivity.
Qed.

Definition bound_env := list (ty * ty * (tm -> tm -> Prop)).

Definition ty_subst_env := list (atom * ty).
Definition tm_subst_env := list (atom * tm).

Fixpoint lookup_ty_subst (X : atom) (S : ty_subst_env) : option ty :=
  match S with
  | [] => None
  | (Y, U) :: S' => if Nat.eqb X Y then Some U else lookup_ty_subst X S'
  end.

Fixpoint subst_ty_env (S : ty_subst_env) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => match lookup_ty_subst X S with Some U => U | None => Ty_FVar X end
  | Ty_Arrow A B => Ty_Arrow (subst_ty_env S A) (subst_ty_env S B)
  | Ty_All A => Ty_All (subst_ty_env S A)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint subst_tm_types (S : ty_subst_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (subst_ty_env S T) (subst_tm_types S b)
  | tm_app a b => tm_app (subst_tm_types S a) (subst_tm_types S b)
  | tm_tabs b => tm_tabs (subst_tm_types S b)
  | tm_tapp a T => tm_tapp (subst_tm_types S a) (subst_ty_env S T)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (subst_tm_types S a)
  | tm_natrec n b s => tm_natrec (subst_tm_types S n) (subst_tm_types S b) (subst_tm_types S s)
  end.

Fixpoint lookup_tm_subst (x : atom) (S : tm_subst_env) : option tm :=
  match S with
  | [] => None
  | (y, u) :: S' => if Nat.eqb x y then Some u else lookup_tm_subst x S'
  end.

Fixpoint subst_tm_env (S : tm_subst_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => match lookup_tm_subst x S with Some u => u | None => tm_fvar x end
  | tm_abs T b => tm_abs T (subst_tm_env S b)
  | tm_app a b => tm_app (subst_tm_env S a) (subst_tm_env S b)
  | tm_tabs b => tm_tabs (subst_tm_env S b)
  | tm_tapp a T => tm_tapp (subst_tm_env S a) T
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (subst_tm_env S a)
  | tm_natrec n b s => tm_natrec (subst_tm_env S n) (subst_tm_env S b) (subst_tm_env S s)
  end.

Lemma subst_ty_open_rec : forall S k X U T,
  subst_ty_env ((X, U) :: S) U = U ->
  subst_ty_env ((X, U) :: S) (open_ty_rec k (Ty_FVar X) T) =
  subst_ty_env ((X, U) :: S) (open_ty_rec k U T).
Proof.
  intros S k X U T Hsub. revert k. induction T; intros k; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + unfold subst_ty_env. simpl. rewrite Nat.eqb_refl. symmetry. exact Hsub.
    + reflexivity.
  - destruct (Nat.eqb a X); reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
  - rewrite IHT. reflexivity.
  - reflexivity.
Qed.

Lemma subst_tm_types_open_rec : forall S k X U t,
  subst_ty_env ((X, U) :: S) U = U ->
  subst_tm_types ((X, U) :: S) (open_tm_ty_rec k (Ty_FVar X) t) =
  subst_tm_types ((X, U) :: S) (open_tm_ty_rec k U t).
Proof.
  intros S k X U t Hsub. revert k. induction t; intros k; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (subst_ty_open_rec S k X U t Hsub), IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt, (subst_ty_open_rec S k X U t0 Hsub). reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma subst_tm_types_open_tm_rec : forall S k u t,
  subst_tm_types S (open_tm_rec k u t) =
  open_tm_rec k (subst_tm_types S u) (subst_tm_types S t).
Proof.
  intros S k u t. revert k. induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma open_ty_rec_lc_identity : forall K U,
  lc_ty_at K U -> forall k W, K <= k -> open_ty_rec k W U = U.
Proof.
  intros K U Hlc. induction Hlc; intros j Y Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - rewrite IHHlc1, IHHlc2; try lia. reflexivity.
  - rewrite IHHlc. f_equal. lia.
  - reflexivity.
Qed.

Lemma subst_ty_env_open_rec_fixed : forall S k U T,
  subst_ty_env S U = U ->
  (forall X V, lookup_ty_subst X S = Some V -> locally_closed_ty V) ->
  subst_ty_env S (open_ty_rec k U T) = open_ty_rec k U (subst_ty_env S T).
Proof.
  intros S k U T Hfixed Hclosed. revert k. induction T; intros k; simpl.
  - destruct (Nat.eqb k n); simpl; [rewrite Hfixed|]; reflexivity.
  - destruct (lookup_ty_subst a S) as [V|] eqn:Hv; simpl.
    + rewrite (open_ty_rec_lc_identity 0 V (Hclosed a V Hv) k U (Nat.le_0_l k)). reflexivity.
    + reflexivity.
  - rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
  - reflexivity.
Qed.

Lemma subst_tm_types_open_ty_rec : forall S k U t,
  subst_ty_env S U = U ->
  (forall X V, lookup_ty_subst X S = Some V -> locally_closed_ty V) ->
  subst_tm_types S (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (subst_tm_types S t).
Proof.
  intros S k U t Hfixed Hclosed. revert k. induction t; intros k; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (subst_ty_env_open_rec_fixed S k U t Hfixed Hclosed), IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt, (subst_ty_env_open_rec_fixed S k U t0 Hfixed Hclosed). reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma subst_tm_env_open_rec : forall S k x v t,
  subst_tm_env ((x, v) :: S) v = v ->
  subst_tm_env ((x, v) :: S) (open_tm_rec k (tm_fvar x) t) =
  subst_tm_env ((x, v) :: S) (open_tm_rec k v t).
Proof.
  intros S k x v t Hsub. revert k. induction t; intros k; simpl.
  - destruct (Nat.eqb k n).
    + unfold subst_tm_env. simpl. rewrite Nat.eqb_refl. symmetry. exact Hsub.
    + reflexivity.
  - destruct (Nat.eqb a x) eqn:E.
    + unfold subst_tm_env. simpl. reflexivity.
    + reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma lookup_tm_subst_notin : forall x S,
  ~ In x (map fst S) -> lookup_tm_subst x S = None.
Proof.
  intros x S. induction S as [|[y v] S IH]; intros H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. left. reflexivity.
    + apply IH. intro Hin. apply H. right. exact Hin.
Qed.

Lemma subst_tm_env_fresh_insert : forall S x v t,
  ~ In x (tm_fvars t) ->
  subst_tm_env ((x,v)::S) t = subst_tm_env S t.
Proof.
  intros S x v t. induction t; intros H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. simpl; auto.
    + reflexivity.
  - f_equal. apply IHt. intro Hin. apply H. apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply H. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply H. apply in_or_app; right; exact Hin.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. intro Hin. apply H. apply in_or_app; left; exact Hin.
  - reflexivity.
  - f_equal. apply IHt. exact H.
  - f_equal.
    + apply IHt1. intro Hin. apply H. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply H. apply in_or_app; right. apply in_or_app; left; exact Hin.
    + apply IHt3. intro Hin. apply H. apply in_or_app; right. apply in_or_app; right; exact Hin.
Qed.

Lemma subst_tm_env_term_closed_fixed : forall S t,
  term_closed t -> subst_tm_env S t = t.
Proof.
  intros S t. induction t; intros Hclosed; unfold term_closed in *; simpl in *.
  - reflexivity.
  - exfalso. specialize (Hclosed a). apply Hclosed. simpl; auto.
  - f_equal. apply IHt. exact Hclosed.
  - f_equal.
    + apply IHt1. intros x Hin. exfalso. apply (Hclosed x). apply in_or_app; left; exact Hin.
    + apply IHt2. intros x Hin. exfalso. apply (Hclosed x). apply in_or_app; right; exact Hin.
  - f_equal. apply IHt. exact Hclosed.
  - f_equal. apply IHt. exact Hclosed.
  - reflexivity.
  - f_equal. apply IHt. exact Hclosed.
  - f_equal.
    + apply IHt1. intros x Hin. exfalso. apply (Hclosed x). apply in_or_app; left; exact Hin.
    + apply IHt2. intros x Hin. exfalso. apply (Hclosed x). apply in_or_app; right. apply in_or_app; left; exact Hin.
    + apply IHt3. intros x Hin. exfalso. apply (Hclosed x). apply in_or_app; right. apply in_or_app; right; exact Hin.
Qed.

Fixpoint lookup_bound (i : nat) (E : bound_env) : option (ty * ty * (tm -> tm -> Prop)) :=
  match i, E with
  | O, (A :: _) => Some A
  | S j, (_ :: E') => lookup_bound j E'
  | _, [] => None
  end.

Fixpoint interp (E : rel_env) (D : bound_env) (T : ty) {struct T} : tm -> tm -> Prop :=
  match T with
  | Ty_BVar i =>
      match lookup_bound i D with
      | Some (_, _, R) => R
      | None => fun _ _ => False
      end
  | Ty_FVar X =>
      match lookup_rel X E with
      | Some (_, _, R) => R
      | None => fun _ _ => False
      end
  | Ty_Arrow A B => fun f1 f2 =>
      value f1 /\ value f2 /\
      forall a1 a2, rel_exp (interp E D A) a1 a2 ->
        rel_exp (interp E D B) (tm_app f1 a1) (tm_app f2 a2)
  | Ty_All A => fun f1 f2 =>
      value f1 /\ value f2 /\
      forall U1 U2 (R : tm -> tm -> Prop),
        wf_ty [] U1 -> wf_ty [] U2 ->
        rel_exp (interp E ((U1, U2, R) :: D) A)
          (tm_tapp f1 U1) (tm_tapp f2 U2)
  | Ty_Nat => fun n1 n2 => exists n, n1 = numeral n /\ n2 = numeral n
  end.

Fixpoint rel_ty_env_left (E : rel_env) : ty_subst_env :=
  match E with
  | [] => []
  | (X, (A, _, _)) :: E' => (X, A) :: rel_ty_env_left E'
  end.

Fixpoint rel_ty_env_right (E : rel_env) : ty_subst_env :=
  match E with
  | [] => []
  | (X, (_, B, _)) :: E' => (X, B) :: rel_ty_env_right E'
  end.

Lemma lookup_ty_subst_rel_left : forall E X A B R,
  lookup_rel X E = Some (A,B,R) ->
  lookup_ty_subst X (rel_ty_env_left E) = Some A.
Proof.
  intros E. induction E as [|[Y Q] E IH]; intros X A B R H; simpl in *.
  - discriminate.
  - destruct Q as [[A0 B0] R0]. destruct (Nat.eqb X Y) eqn:Eeq.
    + inversion H; subst. unfold lookup_ty_subst. simpl. rewrite Eeq. reflexivity.
    + unfold lookup_ty_subst. simpl. rewrite Eeq. eapply IH; eauto.
Qed.

Lemma lookup_ty_subst_rel_right : forall E X A B R,
  lookup_rel X E = Some (A,B,R) ->
  lookup_ty_subst X (rel_ty_env_right E) = Some B.
Proof.
  intros E. induction E as [|[Y Q] E IH]; intros X A B R H; simpl in *.
  - discriminate.
  - destruct Q as [[A0 B0] R0]. destruct (Nat.eqb X Y) eqn:Eeq.
    + inversion H; subst. unfold lookup_ty_subst. simpl. rewrite Eeq. reflexivity.
    + unfold lookup_ty_subst. simpl. rewrite Eeq. eapply IH; eauto.
Qed.

Definition tm_rel_env := list (atom * (tm * tm)).

Fixpoint tm_rel_env_left (M : tm_rel_env) : tm_subst_env :=
  match M with
  | [] => []
  | (x, (a, _)) :: M' => (x, a) :: tm_rel_env_left M'
  end.

Fixpoint tm_rel_env_right (M : tm_rel_env) : tm_subst_env :=
  match M with
  | [] => []
  | (x, (_, b)) :: M' => (x, b) :: tm_rel_env_right M'
  end.

Fixpoint lookup_tm_rel (x : atom) (M : tm_rel_env) : option (tm * tm) :=
  match M with
  | [] => None
  | (y, p) :: M' => if Nat.eqb x y then Some p else lookup_tm_rel x M'
  end.

Lemma lookup_tm_rel_cons_same : forall x a b M,
  lookup_tm_rel x ((x,(a,b))::M) = Some (a,b).
Proof. intros; simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_tm_rel_cons_neq : forall x y a b M,
  x <> y -> lookup_tm_rel x ((y,(a,b))::M) = lookup_tm_rel x M.
Proof.
  intros x y a b M Hneq. simpl. assert (Nat.eqb x y = false) by (apply Nat.eqb_neq; exact Hneq).
  rewrite H. reflexivity.
Qed.

Lemma lookup_tm_rel_left : forall x M a,
  lookup_tm_subst x (tm_rel_env_left M) = Some a ->
  exists b, lookup_tm_rel x M = Some (a, b).
Proof.
  intros x M. induction M as [|[y [a0 b0]] M IH]; intros a H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; subst. exists b0. simpl. reflexivity.
    + destruct (IH a H) as [b Hb]. exists b. simpl. exact Hb.
Qed.

Lemma lookup_tm_rel_right : forall x M b,
  lookup_tm_subst x (tm_rel_env_right M) = Some b ->
  exists a, lookup_tm_rel x M = Some (a, b).
Proof.
  intros x M. induction M as [|[y [a0 b0]] M IH]; intros b H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; subst. exists a0. simpl. reflexivity.
    + destruct (IH b H) as [a Ha]. exists a. simpl. exact Ha.
Qed.

Lemma lookup_tm_rel_left_from : forall x M a b,
  lookup_tm_rel x M = Some (a, b) ->
  lookup_tm_subst x (tm_rel_env_left M) = Some a.
Proof.
  intros x M. induction M as [|[y [a0 b0]] M IH]; intros a b H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; reflexivity.
    + eapply IH; eauto.
Qed.

Lemma lookup_tm_rel_right_from : forall x M a b,
  lookup_tm_rel x M = Some (a, b) ->
  lookup_tm_subst x (tm_rel_env_right M) = Some b.
Proof.
  intros x M. induction M as [|[y [a0 b0]] M IH]; intros a b H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; reflexivity.
    + eapply IH; eauto.
Qed.

Definition rel_ty_env_ok (Delta : ty_context) (E : rel_env) : Prop :=
  forall X, In X Delta -> exists A B R,
    lookup_rel X E = Some (A, B, R) /\ wf_ty [] A /\ wf_ty [] B.

Definition rel_tm_env_ok (E : rel_env) (Gamma : context) (M : tm_rel_env) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    exists a b, lookup_tm_rel x M = Some (a, b) /\ value a /\ value b /\
      interp E [] T a b.

Lemma lookup_context_type_fvars : forall x Gamma T X,
  lookup_context x Gamma = Some T -> In X (ty_fvars T) ->
  In X (context_ty_fvars Gamma).
Proof.
  intros x Gamma. induction Gamma as [|[y U] Gamma IH]; intros T X Hlookup Hfv; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left. exact Hfv.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma rel_ty_env_ok_cons : forall Delta E X A B R,
  ~ In X Delta -> rel_ty_env_ok Delta E -> wf_ty [] A -> wf_ty [] B ->
  rel_ty_env_ok (X::Delta) ((X,(A,B,R))::E).
Proof.
  intros Delta E X A B R Hfresh Hold HWA HWB Y HY.
  simpl in HY. destruct HY as [->|HY].
  - exists A,B,R. rewrite lookup_rel_insert_same. auto.
  - assert (Hneq : Y <> X) by (intro E'; subst; contradiction).
    destruct (Hold Y HY) as [A' [B' [R' [Hlook [H1 H2]]]]].
    exists A',B',R'. rewrite lookup_rel_insert_neq by congruence. auto.
Qed.

Lemma rel_tm_env_ok_extend : forall E Gamma M x T a b,
  ~ In x (context_vars Gamma) -> rel_tm_env_ok E Gamma M ->
  value a -> value b -> interp E [] T a b ->
  rel_tm_env_ok E (update Gamma x T) ((x,(a,b))::M).
Proof.
  intros E Gamma M x T a b Hfresh HM Ha Hb Hab y T' Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:Eyx.
  - apply Nat.eqb_eq in Eyx. subst y. inversion Hlookup; subst T'.
    exists a,b. repeat split; auto. apply lookup_tm_rel_cons_same.
  - assert (Hyx : y <> x) by (intro Heq; subst; rewrite Nat.eqb_refl in Eyx; discriminate).
    destruct (HM y T' Hlookup) as [a' [b' [Hpair [Ha' [Hb' Hab']]]]].
    exists a', b'. repeat split; try assumption.
    rewrite lookup_tm_rel_cons_neq by congruence. exact Hpair.
Qed.

Definition rel_ty_env_closed (E : rel_env) : Prop :=
  (forall X U, lookup_ty_subst X (rel_ty_env_left E) = Some U -> wf_ty [] U) /\
  (forall X U, lookup_ty_subst X (rel_ty_env_right E) = Some U -> wf_ty [] U).

Lemma rel_ty_env_closed_cons : forall E X A B R,
  rel_ty_env_closed E -> wf_ty [] A -> wf_ty [] B ->
  rel_ty_env_closed ((X,(A,B,R))::E).
Proof.
  intros E X A B R [HL HR] HWA HWB. unfold rel_ty_env_closed in *.
  simpl. split; intros Y U Hlook; destruct (Nat.eqb Y X) eqn:Eyx.
  - inversion Hlook; subst. exact HWA.
  - exact (HL Y U Hlook).
  - inversion Hlook; subst. exact HWB.
  - exact (HR Y U Hlook).
Qed.

Definition rel_tm_env_closed (M : tm_rel_env) : Prop :=
  forall x a b, lookup_tm_rel x M = Some (a, b) -> value a /\ value b /\ term_closed a /\ term_closed b.

Lemma rel_tm_env_closed_cons : forall M x a b,
  value a -> value b -> term_closed a -> term_closed b -> rel_tm_env_closed M ->
  rel_tm_env_closed ((x,(a,b))::M).
Proof.
  intros M x a b Ha Hb Hca Hcb HM y u v Hlook. simpl in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlook; subst. repeat split; assumption.
  - exact (HM y u v Hlook).
Qed.

Lemma multi_trans : forall a b c, multi a b -> multi b c -> multi a c.
Proof.
  intros a b c Hab Hbc. induction Hab.
  - exact Hbc.
  - econstructor; eauto.
Qed.

Lemma multi_one : forall a b, a --> b -> multi a b.
Proof. intros; econstructor; eauto using multi_refl. Qed.

Lemma multi_app_l : forall a a' b, multi a a' -> locally_closed_tm b ->
  multi (tm_app a b) (tm_app a' b).
Proof.
  intros a a' b H. induction H; intros Hlc.
  - constructor.
  - eapply multi_step.
    + eapply ST_App1; eauto.
    + eapply IHmulti. exact Hlc.
Qed.

Lemma multi_app_r : forall a b b', value a -> multi b b' ->
  multi (tm_app a b) (tm_app a b').
Proof.
  intros a b b' Ha H. induction H.
  - constructor.
  - econstructor; [eapply ST_App2; eauto|]. exact IHmulti.
Qed.

Lemma multi_tapp : forall a a' U, multi a a' -> locally_closed_ty U ->
  multi (tm_tapp a U) (tm_tapp a' U).
Proof.
  intros a a' U H. induction H.
  - constructor.
  - econstructor; [eapply ST_TApp; eauto|]. exact (IHmulti H1).
Qed.

Lemma multi_succ : forall a a', multi a a' ->
  multi (tm_succ a) (tm_succ a').
Proof.
  intros a a' H. induction H; [constructor|].
  eapply multi_step; [eapply ST_Succ; eauto|exact IHmulti].
Qed.

Lemma numeric_value_numeral : forall n, numeric_value n ->
  exists k, n = numeral k.
Proof.
  intros n H. induction H.
  - exists 0. reflexivity.
  - destruct IHnumeric_value as [k ->]. exists (S k). reflexivity.
Qed.

Lemma numeral_numeric_value : forall n, numeric_value (numeral n).
Proof. induction n; simpl; constructor; assumption. Qed.

Lemma rel_exp_left_reduce : forall R a a' b,
  locally_closed_tm a -> multi a a' -> rel_exp R a' b -> rel_exp R a b.
Proof.
  intros R a a' b Hlc Hm [Hlc' [HlcB [v1 [v2 [Ha [Hb HR]]]]]].
  split; [exact Hlc|]. split; [exact HlcB|]. exists v1,v2. split.
  - destruct Ha as [Ha [Hva Hca]]. split; [eapply multi_trans; eauto|]. split; assumption.
  - split; [exact Hb|exact HR].
Qed.

Lemma rel_exp_right_reduce : forall R a b b',
  locally_closed_tm b -> multi b b' -> rel_exp R a b' -> rel_exp R a b.
Proof.
  intros R a b b' Hlc Hm [HlcA [Hlc' [v1 [v2 [Ha [Hb HR]]]]]].
  split; [exact HlcA|]. split; [exact Hlc|]. exists v1,v2. split.
  - exact Ha.
  - split.
    + destruct Hb as [Hb [Hvb Hcb]]. split; [eapply multi_trans; [exact Hm|exact Hb]|].
      split; assumption.
    + exact HR.
Qed.

Lemma rel_exp_mor : forall R S a b,
  (forall x y, R x y <-> S x y) ->
  (rel_exp R a b <-> rel_exp S a b).
Proof.
  intros R S a b Hrel. unfold rel_exp. split.
  - intros [HlcA [HlcB [v1 [v2 [H1 [H2 H12]]]]]].
    split; [exact HlcA|]. split; [exact HlcB|]. exists v1,v2. split; [exact H1|].
    split; [exact H2|]. apply Hrel. exact H12.
  - intros [HlcA [HlcB [v1 [v2 [H1 [H2 H12]]]]]].
    split; [exact HlcA|]. split; [exact HlcB|]. exists v1,v2. split; [exact H1|].
    split; [exact H2|]. apply Hrel. exact H12.
Qed.

Lemma interp_env_irrel : forall E X Q D T,
  ~ In X (ty_fvars T) ->
  forall a b, interp ((X, Q) :: E) D T a b <-> interp E D T a b.
Proof.
  intros E X Q D T. revert D. induction T; intros D Hfresh v1 v2; simpl in *.
  - tauto.
  - destruct (Nat.eqb a X) eqn:Eeq.
    + apply Nat.eqb_eq in Eeq. subst. exfalso. apply Hfresh. simpl. auto.
    + simpl. destruct (lookup_rel a E); tauto.
  - split.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros x y Hxy. apply rel_exp_mor with (R := interp ((X, Q) :: E) D T1) (S := interp E D T1) in Hxy.
      * specialize (Hfn x y Hxy). apply rel_exp_mor with (R := interp ((X,Q)::E) D T2) (S := interp E D T2); [|exact Hfn].
        intros u v. apply (IHT2 D). intro Hin. apply Hfresh. apply in_app_iff. right. exact Hin.
      * intros u v. apply (IHT1 D). intro Hin. apply Hfresh. apply in_app_iff. left. exact Hin.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros x y Hxy. apply rel_exp_mor with (R := interp E D T1) (S := interp ((X,Q)::E) D T1) in Hxy.
      * specialize (Hfn x y Hxy). apply rel_exp_mor with (R := interp E D T2) (S := interp ((X,Q)::E) D T2); [|exact Hfn].
        intros u v. symmetry. apply (IHT2 D). intro Hin. apply Hfresh. apply in_app_iff. right. exact Hin.
      * intros u v. symmetry. apply (IHT1 D). intro Hin. apply Hfresh. apply in_app_iff. left. exact Hin.
  - split.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 R HU1 HU2.
      apply rel_exp_mor with
        (R := interp ((X,Q)::E) ((U1,U2,R)::D) T)
        (S := interp E ((U1,U2,R)::D) T).
      * intros u v. apply (IHT ((U1,U2,R)::D)). intro Hin. apply Hfresh. exact Hin.
      * apply Hfn; assumption.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 R HU1 HU2.
      apply rel_exp_mor with
        (R := interp E ((U1,U2,R)::D) T)
        (S := interp ((X,Q)::E) ((U1,U2,R)::D) T).
      * intros u v. symmetry. apply (IHT ((U1,U2,R)::D)). intro Hin. apply Hfresh. exact Hin.
      * apply Hfn; assumption.
  - tauto.
Qed.

Lemma rel_tm_env_ok_irrel : forall E X Q Gamma M,
  rel_tm_env_ok E Gamma M -> ~ In X (context_ty_fvars Gamma) ->
  rel_tm_env_ok ((X,Q)::E) Gamma M.
Proof.
  intros E X Q Gamma M HM HX x T Hlook.
  destruct (HM x T Hlook) as [a [b [Hp [Ha [Hb Hab]]]]].
  exists a,b. split; [exact Hp|]. split; [exact Ha|]. split; [exact Hb|].
  apply (proj2 (interp_env_irrel E X Q [] T
    (fun Hin => HX (lookup_context_type_fvars x Gamma T X Hlook Hin)) a b)).
  exact Hab.
Qed.

Lemma lookup_bound_shift : forall P p n,
  lookup_bound (S n) (p :: P) = lookup_bound n P.
Proof. reflexivity. Qed.

Lemma lookup_bound_at_length : forall P Q,
  lookup_bound (length P) (P ++ [Q]) = Some Q.
Proof.
  intros P. induction P as [|p P IH]; intros Q; simpl.
  - reflexivity.
  - exact (IH Q).
Qed.

Lemma lookup_bound_app_ne : forall P Q n,
  n <> length P -> lookup_bound n (P ++ [Q]) = lookup_bound n P.
Proof.
  intros P. induction P as [|p P IH]; intros Q n Hne; simpl in *.
  - destruct n; [contradiction|]. cbn [lookup_bound]. destruct n; reflexivity.
  - destruct n; [reflexivity|]. apply IH. lia.
Qed.

Lemma interp_bvar_open : forall E P X Q n a b,
  lookup_rel X E = None ->
  (interp E (P ++ [Q]) (Ty_BVar n) a b <->
   interp ((X,Q)::E) P (open_ty_rec (length P) (Ty_FVar X) (Ty_BVar n)) a b).
Proof.
  intros E P. induction P as [|p P IH]; intros X Q n a b Hnone.
  - destruct n as [|n]; simpl.
    + rewrite Nat.eqb_refl. reflexivity.
    + unfold lookup_bound. destruct n; reflexivity.
  - destruct n as [|n]; simpl.
    + reflexivity.
    + destruct (Nat.eqb (length P) n) eqn:En.
      * apply Nat.eqb_eq in En. subst n.
        rewrite lookup_bound_at_length. simpl. rewrite Nat.eqb_refl. reflexivity.
      * rewrite lookup_bound_app_ne.
        -- cbn [interp lookup_bound]. tauto.
        -- intro Eq. subst n. rewrite Nat.eqb_refl in En. discriminate.
Qed.

Lemma interp_open_bridge : forall E P X Q T,
  lookup_rel X E = None -> ~ In X (ty_fvars T) ->
  forall a b,
  interp E (P ++ [Q]) T a b <->
  interp ((X,Q)::E) P (open_ty_rec (length P) (Ty_FVar X) T) a b.
Proof.
  intros E P X Q T. revert E P. induction T; intros E P Hnone Hfresh v1 v2; simpl in *.
  - apply interp_bvar_open. exact Hnone.
  - destruct (Nat.eqb a X) eqn:Eax.
    + apply Nat.eqb_eq in Eax. subst. exfalso. apply Hfresh. simpl. auto.
    + simpl. destruct (lookup_rel a E); tauto.
  - assert (Hfresh1 : ~ In X (ty_fvars T1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ In X (ty_fvars T2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    assert (HI1 : forall u v,
      interp E (P++[Q]) T1 u v <->
      interp ((X,Q)::E) P (open_ty_rec (length P) (Ty_FVar X) T1) u v).
    { intros u v. apply IHT1; assumption. }
    assert (HI2 : forall u v,
      interp E (P++[Q]) T2 u v <->
      interp ((X,Q)::E) P (open_ty_rec (length P) (Ty_FVar X) T2) u v).
    { intros u v. apply IHT2; assumption. }
    split.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Harg.
      apply (proj1 (rel_exp_mor (interp E (P++[Q]) T2)
        (interp ((X,Q)::E) P (open_ty_rec (length P) (Ty_FVar X) T2))
        (tm_app v1 a1) (tm_app v2 a2) HI2)).
      apply Hfun.
      apply (proj2 (rel_exp_mor (interp E (P++[Q]) T1)
        (interp ((X,Q)::E) P (open_ty_rec (length P) (Ty_FVar X) T1)
        ) a1 a2 HI1)). exact Harg.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Harg.
      apply (proj2 (rel_exp_mor (interp E (P++[Q]) T2)
        (interp ((X,Q)::E) P (open_ty_rec (length P) (Ty_FVar X) T2))
        (tm_app v1 a1) (tm_app v2 a2) HI2)).
      apply Hfun.
      apply (proj1 (rel_exp_mor (interp E (P++[Q]) T1)
        (interp ((X,Q)::E) P (open_ty_rec (length P) (Ty_FVar X) T1))
        a1 a2 HI1)). exact Harg.
  - split.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 R HU1 HU2.
      assert (HI : forall u v,
        interp E (((U1,U2,R)::P)++[Q]) T u v <->
        interp ((X,Q)::E) ((U1,U2,R)::P)
          (open_ty_rec (length ((U1,U2,R)::P)) (Ty_FVar X) T) u v).
      { intros u v. apply IHT; assumption. }
      apply (proj1 (rel_exp_mor
        (interp E (((U1,U2,R)::P)++[Q]) T)
        (interp ((X,Q)::E) ((U1,U2,R)::P)
          (open_ty_rec (length ((U1,U2,R)::P)) (Ty_FVar X) T))
        (tm_tapp v1 U1) (tm_tapp v2 U2) HI)).
      apply Hfn; assumption.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 R HU1 HU2.
      assert (HI : forall u v,
        interp E (((U1,U2,R)::P)++[Q]) T u v <->
        interp ((X,Q)::E) ((U1,U2,R)::P)
          (open_ty_rec (length ((U1,U2,R)::P)) (Ty_FVar X) T) u v).
      { intros u v. apply IHT; assumption. }
      apply (proj2 (rel_exp_mor
        (interp E (((U1,U2,R)::P)++[Q]) T)
        (interp ((X,Q)::E) ((U1,U2,R)::P)
          (open_ty_rec (length ((U1,U2,R)::P)) (Ty_FVar X) T))
        (tm_tapp v1 U1) (tm_tapp v2 U2) HI)).
      apply Hfn; assumption.
  - tauto.
Qed.

Lemma lookup_bound_prefix : forall P D1 D2 i,
  i < length P -> lookup_bound i (P++D1) = lookup_bound i (P++D2).
Proof.
  induction P as [|p P IH]; intros D1 D2 i Hlt; simpl in *.
  - lia.
  - destruct i; [reflexivity|]. simpl. apply IH. lia.
Qed.

Lemma interp_lc_bound_irrel : forall K T,
  lc_ty_at K T -> forall E P D1 D2,
    length P = K ->
    forall a b, interp E (P++D1) T a b <-> interp E (P++D2) T a b.
Proof.
  intros K T Hlc. induction Hlc; intros E P D1 D2 Hlen a b; simpl.
  - assert (Hlook : lookup_bound i (P++D1) = lookup_bound i (P++D2)).
    { apply lookup_bound_prefix. lia. }
    rewrite Hlook. tauto.
  - tauto.
  - split.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros x y Hxy.
      apply (proj1 (rel_exp_mor (interp E (P++D1) T2) (interp E (P++D2) T2)
        (tm_app a x) (tm_app b y) (fun u v => IHHlc2 E P D1 D2 Hlen u v))).
      apply Hfn.
      apply (proj2 (rel_exp_mor (interp E (P++D1) T1) (interp E (P++D2) T1)
        x y (fun u v => IHHlc1 E P D1 D2 Hlen u v))). exact Hxy.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros x y Hxy.
      apply (proj2 (rel_exp_mor (interp E (P++D1) T2) (interp E (P++D2) T2)
        (tm_app a x) (tm_app b y) (fun u v => IHHlc2 E P D1 D2 Hlen u v))).
      apply Hfn.
      apply (proj1 (rel_exp_mor (interp E (P++D1) T1) (interp E (P++D2) T1)
        x y (fun u v => IHHlc1 E P D1 D2 Hlen u v))). exact Hxy.
  - split.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 R HU1 HU2.
      apply (proj1 (rel_exp_mor
        (interp E ((U1,U2,R)::(P++D1)) T)
        (interp E ((U1,U2,R)::(P++D2)) T)
        (tm_tapp a U1) (tm_tapp b U2)
        (fun u v => IHHlc E ((U1,U2,R)::P) D1 D2 (f_equal S Hlen) u v))).
      apply Hfn; assumption.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 R HU1 HU2.
      apply (proj2 (rel_exp_mor
        (interp E ((U1,U2,R)::(P++D1)) T)
        (interp E ((U1,U2,R)::(P++D2)) T)
        (tm_tapp a U1) (tm_tapp b U2)
        (fun u v => IHHlc E ((U1,U2,R)::P) D1 D2 (f_equal S Hlen) u v))).
      apply Hfn; assumption.
  - tauto.
Qed.


Lemma subst_ty_env_fresh_insert : forall S X U T,
  ~ In X (ty_fvars T) -> subst_ty_env ((X,U)::S) T = subst_ty_env S T.
Proof.
  intros S X U T. induction T; intros H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. simpl; auto.
    + reflexivity.
  - f_equal.
    + apply IHT1. intro Hin. apply H. apply in_or_app; left; exact Hin.
    + apply IHT2. intro Hin. apply H. apply in_or_app; right; exact Hin.
  - f_equal. apply IHT. exact H.
  - reflexivity.
Qed.

Lemma subst_ty_env_self_insert : forall S X T,
  lookup_ty_subst X S = None ->
  subst_ty_env ((X,Ty_FVar X)::S) T = subst_ty_env S T.
Proof.
  intros S X T. induction T; intros Hnone; simpl.
  - reflexivity.
  - destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E. subst. rewrite Hnone. reflexivity.
    + destruct (lookup_ty_subst a S); reflexivity.
  - rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
  - reflexivity.
Qed.

Lemma subst_tm_types_fresh_insert : forall S X U t,
  ~ In X (tm_fvars t) ->
  subst_tm_types ((X,U)::S) t = subst_tm_types S t.
Proof.
  intros S X U t. induction t; intros H; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply subst_ty_env_fresh_insert. intro Hin. apply H. apply in_or_app; left; exact Hin.
    + apply IHt. intro Hin. apply H. apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply H. apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin. apply H. apply in_or_app; right; exact Hin.
  - f_equal. apply IHt. exact H.
  - f_equal.
    + apply IHt. intro Hin. apply H. apply in_or_app; left; exact Hin.
    + apply subst_ty_env_fresh_insert. intro Hin. apply H. apply in_or_app; right; exact Hin.
  - reflexivity.
  - f_equal. apply IHt. exact H.
  - f_equal.
    + apply IHt1. intro Hin. apply H. apply in_or_app; left. exact Hin.
    + apply IHt2. intro Hin. apply H. apply in_or_app; right. apply in_or_app; left; exact Hin.
    + apply IHt3. intro Hin. apply H. apply in_or_app; right. apply in_or_app; right; exact Hin.
Qed.

Lemma subst_ty_env_open_fvar : forall S k X T,
  lookup_ty_subst X S = None ->
  (forall Y U, lookup_ty_subst Y S = Some U -> locally_closed_ty U) ->
  subst_ty_env S (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k (Ty_FVar X) (subst_ty_env S T).
Proof.
  intros S k X T. revert k. induction T; intros k Hnone Hclosed; simpl.
  - destruct (Nat.eqb k n); simpl; auto. rewrite Hnone. reflexivity.
  - destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E. subst. rewrite Hnone. reflexivity.
    + destruct (lookup_ty_subst a S) as [U|] eqn:Hu; simpl.
      * rewrite (open_ty_rec_lc_identity 0 U (Hclosed a U Hu) k (Ty_FVar X) (Nat.le_0_l k)). reflexivity.
      * reflexivity.
  - rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
  - reflexivity.
Qed.

Lemma lookup_ty_subst_notin : forall X S,
  ~ In X (map fst S) -> lookup_ty_subst X S = None.
Proof.
  intros X S. induction S as [|[Y U] S IH]; intros H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. left. reflexivity.
    + apply IH. intro Hin. apply H. right. exact Hin.
Qed.

Lemma wf_ty_weaken : forall Delta T,
  wf_ty Delta T -> forall Delta',
    (forall X, In X Delta -> In X Delta') -> wf_ty Delta' T.
Proof.
  intros Delta T Hwf. induction Hwf as
    [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T Hbody IHbody | Delta]; intros Delta' Hincl.
  - apply WF_Var. apply Hincl. exact Hin.
  - apply WF_Arrow; [apply IH1|apply IH2]; assumption.
  - apply WF_All with (L := L).
    intros X HX. apply IHbody; [exact HX|].
    intros Y HY. simpl in HY. destruct HY as [->|HY]; [left; reflexivity|right; apply Hincl; exact HY].
  - constructor.
Qed.


Lemma lc_open_ty_inv : forall k T X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  intros k T. revert k. induction T; intros k X H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H; subst. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IHT; eauto.
  - constructor.
Qed.

Lemma lc_tm_open_inv : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t. revert K k. induction t; intros K k x H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H; subst. constructor. apply Nat.eqb_neq in E. lia.
  - inversion H; constructor.
  - inversion H; subst. constructor.
    + assumption.
    + eapply IHt; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IHt; eauto.
  - inversion H; subst. constructor; eauto.
  - constructor.
  - inversion H; subst. constructor. eapply IHt; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inv : forall K k t X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  intros K k t. revert K k. induction t; intros K k X H; simpl in *.
  - constructor; inversion H; assumption.
  - constructor; inversion H; assumption.
  - inversion H; subst. constructor.
    + eapply lc_open_ty_inv; eauto.
    + eapply IHt; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IHt; eauto.
  - inversion H; subst. constructor.
    + eapply IHt; eauto.
    + eapply lc_open_ty_inv; eauto.
  - constructor.
  - inversion H; subst. constructor. eapply IHt; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma lc_ty_subst_env : forall S K T,
  lc_ty_at K T ->
  (forall X U, lookup_ty_subst X S = Some U -> forall j, lc_ty_at j U) ->
  lc_ty_at K (subst_ty_env S T).
Proof.
  intros S K T H. revert S. induction H; intros S Hsub; simpl.
  - constructor. assumption.
  - destruct (lookup_ty_subst X S) as [U|] eqn:E.
    + eapply Hsub; eauto.
    + constructor.
  - constructor; eauto.
  - constructor. eapply IHlc_ty_at. intros; eapply Hsub; eauto.
  - constructor.
Qed.

Lemma lc_tm_types_subst_env : forall S K k t,
  lc_tm_at K k t ->
  (forall X U, lookup_ty_subst X S = Some U -> forall j, lc_ty_at j U) ->
  lc_tm_at K k (subst_tm_types S t).
Proof.
  intros S K k t H. revert S. induction H; intros S Hsub; simpl.
  - constructor; assumption.
  - constructor.
  - constructor.
    + eapply lc_ty_subst_env; eauto.
    + eapply IHlc_tm_at; eauto.
  - constructor; eauto.
  - constructor. eapply IHlc_tm_at; eauto.
  - constructor.
    + eapply IHlc_tm_at; eauto.
    + eapply lc_ty_subst_env; eauto.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T -> lc_ty_at (S K) T.
Proof.
  intros K T H. induction H; constructor; eauto; lia.
Qed.

Lemma lc_tm_weaken_k : forall K k t, lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H. induction H; constructor; eauto; lia.
Qed.

Lemma lc_tm_weaken_K : forall K k t, lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H. induction H; constructor; eauto using lc_ty_weaken; lia.
Qed.

Lemma lc_ty_at_all : forall K T, locally_closed_ty T -> lc_ty_at K T.
Proof.
  intros K T H. induction K; [exact H|]. apply lc_ty_weaken. exact IHK.
Qed.

Lemma lc_tm_at_all : forall K k t, locally_closed_tm t -> lc_tm_at K k t.
Proof.
  intros K. induction K; intros k t H.
  - induction k; [exact H|]. apply lc_tm_weaken_k. exact IHk.
  - apply lc_tm_weaken_K. apply IHK. exact H.
Qed.

Lemma open_tm_ty_rec_lc_identity : forall K k t,
  lc_tm_at K k t -> forall n U, K <= n -> open_tm_ty_rec n U t = t.
Proof.
  intros K k t Hlc. revert K k Hlc. induction t; intros K k Hlc j W Hle; simpl in *.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply open_ty_rec_lc_identity; [exact H3|exact Hle].
    + apply IHt with (K:=K) (k:=S k) (n:=j) (U:=W); [exact H4|exact Hle].
  - inversion Hlc; subst. rewrite (IHt1 K k H3 j W Hle), (IHt2 K k H4 j W Hle). reflexivity.
  - inversion Hlc; subst. f_equal. apply IHt with (K:=S K) (k:=k) (n:=S j) (U:=W); [exact H2|lia].
  - inversion Hlc; subst. rewrite (IHt K k H3 j W Hle). f_equal.
    eapply open_ty_rec_lc_identity; [exact H4|exact Hle].
  - reflexivity.
  - inversion Hlc; subst. rewrite (IHt K k H2 j W Hle). reflexivity.
  - inversion Hlc; subst. rewrite (IHt1 K k H4 j W Hle), (IHt2 K k H5 j W Hle), (IHt3 K k H6 j W Hle). reflexivity.
Qed.

Lemma subst_tm_env_open_ty_rec : forall S k U t,
  (forall x v, lookup_tm_subst x S = Some v -> locally_closed_tm v) ->
  subst_tm_env S (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (subst_tm_env S t).
Proof.
  intros S k U t Hclosed. revert k Hclosed. induction t; intros k Hclosed; simpl.
  - reflexivity.
  - destruct (lookup_tm_subst a S) as [v|] eqn:Hv; simpl.
    + pose proof (Hclosed a v Hv) as Hlc. unfold locally_closed_tm in Hlc.
      rewrite (open_tm_ty_rec_lc_identity 0 0 v Hlc k U (Nat.le_0_l k)). reflexivity.
    + reflexivity.
  - rewrite (IHt k Hclosed). reflexivity.
  - rewrite (IHt1 k Hclosed), (IHt2 k Hclosed). reflexivity.
  - f_equal. apply IHt with (k:=Datatypes.S k). exact Hclosed.
  - rewrite (IHt k Hclosed). reflexivity.
  - reflexivity.
  - rewrite (IHt k Hclosed). reflexivity.
  - rewrite (IHt1 k Hclosed), (IHt2 k Hclosed), (IHt3 k Hclosed). reflexivity.
Qed.

Lemma lc_tm_subst_env : forall S K k t,
  lc_tm_at K k t ->
  (forall x u, lookup_tm_subst x S = Some u ->
    forall K' k', lc_tm_at K' k' u) ->
  lc_tm_at K k (subst_tm_env S t).
Proof.
  intros S K k t H. revert S. induction H; intros S Hsub; simpl.
  - constructor; assumption.
  - destruct (lookup_tm_subst x S) as [u|] eqn:E.
    + eapply Hsub; eauto.
    + constructor.
  - constructor; eauto.
  - constructor; eauto.
  - constructor. eapply IHlc_tm_at; eauto.
  - constructor; eauto.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Fixpoint max_atom_list (L : list atom) : atom :=
  match L with [] => 0 | x :: L' => Nat.max x (max_atom_list L') end.

Lemma in_le_max_atom_list : forall x L, In x L -> x <= max_atom_list L.
Proof.
  intros x L H. induction L as [|a L IH]; simpl in *; [contradiction|].
  destruct H as [->|H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [eapply IH; eauto|apply Nat.le_max_r].
Qed.

Lemma fresh_atom_list : forall (L : list atom), exists X, ~ In X L.
Proof.
  intros L. exists (S (max_atom_list L)). intro H.
  pose proof (in_le_max_atom_list _ _ H). lia.
Qed.


Lemma has_type_term_fvars : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall x, In x (tm_term_fvars t) -> In x (context_vars Gamma).
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros z Hz.
  - simpl in Hz. destruct Hz as [<-|[]]. eapply lookup_context_in; eauto.
  - simpl in Hz.
    destruct (fresh_atom_list (L ++ [z])) as [x Hx].
    assert (HxL : ~ In x L) by (intro Hin; apply Hx; apply in_or_app; left; exact Hin).
    assert (Hxz : x <> z).
    { intro Heq. subst. apply Hx. apply in_or_app. right. simpl; auto. }
    assert (Hzopen : In z (tm_term_fvars (open_tm_rec 0 (tm_fvar x) t2))).
    { eapply term_fvars_open_preserve; eauto. }
    specialize (H1 x HxL z Hzopen). simpl in H1. destruct H1 as [Heq|Hin].
    + contradiction.
    + exact Hin.
  - simpl in Hz. apply in_app_iff in Hz as [Hz|Hz].
    + eapply IHHty1; eauto.
    + eapply IHHty2; eauto.
  - simpl in Hz. destruct (fresh_atom_list L) as [X HX].
    apply (H0 X HX z). change (In z (tm_term_fvars (open_tm_ty_rec 0 (Ty_FVar X) t))).
    rewrite tm_term_fvars_open_ty_rec. exact Hz.
  - simpl in Hz. eapply IHHty; exact Hz.
  - contradiction.
  - simpl in Hz. eapply IHHty; exact Hz.
  - simpl in Hz. apply in_app_iff in Hz as [Hz|Hz].
    + eapply IHHty1; eauto.
    + apply in_app_iff in Hz as [Hz|Hz].
      * eapply IHHty2; eauto.
      * eapply IHHty3; eauto.
Qed.




Lemma has_type_empty_term_closed : forall Delta t T,
  has_type Delta [] t T -> term_closed t.
Proof.
  intros Delta t T Hty. unfold term_closed. intros x Hx.
  pose proof (has_type_term_fvars Delta [] t T Hty x Hx) as Hctx. simpl in Hctx. exact Hctx.
Qed.

Lemma wf_ty_locally_closed : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H using wf_ty_ind.
  - constructor.
  - constructor; assumption.
  - unfold locally_closed_ty. constructor.
    destruct (fresh_atom_list L) as [X HX].
    specialize (H0 X HX). apply lc_open_ty_inv with (X := X). exact H0.
  - constructor.
Qed.

Lemma interp_bound_open_type : forall E D T U1 U2 U,
  wf_ty [] U -> lc_ty_at (S (length D)) T ->
  forall a b,
  interp E (D++[(U1,U2,interp E [] U)]) T a b <->
  interp E D (open_ty_rec (length D) U T) a b.
Proof.
  intros E D T U1 U2 U HU Hlc. revert E D U1 U2 U HU Hlc.
  induction T; intros E D U1 U2 U HU Hlc x y; simpl in *.
  - inversion Hlc; subst. destruct (Nat.lt_ge_cases n (length D)) as [Hlt|Hge].
    + rewrite lookup_bound_app_ne by lia.
      destruct (lookup_bound n D) as [[[A B] R]|] eqn:Hlook; simpl.
      * assert (Hneq : Nat.eqb (length D) n = false) by (apply Nat.eqb_neq; lia).
        rewrite Hneq. unfold interp; simpl. rewrite Hlook. tauto.
      * assert (Hneq : Nat.eqb (length D) n = false) by (apply Nat.eqb_neq; lia).
        rewrite Hneq. unfold interp; simpl. rewrite Hlook. tauto.
    + assert (Heq : n = length D) by lia. subst n.
      rewrite lookup_bound_at_length. simpl. rewrite Nat.eqb_refl.
      assert (Hirrel : forall x y, interp E D U x y <-> interp E [] U x y).
      { intros x0 y0. apply (interp_lc_bound_irrel 0 U (wf_ty_locally_closed [] U HU) E [] D [] eq_refl x0 y0). }
      symmetry. apply Hirrel.
  - inversion Hlc; subst. destruct (lookup_rel a E); tauto.
  - inversion Hlc; subst.
    assert (HI1 : forall x y, interp E (D++[(U1,U2,interp E [] U)]) T1 x y <->
        interp E D (open_ty_rec (length D) U T1) x y).
    { intros x0 y0. eapply IHT1; eauto. }
    assert (HI2 : forall x y, interp E (D++[(U1,U2,interp E [] U)]) T2 x y <->
        interp E D (open_ty_rec (length D) U T2) x y).
    { intros x0 y0. eapply IHT2; eauto. }
    split.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros x0 y0 Hxy.
      apply (proj1 (rel_exp_mor (interp E (D++[(U1,U2,interp E [] U)]) T2)
        (interp E D (open_ty_rec (length D) U T2)) (tm_app x x0) (tm_app y y0) HI2)).
      apply Hfn. apply (proj2 (rel_exp_mor (interp E (D++[(U1,U2,interp E [] U)]) T1)
        (interp E D (open_ty_rec (length D) U T1)) x0 y0 HI1)). exact Hxy.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros x0 y0 Hxy.
      apply (proj2 (rel_exp_mor (interp E (D++[(U1,U2,interp E [] U)]) T2)
        (interp E D (open_ty_rec (length D) U T2)) (tm_app x x0) (tm_app y y0) HI2)).
      apply Hfn. apply (proj1 (rel_exp_mor (interp E (D++[(U1,U2,interp E [] U)]) T1)
        (interp E D (open_ty_rec (length D) U T1)) x0 y0 HI1)). exact Hxy.
  - inversion Hlc; subst. split.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros V1 V2 R' HV1 HV2.
      assert (HrelU : forall x y, interp E ((V1,V2,R')::D) U x y <-> interp E [] U x y).
      { intros x0 y0. apply (interp_lc_bound_irrel 0 U (wf_ty_locally_closed [] U HU) E [] ((V1,V2,R')::D) [] eq_refl x0 y0). }
      assert (HI : forall x y,
        interp E ((V1,V2,R')::(D++[(U1,U2,interp E [] U)])) T x y <->
        interp E ((V1,V2,R')::D) (open_ty_rec (S (length D)) U T) x y).
      { intros x0 y0. apply (IHT E ((V1,V2,R')::D) U1 U2 U HU).
        simpl in *. exact H1. }
      apply (proj1 (rel_exp_mor
        (interp E ((V1,V2,R')::(D++[(U1,U2,interp E [] U)])) T)
        (interp E ((V1,V2,R')::D) (open_ty_rec (S (length D)) U T))
        (tm_tapp x V1) (tm_tapp y V2) HI)).
      apply Hfn; assumption.
    + intros [Hv1 [Hv2 Hfn]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros V1 V2 R' HV1 HV2.
      assert (HI : forall x y,
        interp E ((V1,V2,R')::(D++[(U1,U2,interp E [] U)])) T x y <->
        interp E ((V1,V2,R')::D) (open_ty_rec (S (length D)) U T) x y).
      { intros x0 y0. apply (IHT E ((V1,V2,R')::D) U1 U2 U HU).
        simpl in *. exact H1. }
      apply (proj2 (rel_exp_mor
        (interp E ((V1,V2,R')::(D++[(U1,U2,interp E [] U)])) T)
        (interp E ((V1,V2,R')::D) (open_ty_rec (S (length D)) U T))
        (tm_tapp x V1) (tm_tapp y V2) HI)).
      apply Hfn; assumption.
  - inversion Hlc; subst. tauto.
Qed.


Lemma wf_ty_subst_env : forall Delta T,
  wf_ty Delta T -> forall Delta' S,
    (forall X, In X Delta -> exists U, lookup_ty_subst X S = Some U) ->
    (forall X U, lookup_ty_subst X S = Some U -> wf_ty Delta' U) ->
    wf_ty Delta' (subst_ty_env S T).
Proof.
  intros Delta T Hwf. induction Hwf as
    [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T Hbody IHbody | Delta];
    intros Delta' S Hcov Henv; simpl.
  - destruct (Hcov X Hin) as [U Hlook]. rewrite Hlook. eapply Henv; eauto.
  - apply WF_Arrow; [eapply IH1|eapply IH2]; eauto.
  - apply WF_All with (L := L ++ map fst S ++ Delta).
    intros Y HY.
    assert (HYL : ~ In Y L).
    { intro Hin. apply HY. apply in_or_app; left; exact Hin. }
    assert (HYkey : ~ In Y (map fst S)).
    { intro Hin. apply HY. apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (HYdelta : ~ In Y Delta).
    { intro Hin. apply HY. apply in_or_app; right. apply in_or_app; right; exact Hin. }
    pose proof (lookup_ty_subst_notin Y S HYkey) as Hnone.
    pose proof (Hbody Y HYL) as HbodyY.
    set (S' := (Y,Ty_FVar Y)::S).
    assert (Hcov' : forall Z, In Z (Y::Delta) -> exists U, lookup_ty_subst Z S' = Some U).
    { intros Z HZ. simpl in HZ. destruct HZ as [Heq|HZ].
      - subst Z. exists (Ty_FVar Y). simpl. rewrite Nat.eqb_refl. reflexivity.
      - destruct (Hcov Z HZ) as [U Hlook]. exists U. unfold S'. simpl.
        destruct (Nat.eqb Z Y) eqn:Ezy.
        + apply Nat.eqb_eq in Ezy. subst. contradiction.
        + exact Hlook. }
    assert (Henv' : forall Z U, lookup_ty_subst Z S' = Some U -> wf_ty (Y::Delta') U).
    { intros Z U Hlook. unfold S' in Hlook. simpl in Hlook.
      destruct (Nat.eqb Z Y) eqn:Ezy.
      - inversion Hlook; subst. constructor; simpl; auto.
      - apply Henv with (X := Z) in Hlook.
        eapply wf_ty_weaken; [exact Hlook|]. intros W HW. right. exact HW. }
    pose proof (IHbody Y HYL (Y::Delta') S' Hcov' Henv') as Hout.
    unfold S' in Hout.
    rewrite subst_ty_env_self_insert in Hout by exact Hnone.
    change (wf_ty (Y::Delta') (subst_ty_env S (open_ty_rec 0 (Ty_FVar Y) T))) in Hout.
    rewrite subst_ty_env_open_fvar in Hout.
    2: exact Hnone.
    2: intros Z U Hlook; eapply wf_ty_locally_closed; eapply Henv; eauto.
    exact Hout.
  - constructor.
Qed.

Lemma rel_ty_env_closed_lc : forall E,
  rel_ty_env_closed E ->
  (forall X U, lookup_ty_subst X (rel_ty_env_left E) = Some U -> forall K, lc_ty_at K U) /\
  (forall X U, lookup_ty_subst X (rel_ty_env_right E) = Some U -> forall K, lc_ty_at K U).
Proof.
  intros E [HL HR]. split; intros X U H K; eapply lc_ty_at_all;
    eapply wf_ty_locally_closed; eauto.
Qed.

Lemma rel_env_subst_wf : forall Delta E T,
  rel_ty_env_ok Delta E -> rel_ty_env_closed E -> wf_ty Delta T ->
  wf_ty [] (subst_ty_env (rel_ty_env_left E) T) /\
  wf_ty [] (subst_ty_env (rel_ty_env_right E) T).
Proof.
  intros Delta E T HE HEC Hwf. split.
  - eapply wf_ty_subst_env; [exact Hwf| |].
    + intros X HX. destruct (HE X HX) as [A [B [R [Hrel [HA HB]]]]].
      exists A. apply lookup_ty_subst_rel_left with (B:=B) (R:=R). exact Hrel.
    + intros X U Hlook. destruct HEC as [HL _]. eauto.
  - eapply wf_ty_subst_env; [exact Hwf| |].
    + intros X HX. destruct (HE X HX) as [A [B [R [Hrel [HA HB]]]]].
      exists B. apply lookup_ty_subst_rel_right with (A:=A) (R:=R). exact Hrel.
    + intros X U Hlook. destruct HEC as [_ HR]. eauto.
Qed.

Lemma wf_ty_fvars_in : forall Delta T, wf_ty Delta T ->
  forall X, In X (ty_fvars T) -> In X Delta.
Proof.
  intros Delta T H. induction H using wf_ty_ind.
  - simpl. intros Y [<-|[]]. assumption.
  - simpl. intros Y Hin. apply in_app_iff in Hin as [Hin|Hin].
    + eapply IHwf_ty1; eauto.
    + eapply IHwf_ty2; eauto.
  - simpl. intros Y Hin.
    destruct (fresh_atom_list (L ++ [Y])) as [Z HZ].
    assert (HZL : ~ In Z L) by (intro HI; apply HZ; apply in_or_app; left; exact HI).
    assert (HZY : Z <> Y).
    { intro E; subst. apply HZ. apply in_or_app. right. simpl. auto. }
    specialize (H Z HZL).
    assert (Hin' : In Y (ty_fvars (open_ty T (Ty_FVar Z)))).
    { eapply ty_fvars_open_rec_in; eauto. }
    specialize (H0 Z HZL Y Hin').
    simpl in H0. destruct H0 as [E|H0].
    + contradiction.
    + exact H0.
  - simpl. intros Y Hin. contradiction.
Qed.

Lemma wf_closed_ty_subst_fixed : forall U S,
  wf_ty [] U -> subst_ty_env S U = U.
Proof.
  intros U S H.
  assert (Hnone : forall X, ~ In X (ty_fvars U)).
  { intros X HX. pose proof (wf_ty_fvars_in [] U H X HX). contradiction. }
  clear H. induction U; simpl in *.
  - reflexivity.
  - exfalso. apply (Hnone a). simpl. auto.
  - rewrite IHU1, IHU2.
    + reflexivity.
    + intros X HX. exfalso. apply (Hnone X). apply in_or_app. right. exact HX.
    + intros X HX. exfalso. apply (Hnone X). apply in_or_app. left. exact HX.
  - f_equal. apply IHU. exact Hnone.
  - reflexivity.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H using has_type_ind.
  - constructor.
  - unfold locally_closed_tm. constructor.
    + eapply wf_ty_locally_closed; eauto.
    + destruct (fresh_atom_list L) as [x Hx].
      apply lc_tm_open_inv with (x := x). exact (H1 x Hx).
  - unfold locally_closed_tm. constructor; assumption.
  - unfold locally_closed_tm. constructor.
    destruct (fresh_atom_list L) as [X HX].
    apply lc_tm_ty_open_inv with (X := X). exact (H0 X HX).
  - unfold locally_closed_tm. constructor; [assumption|eapply wf_ty_locally_closed; eauto].
  - unfold locally_closed_tm. constructor.
  - unfold locally_closed_tm. constructor. assumption.
  - unfold locally_closed_tm. constructor; assumption.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H. induction H; simpl; constructor; assumption.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H. inversion H; subst; eauto using numeric_value_lc.
Qed.

Lemma rel_tm_env_closed_lc : forall M,
  rel_tm_env_closed M ->
  forall x a b, lookup_tm_rel x M = Some (a, b) ->
    (forall K k, lc_tm_at K k a) /\ (forall K k, lc_tm_at K k b).
Proof.
  intros M HM x a b Hlookup. specialize (HM x a b Hlookup).
  destruct HM as [Ha [Hb [Hca Hcb]]]. split; intros; eapply lc_tm_at_all;
    eapply value_locally_closed; eauto.
Qed.

Lemma has_type_substituted_lc : forall Delta Gamma t T E M,
  has_type Delta Gamma t T -> rel_ty_env_closed E -> rel_tm_env_closed M ->
  locally_closed_tm (subst_tm_env (tm_rel_env_left M)
    (subst_tm_types (rel_ty_env_left E) t)) /\
  locally_closed_tm (subst_tm_env (tm_rel_env_right M)
    (subst_tm_types (rel_ty_env_right E) t)).
Proof.
  intros Delta Gamma t T E M Hty HE HM. split.
  - unfold locally_closed_tm. eapply lc_tm_subst_env.
    + eapply lc_tm_types_subst_env.
      * apply has_type_locally_closed with (Delta := Delta) (Gamma := Gamma) (T := T). exact Hty.
      * destruct (rel_ty_env_closed_lc E HE) as [HL _]. exact HL.
    + intros x u Hlook K' k'.
      destruct (lookup_tm_rel_left x M u Hlook) as [b Hpair].
      destruct (rel_tm_env_closed_lc M HM x u b Hpair) as [Hu _].
      apply Hu.
  - unfold locally_closed_tm. eapply lc_tm_subst_env.
    + eapply lc_tm_types_subst_env.
      * apply has_type_locally_closed with (Delta := Delta) (Gamma := Gamma) (T := T). exact Hty.
      * destruct (rel_ty_env_closed_lc E HE) as [_ HR]. exact HR.
    + intros x u Hlook K' k'.
      destruct (lookup_tm_rel_right x M u Hlook) as [a Hpair].
      destruct (rel_tm_env_closed_lc M HM x a u Hpair) as [_ Hu].
      apply Hu.
Qed.

Lemma logical_relation_identity_extract : forall t U v,
  wf_ty [] U -> value v -> term_closed v ->
  interp [] [] (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) t t ->
  multi (tm_app (tm_tapp t U) v) v.
Proof.
  intros t U v HU Hv Hclosed Hrel.
  cbn [interp] in Hrel.
  destruct Hrel as [Htv1 [Htv2 Hpoly]].
  assert (Harg : rel_exp (singleton_rel v) v v).
  { split; [eapply value_locally_closed; eauto|]. split; [eapply value_locally_closed; eauto|].
    exists v,v. unfold evaluates_to, singleton_rel. repeat split; auto using multi_refl. }
  specialize (Hpoly U U (singleton_rel v) HU HU).
  cbn [interp] in Hpoly.
  destruct Hpoly as [Hlc1 [Hlc2 [f1 [f2 [[Ht1 [Hfv1 Hc1]] [[Ht2 [Hfv2 Hc2]] Hfrel]]]]]].
  cbn [interp] in Hfrel.
  destruct Hfrel as [_ [_ Hfun]].
  specialize (Hfun v v Harg).
  apply rel_exp_singleton_left in Hfun.
  eapply multi_trans.
  - apply multi_app_l.
    + exact Ht1.
    + eapply value_locally_closed; eauto.
  - eapply multi_trans; [exact Hfun|constructor].
Qed.

Lemma eval_app_context : forall f vf a va,
  evaluates_to f vf -> evaluates_to a va -> locally_closed_tm a ->
  multi (tm_app f a) (tm_app vf va).
Proof.
  intros f vf a va [Hf [Hvf Hcf]] [Ha [Hva Hca]] Hlac.
  eapply multi_trans.
  - apply multi_app_l; [exact Hf|exact Hlac].
  - apply multi_app_r; [exact Hvf|exact Ha].
Qed.

Lemma rel_exp_app_arrow : forall E A B f g a b,
  rel_exp (interp E [] (Ty_Arrow A B)) f g ->
  rel_exp (interp E [] A) a b ->
  locally_closed_tm a -> locally_closed_tm b ->
  rel_exp (interp E [] B) (tm_app f a) (tm_app g b).
Proof.
  intros E A B f g a b Hf Ha HlacA HlacB.
  destruct Hf as [Hlf [Hlg Hf]]. destruct Hf as [vf [vg [Evf [Evg Hrelf]]]].
  destruct Evf as [Hf [Hvf Hcf]]. destruct Evg as [Hg [Hvg Hcg]].
  destruct Ha as [Hla [Hlb Ha]]. destruct Ha as [va [vb [Eva [Evb Hrela]]]].
  destruct Eva as [Ha [Hva Hca]]. destruct Evb as [Hb [Hvb Hcb]].
  simpl in Hrelf. destruct Hrelf as [_ [_ Hfn]].
  assert (Harg : rel_exp (interp E [] A) a b).
  { split; [exact Hla|]. split; [exact Hlb|]. exists va,vb. split.
    - split; [exact Ha|]. split; [exact Hva|exact Hca].
    - split.
      + split; [exact Hb|]. split; [exact Hvb|exact Hcb].
      + exact Hrela. }
  pose proof (Hfn a b Harg) as Hout.
  destruct Hout as [Hlo [Hro Hout]].
  destruct Hout as [wa [wb [Ewa [Ewb Hrelout]]]].
  destruct Ewa as [Hwa [Hvalwa Hcwa]]. destruct Ewb as [Hwb [Hvalwb Hcwb]].
  split; [constructor; assumption|]. split; [constructor; assumption|]. exists wa,wb. split.
  - split; [eapply multi_trans; [apply multi_app_l; [exact Hf|exact HlacA]|exact Hwa]|].
    split; assumption.
  - split.
    + split; [eapply multi_trans; [apply multi_app_l; [exact Hg|exact HlacB]|exact Hwb]|].
      split; assumption.
    + exact Hrelout.
Qed.

Lemma eval_tapp_context : forall f vf U,
  evaluates_to f vf -> locally_closed_ty U ->
  multi (tm_tapp f U) (tm_tapp vf U).
Proof.
  intros f vf U [Hf [Hvf Hcf]] Hlc.
  revert Hlc. induction Hf; intros Hlc.
  - constructor.
  - eapply multi_step.
    + eapply ST_TApp; eauto.
    + apply IHHf; assumption.
Qed.

Lemma rel_exp_tapp_all : forall E T f g U1 U2 R,
  rel_exp (interp E [] (Ty_All T)) f g ->
  wf_ty [] U1 -> wf_ty [] U2 ->
  rel_exp (interp E [(U1,U2,R)] T) (tm_tapp f U1) (tm_tapp g U2).
Proof.
  intros E T f g U1 U2 R Hf HU1 HU2.
  destruct Hf as [Hlf [Hlg Hf]]. destruct Hf as [vf [vg [Evf [Evg Hrelf]]]].
  destruct Evf as [Hf [Hvf Hcf]]. destruct Evg as [Hg [Hvg Hcg]].
  simpl in Hrelf. destruct Hrelf as [_ [_ Hpoly]].
  pose proof (Hpoly U1 U2 R HU1 HU2) as Hout.
  destruct Hout as [Hlo [Hro Hout]]. destruct Hout as [wa [wb [Ewa [Ewb Hrelout]]]].
  destruct Ewa as [Hwa [Hva Hca]]. destruct Ewb as [Hwb [Hvb Hcb]].
  split; [eapply lc_tm_tapp; [exact Hlf|eapply wf_ty_locally_closed; eauto]|].
  split; [eapply lc_tm_tapp; [exact Hlg|eapply wf_ty_locally_closed; eauto]|].
  exists wa,wb. split.
  - split.
    + eapply multi_trans.
      * apply eval_tapp_context with (vf:=vf); [split; [exact Hf|split; assumption]|eapply wf_ty_locally_closed; eauto].
      * exact Hwa.
    + split; assumption.
  - split.
    + split.
      * eapply multi_trans.
        -- apply eval_tapp_context with (vf:=vg); [split; [exact Hg|split; assumption]|eapply wf_ty_locally_closed; eauto].
        -- exact Hwb.
      * split; assumption.
    + exact Hrelout.
Qed.

Lemma fundamental_theorem : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall E M, rel_ty_env_ok Delta E -> rel_ty_env_closed E ->
    rel_tm_env_ok E Gamma M -> rel_tm_env_closed M ->
    rel_exp (interp E [] T)
      (subst_tm_env (tm_rel_env_left M) (subst_tm_types (rel_ty_env_left E) t))
      (subst_tm_env (tm_rel_env_right M) (subst_tm_types (rel_ty_env_right E) t)).
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros E M HE HEC HM HMC.
  - destruct (HM x T H) as [a [b [Hpair [Ha [Hb Hab]]]]].
    destruct (HMC x a b Hpair) as [_ [_ [Hca Hcb]]].
    simpl. rewrite (lookup_tm_rel_left_from x M a b Hpair), (lookup_tm_rel_right_from x M a b Hpair).
    split; [eapply value_locally_closed; eauto|].
    split; [eapply value_locally_closed; eauto|]. exists a,b. split.
    + split; [apply multi_refl|]. split; [exact Ha|exact Hca].
    + split.
      * split; [apply multi_refl|]. split; [exact Hb|exact Hcb].
      * exact Hab.
  - assert (Hder : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)).
    { econstructor; eauto. }
    destruct (has_type_substituted_lc Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2) E M Hder HEC HMC) as [HlcL HlcR].
    set (fL := subst_tm_env (tm_rel_env_left M) (subst_tm_types (rel_ty_env_left E) (tm_abs T1 t2))).
    set (fR := subst_tm_env (tm_rel_env_right M) (subst_tm_types (rel_ty_env_right E) (tm_abs T1 t2))).
    cbn [subst_tm_env subst_tm_types] in HlcL, HlcR.
    unfold fL, fR in *. cbn [interp subst_tm_env subst_tm_types].
    change (value (tm_abs (subst_ty_env (rel_ty_env_left E) T1)
        (subst_tm_env (tm_rel_env_left M) (subst_tm_types (rel_ty_env_left E) t2)) /\
      value (tm_abs (subst_ty_env (rel_ty_env_right E) T1)
        (subst_tm_env (tm_rel_env_right M) (subst_tm_types (rel_ty_env_right E) t2)) /\ _).
    split; [constructor; exact HlcL|]. split; [constructor; exact HlcR|].
    intros a b Harg.
    destruct Harg as [Hla [Hlb Hargs]].
    destruct Hargs as [va [vb [Eva [Evb Hrelab]]]].
    destruct Eva as [Ha [Hva Hca]]. destruct Evb as [Hb [Hvb Hcb]].
    assert (Hfreshset : forall z, In z (L ++ context_vars Gamma ++ map fst M ++ tm_fvars (subst_tm_types (rel_ty_env_left E) t2)) -> False -> False) by auto.
    destruct (fresh_atom_list (L ++ context_vars Gamma ++ map fst M ++ tm_fvars (subst_tm_types (rel_ty_env_left E) t2))) as [z Hz].
    assert (HzL : ~ In z L) by (intro Hin; apply Hz; apply in_or_app; left; exact Hin).
    assert (HzG : ~ In z (context_vars Gamma)).
    { intro Hin. apply Hz. apply in_or_app; right. apply in_or_app; left. exact Hin. }
    assert (Hzbody : ~ In z (tm_fvars (subst_tm_types (rel_ty_env_left E) t2))).
    { intro Hin. apply Hz. repeat (apply in_or_app; right). exact Hin. }
    pose proof (H1 z HzL E ((z,(va,vb))::M) HE HEC
      (rel_tm_env_ok_extend E Gamma M z T1 va vb HzG HM Hva Hvb Hrelab)
      (rel_tm_env_closed_cons M z va vb Hva Hvb Hca Hcb HMC)) as Hbody.
    assert (HsubL : subst_tm_env ((z,va)::tm_rel_env_left M) va = va).
    { rewrite subst_tm_env_term_closed_fixed; auto. }
    assert (HsubR : subst_tm_env ((z,vb)::tm_rel_env_right M) vb = vb).
    { rewrite subst_tm_env_term_closed_fixed; auto. }
    assert (EbodyL : subst_tm_env ((z,va)::tm_rel_env_left M)
        (subst_tm_types (rel_ty_env_left E) (open_tm t2 (tm_fvar z))) =
      open_tm_rec 0 va (subst_tm_env (tm_rel_env_left M) (subst_tm_types (rel_ty_env_left E) t2))).
    { rewrite subst_tm_types_open_tm_rec. simpl. rewrite subst_tm_env_open_rec by exact HsubL.
      rewrite subst_tm_env_fresh_insert; [reflexivity|exact Hzbody]. }
    assert (EbodyR : subst_tm_env ((z,vb)::tm_rel_env_right M)
        (subst_tm_types (rel_ty_env_right E) (open_tm t2 (tm_fvar z))) =
      open_tm_rec 0 vb (subst_tm_env (tm_rel_env_right M) (subst_tm_types (rel_ty_env_right E) t2))).
    { assert (HzbodyR : ~ In z (tm_fvars (subst_tm_types (rel_ty_env_right E) t2))).
      { intro Hin. apply Hz. repeat (apply in_or_app; right). exact Hin. }
      rewrite subst_tm_types_open_tm_rec. simpl. rewrite subst_tm_env_open_rec by exact HsubR.
      rewrite subst_tm_env_fresh_insert; [reflexivity|exact HzbodyR]. }
    rewrite EbodyL in Hbody. rewrite EbodyR in Hbody.
    destruct Hbody as [Hbl [Hbr [wL [wR [EwL [EwR Hrelw]]]]]].
    destruct EwL as [HwL [HwvL HcwL]]. destruct EwR as [HwR [HwvR HcwR]].
    split; [exact (lc_tm_app HlcL Hla)|]. split; [exact (lc_tm_app HlcR Hlb)|].
    exists wL,wR. split.
    + split.
      * eapply multi_trans.
        -- apply multi_app_r; [apply v_abs; exact HlcL|exact Ha].
        -- eapply multi_step.
           ++ apply ST_AppAbs; [exact HlcL|exact Hva].
           ++ exact HwL.
      * split; assumption.
    + split.
      * split.
        -- eapply multi_trans.
           ++ apply multi_app_r; [apply v_abs; exact HlcR|exact Hb].
           ++ eapply multi_step.
              ** apply ST_AppAbs; [exact HlcR|exact Hvb].
              ** exact HwR.
        -- split; assumption.
      * exact Hrelw.
  - specialize (IHHty1 E M HE HEC HM HMC) as Hf.
    specialize (IHHty2 E M HE HEC HM HMC) as Ha.
    destruct (has_type_substituted_lc Delta Gamma t2 T1 E M Hty2 HEC HMC) as [Hla Hlb].
    eapply rel_exp_app_arrow; eauto.
  -
  -
  -
  -
  -
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
  intros t Ht U v HU Hv Hval.
  eapply logical_relation_identity_extract; eauto.
  apply has_type_empty_term_closed with (Delta := []) (T := U). exact Hval.
Qed.

End SystemFParametricityRecursionHardTask.
