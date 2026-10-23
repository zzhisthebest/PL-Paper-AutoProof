(** System F parametricity benchmark, Hard variant.
    Features: if. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfHardTask.

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


Hint Constructors lc_ty_at lc_tm_at value : core.

Lemma fresh_atom : forall (L : list atom), exists x, ~ In x L.
Proof.
  intro L. exists (S (fold_right Nat.max 0 L)).
  assert (Hbound : forall n, In n L -> n <= fold_right Nat.max 0 L).
  { induction L as [|a L IH]; intros n Hin; simpl in *.
    - contradiction.
    - destruct Hin as [Heq | Hin].
      + subst; lia.
      + specialize (IH n Hin). lia. }
  intros Hin. apply Hbound in Hin. lia.
Qed.

Lemma lc_open_ty_inv : forall k T U,
  lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  intros k T U; revert k U. induction T; intros k U H; simpl in H.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - constructor.
Qed.

Lemma lc_open_tm_inv : forall K k t u,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t u; revert K k u. induction t; intros K k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma lc_open_tm_ty_inv : forall K k t U,
  lc_tm_at k K (open_tm_ty_rec k U t) -> lc_tm_at (S k) K t.
Proof.
  intros K k t U; revert K k U. induction t; intros K k U H; simpl in H.
  - inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; eauto using lc_open_ty_inv.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto using lc_open_ty_inv.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H; unfold locally_closed_ty in *; eauto.
  destruct (fresh_atom L) as [X HX].
  specialize (H0 X HX). constructor.
  apply lc_open_ty_inv with (U := Ty_FVar X). exact H0.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H; unfold locally_closed_tm in *;
    eauto using wf_ty_lc.
  - destruct (fresh_atom L) as [x Hx].
    specialize (H1 x Hx). apply lc_tm_abs.
    + exact (wf_ty_lc Delta T1 H).
    + apply lc_open_tm_inv with (u := tm_fvar x); exact H1.
  - destruct (fresh_atom L) as [X HX].
    specialize (H0 X HX). apply lc_tm_tabs.
    apply lc_open_tm_ty_inv with (U := Ty_FVar X); exact H0.
  - constructor; eauto. exact (wf_ty_lc Delta U H0).
Qed.

Lemma wf_ty_closed : forall U, wf_ty [] U -> locally_closed_ty U.
Proof. intros U H; exact (wf_ty_lc _ _ H). Qed.

Definition binary_relation := tm -> tm -> Prop.
Definition relation_environment := atom -> binary_relation.

Fixpoint value_relation (T : ty) (bound : list binary_relation)
    (free : relation_environment) (left right : tm) : Prop :=
  match T with
  | Ty_BVar index =>
      exists relation, nth_error bound index = Some relation /\
        relation left right
  | Ty_FVar name => free name left right
  | Ty_Arrow domain codomain =>
      value left /\ value right /\
      forall argument_left argument_right,
        value_relation domain bound free argument_left argument_right ->
        exists result_left result_right,
          tm_app left argument_left -->* result_left /\
          tm_app right argument_right -->* result_right /\
          value_relation codomain bound free result_left result_right
  | Ty_All body =>
      value left /\ value right /\
      forall U1 U2 (relation : binary_relation),
        locally_closed_ty U1 -> locally_closed_ty U2 ->
        (forall a b, relation a b -> value a /\ value b) ->
        exists result_left result_right,
          tm_tapp left U1 -->* result_left /\
          tm_tapp right U2 -->* result_right /\
          value_relation body (relation :: bound) free result_left result_right
  | Ty_Bool =>
      (left = tm_true /\ right = tm_true) \/
      (left = tm_false /\ right = tm_false)
  end.

Definition expression_relation T bound free left right :=
  exists result_left result_right,
    left -->* result_left /\ right -->* result_right /\
    value_relation T bound free result_left result_right.

Fixpoint instantiate_type (types : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar index => Ty_BVar index
  | Ty_FVar name => types name
  | Ty_Arrow domain codomain =>
      Ty_Arrow (instantiate_type types domain) (instantiate_type types codomain)
  | Ty_All body => Ty_All (instantiate_type types body)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint instantiate_term (types : atom -> ty) (terms : atom -> tm)
    (term : tm) : tm :=
  match term with
  | tm_bvar index => tm_bvar index
  | tm_fvar name => terms name
  | tm_abs T body =>
      tm_abs (instantiate_type types T) (instantiate_term types terms body)
  | tm_app function argument =>
      tm_app (instantiate_term types terms function)
             (instantiate_term types terms argument)
  | tm_tabs body => tm_tabs (instantiate_term types terms body)
  | tm_tapp function T =>
      tm_tapp (instantiate_term types terms function) (instantiate_type types T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if condition yes no =>
      tm_if (instantiate_term types terms condition)
            (instantiate_term types terms yes)
            (instantiate_term types terms no)
  end.

Definition replace {A : Type} (environment : atom -> A) (name : atom)
    (item : A) : atom -> A :=
  fun other => if Nat.eqb name other then item else environment other.

Fixpoint free_type_names (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar name => [name]
  | Ty_Arrow A B => free_type_names A ++ free_type_names B
  | Ty_All A => free_type_names A
  | Ty_Bool => []
  end.

Fixpoint free_term_names (term : tm) : list atom :=
  match term with
  | tm_bvar _ => []
  | tm_fvar name => [name]
  | tm_abs _ body | tm_tabs body => free_term_names body
  | tm_app a b => free_term_names a ++ free_term_names b
  | tm_tapp a _ => free_term_names a
  | tm_true | tm_false => []
  | tm_if a b c => free_term_names a ++ free_term_names b ++ free_term_names c
  end.

Fixpoint free_term_type_names (term : tm) : list atom :=
  match term with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false => []
  | tm_abs T body => free_type_names T ++ free_term_type_names body
  | tm_app a b => free_term_type_names a ++ free_term_type_names b
  | tm_tabs body => free_term_type_names body
  | tm_tapp a T => free_term_type_names a ++ free_type_names T
  | tm_if a b c => free_term_type_names a ++ free_term_type_names b ++ free_term_type_names c
  end.

Fixpoint free_context_type_names (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: rest => free_type_names T ++ free_context_type_names rest
  end.

Lemma not_in_app_split : forall {A : Type} (item : A) left right,
  ~ In item (left ++ right) -> ~ In item left /\ ~ In item right.
Proof.
  intros A item left right H; split; intro Hin; apply H;
    apply in_or_app; auto.
Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; subst; unfold locally_closed_tm; auto. Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T ->
  forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H; induction H; intros K' Hle.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
  - apply lc_ty_bool.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H; induction H; intros K' k' Htype Hterm.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_weaken; eauto.
    + apply IHlc_tm_at; lia.
  - apply lc_tm_app; [apply IHlc_tm_at1 | apply IHlc_tm_at2]; lia.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
  - apply lc_tm_tapp.
    + apply IHlc_tm_at; lia.
    + eapply lc_ty_weaken; eauto.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; [apply IHlc_tm_at1 | apply IHlc_tm_at2 | apply IHlc_tm_at3]; lia.
Qed.

Lemma instantiate_type_lc : forall K T types,
  lc_ty_at K T ->
  (forall X, locally_closed_ty (types X)) ->
  lc_ty_at K (instantiate_type types T).
Proof.
  intros K T types H; induction H; intros Htypes; simpl.
  - apply lc_ty_bvar; assumption.
  - eapply lc_ty_weaken. exact (Htypes X). lia.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all; auto.
  - apply lc_ty_bool.
Qed.

Lemma instantiate_term_lc : forall K k t types terms,
  lc_tm_at K k t ->
  (forall X, locally_closed_ty (types X)) ->
  (forall x, locally_closed_tm (terms x)) ->
  lc_tm_at K k (instantiate_term types terms t).
Proof.
  intros K k t types terms H; induction H; intros Htypes Hterms; simpl.
  - apply lc_tm_bvar; assumption.
  - eapply lc_tm_weaken. exact (Hterms x). lia. lia.
  - apply lc_tm_abs; eauto using instantiate_type_lc.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs; auto.
  - apply lc_tm_tapp; eauto using instantiate_type_lc.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; auto.
Qed.

Lemma closed_open_type : forall K T, lc_ty_at K T ->
  forall k U, K <= k -> open_ty_rec k U T = T.
Proof.
  intros K T H; induction H; intros depth U Hle; simpl; auto.
  - destruct (Nat.eqb depth i) eqn:Heq; auto.
    apply Nat.eqb_eq in Heq; lia.
  - rewrite IHlc_ty_at1, IHlc_ty_at2; auto.
  - rewrite IHlc_ty_at; auto; lia.
Qed.

Lemma closed_open_term : forall K j t, lc_tm_at K j t ->
  forall k u, j <= k -> open_tm_rec k u t = t.
Proof.
  intros K j t H; induction H; intros depth u Hle; simpl; auto.
  - destruct (Nat.eqb depth i) eqn:Heq; auto.
    apply Nat.eqb_eq in Heq; lia.
  - rewrite IHlc_tm_at; auto; lia.
  - rewrite IHlc_tm_at1, IHlc_tm_at2; auto.
  - rewrite IHlc_tm_at; auto.
  - rewrite IHlc_tm_at; auto.
  - rewrite IHlc_tm_at1, IHlc_tm_at2, IHlc_tm_at3; auto.
Qed.

Lemma closed_open_term_type : forall K j t, lc_tm_at K j t ->
  forall k U, K <= k -> open_tm_ty_rec k U t = t.
Proof.
  intros K j t H; induction H; intros depth U Hle; simpl; auto.
  - rewrite (closed_open_type _ _ H depth U Hle), IHlc_tm_at; auto.
  - rewrite IHlc_tm_at1, IHlc_tm_at2; auto.
  - rewrite IHlc_tm_at; auto; lia.
  - rewrite IHlc_tm_at, (closed_open_type _ _ H0 depth U Hle); auto.
  - rewrite IHlc_tm_at1, IHlc_tm_at2, IHlc_tm_at3; auto.
Qed.

Lemma instantiate_type_open : forall T k types X U,
  ~ In X (free_type_names T) ->
  (forall Y, locally_closed_ty (types Y)) ->
  instantiate_type (replace types X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_type types T).
Proof.
  induction T; intros k types X U Hfresh Htypes; simpl in *; auto.
  - destruct (Nat.eqb k n); simpl; auto.
    unfold replace. rewrite Nat.eqb_refl. reflexivity.
  - simpl in Hfresh. assert (X <> a) by (intro Heq; subst; apply Hfresh; auto).
    unfold replace. rewrite (proj2 (Nat.eqb_neq X a)) by lia.
    symmetry. eapply closed_open_type. exact (Htypes a). lia.
  - apply not_in_app_split in Hfresh. destruct Hfresh.
    rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
Qed.

Lemma instantiate_term_open : forall t k types terms x v,
  ~ In x (free_term_names t) ->
  (forall y, locally_closed_tm (terms y)) ->
  instantiate_term types (replace terms x v)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (instantiate_term types terms t).
Proof.
  induction t; intros k types terms x v Hfresh Hterms; simpl in *; auto.
  - destruct (Nat.eqb k n); simpl; auto.
    unfold replace. rewrite Nat.eqb_refl. reflexivity.
  - assert (x <> a) by (intro Heq; subst; apply Hfresh; auto).
    unfold replace. rewrite (proj2 (Nat.eqb_neq x a)) by lia.
    symmetry. eapply closed_open_term. exact (Hterms a). lia.
  - f_equal. apply IHt; auto.
  - apply not_in_app_split in Hfresh. destruct Hfresh.
    f_equal; auto.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; apply IHt1 || apply IHt2 || apply IHt3; auto; tauto.
Qed.

Lemma instantiate_term_type_open : forall t k types terms X U,
  ~ In X (free_term_type_names t) ->
  (forall Y, locally_closed_ty (types Y)) ->
  (forall y, locally_closed_tm (terms y)) ->
  instantiate_term (replace types X U) terms
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate_term types terms t).
Proof.
  induction t; intros k types terms X U Hfresh Htypes Hterms; simpl in *; auto.
  - symmetry. eapply closed_open_term_type. exact (Hterms a). lia.
  - apply not_in_app_split in Hfresh. destruct Hfresh.
    rewrite instantiate_type_open, IHt; auto.
  - apply not_in_app_split in Hfresh. destruct Hfresh.
    f_equal; auto.
  - f_equal. apply IHt; auto.
  - apply not_in_app_split in Hfresh. destruct Hfresh.
    rewrite IHt, instantiate_type_open; auto.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; apply IHt1 || apply IHt2 || apply IHt3; auto; tauto.
Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H; induction H; intros Hnext; eauto using multi.
Qed.

Lemma multi_app_left : forall a b argument,
  a -->* b -> locally_closed_tm argument ->
  tm_app a argument -->* tm_app b argument.
Proof.
  intros a b argument H; induction H; intros Hclosed; eauto using multi, step.
Qed.

Lemma multi_app_right : forall function a b,
  value function -> a -->* b ->
  tm_app function a -->* tm_app function b.
Proof.
  intros function a b Hvalue H; induction H; eauto using multi, step.
Qed.

Lemma multi_type_app : forall a b U,
  a -->* b -> locally_closed_ty U -> tm_tapp a U -->* tm_tapp b U.
Proof.
  intros a b U H; induction H; intros Hclosed; eauto using multi, step.
Qed.

Lemma multi_if_condition : forall a b yes no,
  a -->* b -> locally_closed_tm yes -> locally_closed_tm no ->
  tm_if a yes no -->* tm_if b yes no.
Proof.
  intros a b yes no H; induction H; intros Hyes Hno;
    eauto using multi, step.
Qed.

Lemma value_relation_closed : forall T bound free left right,
  (forall index relation, nth_error bound index = Some relation ->
    forall a b, relation a b -> value a /\ value b) ->
  (forall name a b, free name a b -> value a /\ value b) ->
  value_relation T bound free left right -> value left /\ value right.
Proof.
  induction T; intros bound free left right Hbound Hfree Hrel; simpl in Hrel.
  - destruct Hrel as [relation [Hindex Hrelated]].
    eapply Hbound; eauto.
  - eapply Hfree; eauto.
  - tauto.
  - tauto.
  - destruct Hrel as [[-> ->] | [-> ->]]; auto.
Qed.

Lemma value_relation_congr : forall T bound1 bound2 free1 free2 left right,
  (forall index, nth_error bound1 index = nth_error bound2 index) ->
  (forall name, In name (free_type_names T) ->
    forall a b, free1 name a b <-> free2 name a b) ->
  value_relation T bound1 free1 left right <->
  value_relation T bound2 free2 left right.
Proof.
  induction T; intros bound1 bound2 free1 free2 left right Hbound Hfree;
    simpl; try tauto.
  - rewrite Hbound. tauto.
  - apply Hfree; simpl; auto.
  - split; intros [Hl [Hr H]]; repeat split; auto;
      intros a b Ha.
    + pose proof (proj2 (IHT1 _ _ _ _ _ _ Hbound
        (fun name Hin => Hfree name (in_or_app _ _ _ (or_introl Hin)))) Ha) as Hb.
      destruct (H a b Hb) as [c [d [Hc [Hd Hresult]]]].
      exists c, d; repeat split; auto.
      apply (proj1 (IHT2 _ _ _ _ _ _ Hbound
        (fun name Hin => Hfree name (in_or_app _ _ _ (or_intror Hin))))); auto.
    + pose proof (proj1 (IHT1 _ _ _ _ _ _ Hbound
        (fun name Hin => Hfree name (in_or_app _ _ _ (or_introl Hin)))) Ha) as Hb.
      destruct (H a b Hb) as [c [d [Hc [Hd Hresult]]]].
      exists c, d; repeat split; auto.
      apply (proj2 (IHT2 _ _ _ _ _ _ Hbound
        (fun name Hin => Hfree name (in_or_app _ _ _ (or_intror Hin))))); auto.
  - split; intros [Hl [Hr H]]; repeat split; auto;
      intros U1 U2 relation Htype1 Htype2 Hvalid.
    + destruct (H U1 U2 relation Htype1 Htype2 Hvalid)
        as [a [b [Ha [Hb Hresult]]]].
      exists a, b; repeat split; auto.
      apply (proj1 (IHT (relation :: bound1) (relation :: bound2)
        free1 free2 a b (fun index => match index with 0 => eq_refl
          | S index => Hbound index end) Hfree)); exact Hresult.
    + destruct (H U1 U2 relation Htype1 Htype2 Hvalid)
        as [a [b [Ha [Hb Hresult]]]].
      exists a, b; repeat split; auto.
      apply (proj2 (IHT (relation :: bound1) (relation :: bound2)
        free1 free2 a b (fun index => match index with 0 => eq_refl
          | S index => Hbound index end) Hfree)); exact Hresult.
Qed.

Lemma value_relation_bound : forall K T,
  lc_ty_at K T -> forall bound1 bound2 free left right,
  (forall index, index < K ->
    nth_error bound1 index = nth_error bound2 index) ->
  value_relation T bound1 free left right <->
  value_relation T bound2 free left right.
Proof.
  intros K T Hlc; induction Hlc; intros bound1 bound2 free left right Hbound;
    simpl; try tauto.
  - rewrite Hbound by assumption. tauto.
  - split; intros [Hl [Hr H]]; repeat split; auto; intros a b Ha.
    + pose proof (proj2 (IHHlc1 _ _ _ _ _ Hbound) Ha) as Hb.
      destruct (H a b Hb) as [c [d [Hc [Hd Hresult]]]].
      exists c, d; repeat split; auto.
      apply (proj1 (IHHlc2 _ _ _ _ _ Hbound)); exact Hresult.
    + pose proof (proj1 (IHHlc1 _ _ _ _ _ Hbound) Ha) as Hb.
      destruct (H a b Hb) as [c [d [Hc [Hd Hresult]]]].
      exists c, d; repeat split; auto.
      apply (proj2 (IHHlc2 _ _ _ _ _ Hbound)); exact Hresult.
  - split; intros [Hl [Hr H]]; repeat split; auto;
      intros U1 U2 relation Htype1 Htype2 Hvalid;
      destruct (H U1 U2 relation Htype1 Htype2 Hvalid)
        as [a [b [Ha [Hb Hresult]]]];
      assert (Hcons : forall index, index < S k ->
        nth_error (relation :: bound1) index =
        nth_error (relation :: bound2) index)
        by (intros [|index] Hlt; simpl; [reflexivity|apply Hbound; lia]);
      exists a, b; repeat split; auto.
    + apply (proj1 (IHHlc _ _ _ _ _ Hcons)); exact Hresult.
    + apply (proj2 (IHHlc _ _ _ _ _ Hcons)); exact Hresult.
Qed.

Lemma value_relation_open : forall T k U R free1 free2 bound left right,
  length bound = k ->
  (forall other_bound a b,
    value_relation U other_bound free1 a b <-> R a b) ->
  (forall name, In name (free_type_names T) ->
    forall a b, free1 name a b <-> free2 name a b) ->
  value_relation (open_ty_rec k U T) bound free1 left right <->
  value_relation T (bound ++ [R]) free2 left right.
Proof.
  induction T; intros k U R free1 free2 bound left right Hlen Hcandidate Hfree;
    simpl in *; try tauto.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst n.
      rewrite nth_error_app2 by lia.
      replace (k - length bound) with 0 by lia. simpl.
      split; intro H.
      * exists R; split; [reflexivity|].
        apply (proj1 (Hcandidate bound left right)); exact H.
      * destruct H as [relation [Hlookup Hrelated]].
        inversion Hlookup; subst relation.
        apply (proj2 (Hcandidate bound left right)); exact Hrelated.
    + apply Nat.eqb_neq in Heq.
      assert (Hlookup : nth_error (bound ++ [R]) n = nth_error bound n).
      { destruct (Nat.lt_ge_cases n k) as [Hlt | Hge].
        - apply nth_error_app1; lia.
        - rewrite nth_error_app2 by lia.
          rewrite (proj2 (nth_error_None bound n) ltac:(lia)).
          destruct (n - length bound) eqn:Hdiff; [lia|destruct n0; reflexivity]. }
      rewrite Hlookup. tauto.
  - apply Hfree; simpl; auto.
  - assert (Hleft : forall name, In name (free_type_names T1) ->
        forall a b, free1 name a b <-> free2 name a b)
        by (intros name Hin; apply Hfree; apply in_or_app; auto).
    assert (Hright : forall name, In name (free_type_names T2) ->
        forall a b, free1 name a b <-> free2 name a b)
        by (intros name Hin; apply Hfree; apply in_or_app; auto).
    split; intros [Hl [Hr H]]; repeat split; auto; intros a b Ha.
    + pose proof (proj2 (IHT1 _ _ _ _ _ _ _ _ Hlen Hcandidate Hleft) Ha) as Hb.
      destruct (H a b Hb) as [c [d [Hc [Hd Hresult]]]].
      exists c, d; repeat split; auto.
      apply (proj1 (IHT2 _ _ _ _ _ _ _ _ Hlen Hcandidate Hright)); exact Hresult.
    + pose proof (proj1 (IHT1 _ _ _ _ _ _ _ _ Hlen Hcandidate Hleft) Ha) as Hb.
      destruct (H a b Hb) as [c [d [Hc [Hd Hresult]]]].
      exists c, d; repeat split; auto.
      apply (proj2 (IHT2 _ _ _ _ _ _ _ _ Hlen Hcandidate Hright)); exact Hresult.
  - split; intros [Hl [Hr H]]; repeat split; auto;
      intros U1 U2 relation Htype1 Htype2 Hvalid;
      destruct (H U1 U2 relation Htype1 Htype2 Hvalid)
        as [a [b [Ha [Hb Hresult]]]];
      exists a, b; repeat split; auto.
    + apply (proj1 (IHT (S k) U R free1 free2 (relation :: bound)
        a b ltac:(simpl; lia) Hcandidate Hfree)); exact Hresult.
    + apply (proj2 (IHT (S k) U R free1 free2 (relation :: bound)
        a b ltac:(simpl; lia) Hcandidate Hfree)); exact Hresult.
Qed.

Lemma relation_open_closed : forall T U free left right,
  locally_closed_ty U ->
  value_relation (open_ty T U) [] free left right <->
  value_relation T [value_relation U [] free] free left right.
Proof.
  intros T U free left right Hclosed.
  apply (value_relation_open T 0 U (value_relation U [] free)
    free free [] left right).
  - reflexivity.
  - intros other_bound a b.
    apply value_relation_bound with (K := 0); auto.
    intros index Hlt; lia.
  - intros name Hin a b; tauto.
Qed.

Lemma relation_open_fvar : forall T X R free left right,
  ~ In X (free_type_names T) ->
  value_relation (open_ty T (Ty_FVar X)) []
    (replace free X R) left right <->
  value_relation T [R] free left right.
Proof.
  intros T X R free left right Hfresh.
  apply (value_relation_open T 0 (Ty_FVar X) R
    (replace free X R) free [] left right).
  - reflexivity.
  - intros other_bound a b; simpl. unfold replace.
    rewrite Nat.eqb_refl. tauto.
  - intros name Hin a b. unfold replace.
    rewrite (proj2 (Nat.eqb_neq X name)) by
      (intro Heq; subst; contradiction). tauto.
Qed.

Lemma lookup_context_free_types : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  In X (free_type_names T) -> In X (free_context_type_names Gamma).
Proof.
  induction Gamma as [|[y A] Gamma IH]; intros x T X Hlookup Hin;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:Heq.
  - inversion Hlookup; subst. apply in_or_app; auto.
  - apply in_or_app; right; eapply IH; eauto.
Qed.

Lemma relation_context_replace : forall Gamma X free R terms1 terms2,
  ~ In X (free_context_type_names Gamma) ->
  (forall x T, lookup_context x Gamma = Some T ->
    value_relation T [] free (terms1 x) (terms2 x)) ->
  forall x T, lookup_context x Gamma = Some T ->
    value_relation T [] (replace free X R) (terms1 x) (terms2 x).
Proof.
  intros Gamma X free R terms1 terms2 Hfresh Hcontext x T Hlookup.
  apply (proj1 (value_relation_congr T [] [] free (replace free X R)
    (terms1 x) (terms2 x) ltac:(intros index; reflexivity)
    ltac:(intros name Hin a b; unfold replace;
      rewrite (proj2 (Nat.eqb_neq X name)) by
        (intro Heq; subst; apply Hfresh;
          eapply lookup_context_free_types; eauto); tauto))).
  apply Hcontext; assumption.
Qed.

Lemma instantiated_typed_closed : forall Delta Gamma t T types terms,
  has_type Delta Gamma t T ->
  (forall X, locally_closed_ty (types X)) ->
  (forall x, value (terms x)) ->
  locally_closed_tm (instantiate_term types terms t).
Proof.
  intros Delta Gamma t T types terms Htyped Htypes Hterms.
  apply instantiate_term_lc.
  - apply has_type_lc with (Delta := Delta) (Gamma := Gamma) (T := T);
      assumption.
  - assumption.
  - intro x. apply value_closed; auto.
Qed.

Lemma relation_value : forall T free a b,
  (forall name x y, free name x y -> value x /\ value y) ->
  value_relation T [] free a b -> value a /\ value b.
Proof.
  intros T free a b Hfree Hrel.
  eapply value_relation_closed; eauto.
  intros index relation Hlookup. destruct index; discriminate.
Qed.

Lemma replace_types_closed : forall types X U,
  (forall Y, locally_closed_ty (types Y)) -> locally_closed_ty U ->
  forall Y, locally_closed_ty (replace types X U Y).
Proof.
  intros types X U Htypes HU Y; unfold replace.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma replace_terms_value : forall terms x v,
  (forall y, value (terms y)) -> value v ->
  forall y, value (replace terms x v y).
Proof.
  intros terms x v Hterms Hv y; unfold replace.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma replace_relation_valid : forall (free : relation_environment) X
    (R : binary_relation),
  (forall name a b, free name a b -> value a /\ value b) ->
  (forall a b, R a b -> value a /\ value b) ->
  forall name a b, replace free X R name a b -> value a /\ value b.
Proof.
  intros free X R Hfree HR name a b; unfold replace.
  destruct (Nat.eqb X name); [apply HR | eapply Hfree]; eauto.
Qed.

Lemma relation_context_term_replace : forall Gamma x T free terms1 terms2 a b,
  (forall y A, lookup_context y Gamma = Some A ->
    value_relation A [] free (terms1 y) (terms2 y)) ->
  value_relation T [] free a b ->
  forall y A, lookup_context y ((x,T) :: Gamma) = Some A ->
    value_relation A [] free
      (replace terms1 x a y) (replace terms2 x b y).
Proof.
  intros Gamma x T free terms1 terms2 a b Hcontext Harg y A Hlookup.
  simpl in Hlookup. unfold replace.
  destruct (Nat.eqb x y) eqn:Heq.
  - rewrite (Nat.eqb_sym y x), Heq in Hlookup.
    inversion Hlookup; subst. exact Harg.
  - rewrite (Nat.eqb_sym y x), Heq in Hlookup.
    eapply Hcontext; eauto.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta1 theta2 gamma1 gamma2 free,
  (forall X, locally_closed_ty (theta1 X) /\ locally_closed_ty (theta2 X)) ->
  (forall x, value (gamma1 x) /\ value (gamma2 x)) ->
  (forall X a b, free X a b -> value a /\ value b) ->
  (forall x A, lookup_context x Gamma = Some A ->
    value_relation A [] free (gamma1 x) (gamma2 x)) ->
  expression_relation T [] free
    (instantiate_term theta1 gamma1 t)
    (instantiate_term theta2 gamma2 t).
Proof.
  intros Delta Gamma t T Htyped.
  induction Htyped; intros theta1 theta2 gamma1 gamma2 free Htheta Hgamma Hfree Hctx;
    unfold expression_relation in *; simpl.
  - exists (gamma1 x), (gamma2 x).
    split; [constructor|split; [constructor|apply Hctx; assumption]].
  - destruct (fresh_atom (L ++ free_term_names t2)) as [x Hfresh].
    apply not_in_app_split in Hfresh as [HL Hbody].
    assert (Habs : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2))
      by (eapply T_Abs; eauto).
    assert (Hclosed1 : locally_closed_tm
      (tm_abs (instantiate_type theta1 T1)
        (instantiate_term theta1 gamma1 t2)))
      by (change (locally_closed_tm
        (instantiate_term theta1 gamma1 (tm_abs T1 t2)));
        eapply instantiated_typed_closed;
        [exact Habs | intros Y; exact (proj1 (Htheta Y)) |
          intros y; exact (proj1 (Hgamma y))]).
    assert (Hclosed2 : locally_closed_tm
      (tm_abs (instantiate_type theta2 T1)
        (instantiate_term theta2 gamma2 t2)))
      by (change (locally_closed_tm
        (instantiate_term theta2 gamma2 (tm_abs T1 t2)));
        eapply instantiated_typed_closed;
        [exact Habs | intros Y; exact (proj2 (Htheta Y)) |
          intros y; exact (proj2 (Hgamma y))]).
    exists (tm_abs (instantiate_type theta1 T1)
      (instantiate_term theta1 gamma1 t2)),
      (tm_abs (instantiate_type theta2 T1)
      (instantiate_term theta2 gamma2 t2)).
    split; [constructor|split; [constructor|]].
    split; [constructor; exact Hclosed1|].
    split; [constructor; exact Hclosed2|].
    intros argument_left argument_right Hargument.
    destruct (relation_value T1 free _ _ Hfree Hargument)
      as [Hargument_left Hargument_right].
    specialize (H1 x HL theta1 theta2
      (replace gamma1 x argument_left) (replace gamma2 x argument_right)
      free Htheta).
    assert (Hterms : forall y, value (replace gamma1 x argument_left y) /\
      value (replace gamma2 x argument_right y)).
    { intro y; split; apply replace_terms_value; auto;
        intros z; apply (Hgamma z). }
    specialize (H1 Hterms Hfree).
    assert (Hnew : forall y A,
      lookup_context y ((x, T1) :: Gamma) = Some A ->
      value_relation A [] free
        (replace gamma1 x argument_left y)
        (replace gamma2 x argument_right y)).
    { eapply relation_context_term_replace; eauto. }
    destruct (H1 Hnew) as [result_left [result_right
      [Hreduce_left [Hreduce_right Hrelated]]]].
    unfold open_tm in Hreduce_left, Hreduce_right.
    rewrite (instantiate_term_open t2 0 theta1 gamma1 x argument_left
      Hbody ltac:(intro y; apply value_closed; apply (Hgamma y))) in Hreduce_left.
    rewrite (instantiate_term_open t2 0 theta2 gamma2 x argument_right
      Hbody ltac:(intro y; apply value_closed; apply (Hgamma y))) in Hreduce_right.
    exists result_left, result_right. repeat split; auto.
    + eapply multi_step; [eapply ST_AppAbs; eauto | exact Hreduce_left].
    + eapply multi_step; [eapply ST_AppAbs; eauto | exact Hreduce_right].
  - destruct (IHHtyped1 _ _ _ _ _ Htheta Hgamma Hfree Hctx)
      as [function_left [function_right
        [Hfunction_left [Hfunction_right Hfunction]]]].
    destruct (IHHtyped2 _ _ _ _ _ Htheta Hgamma Hfree Hctx)
      as [argument_left [argument_right
        [Hargument_left [Hargument_right Hargument]]]].
    simpl in Hfunction.
    destruct Hfunction as [Hvalue_left [Hvalue_right Happly]].
    destruct (Happly argument_left argument_right Hargument)
      as [result_left [result_right
        [Happly_left [Happly_right Hrelated]]]].
    exists result_left, result_right. repeat split; auto.
    + eapply multi_trans.
      * apply multi_app_left; [exact Hfunction_left|].
        eapply instantiated_typed_closed; eauto;
          [intros X; apply (Htheta X)|intros x; apply (Hgamma x)].
      * eapply multi_trans.
        -- apply multi_app_right; eauto.
        -- exact Happly_left.
    + eapply multi_trans.
      * apply multi_app_left; [exact Hfunction_right|].
        eapply instantiated_typed_closed; eauto;
          [intros X; apply (Htheta X)|intros x; apply (Hgamma x)].
      * eapply multi_trans.
        -- apply multi_app_right; eauto.
        -- exact Happly_right.
  - destruct (fresh_atom
      (L ++ free_term_type_names t ++ free_type_names T ++
        free_context_type_names Gamma)) as [X Hfresh].
    apply not_in_app_split in Hfresh as [HL Hrest].
    apply not_in_app_split in Hrest as [Hbody Hrest].
    apply not_in_app_split in Hrest as [Htype Hcontext].
    assert (Htabs : has_type Delta Gamma (tm_tabs t) (Ty_All T))
      by (eapply T_TAbs; eauto).
    assert (Hclosed1 : locally_closed_tm
      (tm_tabs (instantiate_term theta1 gamma1 t)))
      by (change (locally_closed_tm
        (instantiate_term theta1 gamma1 (tm_tabs t)));
        eapply instantiated_typed_closed;
        [exact Htabs|intros Y; exact (proj1 (Htheta Y))|
          intros y; exact (proj1 (Hgamma y))]).
    assert (Hclosed2 : locally_closed_tm
      (tm_tabs (instantiate_term theta2 gamma2 t)))
      by (change (locally_closed_tm
        (instantiate_term theta2 gamma2 (tm_tabs t)));
        eapply instantiated_typed_closed;
        [exact Htabs|intros Y; exact (proj2 (Htheta Y))|
          intros y; exact (proj2 (Hgamma y))]).
    exists (tm_tabs (instantiate_term theta1 gamma1 t)),
      (tm_tabs (instantiate_term theta2 gamma2 t)).
    split; [constructor|split; [constructor|]].
    split; [constructor; exact Hclosed1|].
    split; [constructor; exact Hclosed2|].
    intros U1 U2 relation HU1 HU2 Hrelation.
    specialize (H0 X HL (replace theta1 X U1) (replace theta2 X U2)
      gamma1 gamma2 (replace free X relation)).
    assert (Htypes : forall Y,
      locally_closed_ty (replace theta1 X U1 Y) /\
      locally_closed_ty (replace theta2 X U2 Y)).
    { intro Y; split; apply replace_types_closed; auto;
        intros Z; apply (Htheta Z). }
    specialize (H0 Htypes Hgamma
      (replace_relation_valid free X relation Hfree Hrelation)).
    destruct (H0 (relation_context_replace Gamma X free relation
      gamma1 gamma2 Hcontext Hctx))
      as [result_left [result_right
        [Hreduce_left [Hreduce_right Hrelated]]]].
    unfold open_tm_ty in Hreduce_left, Hreduce_right.
    rewrite (instantiate_term_type_open t 0 theta1 gamma1 X U1
      Hbody ltac:(intros Y; apply (Htheta Y))
      ltac:(intros y; apply value_closed; apply (Hgamma y))) in Hreduce_left.
    rewrite (instantiate_term_type_open t 0 theta2 gamma2 X U2
      Hbody ltac:(intros Y; apply (Htheta Y))
      ltac:(intros y; apply value_closed; apply (Hgamma y))) in Hreduce_right.
    exists result_left, result_right. repeat split; auto.
    + eapply multi_step; [eapply ST_TAppTabs; eauto|exact Hreduce_left].
    + eapply multi_step; [eapply ST_TAppTabs; eauto|exact Hreduce_right].
    + apply (proj1 (relation_open_fvar T X relation free result_left
        result_right Htype)); exact Hrelated.
  - destruct (IHHtyped _ _ _ _ _ Htheta Hgamma Hfree Hctx)
      as [function_left [function_right
        [Hfunction_left [Hfunction_right Hfunction]]]].
    simpl in Hfunction.
    destruct Hfunction as [Hvalue_left [Hvalue_right Happly]].
    assert (HUclosed : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
    assert (Hinst1 : locally_closed_ty (instantiate_type theta1 U))
      by (apply instantiate_type_lc; auto; intros X; apply (Htheta X)).
    assert (Hinst2 : locally_closed_ty (instantiate_type theta2 U))
      by (apply instantiate_type_lc; auto; intros X; apply (Htheta X)).
    assert (Hvalid : forall a b, value_relation U [] free a b ->
      value a /\ value b)
      by (intros a b; eapply relation_value; eauto).
    destruct (Happly _ _ (value_relation U [] free) Hinst1 Hinst2 Hvalid)
      as [result_left [result_right
        [Happly_left [Happly_right Hrelated]]]].
    exists result_left, result_right. repeat split.
    + eapply multi_trans; [apply multi_type_app; eauto|exact Happly_left].
    + eapply multi_trans; [apply multi_type_app; eauto|exact Happly_right].
    + apply (proj2 (relation_open_closed T U free result_left result_right
        HUclosed)); exact Hrelated.
  - exists tm_true, tm_true.
    split; [constructor|split; [constructor|left; auto]].
  - exists tm_false, tm_false.
    split; [constructor|split; [constructor|right; auto]].
  - destruct (IHHtyped1 _ _ _ _ _ Htheta Hgamma Hfree Hctx)
      as [condition_left [condition_right
        [Hcondition_left [Hcondition_right Hcondition]]]].
    destruct (IHHtyped2 _ _ _ _ _ Htheta Hgamma Hfree Hctx)
      as [yes_left [yes_right [Hyes_left [Hyes_right Hyes]]]].
    destruct (IHHtyped3 _ _ _ _ _ Htheta Hgamma Hfree Hctx)
      as [no_left [no_right [Hno_left [Hno_right Hno]]]].
    assert (Hyes_closed_left : locally_closed_tm
      (instantiate_term theta1 gamma1 t2))
      by (eapply instantiated_typed_closed; eauto;
        [intros X; apply (Htheta X)|intros x; apply (Hgamma x)]).
    assert (Hyes_closed_right : locally_closed_tm
      (instantiate_term theta2 gamma2 t2))
      by (eapply instantiated_typed_closed; eauto;
        [intros X; apply (Htheta X)|intros x; apply (Hgamma x)]).
    assert (Hno_closed_left : locally_closed_tm
      (instantiate_term theta1 gamma1 t3))
      by (eapply instantiated_typed_closed; eauto;
        [intros X; apply (Htheta X)|intros x; apply (Hgamma x)]).
    assert (Hno_closed_right : locally_closed_tm
      (instantiate_term theta2 gamma2 t3))
      by (eapply instantiated_typed_closed; eauto;
        [intros X; apply (Htheta X)|intros x; apply (Hgamma x)]).
    destruct Hcondition as [[-> ->] | [-> ->]].
    + exists yes_left, yes_right. repeat split; auto.
      * eapply multi_trans.
        -- apply multi_if_condition; eauto.
        -- eapply multi_step; [apply ST_IfTrue; eauto|exact Hyes_left].
      * eapply multi_trans.
        -- apply multi_if_condition; eauto.
        -- eapply multi_step; [apply ST_IfTrue; eauto|exact Hyes_right].
    + exists no_left, no_right. repeat split; auto.
      * eapply multi_trans.
        -- apply multi_if_condition; eauto.
        -- eapply multi_step; [apply ST_IfFalse; eauto|exact Hno_left].
      * eapply multi_trans.
        -- apply multi_if_condition; eauto.
        -- eapply multi_step; [apply ST_IfFalse; eauto|exact Hno_right].
Qed.

Lemma free_term_names_open : forall t k x y,
  In y (free_term_names t) ->
  In y (free_term_names (open_tm_rec k (tm_fvar x) t)).
Proof.
  induction t; intros k x y Hin; simpl in *; try contradiction; auto.
  - apply in_app_iff in Hin. apply in_app_iff.
    destruct Hin as [Hin | Hin]; [left; apply IHt1 | right; apply IHt2];
      assumption.
  - repeat rewrite in_app_iff in *.
    destruct Hin as [Hin | [Hin | Hin]].
    + left; apply IHt1; assumption.
    + right; left; apply IHt2; assumption.
    + right; right; apply IHt3; assumption.
Qed.

Lemma free_term_names_open_type : forall t k U,
  free_term_names (open_tm_ty_rec k U t) = free_term_names t.
Proof.
  induction t; intros k U; simpl; auto;
    try (f_equal; auto; fail).
  rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma typing_term_support : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall y, In y (free_term_names t) ->
    exists A, lookup_context y Gamma = Some A.
Proof.
  intros Delta Gamma t T Htyped; induction Htyped; intros y Hin;
    simpl in Hin; try contradiction.
  - destruct Hin as [-> | []]. exists T. assumption.
  - destruct (fresh_atom (L ++ [y])) as [x Hfresh].
    apply not_in_app_split in Hfresh as [HL Hneq].
    specialize (H1 x HL y
      (free_term_names_open t2 0 x y Hin)).
    destruct H1 as [A Hlookup].
    exists A. simpl in Hlookup.
    assert (y <> x) by (intro Heq; subst; apply Hneq; simpl; auto).
    rewrite (proj2 (Nat.eqb_neq y x)) in Hlookup by assumption.
    exact Hlookup.
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + eapply IHHtyped1; eauto.
    + eapply IHHtyped2; eauto.
  - destruct (fresh_atom L) as [X HX].
    specialize (H0 X HX y).
    unfold open_tm_ty in H0.
    rewrite free_term_names_open_type in H0.
    apply H0; assumption.
  - eapply IHHtyped; eauto.
  - repeat rewrite in_app_iff in Hin.
    destruct Hin as [Hin | [Hin | Hin]].
    + eapply IHHtyped1; eauto.
    + eapply IHHtyped2; eauto.
    + eapply IHHtyped3; eauto.
Qed.

Lemma instantiate_type_identity : forall T,
  instantiate_type (fun X => Ty_FVar X) T = T.
Proof. induction T; simpl; congruence. Qed.

Lemma instantiate_term_identity : forall t terms,
  (forall x, In x (free_term_names t) -> terms x = tm_fvar x) ->
  instantiate_term (fun X => Ty_FVar X) terms t = t.
Proof.
  induction t; intros terms Hnames; simpl; auto.
  - apply Hnames; simpl; auto.
  - rewrite instantiate_type_identity.
    rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto; intros x Hin; apply Hnames;
      simpl; apply in_or_app; auto.
  - rewrite IHt; auto.
  - rewrite IHt, instantiate_type_identity; auto.
  - rewrite IHt1, IHt2, IHt3; auto;
      intros x Hin; apply Hnames; simpl;
      repeat rewrite in_app_iff; auto.
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
  intros t Htyped U v HU Hv Hvtyped.
  set (theta := fun X : atom => Ty_FVar X).
  set (terms := fun _ : atom => tm_true).
  set (free := fun _ : atom => fun _ _ : tm => False).
  assert (Hidentity : instantiate_term theta terms t = t).
  { unfold theta. apply instantiate_term_identity.
    intros x Hin.
    destruct (typing_term_support [] empty t _ Htyped x Hin)
      as [A Hlookup]. discriminate. }
  pose proof (fundamental [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Htyped
    theta theta terms terms free
    ltac:(intro X; split; unfold locally_closed_ty, theta; constructor)
    ltac:(intro x; split; unfold terms; constructor)
    ltac:(intros X a b Habsurd; contradiction)
    ltac:(intros x A Hlookup; discriminate)) as Hfundamental.
  unfold expression_relation in Hfundamental.
  rewrite Hidentity in Hfundamental.
  destruct Hfundamental as [poly_left [poly_right
    [Hpoly_left [Hpoly_right Hrelated]]]].
  simpl in Hrelated.
  destruct Hrelated as [_ [_ Hall]].
  set (singleton := fun a b : tm => a = v /\ b = v).
  assert (Hsingleton : forall a b, singleton a b -> value a /\ value b).
  { intros a b [-> ->]; auto. }
  destruct (Hall U U singleton (wf_ty_lc [] U HU)
    (wf_ty_lc [] U HU) Hsingleton)
    as [function_left [function_right
      [Hinstantiate_left [Hinstantiate_right Harrow]]]].
  simpl in Harrow.
  destruct Harrow as [_ [_ Happly]].
  assert (Hargument : value_relation (Ty_BVar 0) [singleton] free v v).
  { simpl. exists singleton. split; [reflexivity|].
    unfold singleton; auto. }
  destruct (Happly v v Hargument) as [result_left [result_right
    [Happlication_left [Happlication_right Hresult]]]].
  simpl in Hresult.
  destruct Hresult as [relation [Hlookup Hresult]].
  inversion Hlookup; subst relation.
  destruct Hresult as [Hequal _]. subst result_left.
  eapply multi_trans.
  - apply multi_app_left.
    + apply multi_type_app; [exact Hpoly_left|].
      exact (wf_ty_lc [] U HU).
    + apply value_closed; exact Hv.
  - eapply multi_trans.
    + apply multi_app_left; [exact Hinstantiate_left|].
      apply value_closed; exact Hv.
    + exact Happlication_left.
Qed.

End SystemFParametricityIfHardTask.
