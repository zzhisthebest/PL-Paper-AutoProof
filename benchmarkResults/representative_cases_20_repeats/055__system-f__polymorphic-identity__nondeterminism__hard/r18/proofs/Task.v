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

(* ================================================================== *)
(* Part 1: list / freshness helpers                                    *)
(* ================================================================== *)

Fixpoint lmax (l : list atom) : atom :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (lmax l')
  end.

Lemma lmax_spec : forall l x, In x l -> x <= lmax l.
Proof.
  induction l as [| y l IH]; intros x Hx.
  - destruct Hx.
  - simpl in Hx. destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto | apply Nat.le_max_r].
Qed.

Definition fresh_atom (l : list atom) : atom := S (lmax l).

Lemma fresh_atom_spec : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l H. unfold fresh_atom in H. apply lmax_spec in H. lia.
Qed.

Lemma in_app_l : forall (A : Type) (l l' : list A) (x : A), In x l -> In x (l ++ l').
Proof. intros; apply in_app_iff; auto. Qed.

Lemma in_app_r : forall (A : Type) (l l' : list A) (x : A), In x l' -> In x (l ++ l').
Proof. intros; apply in_app_iff; auto. Qed.

(* ================================================================== *)
(* Part 2: atoms occurring in types / terms / contexts                 *)
(* ================================================================== *)

Fixpoint atoms_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => atoms_ty T1 ++ atoms_ty T2
  | Ty_All T1 => atoms_ty T1
  end.

Fixpoint atoms_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T b => atoms_ty T ++ atoms_tm b
  | tm_app t1 t2 => atoms_tm t1 ++ atoms_tm t2
  | tm_tabs b => atoms_tm b
  | tm_tapp b T => atoms_tm b ++ atoms_ty T
  | tm_choice t1 t2 => atoms_tm t1 ++ atoms_tm t2
  end.

Definition atoms_context (Gamma : context) : list atom :=
  flat_map (fun p => atoms_ty (snd p)) Gamma.

Lemma lookup_context_In : forall x (Gamma : context) T,
  lookup_context x Gamma = Some T -> In (x, T) Gamma.
Proof.
  induction Gamma as [| [y Ty] Gamma IH]; intros T H; simpl in H.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. injection H as Heq. subst. left. auto.
    + right. apply IH; auto.
Qed.

Lemma in_atoms_context : forall Gamma X,
  In X (atoms_context Gamma) ->
  exists x T, In (x, T) Gamma /\ In X (atoms_ty T).
Proof.
  intros Gamma X H. unfold atoms_context in H.
  apply in_flat_map in H. destruct H as [[x T] [Hin Ht]].
  exists x, T. split; auto.
Qed.

Lemma atoms_context_in : forall Gamma x T X,
  In (x, T) Gamma -> In X (atoms_ty T) -> In X (atoms_context Gamma).
Proof.
  intros. unfold atoms_context. apply in_flat_map. exists (x, T). split; auto.
Qed.

(* ================================================================== *)
(* Part 3: local closedness lemmas                                     *)
(* ================================================================== *)

Lemma lc_ty_at_mono : forall T k k', k <= k' -> lc_ty_at k T -> lc_ty_at k' T.
Proof.
  induction T; intros k k' Hle Hlc; inversion Hlc; subst.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - apply lc_ty_all. apply IHT with (k := S k) (k' := S k'); [lia | assumption].
Qed.

Lemma lc_tm_at_mono : forall t K n K' n',
  K <= K' -> n <= n' -> lc_tm_at K n t -> lc_tm_at K' n' t.
Proof.
  induction t; intros K0 N0 K1 N1 HK HN H; inversion H; subst.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_at_mono; eauto.
    + apply IHt with (K := K0) (n := S N0) (K' := K1) (n' := S N1); [lia | lia | assumption].
  - apply lc_tm_app.
    + apply IHt1 with (K := K0) (n := N0) (K' := K1) (n' := N1); [lia | lia | assumption].
    + apply IHt2 with (K := K0) (n := N0) (K' := K1) (n' := N1); [lia | lia | assumption].
  - apply lc_tm_tabs. apply IHt with (K := S K0) (n := N0) (K' := S K1) (n' := N1); [lia | lia | assumption].
  - apply lc_tm_tapp.
    + apply IHt with (K := K0) (n := N0) (K' := K1) (n' := N1); [lia | lia | assumption].
    + eapply lc_ty_at_mono; eauto.
  - apply lc_tm_choice.
    + apply IHt1 with (K := K0) (n := N0) (K' := K1) (n' := N1); [lia | lia | assumption].
    + apply IHt2 with (K := K0) (n := N0) (K' := K1) (n' := N1); [lia | lia | assumption].
Qed.

Lemma lc_ty_at_all : forall T, locally_closed_ty T -> forall k, lc_ty_at k T.
Proof.
  intros T H k. apply lc_ty_at_mono with (k := 0); auto. lia.
Qed.

Lemma lc_ty_fvar_all : forall X k, lc_ty_at k (Ty_FVar X).
Proof. intros; apply lc_ty_fvar. Qed.

Lemma value_lc : forall t, value t -> locally_closed_tm t.
Proof. intros t H; inversion H; subst; assumption. Qed.

(* opening inversions: from the opened thing being locally closed,
   deduce the original is locally closed one level deeper *)

Lemma lc_ty_open_inv : forall T k U,
  (forall m, lc_ty_at m U) ->
  lc_ty_at k (open_ty_rec k U T) ->
  lc_ty_at (S k) T.
Proof.
  induction T; intros k U HU H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + apply Nat.eqb_neq in E. inversion H; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion H; subst. apply lc_ty_arrow.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - apply lc_ty_all. inversion H; subst.
    eapply IHT with (k := S k) (U := U); eauto.
Qed.

Lemma lc_ty_open_fwd : forall T k U,
  lc_ty_at (S k) T -> (forall m, lc_ty_at m U) ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. auto.
    + apply Nat.eqb_neq in E. inversion HT; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion HT; subst. apply lc_ty_arrow.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - apply lc_ty_all. inversion HT; subst.
    eapply IHT with (k := S k) (U := U); eauto.
Qed.

Lemma lc_tm_at_K_mono : forall t K K' n, K <= K' -> lc_tm_at K n t -> lc_tm_at K' n t.
Proof.
  intros t K K' n H1 H2. eapply lc_tm_at_mono; eauto.
Qed.

Lemma lc_tm_open_inv : forall t K n u,
  (forall m, lc_tm_at K m u) ->
  lc_tm_at K n (open_tm_rec n u t) ->
  lc_tm_at K (S n) t.
Proof.
  induction t; intros K N u HU H; simpl in H.
  - destruct (Nat.eqb N n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + apply Nat.eqb_neq in E. inversion H; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + assumption.
    + eapply IHt; eauto.
  - inversion H; subst. apply lc_tm_app.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - apply lc_tm_tabs. inversion H; subst.
    eapply IHt with (K := S K) (n := N); [intros m; apply (lc_tm_at_K_mono u K (S K) m); [lia | apply HU] | assumption].
  - inversion H; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + assumption.
  - inversion H; subst. apply lc_tm_choice.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
Qed.

Lemma lc_tm_open_fwd : forall t K n u,
  lc_tm_at K (S n) t -> (forall m, lc_tm_at K m u) ->
  lc_tm_at K n (open_tm_rec n u t).
Proof.
  induction t; intros K N u HT HU; simpl.
  - destruct (Nat.eqb N n) eqn:E.
    + apply Nat.eqb_eq in E. subst. auto.
    + apply Nat.eqb_neq in E. inversion HT; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion HT; subst. apply lc_tm_abs.
    + assumption.
    + eapply IHt; eauto.
  - inversion HT; subst. apply lc_tm_app.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - apply lc_tm_tabs. inversion HT; subst.
    eapply IHt with (K := S K) (n := N); [assumption | intros m; apply (lc_tm_at_K_mono u K (S K) m); [lia | apply HU]].
  - inversion HT; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + assumption.
  - inversion HT; subst. apply lc_tm_choice.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
Qed.

Lemma lc_tm_open_ty_inv : forall t K n U,
  (forall m, lc_ty_at m U) ->
  lc_tm_at K n (open_tm_ty_rec K U t) ->
  lc_tm_at (S K) n t.
Proof.
  induction t; intros K N U HU H; simpl in H.
  - inversion H; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + eapply lc_ty_open_inv; eauto.
    + eapply IHt; eauto.
  - inversion H; subst. apply lc_tm_app.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - apply lc_tm_tabs. inversion H; subst.
    eapply IHt with (K := S K) (n := N); eauto.
  - inversion H; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply lc_ty_open_inv with (k := K) (U := U); eauto.
  - inversion H; subst. apply lc_tm_choice.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
Qed.

Lemma lc_tm_open_ty_fwd : forall t K n U,
  lc_tm_at (S K) n t -> (forall m, lc_ty_at m U) ->
  lc_tm_at K n (open_tm_ty_rec K U t).
Proof.
  induction t; intros K N U HT HU; simpl.
  - apply lc_tm_bvar. inversion HT; lia.
  - apply lc_tm_fvar.
  - inversion HT; subst. apply lc_tm_abs.
    + eapply lc_ty_open_fwd; eauto.
    + eapply IHt; eauto.
  - inversion HT; subst. apply lc_tm_app.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - apply lc_tm_tabs. inversion HT; subst.
    eapply IHt with (K := S K) (n := N); eauto.
  - inversion HT; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply lc_ty_open_fwd; eauto.
  - inversion HT; subst. apply lc_tm_choice.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
Qed.

(* wf_ty implies local closedness *)
Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H.
  induction H as [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T Hbody IHb].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    set (X := fresh_atom L).
    assert (HX : ~ In X L) by (unfold X; apply fresh_atom_spec).
    specialize (IHb X HX).
    eapply lc_ty_open_inv with (k := 0) (U := Ty_FVar X).
    + intros; apply lc_ty_fvar.
    + exact IHb.
Qed.

(* has_type implies local closedness of the term *)
Lemma has_type_lc : forall Delta Gamma t T, has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H.
  induction H as [Delta Gamma x T Hlook Hwf
                | L Delta Gamma T1 t2 T2 Hwf Hbody IHb
                | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                | L Delta Gamma t T Hbody IHb
                | Delta Gamma t T U H1 IH1 Hwf
                | Delta Gamma t1 t2 T H1 IH1 H2 IH2].
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply wf_ty_lc; eassumption.
    + set (x := fresh_atom (L ++ atoms_tm t2)).
      assert (HxL : ~ In x L).
      { intro Hc. apply (fresh_atom_spec (L ++ atoms_tm t2)). apply in_app_iff. auto. }
      specialize (IHb x HxL).
      eapply lc_tm_open_inv with (K := 0) (n := 0) (u := tm_fvar x).
      * intros; apply lc_tm_fvar.
      * exact IHb.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    set (X := fresh_atom (L ++ atoms_ty T)).
    assert (HXL : ~ In X L).
    { intro Hc. apply (fresh_atom_spec (L ++ atoms_ty T)). apply in_app_iff. auto. }
    specialize (IHb X HXL).
    eapply lc_tm_open_ty_inv with (K := 0) (n := 0) (U := Ty_FVar X).
    * intros; apply lc_ty_fvar.
    * exact IHb.
  - apply lc_tm_tapp; [assumption | eapply wf_ty_lc; eassumption].
  - apply lc_tm_choice; assumption.
Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T, has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H.
  induction H as [Delta Gamma x T Hlook Hwf
                | L Delta Gamma T1 t2 T2 Hwf Hbody IHb
                | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                | L Delta Gamma t T Hbody IHb
                | Delta Gamma t T U H1 IH1 Hwf
                | Delta Gamma t1 t2 T H1 IH1 H2 IH2].
  - eapply wf_ty_lc; eassumption.
  - apply lc_ty_arrow.
    + eapply wf_ty_lc; eassumption.
    + set (x := fresh_atom (L ++ atoms_tm t2)).
      assert (HxL : ~ In x L).
      { intro Hc. apply (fresh_atom_spec (L ++ atoms_tm t2)). apply in_app_iff. auto. }
      specialize (IHb x HxL). exact IHb.
  - inversion IH1; subst. assumption.
  - apply lc_ty_all.
    set (X := fresh_atom (L ++ atoms_ty T)).
    assert (HXL : ~ In X L).
    { intro Hc. apply (fresh_atom_spec (L ++ atoms_ty T)). apply in_app_iff. auto. }
    specialize (IHb X HXL).
    eapply lc_ty_open_inv with (k := 0) (U := Ty_FVar X).
    + intros; apply lc_ty_fvar.
    + exact IHb.
  - apply lc_ty_open_fwd.
    + inversion IH1; subst. assumption.
    + intros m. apply lc_ty_at_mono with (k := 0); [lia | eapply wf_ty_lc; eassumption].
  - assumption.
Qed.

(* ================================================================== *)
(* Part 4: semantic types, type instantiation, term instantiation      *)
(* ================================================================== *)

Record sem_ty := {
  sty_ty : ty;
  sty_lc : locally_closed_ty sty_ty;
  sty_rel : tm -> Prop;
  sty_rel_value : forall t, sty_rel t -> value t
}.

Definition default_sem_ty : sem_ty.
Proof.
  refine {| sty_ty := Ty_All (Ty_BVar 0); sty_rel := fun _ => False |}.
  - apply lc_ty_all, lc_ty_bvar. lia.
  - intros t H. destruct H.
Defined.

Definition nth_sem (E : list sem_ty) (i : nat) : sem_ty :=
  match nth_error E i with Some s => s | None => default_sem_ty end.

Definition mk_sem (U : ty) (Hlc : locally_closed_ty U) (R : tm -> Prop)
  (HR : forall t, R t -> value t) : sem_ty :=
  {| sty_ty := U; sty_lc := Hlc; sty_rel := R; sty_rel_value := HR |}.

Definition sty (sigma : atom -> sem_ty) : atom -> ty := fun X => sty_ty (sigma X).

Definition upd_sem (sigma : atom -> sem_ty) (X : atom) (s : sem_ty) : atom -> sem_ty :=
  fun Y => if Nat.eqb Y X then s else sigma Y.

Definition upd_rho (rho : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else rho y.

Lemma upd_sem_X : forall sigma X s, upd_sem sigma X s X = s.
Proof. intros. unfold upd_sem. rewrite Nat.eqb_refl. auto. Qed.

Lemma upd_sem_other : forall sigma X s Y, Y <> X -> upd_sem sigma X s Y = sigma Y.
Proof. intros. unfold upd_sem. apply Nat.eqb_neq in H. rewrite H. auto. Qed.

Lemma upd_rho_x : forall rho x u, upd_rho rho x u x = u.
Proof. intros. unfold upd_rho. rewrite Nat.eqb_refl. auto. Qed.

Lemma upd_rho_other : forall rho x u y, y <> x -> upd_rho rho x u y = rho y.
Proof. intros. unfold upd_rho. apply Nat.eqb_neq in H. rewrite H. auto. Qed.

Lemma mk_sem_ty : forall U H R HR, sty_ty (mk_sem U H R HR) = U.
Proof. reflexivity. Qed.

Lemma mk_sem_rel : forall U H R HR t, sty_rel (mk_sem U H R HR) t = R t.
Proof. reflexivity. Qed.

(* --- type instantiation --- *)

Fixpoint ty_inst (s : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => s X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_inst s T1) (ty_inst s T2)
  | Ty_All T1 => Ty_All (ty_inst s T1)
  end.

Fixpoint tm_ty_inst (s : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (ty_inst s T) (tm_ty_inst s b)
  | tm_app t1 t2 => tm_app (tm_ty_inst s t1) (tm_ty_inst s t2)
  | tm_tabs b => tm_tabs (tm_ty_inst s b)
  | tm_tapp b T => tm_tapp (tm_ty_inst s b) (ty_inst s T)
  | tm_choice t1 t2 => tm_choice (tm_ty_inst s t1) (tm_ty_inst s t2)
  end.

Fixpoint tm_rho_inst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_abs T b => tm_abs T (tm_rho_inst rho b)
  | tm_app t1 t2 => tm_app (tm_rho_inst rho t1) (tm_rho_inst rho t2)
  | tm_tabs b => tm_tabs (tm_rho_inst rho b)
  | tm_tapp b T => tm_tapp (tm_rho_inst rho b) T
  | tm_choice t1 t2 => tm_choice (tm_rho_inst rho t1) (tm_rho_inst rho t2)
  end.

Definition inst (sigma : atom -> sem_ty) (rho : atom -> tm) (t : tm) : tm :=
  tm_rho_inst rho (tm_ty_inst (sty sigma) t).

(* --- commutation of instantiation with the opening operations --- *)

Lemma open_ty_rec_lc : forall T n k V, lc_ty_at n T -> n <= k -> open_ty_rec k V T = T.
Proof.
  induction T; intros N k V H Hle; simpl.
  - inversion H; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + auto.
  - auto.
  - inversion H; subst.
    rewrite IHT1 with (n := N) (k := k) (V := V); auto.
    rewrite IHT2 with (n := N) (k := k) (V := V); auto.
  - inversion H; subst.
    rewrite IHT with (n := S N) (k := S k) (V := V); auto. lia.
Qed.

Lemma ty_inst_open_ty : forall s k U T,
  (forall X, locally_closed_ty (s X)) ->
  ty_inst s (open_ty_rec k U T) = open_ty_rec k (ty_inst s U) (ty_inst s T).
Proof.
  intros s k U T Hs. revert k U. induction T; intros k U; simpl.
  - destruct (Nat.eqb k n); auto.
  - symmetry. apply open_ty_rec_lc with (n := 0).
    + apply Hs.
    + lia.
  - rewrite IHT1; auto. rewrite IHT2; auto.
  - rewrite IHT; auto.
Qed.

Lemma ty_inst_id : forall T, ty_inst (fun X => Ty_FVar X) T = T.
Proof. induction T; simpl; congruence. Qed.

Lemma tm_ty_inst_open_tm : forall s t u k,
  tm_ty_inst s (open_tm_rec k u t) = open_tm_rec k (tm_ty_inst s u) (tm_ty_inst s t).
Proof.
  intros s t. induction t; intros u k; simpl.
  - destruct (Nat.eqb k n); auto.
  - auto.
  - rewrite IHt. auto.
  - rewrite IHt1, IHt2. auto.
  - rewrite IHt. auto.
  - rewrite IHt. auto.
  - rewrite IHt1, IHt2. auto.
Qed.

Lemma open_tm_rec_lc : forall t K n k u,
  lc_tm_at K n t -> n <= k -> open_tm_rec k u t = t.
Proof.
  induction t; intros K N k u H Hle; simpl.
  - inversion H; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + auto.
  - auto.
  - inversion H; subst. rewrite IHt with (K := K) (n := S N) (k := S k); auto. lia.
  - inversion H; subst. rewrite IHt1 with (K := K) (n := N) (k := k); auto.
    rewrite IHt2 with (K := K) (n := N) (k := k); auto.
  - inversion H; subst. rewrite IHt with (K := S K) (n := N) (k := k); auto.
  - inversion H; subst. rewrite IHt with (K := K) (n := N) (k := k); auto.
  - inversion H; subst. rewrite IHt1 with (K := K) (n := N) (k := k); auto.
    rewrite IHt2 with (K := K) (n := N) (k := k); auto.
Qed.

Lemma open_tm_ty_rec_lc : forall t K n U,
  lc_tm_at K n t -> open_tm_ty_rec K U t = t.
Proof.
  induction t; intros K N U H; simpl.
  - auto.
  - auto.
  - inversion H; subst. rewrite IHt with (K := K) (n := S N); auto.
    rewrite open_ty_rec_lc with (n := K) (k := K) (V := U); auto.
  - inversion H; subst. rewrite IHt1 with (K := K) (n := N); auto.
    rewrite IHt2 with (K := K) (n := N); auto.
  - inversion H; subst. rewrite IHt with (K := S K) (n := N); auto.
  - inversion H; subst. rewrite IHt with (K := K) (n := N); auto.
    rewrite open_ty_rec_lc with (n := K) (k := K) (V := U); auto.
  - inversion H; subst. rewrite IHt1 with (K := K) (n := N); auto.
    rewrite IHt2 with (K := K) (n := N); auto.
Qed.

Lemma tm_rho_inst_open_tm : forall rho t u k,
  (forall x, locally_closed_tm (rho x)) ->
  tm_rho_inst rho (open_tm_rec k u t) = open_tm_rec k (tm_rho_inst rho u) (tm_rho_inst rho t).
Proof.
  intros rho t. induction t; intros u k Hrho; simpl.
  - destruct (Nat.eqb k n); auto.
  - symmetry. apply open_tm_rec_lc with (K := 0) (n := 0); [apply Hrho | lia].
  - rewrite IHt; auto.
  - rewrite IHt1; auto. rewrite IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1; auto. rewrite IHt2; auto.
Qed.

Lemma tm_ty_inst_open_tm_ty : forall s t U k,
  (forall X, locally_closed_ty (s X)) ->
  tm_ty_inst s (open_tm_ty_rec k U t) = open_tm_ty_rec k (ty_inst s U) (tm_ty_inst s t).
Proof.
  intros s t. induction t; intros U k Hs; simpl.
  - auto.
  - auto.
  - rewrite IHt; auto. rewrite ty_inst_open_ty; auto.
  - rewrite IHt1; auto. rewrite IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto. rewrite ty_inst_open_ty; auto.
  - rewrite IHt1; auto. rewrite IHt2; auto.
Qed.

Lemma tm_rho_inst_open_tm_ty : forall rho t U k,
  (forall x, locally_closed_tm (rho x)) ->
  tm_rho_inst rho (open_tm_ty_rec k U t) = open_tm_ty_rec k U (tm_rho_inst rho t).
Proof.
  intros rho t. induction t; intros U k Hrho; simpl.
  - auto.
  - symmetry. apply open_tm_ty_rec_lc with (K := k) (n := 0).
    apply (lc_tm_at_K_mono (rho a) 0 k 0); [lia | apply Hrho].
  - rewrite IHt; auto.
  - rewrite IHt1; auto. rewrite IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1; auto. rewrite IHt2; auto.
Qed.

Lemma inst_open_tm : forall sigma rho t u,
  (forall x, locally_closed_tm (rho x)) ->
  inst sigma rho (open_tm t u) = open_tm (inst sigma rho t) (inst sigma rho u).
Proof.
  intros. unfold inst, open_tm.
  rewrite tm_ty_inst_open_tm. rewrite tm_rho_inst_open_tm; auto.
Qed.

Lemma inst_open_tm_ty : forall sigma rho t U,
  (forall x, locally_closed_tm (rho x)) ->
  inst sigma rho (open_tm_ty t U) = open_tm_ty (inst sigma rho t) (ty_inst (sty sigma) U).
Proof.
  intros. unfold inst, open_tm_ty.
  rewrite tm_ty_inst_open_tm_ty; [| intros X; apply sty_lc].
  rewrite tm_rho_inst_open_tm_ty; auto.
Qed.

Lemma ty_inst_id_gen : forall s, (forall X, s X = Ty_FVar X) -> forall T, ty_inst s T = T.
Proof.
  intros s Hs T. induction T; simpl; try reflexivity.
  - apply Hs.
  - rewrite IHT1, IHT2; reflexivity.
  - rewrite IHT; reflexivity.
Qed.

Lemma tm_ty_inst_id_gen : forall s, (forall X, s X = Ty_FVar X) -> forall t, tm_ty_inst s t = t.
Proof.
  intros s Hs t. induction t; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHt, (ty_inst_id_gen s Hs). reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt, (ty_inst_id_gen s Hs). reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma tm_rho_inst_id_gen : forall rho, (forall x, rho x = tm_fvar x) -> forall t, tm_rho_inst rho t = t.
Proof.
  intros rho Hr t. induction t; simpl.
  - reflexivity.
  - apply Hr.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma inst_id_ty_inst : forall t, tm_ty_inst (fun X => Ty_FVar X) t = t.
Proof. apply tm_ty_inst_id_gen. intros; reflexivity. Qed.

Lemma inst_id_rho_inst : forall t, tm_rho_inst (fun x => tm_fvar x) t = t.
Proof. apply tm_rho_inst_id_gen. intros; reflexivity. Qed.

(* --- extensionality of instantiation w.r.t. the environments --- *)

Lemma ty_inst_ext : forall s s' T,
  (forall X, In X (atoms_ty T) -> s X = s' X) ->
  ty_inst s T = ty_inst s' T.
Proof.
  intros s s' T. induction T; intros H; simpl.
  - reflexivity.
  - apply H. simpl. auto.
  - rewrite IHT1, IHT2; auto;
      intros X HX; apply H; simpl; apply in_app_iff; auto.
  - rewrite IHT; auto.
Qed.

Lemma tm_ty_inst_ext : forall s s' t,
  (forall X, In X (atoms_tm t) -> s X = s' X) ->
  tm_ty_inst s t = tm_ty_inst s' t.
Proof.
  intros s s' t.
  induction t as [bn | fa | Ta ba IHba | a1 IHa1 a2 IHa2 | tb IHtb | tb2 IHtb2 Ta2 | c1 IHc1 c2 IHc2]; intros H; simpl.
  - reflexivity.
  - reflexivity.
  - assert (E1 : ty_inst s Ta = ty_inst s' Ta).
    { apply ty_inst_ext. intros X HX. apply H. simpl. apply in_app_iff. auto. }
    assert (E2 : tm_ty_inst s ba = tm_ty_inst s' ba).
    { apply IHba. intros X HX. apply H. simpl. apply in_app_iff. auto. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : tm_ty_inst s a1 = tm_ty_inst s' a1).
    { apply IHa1. intros X HX. apply H. simpl. apply in_app_iff. auto. }
    assert (E2 : tm_ty_inst s a2 = tm_ty_inst s' a2).
    { apply IHa2. intros X HX. apply H. simpl. apply in_app_iff. auto. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : tm_ty_inst s tb = tm_ty_inst s' tb).
    { apply IHtb. intros X HX. apply H. simpl. auto. }
    rewrite E1. reflexivity.
  - assert (E1 : tm_ty_inst s tb2 = tm_ty_inst s' tb2).
    { apply IHtb2. intros X HX. apply H. simpl. apply in_app_iff. auto. }
    assert (E2 : ty_inst s Ta2 = ty_inst s' Ta2).
    { apply ty_inst_ext. intros X HX. apply H. simpl. apply in_app_iff. auto. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : tm_ty_inst s c1 = tm_ty_inst s' c1).
    { apply IHc1. intros X HX. apply H. simpl. apply in_app_iff. auto. }
    assert (E2 : tm_ty_inst s c2 = tm_ty_inst s' c2).
    { apply IHc2. intros X HX. apply H. simpl. apply in_app_iff. auto. }
    rewrite E1, E2. reflexivity.
Qed.

Lemma tm_rho_inst_ext : forall rho rho' t,
  (forall x, In x (atoms_tm t) -> rho x = rho' x) ->
  tm_rho_inst rho t = tm_rho_inst rho' t.
Proof.
  intros rho rho' t.
  induction t as [bn | fa | Ta ba IHba | a1 IHa1 a2 IHa2 | tb IHtb | tb2 IHtb2 Ta2 | c1 IHc1 c2 IHc2]; intros H; simpl.
  - reflexivity.
  - apply H. simpl. auto.
  - assert (E1 : tm_rho_inst rho ba = tm_rho_inst rho' ba).
    { apply IHba. intros x HX. apply H. simpl. apply in_app_iff. auto. }
    rewrite E1. reflexivity.
  - assert (E1 : tm_rho_inst rho a1 = tm_rho_inst rho' a1).
    { apply IHa1. intros x HX. apply H. simpl. apply in_app_iff. auto. }
    assert (E2 : tm_rho_inst rho a2 = tm_rho_inst rho' a2).
    { apply IHa2. intros x HX. apply H. simpl. apply in_app_iff. auto. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : tm_rho_inst rho tb = tm_rho_inst rho' tb).
    { apply IHtb. intros x HX. apply H. simpl. auto. }
    rewrite E1. reflexivity.
  - assert (E1 : tm_rho_inst rho tb2 = tm_rho_inst rho' tb2).
    { apply IHtb2. intros x HX. apply H. simpl. apply in_app_iff. auto. }
    rewrite E1. reflexivity.
  - assert (E1 : tm_rho_inst rho c1 = tm_rho_inst rho' c1).
    { apply IHc1. intros x HX. apply H. simpl. apply in_app_iff. auto. }
    assert (E2 : tm_rho_inst rho c2 = tm_rho_inst rho' c2).
    { apply IHc2. intros x HX. apply H. simpl. apply in_app_iff. auto. }
    rewrite E1, E2. reflexivity.
Qed.

Lemma ty_inst_id_f : forall T, ty_inst (fun X => Ty_FVar X) T = T.
Proof. apply ty_inst_id. Qed.

(* ================================================================== *)
(* Part 5: the type-indexed logical relation                           *)
(* ================================================================== *)

Fixpoint V (E : list sem_ty) (sigma : atom -> sem_ty) (T : ty) (t : tm) {struct T} : Prop :=
  match T with
  | Ty_BVar i => sty_rel (nth_sem E i) t
  | Ty_FVar X => sty_rel (sigma X) t
  | Ty_Arrow T1 T2 =>
      value t /\
      forall u, V E sigma T1 u ->
        locally_closed_tm (tm_app t u) /\ (exists v, tm_app t u -->* v /\ V E sigma T2 v)
  | Ty_All T1 =>
      value t /\
      forall (U : ty) (Hlc : locally_closed_ty U) (R : tm -> Prop)
             (HR : forall w, R w -> value w),
        locally_closed_tm (tm_tapp t U) /\
        (exists v, tm_tapp t U -->* v /\ V (mk_sem U Hlc R HR :: E) sigma T1 v)
  end.

Definition C (E : list sem_ty) (sigma : atom -> sem_ty) (T : ty) (t : tm) : Prop :=
  locally_closed_tm t /\ (exists v, t -->* v /\ V E sigma T v).

Lemma V_value : forall E sigma T t, V E sigma T t -> value t.
Proof.
  intros E sigma T. induction T; intros t H; simpl in H.
  - eapply sty_rel_value; exact H.
  - eapply sty_rel_value; exact H.
  - destruct H as [Hv _]; exact Hv.
  - destruct H as [Hv _]; exact Hv.
Qed.

Lemma V_lc : forall E sigma T t, V E sigma T t -> locally_closed_tm t.
Proof. intros E sigma T t H. apply value_lc. exact (V_value E sigma T t H). Qed.

Lemma C_lc : forall E sigma T t, C E sigma T t -> locally_closed_tm t.
Proof. intros E sigma T t H; unfold C in H; tauto. Qed.

Lemma C_red : forall E sigma T t, C E sigma T t -> exists v, t -->* v /\ V E sigma T v.
Proof. intros E sigma T t H; unfold C in H; tauto. Qed.

Lemma C_intro : forall E sigma T t v,
  locally_closed_tm t -> t -->* v -> V E sigma T v -> C E sigma T t.
Proof. intros E sigma T t v Hlc Hm HV. unfold C. split; auto. exists v; auto. Qed.

Lemma C_value : forall E sigma T v, V E sigma T v -> C E sigma T v.
Proof.
  intros E sigma T v HV. unfold C. split.
  - exact (value_lc v (V_value E sigma T v HV)).
  - exists v. split; [apply multi_refl | auto].
Qed.

Lemma V_arrow : forall E sigma T1 T2 t,
  V E sigma (Ty_Arrow T1 T2) t ->
  forall u, V E sigma T1 u -> C E sigma T2 (tm_app t u).
Proof. intros E sigma T1 T2 t [Hv H] u Hu. unfold C. auto. Qed.

Lemma V_all : forall E sigma T t,
  V E sigma (Ty_All T) t ->
  forall U Hlc R HR, C (mk_sem U Hlc R HR :: E) sigma T (tm_tapp t U).
Proof. intros E sigma T t [Hv H] U Hlc R HR. unfold C. auto. Qed.

Lemma C_congr : forall E E' sigma sigma' T T' t,
  (forall v, V E sigma T v <-> V E' sigma' T' v) ->
  (C E sigma T t <-> C E' sigma' T' t).
Proof.
  intros E E' sigma sigma' T T' t H. unfold C.
  split; intros [Hlc [v [Hm HV]]]; split; auto; exists v; split; auto.
  - apply (proj1 (H v)); auto.
  - apply (proj2 (H v)); auto.
Qed.

(* --- multi-step lemmas --- *)

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H. induction H; intros H2; auto.
  apply multi_step with y; auto.
Qed.

Lemma C_multi : forall E sigma T t t',
  t -->* t' -> C E sigma T t' -> locally_closed_tm t -> C E sigma T t.
Proof.
  intros E sigma T t t' Hm HC Hlc. unfold C in *.
  destruct HC as [Hlc' [v [Hv HV]]]. split; auto.
  exists v. split; auto. eapply multi_trans; eauto.
Qed.

Lemma C_step : forall E sigma T t t',
  step t t' -> C E sigma T t' -> locally_closed_tm t -> C E sigma T t.
Proof.
  intros E sigma T t t' Hs HC Hlc.
  eapply C_multi.
  - apply multi_step with t'; [exact Hs | apply multi_refl].
  - exact HC.
  - exact Hlc.
Qed.

Lemma multi_app1 : forall t t' u, t -->* t' -> locally_closed_tm u -> tm_app t u -->* tm_app t' u.
Proof.
  intros t t' u H. induction H; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (tm_app y u); [apply ST_App1; auto | apply IHmulti; auto].
Qed.

Lemma multi_app2 : forall v t t', value v -> t -->* t' -> tm_app v t -->* tm_app v t'.
Proof.
  intros v t t' Hv H. induction H.
  - apply multi_refl.
  - apply multi_step with (tm_app v y); [apply ST_App2; auto | apply IHmulti].
Qed.

Lemma multi_tapp : forall t t' U, t -->* t' -> locally_closed_ty U -> tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H. induction H; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (tm_tapp y U); [apply ST_TApp; auto | apply IHmulti; auto].
Qed.

Lemma multi_choice_l : forall t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 -> tm_choice t1 t2 -->* t1.
Proof.
  intros. apply multi_step with t1; [apply ST_ChoiceLeft; auto | apply multi_refl].
Qed.

Lemma lc_tm_choice_inv : forall K k t1 t2,
  lc_tm_at K k (tm_choice t1 t2) -> lc_tm_at K k t1 /\ lc_tm_at K k t2.
Proof. intros K k t1 t2 H; inversion H; auto. Qed.

Lemma lc_tm_app_inv : forall K k t1 t2,
  lc_tm_at K k (tm_app t1 t2) -> lc_tm_at K k t1 /\ lc_tm_at K k t2.
Proof. intros K k t1 t2 H; inversion H; auto. Qed.

Lemma lc_tm_abs_inv : forall K k T t,
  lc_tm_at K k (tm_abs T t) -> lc_ty_at K T /\ lc_tm_at K (S k) t.
Proof. intros K k T t H; inversion H; auto. Qed.

Lemma lc_tm_tabs_inv : forall K k t,
  lc_tm_at K k (tm_tabs t) -> lc_tm_at (S K) k t.
Proof. intros K k t H; inversion H; auto. Qed.

Lemma lc_tm_tapp_inv : forall K k t T,
  lc_tm_at K k (tm_tapp t T) -> lc_tm_at K k t /\ lc_ty_at K T.
Proof. intros K k t T H; inversion H; auto. Qed.

Lemma lc_tm_abs_intro : forall K k T t,
  lc_ty_at K T -> lc_tm_at K (S k) t -> lc_tm_at K k (tm_abs T t).
Proof. intros; apply lc_tm_abs; auto. Qed.

Lemma step_lc : forall t t', step t t' -> locally_closed_tm t -> locally_closed_tm t'.
Proof.
  intros t t' H. induction H; intros Hlc.
  - (* ST_AppAbs *)
    apply lc_tm_app_inv in Hlc. destruct Hlc as [Hlc1 Hlc2].
    apply lc_tm_abs_inv in Hlc1. destruct Hlc1 as [HlcT Hlct].
    eapply lc_tm_open_fwd.
    + exact Hlct.
    + intros m. apply lc_tm_at_mono with (K := 0) (n := 0); [lia | lia | apply value_lc; assumption].
  - (* ST_App1 *)
    apply lc_tm_app_inv in Hlc. destruct Hlc as [Hlc1 Hlc2].
    apply lc_tm_app; [apply IHstep; exact Hlc1 | exact Hlc2].
  - (* ST_App2 *)
    apply lc_tm_app_inv in Hlc. destruct Hlc as [Hlc1 Hlc2].
    apply lc_tm_app; [exact Hlc1 | apply IHstep; exact Hlc2].
  - (* ST_TAppTabs *)
    apply lc_tm_tapp_inv in Hlc. destruct Hlc as [Hlc1 HlcT].
    apply lc_tm_tabs_inv in Hlc1.
    eapply lc_tm_open_ty_fwd.
    + exact Hlc1.
    + intros m. eapply lc_ty_at_mono; [| exact HlcT]. lia.
  - (* ST_TApp *)
    apply lc_tm_tapp_inv in Hlc. destruct Hlc as [Hlc1 HlcT].
    apply lc_tm_tapp; [apply IHstep; exact Hlc1 | exact HlcT].
  - (* ST_ChoiceLeft *)
    apply lc_tm_choice_inv in Hlc; tauto.
  - (* ST_ChoiceRight *)
    apply lc_tm_choice_inv in Hlc; tauto.
Qed.

Lemma multi_lc : forall t t', t -->* t' -> locally_closed_tm t -> locally_closed_tm t'.
Proof.
  intros t t' H. induction H; intros Hlc; auto.
  apply IHmulti. apply step_lc with (t := x); auto.
Qed.

(* ================================================================== *)
(* Part 6: environment lemmas for the logical relation                 *)
(* ================================================================== *)

Lemma nth_sem_app_l : forall E E' i, i < length E -> nth_sem (E ++ E') i = nth_sem E i.
Proof.
  intros E E' i Hi. unfold nth_sem. rewrite nth_error_app1; auto.
Qed.

Lemma nth_sem_app_len : forall E s, nth_sem (E ++ [s]) (length E) = s.
Proof.
  intros E s. unfold nth_sem. rewrite nth_error_app2 by lia.
  replace (length E - length E) with 0 by lia. simpl. auto.
Qed.

Lemma nth_sem_cons_0 : forall s E, nth_sem (s :: E) 0 = s.
Proof. auto. Qed.

Lemma nth_sem_cons_S : forall s E i, nth_sem (s :: E) (S i) = nth_sem E i.
Proof. auto. Qed.

Lemma V_prefix : forall T K, lc_ty_at K T ->
  forall pre, length pre = K ->
  forall A B sigma t, V (pre ++ A) sigma T t <-> V (pre ++ B) sigma T t.
Proof.
  induction T; intros K HK pre Hlen A B sigma t; simpl.
  - (* BVar *)
    inversion HK; subst.
    rewrite nth_sem_app_l with (E' := A) by lia.
    rewrite nth_sem_app_l with (E' := B) by lia.
    reflexivity.
  - (* FVar *) reflexivity.
  - (* Arrow *)
    assert (HK1 : lc_ty_at K T1) by (inversion HK; assumption).
    assert (HK2 : lc_ty_at K T2) by (inversion HK; assumption).
    split; intros [Hv H]; split; auto; intros u Hu.
    + apply (proj1 (C_congr _ _ _ _ _ _ _ (fun v => IHT2 K HK2 pre Hlen A B sigma v))).
      apply H. apply (proj2 (IHT1 K HK1 pre Hlen A B sigma u)); auto.
    + apply (proj2 (C_congr _ _ _ _ _ _ _ (fun v => IHT2 K HK2 pre Hlen A B sigma v))).
      apply H. apply (proj1 (IHT1 K HK1 pre Hlen A B sigma u)); auto.
  - (* All *)
    split; intros [Hv H]; split; auto; intros U Hlc R HR.
    + assert (HK' : lc_ty_at (S K) T) by (inversion HK; assumption).
      assert (Hlen' : length (mk_sem U Hlc R HR :: pre) = S K) by (simpl; lia).
      apply (proj1 (C_congr _ _ _ _ _ _ _
        (fun v => IHT (S K) HK' (mk_sem U Hlc R HR :: pre) Hlen' A B sigma v))).
      apply H.
    + assert (HK' : lc_ty_at (S K) T) by (inversion HK; assumption).
      assert (Hlen' : length (mk_sem U Hlc R HR :: pre) = S K) by (simpl; lia).
      apply (proj2 (C_congr _ _ _ _ _ _ _
        (fun v => IHT (S K) HK' (mk_sem U Hlc R HR :: pre) Hlen' A B sigma v))).
      apply H.
Qed.

Lemma V_env_indep : forall U, locally_closed_ty U ->
  forall E E' sigma t, V E sigma U t <-> V E' sigma U t.
Proof.
  intros U Hlc E E' sigma t.
  apply V_prefix with (K := 0) (pre := []).
  - exact Hlc.
  - simpl. reflexivity.
Qed.

Lemma V_sigma_agree : forall T sigma sigma',
  (forall X, In X (atoms_ty T) -> sigma X = sigma' X) ->
  forall E t, V E sigma T t <-> V E sigma' T t.
Proof.
  induction T; intros sigma sigma' Hag E t; simpl.
  - reflexivity.
  - assert (Heq : sigma a = sigma' a) by (apply Hag; simpl; auto).
    rewrite Heq. reflexivity.
  - split; intros [Hv H]; split; auto; intros u Hu.
    + apply (proj1 (C_congr _ _ _ _ _ _ _
        (fun v => IHT2 sigma sigma' (fun X HX => Hag X (in_app_r _ _ _ _ HX)) E v))).
      apply H. apply (proj2 (IHT1 sigma sigma' (fun X HX => Hag X (in_app_l _ _ _ _ HX)) E u)); auto.
    + apply (proj2 (C_congr _ _ _ _ _ _ _
        (fun v => IHT2 sigma sigma' (fun X HX => Hag X (in_app_r _ _ _ _ HX)) E v))).
      apply H. apply (proj1 (IHT1 sigma sigma' (fun X HX => Hag X (in_app_l _ _ _ _ HX)) E u)); auto.
  - split; intros [Hv H]; split; auto; intros U Hlc R HR.
    + apply (proj1 (C_congr _ _ _ _ _ _ _
        (fun v => IHT sigma sigma' Hag (mk_sem U Hlc R HR :: E) v))). apply H.
    + apply (proj2 (C_congr _ _ _ _ _ _ _
        (fun v => IHT sigma sigma' Hag (mk_sem U Hlc R HR :: E) v))). apply H.
Qed.

Lemma V_open_general : forall (sigma : atom -> sem_ty) k (T V0 : ty) (s : sem_ty),
  lc_ty_at (S k) T ->
  (forall (E' : list sem_ty) t, V E' sigma V0 t <-> sty_rel s t) ->
  forall E, length E = k ->
  forall t, V E sigma (open_ty_rec k V0 T) t <-> V (E ++ [s]) sigma T t.
Proof.
  intros sigma k T. revert k. induction T; intros k V0 s Hlc Hag E Hlen t; simpl.
  - (* BVar *)
    destruct (Nat.eqb k n) eqn:E1.
    + apply Nat.eqb_eq in E1. subst n.
      rewrite <- Hlen. simpl. rewrite nth_sem_app_len.
      split; intros H.
      * apply (proj1 (Hag E t)); exact H.
      * apply (proj2 (Hag E t)); exact H.
    + apply Nat.eqb_neq in E1.
      assert (Hnk : n < length E) by (inversion Hlc; subst; lia).
      simpl. rewrite (nth_sem_app_l E [s] n Hnk).
      reflexivity.
  - (* FVar *) reflexivity.
  - (* Arrow *)
    assert (Hlc1 : lc_ty_at (S k) T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at (S k) T2) by (inversion Hlc; assumption).
    split; intros [Hv H]; split; auto; intros u Hu.
    + apply (proj1 (C_congr _ _ _ _ _ _ _ (fun v => IHT2 k V0 s Hlc2 Hag E Hlen v))).
      apply H. apply (proj2 (IHT1 k V0 s Hlc1 Hag E Hlen u)); auto.
    + apply (proj2 (C_congr _ _ _ _ _ _ _ (fun v => IHT2 k V0 s Hlc2 Hag E Hlen v))).
      apply H. apply (proj1 (IHT1 k V0 s Hlc1 Hag E Hlen u)); auto.
  - (* All *)
    assert (Hlc' : lc_ty_at (S (S k)) T) by (inversion Hlc; assumption).
    split; intros [Hv H]; split; auto; intros U HlcU R HR.
    + assert (Hlen' : length (mk_sem U HlcU R HR :: E) = S k) by (simpl; lia).
      apply (proj1 (C_congr _ _ _ _ _ _ _
        (fun v => IHT (S k) V0 s Hlc' Hag (mk_sem U HlcU R HR :: E) Hlen' v))).
      apply H.
    + assert (Hlen' : length (mk_sem U HlcU R HR :: E) = S k) by (simpl; lia).
      apply (proj2 (C_congr _ _ _ _ _ _ _
        (fun v => IHT (S k) V0 s Hlc' Hag (mk_sem U HlcU R HR :: E) Hlen' v))).
      apply H.
Qed.

Lemma C_open_general : forall (sigma : atom -> sem_ty) k (T V0 : ty) (s : sem_ty),
  lc_ty_at (S k) T ->
  (forall (E' : list sem_ty) t, V E' sigma V0 t <-> sty_rel s t) ->
  forall E, length E = k ->
  forall t, C E sigma (open_ty_rec k V0 T) t <-> C (E ++ [s]) sigma T t.
Proof.
  intros sigma k T V0 s Hlc Hag E Hlen t.
  apply C_congr. intros v. eapply V_open_general; eauto.
Qed.

(* ================================================================== *)
(* Part 7a: closedness under instantiation, free term variables        *)
(* ================================================================== *)

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => fv_tm b
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs b => fv_tm b
  | tm_tapp b _ => fv_tm b
  | tm_choice t1 t2 => fv_tm t1 ++ fv_tm t2
  end.

Lemma fv_tm_tm_ty_inst : forall s t, fv_tm (tm_ty_inst s t) = fv_tm t.
Proof.
  intros s t.
  induction t as [bn | fa | Ta ba IHba | a1 IHa1 a2 IHa2 | tb IHtb | tb2 IHtb2 Ta2 | c1 IHc1 c2 IHc2];
    simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHba. reflexivity.
  - rewrite IHa1, IHa2. reflexivity.
  - rewrite IHtb. reflexivity.
  - rewrite IHtb2. reflexivity.
  - rewrite IHc1, IHc2. reflexivity.
Qed.

Lemma fv_tm_atoms : forall t x, In x (fv_tm t) -> In x (atoms_tm t).
Proof.
  induction t as [bn | fa | Ta ba IHba | a1 IHa1 a2 IHa2 | tb IHtb | tb2 IHtb2 Ta2 | c1 IHc1 c2 IHc2];
    intros x H; simpl in *.
  - destruct H.
  - auto.
  - apply in_app_iff. right. apply IHba; auto.
  - apply in_app_iff in H. apply in_app_iff. destruct H as [H|H]; [left | right]; auto.
  - apply IHtb; auto.
  - apply in_app_iff. left. apply IHtb2; auto.
  - apply in_app_iff in H. apply in_app_iff. destruct H as [H|H]; [left | right]; auto.
Qed.

Lemma tm_rho_inst_ext_fv : forall rho rho' t,
  (forall x, In x (fv_tm t) -> rho x = rho' x) ->
  tm_rho_inst rho t = tm_rho_inst rho' t.
Proof.
  intros rho rho' t.
  induction t as [bn | fa | Ta ba IHba | a1 IHa1 a2 IHa2 | tb IHtb | tb2 IHtb2 Ta2 | c1 IHc1 c2 IHc2];
    intros H; simpl.
  - reflexivity.
  - apply H. simpl. auto.
  - assert (E1 : tm_rho_inst rho ba = tm_rho_inst rho' ba).
    { apply IHba. intros x Hx. apply H. simpl. auto. }
    rewrite E1. reflexivity.
  - assert (E1 : tm_rho_inst rho a1 = tm_rho_inst rho' a1).
    { apply IHa1. intros x Hx. apply H. simpl. apply in_app_iff. auto. }
    assert (E2 : tm_rho_inst rho a2 = tm_rho_inst rho' a2).
    { apply IHa2. intros x Hx. apply H. simpl. apply in_app_iff. auto. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : tm_rho_inst rho tb = tm_rho_inst rho' tb).
    { apply IHtb. intros x Hx. apply H. simpl. auto. }
    rewrite E1. reflexivity.
  - assert (E1 : tm_rho_inst rho tb2 = tm_rho_inst rho' tb2).
    { apply IHtb2. intros x Hx. apply H. simpl. auto. }
    rewrite E1. reflexivity.
  - assert (E1 : tm_rho_inst rho c1 = tm_rho_inst rho' c1).
    { apply IHc1. intros x Hx. apply H. simpl. apply in_app_iff. auto. }
    assert (E2 : tm_rho_inst rho c2 = tm_rho_inst rho' c2).
    { apply IHc2. intros x Hx. apply H. simpl. apply in_app_iff. auto. }
    rewrite E1, E2. reflexivity.
Qed.

Lemma lc_ty_inst : forall T k, lc_ty_at k T ->
  forall s, (forall X, locally_closed_ty (s X)) -> lc_ty_at k (ty_inst s T).
Proof.
  induction T; intros k Hk s Hs; simpl.
  - inversion Hk; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_at_mono with (k := 0); [lia | apply Hs].
  - inversion Hk; subst. apply lc_ty_arrow; auto.
  - inversion Hk; subst. apply lc_ty_all; auto.
Qed.

Lemma lc_tm_ty_inst : forall t K n, lc_tm_at K n t ->
  forall s, (forall X, locally_closed_ty (s X)) -> lc_tm_at K n (tm_ty_inst s t).
Proof.
  induction t as [bn | fa | Ta ba IHba | a1 IHa1 a2 IHa2 | tb IHtb | tb2 IHtb2 Ta2 | c1 IHc1 c2 IHc2];
    intros K N H s Hs; simpl.
  - inversion H; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs_inv in H. destruct H as [HT Hb].
    apply lc_tm_abs.
    + apply lc_ty_inst with (k := K); auto.
    + apply IHba; auto.
  - apply lc_tm_app_inv in H. destruct H as [H1 H2].
    apply lc_tm_app; [apply IHa1 | apply IHa2]; auto.
  - apply lc_tm_tabs_inv in H. apply lc_tm_tabs. apply IHtb; auto.
  - apply lc_tm_tapp_inv in H. destruct H as [H1 H2].
    apply lc_tm_tapp.
    + apply IHtb2; auto.
    + apply lc_ty_inst with (k := K); auto.
  - apply lc_tm_choice_inv in H. destruct H as [H1 H2].
    apply lc_tm_choice; [apply IHc1 | apply IHc2]; auto.
Qed.

Lemma lc_tm_rho_inst : forall t K n, lc_tm_at K n t ->
  forall rho, (forall x, locally_closed_tm (rho x)) -> lc_tm_at K n (tm_rho_inst rho t).
Proof.
  induction t as [bn | fa | Ta ba IHba | a1 IHa1 a2 IHa2 | tb IHtb | tb2 IHtb2 Ta2 | c1 IHc1 c2 IHc2];
    intros K N H rho Hrho; simpl.
  - inversion H; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_at_mono with (K := 0) (n := 0); [lia | lia | apply Hrho].
  - apply lc_tm_abs_inv in H. destruct H as [HT Hb].
    apply lc_tm_abs; [assumption | apply IHba; auto].
  - apply lc_tm_app_inv in H. destruct H as [H1 H2].
    apply lc_tm_app; [apply IHa1 | apply IHa2]; auto.
  - apply lc_tm_tabs_inv in H. apply lc_tm_tabs. apply IHtb; auto.
  - apply lc_tm_tapp_inv in H. destruct H as [H1 H2].
    apply lc_tm_tapp; [apply IHtb2 | assumption]; auto.
  - apply lc_tm_choice_inv in H. destruct H as [H1 H2].
    apply lc_tm_choice; [apply IHc1 | apply IHc2]; auto.
Qed.

Lemma lc_tm_inst : forall sigma rho t K n,
  lc_tm_at K n t ->
  (forall x, locally_closed_tm (rho x)) ->
  lc_tm_at K n (inst sigma rho t).
Proof.
  intros. unfold inst. apply lc_tm_rho_inst; auto.
  apply lc_tm_ty_inst; auto. intros X; apply sty_lc.
Qed.

Definition env_ok (sigma : atom -> sem_ty) (rho : atom -> tm) (Gamma : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value (rho x) /\ V [] sigma T (rho x).

(* ================================================================== *)
(* Part 7b: the fundamental theorem                                    *)
(* ================================================================== *)

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sigma rho,
    (forall x, locally_closed_tm (rho x)) ->
    env_ok sigma rho Gamma ->
    C [] sigma T (inst sigma rho t).
Proof.
  intros Delta Gamma t T Hder.
  induction Hder as
    [ Delta Gamma x T Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHb
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t0 T Hbody IHb
    | Delta Gamma t1 T U H1 IH1 Hwf
    | Delta Gamma t1 t2 T H1 IH1 H2 IH2 ].
  - (* T_Var *)
    intros sigma rho Hrl Henv. simpl.
    destruct (Henv x T Hlook) as [Hv HV]. apply C_value; exact HV.
  - (* T_Abs *)
    intros sigma rho Hrl Henv.
    set (body := inst sigma rho t2).
    set (T1' := ty_inst (sty sigma) T1).
    change (C [] sigma (Ty_Arrow T1 T2) (tm_abs T1' body)).
    assert (HlcT1' : lc_ty_at 0 T1').
    { subst T1'. apply lc_ty_inst with (k := 0).
      - eapply wf_ty_lc; eassumption.
      - intros Z; apply sty_lc. }
    set (x0 := fresh_atom (L ++ atoms_tm t2)).
    assert (Hx0L : ~ In x0 L).
    { intro Hc. apply (fresh_atom_spec (L ++ atoms_tm t2)). apply in_app_iff. auto. }
    assert (Hx0tm : ~ In x0 (atoms_tm t2)).
    { intro Hc. apply (fresh_atom_spec (L ++ atoms_tm t2)). apply in_app_iff. auto. }
    assert (Hlc2b : lc_tm_at 0 1 t2).
    { pose proof (has_type_lc _ _ _ _ (Hbody x0 Hx0L)) as Hlcopen.
      eapply lc_tm_open_inv with (K := 0) (n := 0) (u := tm_fvar x0).
      - intros; apply lc_tm_fvar.
      - exact Hlcopen. }
    assert (Hlcb : lc_tm_at 0 1 body).
    { subst body. apply lc_tm_inst; auto. }
    assert (Hlcabs : locally_closed_tm (tm_abs T1' body)).
    { apply lc_tm_abs; auto. }
    assert (Hval : value (tm_abs T1' body)).
    { apply v_abs; exact Hlcabs. }
    assert (HVarrow : V [] sigma (Ty_Arrow T1 T2) (tm_abs T1' body)).
    { simpl. split; [exact Hval |].
      intros u Hu.
      assert (Hvu : value u) by (apply V_value in Hu; exact Hu).
      assert (Hlcu : locally_closed_tm u) by (apply value_lc; exact Hvu).
      split.
      - apply lc_tm_app; [exact Hlcabs | exact Hlcu].
      - set (rho' := upd_rho rho x0 u).
        assert (Hrl' : forall y, locally_closed_tm (rho' y)).
        { intro y. unfold rho', upd_rho. simpl.
          destruct (Nat.eqb y x0) eqn:E.
          - apply Hlcu.
          - apply Hrl. }
        assert (Henv' : env_ok sigma rho' (update Gamma x0 T1)).
        { intros y Ty Hlook. simpl in Hlook.
          destruct (Nat.eqb y x0) eqn:E.
          - apply Nat.eqb_eq in E. subst y. injection Hlook as <-.
            split.
            + unfold rho'. rewrite upd_rho_x. exact Hvu.
            + unfold rho'. rewrite upd_rho_x. exact Hu.
          - apply Nat.eqb_neq in E.
            destruct (Henv y Ty Hlook) as [Hvy HVy].
            assert (Hry : rho' y = rho y) by (unfold rho'; rewrite upd_rho_other; auto).
            split.
            + rewrite Hry. exact Hvy.
            + rewrite Hry. exact HVy. }
        pose proof (IHb x0 Hx0L sigma rho' Hrl' Henv') as HC0.
        assert (Hinst : inst sigma rho' (open_tm t2 (tm_fvar x0)) = open_tm body u).
        { rewrite inst_open_tm; [| exact Hrl'].
          assert (Hrho'x : inst sigma rho' (tm_fvar x0) = u).
          { change (rho' x0 = u). unfold rho'. apply upd_rho_x. }
          assert (Hbody' : inst sigma rho' t2 = body).
          { subst body. unfold inst.
            apply tm_rho_inst_ext_fv. intros y Hy.
            unfold rho', upd_rho. simpl. destruct (Nat.eqb y x0) eqn:E; auto.
            apply Nat.eqb_eq in E. subst y. exfalso. apply Hx0tm.
            rewrite fv_tm_tm_ty_inst in Hy. apply fv_tm_atoms in Hy. exact Hy. }
          rewrite Hrho'x, Hbody'. reflexivity. }
        rewrite Hinst in HC0.
        eapply C_multi with (t' := open_tm body u).
        + apply multi_step with (open_tm body u); [apply ST_AppAbs; auto | apply multi_refl].
        + exact HC0.
        + apply lc_tm_app; [exact Hlcabs | exact Hlcu]. }
    unfold C. split.
    + exact Hlcabs.
    + exists (tm_abs T1' body). split; [apply multi_refl | exact HVarrow].
  - (* T_App *)
    intros sigma rho Hrl Henv.
    change (C [] sigma T2 (tm_app (inst sigma rho t1) (inst sigma rho t2))).
    pose proof (IH1 sigma rho Hrl Henv) as HC1.
    pose proof (IH2 sigma rho Hrl Henv) as HC2.
    destruct HC1 as [Hlc1 [v1 [Hm1 HV1]]].
    destruct HC2 as [Hlc2 [v2 [Hm2 HV2]]].
    assert (Hv1 : value v1) by (apply V_value in HV1; exact HV1).
    assert (Hv2 : value v2) by (apply V_value in HV2; exact HV2).
    destruct (V_arrow _ _ _ _ _ HV1 v2 HV2) as [Hlcapp [w [Hmw HVw]]].
    eapply C_multi with (t' := tm_app v1 v2).
    + apply multi_trans with (b := tm_app v1 (inst sigma rho t2)).
      * apply multi_app1; auto.
      * apply multi_app2; auto.
    + apply C_intro with (v := w); [exact Hlcapp | exact Hmw | exact HVw].
    + apply lc_tm_app; auto.
  - (* T_TAbs *)
    intros sigma rho Hrl Henv.
    set (body := inst sigma rho t0).
    change (C [] sigma (Ty_All T) (tm_tabs body)).
    set (X0 := fresh_atom (L ++ atoms_ty T ++ atoms_tm t0 ++ atoms_context Gamma)).
    assert (HXall : ~ In X0 (L ++ atoms_ty T ++ atoms_tm t0 ++ atoms_context Gamma))
      by apply fresh_atom_spec.
    assert (HX0L : ~ In X0 L).
    { intro Hc. apply HXall. apply in_app_iff. left. exact Hc. }
    assert (HX0T : ~ In X0 (atoms_ty T)).
    { intro Hc. apply HXall. apply in_app_iff. right. apply in_app_iff. left. exact Hc. }
    assert (HX0tm : ~ In X0 (atoms_tm t0)).
    { intro Hc. apply HXall. apply in_app_iff. right. apply in_app_iff. right.
      apply in_app_iff. left. exact Hc. }
    assert (HX0ctx : ~ In X0 (atoms_context Gamma)).
    { intro Hc. apply HXall. apply in_app_iff. right. apply in_app_iff. right.
      apply in_app_iff. right. exact Hc. }
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (has_type_lc_ty _ _ _ _ (Hbody X0 HX0L)) as Hlcopen.
      eapply lc_ty_open_inv with (k := 0) (U := Ty_FVar X0).
      - intros; apply lc_ty_fvar.
      - exact Hlcopen. }
    assert (Hlcb : lc_tm_at 1 0 body).
    { subst body.
      pose proof (has_type_lc _ _ _ _ (Hbody X0 HX0L)) as Hlcopen.
      assert (Ht0 : lc_tm_at 1 0 t0).
      { eapply lc_tm_open_ty_inv with (K := 0) (n := 0) (U := Ty_FVar X0).
        - intros; apply lc_ty_fvar.
        - exact Hlcopen. }
      apply lc_tm_inst; auto. }
    assert (Hval : value (tm_tabs body)) by (apply v_tabs, lc_tm_tabs; exact Hlcb).
    assert (HVall : V [] sigma (Ty_All T) (tm_tabs body)).
    { simpl. split; [exact Hval |].
      intros U HlcU R HR.
      split.
      - (* lc of tm_tapp *) apply lc_tm_tapp; [apply value_lc; exact Hval | exact HlcU].
      - set (s := mk_sem U HlcU R HR).
        set (sigmaX := upd_sem sigma X0 s).
        assert (Hsy : sty_ty (sigmaX X0) = U).
        { unfold sigmaX. rewrite upd_sem_X. reflexivity. }
        assert (HenvX : env_ok sigmaX rho Gamma).
        { intros y Ty Hlook.
          destruct (Henv y Ty Hlook) as [Hvy HVy]. split; auto.
          assert (HXnotTy : ~ In X0 (atoms_ty Ty)).
          { intro Hc. apply HX0ctx. apply atoms_context_in with (x := y) (T := Ty); auto.
            apply lookup_context_In; auto. }
          assert (Hag : forall Z, In Z (atoms_ty Ty) -> sigmaX Z = sigma Z).
          { intros Z HZ. unfold sigmaX. apply upd_sem_other.
            intro Heq. subst Z. apply HXnotTy; auto. }
          apply (proj2 (V_sigma_agree Ty sigmaX sigma Hag [] (rho y))). exact HVy. }
        pose proof (IHb X0 HX0L sigmaX rho Hrl HenvX) as HC0.
        assert (Hinst : inst sigmaX rho (open_tm_ty t0 (Ty_FVar X0)) = open_tm_ty body U).
        { rewrite inst_open_tm_ty; [| exact Hrl].
          assert (Htm : tm_ty_inst (sty sigmaX) t0 = tm_ty_inst (sty sigma) t0).
          { apply tm_ty_inst_ext. intros Z HZ. unfold sty, sigmaX.
            rewrite upd_sem_other.
            - reflexivity.
            - intro Heq. subst Z. apply HX0tm; auto. }
          assert (Hsty : ty_inst (sty sigmaX) (Ty_FVar X0) = U).
          { simpl. unfold sty, sigmaX. rewrite upd_sem_X. reflexivity. }
          subst body. unfold inst. rewrite Htm, Hsty. reflexivity. }
        rewrite Hinst in HC0.
        assert (Hagf : forall (E' : list sem_ty) t,
          V E' sigmaX (Ty_FVar X0) t <-> sty_rel s t).
        { intros E' t. simpl. unfold sigmaX, s. rewrite upd_sem_X. reflexivity. }
        assert (HC1 : C [s] sigmaX T (open_tm_ty body U)).
        { eapply (proj1 (C_open_general sigmaX 0 T (Ty_FVar X0) s HlcT Hagf [] (eq_refl 0) (open_tm_ty body U))).
          exact HC0. }
        assert (HagT : forall Z, In Z (atoms_ty T) -> sigmaX Z = sigma Z).
        { intros Z HZ. unfold sigmaX. apply upd_sem_other.
          intro Heq. subst Z. apply HX0T; auto. }
        assert (HC2 : C [s] sigma T (open_tm_ty body U)).
        { apply (proj1 (C_congr [s] [s] sigmaX sigma T T (open_tm_ty body U)
            (fun v => V_sigma_agree T sigmaX sigma HagT [s] v))).
          exact HC1. }
        destruct HC2 as [Hlcx [w [Hmw HVw]]].
        exists w. split.
        + eapply multi_trans.
          * apply multi_step with (y := open_tm_ty body U).
            -- apply ST_TAppTabs.
               ++ apply lc_tm_tabs; exact Hlcb.
               ++ exact HlcU.
            -- apply multi_refl.
          * exact Hmw.
        + exact HVw. }
    unfold C. split.
    + apply lc_tm_tabs; exact Hlcb.
    + exists (tm_tabs body). split; [apply multi_refl | exact HVall].
  - (* T_TApp *)
    intros sigma rho Hrl Henv.
    set (U' := ty_inst (sty sigma) U).
    change (C [] sigma (open_ty T U) (tm_tapp (inst sigma rho t1) U')).
    pose proof (IH1 sigma rho Hrl Henv) as HC1.
    destruct HC1 as [Hlc1 [v1 [Hm1 HV1]]].
    assert (HlcU' : locally_closed_ty U').
    { subst U'. apply lc_ty_inst with (k := 0).
      - eapply wf_ty_lc; eassumption.
      - intros Z; apply sty_lc. }
    set (R := V [] sigma U).
    assert (HR : forall w, R w -> value w).
    { intros w Hw. apply V_value in Hw. exact Hw. }
    set (s := mk_sem U' HlcU' R HR).
    pose proof (V_all _ _ _ _ HV1 U' HlcU' R HR) as HC2.
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (has_type_lc_ty _ _ _ _ H1) as HT. inversion HT; subst; assumption. }
    assert (Hag : forall (E' : list sem_ty) t, V E' sigma U t <-> sty_rel s t).
    { intros E' t. unfold s. rewrite mk_sem_rel. unfold R.
      symmetry. apply V_env_indep. eapply wf_ty_lc; eassumption. }
    assert (HC3 : C [] sigma (open_ty T U) (tm_tapp v1 U')).
    { eapply (proj2 (C_open_general sigma 0 T U s HlcT Hag [] (eq_refl 0) (tm_tapp v1 U'))).
      exact HC2. }
    eapply C_multi with (t' := tm_tapp v1 U').
    + apply multi_tapp; auto.
    + exact HC3.
    + apply lc_tm_tapp; auto.
  - (* T_Choice *)
    intros sigma rho Hrl Henv.
    change (C [] sigma T (tm_choice (inst sigma rho t1) (inst sigma rho t2))).
    pose proof (IH1 sigma rho Hrl Henv) as HC1.
    pose proof (IH2 sigma rho Hrl Henv) as HC2.
    destruct HC1 as [Hlc1 [v1 [Hm1 HV1]]].
    destruct HC2 as [Hlc2 _].
    assert (Hstep : tm_choice (inst sigma rho t1) (inst sigma rho t2) --> inst sigma rho t1).
    { apply ST_ChoiceLeft; auto. }
    eapply C_multi with (t' := v1).
    + apply multi_step with (y := inst sigma rho t1).
      * exact Hstep.
      * exact Hm1.
    + apply C_value; exact HV1.
    + apply lc_tm_choice; auto.
Qed.

(* ================================================================== *)
(* Part 8: the target theorem                                          *)
(* ================================================================== *)

Lemma inst_identity : forall sigma rho,
  (forall X, sty_ty (sigma X) = Ty_FVar X) ->
  (forall x, rho x = tm_fvar x) ->
  forall t, inst sigma rho t = t.
Proof.
  intros sigma rho Hs Hr t.
  change (tm_rho_inst rho (tm_ty_inst (fun X => sty_ty (sigma X)) t) = t).
  rewrite (tm_ty_inst_id_gen (fun X => sty_ty (sigma X)) Hs t).
  apply tm_rho_inst_id_gen. intros x. apply Hr.
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
  intros t Ht U v Hwf Hv Hvhv.
  set (sigma0 := fun X => mk_sem (Ty_FVar X) (lc_ty_fvar 0 X) (fun _ => False) (fun w H => False_ind (value w) H)).
  set (rho0 := fun x => tm_fvar x).
  assert (Hrho0 : forall x, locally_closed_tm (rho0 x)).
  { intro x. unfold rho0. apply lc_tm_fvar. }
  assert (Henv0 : env_ok sigma0 rho0 empty).
  { intros x Ty Hlook. simpl in Hlook. discriminate. }
  pose proof (fundamental [] empty t (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht sigma0 rho0 Hrho0 Henv0) as HC.
  assert (Hinst : inst sigma0 rho0 t = t).
  { apply inst_identity.
    - intro X. unfold sigma0. reflexivity.
    - intro x. unfold rho0. reflexivity. }
  rewrite Hinst in HC.
  unfold C in HC. destruct HC as [Hlct [v0 [Hm0 HV0]]].
  simpl in HV0. destruct HV0 as [Hv0val HV0].
  set (R := fun w : tm => w = v).
  assert (HR : forall w, R w -> value w).
  { intros w Hw. unfold R in Hw. subst w. exact Hv. }
  pose proof (HV0 U (wf_ty_lc [] U Hwf) R HR) as HC1.
  unfold C in HC1. destruct HC1 as [Hlc1 [v1 [Hm1 HV1]]].
  simpl in HV1. destruct HV1 as [Hv1val HV1'].
  assert (Hvv : V [mk_sem U (wf_ty_lc [] U Hwf) R HR] sigma0 (Ty_BVar 0) v).
  { simpl. unfold R. reflexivity. }
  pose proof (HV1' v Hvv) as HC2.
  unfold C in HC2. destruct HC2 as [Hlc2 [v2 [Hm2 HV2]]].
  simpl in HV2. unfold R in HV2. subst v2.
  assert (Hm_tapp : tm_tapp t U -->* v1).
  { eapply multi_trans.
    - apply multi_tapp; [exact Hm0 | exact (wf_ty_lc [] U Hwf)].
    - exact Hm1. }
  assert (Hm_app : tm_app (tm_tapp t U) v -->* tm_app v1 v).
  { apply multi_app1; [exact Hm_tapp | apply value_lc; exact Hv]. }
  eapply multi_trans.
  - exact Hm_app.
  - exact Hm2.
Qed.

End SystemFParametricityNondeterminismHardTask.
