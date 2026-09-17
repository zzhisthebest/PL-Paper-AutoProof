(** System F CBV strong-normalization benchmark, Medium variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNondeterminismMediumTask.

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

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

Definition type_substitution := atom -> ty.

Definition term_substitution := atom -> tm.

Fixpoint instantiate_ty (theta : type_substitution) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (instantiate_ty theta T1) (instantiate_ty theta T2)
  | Ty_All T1 => Ty_All (instantiate_ty theta T1)
  end.

Fixpoint instantiate
    (theta : type_substitution) (gamma : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T t1 => tm_abs (instantiate_ty theta T) (instantiate theta gamma t1)
  | tm_app t1 t2 => tm_app (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_tabs t1 => tm_tabs (instantiate theta gamma t1)
  | tm_tapp t1 T => tm_tapp (instantiate theta gamma t1) (instantiate_ty theta T)
  | tm_choice t1 t2 => tm_choice (instantiate theta gamma t1) (instantiate theta gamma t2)
  end.

Definition type_substitution_closed (theta : type_substitution) : Prop :=
  forall X : atom, locally_closed_ty (theta X).

Definition term_substitution_closed (gamma : term_substitution) : Prop :=
  forall x : atom, locally_closed_tm (gamma x).

Definition relation := tm -> Prop.
Record value_candidate := {
  candidate_relation : relation;
  candidate_values : forall v, candidate_relation v -> value v
}.
Definition relation_env := atom -> option value_candidate.
Definition relation_update (rho : relation_env) (X : atom) (a : value_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition expression_lifting (R : relation) (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t /\
  forall v, t -->* v -> value v -> R v.

Fixpoint value_relation (eta : list value_candidate) (rho : relation_env)
    (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v | None => False end
  | Ty_Arrow T1 T2 =>
      value v /\ exists U body, v = tm_abs U body /\
      forall arg, value_relation eta rho T1 arg ->
        expression_lifting (value_relation eta rho T2) (open_tm body arg)
  | Ty_All T =>
      value v /\ exists body, v = tm_tabs body /\
      forall (U : ty) (a : value_candidate), locally_closed_ty U ->
        expression_lifting (value_relation (a :: eta) rho T) (open_tm_ty body U)
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

(* A few finite-support facts are useful when applying the locally nameless
   typing rules.  The particular representation of atoms is immaterial. *)
Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T t1 => fv_ty T ++ fv_tm t1
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t1 => fv_tm t1
  | tm_tapp t1 T => fv_tm t1 ++ fv_ty T
  | tm_choice t1 t2 => fv_tm t1 ++ fv_tm t2
  end.

Fixpoint fv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fv_ty T ++ fv_context Gamma'
  end.

Fixpoint list_max (L : list atom) : atom :=
  match L with
  | [] => 0
  | a :: L' => Nat.max a (list_max L')
  end.

Lemma in_list_max : forall x L, In x L -> x <= list_max L.
Proof.
  intros y L. induction L as [|a L IH]; simpl; intro H.
  - contradiction.
  - destruct H as [->|H].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (list_max L); auto using Nat.le_max_r.
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (list_max L)); intro H.
  pose proof (in_list_max _ _ H); lia.
Qed.

Lemma lc_ty_mono : forall T K K', K <= K' -> lc_ty_at K T -> lc_ty_at K' T.
Proof.
  intros T; induction T as [n|X|T1 IH1 T2 IH2|T IH]; intros K K' HKK' H.
  - inversion H. constructor; lia.
  - constructor.
  - inversion H. constructor; eauto.
  - inversion H. constructor.
    apply IH with (K:=S K) (K':=S K'); [lia|assumption].
Qed.

Lemma lc_ty_weaken : forall K T, locally_closed_ty T -> lc_ty_at K T.
Proof.
  intros K T H. apply lc_ty_mono with (T:=T) (K:=0) (K':=K).
  - lia.
  - exact H.
Qed.

Lemma lc_tm_mono : forall t K K' k k', K <= K' -> k <= k' ->
  lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  intros t; induction t; intros K K' k k' HKK' Hkk' H.
  - inversion H; apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - inversion H; apply lc_tm_abs.
    + apply lc_ty_mono with (T:=t) (K:=K); assumption.
    + apply IHt with (K:=K) (K':=K') (k:=S k) (k':=S k').
      * assumption.
      * lia.
      * assumption.
  - inversion H; apply lc_tm_app.
    + apply IHt1 with (K:=K) (K':=K') (k:=k) (k':=k'); assumption.
    + apply IHt2 with (K:=K) (K':=K') (k:=k) (k':=k'); assumption.
  - inversion H; apply lc_tm_tabs.
    apply IHt with (K:=S K) (K':=S K') (k:=k) (k':=k').
    * lia.
    * assumption.
    * assumption.
  - inversion H; apply lc_tm_tapp.
    all: try lia.
    all: eauto using lc_ty_mono.
  - inversion H; apply lc_tm_choice.
    all: try lia.
    all: eauto.
Qed.

Lemma lc_tm_weaken : forall K k t, locally_closed_tm t -> lc_tm_at K k t.
Proof.
  intros K k t H. apply lc_tm_mono with (t:=t) (K:=0) (K':=K) (k:=0) (k':=k).
  - lia.
  - lia.
  - exact H.
Qed.

Lemma open_ty_rec_lc : forall T K U, lc_ty_at K T ->
  open_ty_rec K U T = T.
Proof.
  intros T; induction T as [i|X|T1 IH1 T2 IH2|T IH]; intros K U H;
    inversion H; subst.
  - simpl. destruct (Nat.eqb K i) eqn:E; simpl; auto.
    apply Nat.eqb_eq in E; lia.
  - reflexivity.
  - simpl. f_equal; eauto.
  - simpl. f_equal. apply IH. assumption.
Qed.

Lemma open_tm_ty_rec_lc : forall K U k t, lc_tm_at K k t ->
  open_tm_ty_rec K U t = t.
Proof.
  intros K U k t H; induction H.
  - reflexivity.
  - reflexivity.
  - simpl; f_equal; auto using open_ty_rec_lc.
  - simpl; f_equal; auto.
  - simpl; f_equal; auto.
  - simpl; f_equal; auto using open_ty_rec_lc.
  - simpl; f_equal; auto.
Qed.

Lemma open_tm_ty_rec_closed : forall k U t, locally_closed_tm t ->
  open_tm_ty_rec k U t = t.
Proof.
  intros k U t H.
  apply open_tm_ty_rec_lc with (K:=k) (U:=U) (k:=0).
  apply lc_tm_weaken with (K:=k); exact H.
Qed.

Lemma open_tm_ty_lc : forall U t, locally_closed_tm t ->
  open_tm_ty t U = t.
Proof.
  intros; unfold open_tm_ty; apply open_tm_ty_rec_lc with (K:=0) (k:=0).
  exact H.
Qed.

Lemma lc_open_ty_rec : forall T K U,
  lc_ty_at (S K) T -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros T; induction T as [i|X|T1 IH1 T2 IH2|T IH];
    intros K U H HU; inversion H; subst.
  - simpl. destruct (Nat.eqb K i) eqn:E.
    + exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E; lia.
  - constructor.
  - simpl; apply lc_ty_arrow; eauto.
  - simpl; apply lc_ty_all.
    apply IH with (K:=S K) (U:=U).
    + assumption.
    + apply lc_ty_mono with (T:=U) (K:=K) (K':=S K); auto; lia.
Qed.

Lemma lc_open_tm_rec : forall t K k u,
  lc_tm_at K (S k) t -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros t; induction t as
    [i|x|T IHt t|t1 IH1 t2 IH2|t IHt|t1 IHt1 T|t1 IHt1 t2 IHt2];
    intros K k u H Hu; inversion H; subst.
  - simpl. destruct (Nat.eqb k i) eqn:E; auto.
    apply lc_tm_bvar. apply Nat.eqb_neq in E; lia.
  - apply lc_tm_fvar.
  - simpl; apply lc_tm_abs.
    + assumption.
    + apply (t K (S k) u).
      * assumption.
      * apply lc_tm_mono with (K:=K) (K':=K) (k:=k) (k':=S k); auto; lia.
  - simpl; apply lc_tm_app; eauto.
  - simpl; apply lc_tm_tabs. apply IHt with (K:=S K) (k:=k) (u:=u).
    + assumption.
    + apply lc_tm_mono with (K:=K) (K':=S K) (k:=k) (k':=k); auto; lia.
  - simpl; apply lc_tm_tapp; eauto.
  - simpl; apply lc_tm_choice; eauto.
Qed.

Lemma lc_open_tm : forall t u, locally_closed_tm (tm_abs (Ty_FVar 0) t) ->
  locally_closed_tm u -> locally_closed_tm (open_tm t u).
Proof.
  intros t u Ht Hu. unfold locally_closed_tm in *; unfold open_tm.
  apply lc_open_tm_rec with (K:=0) (k:=0); auto.
  inversion Ht; assumption.
Qed.

Lemma lc_open_tm_ty_rec : forall t K k U,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros t; induction t as
    [i|x|T IHt t|t1 IH1 t2 IH2|t IHt|t1 IHt1 T|t1 IHt1 t2 IHt2];
    intros K k U H HU; inversion H; subst.
  - apply lc_tm_bvar; assumption.
  - apply lc_tm_fvar.
  - simpl; apply lc_tm_abs.
    + apply lc_open_ty_rec with (K:=K); assumption.
    + apply (t K (S k) U); assumption.
  - simpl; apply lc_tm_app; eauto.
  - simpl; apply lc_tm_tabs. apply IHt with (K:=S K) (k:=k) (U:=U).
    + assumption.
    + apply lc_ty_mono with (T:=U) (K:=K) (K':=S K); auto; lia.
  - simpl; apply lc_tm_tapp; eauto using lc_open_ty_rec.
  - simpl; apply lc_tm_choice; eauto.
Qed.

Lemma lc_open_tm_ty : forall t U, locally_closed_tm (tm_tabs t) ->
  locally_closed_ty U -> locally_closed_tm (open_tm_ty t U).
Proof.
  intros t U Ht HU. unfold locally_closed_tm in *; unfold locally_closed_ty in HU.
  unfold open_tm_ty. apply lc_open_tm_ty_rec with (K:=0) (k:=0); auto.
  inversion Ht; assumption.
Qed.

Lemma lc_step : forall t u, locally_closed_tm t -> t --> u ->
  locally_closed_tm u.
Proof.
  intros t u Ht H; revert Ht; induction H; intros Ht; unfold locally_closed_tm in *.
  - apply lc_open_tm_rec with (K:=0) (k:=0).
    + match goal with
      | [ A : lc_tm_at _ _ (tm_abs _ _) |- _ ] => inversion A; assumption
      end.
    + match goal with
      | [ A : value _ |- _ ] => inversion A; assumption
      end.
  - apply lc_tm_app.
    + inversion Ht; eauto.
    + inversion Ht; assumption.
  - apply lc_tm_app.
    + inversion Ht; assumption.
    + inversion Ht; eauto.
  - apply lc_open_tm_ty_rec with (K:=0) (k:=0).
    + match goal with
      | [ A : lc_tm_at _ _ (tm_tabs _) |- _ ] => inversion A; assumption
      end.
    + assumption.
  - apply lc_tm_tapp.
    + inversion Ht; eauto.
    + assumption.
  - inversion Ht; assumption.
  - inversion Ht; assumption.
Qed.

Lemma instantiate_ty_lc : forall T K theta,
  lc_ty_at K T -> type_substitution_closed theta ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros T; induction T as [i|X|T1 IH1 T2 IH2|T IH];
    intros K theta H Htheta; inversion H; subst; simpl.
  - apply lc_ty_bvar; assumption.
  - apply lc_ty_mono with (T:=theta X) (K:=0) (K':=K).
    + lia.
    + apply Htheta.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IH with (K:=S K) (theta:=theta); auto.
Qed.

Lemma instantiate_lc : forall t K k theta gamma,
  lc_tm_at K k t -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros t; induction t as
    [i|x|T IHt t|t1 IH1 t2 IH2|t IHt|t1 IHt1 T|t1 IHt1 t2 IHt2];
    intros K k theta gamma H Htheta Hgamma; inversion H; subst; simpl.
  - apply lc_tm_bvar; assumption.
  - apply lc_tm_weaken with (K:=K) (k:=k); apply Hgamma.
  - apply lc_tm_abs.
    + apply instantiate_ty_lc; auto.
    + apply t with (K:=K) (k:=S k); auto.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHt with (K:=S K) (k:=k); auto.
  - apply lc_tm_tapp; eauto using instantiate_ty_lc.
  - apply lc_tm_choice; eauto.
Qed.

Lemma value_relation_value : forall eta rho T v,
  value_relation eta rho T v -> value v.
Proof.
  intros eta rho T; induction T; simpl; intros v H.
  - destruct (nth_error eta n) as [a|] eqn:E; simpl in H; try contradiction.
    apply (candidate_values a v H).
  - destruct (rho a) as [c|] eqn:E; simpl in H; try contradiction.
    apply (candidate_values c v H).
  - tauto.
  - tauto.
Qed.

Lemma expression_relation_lc : forall eta rho T t,
  expression_relation eta rho T t -> locally_closed_tm t.
Proof. intros; exact (proj1 H). Qed.

Lemma expression_relation_sn : forall eta rho T t,
  expression_relation eta rho T t -> strongly_normalizing t.
Proof. intros; exact (proj1 (proj2 H)). Qed.

Lemma sn_step : forall t u, strongly_normalizing t -> t --> u ->
  strongly_normalizing u.
Proof.
  intros t u H; inversion H; auto.
Qed.

Lemma expression_tail : forall R t t', expression_lifting R t -> t --> t' ->
  expression_lifting R t'.
Proof.
  intros R t t' [Hlc [Hsn Hend]] Hstep.
  split.
  - exact (lc_step t t' Hlc Hstep).
  - split.
    + exact (sn_step t t' Hsn Hstep).
    + intros v Hmulti Hv.
      assert (Hm : multi t v).
      { apply multi_step with t'; assumption. }
      exact (Hend v Hm Hv).
Qed.

Lemma app_endpoint : forall eta rho T1 T2 t1 t2 v,
  expression_relation eta rho (Ty_Arrow T1 T2) t1 ->
  expression_relation eta rho T1 t2 ->
  tm_app t1 t2 -->* v -> value v ->
  value_relation eta rho T2 v.
Proof.
  admit.
Admitted.

Lemma app_expression : forall eta rho T1 T2 t1 t2,
  expression_relation eta rho (Ty_Arrow T1 T2) t1 ->
  expression_relation eta rho T1 t2 ->
  expression_relation eta rho T2 (tm_app t1 t2).
Proof.
  intros eta rho T1 T2 t1 t2 E1 E2.
  destruct E1 as [LC1 [SN1 End1]]. destruct E2 as [LC2 [SN2 End2]].
  split.
  - apply lc_tm_app; assumption.
  - split.
    + revert t2 LC2 SN2 End2.
      induction SN1 as [f Hf IHf].
      intros t2 LC2 SN2 End2.
      induction SN2 as [a Ha IHa].
    apply SN_intro. intros u Hu; inversion Hu; subst.
    * pose proof (End1 (tm_abs T t) (multi_refl _) (v_abs T t H1)) as Hfun.
      simpl in Hfun.
      destruct Hfun as [_ [U [body [Heq Hbody]]]].
      inversion Heq; clear Heq.
      apply expression_relation_sn with (eta:=eta) (rho:=rho) (T:=T2)
        (t:=open_tm body a). apply Hbody.
      exact (End2 a (multi_refl a) H3).
    * apply (IHf t1' H1).
      -- apply lc_step with (t:=f); assumption.
      -- assert (Ef : expression_lifting (value_relation eta rho
          (Ty_Arrow T1 T2)) f).
         { unfold expression_lifting; exact (conj LC1 (conj (SN_intro f Hf) End1)). }
         pose proof (expression_tail (value_relation eta rho
          (Ty_Arrow T1 T2)) f t1' Ef H1) as Et.
         exact (proj2 (proj2 Et)).
      -- exact LC2.
      -- exact (SN_intro a Ha).
      -- exact End2.
    * apply (IHa t1' H1).
      -- apply lc_step with (t:=a); assumption.
      -- assert (Ea : expression_lifting (value_relation eta rho T1) a).
         { unfold expression_lifting; exact (conj LC2 (conj (SN_intro a Ha) End2)). }
         pose proof (expression_tail (value_relation eta rho T1)
          a t1' Ea H1) as Et.
         exact (proj2 (proj2 Et)).
    + apply app_endpoint with (eta:=eta) (rho:=rho) (T1:=T1) (T2:=T2)
        (t1:=t1) (t2:=t2); [split; [exact LC1|split; [exact SN1|exact End1]]|
        split; [exact LC2|split; [exact SN2|exact End2]]|assumption|assumption].
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationNondeterminismMediumTask.
