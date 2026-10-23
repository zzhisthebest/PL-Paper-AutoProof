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

Lemma value_no_step : forall v u, value v -> ~ v --> u.
Proof.
  intros v u Hv Hs; inversion Hv; subst; inversion Hs; subst;
    try solve [inversion H0]; try solve [inversion H1]; try solve [inversion H2].
Qed.

Lemma value_multi : forall v u, value v -> v -->* u -> u = v.
Proof.
  intros v u Hv Hm; inversion Hm; subst; auto.
  exfalso; eapply value_no_step; eauto.
Qed.

Lemma value_SN : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv; constructor; intros u Hs.
  exfalso; eapply value_no_step; eauto.
Qed.

Lemma relation_value : forall eta rho T v,
  value_relation eta rho T v -> value v.
Proof.
  induction T; simpl; intros v Hv; eauto using candidate_values.
  - destruct (nth_error eta n) as [a|]; [exact (candidate_values a _ Hv)|contradiction].
  - destruct (rho a) as [b|]; [exact (candidate_values b _ Hv)|contradiction].
  - exact (proj1 Hv).
  - exact (proj1 Hv).
Qed.

Lemma relation_value_lc : forall eta rho T v,
  value_relation eta rho T v -> locally_closed_tm v.
Proof.
  intros eta rho T v H.
  apply relation_value in H; inversion H; assumption.
Qed.

Lemma lift_value : forall R v,
  value v -> R v -> expression_lifting R v.
Proof.
  intros R v Hv Hr; split; [inversion Hv; auto|].
  split; [now apply value_SN|].
  intros w Hm _. rewrite (value_multi _ _ Hv Hm); assumption.
Qed.

Lemma SN_step : forall t u, strongly_normalizing t -> t --> u ->
  strongly_normalizing u.
Proof.
  intros t u Hsn Hstep; inversion Hsn; eauto.
Qed.

Lemma SN_multi : forall t u, strongly_normalizing t -> t -->* u ->
  strongly_normalizing u.
Proof.
  intros t u Hsn Hm; induction Hm; eauto using SN_step.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v Hm; induction Hm; intros Huv; eauto using multi.
Qed.

Lemma multi_app1 : forall t u s, t -->* u ->
  locally_closed_tm s -> tm_app t s -->* tm_app u s.
Proof.
  intros t u s Hm Hlc; induction Hm; eauto using multi, step.
Qed.

Lemma multi_app2 : forall v t u, value v -> t -->* u ->
  tm_app v t -->* tm_app v u.
Proof.
  intros v t u Hv Hm; induction Hm; eauto using multi, step.
Qed.

Lemma multi_tapp : forall t u T, t -->* u ->
  locally_closed_ty T -> tm_tapp t T -->* tm_tapp u T.
Proof.
  intros t u T Hm Hlc; induction Hm; eauto using multi, step.
Qed.

Lemma SN_choice : forall t u, locally_closed_tm t -> locally_closed_tm u ->
  strongly_normalizing t -> strongly_normalizing u ->
  strongly_normalizing (tm_choice t u).
Proof.
  intros t u Ht Hu Hsn1 Hsn2; constructor; intros w Hstep.
  inversion Hstep; subst; assumption.
Qed.

Lemma lift_choice : forall R t u,
  expression_lifting R t -> expression_lifting R u ->
  expression_lifting R (tm_choice t u).
Proof.
  intros R t u [Hlt [Hst Hrt]] [Hlu [Hsu Hru]].
  unfold expression_lifting; split; [constructor; assumption|].
  split; [now apply SN_choice|].
  intros v Hm Hv; inversion Hm; subst; [inversion Hv|].
  inversion H; subst; eauto.
Qed.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T U => fv_ty T ++ fv_ty U
  | Ty_All T => fv_ty T
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t | tm_tabs t => fv_tm t
  | tm_app t u | tm_choice t u => fv_tm t ++ fv_tm u
  | tm_tapp t _ => fv_tm t
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t => fv_ty T ++ ftv_tm t
  | tm_tabs t => ftv_tm t
  | tm_app t u | tm_choice t u => ftv_tm t ++ ftv_tm u
  | tm_tapp t T => ftv_tm t ++ fv_ty T
  end.

Definition fresh (L : list atom) := S (fold_right Nat.max 0 L).

Lemma in_fold_max : forall L x, In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x H; simpl in *; [contradiction|].
  destruct H as [->|H]; [lia|].
  specialize (IH _ H); lia.
Qed.

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L H; unfold fresh in H.
  pose proof (in_fold_max _ _ H); lia.
Qed.

Lemma lc_ty_open_rec : forall T k U, lc_ty_at k T ->
  lc_ty_at 0 U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U Ht Hu; inversion Ht; subst; simpl; eauto.
  - destruct (Nat.eqb k n) eqn:Hkn; eauto.
    apply Nat.eqb_eq in Hkn; subst.
    clear Ht. induction Hu; constructor; auto; lia.
Qed.

Lemma open_ty_lc_id_gen : forall T d k U, lc_ty_at d T ->
  d <= k -> open_ty_rec k U T = T.
Proof.
  induction T; intros d k U Hlc Hle; inversion Hlc; subst; simpl; auto.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal; eauto.
  - f_equal; eapply IHT; eauto; lia.
Qed.

Lemma open_ty_lc_id : forall T k U, locally_closed_ty T ->
  open_ty_rec k U T = T.
Proof. intros; eapply open_ty_lc_id_gen; eauto; lia. Qed.

Lemma open_tm_lc_id_gen : forall t D d k u, lc_tm_at D d t ->
  d <= k -> open_tm_rec k u t = t.
Proof.
  induction t; intros D d k u Hlc Hle; inversion Hlc; subst; simpl; auto.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal; eapply IHt; eauto; lia.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma open_tm_lc_id : forall t k u, locally_closed_tm t ->
  open_tm_rec k u t = t.
Proof. intros; eapply open_tm_lc_id_gen; eauto; lia. Qed.

Lemma open_tm_ty_lc_id_gen : forall t D d k U, lc_tm_at D d t ->
  D <= k -> open_tm_ty_rec k U t = t.
Proof.
  induction t; intros D d k U Hlc Hle; inversion Hlc; subst; simpl; auto;
    try (f_equal; eauto using open_ty_lc_id_gen).
  f_equal; eapply IHt; eauto; lia.
Qed.

Lemma open_tm_ty_lc_id : forall t k U, locally_closed_tm t ->
  open_tm_ty_rec k U t = t.
Proof. intros; eapply open_tm_ty_lc_id_gen; eauto; lia. Qed.

Lemma lc_ty_deopen : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion Hlc; subst; constructor; lia.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H; unfold locally_closed_ty in *;
    eauto using lc_ty_at.
  constructor. eapply lc_ty_deopen.
  apply H0. apply fresh_not_in.
Qed.

Lemma lc_tm_deopen : forall t D k x,
  lc_tm_at D k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at D (S k) t.
Proof.
  induction t; intros D k x Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion Hlc; subst; constructor; lia.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_deopen : forall t D k X,
  lc_tm_at D k (open_tm_ty_rec D (Ty_FVar X) t) ->
  lc_tm_at (S D) k t.
Proof.
  induction t; intros D k X Hlc; simpl in Hlc; inversion Hlc; subst;
    eauto using lc_tm_at, lc_ty_deopen.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H;
    unfold locally_closed_tm in *; eauto using lc_tm_at, wf_ty_lc.
  - apply lc_tm_abs; [exact (wf_ty_lc _ _ H)|].
    eapply lc_tm_deopen.
    apply H1. apply fresh_not_in.
  - constructor. eapply lc_tm_ty_deopen.
    apply H0. apply fresh_not_in.
  - apply lc_tm_tapp; [assumption|exact (wf_ty_lc _ _ H0)].
Qed.

Lemma lc_ty_weaken : forall T d k,
  lc_ty_at d T -> d <= k -> lc_ty_at k T.
Proof.
  intros T d k H; revert k; induction H; intros k' Hle.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHlc_ty_at; lia.
Qed.

Lemma lc_tm_weaken : forall t D k D' k',
  lc_tm_at D k t -> D <= D' -> k <= k' -> lc_tm_at D' k' t.
Proof.
  intros t D k D' k' H; revert D' k'; induction H;
    intros D' k' HD Hk.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; [eapply lc_ty_weaken; eauto|apply IHlc_tm_at; lia].
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
  - apply lc_tm_tapp; eauto using lc_ty_weaken.
  - apply lc_tm_choice; eauto.
Qed.

Lemma lc_tm_open : forall t D k u,
  lc_tm_at D (S k) t -> locally_closed_tm u ->
  lc_tm_at D k (open_tm_rec k u t).
Proof.
  induction t; intros D k u Hlc Hu; inversion Hlc; subst; simpl;
    eauto using lc_tm_at.
  - destruct (Nat.eqb k n) eqn:E.
    + eapply lc_tm_weaken; eauto; lia.
    + constructor. apply Nat.eqb_neq in E; lia.
Qed.

Lemma lc_ty_open : forall T k U,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U Hlc Hu; inversion Hlc; subst; simpl;
    eauto using lc_ty_at.
  - destruct (Nat.eqb k n) eqn:E.
    + eapply lc_ty_weaken; eauto; lia.
    + constructor. apply Nat.eqb_neq in E; lia.
Qed.

Lemma lc_tm_ty_open : forall t D k U,
  lc_tm_at (S D) k t -> locally_closed_ty U ->
  lc_tm_at D k (open_tm_ty_rec D U t).
Proof.
  induction t; intros D k U Hlc Hu; inversion Hlc; subst; simpl;
    eauto using lc_tm_at, lc_ty_open.
Qed.

Lemma step_lc : forall t u, locally_closed_tm t -> t --> u ->
  locally_closed_tm u.
Proof.
  intros t u Hlc Hs; revert Hlc; induction Hs; intros Hlc;
    inversion Hlc; subst.
  - eapply lc_tm_open; eauto. inversion H; assumption.
  - apply lc_tm_app; [apply IHHs; assumption|assumption].
  - apply lc_tm_app; [assumption|apply IHHs; assumption].
  - eapply lc_tm_ty_open; eauto. inversion H; assumption.
  - apply lc_tm_tapp; [apply IHHs; assumption|assumption].
  - assumption.
  - assumption.
Qed.

Lemma lift_step : forall R t u, expression_lifting R t -> t --> u ->
  expression_lifting R u.
Proof.
  intros R t u [Hlc [Hsn Hrel]] Hs.
  split; [eapply step_lc; eauto|].
  split; [eapply SN_step; eauto|].
  intros v Hm Hv; apply Hrel; eauto using multi.
Qed.

Lemma lift_expansion : forall R t,
  locally_closed_tm t -> ~ value t ->
  (forall u, t --> u -> expression_lifting R u) ->
  expression_lifting R t.
Proof.
  intros R t Hlc Hnv Hnext.
  split; [assumption|].
  split; [constructor; intros u Hs; exact (proj1 (proj2 (Hnext _ Hs)))|].
  intros v Hm Hv; inversion Hm; subst; [contradiction|].
  exact ((proj2 (proj2 (Hnext _ H))) _ H0 Hv).
Qed.

Lemma app_not_value : forall t u, ~ value (tm_app t u).
Proof. intros t u H; inversion H. Qed.

Lemma tapp_not_value : forall t T, ~ value (tm_tapp t T).
Proof. intros t T H; inversion H. Qed.

Lemma lift_app2 : forall P R U body arg,
  value (tm_abs U body) -> expression_lifting P arg ->
  (forall v, P v -> expression_lifting R (open_tm body v)) ->
  expression_lifting R (tm_app (tm_abs U body) arg).
Proof.
  intros P R U body arg Hval Harg Hbody.
  destruct Harg as [Hlc [Hsn Hrel]].
  revert Hlc Hrel.
  induction Hsn as [arg Hsn IH]; intros Hlc Hrel.
  apply lift_expansion; [constructor; [inversion Hval; assumption|assumption]
    |apply app_not_value|].
  intros next Hstep; inversion Hstep; subst.
  - apply Hbody. apply Hrel; [constructor|assumption].
  - exfalso; eapply value_no_step; eauto.
  - apply IH; [assumption|eapply step_lc; eauto|].
    intros v Hm Hv; apply Hrel; [eapply multi_step; eauto|assumption].
Qed.

Lemma lift_app : forall eta rho A B fn arg,
  expression_relation eta rho (Ty_Arrow A B) fn ->
  expression_relation eta rho A arg ->
  expression_relation eta rho B (tm_app fn arg).
Proof.
  intros eta rho A B fn arg [Hlc [Hsn Hrel]] Harg.
  revert Hlc Hrel.
  induction Hsn as [fn Hsn IH]; intros Hlc Hrel.
  apply lift_expansion; [constructor; [assumption|exact (proj1 Harg)]
    |apply app_not_value|].
  intros next Hstep; inversion Hstep; subst.
  - assert (Hv : value (tm_abs T t)) by (constructor; assumption).
    pose proof (Hrel _ (multi_refl _) Hv) as Hfn.
    destruct Hfn as [_ [U' [body [Heq Hbody]]]].
    inversion Heq; subst.
    apply Hbody; apply (proj2 (proj2 Harg)); [constructor|assumption].
  - apply IH; [exact H1|eapply (step_lc fn t1'); eauto|].
    intros v Hm Hv; apply Hrel; [eapply multi_step; eauto|assumption].
  - assert (Hv : value fn) by assumption.
    pose proof (Hrel _ (multi_refl _) Hv) as Hfn.
    destruct Hfn as [_ [U [body [Heq Hbody]]]].
    subst fn; eapply lift_step.
    + eapply lift_app2; eauto.
    + exact Hstep.
Qed.

Lemma lift_tapp : forall P R fn U,
  locally_closed_ty U -> expression_lifting P fn ->
  (forall v, P v -> exists body, v = tm_tabs body /\
      expression_lifting R (open_tm_ty body U)) ->
  expression_lifting R (tm_tapp fn U).
Proof.
  intros P R fn U Hty [Hlc [Hsn Hrel]] Hbody.
  revert Hlc Hrel.
  induction Hsn as [fn Hsn IH]; intros Hlc Hrel.
  apply lift_expansion; [constructor; assumption|apply tapp_not_value|].
  intros next Hstep; inversion Hstep; subst.
  - assert (Hv : value (tm_tabs t)) by (constructor; assumption).
    destruct (Hbody _ (Hrel _ (multi_refl _) Hv))
      as [body [Heq Hb]]. inversion Heq; subst; assumption.
  - apply IH; [assumption|eapply step_lc; eauto|].
    intros v Hm Hv; apply Hrel; [eapply multi_step; eauto|assumption].
Qed.

Lemma lift_iff : forall R S t,
  (forall v, R v <-> S v) ->
  expression_lifting R t <-> expression_lifting S t.
Proof.
  intros R S t Hiff; unfold expression_lifting.
  split; intros [Hlc [Hsn Hrel]].
  - split; [assumption|]; split; [assumption|].
    intros v Hm Hv; apply Hiff; eauto.
  - split; [assumption|]; split; [assumption|].
    intros v Hm Hv; apply Hiff; eauto.
Qed.

Lemma relation_eta_agree : forall T d eta eta' rho v,
  lc_ty_at d T ->
  (forall i, i < d -> nth_error eta i = nth_error eta' i) ->
  (value_relation eta rho T v <-> value_relation eta' rho T v).
Proof.
  induction T; intros d eta eta' rho v Hlc Hagree;
    inversion Hlc; subst; simpl.
  - rewrite (Hagree n H1); tauto.
  - tauto.
  - assert (Hdom : forall w, value_relation eta rho T1 w <->
        value_relation eta' rho T1 w) by (intro w; eapply IHT1; eauto).
    assert (Hcod : forall w, value_relation eta rho T2 w <->
        value_relation eta' rho T2 w) by (intro w; eapply IHT2; eauto).
    split; intros [Hv [U [body [Heq Hbody]]]].
    + split; [assumption|exists U, body; split; [assumption|]].
      intros arg Harg; apply (proj1 (lift_iff _ _ _ Hcod)).
      apply Hbody; apply (proj2 (Hdom _)); assumption.
    + split; [assumption|exists U, body; split; [assumption|]].
      intros arg Harg; apply (proj2 (lift_iff _ _ _ Hcod)).
      apply Hbody; apply (proj1 (Hdom _)); assumption.
  - split; intros [Hv [body [Heq Hbody]]].
    + split; [assumption|exists body; split; [assumption|]].
      intros U a HU.
      assert (Hrec : forall w,
          value_relation (a :: eta) rho T w <->
          value_relation (a :: eta') rho T w).
      { intro w; eapply IHT; [eassumption|].
        intros [|i] Hi; simpl; auto; apply Hagree; lia. }
      apply (proj1 (lift_iff _ _ _ Hrec)); apply Hbody; assumption.
    + split; [assumption|exists body; split; [assumption|]].
      intros U a HU.
      assert (Hrec : forall w,
          value_relation (a :: eta) rho T w <->
          value_relation (a :: eta') rho T w).
      { intro w; eapply IHT; [eassumption|].
        intros [|i] Hi; simpl; auto; apply Hagree; lia. }
      apply (proj2 (lift_iff _ _ _ Hrec)); apply Hbody; assumption.
Qed.

Lemma relation_eta_closed : forall U eta rho v,
  locally_closed_ty U ->
  (value_relation eta rho U v <-> value_relation [] rho U v).
Proof.
  intros U eta rho v Hlc; eapply relation_eta_agree; eauto.
  intros i Hi; lia.
Qed.

Lemma relation_rho_agree : forall T eta rho rho' v,
  (forall X, In X (fv_ty T) -> rho X = rho' X) ->
  (value_relation eta rho T v <-> value_relation eta rho' T v).
Proof.
  induction T; intros eta rho rho' v Hagree; simpl in *.
  - tauto.
  - rewrite (Hagree a (or_introl eq_refl)); tauto.
  - assert (Hdom : forall w, value_relation eta rho T1 w <->
        value_relation eta rho' T1 w).
    { intro w; apply IHT1; intros X HX; apply Hagree; apply in_or_app; auto. }
    assert (Hcod : forall w, value_relation eta rho T2 w <->
        value_relation eta rho' T2 w).
    { intro w; apply IHT2; intros X HX; apply Hagree; apply in_or_app; auto. }
    split; intros [Hv [U [body [Heq Hbody]]]].
    + split; [assumption|exists U, body; split; [assumption|]].
      intros arg Harg; apply (proj1 (lift_iff _ _ _ Hcod)).
      apply Hbody; apply (proj2 (Hdom _)); assumption.
    + split; [assumption|exists U, body; split; [assumption|]].
      intros arg Harg; apply (proj2 (lift_iff _ _ _ Hcod)).
      apply Hbody; apply (proj1 (Hdom _)); assumption.
  - split; intros [Hv [body [Heq Hbody]]].
    + split; [assumption|exists body; split; [assumption|]].
      intros U a HU.
      assert (Hrec : forall w,
          value_relation (a :: eta) rho T w <->
          value_relation (a :: eta) rho' T w).
      { intro w; apply IHT; exact Hagree. }
      apply (proj1 (lift_iff _ _ _ Hrec)); apply Hbody; assumption.
    + split; [assumption|exists body; split; [assumption|]].
      intros U a HU.
      assert (Hrec : forall w,
          value_relation (a :: eta) rho T w <->
          value_relation (a :: eta) rho' T w).
      { intro w; apply IHT; exact Hagree. }
      apply (proj2 (lift_iff _ _ _ Hrec)); apply Hbody; assumption.
Qed.

Lemma relation_rho_fresh : forall T eta rho X a v,
  ~ In X (fv_ty T) ->
  (value_relation eta (relation_update rho X a) T v <->
   value_relation eta rho T v).
Proof.
  intros T eta rho X a v Hfresh; apply relation_rho_agree.
  intros Y HY; unfold relation_update.
  destruct (Nat.eqb X Y) eqn:E; auto.
  apply Nat.eqb_eq in E; subst; contradiction.
Qed.

Definition type_candidate (rho : relation_env) (U : ty) : value_candidate :=
  {| candidate_relation := value_relation [] rho U;
     candidate_values := relation_value [] rho U |}.

Lemma relation_open : forall T k eta rho rho' V a v,
  length eta = k ->
  (forall X, In X (fv_ty T) -> rho' X = rho X) ->
  (forall env w, value_relation env rho' V w <-> candidate_relation a w) ->
  (value_relation eta rho' (open_ty_rec k V T) v <->
   value_relation (eta ++ [a]) rho T v).
Proof.
  induction T as [n|Y|T1 IHT1 T2 IHT2|T IHT];
    intros k eta rho rho' V a v Hlength Hagree HV; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E.
      rewrite nth_error_app2 by lia.
      replace (n - length eta) with 0 by lia; simpl.
      apply HV.
    + apply Nat.eqb_neq in E.
      destruct (Nat.lt_ge_cases n k) as [Hlt|Hge].
      * rewrite nth_error_app1 by lia; tauto.
      * simpl.
        rewrite (proj2 (nth_error_None eta n)) by lia.
        rewrite (proj2 (nth_error_None (eta ++ [a]) n)) by
          (rewrite length_app; simpl; lia); tauto.
  - rewrite (Hagree Y (or_introl eq_refl)); tauto.
  - assert (Hdom : forall w,
        value_relation eta rho' (open_ty_rec k V T1) w <->
        value_relation (eta ++ [a]) rho T1 w).
    { intro w; eapply IHT1; eauto.
      intros X HX; apply Hagree; apply in_or_app; auto. }
    assert (Hcod : forall w,
        value_relation eta rho' (open_ty_rec k V T2) w <->
        value_relation (eta ++ [a]) rho T2 w).
    { intro w; eapply IHT2; eauto.
      intros X HX; apply Hagree; apply in_or_app; auto. }
    split; intros [Hv [U [body [Heq Hbody]]]].
    + split; [assumption|exists U, body; split; [assumption|]].
      intros arg Harg; apply (proj1 (lift_iff _ _ _ Hcod)).
      apply Hbody; apply (proj2 (Hdom _)); assumption.
    + split; [assumption|exists U, body; split; [assumption|]].
      intros arg Harg; apply (proj2 (lift_iff _ _ _ Hcod)).
      apply Hbody; apply (proj1 (Hdom _)); assumption.
  - split; intros [Hv [body [Heq Hbody]]].
    + split; [assumption|exists body; split; [assumption|]].
      intros U b HU.
      assert (Hrec : forall w,
          value_relation (b :: eta) rho' (open_ty_rec (S k) V T) w <->
          value_relation (b :: eta ++ [a]) rho T w).
      { intro w; change (b :: eta ++ [a]) with ((b :: eta) ++ [a]).
        eapply IHT; eauto. simpl; lia. }
      apply (proj1 (lift_iff _ _ _ Hrec)); apply Hbody; assumption.
    + split; [assumption|exists body; split; [assumption|]].
      intros U b HU.
      assert (Hrec : forall w,
          value_relation (b :: eta) rho' (open_ty_rec (S k) V T) w <->
          value_relation (b :: eta ++ [a]) rho T w).
      { intro w; change (b :: eta ++ [a]) with ((b :: eta) ++ [a]).
        eapply IHT; eauto. simpl; lia. }
      apply (proj2 (lift_iff _ _ _ Hrec)); apply Hbody; assumption.
Qed.

Definition theta_update (theta : type_substitution) X U : type_substitution :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition gamma_update (gamma : term_substitution) x u : term_substitution :=
  fun y => if Nat.eqb x y then u else gamma y.

Lemma not_in_app_split : forall (A B : list atom) x,
  ~ In x (A ++ B) -> ~ In x A /\ ~ In x B.
Proof.
  intros A B x H; split; intros Hin; apply H; apply in_or_app; auto.
Qed.

Lemma theta_update_closed : forall theta X U,
  type_substitution_closed theta -> locally_closed_ty U ->
  type_substitution_closed (theta_update theta X U).
Proof.
  intros theta X U Htheta HU Y; unfold theta_update.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma gamma_update_closed : forall gamma x u,
  term_substitution_closed gamma -> locally_closed_tm u ->
  term_substitution_closed (gamma_update gamma x u).
Proof.
  intros gamma x u Hgamma Hu y; unfold gamma_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma instantiate_ty_lc : forall T k theta,
  lc_ty_at k T -> type_substitution_closed theta ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  intros T k theta Hlc; revert theta; induction Hlc; intros theta Htheta;
    simpl; eauto using lc_ty_at, lc_ty_weaken.
  eapply lc_ty_weaken with (d := 0); [apply Htheta|lia].
Qed.

Lemma instantiate_lc : forall t D k theta gamma,
  lc_tm_at D k t -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at D k (instantiate theta gamma t).
Proof.
  intros t D k theta gamma Hlc; revert theta gamma;
    induction Hlc; intros theta gamma Htheta Hgamma; simpl.
  - constructor; assumption.
  - eapply lc_tm_weaken with (D := 0) (k := 0);
      [apply Hgamma|lia|lia].
  - constructor; eauto using instantiate_ty_lc.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto using instantiate_ty_lc.
  - constructor; eauto.
Qed.

Lemma instantiate_ty_open : forall T k X U theta,
  ~ In X (fv_ty T) -> type_substitution_closed theta ->
  instantiate_ty (theta_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k X U theta Hfresh Htheta; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold theta_update; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - assert (a <> X) by (intro Heq; subst; apply Hfresh; simpl; auto).
    unfold theta_update.
    assert (E : (X =? a) = false) by (apply Nat.eqb_neq; lia).
    rewrite E.
    symmetry; apply open_ty_lc_id; apply Htheta.
  - apply not_in_app_split in Hfresh; destruct Hfresh as [H1 H2].
    rewrite (IHT1 _ _ _ _ H1 Htheta), (IHT2 _ _ _ _ H2 Htheta).
    reflexivity.
  - rewrite (IHT _ _ _ _ Hfresh Htheta); reflexivity.
Qed.

Lemma instantiate_tm_open : forall t k x u theta gamma,
  ~ In x (fv_tm t) -> term_substitution_closed gamma ->
  instantiate theta (gamma_update gamma x u)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (instantiate theta gamma t).
Proof.
  induction t; intros k x u theta gamma Hfresh Hgamma; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold gamma_update; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - assert (a <> x) by (intro Heq; subst; apply Hfresh; simpl; auto).
    unfold gamma_update.
    assert (E : (x =? a) = false) by (apply Nat.eqb_neq; lia).
    rewrite E.
    symmetry; apply open_tm_lc_id; apply Hgamma.
  - rewrite (IHt _ _ _ _ _ Hfresh Hgamma); reflexivity.
  - apply not_in_app_split in Hfresh; destruct Hfresh as [H1 H2].
    rewrite (IHt1 _ _ _ _ _ H1 Hgamma),
      (IHt2 _ _ _ _ _ H2 Hgamma); reflexivity.
  - rewrite (IHt _ _ _ _ _ Hfresh Hgamma); reflexivity.
  - rewrite (IHt _ _ _ _ _ Hfresh Hgamma); reflexivity.
  - apply not_in_app_split in Hfresh; destruct Hfresh as [H1 H2].
    rewrite (IHt1 _ _ _ _ _ H1 Hgamma),
      (IHt2 _ _ _ _ _ H2 Hgamma); reflexivity.
Qed.

Lemma instantiate_tm_ty_open : forall t k X U theta gamma,
  ~ In X (ftv_tm t) -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate (theta_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros k X U theta gamma Hfresh Htheta Hgamma;
    simpl in *; auto.
  - symmetry; apply open_tm_ty_lc_id; apply Hgamma.
  - apply not_in_app_split in Hfresh; destruct Hfresh as [H1 H2].
    rewrite (instantiate_ty_open _ _ _ _ _ H1 Htheta).
    rewrite (IHt _ _ _ _ _ H2 Htheta Hgamma); reflexivity.
  - apply not_in_app_split in Hfresh; destruct Hfresh as [H1 H2].
    rewrite (IHt1 _ _ _ _ _ H1 Htheta Hgamma),
      (IHt2 _ _ _ _ _ H2 Htheta Hgamma); reflexivity.
  - rewrite (IHt _ _ _ _ _ Hfresh Htheta Hgamma); reflexivity.
  - apply not_in_app_split in Hfresh; destruct Hfresh as [H1 H2].
    rewrite (IHt _ _ _ _ _ H1 Htheta Hgamma).
    rewrite (instantiate_ty_open _ _ _ _ _ H2 Htheta); reflexivity.
  - apply not_in_app_split in Hfresh; destruct Hfresh as [H1 H2].
    rewrite (IHt1 _ _ _ _ _ H1 Htheta Hgamma),
      (IHt2 _ _ _ _ _ H2 Htheta Hgamma); reflexivity.
Qed.

Fixpoint ftv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: tail => fv_ty T ++ ftv_context tail
  end.

Lemma lookup_ftv : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros x T X Hlookup Hfv;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst; apply in_or_app; auto.
  - apply in_or_app; right; eapply IH; eauto.
Qed.

Lemma related_gamma_update : forall rho Gamma gamma x T arg,
  related_substitution rho Gamma gamma ->
  value_relation [] rho T arg ->
  related_substitution rho ((x, T) :: Gamma)
    (gamma_update gamma x arg).
Proof.
  intros rho Gamma gamma x T arg Hgamma Harg y S Hlookup.
  simpl in Hlookup; unfold gamma_update.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst.
    rewrite Nat.eqb_refl in Hlookup; inversion Hlookup; subst; assumption.
  - rewrite Nat.eqb_sym in Hlookup; rewrite E in Hlookup.
    apply Hgamma; assumption.
Qed.

Lemma related_rho_update : forall rho Gamma gamma X a,
  ~ In X (ftv_context Gamma) ->
  related_substitution rho Gamma gamma ->
  related_substitution (relation_update rho X a) Gamma gamma.
Proof.
  intros rho Gamma gamma X a Hfresh Hgamma x T Hlookup.
  assert (Hnot : ~ In X (fv_ty T)).
  { intro Hin; apply Hfresh; eapply lookup_ftv; eauto. }
  apply (proj2 (relation_rho_fresh T [] rho X a _ Hnot)).
  apply Hgamma; assumption.
Qed.

Lemma relation_open_fvar : forall T X rho a v,
  ~ In X (fv_ty T) ->
  (value_relation [] (relation_update rho X a)
      (open_ty T (Ty_FVar X)) v <->
   value_relation [a] rho T v).
Proof.
  intros T X rho a v Hfresh.
  eapply relation_open with (eta := [])
    (rho' := relation_update rho X a) (V := Ty_FVar X);
    simpl; eauto.
  - intros Y HY; unfold relation_update.
    destruct (Nat.eqb X Y) eqn:E; auto.
    apply Nat.eqb_eq in E; subst; contradiction.
  - intros env w; simpl; unfold relation_update.
    rewrite Nat.eqb_refl; tauto.
Qed.

Lemma relation_open_type : forall T U rho v,
  locally_closed_ty U ->
  (value_relation [] rho (open_ty T U) v <->
   value_relation [type_candidate rho U] rho T v).
Proof.
  intros T U rho v HU.
  eapply relation_open with (eta := []) (rho' := rho) (V := U);
    simpl; eauto.
  intros env w; apply relation_eta_closed; assumption.
Qed.

Lemma instantiate_ty_id : forall T,
  instantiate_ty Ty_FVar T = T.
Proof. induction T; simpl; congruence. Qed.

Lemma instantiate_id : forall t,
  instantiate Ty_FVar tm_fvar t = t.
Proof.
  induction t; simpl; try rewrite instantiate_ty_id;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2; reflexivity.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta gamma rho,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    related_substitution rho Gamma gamma ->
    expression_relation [] rho T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Htyping; induction Htyping;
    intros theta gamma rho Htheta Hgamma Hrelated; simpl.
  - apply lift_value.
    + apply relation_value with (eta := []) (rho := rho) (T := T).
      apply Hrelated; assumption.
    + apply Hrelated; assumption.
  - assert (Habs : locally_closed_tm
        (tm_abs (instantiate_ty theta T1) (instantiate theta gamma t2))).
    { change (locally_closed_tm
        (instantiate theta gamma (tm_abs T1 t2))).
      eapply instantiate_lc; eauto.
      eapply has_type_lc; eapply T_Abs; eauto. }
    apply lift_value; [constructor; exact Habs|].
    simpl; split; [constructor; exact Habs|].
    exists (instantiate_ty theta T1), (instantiate theta gamma t2).
    split; [reflexivity|].
    intros arg Harg.
    set (x := fresh (L ++ fv_tm t2)).
    assert (HxL : ~ In x L).
    { unfold x; intro Hin; apply (fresh_not_in (L ++ fv_tm t2));
        apply in_or_app; auto. }
    assert (Hxt : ~ In x (fv_tm t2)).
    { unfold x; intro Hin; apply (fresh_not_in (L ++ fv_tm t2));
        apply in_or_app; auto. }
    pose proof (relation_value_lc [] rho T1 arg Harg) as Harglc.
    specialize (H1 x HxL theta (gamma_update gamma x arg) rho
      Htheta (gamma_update_closed _ _ _ Hgamma Harglc)
      (related_gamma_update _ _ _ _ _ _ Hrelated Harg)) as Hbody.
    unfold open_tm in Hbody |- *.
    rewrite (instantiate_tm_open t2 0 x arg theta gamma Hxt Hgamma)
      in Hbody.
    exact Hbody.
  - eapply lift_app; eauto.
  - assert (Htabs : locally_closed_tm
        (tm_tabs (instantiate theta gamma t))).
    { change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
      eapply instantiate_lc; eauto.
      eapply has_type_lc; eapply T_TAbs; eauto. }
    apply lift_value; [constructor; exact Htabs|].
    simpl; split; [constructor; exact Htabs|].
    exists (instantiate theta gamma t); split; [reflexivity|].
    intros U a HU.
    set (X := fresh (L ++ fv_ty T ++ ftv_tm t ++ ftv_context Gamma)).
    assert (HXL : ~ In X L).
    { unfold X; intro Hin; apply (fresh_not_in
        (L ++ fv_ty T ++ ftv_tm t ++ ftv_context Gamma));
        apply in_or_app; auto. }
    assert (HXT : ~ In X (fv_ty T)).
    { unfold X; intro Hin; apply (fresh_not_in
        (L ++ fv_ty T ++ ftv_tm t ++ ftv_context Gamma));
        apply in_or_app; right; apply in_or_app; left; assumption. }
    assert (HXt : ~ In X (ftv_tm t)).
    { unfold X; intro Hin; apply (fresh_not_in
        (L ++ fv_ty T ++ ftv_tm t ++ ftv_context Gamma));
        apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; left; assumption. }
    assert (HXG : ~ In X (ftv_context Gamma)).
    { unfold X; intro Hin; apply (fresh_not_in
        (L ++ fv_ty T ++ ftv_tm t ++ ftv_context Gamma));
        apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; right; assumption. }
    pose proof (H0 X HXL (theta_update theta X U) gamma
      (relation_update rho X a)
      (theta_update_closed _ _ _ Htheta HU) Hgamma
      (related_rho_update _ _ _ _ _ HXG Hrelated)) as Hbody.
    unfold open_tm_ty in Hbody |- *.
    rewrite (instantiate_tm_ty_open t 0 X U theta gamma HXt Htheta Hgamma)
      in Hbody.
    apply (proj1 (lift_iff _ _ _
      (fun v => relation_open_fvar T X rho a v HXT))).
    exact Hbody.
  - assert (HU : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
    assert (HUinst : locally_closed_ty (instantiate_ty theta U)).
    { eapply instantiate_ty_lc; eauto. }
    eapply lift_tapp with
      (P := value_relation [] rho (Ty_All T))
      (R := value_relation [] rho (open_ty T U)).
    + exact HUinst.
    + eapply IHHtyping; eauto.
    + intros v Hv; simpl in Hv.
      destruct Hv as [_ [body [-> Hbody]]].
      exists body; split; [reflexivity|].
      specialize (Hbody (instantiate_ty theta U) (type_candidate rho U)
        HUinst).
      apply (proj2 (lift_iff _ _ _
        (fun w => relation_open_type T U rho w HU))).
      exact Hbody.
  - eapply lift_choice.
    + eapply IHHtyping1; eauto.
    + eapply IHHtyping2; eauto.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Htyping.
  pose proof (fundamental [] empty t T Htyping Ty_FVar tm_fvar
    (fun _ => None)) as Hfund.
  assert (Htheta : type_substitution_closed Ty_FVar).
  { intros X; constructor. }
  assert (Hgamma : term_substitution_closed tm_fvar).
  { intros x; constructor. }
  specialize (Hfund Htheta Hgamma).
  assert (Hrelated : related_substitution (fun _ => None) empty tm_fvar).
  { intros x U Hlookup; discriminate. }
  specialize (Hfund Hrelated).
  rewrite instantiate_id in Hfund.
  exact (proj1 (proj2 Hfund)).
Qed.

End SystemFNormalizationNondeterminismMediumTask.
