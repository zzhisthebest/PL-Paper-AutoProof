(** System F relational parametricity benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Module SystemFParametricityTask.
Import ListNotations.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

(** Language syntax, using locally nameless term and type binders. *)

Definition atom := nat.

Inductive ty : Type :=
  | Ty_BVar : nat -> ty
  | Ty_FVar : atom -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_All : ty -> ty.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_abs : ty -> tm -> tm
  | tm_app : tm -> tm -> tm
  | tm_tabs : tm -> tm
  | tm_tapp : tm -> ty -> tm.

(** Opening operations and local closure. *)

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

(** Call-by-value operational semantics. *)

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
  | ST_TAppTabs : forall t T,
      locally_closed_tm (tm_tabs t) ->
      locally_closed_ty T ->
      tm_tapp (tm_tabs t) T --> open_tm_ty t T
  | ST_TApp : forall t t' T,
      t --> t' ->
      locally_closed_ty T ->
      tm_tapp t T --> tm_tapp t' T
where "t1 '-->' t2" := (step t1 t2).

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(** Type well-formedness and typing rules. *)

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

Inductive wf_ty : ty_context -> ty -> Prop :=
  | WF_Var : forall Delta X,
      In X Delta ->
      wf_ty Delta (Ty_FVar X)
  | WF_Arrow : forall Delta T1 T2,
      wf_ty Delta T1 ->
      wf_ty Delta T2 ->
      wf_ty Delta (Ty_Arrow T1 T2)
  | WF_All : forall (L : list atom) Delta T,
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
        has_type Delta (update Gamma x T1)
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

(** Target theorem. *)

(** Some elementary infrastructure for the logical relation.  An expression is
    related when it evaluates (on both sides) to related values. *)

Lemma multi_trans : forall (x y z : tm), x -->* y -> y -->* z -> x -->* z.
Proof.
  intros x y z H; induction H; intros H2; eauto using multi.
Qed.

Lemma multi_one : forall x y, x --> y -> x -->* y.
Proof. intros; eauto using multi. Qed.

Lemma multi_app_l : forall t t' u,
  t -->* t' -> locally_closed_tm u -> tm_app t u -->* tm_app t' u.
Proof.
  intros t t' u H; induction H; intros Hu; eauto using multi, step.
Qed.

Lemma multi_app_r : forall v u u',
  value v -> u -->* u' -> tm_app v u -->* tm_app v u'.
Proof.
  intros v u u' Hv H; induction H; eauto using multi, step.
Qed.

Lemma multi_tapp : forall t t' U,
  t -->* t' -> locally_closed_ty U -> tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H; induction H; intros HU; eauto using multi, step.
Qed.

Definition expression_relation (R : relation tm) : relation tm :=
  fun e1 e2 => exists v1 v2,
    e1 -->* v1 /\ e2 -->* v2 /\ value v1 /\ value v2 /\ R v1 v2.

Record relational_binding : Type := mk_relational_binding {
  binding_left_type : ty;
  binding_right_type : ty;
  binding_relation : relation tm
}.

Definition relational_environment := atom -> option relational_binding.
Definition term_environment := atom -> option (tm * tm).

Definition empty_relational_environment : relational_environment := fun _ => None.
Definition empty_term_environment : term_environment := fun _ => None.

Definition extend_relational_environment (rho : relational_environment)
    (X : atom) (p : relational_binding) : relational_environment :=
  fun Y => if Nat.eqb X Y then Some p else rho Y.

Definition extend_term_environment (sigma : term_environment)
    (x : atom) (p : tm * tm) : term_environment :=
  fun y => if Nat.eqb x y then Some p else sigma y.

Definition chosen_type (left : bool) (p : relational_binding) : ty :=
  if left then binding_left_type p else binding_right_type p.

Definition chosen_term (left : bool) (p : tm * tm) : tm :=
  if left then fst p else snd p.

Fixpoint instantiate_type (left : bool) (rho : relational_environment)
    (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X =>
      match rho X with
      | Some p => chosen_type left p
      | None => Ty_FVar X
      end
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (instantiate_type left rho T1) (instantiate_type left rho T2)
  | Ty_All T1 => Ty_All (instantiate_type left rho T1)
  end.

Fixpoint instantiate_term (left : bool) (rho : relational_environment)
    (sigma : term_environment) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x =>
      match sigma x with
      | Some p => chosen_term left p
      | None => tm_fvar x
      end
  | tm_abs T t1 =>
      tm_abs (instantiate_type left rho T)
        (instantiate_term left rho sigma t1)
  | tm_app t1 t2 =>
      tm_app (instantiate_term left rho sigma t1)
        (instantiate_term left rho sigma t2)
  | tm_tabs t1 => tm_tabs (instantiate_term left rho sigma t1)
  | tm_tapp t1 T =>
      tm_tapp (instantiate_term left rho sigma t1)
        (instantiate_type left rho T)
  end.

(** [value_relation] is deliberately defined on the locally nameless type,
    rather than on a syntactically substituted type.  [beta] interprets bound
    variables and [rho] interprets free variables. *)
Fixpoint value_relation (T : ty) (beta : list (relation tm))
    (rho : relational_environment) (v1 v2 : tm) : Prop :=
  value v1 /\ value v2 /\
  match T with
  | Ty_BVar i =>
      match nth_error beta i with Some R => R v1 v2 | None => False end
  | Ty_FVar X =>
      match rho X with
      | Some p => binding_relation p v1 v2
      | None => False
      end
  | Ty_Arrow T1 T2 => forall a1 a2,
      value_relation T1 beta rho a1 a2 ->
      expression_relation (value_relation T2 beta rho)
        (tm_app v1 a1) (tm_app v2 a2)
  | Ty_All T1 => forall U1 U2 (R : relation tm),
      locally_closed_ty U1 -> locally_closed_ty U2 ->
      (forall a1 a2, R a1 a2 -> value a1 /\ value a2) ->
      expression_relation (value_relation T1 (R :: beta) rho)
        (tm_tapp v1 U1) (tm_tapp v2 U2)
  end.

Definition admissible_relation (R : relation tm) : Prop :=
  forall v1 v2, R v1 v2 -> value v1 /\ value v2.

Definition relational_environment_ok (Delta : ty_context)
    (rho : relational_environment) : Prop :=
  (forall X p, rho X = Some p ->
    locally_closed_ty (binding_left_type p) /\
    locally_closed_ty (binding_right_type p) /\
    admissible_relation (binding_relation p)) /\
  (forall X, In X Delta -> exists p, rho X = Some p).

Definition substitutions_related (Gamma : context)
    (rho : relational_environment) (sigma : term_environment) : Prop :=
  (forall x v1 v2, sigma x = Some (v1, v2) -> value v1 /\ value v2) /\
  (forall x T, lookup_context x Gamma = Some T -> exists v1 v2,
    sigma x = Some (v1, v2) /\ value_relation T [] rho v1 v2).

Definition terms_related (T : ty) (rho : relational_environment)
    (e1 e2 : tm) : Prop :=
  expression_relation (value_relation T [] rho) e1 e2.

Lemma in_fold_max : forall x xs,
  In x xs -> x <= fold_right Nat.max 0 xs.
Proof.
  intros x xs; induction xs as [|a xs IH]; simpl; intros H.
  - contradiction.
  - destruct H as [<-|H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall xs,
  ~ In (S (fold_right Nat.max 0 xs)) xs.
Proof.
  intros xs H. pose proof (in_fold_max _ _ H). lia.
Qed.

Lemma lc_ty_open_rec_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; constructor; lia.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma lc_tm_open_rec_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; constructor; lia.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_rec_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H; inversion H; constructor; eauto
    using lc_ty_open_rec_inv.
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - constructor.
  - constructor; assumption.
  - constructor.
    set (X := S (fold_right Nat.max 0 L)).
    apply (lc_ty_open_rec_inv T 0 X).
    apply H0. unfold X. apply fresh_not_in.
Qed.

Lemma typing_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - constructor.
  - constructor.
    + apply wf_ty_locally_closed in H; exact H.
    + set (x := S (fold_right Nat.max 0 L)).
      apply (lc_tm_open_rec_inv t2 0 0 x).
      apply H1. unfold x. apply fresh_not_in.
  - constructor; assumption.
  - constructor.
    set (X := S (fold_right Nat.max 0 L)).
    apply (lc_tm_ty_open_rec_inv t 0 0 X).
    apply H0. unfold X. apply fresh_not_in.
  - constructor.
    + assumption.
    + apply wf_ty_locally_closed in H0; exact H0.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma lc_ty_weaken : forall K K' T,
  lc_ty_at K T -> K <= K' -> lc_ty_at K' T.
Proof.
  intros K K' T H Hle; revert K' Hle; induction H; intros K' Hle.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
Qed.

Lemma lc_tm_weaken : forall K k K' k' t,
  lc_tm_at K k t -> K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k K' k' t H; revert K' k'; induction H;
    intros K' k' HK Hk.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; eauto using lc_ty_weaken; apply IHlc_tm_at; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
  - apply lc_tm_tapp; eauto using lc_ty_weaken.
Qed.

Lemma instantiate_type_lc : forall left rho K T,
  (forall X p, rho X = Some p ->
     locally_closed_ty (binding_left_type p) /\
     locally_closed_ty (binding_right_type p)) ->
  lc_ty_at K T -> lc_ty_at K (instantiate_type left rho T).
Proof.
  intros left rho K T Hrho Hlc; induction Hlc; simpl.
  - constructor; assumption.
  - destruct (rho X) as [p|] eqn:E.
    + specialize (Hrho X p E). destruct Hrho as [HL HR].
      unfold chosen_type. destruct left; eapply lc_ty_weaken; eauto; lia.
    + constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma instantiate_term_lc : forall left rho sigma K k t,
  (forall X p, rho X = Some p ->
     locally_closed_ty (binding_left_type p) /\
     locally_closed_ty (binding_right_type p)) ->
  (forall x v1 v2, sigma x = Some (v1, v2) -> value v1 /\ value v2) ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate_term left rho sigma t).
Proof.
  intros left rho sigma K k t Hrho Hsigma Hlc; induction Hlc; simpl.
  - constructor; assumption.
  - destruct (sigma x) as [[v1 v2]|] eqn:E.
    + specialize (Hsigma x v1 v2 E). destruct Hsigma as [H1 H2].
      unfold chosen_term. destruct left;
        eapply lc_tm_weaken.
      * apply value_locally_closed; exact H1.
      * lia.
      * lia.
      * apply value_locally_closed; exact H2.
      * lia.
      * lia.
    + constructor.
  - constructor; eauto using instantiate_type_lc.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; eauto using instantiate_type_lc.
Qed.

Fixpoint free_term_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => free_term_atoms t1
  | tm_app t1 t2 => free_term_atoms t1 ++ free_term_atoms t2
  | tm_tabs t1 => free_term_atoms t1
  | tm_tapp t1 _ => free_term_atoms t1
  end.

Fixpoint free_type_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => free_type_atoms T1 ++ free_type_atoms T2
  | Ty_All T1 => free_type_atoms T1
  end.

Fixpoint free_type_atoms_in_term (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t1 => free_type_atoms T ++ free_type_atoms_in_term t1
  | tm_app t1 t2 => free_type_atoms_in_term t1 ++ free_type_atoms_in_term t2
  | tm_tabs t1 => free_type_atoms_in_term t1
  | tm_tapp t1 T => free_type_atoms_in_term t1 ++ free_type_atoms T
  end.

Lemma not_in_app_split : forall (x : atom) l1 l2,
  ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros x l1 l2 H; split; intros Hin; apply H; apply in_or_app; auto.
Qed.

Lemma open_ty_rec_lc_identity : forall T K k U,
  lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  intros T K k U Hlc; revert k; induction Hlc as
    [K i Hi|K X|K A B HA IHA HB IHB|K T HT IH]; intros j Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - rewrite IHA by exact Hle. rewrite IHB by exact Hle. reflexivity.
  - rewrite IH by lia. reflexivity.
Qed.

Lemma open_tm_rec_lc_identity : forall t K k j u,
  lc_tm_at K k t -> k <= j -> open_tm_rec j u t = t.
Proof.
  induction t; intros K k j u Hlc Hle; inversion Hlc; simpl.
  - destruct (Nat.eqb j n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal. eapply IHt; eauto; lia.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma open_tm_ty_rec_lc_identity : forall t K k J U,
  lc_tm_at K k t -> K <= J -> open_tm_ty_rec J U t = t.
Proof.
  induction t; intros K k J U Hlc Hle; inversion Hlc; simpl; try reflexivity.
  - f_equal.
    + eapply open_ty_rec_lc_identity; eauto.
    + eapply IHt; eauto.
  - f_equal; eauto.
  - f_equal. eapply IHt; eauto; lia.
  - f_equal.
    + eapply IHt; eauto.
    + eapply open_ty_rec_lc_identity; eauto.
Qed.

Lemma instantiate_open_term : forall t k x left rho sigma a1 a2,
  (forall y v1 v2, sigma y = Some (v1,v2) -> value v1 /\ value v2) ->
  ~ In x (free_term_atoms t) ->
  instantiate_term left rho (extend_term_environment sigma x (a1,a2))
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (chosen_term left (a1,a2))
    (instantiate_term left rho sigma t).
Proof.
  induction t; intros k x left rho sigma a1 a2 Hsigma Hfresh; simpl in *.
  - destruct (Nat.eqb k n).
    + simpl. unfold extend_term_environment. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (x <> a) by (intro; subst; apply Hfresh; auto).
    unfold extend_term_environment. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    + destruct (sigma a) as [[v1 v2]|] eqn:Es; simpl; [|reflexivity].
      specialize (Hsigma a v1 v2 Es) as [Hv1 Hv2].
      unfold chosen_term. destruct left; symmetry.
      * eapply open_tm_rec_lc_identity.
        -- apply value_locally_closed; exact Hv1.
        -- lia.
      * eapply open_tm_rec_lc_identity.
        -- apply value_locally_closed; exact Hv2.
        -- lia.
  - f_equal; eauto.
  - apply not_in_app_split in Hfresh as [H1 H2]. f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma instantiate_open_type : forall T k X left rho p,
  (forall Y q, rho Y = Some q ->
    locally_closed_ty (binding_left_type q) /\
    locally_closed_ty (binding_right_type q)) ->
  ~ In X (free_type_atoms T) ->
  instantiate_type left (extend_relational_environment rho X p)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k (chosen_type left p) (instantiate_type left rho T).
Proof.
  induction T; intros k X left rho p Hrho Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold extend_relational_environment. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by (intro; subst; apply Hfresh; auto).
    unfold extend_relational_environment. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    + destruct (rho a) as [q|] eqn:Eq; simpl; [|reflexivity].
      specialize (Hrho a q Eq) as [HL HR]. unfold chosen_type.
      destruct left; symmetry.
      * eapply open_ty_rec_lc_identity; [exact HL|lia].
      * eapply open_ty_rec_lc_identity; [exact HR|lia].
  - apply not_in_app_split in Hfresh as [H1 H2]. f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma instantiate_open_type_in_term : forall t K X left rho sigma p,
  (forall Y q, rho Y = Some q ->
    locally_closed_ty (binding_left_type q) /\
    locally_closed_ty (binding_right_type q)) ->
  (forall y v1 v2, sigma y = Some (v1,v2) -> value v1 /\ value v2) ->
  ~ In X (free_type_atoms_in_term t) ->
  instantiate_term left (extend_relational_environment rho X p) sigma
    (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K (chosen_type left p)
    (instantiate_term left rho sigma t).
Proof.
  induction t; intros K X left rho sigma p Hrho Hsigma Hfresh; simpl in *.
  - reflexivity.
  - destruct (sigma a) as [[v1 v2]|] eqn:E; simpl; [|reflexivity].
    specialize (Hsigma a v1 v2 E) as [H1 H2]. unfold chosen_term.
    destruct left; symmetry.
    + eapply open_tm_ty_rec_lc_identity.
      * apply value_locally_closed; exact H1.
      * lia.
    + eapply open_tm_ty_rec_lc_identity.
      * apply value_locally_closed; exact H2.
      * lia.
  - apply not_in_app_split in Hfresh as [H1 H2]. f_equal.
    + apply instantiate_open_type; assumption.
    + eauto.
  - apply not_in_app_split in Hfresh as [H1 H2]. f_equal; eauto.
  - f_equal; eauto.
  - apply not_in_app_split in Hfresh as [H1 H2]. f_equal; eauto using instantiate_open_type.
Qed.

Lemma extend_relational_environment_ok : forall Delta rho X p,
  relational_environment_ok Delta rho ->
  locally_closed_ty (binding_left_type p) ->
  locally_closed_ty (binding_right_type p) ->
  admissible_relation (binding_relation p) ->
  relational_environment_ok (X :: Delta)
    (extend_relational_environment rho X p).
Proof.
  intros Delta rho X p [Hclosed Hdom] HL HR Hadm; split.
  - intros Y q E. unfold extend_relational_environment in E.
    destruct (Nat.eqb X Y) eqn:EQ.
    + inversion E; subst; auto.
    + eauto.
  - intros Y [<-|Hin].
    + exists p. unfold extend_relational_environment. rewrite Nat.eqb_refl. reflexivity.
    + destruct (Hdom Y Hin) as [q E].
      unfold extend_relational_environment.
      destruct (Nat.eqb X Y) eqn:EQ.
      * exists p. reflexivity.
      * exists q. exact E.
Qed.

Lemma value_relation_values : forall T beta rho v1 v2,
  value_relation T beta rho v1 v2 -> value v1 /\ value v2.
Proof. destruct T; simpl; tauto. Qed.

Lemma extend_substitutions_related : forall Gamma rho sigma x T a1 a2,
  substitutions_related Gamma rho sigma ->
  value_relation T [] rho a1 a2 ->
  substitutions_related (update Gamma x T) rho
    (extend_term_environment sigma x (a1,a2)).
Proof.
  intros Gamma rho sigma x T a1 a2 [Hclosed Hrel] Ha; split.
  - intros y v1 v2 E. unfold extend_term_environment in E.
    destruct (Nat.eqb x y) eqn:EQ.
    + inversion E; subst. eapply value_relation_values; eauto.
    + eauto.
  - intros y U Hlookup. simpl in Hlookup.
    destruct (Nat.eqb y x) eqn:EQ.
    + apply Nat.eqb_eq in EQ; subst. inversion Hlookup; subst.
      exists a1, a2; split.
      * unfold extend_term_environment. rewrite Nat.eqb_refl. reflexivity.
      * exact Ha.
    + destruct (Hrel y U Hlookup) as [v1 [v2 [E Hr]]].
      exists v1, v2; split; [|exact Hr].
      unfold extend_term_environment. rewrite Nat.eqb_sym, EQ. exact E.
Qed.

Lemma expression_relation_iff : forall R S e1 e2,
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  expression_relation R e1 e2 <-> expression_relation S e1 e2.
Proof.
  intros R S e1 e2 Hiff; split;
    intros (v1 & v2 & H1 & H2 & Hv1 & Hv2 & HR);
    exists v1, v2; repeat split; auto; apply Hiff; assumption.
Qed.

Definition relation_stacks_agree (k : nat)
    (b1 b2 : list (relation tm)) : Prop :=
  forall i, i < k -> nth_error b1 i = nth_error b2 i.

Lemma relation_stacks_agree_cons : forall k R b1 b2,
  relation_stacks_agree k b1 b2 ->
  relation_stacks_agree (S k) (R :: b1) (R :: b2).
Proof.
  intros k R b1 b2 H i Hi. destruct i; simpl; auto.
  apply H; lia.
Qed.

Lemma value_relation_stack_extensional : forall T k b1 b2 rho,
  lc_ty_at k T -> relation_stacks_agree k b1 b2 ->
  forall v1 v2,
    value_relation T b1 rho v1 v2 <-> value_relation T b2 rho v1 v2.
Proof.
  induction T; intros k b1 b2 rho Hlc Hag v1 v2; inversion Hlc; subst; simpl.
  - rewrite (Hag n H1). tauto.
  - tauto.
  - assert (lc_ty_at k T1) as Hlc1 by (inversion Hlc; assumption).
    assert (lc_ty_at k T2) as Hlc2 by (inversion Hlc; assumption).
    specialize (IHT1 k b1 b2 rho Hlc1 Hag).
    specialize (IHT2 k b1 b2 rho Hlc2 Hag).
    split; intros (Hv1 & Hv2 & Hfun); repeat split; auto;
      intros a1 a2 Ha.
    + eapply (proj1 (expression_relation_iff
        (value_relation T2 b1 rho) (value_relation T2 b2 rho)
        (tm_app v1 a1) (tm_app v2 a2) IHT2)).
      exact (Hfun a1 a2 (proj2 (IHT1 a1 a2) Ha)).
    + eapply (proj1 (expression_relation_iff
        (value_relation T2 b2 rho) (value_relation T2 b1 rho)
        (tm_app v1 a1) (tm_app v2 a2)
        (fun x y => iff_sym (IHT2 x y)))).
      exact (Hfun a1 a2 (proj1 (IHT1 a1 a2) Ha)).
  - assert (lc_ty_at (S k) T) as Hbody by (inversion Hlc; assumption).
    split; intros (Hv1 & Hv2 & Hall); repeat split; auto;
      intros U1 U2 R HU1 HU2 Hadm.
    + pose proof (IHT (S k) (R :: b1) (R :: b2) rho Hbody
        (relation_stacks_agree_cons k R b1 b2 Hag)) as IH.
      eapply (proj1 (expression_relation_iff
        (value_relation T (R :: b1) rho)
        (value_relation T (R :: b2) rho)
        (tm_tapp v1 U1) (tm_tapp v2 U2) IH)).
      apply Hall; assumption.
    + pose proof (IHT (S k) (R :: b1) (R :: b2) rho Hbody
        (relation_stacks_agree_cons k R b1 b2 Hag)) as IH.
      eapply (proj2 (expression_relation_iff
        (value_relation T (R :: b1) rho)
        (value_relation T (R :: b2) rho)
        (tm_tapp v1 U1) (tm_tapp v2 U2) IH)).
      apply Hall; assumption.
Qed.

Corollary value_relation_closed_stack : forall T rho b1 b2 v1 v2,
  locally_closed_ty T ->
  (value_relation T b1 rho v1 v2 <-> value_relation T b2 rho v1 v2).
Proof.
  intros. eapply value_relation_stack_extensional; eauto.
  intros i Hi; lia.
Qed.

Fixpoint insert_relation (k : nat) (R : relation tm)
    (beta : list (relation tm)) : list (relation tm) :=
  match k, beta with
  | 0, _ => R :: beta
  | S k', Q :: beta' => Q :: insert_relation k' R beta'
  | S _, [] => []
  end.

Lemma nth_error_insert_before : forall beta k R i,
  i < k -> k <= length beta ->
  nth_error (insert_relation k R beta) i = nth_error beta i.
Proof.
  induction beta as [|Q beta IH]; destruct k; intros R i Hi Hlen; simpl in *; try lia.
  destruct i; simpl; auto. apply IH; lia.
Qed.

Lemma nth_error_insert_at : forall beta k R,
  k <= length beta -> nth_error (insert_relation k R beta) k = Some R.
Proof.
  induction beta as [|Q beta IH]; intros k R Hlen; destruct k; simpl in *; auto; try lia.
  apply IH; lia.
Qed.

Lemma value_relation_open_bound : forall T k U beta rho,
  lc_ty_at (S k) T -> locally_closed_ty U -> k <= length beta ->
  forall v1 v2,
  value_relation (open_ty_rec k U T) beta rho v1 v2 <->
  value_relation T
    (insert_relation k (value_relation U [] rho) beta) rho v1 v2.
Proof.
  induction T; intros k U beta rho Hlc HU Hlen v1 v2; inversion Hlc; subst.
  - simpl. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      rewrite nth_error_insert_at by exact Hlen.
      pose proof (value_relation_closed_stack U rho beta [] v1 v2 HU) as Hstack.
      pose proof (value_relation_values U [] rho v1 v2) as Hvals.
      simpl. tauto.
    + apply Nat.eqb_neq in E.
      assert (n < k) by lia.
      rewrite nth_error_insert_before by assumption. simpl. tauto.
  - simpl. tauto.
  - assert (lc_ty_at (S k) T1) as Hlc1 by (inversion Hlc; assumption).
    assert (lc_ty_at (S k) T2) as Hlc2 by (inversion Hlc; assumption).
    pose proof (IHT1 k U beta rho Hlc1 HU Hlen) as IH1.
    pose proof (IHT2 k U beta rho Hlc2 HU Hlen) as IH2.
    simpl; split; intros (Hv1 & Hv2 & Hfun); repeat split; auto;
      intros a1 a2 Ha.
    + eapply (proj1 (expression_relation_iff
        (value_relation (open_ty_rec k U T2) beta rho)
        (value_relation T2
          (insert_relation k (value_relation U [] rho) beta) rho)
        (tm_app v1 a1) (tm_app v2 a2) IH2)).
      exact (Hfun a1 a2 (proj2 (IH1 a1 a2) Ha)).
    + eapply (proj2 (expression_relation_iff
        (value_relation (open_ty_rec k U T2) beta rho)
        (value_relation T2
          (insert_relation k (value_relation U [] rho) beta) rho)
        (tm_app v1 a1) (tm_app v2 a2) IH2)).
      exact (Hfun a1 a2 (proj1 (IH1 a1 a2) Ha)).
  - assert (lc_ty_at (S (S k)) T) as Hbody by (inversion Hlc; assumption).
    simpl; split; intros (Hv1 & Hv2 & Hall); repeat split; auto;
      intros U1 U2 R HU1 HU2 Hadm.
    + pose proof (IHT (S k) U (R :: beta) rho Hbody HU) as IH.
      specialize (IH ltac:(simpl; lia)).
      eapply (proj1 (expression_relation_iff _ _ _ _ IH)).
      apply Hall; assumption.
    + pose proof (IHT (S k) U (R :: beta) rho Hbody HU) as IH.
      specialize (IH ltac:(simpl; lia)).
      eapply (proj2 (expression_relation_iff _ _ _ _ IH)).
      apply Hall; assumption.
Qed.

Corollary value_relation_open : forall T U rho v1 v2,
  lc_ty_at 1 T -> locally_closed_ty U ->
  (value_relation (open_ty T U) [] rho v1 v2 <->
   value_relation T [value_relation U [] rho] rho v1 v2).
Proof.
  intros. apply value_relation_open_bound; auto.
Qed.

Lemma value_relation_open_free : forall T k X p beta rho,
  lc_ty_at (S k) T -> ~ In X (free_type_atoms T) ->
  k <= length beta -> forall v1 v2,
  value_relation (open_ty_rec k (Ty_FVar X) T) beta
    (extend_relational_environment rho X p) v1 v2 <->
  value_relation T (insert_relation k (binding_relation p) beta) rho v1 v2.
Proof.
  induction T; intros k X p beta rho Hlc Hfresh Hlen v1 v2;
    inversion Hlc; subst; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      unfold extend_relational_environment.
      destruct (Nat.eqb X X) eqn:EX.
      * cbn [value_relation]. rewrite EX.
        rewrite nth_error_insert_at by exact Hlen. reflexivity.
      * apply Nat.eqb_neq in EX; contradiction.
    + apply Nat.eqb_neq in E. assert (n < k) by lia.
      rewrite nth_error_insert_before by assumption. simpl. tauto.
  - assert (X <> a) by (intro; subst; apply Hfresh; auto).
    unfold extend_relational_environment. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    + tauto.
  - apply not_in_app_split in Hfresh as [Hf1 Hf2].
    assert (lc_ty_at (S k) T1) as Hlc1 by (inversion Hlc; assumption).
    assert (lc_ty_at (S k) T2) as Hlc2 by (inversion Hlc; assumption).
    pose proof (IHT1 k X p beta rho Hlc1 Hf1 Hlen) as IH1.
    pose proof (IHT2 k X p beta rho Hlc2 Hf2 Hlen) as IH2.
    split; intros (Hv1 & Hv2 & Hfun); repeat split; auto;
      intros a1 a2 Ha.
    + eapply (proj1 (expression_relation_iff _ _ _ _ IH2)).
      exact (Hfun a1 a2 (proj2 (IH1 a1 a2) Ha)).
    + eapply (proj2 (expression_relation_iff _ _ _ _ IH2)).
      exact (Hfun a1 a2 (proj1 (IH1 a1 a2) Ha)).
  - assert (lc_ty_at (S (S k)) T) as Hbody by (inversion Hlc; assumption).
    split; intros (Hv1 & Hv2 & Hall); repeat split; auto;
      intros U1 U2 R HU1 HU2 Hadm.
    + pose proof (IHT (S k) X p (R :: beta) rho Hbody Hfresh) as IH.
      specialize (IH ltac:(simpl; lia)).
      eapply (proj1 (expression_relation_iff _ _ _ _ IH)).
      apply Hall; assumption.
    + pose proof (IHT (S k) X p (R :: beta) rho Hbody Hfresh) as IH.
      specialize (IH ltac:(simpl; lia)).
      eapply (proj2 (expression_relation_iff _ _ _ _ IH)).
      apply Hall; assumption.
Qed.

Corollary value_relation_open_free_top : forall T X p rho v1 v2,
  lc_ty_at 1 T -> ~ In X (free_type_atoms T) ->
  (value_relation (open_ty T (Ty_FVar X)) []
      (extend_relational_environment rho X p) v1 v2 <->
   value_relation T [binding_relation p] rho v1 v2).
Proof.
  intros. apply value_relation_open_free; auto.
Qed.

Lemma lc_ty_open_rec : forall T k U,
  lc_ty_at (S k) T -> lc_ty_at k U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; inversion HT; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + exact HU.
    + apply Nat.eqb_neq in E. apply lc_ty_bvar; lia.
  - constructor.
  - constructor; eauto.
  - apply lc_ty_all. eapply IHT; eauto.
    eapply lc_ty_weaken; eauto; lia.
Qed.

Lemma typing_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H.
  - apply wf_ty_locally_closed in H0; exact H0.
  - apply lc_ty_arrow.
    + eapply wf_ty_locally_closed; exact H.
    + set (x := S (fold_right Nat.max 0 L)).
      apply (H1 x). unfold x. apply fresh_not_in.
  - inversion IHhas_type1; assumption.
  - constructor.
    set (X := S (fold_right Nat.max 0 L)).
    apply (lc_ty_open_rec_inv T 0 X).
    apply H0. unfold X. apply fresh_not_in.
  - inversion IHhas_type; subst.
    eapply lc_ty_open_rec.
    + exact H3.
    + apply wf_ty_locally_closed in H0. exact H0.
Qed.

Lemma expression_relation_prepend : forall R e1 e2 e1' e2',
  e1' -->* e1 -> e2' -->* e2 -> expression_relation R e1 e2 ->
  expression_relation R e1' e2'.
Proof.
  intros R e1 e2 e1' e2' H1 H2
    (v1 & v2 & E1 & E2 & Hv1 & Hv2 & HR).
  exists v1, v2; repeat split; eauto using multi_trans.
Qed.

Lemma value_relation_admissible : forall T beta rho,
  admissible_relation (value_relation T beta rho).
Proof. intros T beta rho v1 v2 H; eapply value_relation_values; eauto. Qed.

Lemma value_relation_fresh_environment : forall T X p beta rho,
  ~ In X (free_type_atoms T) -> forall v1 v2,
  value_relation T beta (extend_relational_environment rho X p) v1 v2 <->
  value_relation T beta rho v1 v2.
Proof.
  induction T; intros X p beta rho Hfresh v1 v2; simpl in *.
  - tauto.
  - assert (X <> a) by (intro; subst; apply Hfresh; auto).
    unfold extend_relational_environment. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    + tauto.
  - apply not_in_app_split in Hfresh as [Hf1 Hf2].
    pose proof (IHT1 X p beta rho Hf1) as IH1.
    pose proof (IHT2 X p beta rho Hf2) as IH2.
    split; intros (Hv1 & Hv2 & Hfun); repeat split; auto;
      intros a1 a2 Ha.
    + eapply (proj1 (expression_relation_iff _ _ _ _ IH2)).
      exact (Hfun a1 a2 (proj2 (IH1 a1 a2) Ha)).
    + eapply (proj2 (expression_relation_iff _ _ _ _ IH2)).
      exact (Hfun a1 a2 (proj1 (IH1 a1 a2) Ha)).
  - split; intros (Hv1 & Hv2 & Hall); repeat split; auto;
      intros U1 U2 R HU1 HU2 Hadm.
    + pose proof (IHT X p (R :: beta) rho Hfresh) as IH.
      eapply (proj1 (expression_relation_iff _ _ _ _ IH)).
      apply Hall; assumption.
    + pose proof (IHT X p (R :: beta) rho Hfresh) as IH.
      eapply (proj2 (expression_relation_iff _ _ _ _ IH)).
      apply Hall; assumption.
Qed.

Fixpoint free_type_atoms_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => free_type_atoms T ++ free_type_atoms_context Gamma'
  end.

Lemma lookup_context_free_atoms : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (free_type_atoms T) ->
  In X (free_type_atoms_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlook Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. apply in_or_app; auto.
    + apply in_or_app; right; eauto.
Qed.

Lemma substitutions_related_extend_type : forall Gamma rho sigma X p,
  substitutions_related Gamma rho sigma ->
  ~ In X (free_type_atoms_context Gamma) ->
  substitutions_related Gamma (extend_relational_environment rho X p) sigma.
Proof.
  intros Gamma rho sigma X p [Hclosed Hrel] Hfresh; split; auto.
  intros x T Hlook. destruct (Hrel x T Hlook) as (v1 & v2 & E & HR).
  exists v1, v2; split; auto.
  assert (Hnot : ~ In X (free_type_atoms T)).
  { intro Hin. apply Hfresh. eapply lookup_context_free_atoms; eauto. }
  exact (proj2 (value_relation_fresh_environment T X p [] rho Hnot v1 v2) HR).
Qed.

(** The fundamental theorem.  Its proof follows the five constructors of
    [has_type], with one bullet for each typing rule. *)
Theorem fundamental_theorem : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall rho sigma,
  relational_environment_ok Delta rho ->
  substitutions_related Gamma rho sigma ->
  terms_related T rho
    (instantiate_term true rho sigma t)
    (instantiate_term false rho sigma t).
Proof.
  intros Delta Gamma t T Hty; induction Hty; intros rho sigma Hrho Hsigma.
  - destruct Hsigma as [Hsclosed Hsrel].
    destruct (Hsrel x T H) as (v1 & v2 & E & HR).
    simpl. rewrite E. exists v1, v2; repeat split; auto using multi_refl.
    all: eapply value_relation_values; eauto.
  - destruct Hrho as [Hrclosed Hrdom].
    destruct Hsigma as [Hsclosed Hsrel].
    assert (Hlc0 : locally_closed_tm (tm_abs T1 t2)).
    { eapply typing_locally_closed. econstructor; eauto. }
    assert (Hlcl : locally_closed_tm
      (instantiate_term true rho sigma (tm_abs T1 t2))).
    { eapply instantiate_term_lc; eauto. }
    assert (Hlcr : locally_closed_tm
      (instantiate_term false rho sigma (tm_abs T1 t2))).
    { eapply instantiate_term_lc; eauto. }
    assert (Hvl : value (instantiate_term true rho sigma (tm_abs T1 t2)))
      by (simpl; constructor; exact Hlcl).
    assert (Hvr : value (instantiate_term false rho sigma (tm_abs T1 t2)))
      by (simpl; constructor; exact Hlcr).
    exists (instantiate_term true rho sigma (tm_abs T1 t2)),
      (instantiate_term false rho sigma (tm_abs T1 t2)).
    repeat split; auto using multi_refl.
    intros a1 a2 Ha.
    set (x := S (fold_right Nat.max 0 (L ++ free_term_atoms t2))).
    assert (Hxall : ~ In x (L ++ free_term_atoms t2)).
    { unfold x; apply fresh_not_in. }
    apply not_in_app_split in Hxall as [HxL Hxt].
    pose proof (extend_substitutions_related Gamma rho sigma x T1 a1 a2)
      as Hext.
    specialize (Hext (conj Hsclosed Hsrel) Ha).
    specialize (H1 x HxL rho
      (extend_term_environment sigma x (a1,a2))
      (conj Hrclosed Hrdom) Hext).
    rewrite (instantiate_open_term t2 0 x true rho sigma a1 a2
      Hsclosed Hxt) in H1.
    rewrite (instantiate_open_term t2 0 x false rho sigma a1 a2
      Hsclosed Hxt) in H1.
    eapply expression_relation_prepend; [| |exact H1].
    + apply multi_one. simpl. apply ST_AppAbs; auto.
      eapply value_relation_values; eauto.
    + apply multi_one. simpl. apply ST_AppAbs; auto.
      eapply value_relation_values; eauto.
  - specialize (IHHty1 rho sigma Hrho Hsigma).
    specialize (IHHty2 rho sigma Hrho Hsigma).
    destruct IHHty1 as (f1 & f2 & Ef1 & Ef2 & Hvf1 & Hvf2 & Hfrel).
    destruct IHHty2 as (a1 & a2 & Ea1 & Ea2 & Hva1 & Hva2 & Harel).
    assert (Hlcargl : locally_closed_tm (instantiate_term true rho sigma t2)).
    { eapply instantiate_term_lc.
      - intros X p E. destruct Hrho as [HC _]. specialize (HC X p E); tauto.
      - destruct Hsigma as [HC _]. exact HC.
      - eapply typing_locally_closed; eauto. }
    assert (Hlcarg2 : locally_closed_tm (instantiate_term false rho sigma t2)).
    { eapply instantiate_term_lc.
      - intros X p E. destruct Hrho as [HC _]. specialize (HC X p E); tauto.
      - destruct Hsigma as [HC _]. exact HC.
      - eapply typing_locally_closed; eauto. }
    destruct Hfrel as [_ [_ Happly]].
    specialize (Happly a1 a2 Harel).
    eapply expression_relation_prepend; [| |exact Happly].
    + eapply multi_trans.
      * apply multi_app_l; eauto.
      * apply multi_app_r; eauto.
    + eapply multi_trans.
      * apply multi_app_l; eauto.
      * apply multi_app_r; eauto.
  - destruct Hrho as [Hrclosed Hrdom].
    destruct Hsigma as [Hsclosed Hsrel].
    assert (Hlc0 : locally_closed_tm (tm_tabs t)).
    { eapply typing_locally_closed. econstructor; eauto. }
    assert (Hlcl : locally_closed_tm
      (instantiate_term true rho sigma (tm_tabs t))).
    { eapply instantiate_term_lc; eauto. }
    assert (Hlcr : locally_closed_tm
      (instantiate_term false rho sigma (tm_tabs t))).
    { eapply instantiate_term_lc; eauto. }
    assert (Hvl : value (instantiate_term true rho sigma (tm_tabs t)))
      by (simpl; constructor; exact Hlcl).
    assert (Hvr : value (instantiate_term false rho sigma (tm_tabs t)))
      by (simpl; constructor; exact Hlcr).
    exists (instantiate_term true rho sigma (tm_tabs t)),
      (instantiate_term false rho sigma (tm_tabs t)).
    repeat split; auto using multi_refl.
    intros U1 U2 R HU1 HU2 Hadm.
    set (p := mk_relational_binding U1 U2 R).
    set (X := S (fold_right Nat.max 0
      (L ++ free_type_atoms_in_term t ++ free_type_atoms T ++
       free_type_atoms_context Gamma))).
    assert (Hfresh : ~ In X
      (L ++ free_type_atoms_in_term t ++ free_type_atoms T ++
       free_type_atoms_context Gamma)).
    { unfold X; apply fresh_not_in. }
    repeat rewrite in_app_iff in Hfresh.
    apply Decidable.not_or in Hfresh as [HxL Hfresh].
    apply Decidable.not_or in Hfresh as [Hxt Hfresh].
    apply Decidable.not_or in Hfresh as [HxT HxG].
    assert (Hrhoext : relational_environment_ok (X :: Delta)
      (extend_relational_environment rho X p)).
    { apply extend_relational_environment_ok; unfold p; simpl; auto. }
    assert (Hsigext : substitutions_related Gamma
      (extend_relational_environment rho X p) sigma).
    { apply substitutions_related_extend_type; auto. }
    specialize (H0 X HxL (extend_relational_environment rho X p)
      sigma Hrhoext Hsigext).
    rewrite (instantiate_open_type_in_term t 0 X true rho sigma p
      Hrclosed Hsclosed Hxt) in H0.
    rewrite (instantiate_open_type_in_term t 0 X false rho sigma p
      Hrclosed Hsclosed Hxt) in H0.
    apply (proj1 (expression_relation_iff _ _ _ _
      (value_relation_open_free_top T X p rho))); auto.
    eapply expression_relation_prepend; [| |exact H0].
    + apply multi_one. simpl. apply ST_TAppTabs; auto.
    + apply multi_one. simpl. apply ST_TAppTabs; auto.
  - specialize (IHHty rho sigma Hrho Hsigma).
    destruct IHHty as (f1 & f2 & Ef1 & Ef2 & Hvf1 & Hvf2 & Hfrel).
    destruct Hfrel as [_ [_ Hall]].
    assert (HUl : locally_closed_ty (instantiate_type true rho U)).
    { eapply instantiate_type_lc.
      - intros X p E. destruct Hrho as [HC _]. specialize (HC X p E); tauto.
      - apply wf_ty_locally_closed in H0. exact H0. }
    assert (HUr : locally_closed_ty (instantiate_type false rho U)).
    { eapply instantiate_type_lc.
      - intros X p E. destruct Hrho as [HC _]. specialize (HC X p E); tauto.
      - apply wf_ty_locally_closed in H0. exact H0. }
    specialize (Hall (instantiate_type true rho U)
      (instantiate_type false rho U) (value_relation U [] rho)
      HUl HUr (value_relation_admissible U [] rho)).
    assert (Hbody : lc_ty_at 1 T).
    { pose proof (typing_type_locally_closed _ _ _ _ Hty) as HAll.
      inversion HAll; assumption. }
    apply (proj2 (expression_relation_iff _ _ _ _
      (value_relation_open T U rho))); auto using wf_ty_locally_closed.
    eapply expression_relation_prepend; [| |exact Hall].
    + apply multi_tapp; assumption.
    + apply multi_tapp; assumption.
Qed.

End SystemFParametricityTask.
