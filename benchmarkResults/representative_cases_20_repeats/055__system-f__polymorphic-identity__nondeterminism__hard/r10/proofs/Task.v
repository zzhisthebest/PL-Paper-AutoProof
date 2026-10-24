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

(* ===================================================================== *)
(* Semantic infrastructure: type environments, normalization, atoms.      *)
(* ===================================================================== *)

Definition tyenv := atom -> ty.
Definition predenv := atom -> tm -> Prop.

Definition extend_ty (TE : tyenv) (X : atom) (U : ty) : tyenv :=
  fun Y => if Nat.eqb Y X then U else TE Y.

Definition extend_pred (RE : predenv) (X : atom) (P : tm -> Prop) : predenv :=
  fun Y => if Nat.eqb Y X then P else RE Y.

Lemma extend_ty_same : forall TE X U,
  extend_ty TE X U X = U.
Proof. intros. unfold extend_ty. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_ty_other : forall TE X Y U,
  X <> Y -> extend_ty TE X U Y = TE Y.
Proof.
  intros. unfold extend_ty. destruct (Nat.eqb Y X) eqn:E; auto.
  exfalso. apply Nat.eqb_eq in E. auto.
Qed.

Lemma extend_pred_same : forall RE X P,
  extend_pred RE X P X = P.
Proof. intros. unfold extend_pred. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_pred_other : forall RE X Y P,
  X <> Y -> extend_pred RE X P Y = RE Y.
Proof.
  intros. unfold extend_pred. destruct (Nat.eqb Y X) eqn:E; auto.
  exfalso. apply Nat.eqb_eq in E. auto.
Qed.

Lemma extend_ty_swap : forall TE X Y U V Z,
  X <> Y ->
  extend_ty (extend_ty TE X U) Y V Z = extend_ty (extend_ty TE Y V) X U Z.
Proof.
  intros. unfold extend_ty.
  destruct (Nat.eqb Z Y) eqn:E1; destruct (Nat.eqb Z X) eqn:E2; auto.
  exfalso. apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. subst. auto.
Qed.

Lemma extend_ty_idem : forall TE X U Z,
  extend_ty (extend_ty TE X U) X U Z = extend_ty TE X U Z.
Proof.
  intros. unfold extend_ty. destruct (Nat.eqb Z X); reflexivity.
Qed.

(* Normalization of types and terms by a type substitution. *)
Fixpoint norm_ty (TE : tyenv) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => TE X
  | Ty_Arrow A B => Ty_Arrow (norm_ty TE A) (norm_ty TE B)
  | Ty_All B => Ty_All (norm_ty TE B)
  end.

Fixpoint norm_tm (TE : tyenv) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (norm_ty TE T) (norm_tm TE b)
  | tm_app f a => tm_app (norm_tm TE f) (norm_tm TE a)
  | tm_tabs b => tm_tabs (norm_tm TE b)
  | tm_tapp f T => tm_tapp (norm_tm TE f) (norm_ty TE T)
  | tm_choice a b => tm_choice (norm_tm TE a) (norm_tm TE b)
  end.

(* The free type-variable names occurring in a type, and the free type-variable
   names occurring in the type annotations of a term. *)
Fixpoint ty_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_atoms A ++ ty_atoms B
  | Ty_All B => ty_atoms B
  end.

Fixpoint tm_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T b => ty_atoms T ++ tm_atoms b
  | tm_app f a => tm_atoms f ++ tm_atoms a
  | tm_tabs b => tm_atoms b
  | tm_tapp f T => tm_atoms f ++ ty_atoms T
  | tm_choice a b => tm_atoms a ++ tm_atoms b
  end.

Definition closed_tyenv (TE : tyenv) : Prop :=
  forall X, wf_ty [] (TE X) /\ ty_atoms (TE X) = [].

(* ===================================================================== *)
(* Basic facts about atoms and normalization.                             *)
(* ===================================================================== *)

Lemma in_app_or' : forall A (l1 l2 : list A) x,
  In x (l1 ++ l2) -> In x l1 \/ In x l2.
Proof. intros. apply in_app_or. auto. Qed.

Lemma norm_ty_of_no_atoms : forall TE T,
  ty_atoms T = [] -> norm_ty TE T = T.
Proof.
  intros TE T. revert T. fix IH 1. intros [i|X|A B|B0]; simpl; intros H.
  - reflexivity.
  - simpl in H. inversion H.
  - pose proof (app_eq_nil _ _ H) as [H1 H2].
    rewrite (IH A H1), (IH B H2). reflexivity.
  - rewrite (IH B0 H). reflexivity.
Qed.

Lemma norm_ty_no_atoms : forall TE T,
  ty_atoms (norm_ty TE T) = [] ->
  norm_ty TE (norm_ty TE T) = norm_ty TE T.
Proof.
  intros TE T. revert TE.
  induction T as [i | X | A IHA B IHB | B IHB]; intros TE H; simpl in *.
  - reflexivity.
  - apply norm_ty_of_no_atoms. auto.
  - pose proof (app_eq_nil _ _ H) as [H1 H2].
    rewrite (IHA TE H1), (IHB TE H2). reflexivity.
  - rewrite (IHB TE H). reflexivity.
Qed.

Lemma norm_ty_atoms_nil : forall TE T,
  closed_tyenv TE -> ty_atoms (norm_ty TE T) = [].
Proof.
  intros TE T Hc.
  induction T as [i | X | A IHA B IHB | B IHB]; simpl.
  - reflexivity.
  - apply (proj2 (Hc X)).
  - rewrite IHA, IHB. reflexivity.
  - apply IHB.
Qed.

Lemma norm_tm_atoms_nil : forall TE t,
  closed_tyenv TE -> tm_atoms (norm_tm TE t) = [].
Proof.
  intros TE t Hc.
  induction t as [i | x | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite norm_ty_atoms_nil by auto. rewrite IHb. reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - apply IHb.
  - rewrite IHf. rewrite norm_ty_atoms_nil by auto. reflexivity.
  - rewrite IHa, IHb. reflexivity.
Qed.

Lemma norm_ty_idem : forall TE T,
  closed_tyenv TE -> norm_ty TE (norm_ty TE T) = norm_ty TE T.
Proof.
  intros. apply norm_ty_no_atoms. apply norm_ty_atoms_nil. auto.
Qed.

Lemma norm_tm_idem : forall TE t,
  closed_tyenv TE -> norm_tm TE (norm_tm TE t) = norm_tm TE t.
Proof.
  intros TE t Hc. induction t; simpl; auto.
  - rewrite norm_ty_idem by auto. rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt, norm_ty_idem by auto. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* Local-closedness of well-formed types and opening facts.              *)
(* --------------------------------------------------------------------- *)

Definition fresh (L : list atom) : atom := S (fold_right max 0 L).

Lemma fold_max_ge : forall L X, In X L -> X <= fold_right max 0 L.
Proof.
  intros L. induction L as [|a l IH]; intros X Hin.
  - inversion Hin.
  - simpl. destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + pose proof (IH X Hin). apply Nat.le_trans with (fold_right max 0 l); auto.
      apply Nat.le_max_r.
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L Hin. unfold fresh in Hin.
  pose proof (fold_max_ge L _ Hin). lia.
Qed.

Lemma lc_ty_at_mono : forall k k' T,
  k <= k' -> lc_ty_at k T -> lc_ty_at k' T.
Proof.
  intros k k' T. revert k k'.
  induction T as [i | X | A IHA B IHB | B IHB]; intros k k' Hle H.
  - simpl. inversion H as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]. apply lc_ty_bvar. lia.
  - simpl. apply lc_ty_fvar.
  - simpl. inversion H as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]; subst.
    apply lc_ty_arrow.
    + apply IHA with (k := k) (k' := k'); [assumption | assumption].
    + apply IHB with (k := k) (k' := k'); [assumption | assumption].
  - simpl. inversion H as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]; subst.
    apply lc_ty_all.
    apply IHB with (k := S k) (k' := S k'); [lia | assumption].
Qed.

Lemma lc_ty_open_rec_irrel : forall k U T,
  lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  intros k U T. revert k U.
  induction T as [i | X | A IHA B IHB | B IHB]; intros k U H; simpl.
  - destruct (Nat.eqb k i) eqn:E; auto.
    apply Nat.eqb_eq in E. subst.
    inversion H as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]. lia.
  - reflexivity.
  - inversion H as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]; subst.
    rewrite (IHA k U HA), (IHB k U HB). reflexivity.
  - apply f_equal.
    inversion H as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]; subst.
    apply IHB with (k := S k) (U := U). assumption.
Qed.

Lemma lc_ty_open_inv : forall k U T,
  lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  intros k U T. revert k U.
  induction T as [i | X | A IHA B IHB | B IHB]; intros k U H; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + inversion H as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB].
      apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion H as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]; subst.
    apply lc_ty_arrow.
    + apply IHA with (k := k) (U := U). assumption.
    + apply IHB with (k := k) (U := U). assumption.
  - apply lc_ty_all.
    inversion H as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]; subst.
    apply IHB with (k := S k) (U := U). assumption.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all.
    pose proof (fresh_notin (L ++ Delta)) as Hf.
    assert (Hin : ~ In (fresh (L ++ Delta)) L).
    { intro Hc. apply Hf. apply in_or_app. auto. }
    apply lc_ty_open_inv with (U := Ty_FVar (fresh (L ++ Delta))) (k := 0).
    apply H0. auto.
Qed.

Lemma wf_ty_lc_any : forall Delta T, wf_ty Delta T -> forall k, lc_ty_at k T.
Proof.
  intros Delta T H k.
  apply lc_ty_at_mono with (k := 0) (k' := k).
  - lia.
  - apply wf_ty_lc with (Delta := Delta). assumption.
Qed.

Lemma lc_ty_closed_open : forall TE X U k,
  closed_tyenv TE -> open_ty_rec k U (TE X) = TE X.
Proof.
  intros. apply lc_ty_open_rec_irrel.
  apply wf_ty_lc_any with (Delta := []). apply (proj1 (H X)).
Qed.

(* Commutation of normalization with opening / substitution. *)

Lemma norm_ty_open_ty_rec : forall TE k U T,
  closed_tyenv TE ->
  norm_ty TE (open_ty_rec k U T) =
  open_ty_rec k (norm_ty TE U) (norm_ty TE T).
Proof.
  intros TE k U T Hc. revert k.
  induction T as [i | X | A IHA B IHB | B IHB]; intros k; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply lc_ty_closed_open. auto.
  - rewrite IHA, IHB. reflexivity.
  - rewrite IHB. reflexivity.
Qed.

Lemma norm_ty_open_ty : forall TE U T,
  closed_tyenv TE ->
  norm_ty TE (open_ty T U) = open_ty (norm_ty TE T) (norm_ty TE U).
Proof. intros. apply norm_ty_open_ty_rec. auto. Qed.

Lemma norm_tm_open_tm_rec : forall TE k t u,
  norm_tm TE (open_tm_rec k u t) = open_tm_rec k (norm_tm TE u) (norm_tm TE t).
Proof.
  intros TE k t u. revert k u.
  induction t as [i | x | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb];
    intros k u; simpl.
  - destruct (Nat.eqb k i); simpl; reflexivity.
  - reflexivity.
  - rewrite (IHb (S k) u). reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite (IHb k u). reflexivity.
  - rewrite IHf. reflexivity.
  - rewrite IHa, IHb. reflexivity.
Qed.

Lemma norm_tm_open_tm : forall TE t u,
  norm_tm TE (open_tm t u) = open_tm (norm_tm TE t) (norm_tm TE u).
Proof. intros. unfold open_tm. apply norm_tm_open_tm_rec. Qed.

Lemma norm_tm_open_tm_ty_rec : forall TE k U t,
  closed_tyenv TE ->
  norm_tm TE (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (norm_ty TE U) (norm_tm TE t).
Proof.
  intros TE k U t Hc. revert k.
  induction t as [i | x | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb];
    intros k; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply norm_ty_open_ty_rec. auto.
    + apply IHb.
  - f_equal; [apply IHf | apply IHa].
  - f_equal. apply IHb.
  - f_equal.
    + apply IHf.
    + apply norm_ty_open_ty_rec. auto.
  - f_equal; [apply IHa | apply IHb].
Qed.

Lemma norm_tm_open_tm_ty : forall TE U t,
  closed_tyenv TE ->
  norm_tm TE (open_tm_ty t U) = open_tm_ty (norm_tm TE t) (norm_ty TE U).
Proof. intros. apply norm_tm_open_tm_ty_rec. auto. Qed.

Lemma norm_tm_tm_subst : forall TE x s t,
  norm_tm TE (tm_subst x s t) = tm_subst x (norm_tm TE s) (norm_tm TE t).
Proof.
  intros TE x s t. revert x s.
  induction t as [i | y | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb];
    intros x s; simpl.
  - reflexivity.
  - destruct (Nat.eqb x y); reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IHf. reflexivity.
  - rewrite IHa, IHb. reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* Monotonicity and opening lemmas for local closedness.                 *)
(* --------------------------------------------------------------------- *)

Lemma lc_tm_at_mono : forall K K' k k' t,
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  intros K K' k k' t. revert K K' k k'.
  induction t as [i | x | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb];
    intros K K' k k' HK Hk H.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_abs.
    + apply lc_ty_at_mono with (k := K) (k' := K'); assumption.
    + apply IHb with (K := K) (K' := K') (k := S k) (k' := S k'); [assumption | lia | assumption].
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_app.
    + apply IHf with (K := K) (K' := K') (k := k) (k' := k'); assumption.
    + apply IHa with (K := K) (K' := K') (k := k) (k' := k'); assumption.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_tabs.
    apply IHb with (K := S K) (K' := S K') (k := k) (k' := k'); [lia | assumption | assumption].
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_tapp.
    + apply IHf with (K := K) (K' := K') (k := k) (k' := k'); assumption.
    + apply lc_ty_at_mono with (k := K) (k' := K'); assumption.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_choice.
    + apply IHa with (K := K) (K' := K') (k := k) (k' := k'); assumption.
    + apply IHb with (K := K) (K' := K') (k := k) (k' := k'); assumption.
Qed.

Lemma lc_tm_open_rec : forall K j t u,
  lc_tm_at K (S j) t -> lc_tm_at K j u ->
  lc_tm_at K j (open_tm_rec j u t).
Proof.
  intros K j t u. revert K j u.
  induction t as [i | x | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb];
    intros K j u H Hu; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. subst. assumption.
    + apply lc_tm_bvar. apply Nat.eqb_neq in E. inversion H. lia.
  - apply lc_tm_fvar.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                 | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_abs.
    + assumption.
    + eapply IHb.
      * eassumption.
      * eapply lc_tm_at_mono; [| | eassumption]; lia.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                 | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_app; eauto.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                 | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_tabs.
    eapply IHb.
    + eassumption.
    + eapply lc_tm_at_mono; [| | eassumption]; lia.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                 | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_tapp; eauto.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                 | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_choice; eauto.
Qed.

Lemma lc_ty_open_rec : forall K T U,
  lc_ty_at (S K) T -> lc_ty_at K U -> lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K T U. revert K U.
  induction T as [i | X | A IHA B IHB | B IHB]; intros K U H HU; simpl.
  - destruct (Nat.eqb K i) eqn:E.
    + apply Nat.eqb_eq in E. subst. assumption.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E. inversion H. lia.
  - apply lc_ty_fvar.
  - inversion H as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]; subst.
    apply lc_ty_arrow.
    + apply IHA with (K := K) (U := U); auto.
    + apply IHB with (K := K) (U := U); auto.
  - apply lc_ty_all.
    inversion H as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]; subst.
    apply IHB with (K := S K) (U := U).
    + assumption.
    + eapply lc_ty_at_mono; [| eassumption]. lia.
Qed.

Lemma lc_tm_open_ty_rec : forall K k t U,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t U. revert K k U.
  induction t as [i | x | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb];
    intros K k U H HU; simpl.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_abs.
    + apply lc_ty_open_rec with (K := K) (T := T) (U := U); assumption.
    + apply IHb with (K := K) (k := S k) (U := U); assumption.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_app.
    + apply IHf with (K := K) (k := k) (U := U); assumption.
    + apply IHa with (K := K) (k := k) (U := U); assumption.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_tabs.
    apply IHb with (K := S K) (k := k) (U := U).
    + assumption.
    + apply lc_ty_at_mono with (k := K) (k' := S K); [lia | assumption].
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_tapp.
    + apply IHf with (K := K) (k := k) (U := U); assumption.
    + apply lc_ty_open_rec with (K := K) (T := T) (U := U); assumption.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_choice.
    + apply IHa with (K := K) (k := k) (U := U); assumption.
    + apply IHb with (K := K) (k := k) (U := U); assumption.
Qed.

Lemma lc_tm_open_ty : forall t U,
  lc_tm_at 1 0 t -> lc_ty_at 0 U ->
  lc_tm_at 0 0 (open_tm_ty t U).
Proof. intros. apply lc_tm_open_ty_rec; auto. Qed.

Lemma lc_tm_open : forall t u,
  lc_tm_at 0 1 t -> lc_tm_at 0 0 u ->
  lc_tm_at 0 0 (open_tm t u).
Proof. intros. apply lc_tm_open_rec; auto. Qed.

Lemma value_lc : forall v, value v -> lc_tm_at 0 0 v.
Proof. intros v H. inversion H; assumption. Qed.

(* Type substitution inside a term preserves local closedness when the
   substituted type is closed. *)
Lemma ty_subst_lc : forall K T Y U,
  lc_ty_at K T -> lc_ty_at K U -> lc_ty_at K (ty_subst Y U T).
Proof.
  intros K T. revert K. induction T as [i | X | A IHA B IHB | B IHB];
    intros K Y U HT HU; simpl.
  - apply lc_ty_bvar. inversion HT as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]; lia.
  - destruct (Nat.eqb Y X); [assumption | apply lc_ty_fvar].
  - inversion HT as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]; subst.
    apply lc_ty_arrow; auto.
  - apply lc_ty_all.
    inversion HT as [k0 i0 Hlt | k0 X0 | k0 A0 B0 HA HB | k0 B0 HB]; subst.
    apply IHB with (K := S K) (Y := Y) (U := U).
    + assumption.
    + apply lc_ty_at_mono with (k := K) (k' := S K); [lia | assumption].
Qed.

Lemma tm_ty_subst_lc : forall K k t Y U,
  lc_tm_at K k t -> lc_ty_at 0 U -> lc_tm_at K k (tm_ty_subst Y U t).
Proof.
  intros K k t Y U. revert K k Y U.
  induction t as [i | x | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb];
    intros K k Y U H HU; simpl.
  - assumption.
  - apply lc_tm_fvar.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_abs.
    + apply ty_subst_lc with (K := K) (Y := Y) (U := U); auto.
      apply lc_ty_at_mono with (k := 0) (k' := K); [lia | assumption].
    + apply IHb with (K := K) (k := S k) (Y := Y) (U := U); assumption.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_app.
    + apply IHf with (K := K) (k := k) (Y := Y) (U := U); assumption.
    + apply IHa with (K := K) (k := k) (Y := Y) (U := U); assumption.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_tabs.
    apply IHb with (K := S K) (k := k) (Y := Y) (U := U); assumption.
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_tapp.
    + apply IHf with (K := K) (k := k) (Y := Y) (U := U); assumption.
    + apply ty_subst_lc with (K := K) (Y := Y) (U := U); auto.
      apply lc_ty_at_mono with (k := 0) (k' := K); [lia | assumption].
  - inversion H as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                   | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_choice.
    + apply IHa with (K := K) (k := k) (Y := Y) (U := U); assumption.
    + apply IHb with (K := K) (k := k) (Y := Y) (U := U); assumption.
Qed.

(* --------------------------------------------------------------------- *)
(* Step relation: local closedness preservation and multi-step lemmas.    *)
(* --------------------------------------------------------------------- *)

Lemma step_lc : forall t t', t --> t' -> lc_tm_at 0 0 t -> lc_tm_at 0 0 t'.
Proof.
  intros t t' H. induction H; intros Hlc.
  - (* ST_AppAbs *)
    inversion Hlc as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                     | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    inversion Hf as [K1 k1 i1 Hi1 | K1 k1 x1 | K1 k1 T1 b1 HT1 Hb1 | K1 k1 f1 a1 Hf1 Ha1
                     | K1 k1 b1 Hb1 | K1 k1 f1 T1 Hf1 HT1 | K1 k1 a1 b1 Ha1 Hb1]; subst.
    apply lc_tm_open.
    + assumption.
    + apply value_lc. assumption.
  - (* ST_App1 *)
    inversion Hlc as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                     | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_app.
    + apply IHstep. assumption.
    + assumption.
  - (* ST_App2 *)
    inversion Hlc as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                     | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_app.
    + assumption.
    + apply IHstep. assumption.
  - (* ST_TAppTabs *)
    inversion Hlc as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                     | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    inversion Hf as [K1 k1 i1 Hi1 | K1 k1 x1 | K1 k1 T1 b1 HT1 Hb1 | K1 k1 f1 a1 Hf1 Ha1
                     | K1 k1 b1 Hb1 | K1 k1 f1 T1 Hf1 HT1 | K1 k1 a1 b1 Ha1 Hb1]; subst.
    apply lc_tm_open_ty.
    + assumption.
    + assumption.
  - (* ST_TApp *)
    inversion Hlc as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                     | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    apply lc_tm_tapp.
    + apply IHstep. assumption.
    + assumption.
  - (* ST_ChoiceLeft *)
    inversion Hlc as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                     | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    assumption.
  - (* ST_ChoiceRight *)
    inversion Hlc as [K0 k0 i0 Hi | K0 k0 x0 | K0 k0 T0 b0 HT Hb | K0 k0 f0 a0 Hf Ha
                     | K0 k0 b0 Hb | K0 k0 f0 T0 Hf HT | K0 k0 a0 b0 Ha Hb]; subst.
    assumption.
Qed.

Lemma multi_lc : forall t t', t -->* t' -> lc_tm_at 0 0 t -> lc_tm_at 0 0 t'.
Proof.
  intros t t' H. induction H; intros Hlc.
  - assumption.
  - apply IHmulti. apply step_lc with (t := x); auto.
Qed.

Lemma value_step_false : forall v t, value v -> v --> t -> False.
Proof.
  intros v t Hv Hs. induction Hs; inversion Hv.
Qed.

Lemma value_multistep : forall v w, value v -> v -->* w -> w = v.
Proof.
  intros v w Hv Hm. induction Hm.
  - reflexivity.
  - exfalso. eapply value_step_false; eauto.
Qed.

(* Multi-step congruences. *)
Lemma multi_app_l : forall t t' u,
  t -->* t' -> lc_tm_at 0 0 u ->
  tm_app t u -->* tm_app t' u.
Proof.
  intros t t' u H. induction H; intros Hu.
  - apply multi_refl.
  - apply multi_step with (y := tm_app y u).
    + apply ST_App1; assumption.
    + apply IHmulti; assumption.
Qed.

Lemma multi_app_r : forall v t t',
  value v -> t -->* t' ->
  tm_app v t -->* tm_app v t'.
Proof.
  intros v t t' Hv H. induction H.
  - apply multi_refl.
  - apply multi_step with (y := tm_app v y).
    + apply ST_App2; assumption.
    + apply IHmulti.
Qed.

Lemma multi_tapp : forall t t' T,
  t -->* t' -> lc_ty_at 0 T ->
  tm_tapp t T -->* tm_tapp t' T.
Proof.
  intros t t' T H. induction H; intros HT.
  - apply multi_refl.
  - apply multi_step with (y := tm_tapp y T).
    + apply ST_TApp; assumption.
    + apply IHmulti; assumption.
Qed.

Lemma multi_trans : forall t1 t2 t3,
  t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H. induction H; intros H2.
  - assumption.
  - apply multi_step with (y := y).
    + assumption.
    + apply IHmulti. assumption.
Qed.

Lemma multi_app_cong : forall f f' a a',
  f -->* f' -> value f' -> a -->* a' -> lc_tm_at 0 0 a ->
  tm_app f a -->* tm_app f' a'.
Proof.
  intros f f' a a' Hf Hv Ha Hla.
  apply multi_trans with (t2 := tm_app f' a).
  - apply multi_app_l; assumption.
  - apply multi_app_r; assumption.
Qed.

(* --------------------------------------------------------------------- *)
(* The logical predicate.                                                *)
(* --------------------------------------------------------------------- *)

Fixpoint ty_size (T : ty) : nat :=
  match T with
  | Ty_BVar _ => 1
  | Ty_FVar _ => 1
  | Ty_Arrow A B => S (ty_size A + ty_size B)
  | Ty_All B => S (ty_size B)
  end.

Fixpoint sem (f : nat) (L : list atom) (T : ty) (TE : tyenv) (RE : predenv) (t : tm) : Prop :=
  match f with
  | O => False
  | S n =>
    lc_tm_at 0 0 t /\
    exists v, t -->* v /\ value v /\ lc_tm_at 0 0 v /\
      match T with
      | Ty_BVar _ => False
      | Ty_FVar X => RE X (norm_tm TE v)
      | Ty_Arrow A B =>
          exists T0 b, v = tm_abs T0 b /\
            (forall u, value u -> lc_tm_at 0 0 u -> norm_tm TE u = u ->
               sem n L A TE RE u -> sem n L B TE RE (open_tm b u))
      | Ty_All B =>
          exists b, v = tm_tabs b /\
            (forall X U Q, ~ In X L -> wf_ty [] U -> ty_atoms U = [] ->
               sem n (X :: L) (open_ty B (Ty_FVar X))
                 (extend_ty TE X U) (extend_pred RE X Q)
                 (open_tm_ty b (Ty_FVar X)))
      end
  end.

Definition sem_ty (T : ty) (L : list atom) (TE : tyenv) (RE : predenv) (t : tm) : Prop :=
  sem (ty_size T) L T TE RE t.

(* --------------------------------------------------------------------- *)
(* Atoms and the L-invariant.                                            *)
(* --------------------------------------------------------------------- *)

Definition L_ok (L : list atom) (T : ty) (t : tm) : Prop :=
  (forall X, In X (ty_atoms T) -> In X L) /\
  (forall X, In X (tm_atoms t) -> In X L).

Lemma L_ok_all : forall L T t, L_ok L T t ->
  forall X, In X (ty_atoms T) -> In X L.
Proof. intros. apply (proj1 H). auto. Qed.

Lemma L_ok_tm : forall L T t, L_ok L T t ->
  forall X, In X (tm_atoms t) -> In X L.
Proof. intros. apply (proj2 H). auto. Qed.

Lemma ty_atoms_open_ty_rec : forall k U T X,
  In X (ty_atoms (open_ty_rec k U T)) ->
  In X (ty_atoms T) \/ In X (ty_atoms U).
Proof.
  intros k U T. revert k.
  induction T as [i | Y | A IHA B IHB | B IHB]; intros k X H; simpl in *.
  - destruct (Nat.eqb k i); auto.
  - destruct H as [->|[]]; auto.
  - apply in_app_or in H as [H|H].
    + destruct (IHA k X H) as [H'|H']; [left; apply in_or_app; left; auto | right; auto].
    + destruct (IHB k X H) as [H'|H']; [left; apply in_or_app; right; auto | right; auto].
  - destruct (IHB (S k) X H) as [H'|H']; auto.
Qed.

Lemma ty_atoms_open_ty : forall U T X,
  In X (ty_atoms (open_ty T U)) ->
  In X (ty_atoms T) \/ In X (ty_atoms U).
Proof. intros. apply ty_atoms_open_ty_rec with (k := 0). auto. Qed.

Lemma ty_atoms_ty_subst : forall Y U T X,
  In X (ty_atoms (ty_subst Y U T)) ->
  In X (ty_atoms T) \/ In X (ty_atoms U).
Proof.
  intros Y U T. revert Y U.
  induction T as [i | Z | A IHA B IHB | B IHB]; intros Y U X H; simpl in *.
  - auto.
  - destruct (Nat.eqb Y Z) eqn:E; simpl in *.
    + right. auto.
    + left. auto.
  - apply in_app_or in H as [H|H].
    + destruct (IHA Y U X H) as [H'|H']; [left; apply in_or_app; left; auto | right; auto].
    + destruct (IHB Y U X H) as [H'|H']; [left; apply in_or_app; right; auto | right; auto].
  - destruct (IHB Y U X H) as [H'|H']; auto.
Qed.

Lemma tm_atoms_open_tm_rec : forall k u t X,
  In X (tm_atoms (open_tm_rec k u t)) ->
  In X (tm_atoms t) \/ In X (tm_atoms u).
Proof.
  intros k u t. revert k.
  induction t as [i | x | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb];
    intros k X H; simpl in *.
  - destruct (Nat.eqb k i); simpl in *; auto.
  - destruct H.
  - apply in_app_or in H as [H|H].
    + left. apply in_or_app. left. auto.
    + destruct (IHb (S k) X H) as [H'|H']; [left; apply in_or_app; right; auto | right; auto].
  - apply in_app_or in H as [H|H].
    + destruct (IHf k X H) as [H'|H']; [left; apply in_or_app; left; auto | right; auto].
    + destruct (IHa k X H) as [H'|H']; [left; apply in_or_app; right; auto | right; auto].
  - destruct (IHb k X H) as [H'|H']; auto.
  - apply in_app_or in H as [H|H].
    + destruct (IHf k X H) as [H'|H']; [left; apply in_or_app; left; auto | right; auto].
    + left. apply in_or_app. right. auto.
  - apply in_app_or in H as [H|H].
    + destruct (IHa k X H) as [H'|H']; [left; apply in_or_app; left; auto | right; auto].
    + destruct (IHb k X H) as [H'|H']; [left; apply in_or_app; right; auto | right; auto].
Qed.

Lemma tm_atoms_open_tm_ty_rec : forall k U t X,
  In X (tm_atoms (open_tm_ty_rec k U t)) ->
  In X (tm_atoms t) \/ In X (ty_atoms U).
Proof.
  intros k U t. revert k.
  induction t as [i | x | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb];
    intros k X H; simpl in *.
  - auto.
  - auto.
  - apply in_app_or in H as [H|H].
    + destruct (ty_atoms_open_ty_rec k U T X H) as [H'|H'];
        [left; apply in_or_app; left; auto | right; auto].
    + destruct (IHb k X H) as [H'|H']; [left; apply in_or_app; right; auto | right; auto].
  - apply in_app_or in H as [H|H].
    + destruct (IHf k X H) as [H'|H']; [left; apply in_or_app; left; auto | right; auto].
    + destruct (IHa k X H) as [H'|H']; [left; apply in_or_app; right; auto | right; auto].
  - destruct (IHb (S k) X H) as [H'|H']; auto.
  - apply in_app_or in H as [H|H].
    + destruct (IHf k X H) as [H'|H']; [left; apply in_or_app; left; auto | right; auto].
    + destruct (ty_atoms_open_ty_rec k U T X H) as [H'|H'];
        [left; apply in_or_app; right; auto | right; auto].
  - apply in_app_or in H as [H|H].
    + destruct (IHa k X H) as [H'|H']; [left; apply in_or_app; left; auto | right; auto].
    + destruct (IHb k X H) as [H'|H']; [left; apply in_or_app; right; auto | right; auto].
Qed.

Lemma step_atoms : forall t t', t --> t' ->
  forall X, In X (tm_atoms t') -> In X (tm_atoms t).
Proof.
  intros t t' H. induction H; intros X Hin; simpl in *.
  - (* ST_AppAbs *)
    destruct (tm_atoms_open_tm_rec 0 v t X Hin) as [H1|H2].
    + apply in_or_app. left. apply in_or_app. right. auto.
    + apply in_or_app. right. auto.
  - (* ST_App1 *)
    apply in_app_or in Hin as [H1|H2].
    + apply in_or_app. left. apply IHstep. auto.
    + apply in_or_app. right. auto.
  - (* ST_App2 *)
    apply in_app_or in Hin as [H1|H2].
    + apply in_or_app. left. auto.
    + apply in_or_app. right. apply IHstep. auto.
  - (* ST_TAppTabs *)
    destruct (tm_atoms_open_tm_ty_rec 0 T t X Hin) as [H1|H2].
    + apply in_or_app. left. auto.
    + apply in_or_app. right. auto.
  - (* ST_TApp *)
    apply in_app_or in Hin as [H1|H2].
    + apply in_or_app. left. apply IHstep. auto.
    + apply in_or_app. right. auto.
  - (* ST_ChoiceLeft *)
    apply in_or_app. left. auto.
  - (* ST_ChoiceRight *)
    apply in_or_app. right. auto.
Qed.

Lemma multi_atoms : forall t t', t -->* t' ->
  forall X, In X (tm_atoms t') -> In X (tm_atoms t).
Proof.
  intros t t' H. induction H; intros X Hin.
  - auto.
  - apply step_atoms with (t := x) (t' := y).
    + assumption.
    + apply IHmulti. assumption.
Qed.

Lemma L_ok_weaken : forall L L' T t,
  L_ok L T t -> (forall X, In X L -> In X L') -> L_ok L' T t.
Proof.
  intros L L' T t [H1 H2] Hsub. split; intros X HX; auto.
Qed.

Lemma L_ok_subterm_abs : forall L T b T0,
  L_ok L (Ty_Arrow T0 T) (tm_abs T0 b) -> L_ok L T b.
Proof.
  intros L T b T0 [H1 H2]. split.
  - intros X HX. apply H1. simpl. apply in_or_app. auto.
  - intros X HX. apply H2. simpl. apply in_or_app. auto.
Qed.

Lemma L_ok_app_l : forall L A f a,
  L_ok L A (tm_app f a) -> L_ok L A f.
Proof.
  intros L A f a [H1 H2]. split; auto.
  intros X HX. apply H2. simpl. apply in_or_app. auto.
Qed.

Lemma L_ok_app_r : forall L B f a,
  L_ok L B (tm_app f a) -> L_ok L B a.
Proof.
  intros L B f a [H1 H2]. split; auto.
  intros X HX. apply H2. simpl. apply in_or_app. auto.
Qed.

Lemma L_ok_subterm_tabs : forall L B b,
  L_ok L (Ty_All B) (tm_tabs b) -> L_ok L B b.
Proof.
  intros L B b [H1 H2]. split; auto.
Qed.

Lemma L_ok_tapp_l : forall L B f T,
  L_ok L B (tm_tapp f T) -> L_ok L B f.
Proof.
  intros L B f T [H1 H2]. split; auto.
  intros X HX. apply H2. simpl. apply in_or_app. auto.
Qed.

Lemma L_ok_choice_l : forall L A a b,
  L_ok L A (tm_choice a b) -> L_ok L A a.
Proof.
  intros L A a b [H1 H2]. split; auto.
  intros X HX. apply H2. simpl. apply in_or_app. auto.
Qed.

Lemma L_ok_choice_r : forall L A a b,
  L_ok L A (tm_choice a b) -> L_ok L A b.
Proof.
  intros L A a b [H1 H2]. split; auto.
  intros X HX. apply H2. simpl. apply in_or_app. auto.
Qed.

(* --------------------------------------------------------------------- *)
(* Normalization preserves and reflects closedness and values.           *)
(* --------------------------------------------------------------------- *)

Lemma lc_ty_norm : forall TE T K,
  closed_tyenv TE ->
  (lc_ty_at K T <-> lc_ty_at K (norm_ty TE T)).
Proof.
  intros TE T. revert T.
  induction T as [i | X | A IHA B IHB | B IHB]; intros K Hc; simpl; split; intro H.
  - inversion H. apply lc_ty_bvar. lia.
  - inversion H. apply lc_ty_bvar. lia.
  - apply wf_ty_lc_any with (Delta := []). apply (proj1 (Hc X)).
  - apply lc_ty_fvar.
  - inversion H. apply lc_ty_arrow.
    + apply (IHA K Hc). assumption.
    + apply (IHB K Hc). assumption.
  - inversion H. apply lc_ty_arrow.
    + apply (IHA K Hc). assumption.
    + apply (IHB K Hc). assumption.
  - inversion H. apply lc_ty_all. apply (IHB (S K) Hc). assumption.
  - inversion H. apply lc_ty_all. apply (IHB (S K) Hc). assumption.
Qed.

Lemma lc_tm_norm : forall TE t K k,
  closed_tyenv TE ->
  (lc_tm_at K k t <-> lc_tm_at K k (norm_tm TE t)).
Proof.
  intros TE t. revert t.
  induction t as [i | x | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb];
    intros K k Hc; simpl; split; intro H.
  - inversion H. apply lc_tm_bvar. lia.
  - inversion H. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_fvar.
  - inversion H. apply lc_tm_abs.
    + apply (lc_ty_norm TE T K Hc). assumption.
    + apply (IHb K (S k) Hc). assumption.
  - inversion H. apply lc_tm_abs.
    + apply (lc_ty_norm TE T K Hc). assumption.
    + apply (IHb K (S k) Hc). assumption.
  - inversion H. apply lc_tm_app.
    + apply (IHf K k Hc). assumption.
    + apply (IHa K k Hc). assumption.
  - inversion H. apply lc_tm_app.
    + apply (IHf K k Hc). assumption.
    + apply (IHa K k Hc). assumption.
  - inversion H. apply lc_tm_tabs. apply (IHb (S K) k Hc). assumption.
  - inversion H. apply lc_tm_tabs. apply (IHb (S K) k Hc). assumption.
  - inversion H. apply lc_tm_tapp.
    + apply (IHf K k Hc). assumption.
    + apply (lc_ty_norm TE T K Hc). assumption.
  - inversion H. apply lc_tm_tapp.
    + apply (IHf K k Hc). assumption.
    + apply (lc_ty_norm TE T K Hc). assumption.
  - inversion H. apply lc_tm_choice.
    + apply (IHa K k Hc). assumption.
    + apply (IHb K k Hc). assumption.
  - inversion H. apply lc_tm_choice.
    + apply (IHa K k Hc). assumption.
    + apply (IHb K k Hc). assumption.
Qed.

Lemma value_norm : forall TE v,
  closed_tyenv TE -> value v -> value (norm_tm TE v).
Proof.
  intros TE v Hc H. inversion H as [T t Hlc | t Hlc]; subst; simpl; constructor.
  - apply (proj1 (lc_tm_norm TE (tm_abs T t) 0 0 Hc)). assumption.
  - apply (proj1 (lc_tm_norm TE (tm_tabs t) 0 0 Hc)). assumption.
Qed.

Lemma value_norm_inv : forall TE v,
  closed_tyenv TE -> value (norm_tm TE v) -> value v.
Proof.
  intros TE v Hc H.
  destruct v as [i | x | T b | f1 a1 | b | f2 T2 | c1 c2]; simpl in H;
    try (inversion H; fail).
  - apply v_abs. apply (proj2 (lc_tm_norm TE (tm_abs T b) 0 0 Hc)).
    simpl. apply value_lc. exact H.
  - apply v_tabs. apply (proj2 (lc_tm_norm TE (tm_tabs b) 0 0 Hc)).
    simpl. apply value_lc. exact H.
Qed.

(* Inversion of normalization at each term constructor. *)
Lemma norm_tm_abs_eq : forall TE t T b,
  norm_tm TE t = tm_abs T b ->
  exists T0 b0, t = tm_abs T0 b0 /\ norm_ty TE T0 = T /\ norm_tm TE b0 = b.
Proof.
  intros TE t. destruct t; simpl; intros T0 b0 H; try discriminate;
    (inversion H; subst; eauto).
Qed.

Lemma norm_tm_tabs_eq : forall TE t b,
  norm_tm TE t = tm_tabs b ->
  exists b0, t = tm_tabs b0 /\ norm_tm TE b0 = b.
Proof.
  intros TE t. destruct t; simpl; intros b0 H; try discriminate;
    (inversion H; subst; eauto).
Qed.

Lemma norm_tm_app_eq : forall TE t f a,
  norm_tm TE t = tm_app f a ->
  exists f0 a0, t = tm_app f0 a0 /\ norm_tm TE f0 = f /\ norm_tm TE a0 = a.
Proof.
  intros TE t. destruct t; simpl; intros f0 a0 H; try discriminate;
    (inversion H; subst; eauto).
Qed.

Lemma norm_tm_tapp_eq : forall TE t f T,
  norm_tm TE t = tm_tapp f T ->
  exists f0 T0, t = tm_tapp f0 T0 /\ norm_tm TE f0 = f /\ norm_ty TE T0 = T.
Proof.
  intros TE t. destruct t; simpl; intros f0 T0 H; try discriminate;
    (inversion H; subst; eauto).
Qed.

Lemma norm_tm_choice_eq : forall TE t a b,
  norm_tm TE t = tm_choice a b ->
  exists a0 b0, t = tm_choice a0 b0 /\ norm_tm TE a0 = a /\ norm_tm TE b0 = b.
Proof.
  intros TE t. destruct t; simpl; intros a0 b0 H; try discriminate;
    (inversion H; subst; eauto).
Qed.

(* --------------------------------------------------------------------- *)
(* Single-step commutation with normalization.                           *)
(* --------------------------------------------------------------------- *)

Lemma step_norm : forall TE t t',
  closed_tyenv TE -> t --> t' -> norm_tm TE t --> norm_tm TE t'.
Proof.
  intros TE t t' Hc H. induction H.
  - (* ST_AppAbs *)
    simpl. rewrite (norm_tm_open_tm TE t v). apply ST_AppAbs.
    + apply (proj1 (lc_tm_norm TE (tm_abs T t) 0 0 Hc)). assumption.
    + apply value_norm; auto.
  - (* ST_App1 *)
    simpl. apply ST_App1.
    + apply IHstep.
    + apply (proj1 (lc_tm_norm TE t2 0 0 Hc)). assumption.
  - (* ST_App2 *)
    simpl. apply ST_App2.
    + apply value_norm; auto.
    + apply IHstep.
  - (* ST_TAppTabs *)
    simpl. rewrite (norm_tm_open_tm_ty TE T t Hc). apply ST_TAppTabs.
    + apply (proj1 (lc_tm_norm TE (tm_tabs t) 0 0 Hc)). assumption.
    + apply (proj1 (lc_ty_norm TE T 0 Hc)). assumption.
  - (* ST_TApp *)
    simpl. apply ST_TApp.
    + apply IHstep.
    + apply (proj1 (lc_ty_norm TE T 0 Hc)). assumption.
  - (* ST_ChoiceLeft *)
    simpl. apply ST_ChoiceLeft.
    + apply (proj1 (lc_tm_norm TE t1 0 0 Hc)). assumption.
    + apply (proj1 (lc_tm_norm TE t2 0 0 Hc)). assumption.
  - (* ST_ChoiceRight *)
    simpl. apply ST_ChoiceRight.
    + apply (proj1 (lc_tm_norm TE t1 0 0 Hc)). assumption.
    + apply (proj1 (lc_tm_norm TE t2 0 0 Hc)). assumption.
Qed.

Lemma multi_norm : forall TE t t',
  closed_tyenv TE -> t -->* t' -> norm_tm TE t -->* norm_tm TE t'.
Proof.
  intros TE t t' Hc H. induction H.
  - apply multi_refl.
  - apply multi_step with (y := norm_tm TE y).
    + apply step_norm; auto.
    + apply IHmulti.
Qed.

Lemma step_norm_inv : forall TE t0 s,
  closed_tyenv TE -> norm_tm TE t0 --> s ->
  exists t', t0 --> t' /\ s = norm_tm TE t'.
Proof.
  intros TE t0 s Hc Hstep.
  remember (norm_tm TE t0) as nt eqn:E.
  revert t0 E.
  induction Hstep; intros t0 E.
  - (* ST_AppAbs *)
    symmetry in E.
    destruct (norm_tm_app_eq TE t0 (tm_abs T t) v E) as (f & a & Eqt & Ef & Ea).
    destruct (norm_tm_abs_eq TE f T t Ef) as (T0 & b0 & Eqf & ET0 & Eb).
    assert (Hva : value a).
    { apply (value_norm_inv TE a Hc). rewrite Ea. assumption. }
    assert (Hlca : lc_tm_at 0 0 (tm_abs T0 b0)).
    { apply (proj2 (lc_tm_norm TE (tm_abs T0 b0) 0 0 Hc)). simpl. rewrite ET0, Eb. assumption. }
    exists (open_tm b0 a). split.
    + rewrite Eqt, Eqf. apply ST_AppAbs; assumption.
    + simpl. rewrite norm_tm_open_tm, Eb, Ea. reflexivity.
  - (* ST_App1 *)
    symmetry in E.
    destruct (norm_tm_app_eq TE t0 t1 t2 E) as (f0 & a0 & Eqt & Ef & Ea).
    destruct (IHHstep f0 (eq_sym Ef)) as (f0' & Hstepf & Ef').
    assert (Hlca0 : lc_tm_at 0 0 a0).
    { apply (proj2 (lc_tm_norm TE a0 0 0 Hc)). rewrite Ea. assumption. }
    exists (tm_app f0' a0). split.
    + rewrite Eqt. apply ST_App1; assumption.
    + simpl. rewrite Ef', Ea. reflexivity.
  - (* ST_App2 *)
    symmetry in E.
    destruct (norm_tm_app_eq TE t0 v1 t2 E) as (f0 & a0 & Eqt & Ef & Ea).
    assert (Hval : value f0).
    { apply (value_norm_inv TE f0 Hc). rewrite Ef. assumption. }
    destruct (IHHstep a0 (eq_sym Ea)) as (a0' & Hstepa & Ea').
    exists (tm_app f0 a0'). split.
    + rewrite Eqt. apply ST_App2; assumption.
    + simpl. rewrite Ef, Ea'. reflexivity.
  - (* ST_TAppTabs *)
    symmetry in E.
    destruct (norm_tm_tapp_eq TE t0 (tm_tabs t) T E) as (f0 & T0 & Eqt & Ef & ET).
    destruct (norm_tm_tabs_eq TE f0 t Ef) as (b0 & Eqf & Eb).
    assert (Hlc0 : lc_tm_at 0 0 (tm_tabs b0)).
    { apply (proj2 (lc_tm_norm TE (tm_tabs b0) 0 0 Hc)). simpl. rewrite Eb. assumption. }
    assert (HT0 : lc_ty_at 0 T0).
    { apply (proj2 (lc_ty_norm TE T0 0 Hc)). rewrite ET. assumption. }
    exists (open_tm_ty b0 T0). split.
    + rewrite Eqt, Eqf. apply ST_TAppTabs; assumption.
    + simpl. rewrite (norm_tm_open_tm_ty TE T0 b0 Hc), Eb, ET. reflexivity.
  - (* ST_TApp *)
    symmetry in E.
    destruct (norm_tm_tapp_eq TE t0 t T E) as (f0 & T0 & Eqt & Ef & ET).
    destruct (IHHstep f0 (eq_sym Ef)) as (f0' & Hstepf & Ef').
    assert (HT0 : lc_ty_at 0 T0).
    { apply (proj2 (lc_ty_norm TE T0 0 Hc)). rewrite ET. assumption. }
    exists (tm_tapp f0' T0). split.
    + rewrite Eqt. apply ST_TApp; assumption.
    + simpl. rewrite Ef', ET. reflexivity.
  - (* ST_ChoiceLeft *)
    symmetry in E.
    destruct (norm_tm_choice_eq TE t0 t1 t2 E) as (a0 & b0 & Eqt & Ea & Eb).
    assert (Hlca0 : lc_tm_at 0 0 a0).
    { apply (proj2 (lc_tm_norm TE a0 0 0 Hc)). rewrite Ea. assumption. }
    assert (Hlcb0 : lc_tm_at 0 0 b0).
    { apply (proj2 (lc_tm_norm TE b0 0 0 Hc)). rewrite Eb. assumption. }
    exists a0. split.
    + rewrite Eqt. apply ST_ChoiceLeft; assumption.
    + rewrite Ea. reflexivity.
  - (* ST_ChoiceRight *)
    symmetry in E.
    destruct (norm_tm_choice_eq TE t0 t1 t2 E) as (a0 & b0 & Eqt & Ea & Eb).
    assert (Hlca0 : lc_tm_at 0 0 a0).
    { apply (proj2 (lc_tm_norm TE a0 0 0 Hc)). rewrite Ea. assumption. }
    assert (Hlcb0 : lc_tm_at 0 0 b0).
    { apply (proj2 (lc_tm_norm TE b0 0 0 Hc)). rewrite Eb. assumption. }
    exists b0. split.
    + rewrite Eqt. apply ST_ChoiceRight; assumption.
    + rewrite Eb. reflexivity.
Qed.

Lemma multi_norm_inv : forall TE t s,
  closed_tyenv TE -> norm_tm TE t -->* s ->
  exists t', t -->* t' /\ s = norm_tm TE t'.
Proof.
  intros TE t s Hc H. remember (norm_tm TE t) as nt eqn:E.
  revert t E. induction H; intros t0 E.
  - exists t0. split; [apply multi_refl | assumption].
  - rewrite E in H.
    destruct (step_norm_inv TE t0 y Hc H) as (t1 & Hstep & Ey).
    destruct (IHmulti t1 Ey) as (t2 & Hmulti & Ez).
    exists t2. split.
    + apply multi_step with (y := t1); assumption.
    + assumption.
Qed.

(* --------------------------------------------------------------------- *)
(* Auxiliary lemmas for the normalization invariance of the predicate.   *)
(* --------------------------------------------------------------------- *)

Lemma extend_ty_closed : forall TE X U,
  closed_tyenv TE -> wf_ty [] U -> ty_atoms U = [] ->
  closed_tyenv (extend_ty TE X U).
Proof.
  intros TE X U Hc HU HUa Z. unfold extend_ty.
  destruct (Nat.eqb Z X) eqn:E.
  - split; assumption.
  - apply Hc.
Qed.

Lemma ty_size_open_ty_rec : forall k U T,
  ty_size U = 1 -> ty_size (open_ty_rec k U T) = ty_size T.
Proof.
  intros k U T HU. revert k.
  induction T as [i | X | A IHA B IHB | B IHB]; intros k; simpl.
  - destruct (Nat.eqb k i).
    + simpl. auto.
    + reflexivity.
  - reflexivity.
  - rewrite IHA by auto. rewrite IHB by auto. reflexivity.
  - rewrite IHB by auto. reflexivity.
Qed.

Lemma ty_size_open_ty_fvar : forall k X T,
  ty_size (open_ty_rec k (Ty_FVar X) T) = ty_size T.
Proof. intros. apply ty_size_open_ty_rec. reflexivity. Qed.

Lemma norm_tm_no_atoms : forall TE t,
  closed_tyenv TE -> norm_tm TE t = t -> tm_atoms t = [].
Proof.
  intros TE t Hc H. rewrite <- H. apply norm_tm_atoms_nil. auto.
Qed.

Lemma norm_ty_extend_other : forall TE X U T,
  ~ In X (ty_atoms T) ->
  norm_ty (extend_ty TE X U) T = norm_ty TE T.
Proof.
  intros TE X U T. revert X U.
  induction T as [i | Y | A IHA B IHB | B IHB]; intros X U H; simpl in *.
  - reflexivity.
  - unfold extend_ty. destruct (Nat.eqb Y X) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. simpl. auto.
    + reflexivity.
  - assert (HA : ~ In X (ty_atoms A)) by (intro Hc; apply H; apply in_or_app; auto).
    assert (HB : ~ In X (ty_atoms B)) by (intro Hc; apply H; apply in_or_app; auto).
    rewrite IHA by auto. rewrite IHB by auto. reflexivity.
  - rewrite IHB by auto. reflexivity.
Qed.

Lemma norm_tm_extend_other : forall TE X U t,
  ~ In X (tm_atoms t) ->
  norm_tm (extend_ty TE X U) t = norm_tm TE t.
Proof.
  intros TE X U t. revert X U.
  induction t as [i | x | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb];
    intros X U H; simpl in *.
  - reflexivity.
  - reflexivity.
  - assert (HT : ~ In X (ty_atoms T)) by (intro Hc; apply H; simpl; apply in_or_app; auto).
    assert (HA : ~ In X (tm_atoms b)) by (intro Hc; apply H; simpl; apply in_or_app; auto).
    rewrite norm_ty_extend_other by auto. rewrite IHb by auto. reflexivity.
  - assert (Hf : ~ In X (tm_atoms f)) by (intro Hc; apply H; simpl; apply in_or_app; auto).
    assert (Ha : ~ In X (tm_atoms a)) by (intro Hc; apply H; simpl; apply in_or_app; auto).
    rewrite IHf by auto. rewrite IHa by auto. reflexivity.
  - rewrite IHb by auto. reflexivity.
  - assert (Hf : ~ In X (tm_atoms f)) by (intro Hc; apply H; simpl; apply in_or_app; auto).
    assert (HT : ~ In X (ty_atoms T)) by (intro Hc; apply H; simpl; apply in_or_app; auto).
    rewrite IHf by auto. rewrite norm_ty_extend_other by auto. reflexivity.
  - assert (Ha : ~ In X (tm_atoms a)) by (intro Hc; apply H; simpl; apply in_or_app; auto).
    assert (Hb : ~ In X (tm_atoms b)) by (intro Hc; apply H; simpl; apply in_or_app; auto).
    rewrite IHa by auto. rewrite IHb by auto. reflexivity.
Qed.

Lemma L_ok_all_body : forall L X B b,
  ~ In X L -> L_ok L (Ty_All B) (tm_tabs b) ->
  L_ok (X :: L) (open_ty B (Ty_FVar X)) (open_tm_ty b (Ty_FVar X)).
Proof.
  intros L X B b HX [H1 H2]. split.
  - intros Y HY. apply ty_atoms_open_ty_rec in HY as [HY|HY].
    + apply in_cons. apply H1. auto.
    + simpl in HY. destruct HY as [->|[]]. apply in_eq.
  - intros Y HY. apply tm_atoms_open_tm_ty_rec in HY as [HY|HY].
    + apply in_cons. apply H2. auto.
    + simpl in HY. destruct HY as [->|[]]. apply in_eq.
Qed.

Lemma L_ok_all_body_norm : forall TE L X B b,
  closed_tyenv TE -> ~ In X L -> L_ok L (Ty_All B) (tm_tabs b) ->
  L_ok (X :: L) (open_ty B (Ty_FVar X)) (open_tm_ty (norm_tm TE b) (Ty_FVar X)).
Proof.
  intros TE L X B b Hc HX [H1 H2]. split.
  - intros Y HY. apply ty_atoms_open_ty_rec in HY as [HY|HY].
    + apply in_cons. apply H1. auto.
    + simpl in HY. destruct HY as [->|[]]. apply in_eq.
  - intros Y HY. apply tm_atoms_open_tm_ty_rec in HY as [HY|HY].
    + rewrite norm_tm_atoms_nil in HY by auto. inversion HY.
    + simpl in HY. destruct HY as [->|[]]. apply in_eq.
Qed.

Lemma L_ok_arrow_body : forall L B T0 b u,
  L_ok L (Ty_Arrow T0 B) (tm_abs T0 b) -> tm_atoms u = [] ->
  L_ok L B (open_tm b u).
Proof.
  intros L B T0 b u [H1 H2] Hu. split.
  - intros Y HY. apply H1. simpl. apply in_or_app. auto.
  - intros Y HY. apply tm_atoms_open_tm_rec with (k := 0) in HY as [HY|HY]; auto.
    + apply H2. simpl. apply in_or_app. auto.
    + rewrite Hu in HY. inversion HY.
Qed.

Lemma L_ok_value_arrow : forall L A B t v T0 b,
  L_ok L (Ty_Arrow A B) t -> t -->* v -> v = tm_abs T0 b ->
  L_ok L (Ty_Arrow T0 B) (tm_abs T0 b).
Proof.
  intros L A B t v T0 b [H1 H2] Hm Ev. split.
  - intros X HX. apply in_app_or in HX as [HX|HX].
    + apply H2. apply (multi_atoms t v Hm). rewrite Ev. simpl. apply in_or_app. left. auto.
    + apply H1. simpl. apply in_or_app. right. auto.
  - intros X HX. apply H2. apply (multi_atoms t v Hm). rewrite Ev. simpl. auto.
Qed.

Lemma L_ok_value_tabs : forall L B t b,
  L_ok L (Ty_All B) t -> t -->* tm_tabs b ->
  L_ok L (Ty_All B) (tm_tabs b).
Proof.
  intros L B t b [H1 H2] Hm. split.
  - intros X HX. apply H1. auto.
  - intros X HX. apply H2. apply (multi_atoms t (tm_tabs b) Hm). auto.
Qed.

Lemma norm_open_tm_ty_all : forall TE X U b,
  closed_tyenv TE -> wf_ty [] U -> ty_atoms U = [] -> ~ In X (tm_atoms b) ->
  norm_tm (extend_ty TE X U) (open_tm_ty b (Ty_FVar X)) =
  norm_tm (extend_ty TE X U) (open_tm_ty (norm_tm TE b) (Ty_FVar X)).
Proof.
  intros TE X U b Hc HU HUa HX.
  set (TE' := extend_ty TE X U).
  assert (Hc' : closed_tyenv TE') by (apply extend_ty_closed; auto).
  rewrite (norm_tm_open_tm_ty TE' (Ty_FVar X) b Hc').
  rewrite (norm_tm_open_tm_ty TE' (Ty_FVar X) (norm_tm TE b) Hc').
  unfold TE'.
  rewrite (norm_tm_extend_other TE X U b HX).
  rewrite (norm_tm_extend_other TE X U (norm_tm TE b)).
  2: { rewrite norm_tm_atoms_nil by auto. auto. }
  rewrite (norm_tm_idem TE b Hc).
  simpl. rewrite (extend_ty_same TE X U). reflexivity.
Qed.

Lemma sem_norm : forall f L T TE RE t,
  closed_tyenv TE -> L_ok L T t -> f >= ty_size T ->
  (sem f L T TE RE t <-> sem f L T TE RE (norm_tm TE t)).
Proof.
  intros f. induction f as [|n IH]; intros L T TE RE t Hc HL Hsize.
  - simpl. split; intro H; inversion H.
  - destruct T as [i | X | A B | B].
    + (* BVar *)
      simpl. split; intro H;
        destruct H as (Hlc & v & Hm & Hval & Hlcv & Hf); contradiction.
    + (* FVar *)
      simpl. split.
      * intro H. destruct H as (Hlc & v & Hm & Hval & Hlcv & Hre).
        split.
        { apply (proj1 (lc_tm_norm TE t 0 0 Hc)). assumption. }
        exists (norm_tm TE v). split.
        { apply multi_norm; auto. }
        split.
        { apply value_norm; auto. }
        split.
        { apply (proj1 (lc_tm_norm TE v 0 0 Hc)). assumption. }
        rewrite norm_tm_idem by auto. assumption.
      * intro H. destruct H as (Hlc & v & Hm & Hval & Hlcv & Hre).
        destruct (multi_norm_inv TE t v Hc Hm) as (w & Hmw & Ev).
        split.
        { apply (proj2 (lc_tm_norm TE t 0 0 Hc)). assumption. }
        exists w. split.
        { assumption. }
        split.
        { apply (value_norm_inv TE w Hc). rewrite Ev in Hval. assumption. }
        split.
        { apply (proj2 (lc_tm_norm TE w 0 0 Hc)). rewrite Ev in Hlcv. assumption. }
        rewrite Ev in Hre. rewrite (norm_tm_idem TE w Hc) in Hre. assumption.
    + (* Arrow *)
      simpl. split.
      * intro H. destruct H as (Hlc & v & Hm & Hval & Hlcv & T0 & b & Ev & Hcl).
        split.
        { apply (proj1 (lc_tm_norm TE t 0 0 Hc)). assumption. }
        exists (norm_tm TE v). split.
        { apply multi_norm; auto. }
        split.
        { apply value_norm; auto. }
        split.
        { apply (proj1 (lc_tm_norm TE v 0 0 Hc)). assumption. }
        exists (norm_ty TE T0), (norm_tm TE b). split.
        { rewrite Ev. reflexivity. }
        intros u Hvu Hlcu Hnu HsemA.
        assert (HLB : L_ok L B (open_tm b u)).
        { apply L_ok_arrow_body with (T0 := T0).
          - apply L_ok_value_arrow with (A := A) (t := t) (v := v); auto.
          - apply norm_tm_no_atoms with (TE := TE); auto. }
        assert (Hsz : n >= ty_size B) by (simpl in Hsize; lia).
        rewrite <- Hnu. rewrite <- (norm_tm_open_tm TE b u).
        apply (proj1 (IH L B TE RE (open_tm b u) Hc HLB Hsz)).
        apply Hcl; auto.
      * intro H. destruct H as (Hlc & v' & Hm & Hval & Hlcv & T0' & b' & Ev & Hcl).
        destruct (multi_norm_inv TE t v' Hc Hm) as (v & Hmw & Evv).
        rewrite Evv in Ev.
        destruct (norm_tm_abs_eq TE v T0' b' Ev) as (T0 & b & Evabs & ET0 & Eb).
        split.
        { apply (proj2 (lc_tm_norm TE t 0 0 Hc)). assumption. }
        exists v. split.
        { assumption. }
        split.
        { apply (value_norm_inv TE v Hc). rewrite <- Evv. assumption. }
        split.
        { apply (proj2 (lc_tm_norm TE v 0 0 Hc)). rewrite <- Evv. assumption. }
        exists T0, b. split.
        { assumption. }
        intros u Hvu Hlcu Hnu HsemA.
        assert (HLB : L_ok L B (open_tm b u)).
        { apply L_ok_arrow_body with (T0 := T0).
          - apply L_ok_value_arrow with (A := A) (t := t) (v := v); auto.
          - apply norm_tm_no_atoms with (TE := TE); auto. }
        assert (Hsz : n >= ty_size B) by (simpl in Hsize; lia).
        apply (proj2 (IH L B TE RE (open_tm b u) Hc HLB Hsz)).
        rewrite norm_tm_open_tm. rewrite Hnu. rewrite Eb.
        apply Hcl; auto.
    + (* All *)
      simpl. split.
      * intro H. destruct H as (Hlc & v & Hm & Hval & Hlcv & b & Ev & Hcl).
        split.
        { apply (proj1 (lc_tm_norm TE t 0 0 Hc)). assumption. }
        exists (norm_tm TE v). split.
        { apply multi_norm; auto. }
        split.
        { apply value_norm; auto. }
        split.
        { apply (proj1 (lc_tm_norm TE v 0 0 Hc)). assumption. }
        exists (norm_tm TE b). split.
        { rewrite Ev. reflexivity. }
        intros X U Q HXL HU HUa.
        assert (Hc' : closed_tyenv (extend_ty TE X U))
          by (apply extend_ty_closed; auto).
        assert (HLtab : L_ok L (Ty_All B) (tm_tabs b)).
        { apply L_ok_value_tabs with (t := t).
          - exact HL.
          - rewrite <- Ev. exact Hm. }
        assert (HL' : L_ok (X :: L) (open_ty B (Ty_FVar X)) (open_tm_ty b (Ty_FVar X)))
          by (apply L_ok_all_body; auto).
        assert (HL'' : L_ok (X :: L) (open_ty B (Ty_FVar X))
                        (open_tm_ty (norm_tm TE b) (Ty_FVar X)))
          by (apply L_ok_all_body_norm; auto).
        assert (Hsz : n >= ty_size (open_ty B (Ty_FVar X))).
        { unfold open_ty. rewrite ty_size_open_ty_fvar. simpl in Hsize. lia. }
        assert (HXb : ~ In X (tm_atoms b)).
        { intro HcX. apply HXL. apply (proj2 HL). apply (multi_atoms t v Hm).
          rewrite Ev. simpl. auto. }
        assert (HsemB : sem n (X :: L) (open_ty B (Ty_FVar X))
                  (extend_ty TE X U) (extend_pred RE X Q)
                  (norm_tm (extend_ty TE X U) (open_tm_ty b (Ty_FVar X)))).
        { apply (proj1 (IH (X :: L) (open_ty B (Ty_FVar X))
                           (extend_ty TE X U) (extend_pred RE X Q)
                           (open_tm_ty b (Ty_FVar X)) Hc' HL' Hsz)).
          apply Hcl; auto. }
        rewrite (norm_open_tm_ty_all TE X U b Hc HU HUa HXb) in HsemB.
        apply (proj2 (IH (X :: L) (open_ty B (Ty_FVar X))
                          (extend_ty TE X U) (extend_pred RE X Q)
                          (open_tm_ty (norm_tm TE b) (Ty_FVar X)) Hc' HL'' Hsz)).
        exact HsemB.
      * intro H. destruct H as (Hlc & v' & Hm & Hval & Hlcv & b' & Ev & Hcl).
        destruct (multi_norm_inv TE t v' Hc Hm) as (v & Hmw & Evv).
        rewrite Evv in Ev.
        destruct (norm_tm_tabs_eq TE v b' Ev) as (b & Evtabs & Eb).
        subst b'.
        split.
        { apply (proj2 (lc_tm_norm TE t 0 0 Hc)). assumption. }
        exists v. split.
        { assumption. }
        split.
        { apply (value_norm_inv TE v Hc). rewrite <- Evv. assumption. }
        split.
        { apply (proj2 (lc_tm_norm TE v 0 0 Hc)). rewrite <- Evv. assumption. }
        exists b. split.
        { assumption. }
        intros X U Q HXL HU HUa.
        assert (Hc' : closed_tyenv (extend_ty TE X U))
          by (apply extend_ty_closed; auto).
        assert (HLtab : L_ok L (Ty_All B) (tm_tabs b)).
        { apply L_ok_value_tabs with (t := t).
          - exact HL.
          - rewrite <- Evtabs. exact Hmw. }
        assert (HL' : L_ok (X :: L) (open_ty B (Ty_FVar X)) (open_tm_ty b (Ty_FVar X)))
          by (apply L_ok_all_body; auto).
        assert (HL'' : L_ok (X :: L) (open_ty B (Ty_FVar X))
                        (open_tm_ty (norm_tm TE b) (Ty_FVar X)))
          by (apply L_ok_all_body_norm; auto).
        assert (Hsz : n >= ty_size (open_ty B (Ty_FVar X))).
        { unfold open_ty. rewrite ty_size_open_ty_fvar. simpl in Hsize. lia. }
        assert (HXb : ~ In X (tm_atoms b)).
        { intro HcX. apply HXL. apply (proj2 HL). apply (multi_atoms t v Hmw).
          rewrite Evtabs. simpl. auto. }
        assert (HsemB : sem n (X :: L) (open_ty B (Ty_FVar X))
                  (extend_ty TE X U) (extend_pred RE X Q)
                  (open_tm_ty (norm_tm TE b) (Ty_FVar X))).
        { apply Hcl; auto. }
        assert (HsemN : sem n (X :: L) (open_ty B (Ty_FVar X))
                  (extend_ty TE X U) (extend_pred RE X Q)
                  (norm_tm (extend_ty TE X U) (open_tm_ty (norm_tm TE b) (Ty_FVar X)))).
        { apply (proj1 (IH (X :: L) (open_ty B (Ty_FVar X))
                           (extend_ty TE X U) (extend_pred RE X Q)
                           (open_tm_ty (norm_tm TE b) (Ty_FVar X)) Hc' HL'' Hsz)).
          exact HsemB. }
        apply (proj2 (IH (X :: L) (open_ty B (Ty_FVar X))
                          (extend_ty TE X U) (extend_pred RE X Q)
                          (open_tm_ty b (Ty_FVar X)) Hc' HL' Hsz)).
        rewrite (norm_open_tm_ty_all TE X U b Hc HU HUa HXb).
        exact HsemN.
Qed.

(* --------------------------------------------------------------------- *)
(* Environment invariance and atom-freeness.                             *)
(* --------------------------------------------------------------------- *)

Lemma list_nil_of_no_in : forall (l : list atom),
  (forall X, ~ In X l) -> l = [].
Proof.
  intros l H. destruct l as [|a l]; auto.
  exfalso. apply (H a). simpl. auto.
Qed.

Lemma tm_atoms_nil_of_no_in : forall t,
  (forall X, ~ In X (tm_atoms t)) -> tm_atoms t = [].
Proof. intros. apply list_nil_of_no_in. auto. Qed.

Lemma norm_ty_no_atoms_id : forall TE T,
  ty_atoms T = [] -> norm_ty TE T = T.
Proof. intros. apply norm_ty_of_no_atoms. auto. Qed.

Lemma norm_tm_no_atoms_id : forall TE t,
  tm_atoms t = [] -> norm_tm TE t = t.
Proof.
  intros TE t. revert t. fix IH 1.
  intros [i | x | T b | f a | b | f T | a b]; simpl; intros H.
  - reflexivity.
  - reflexivity.
  - destruct (app_eq_nil _ _ H) as [H1 H2].
    rewrite (norm_ty_no_atoms_id TE T H1), (IH b H2). reflexivity.
  - destruct (app_eq_nil _ _ H) as [H1 H2].
    rewrite (IH f H1), (IH a H2). reflexivity.
  - rewrite (IH b H). reflexivity.
  - destruct (app_eq_nil _ _ H) as [H1 H2].
    rewrite (IH f H1), (norm_ty_no_atoms_id TE T H2). reflexivity.
  - destruct (app_eq_nil _ _ H) as [H1 H2].
    rewrite (IH a H1), (IH b H2). reflexivity.
Qed.

Lemma norm_ty_env_eq : forall TE1 TE2 T,
  (forall Z, TE1 Z = TE2 Z) -> norm_ty TE1 T = norm_ty TE2 T.
Proof.
  intros TE1 TE2 T H.
  induction T as [i | X | A IHA B IHB | B IHB]; simpl.
  - reflexivity.
  - apply H.
  - rewrite IHA, IHB. reflexivity.
  - rewrite IHB. reflexivity.
Qed.

Lemma norm_tm_env_eq : forall TE1 TE2 t,
  (forall Z, TE1 Z = TE2 Z) -> norm_tm TE1 t = norm_tm TE2 t.
Proof.
  intros TE1 TE2 t H.
  induction t as [i | x | T b IHb | f IHf a IHa | b IHb | f IHf T | a IHa b IHb]; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply norm_ty_env_eq. auto.
    + apply IHb.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IHf. f_equal. apply norm_ty_env_eq. auto.
  - rewrite IHa, IHb. reflexivity.
Qed.

Lemma sem_env_irrel_full : forall f L T TE1 TE2 RE1 RE2 t,
  (forall Z, TE1 Z = TE2 Z) ->
  (forall Z, RE1 Z = RE2 Z) ->
  (sem f L T TE1 RE1 t <-> sem f L T TE2 RE2 t).
Proof.
  intros f. induction f as [|n IH]; intros L T TE1 TE2 RE1 RE2 t HT HE; simpl.
  - tauto.
  - destruct T as [i | X | A B | B].
    + simpl. tauto.
    + (* FVar *)
      simpl. split.
      * intro H0. destruct H0 as (Hlc & v & Hm & Hval & Hlcv & Hre).
        split; [assumption |].
        exists v. split; [assumption |]. split; [assumption |]. split; [assumption |].
        rewrite <- (norm_tm_env_eq TE1 TE2 v HT). rewrite <- (HE X). assumption.
      * intro H0. destruct H0 as (Hlc & v & Hm & Hval & Hlcv & Hre).
        split; [assumption |].
        exists v. split; [assumption |]. split; [assumption |]. split; [assumption |].
        rewrite (norm_tm_env_eq TE1 TE2 v HT). rewrite (HE X). assumption.
    + (* Arrow *)
      simpl.
      assert (HAB : forall u, sem n L A TE1 RE1 u <-> sem n L A TE2 RE2 u)
        by (intro u; apply IH; auto).
      assert (HBB : forall u, sem n L B TE1 RE1 u <-> sem n L B TE2 RE2 u)
        by (intro u; apply IH; auto).
      split.
      * intro H. destruct H as (Hlc & v & Hm & Hv & Hlcv & T0 & b & Ev & Hcl).
        split; [assumption |].
        exists v. split; [assumption |]. split; [assumption |]. split; [assumption |].
        exists T0, b. split; [assumption |].
        intros u Hvu Hlu Hnu HsemA.
        rewrite <- (norm_tm_env_eq TE1 TE2 u HT) in Hnu.
        apply (proj1 (HBB (open_tm b u))).
        apply Hcl; auto.
        apply (proj2 (HAB u)); auto.
      * intro H. destruct H as (Hlc & v & Hm & Hv & Hlcv & T0 & b & Ev & Hcl).
        split; [assumption |].
        exists v. split; [assumption |]. split; [assumption |]. split; [assumption |].
        exists T0, b. split; [assumption |].
        intros u Hvu Hlu Hnu HsemA.
        rewrite (norm_tm_env_eq TE1 TE2 u HT) in Hnu.
        apply (proj2 (HBB (open_tm b u))).
        apply Hcl; auto.
        apply (proj1 (HAB u)); auto.
    + (* All *)
      simpl. split.
      * intro H. destruct H as (Hlc & v & Hm & Hv & Hlcv & b & Ev & Hcl).
        split; [assumption |].
        exists v. split; [assumption |]. split; [assumption |]. split; [assumption |].
        exists b. split; [assumption |].
        intros X0 U Q HXL HU HUa.
        assert (HT' : forall Z, extend_ty TE1 X0 U Z = extend_ty TE2 X0 U Z).
        { intro Z. unfold extend_ty. destruct (Nat.eqb Z X0); auto. }
        assert (HE' : forall Z, extend_pred RE1 X0 Q Z = extend_pred RE2 X0 Q Z).
        { intro Z. unfold extend_pred. destruct (Nat.eqb Z X0); auto. }
        apply (proj1 (IH (X0 :: L) (open_ty B (Ty_FVar X0))
                        (extend_ty TE1 X0 U) (extend_ty TE2 X0 U)
                        (extend_pred RE1 X0 Q) (extend_pred RE2 X0 Q)
                        (open_tm_ty b (Ty_FVar X0)) HT' HE')).
        apply Hcl; auto.
      * intro H. destruct H as (Hlc & v & Hm & Hv & Hlcv & b & Ev & Hcl).
        split; [assumption |].
        exists v. split; [assumption |]. split; [assumption |]. split; [assumption |].
        exists b. split; [assumption |].
        intros X0 U Q HXL HU HUa.
        assert (HT' : forall Z, extend_ty TE1 X0 U Z = extend_ty TE2 X0 U Z).
        { intro Z. unfold extend_ty. destruct (Nat.eqb Z X0); auto. }
        assert (HE' : forall Z, extend_pred RE1 X0 Q Z = extend_pred RE2 X0 Q Z).
        { intro Z. unfold extend_pred. destruct (Nat.eqb Z X0); auto. }
        apply (proj2 (IH (X0 :: L) (open_ty B (Ty_FVar X0))
                        (extend_ty TE1 X0 U) (extend_ty TE2 X0 U)
                        (extend_pred RE1 X0 Q) (extend_pred RE2 X0 Q)
                        (open_tm_ty b (Ty_FVar X0)) HT' HE')).
        apply Hcl; auto.
Qed.

(* --------------------------------------------------------------------- *)
(* Environment irrelevance at an atom absent from the type, for closed    *)
(* (atom-free) terms.                                                    *)
(* --------------------------------------------------------------------- *)

Lemma tm_atoms_of_multistep : forall t v,
  t -->* v -> tm_atoms t = [] -> tm_atoms v = [].
Proof.
  intros t v Hm H. apply tm_atoms_nil_of_no_in. intros Z HZ.
  pose proof (multi_atoms t v Hm Z HZ). rewrite H in H0. inversion H0.
Qed.

Lemma tm_atoms_open_tm_nil : forall b u,
  tm_atoms b = [] -> tm_atoms u = [] -> tm_atoms (open_tm b u) = [].
Proof.
  intros b u Hb Hu. apply tm_atoms_nil_of_no_in. intros Z HZ.
  apply tm_atoms_open_tm_rec with (k := 0) in HZ as [HZ|HZ];
    [rewrite Hb in HZ | rewrite Hu in HZ]; inversion HZ.
Qed.

Lemma tm_atoms_open_tm_ty_nil : forall b X U,
  tm_atoms b = [] -> ty_atoms U = [] ->
  tm_atoms (open_tm_ty_rec X U b) = [].
Proof.
  intros b X U Hb HU. apply tm_atoms_nil_of_no_in. intros Z HZ.
  apply tm_atoms_open_tm_ty_rec with (k := X) in HZ as [HZ|HZ];
    [rewrite Hb in HZ | rewrite HU in HZ]; inversion HZ.
Qed.

Lemma tm_atoms_open_tm_ty_nil0 : forall b U,
  tm_atoms b = [] -> ty_atoms U = [] -> tm_atoms (open_tm_ty b U) = [].
Proof. intros. unfold open_tm_ty. apply tm_atoms_open_tm_ty_nil; auto. Qed.

Lemma sem_avoid_fvar : forall f L T TE1 TE2 RE1 RE2 X t,
  closed_tyenv TE1 -> closed_tyenv TE2 ->
  f >= ty_size T ->
  ~ In X (ty_atoms T) ->
  tm_atoms t = [] ->
  L_ok L T t ->
  (forall Z, Z <> X -> TE1 Z = TE2 Z) ->
  (forall Z, Z <> X -> RE1 Z = RE2 Z) ->
  (sem f L T TE1 RE1 t <-> sem f L T TE2 RE2 t).
Proof.
  intros f. induction f as [|n IH]; intros L T TE1 TE2 RE1 RE2 X t Hc1 Hc2 Hsz HX Ht0 HL HT HE.
  - simpl. tauto.
  - destruct T as [i | Y | A B | B].
    + simpl. tauto.
    + (* FVar Y *)
      assert (HY : Y <> X) by (intro Hc; subst; apply HX; simpl; auto).
      simpl. split.
      * intro H0. destruct H0 as (Hlc & v & Hm & Hval & Hlcv & Hre).
        split; [assumption |].
        exists v. split; [assumption |]. split; [assumption |]. split; [assumption |].
        assert (Hv0 : tm_atoms v = []) by (apply tm_atoms_of_multistep with (t := t); auto).
        rewrite (norm_tm_no_atoms_id TE2 v Hv0).
        rewrite <- (HE Y HY).
        rewrite (norm_tm_no_atoms_id TE1 v Hv0) in Hre.
        assumption.
      * intro H0. destruct H0 as (Hlc & v & Hm & Hval & Hlcv & Hre).
        split; [assumption |].
        exists v. split; [assumption |]. split; [assumption |]. split; [assumption |].
        assert (Hv0 : tm_atoms v = []) by (apply tm_atoms_of_multistep with (t := t); auto).
        rewrite (norm_tm_no_atoms_id TE1 v Hv0).
        rewrite (HE Y HY).
        rewrite (norm_tm_no_atoms_id TE2 v Hv0) in Hre.
        assumption.
    + (* Arrow A B *)
      assert (HXA : ~ In X (ty_atoms A)) by (intro Hc; apply HX; simpl; apply in_or_app; left; auto).
      assert (HXB : ~ In X (ty_atoms B)) by (intro Hc; apply HX; simpl; apply in_or_app; right; auto).
      assert (HszA : n >= ty_size A) by (simpl in Hsz; lia).
      assert (HszB : n >= ty_size B) by (simpl in Hsz; lia).
      simpl. split.
      * intro H0. destruct H0 as (Hlc & v & Hm & Hval & Hlcv & T0 & b & Ev & Hcl).
        assert (Hv0 : tm_atoms v = []) by (apply tm_atoms_of_multistep with (t := t); auto).
        assert (Hb0 : tm_atoms b = []).
        { apply tm_atoms_nil_of_no_in. intros Z HZ.
          assert (Hin : In Z (tm_atoms v)).
          { rewrite Ev. simpl. apply in_or_app. right. auto. }
          rewrite Hv0 in Hin. inversion Hin. }
        split; [assumption |].
        exists v. split; [assumption |]. split; [assumption |]. split; [assumption |].
        exists T0, b. split; [assumption |].
        intros u Hvu Hlu Hnu2 HsemA2.
        assert (Hu0 : tm_atoms u = []).
        { apply norm_tm_no_atoms with (TE := TE2); auto. }
        assert (Hnu1 : norm_tm TE1 u = u) by (apply norm_tm_no_atoms_id; auto).
        assert (Hbu0 : tm_atoms (open_tm b u) = []).
        { apply tm_atoms_open_tm_nil; auto. }
        assert (LA : L_ok L A u).
        { split.
          - intros Z HZ. apply (proj1 HL). simpl. apply in_or_app. left. auto.
          - intros Z HZ. rewrite Hu0 in HZ. inversion HZ. }
        assert (LB : L_ok L B (open_tm b u)).
        { split.
          - intros Z HZ. apply (proj1 HL). simpl. apply in_or_app. right. auto.
          - intros Z HZ. rewrite Hbu0 in HZ. inversion HZ. }
        assert (HiffA : sem n L A TE1 RE1 u <-> sem n L A TE2 RE2 u)
          by (apply (IH L A TE1 TE2 RE1 RE2 X u); auto).
        assert (HiffB : sem n L B TE1 RE1 (open_tm b u) <-> sem n L B TE2 RE2 (open_tm b u))
          by (apply (IH L B TE1 TE2 RE1 RE2 X (open_tm b u)); auto).
        apply (proj1 HiffB).
        apply Hcl; auto.
        apply (proj2 HiffA); auto.
      * intro H0. destruct H0 as (Hlc & v & Hm & Hval & Hlcv & T0 & b & Ev & Hcl).
        assert (Hv0 : tm_atoms v = []) by (apply tm_atoms_of_multistep with (t := t); auto).
        assert (Hb0 : tm_atoms b = []).
        { apply tm_atoms_nil_of_no_in. intros Z HZ.
          assert (Hin : In Z (tm_atoms v)).
          { rewrite Ev. simpl. apply in_or_app. right. auto. }
          rewrite Hv0 in Hin. inversion Hin. }
        split; [assumption |].
        exists v. split; [assumption |]. split; [assumption |]. split; [assumption |].
        exists T0, b. split; [assumption |].
        intros u Hvu Hlu Hnu1 HsemA1.
        assert (Hu0 : tm_atoms u = []).
        { apply norm_tm_no_atoms with (TE := TE1); auto. }
        assert (Hnu2 : norm_tm TE2 u = u) by (apply norm_tm_no_atoms_id; auto).
        assert (Hbu0 : tm_atoms (open_tm b u) = []).
        { apply tm_atoms_open_tm_nil; auto. }
        assert (LA : L_ok L A u).
        { split.
          - intros Z HZ. apply (proj1 HL). simpl. apply in_or_app. left. auto.
          - intros Z HZ. rewrite Hu0 in HZ. inversion HZ. }
        assert (LB : L_ok L B (open_tm b u)).
        { split.
          - intros Z HZ. apply (proj1 HL). simpl. apply in_or_app. right. auto.
          - intros Z HZ. rewrite Hbu0 in HZ. inversion HZ. }
        assert (HiffA : sem n L A TE1 RE1 u <-> sem n L A TE2 RE2 u)
          by (apply (IH L A TE1 TE2 RE1 RE2 X u); auto).
        assert (HiffB : sem n L B TE1 RE1 (open_tm b u) <-> sem n L B TE2 RE2 (open_tm b u))
          by (apply (IH L B TE1 TE2 RE1 RE2 X (open_tm b u)); auto).
        apply (proj2 HiffB).
        apply Hcl; auto.
        apply (proj1 HiffA); auto.
    + (* All B *)
      assert (HXB : ~ In X (ty_atoms B)) by auto.
      assert (HszB : n >= ty_size B) by (simpl in Hsz; lia).
      simpl. split.
      * intro H0. destruct H0 as (Hlc & v & Hm & Hval & Hlcv & b & Ev & Hcl).
        assert (Hv0 : tm_atoms v = []) by (apply tm_atoms_of_multistep with (t := t); auto).
        assert (Hb0 : tm_atoms b = []).
        { apply tm_atoms_nil_of_no_in. intros Z HZ.
          assert (Hin : In Z (tm_atoms v)) by (rewrite Ev; simpl; auto).
          rewrite Hv0 in Hin. inversion Hin. }
        split; [assumption |].
        exists v. split; [assumption |]. split; [assumption |]. split; [assumption |].
        exists b. split; [assumption |].
        intros X0 U Q HXL HU HUa.
        assert (Hc1' : closed_tyenv (extend_ty TE1 X0 U))
          by (apply extend_ty_closed; auto).
        assert (Hc2' : closed_tyenv (extend_ty TE2 X0 U))
          by (apply extend_ty_closed; auto).
        assert (HLtab : L_ok L (Ty_All B) (tm_tabs b)).
        { split.
          - intros Z HZ. apply (proj1 HL). auto.
          - intros Z HZ. simpl in HZ. rewrite Hb0 in HZ. inversion HZ. }
        assert (HL' : L_ok (X0 :: L) (open_ty B (Ty_FVar X0)) (open_tm_ty b (Ty_FVar X0)))
          by (apply L_ok_all_body; auto).
        assert (HszBody : n >= ty_size (open_ty B (Ty_FVar X0))).
        { unfold open_ty. rewrite ty_size_open_ty_fvar. exact HszB. }
        assert (Hnorm1 : norm_tm (extend_ty TE1 X0 U) (open_tm_ty b (Ty_FVar X0))
                         = open_tm_ty b U).
        { rewrite (norm_tm_open_tm_ty (extend_ty TE1 X0 U) (Ty_FVar X0) b Hc1').
          rewrite (norm_tm_no_atoms_id _ b Hb0). simpl.
          rewrite (extend_ty_same TE1 X0 U). reflexivity. }
        assert (Hnorm2 : norm_tm (extend_ty TE2 X0 U) (open_tm_ty b (Ty_FVar X0))
                         = open_tm_ty b U).
        { rewrite (norm_tm_open_tm_ty (extend_ty TE2 X0 U) (Ty_FVar X0) b Hc2').
          rewrite (norm_tm_no_atoms_id _ b Hb0). simpl.
          rewrite (extend_ty_same TE2 X0 U). reflexivity. }
        assert (Hsem1 : sem n (X0 :: L) (open_ty B (Ty_FVar X0))
                          (extend_ty TE1 X0 U) (extend_pred RE1 X0 Q)
                          (open_tm_ty b (Ty_FVar X0)))
          by (apply Hcl; auto).
        assert (HsemN1 : sem n (X0 :: L) (open_ty B (Ty_FVar X0))
                           (extend_ty TE1 X0 U) (extend_pred RE1 X0 Q)
                           (open_tm_ty b U)).
        { rewrite <- Hnorm1.
          apply (proj1 (sem_norm n (X0 :: L) (open_ty B (Ty_FVar X0))
                         (extend_ty TE1 X0 U) (extend_pred RE1 X0 Q)
                         (open_tm_ty b (Ty_FVar X0)) Hc1' HL' HszBody)).
          exact Hsem1. }
        destruct (Nat.eqb X0 X) eqn:EX0.
        -- apply Nat.eqb_eq in EX0. subst X0.
           assert (HT' : forall Z, extend_ty TE1 X U Z = extend_ty TE2 X U Z).
           { intro Z. unfold extend_ty. destruct (Nat.eqb Z X) eqn:EZ.
             - reflexivity.
             - apply HT. apply Nat.eqb_neq in EZ. auto. }
           assert (HE' : forall Z, extend_pred RE1 X Q Z = extend_pred RE2 X Q Z).
           { intro Z. unfold extend_pred. destruct (Nat.eqb Z X) eqn:EZ.
             - reflexivity.
             - apply HE. apply Nat.eqb_neq in EZ. auto. }
           assert (HsemN2 : sem n (X :: L) (open_ty B (Ty_FVar X))
                              (extend_ty TE2 X U) (extend_pred RE2 X Q)
                              (open_tm_ty b U)).
           { apply (proj1 (sem_env_irrel_full n (X :: L) (open_ty B (Ty_FVar X))
                             (extend_ty TE1 X U) (extend_ty TE2 X U)
                             (extend_pred RE1 X Q) (extend_pred RE2 X Q)
                             (open_tm_ty b U) HT' HE')).
             exact HsemN1. }
           apply (proj2 (sem_norm n (X :: L) (open_ty B (Ty_FVar X))
                          (extend_ty TE2 X U) (extend_pred RE2 X Q)
                          (open_tm_ty b (Ty_FVar X)) Hc2' HL' HszBody)).
           rewrite Hnorm2.
           exact HsemN2.
        -- apply Nat.eqb_neq in EX0.
           assert (HT' : forall Z, Z <> X ->
                        extend_ty TE1 X0 U Z = extend_ty TE2 X0 U Z).
           { intros Z HZ. unfold extend_ty. destruct (Nat.eqb Z X0) eqn:EZ.
             - reflexivity.
             - apply HT. apply Nat.eqb_neq in EZ. auto. }
           assert (HE' : forall Z, Z <> X ->
                        extend_pred RE1 X0 Q Z = extend_pred RE2 X0 Q Z).
           { intros Z HZ. unfold extend_pred. destruct (Nat.eqb Z X0) eqn:EZ.
             - reflexivity.
             - apply HE. apply Nat.eqb_neq in EZ. auto. }
           assert (HX_type : ~ In X (ty_atoms (open_ty B (Ty_FVar X0)))).
           { intro Hc. apply ty_atoms_open_ty_rec in Hc as [Hc|Hc].
             - apply HXB. auto.
             - simpl in Hc. destruct Hc as [Hc|[]]. subst. auto. }
           assert (Hopen0 : tm_atoms (open_tm_ty b U) = [])
             by (apply tm_atoms_open_tm_ty_nil0; auto).
           assert (HLW : L_ok (X0 :: L) (open_ty B (Ty_FVar X0)) (open_tm_ty b U)).
           { split.
             - intros Z HZ. apply (proj1 HL'). auto.
             - intros Z HZ. rewrite Hopen0 in HZ. inversion HZ. }
           assert (HiffW : sem n (X0 :: L) (open_ty B (Ty_FVar X0))
                             (extend_ty TE1 X0 U) (extend_pred RE1 X0 Q)
                             (open_tm_ty b U)
                           <-> sem n (X0 :: L) (open_ty B (Ty_FVar X0))
                             (extend_ty TE2 X0 U) (extend_pred RE2 X0 Q)
                             (open_tm_ty b U))
             by (apply (IH (X0 :: L) (open_ty B (Ty_FVar X0)) (extend_ty TE1 X0 U) (extend_ty TE2 X0 U) (extend_pred RE1 X0 Q) (extend_pred RE2 X0 Q) X (open_tm_ty b U)); auto).
           assert (HsemN2 : sem n (X0 :: L) (open_ty B (Ty_FVar X0))
                              (extend_ty TE2 X0 U) (extend_pred RE2 X0 Q)
                              (open_tm_ty b U)).
           { apply (proj1 HiffW); exact HsemN1. }
           apply (proj2 (sem_norm n (X0 :: L) (open_ty B (Ty_FVar X0))
                          (extend_ty TE2 X0 U) (extend_pred RE2 X0 Q)
                          (open_tm_ty b (Ty_FVar X0)) Hc2' HL' HszBody)).
           rewrite Hnorm2.
           exact HsemN2.
      * intro H0. destruct H0 as (Hlc & v & Hm & Hval & Hlcv & b & Ev & Hcl).
        assert (Hv0 : tm_atoms v = []) by (apply tm_atoms_of_multistep with (t := t); auto).
        assert (Hb0 : tm_atoms b = []).
        { apply tm_atoms_nil_of_no_in. intros Z HZ.
          assert (Hin : In Z (tm_atoms v)) by (rewrite Ev; simpl; auto).
          rewrite Hv0 in Hin. inversion Hin. }
        split; [assumption |].
        exists v. split; [assumption |]. split; [assumption |]. split; [assumption |].
        exists b. split; [assumption |].
        intros X0 U Q HXL HU HUa.
        assert (Hc1' : closed_tyenv (extend_ty TE1 X0 U))
          by (apply extend_ty_closed; auto).
        assert (Hc2' : closed_tyenv (extend_ty TE2 X0 U))
          by (apply extend_ty_closed; auto).
        assert (HLtab : L_ok L (Ty_All B) (tm_tabs b)).
        { split.
          - intros Z HZ. apply (proj1 HL). auto.
          - intros Z HZ. simpl in HZ. rewrite Hb0 in HZ. inversion HZ. }
        assert (HL' : L_ok (X0 :: L) (open_ty B (Ty_FVar X0)) (open_tm_ty b (Ty_FVar X0)))
          by (apply L_ok_all_body; auto).
        assert (HszBody : n >= ty_size (open_ty B (Ty_FVar X0))).
        { unfold open_ty. rewrite ty_size_open_ty_fvar. exact HszB. }
        assert (Hnorm1 : norm_tm (extend_ty TE1 X0 U) (open_tm_ty b (Ty_FVar X0))
                         = open_tm_ty b U).
        { rewrite (norm_tm_open_tm_ty (extend_ty TE1 X0 U) (Ty_FVar X0) b Hc1').
          rewrite (norm_tm_no_atoms_id _ b Hb0). simpl.
          rewrite (extend_ty_same TE1 X0 U). reflexivity. }
        assert (Hnorm2 : norm_tm (extend_ty TE2 X0 U) (open_tm_ty b (Ty_FVar X0))
                         = open_tm_ty b U).
        { rewrite (norm_tm_open_tm_ty (extend_ty TE2 X0 U) (Ty_FVar X0) b Hc2').
          rewrite (norm_tm_no_atoms_id _ b Hb0). simpl.
          rewrite (extend_ty_same TE2 X0 U). reflexivity. }
        assert (Hsem2 : sem n (X0 :: L) (open_ty B (Ty_FVar X0))
                          (extend_ty TE2 X0 U) (extend_pred RE2 X0 Q)
                          (open_tm_ty b (Ty_FVar X0)))
          by (apply Hcl; auto).
        assert (HsemN2 : sem n (X0 :: L) (open_ty B (Ty_FVar X0))
                           (extend_ty TE2 X0 U) (extend_pred RE2 X0 Q)
                           (open_tm_ty b U)).
        { rewrite <- Hnorm2.
          apply (proj1 (sem_norm n (X0 :: L) (open_ty B (Ty_FVar X0))
                         (extend_ty TE2 X0 U) (extend_pred RE2 X0 Q)
                         (open_tm_ty b (Ty_FVar X0)) Hc2' HL' HszBody)).
          exact Hsem2. }
        destruct (Nat.eqb X0 X) eqn:EX0.
        -- apply Nat.eqb_eq in EX0. subst X0.
           assert (HT' : forall Z, extend_ty TE1 X U Z = extend_ty TE2 X U Z).
           { intro Z. unfold extend_ty. destruct (Nat.eqb Z X) eqn:EZ.
             - reflexivity.
             - apply HT. apply Nat.eqb_neq in EZ. auto. }
           assert (HE' : forall Z, extend_pred RE1 X Q Z = extend_pred RE2 X Q Z).
           { intro Z. unfold extend_pred. destruct (Nat.eqb Z X) eqn:EZ.
             - reflexivity.
             - apply HE. apply Nat.eqb_neq in EZ. auto. }
           assert (HsemN1 : sem n (X :: L) (open_ty B (Ty_FVar X))
                              (extend_ty TE1 X U) (extend_pred RE1 X Q)
                              (open_tm_ty b U)).
           { apply (proj2 (sem_env_irrel_full n (X :: L) (open_ty B (Ty_FVar X))
                             (extend_ty TE1 X U) (extend_ty TE2 X U)
                             (extend_pred RE1 X Q) (extend_pred RE2 X Q)
                             (open_tm_ty b U) HT' HE')).
             exact HsemN2. }
           apply (proj2 (sem_norm n (X :: L) (open_ty B (Ty_FVar X))
                          (extend_ty TE1 X U) (extend_pred RE1 X Q)
                          (open_tm_ty b (Ty_FVar X)) Hc1' HL' HszBody)).
           rewrite Hnorm1.
           exact HsemN1.
        -- apply Nat.eqb_neq in EX0.
           assert (HT' : forall Z, Z <> X ->
                        extend_ty TE1 X0 U Z = extend_ty TE2 X0 U Z).
           { intros Z HZ. unfold extend_ty. destruct (Nat.eqb Z X0) eqn:EZ.
             - reflexivity.
             - apply HT. apply Nat.eqb_neq in EZ. auto. }
           assert (HE' : forall Z, Z <> X ->
                        extend_pred RE1 X0 Q Z = extend_pred RE2 X0 Q Z).
           { intros Z HZ. unfold extend_pred. destruct (Nat.eqb Z X0) eqn:EZ.
             - reflexivity.
             - apply HE. apply Nat.eqb_neq in EZ. auto. }
           assert (HX_type : ~ In X (ty_atoms (open_ty B (Ty_FVar X0)))).
           { intro Hc. apply ty_atoms_open_ty_rec in Hc as [Hc|Hc].
             - apply HXB. auto.
             - simpl in Hc. destruct Hc as [Hc|[]]. subst. auto. }
           assert (Hopen0 : tm_atoms (open_tm_ty b U) = [])
             by (apply tm_atoms_open_tm_ty_nil0; auto).
           assert (HLW : L_ok (X0 :: L) (open_ty B (Ty_FVar X0)) (open_tm_ty b U)).
           { split.
             - intros Z HZ. apply (proj1 HL'). auto.
             - intros Z HZ. rewrite Hopen0 in HZ. inversion HZ. }
           assert (HiffW : sem n (X0 :: L) (open_ty B (Ty_FVar X0))
                             (extend_ty TE1 X0 U) (extend_pred RE1 X0 Q)
                             (open_tm_ty b U)
                           <-> sem n (X0 :: L) (open_ty B (Ty_FVar X0))
                             (extend_ty TE2 X0 U) (extend_pred RE2 X0 Q)
                             (open_tm_ty b U))
             by (apply (IH (X0 :: L) (open_ty B (Ty_FVar X0)) (extend_ty TE1 X0 U) (extend_ty TE2 X0 U) (extend_pred RE1 X0 Q) (extend_pred RE2 X0 Q) X (open_tm_ty b U)); auto).
           assert (HsemN1 : sem n (X0 :: L) (open_ty B (Ty_FVar X0))
                              (extend_ty TE1 X0 U) (extend_pred RE1 X0 Q)
                              (open_tm_ty b U)).
           { apply (proj2 HiffW); exact HsemN2. }
           apply (proj2 (sem_norm n (X0 :: L) (open_ty B (Ty_FVar X0))
                          (extend_ty TE1 X0 U) (extend_pred RE1 X0 Q)
                          (open_tm_ty b (Ty_FVar X0)) Hc1' HL' HszBody)).
           rewrite Hnorm1.
           exact HsemN1.

Qed.

(* --------------------------------------------------------------------- *)
(* Value-level semantics and fuel invariance.                            *)
(* --------------------------------------------------------------------- *)

Lemma sem_value_iff : forall n L T TE RE v,
  value v -> lc_tm_at 0 0 v ->
  (sem (S n) L T TE RE v <->
   lc_tm_at 0 0 v /\
   match T with
   | Ty_BVar _ => False
   | Ty_FVar X => RE X (norm_tm TE v)
   | Ty_Arrow A B => exists T0 b, v = tm_abs T0 b /\
       (forall u, value u -> lc_tm_at 0 0 u -> norm_tm TE u = u ->
          sem n L A TE RE u -> sem n L B TE RE (open_tm b u))
   | Ty_All B => exists b, v = tm_tabs b /\
       (forall X U Q, ~ In X L -> wf_ty [] U -> ty_atoms U = [] ->
          sem n (X :: L) (open_ty B (Ty_FVar X)) (extend_ty TE X U)
            (extend_pred RE X Q) (open_tm_ty b (Ty_FVar X)))
   end).
Proof.
  intros n L T TE RE v Hv Hlc. destruct T as [i | X | A B | B]; simpl; split; intro H.
  - destruct H as (H1 & w & Hm & H2 & H3 & Hf); contradiction.
  - destruct H as (H1 & Hf); contradiction.
  - destruct H as (H1 & w & Hm & H2 & H3 & Hre). split; [assumption|].
    assert (Hwv : w = v) by (apply (value_multistep v w Hv Hm)). subst. assumption.
  - destruct H as (H1 & Hre). split; [assumption|].
    exists v. split; [apply multi_refl|]. split; [assumption|]. split; [assumption|]. assumption.
  - destruct H as (H1 & w & Hm & H2 & H3 & T0 & b & Ev & Hcl). split; [assumption|].
    assert (Hwv : w = v) by (apply (value_multistep v w Hv Hm)). subst.
    exists T0, b. split; [reflexivity|]. assumption.
  - destruct H as (H1 & T0 & b & Ev & Hcl). split; [assumption|].
    exists v. split; [apply multi_refl|]. split; [assumption|]. split; [assumption|].
    exists T0, b. split; [assumption|]. assumption.
  - destruct H as (H1 & w & Hm & H2 & H3 & b & Ev & Hcl). split; [assumption|].
    assert (Hwv : w = v) by (apply (value_multistep v w Hv Hm)). subst.
    exists b. split; [reflexivity|]. assumption.
  - destruct H as (H1 & b & Ev & Hcl). split; [assumption|].
    exists v. split; [apply multi_refl|]. split; [assumption|]. split; [assumption|].
    exists b. split; [assumption|]. assumption.
Qed.

Lemma sem_fuel_step : forall f L T TE RE t,
  f >= ty_size T -> (sem (S f) L T TE RE t <-> sem f L T TE RE t).
Proof.
  intros f. induction f as [|n IH]; intros L T TE RE t H.
  - destruct T; simpl in *; lia.
  - destruct T as [i | X | A B | B]; simpl.
    + tauto.
    + tauto.
    + assert (HszA : n >= ty_size A) by (simpl in H; lia).
      assert (HszB : n >= ty_size B) by (simpl in H; lia).
      split; intro H0; destruct H0 as (H1 & v & Hm & Hv & Hlcv & T0 & b & Ev & Hcl);
        split; [assumption|].
      * exists v; split; [assumption|]; split; [assumption|]; split; [assumption|].
        exists T0, b; split; [assumption|].
        intros u Hvu Hlu Hnu HsemA.
        apply (proj1 (IH L B TE RE (open_tm b u) HszB)).
        apply Hcl; auto.
        apply (proj2 (IH L A TE RE u HszA)); auto.
      * exists v; split; [assumption|]; split; [assumption|]; split; [assumption|].
        exists T0, b; split; [assumption|].
        intros u Hvu Hlu Hnu HsemA.
        apply (proj2 (IH L B TE RE (open_tm b u) HszB)).
        apply Hcl; auto.
        apply (proj1 (IH L A TE RE u HszA)); auto.
    + assert (HszB : n >= ty_size (open_ty B (Ty_FVar X))).
      { unfold open_ty. rewrite ty_size_open_ty_fvar. simpl in H. lia. }
      split; intro H0; destruct H0 as (H1 & v & Hm & Hv & Hlcv & b & Ev & Hcl);
        split; [assumption|].
      * exists v; split; [assumption|]; split; [assumption|]; split; [assumption|].
        exists b; split; [assumption|].
        intros X0 U Q HXL HU HUa.
        apply (proj1 (IH (X0 :: L) (open_ty B (Ty_FVar X0))
                        (extend_ty TE X0 U) (extend_pred RE X0 Q)
                        (open_tm_ty b (Ty_FVar X0)) HszB)).
        apply Hcl; auto.
      * exists v; split; [assumption|]; split; [assumption|]; split; [assumption|].
        exists b; split; [assumption|].
        intros X0 U Q HXL HU HUa.
        apply (proj2 (IH (X0 :: L) (open_ty B (Ty_FVar X0))
                        (extend_ty TE X0 U) (extend_pred RE X0 Q)
                        (open_tm_ty b (Ty_FVar X0)) HszB)).
        apply Hcl; auto.
Qed.

Lemma sem_fuel_ge : forall f L T TE RE t,
  f >= ty_size T -> (sem f L T TE RE t <-> sem (ty_size T) L T TE RE t).
Proof.
  intros f. induction f as [|n IH]; intros L T TE RE t H.
  - destruct T; simpl in *; lia.
  - destruct (le_lt_eq_dec (ty_size T) (S n) H) as [Hlt|Heq].
    + assert (Hn : n >= ty_size T) by lia.
      split; intro H0.
      * apply (proj1 (IH L T TE RE t Hn)).
        apply (proj1 (sem_fuel_step n L T TE RE t Hn)); exact H0.
      * apply (proj2 (sem_fuel_step n L T TE RE t Hn)).
        apply (proj2 (IH L T TE RE t Hn)); exact H0.
    + subst. tauto.
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
  (* Complete the proof of the free theorem. *)
Qed.

End SystemFParametricityNondeterminismHardTask.
