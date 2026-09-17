(** System F CBV strong-normalization benchmark, Medium variant.
    Features: none. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNoneMediumTask.

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

(** Auxiliary locally-nameless infrastructure. *)

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
  | tm_abs _ t1 => fv_tm t1
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t1 => fv_tm t1
  | tm_tapp t1 _ => fv_tm t1
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t1 => fv_ty T ++ ftv_tm t1
  | tm_app t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | tm_tabs t1 => ftv_tm t1
  | tm_tapp t1 T => ftv_tm t1 ++ fv_ty T
  end.

Fixpoint fv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fv_ty T ++ fv_context Gamma'
  end.

Definition fresh_atom (L : list atom) : atom :=
  S (fold_right Nat.max 0 L).

Lemma in_fold_max : forall x L, In x L -> x <= fold_right Nat.max 0 L.
Proof.
  intros x L H. induction L as [|a L IH]; simpl in *.
  - contradiction.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_atom_notin : forall L, ~ In (fresh_atom L) L.
Proof.
  intros L H. unfold fresh_atom in H.
  pose proof (in_fold_max _ _ H). lia.
Qed.

Definition type_update (theta : type_substitution) (X : atom) (U : ty) :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition term_update (gamma : term_substitution) (x : atom) (v : tm) :=
  fun y => if Nat.eqb x y then v else gamma y.

Lemma lc_ty_weaken : forall k k' T,
  lc_ty_at k T -> k <= k' -> lc_ty_at k' T.
Proof.
  intros k k' T H. generalize dependent k'.
  induction H; intros k' Hle.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
Qed.

Lemma lc_tm_weaken : forall K k K' k' t,
  lc_tm_at K k t -> K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k K' k' t H. generalize dependent K'. generalize dependent k'.
  induction H; intros k' Hk K' HK.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_weaken; eauto.
    + apply IHlc_tm_at; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
  - apply lc_tm_tapp; eauto using lc_ty_weaken.
Qed.

Lemma lc_ty_open_var_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IHT; eassumption.
Qed.

Lemma lc_tm_open_var_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IHt; eassumption.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma lc_tm_open_ty_var_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H.
  - inversion H; subst. constructor. assumption.
  - constructor.
  - inversion H; subst. constructor.
    + eapply lc_ty_open_var_inv; eassumption.
    + eapply IHt; eassumption.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IHt; eassumption.
  - inversion H; subst. constructor.
    + eapply IHt; eassumption.
    + eapply lc_ty_open_var_inv; eassumption.
Qed.

Lemma lc_ty_open_closed : forall T k U,
  lc_ty_at (S k) T -> lc_ty_at k U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; simpl; inversion HT; subst.
  - destruct (Nat.eqb k n) eqn:E.
    + exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHT.
    + assumption.
    + eapply lc_ty_weaken; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H as
      [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 |
       L Delta T Hopen IHopen].
  - constructor.
  - constructor; assumption.
  - constructor. set (X := fresh_atom L).
    apply (lc_ty_open_var_inv T 0 X).
    apply IHopen. apply fresh_atom_notin.
Qed.

Lemma typing_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H. induction H as
      [Delta Gamma x T Hlook Hwf |
       L Delta Gamma T1 t2 T2 Hwf Hbody IHbody |
       Delta Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2 |
       L Delta Gamma t T Hbody IHbody |
       Delta Gamma t T U Ht IHt HU].
  - apply wf_ty_lc in Hwf. exact Hwf.
  - constructor.
    + apply wf_ty_lc in Hwf. exact Hwf.
    + set (x := fresh_atom L).
      exact (IHbody x (fresh_atom_notin L)).
  - inversion IH1; assumption.
  - constructor. set (X := fresh_atom L).
    apply (lc_ty_open_var_inv T 0 X).
    exact (IHbody X (fresh_atom_notin L)).
  - inversion IHt; subst.
    eapply lc_ty_open_closed.
    + exact H1.
    + apply wf_ty_lc in HU. exact HU.
Qed.

Lemma typing_tm_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H as
      [Delta Gamma x T Hlook Hwf |
       L Delta Gamma T1 t2 T2 Hwf Hbody IHbody |
       Delta Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2 |
       L Delta Gamma t T Hbody IHbody |
       Delta Gamma t T U Ht IHt HU].
  - constructor.
  - constructor.
    + apply wf_ty_lc in Hwf. exact Hwf.
    + set (x := fresh_atom L).
      apply (lc_tm_open_var_inv t2 0 0 x).
      exact (IHbody x (fresh_atom_notin L)).
  - constructor; assumption.
  - constructor. set (X := fresh_atom L).
    apply (lc_tm_open_ty_var_inv t 0 0 X).
    exact (IHbody X (fresh_atom_notin L)).
  - apply lc_tm_tapp.
    + exact IHt.
    + apply wf_ty_lc in HU. exact HU.
Qed.

Lemma instantiate_ty_lc : forall theta T k,
  type_substitution_closed theta -> lc_ty_at k T ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  intros theta T k Htheta HT. induction HT; simpl.
  - apply lc_ty_bvar. assumption.
  - apply lc_ty_weaken with (k := 0).
    + apply Htheta.
    + lia.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. assumption.
Qed.

Lemma instantiate_lc : forall theta gamma t K k,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma t K k Htheta Hgamma Ht. induction Ht; simpl.
  - apply lc_tm_bvar. assumption.
  - apply lc_tm_weaken with (K := 0) (k := 0).
    + apply Hgamma.
    + lia.
    + lia.
  - apply lc_tm_abs.
    + eapply instantiate_ty_lc; eauto.
    + assumption.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. assumption.
  - apply lc_tm_tapp.
    + assumption.
    + eapply instantiate_ty_lc; eauto.
Qed.

Lemma open_ty_rec_lc_noop : forall T K k U,
  lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  intros T K k U H. generalize dependent k.
  induction H; intros j Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E; auto.
    apply Nat.eqb_eq in E. lia.
  - reflexivity.
  - rewrite IHlc_ty_at1, IHlc_ty_at2; auto.
  - rewrite IHlc_ty_at; auto; lia.
Qed.

Lemma open_tm_rec_lc_noop : forall t K d k u,
  lc_tm_at K d t -> d <= k -> open_tm_rec k u t = t.
Proof.
  intros t K d k u H. generalize dependent k.
  induction H; intros j Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E; auto.
    apply Nat.eqb_eq in E. lia.
  - reflexivity.
  - rewrite IHlc_tm_at; auto; lia.
  - rewrite IHlc_tm_at1, IHlc_tm_at2; auto.
  - rewrite IHlc_tm_at; auto.
  - rewrite IHlc_tm_at; auto.
Qed.

Lemma open_tm_ty_rec_lc_noop : forall t K d k U,
  lc_tm_at K d t -> K <= k -> open_tm_ty_rec k U t = t.
Proof.
  intros t K d k U H. generalize dependent k.
  induction H; intros j Hle; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite open_ty_rec_lc_noop with (K := K), IHlc_tm_at; auto.
  - rewrite IHlc_tm_at1, IHlc_tm_at2; auto.
  - rewrite IHlc_tm_at; auto; lia.
  - rewrite IHlc_tm_at, open_ty_rec_lc_noop with (K := K); auto.
Qed.

Lemma instantiate_ty_open_var : forall theta X U T k,
  type_substitution_closed theta ->
  ~ In X (fv_ty T) ->
  instantiate_ty (type_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k Htheta Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl; try reflexivity.
    unfold type_update. rewrite Nat.eqb_refl. reflexivity.
  - assert (X <> a) by (intro; subst; apply Hfresh; auto).
    unfold type_update. destruct (Nat.eqb X a) eqn:E; auto.
    apply Nat.eqb_eq in E. contradiction.
    symmetry. apply open_ty_rec_lc_noop with (K := 0).
    + apply Htheta.
    + lia.
  - rewrite IHT1, IHT2; auto; intro H; apply Hfresh; apply in_or_app; auto.
  - rewrite IHT; auto.
Qed.

Lemma instantiate_open_var : forall theta gamma x v t k,
  term_substitution_closed gamma ->
  ~ In x (fv_tm t) ->
  instantiate theta (term_update gamma x v)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (instantiate theta gamma t).
Proof.
  induction t; intros k Hgamma Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl; try reflexivity.
    unfold term_update. rewrite Nat.eqb_refl. reflexivity.
  - assert (x <> a) by (intro; subst; apply Hfresh; auto).
    unfold term_update. destruct (Nat.eqb x a) eqn:E; auto.
    apply Nat.eqb_eq in E. contradiction.
    symmetry. apply open_tm_rec_lc_noop with (K := 0) (d := 0).
    + apply Hgamma.
    + lia.
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt1; auto. intro H; apply Hfresh. apply in_or_app; auto.
    + apply IHt2; auto. intro H; apply Hfresh. apply in_or_app; auto.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
Qed.

Lemma instantiate_open_ty_var : forall theta gamma X U t k,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  ~ In X (ftv_tm t) ->
  instantiate (type_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros k Htheta Hgamma Hfresh; simpl in *; try reflexivity.
  - symmetry. apply open_tm_ty_rec_lc_noop with (K := 0) (d := 0).
    + apply Hgamma.
    + lia.
  - f_equal.
    + apply instantiate_ty_open_var; auto. intro H; apply Hfresh.
      apply in_or_app; auto.
    + apply IHt; auto. intro H; apply Hfresh. apply in_or_app; auto.
  - f_equal.
    + apply IHt1; auto. intro H; apply Hfresh. apply in_or_app; auto.
    + apply IHt2; auto. intro H; apply Hfresh. apply in_or_app; auto.
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt; auto. intro H; apply Hfresh. apply in_or_app; auto.
    + apply instantiate_ty_open_var; auto. intro H; apply Hfresh.
      apply in_or_app; auto.
Qed.

Lemma type_update_closed : forall theta X U,
  type_substitution_closed theta -> locally_closed_ty U ->
  type_substitution_closed (type_update theta X U).
Proof.
  intros theta X U Htheta HU Y. unfold type_update.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma term_update_closed : forall gamma x v,
  term_substitution_closed gamma -> locally_closed_tm v ->
  term_substitution_closed (term_update gamma x v).
Proof.
  intros gamma x v Hgamma Hv y. unfold term_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma lc_tm_open_closed : forall t K k u,
  lc_tm_at K (S k) t -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k u Ht Hu; simpl; inversion Ht; subst.
  - destruct (Nat.eqb k n) eqn:E.
    + exact Hu.
    + apply lc_tm_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + assumption.
    + apply IHt; auto. eapply lc_tm_weaken; eauto; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. eapply IHt; eauto.
    eapply lc_tm_weaken; eauto; lia.
  - apply lc_tm_tapp; eauto.
Qed.

Lemma lc_tm_open_ty_closed : forall t K k U,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U Ht HU; simpl; inversion Ht; subst.
  - apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_open_closed; eauto.
    + eapply IHt; eauto.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. eapply IHt; eauto.
    eapply lc_ty_weaken; eauto; lia.
  - apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply lc_ty_open_closed; eauto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma value_no_step : forall v u, value v -> ~ (v --> u).
Proof.
  intros v u Hv Hs. inversion Hv; subst; inversion Hs.
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros u Hs.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma multi_from_value : forall v u,
  value v -> v -->* u -> u = v.
Proof.
  intros v u Hv Hm. inversion Hm; subst; auto.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma expression_lifting_value : forall R v,
  value v -> R v -> expression_lifting R v.
Proof.
  intros R v Hv HR. split.
  - apply value_lc. exact Hv.
  - split.
    + apply value_sn. exact Hv.
    + intros w Hm Hw. pose proof (multi_from_value _ _ Hv Hm). subst. exact HR.
Qed.

Lemma lc_step : forall t u,
  locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hs. generalize dependent Hlc. induction Hs; intros Hlc.
  - inversion Hlc; subst.
    match goal with
    | Habs : lc_tm_at 0 0 (tm_abs _ _) |- _ => inversion Habs; subst
    end.
    eapply lc_tm_open_closed; eassumption.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply IHHs. assumption.
    + assumption.
  - inversion Hlc; subst. apply lc_tm_app.
    + assumption.
    + apply IHHs. assumption.
  - inversion Hlc; subst.
    match goal with
    | Htabs : lc_tm_at 0 0 (tm_tabs _) |- _ => inversion Htabs; subst
    end.
    eapply lc_tm_open_ty_closed; eassumption.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply IHHs. assumption.
    + assumption.
Qed.

Lemma expression_lifting_step : forall R t u,
  expression_lifting R t -> t --> u -> expression_lifting R u.
Proof.
  intros R t u [Hlc [Hsn Hvalues]] Hstep.
  split; [eapply lc_step; eauto |]. split.
  - inversion Hsn; eauto.
  - intros v Hm Hv. apply (Hvalues v); auto.
    eapply multi_step; eauto.
Qed.

Definition relation_env_total (rho : relation_env) : Prop :=
  forall X, exists a, rho X = Some a.

Lemma relation_update_total : forall rho X a,
  relation_env_total rho -> relation_env_total (relation_update rho X a).
Proof.
  intros rho X a H Y. unfold relation_update.
  destruct (Nat.eqb X Y); eauto.
Qed.

Lemma value_relation_is_value : forall eta rho T v,
  lc_ty_at (length eta) T -> relation_env_total rho ->
  value_relation eta rho T v -> value v.
Proof.
  induction T; intros v Hlc Htotal Hrel; simpl in Hrel; inversion Hlc; subst.
  - destruct (nth_error eta n) as [a|] eqn:E; try contradiction.
    eapply candidate_values; eauto.
  - destruct (Htotal a) as [c E]. rewrite E in Hrel.
    eapply candidate_values; eauto.
  - tauto.
  - tauto.
Qed.

Lemma nth_error_insert_lt : forall (A : Type) (pre tail : list A) a n,
  n < length pre ->
  nth_error (pre ++ tail) n = nth_error (pre ++ a :: tail) n.
Proof.
  intros A pre. induction pre as [|b pre IH]; intros tail a n H; simpl in *.
  - lia.
  - destruct n; simpl; auto. apply IH. lia.
Qed.

Lemma nth_error_insert_at : forall (A : Type) (pre tail : list A) a,
  nth_error (pre ++ a :: tail) (length pre) = Some a.
Proof.
  intros A pre. induction pre as [|b pre IH]; intros tail a; simpl; auto.
Qed.

Lemma value_relation_tail_irrelevant : forall T pre eta1 eta2 rho v,
  lc_ty_at (length pre) T ->
  value_relation (pre ++ eta1) rho T v <->
  value_relation (pre ++ eta2) rho T v.
Proof.
  induction T; intros pre eta1 eta2 rho v Hlc; inversion Hlc; subst; simpl.
  - rewrite (@nth_error_app1 value_candidate pre eta1 n H1).
    rewrite (@nth_error_app1 value_candidate pre eta2 n H1). reflexivity.
  - reflexivity.
  - split.
    + intros [Hv [U [body [Heq Hbody]]]]. split; [exact Hv|].
      exists U, body. split; [exact Heq|]. intros arg Harg.
      apply (proj2 (IHT1 pre eta1 eta2 rho arg H2)) in Harg.
      specialize (Hbody arg Harg).
      destruct Hbody as [Hlc' [Hsn Hvals]]. split; [exact Hlc'|]; split;
        [exact Hsn|intros w Hm Hw].
      apply (proj1 (IHT2 pre eta1 eta2 rho w H3)). apply (Hvals w); auto.
    + intros [Hv [U [body [Heq Hbody]]]]. split; [exact Hv|].
      exists U, body. split; [exact Heq|]. intros arg Harg.
      apply (proj1 (IHT1 pre eta1 eta2 rho arg H2)) in Harg.
      specialize (Hbody arg Harg).
      destruct Hbody as [Hlc' [Hsn Hvals]]. split; [exact Hlc'|]; split;
        [exact Hsn|intros w Hm Hw].
      apply (proj2 (IHT2 pre eta1 eta2 rho w H3)). apply (Hvals w); auto.
  - split.
    + intros [Hv [body [Heq Hbody]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros U a HU.
      specialize (Hbody U a HU). unfold expression_lifting in *.
      destruct Hbody as [Hlc' [Hsn Hvals]]. split; [exact Hlc'|].
      split; [exact Hsn|]. intros w Hm Hw.
      apply (proj1 (IHT (a :: pre) eta1 eta2 rho w H1)).
      apply (Hvals w); auto.
    + intros [Hv [body [Heq Hbody]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros U a HU.
      specialize (Hbody U a HU). unfold expression_lifting in *.
      destruct Hbody as [Hlc' [Hsn Hvals]]. split; [exact Hlc'|].
      split; [exact Hsn|]. intros w Hm Hw.
      apply (proj2 (IHT (a :: pre) eta1 eta2 rho w H1)).
      apply (Hvals w); auto.
Qed.

Lemma value_relation_rho_update_irrelevant : forall T eta rho X a v,
  ~ In X (fv_ty T) ->
  value_relation eta (relation_update rho X a) T v <->
  value_relation eta rho T v.
Proof.
  induction T; intros eta rho X cand v Hfresh; simpl in *.
  - reflexivity.
  - assert (X <> a) by (intro; subst; apply Hfresh; auto).
    unfold relation_update. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + reflexivity.
  - assert (Hf1 : ~ In X (fv_ty T1)) by
        (intro H; apply Hfresh; apply in_or_app; auto).
    assert (Hf2 : ~ In X (fv_ty T2)) by
        (intro H; apply Hfresh; apply in_or_app; auto).
    split.
    + intros [Hv [U [body [Heq Hbody]]]]. split; [exact Hv|].
      exists U, body. split; [exact Heq|]. intros arg Harg.
      apply (proj2 (IHT1 eta rho X cand arg Hf1)) in Harg.
      specialize (Hbody arg Harg). destruct Hbody as [Hl [Hs Hvals]].
      split; [exact Hl|]. split; [exact Hs|]. intros w Hm Hw.
      apply (proj1 (IHT2 eta rho X cand w Hf2)). apply (Hvals w); auto.
    + intros [Hv [U [body [Heq Hbody]]]]. split; [exact Hv|].
      exists U, body. split; [exact Heq|]. intros arg Harg.
      apply (proj1 (IHT1 eta rho X cand arg Hf1)) in Harg.
      specialize (Hbody arg Harg). destruct Hbody as [Hl [Hs Hvals]].
      split; [exact Hl|]. split; [exact Hs|]. intros w Hm Hw.
      apply (proj2 (IHT2 eta rho X cand w Hf2)). apply (Hvals w); auto.
  - split.
    + intros [Hv [body [Heq Hbody]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros U b HU.
      specialize (Hbody U b HU). destruct Hbody as [Hl [Hs Hvals]].
      split; [exact Hl|]. split; [exact Hs|]. intros w Hm Hw.
      apply (proj1 (IHT (b :: eta) rho X cand w Hfresh)).
      apply (Hvals w); auto.
    + intros [Hv [body [Heq Hbody]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros U b HU.
      specialize (Hbody U b HU). destruct Hbody as [Hl [Hs Hvals]].
      split; [exact Hl|]. split; [exact Hs|]. intros w Hm Hw.
      apply (proj2 (IHT (b :: eta) rho X cand w Hfresh)).
      apply (Hvals w); auto.
Qed.

Lemma value_relation_open_fvar : forall T pre eta rho X a v,
  lc_ty_at (S (length pre)) T -> ~ In X (fv_ty T) ->
  value_relation (pre ++ eta) (relation_update rho X a)
    (open_ty_rec (length pre) (Ty_FVar X) T) v <->
  value_relation (pre ++ a :: eta) rho T v.
Proof.
  induction T; intros pre eta rho X cand v Hlc Hfresh;
    inversion Hlc; subst; simpl in *.
  - destruct (Nat.eqb (length pre) n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      cbn [value_relation]. unfold relation_update. rewrite Nat.eqb_refl.
      rewrite nth_error_insert_at. reflexivity.
    + apply Nat.eqb_neq in E. assert (n < length pre) by lia.
      cbn [value_relation].
      rewrite (nth_error_insert_lt _ pre eta cand n H).
      reflexivity.
  - assert (X <> a) by (intro; subst; apply Hfresh; auto).
    unfold relation_update. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + reflexivity.
  - assert (Hf1 : ~ In X (fv_ty T1)) by
        (intro H; apply Hfresh; apply in_or_app; auto).
    assert (Hf2 : ~ In X (fv_ty T2)) by
        (intro H; apply Hfresh; apply in_or_app; auto).
    split.
    + intros [Hv [U [body [Heq Hbody]]]]. split; [exact Hv|].
      exists U, body. split; [exact Heq|]. intros arg Harg.
      apply (proj2 (IHT1 pre eta rho X cand arg H2 Hf1)) in Harg.
      specialize (Hbody arg Harg). destruct Hbody as [Hl [Hs Hvals]].
      split; [exact Hl|]. split; [exact Hs|]. intros w Hm Hw.
      apply (proj1 (IHT2 pre eta rho X cand w H3 Hf2)). apply (Hvals w); auto.
    + intros [Hv [U [body [Heq Hbody]]]]. split; [exact Hv|].
      exists U, body. split; [exact Heq|]. intros arg Harg.
      apply (proj1 (IHT1 pre eta rho X cand arg H2 Hf1)) in Harg.
      specialize (Hbody arg Harg). destruct Hbody as [Hl [Hs Hvals]].
      split; [exact Hl|]. split; [exact Hs|]. intros w Hm Hw.
      apply (proj2 (IHT2 pre eta rho X cand w H3 Hf2)). apply (Hvals w); auto.
  - split.
    + intros [Hv [body [Heq Hbody]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros U b HU.
      specialize (Hbody U b HU). destruct Hbody as [Hl [Hs Hvals]].
      split; [exact Hl|]. split; [exact Hs|]. intros w Hm Hw.
      apply (proj1 (IHT (b :: pre) eta rho X cand w H1 Hfresh)).
      apply (Hvals w); auto.
    + intros [Hv [body [Heq Hbody]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros U b HU.
      specialize (Hbody U b HU). destruct Hbody as [Hl [Hs Hvals]].
      split; [exact Hl|]. split; [exact Hs|]. intros w Hm Hw.
      apply (proj2 (IHT (b :: pre) eta rho X cand w H1 Hfresh)).
      apply (Hvals w); auto.
Qed.

Lemma value_relation_open_candidate : forall T pre eta rho U a v,
  lc_ty_at (S (length pre)) T -> locally_closed_ty U ->
  (forall w, candidate_relation a w <-> value_relation eta rho U w) ->
  value_relation (pre ++ eta) rho (open_ty_rec (length pre) U T) v <->
  value_relation (pre ++ a :: eta) rho T v.
Proof.
  induction T; intros pre eta rho U cand v Hlc HU Ha;
    inversion Hlc; subst; simpl in *.
  - destruct (Nat.eqb (length pre) n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. rewrite nth_error_insert_at.
      specialize (value_relation_tail_irrelevant U [] (pre ++ eta) eta rho v HU)
        as Hirr. simpl in Hirr. specialize (Ha v). tauto.
    + apply Nat.eqb_neq in E. assert (n < length pre) by lia.
      cbn [value_relation].
      rewrite (nth_error_insert_lt _ pre eta cand n H). reflexivity.
  - reflexivity.
  - split.
    + intros [Hv [V [body [Heq Hbody]]]]. split; [exact Hv|].
      exists V, body. split; [exact Heq|]. intros arg Harg.
      apply (proj2 (IHT1 pre eta rho U cand arg H2 HU Ha)) in Harg.
      specialize (Hbody arg Harg). destruct Hbody as [Hl [Hs Hvals]].
      split; [exact Hl|]. split; [exact Hs|]. intros w Hm Hw.
      apply (proj1 (IHT2 pre eta rho U cand w H3 HU Ha)). apply (Hvals w); auto.
    + intros [Hv [V [body [Heq Hbody]]]]. split; [exact Hv|].
      exists V, body. split; [exact Heq|]. intros arg Harg.
      apply (proj1 (IHT1 pre eta rho U cand arg H2 HU Ha)) in Harg.
      specialize (Hbody arg Harg). destruct Hbody as [Hl [Hs Hvals]].
      split; [exact Hl|]. split; [exact Hs|]. intros w Hm Hw.
      apply (proj2 (IHT2 pre eta rho U cand w H3 HU Ha)). apply (Hvals w); auto.
  - split.
    + intros [Hv [body [Heq Hbody]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros V b HV.
      specialize (Hbody V b HV). destruct Hbody as [Hl [Hs Hvals]].
      split; [exact Hl|]. split; [exact Hs|]. intros w Hm Hw.
      apply (proj1 (IHT (b :: pre) eta rho U cand w H1 HU Ha)).
      apply (Hvals w); auto.
    + intros [Hv [body [Heq Hbody]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros V b HV.
      specialize (Hbody V b HV). destruct Hbody as [Hl [Hs Hvals]].
      split; [exact Hl|]. split; [exact Hs|]. intros w Hm Hw.
      apply (proj2 (IHT (b :: pre) eta rho U cand w H1 HU Ha)).
      apply (Hvals w); auto.
Qed.

Lemma expression_lifting_congr : forall R S t,
  (forall v, R v <-> S v) ->
  expression_lifting R t <-> expression_lifting S t.
Proof.
  intros R S t Hiff. unfold expression_lifting.
  split.
  - intros [Hlc [Hsn Hvals]]. split; [exact Hlc|]. split; [exact Hsn|].
    intros v Hm Hv. apply (proj1 (Hiff v)). apply (Hvals v); auto.
  - intros [Hlc [Hsn Hvals]]. split; [exact Hlc|]. split; [exact Hsn|].
    intros v Hm Hv. apply (proj2 (Hiff v)). apply (Hvals v); auto.
Qed.

Lemma expression_relation_app : forall eta rho T1 T2 t1 t2,
  expression_relation eta rho (Ty_Arrow T1 T2) t1 ->
  expression_relation eta rho T1 t2 ->
  expression_relation eta rho T2 (tm_app t1 t2).
Proof.
  intros eta rho T1 T2 t1 t2
    [Hlc1 [Hsn1 Hvals1]] [Hlc2 [Hsn2 Hvals2]].
  revert Hlc1 Hvals1 t2 Hlc2 Hsn2 Hvals2.
  induction Hsn1 as [t1 Hred1 IH1].
  intros Hlc1 Hvals1 t2 Hlc2 Hsn2 Hvals2.
  revert Hlc2 Hvals2.
  induction Hsn2 as [t2 Hred2 IH2]. intros Hlc2 Hvals2.
  assert (Hsucc : forall q, tm_app t1 t2 --> q ->
      expression_relation eta rho T2 q).
  { intros q Hstep. inversion Hstep; subst.
    - pose proof (Hvals1 (tm_abs T t) (multi_refl _) (v_abs T t H1)) as Hfun.
      pose proof (Hvals2 t2 (multi_refl _) H3) as Harg.
      simpl in Hfun. destruct Hfun as [_ [U [body [Heq Happly]]]].
      inversion Heq; subst. apply Happly. exact Harg.
    - apply (IH1 t1' H1).
      + eapply lc_step; [exact Hlc1|exact H1].
      + intros v Hm Hv. apply (Hvals1 v); auto.
        eapply multi_step; [exact H1|exact Hm].
      + exact Hlc2.
      + constructor. exact Hred2.
      + exact Hvals2.
    - match goal with Hs : t2 --> ?u |- _ => apply (IH2 u Hs) end.
      + eapply lc_step; eauto.
      + intros v Hm Hv. apply (Hvals2 v); auto.
        eapply multi_step; eauto.
  }
  unfold expression_relation, expression_lifting. split.
  - apply lc_tm_app; assumption.
  - split.
    + constructor. intros q Hstep.
      destruct (Hsucc q Hstep) as [_ [Hsn _]]. exact Hsn.
    + intros v Hm Hv. inversion Hm; subst.
      * inversion Hv.
      * destruct (Hsucc y H) as [_ [_ Hvalues]].
        apply (Hvalues v); assumption.
Qed.

Lemma expression_relation_tapp : forall eta rho T t U a,
  expression_relation eta rho (Ty_All T) t -> locally_closed_ty U ->
  expression_relation (a :: eta) rho T (tm_tapp t U).
Proof.
  intros eta rho T t U a [Hlc [Hsn Hvals]] HU.
  revert Hlc Hvals. induction Hsn as [t Hred IH]. intros Hlc Hvals.
  assert (Hsucc : forall q, tm_tapp t U --> q ->
      expression_relation (a :: eta) rho T q).
  { intros q Hstep. inversion Hstep; subst.
    - pose proof (Hvals (tm_tabs t0) (multi_refl _) (v_tabs t0 H1)) as Hall.
      simpl in Hall. destruct Hall as [_ [body [Heq Hbody]]].
      inversion Heq; subst. apply Hbody; assumption.
    - apply (IH t' H1).
      + eapply lc_step; [exact Hlc|exact H1].
      + intros v Hm Hv. apply (Hvals v); auto.
        eapply multi_step; [exact H1|exact Hm].
  }
  unfold expression_relation, expression_lifting. split.
  - apply lc_tm_tapp; assumption.
  - split.
    + constructor. intros q Hstep.
      destruct (Hsucc q Hstep) as [_ [Hsn _]]. exact Hsn.
    + intros v Hm Hv. inversion Hm; subst.
      * inversion Hv.
      * destruct (Hsucc y H) as [_ [_ Hvalues]].
        apply (Hvalues v); assumption.
Qed.

Lemma lookup_type_fv_in_context : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) ->
  In X (fv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlook Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. apply in_or_app; auto.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma related_substitution_rho_update : forall rho Gamma gamma X a,
  related_substitution rho Gamma gamma -> ~ In X (fv_context Gamma) ->
  related_substitution (relation_update rho X a) Gamma gamma.
Proof.
  intros rho Gamma gamma X a Hrel Hfresh x T Hlook.
  assert (Hnot : ~ In X (fv_ty T)).
  { intro Hin. apply Hfresh. eapply lookup_type_fv_in_context; eauto. }
  apply (proj2 (value_relation_rho_update_irrelevant
    T [] rho X a (gamma x) Hnot)).
  eapply Hrel; eauto.
Qed.

Lemma related_substitution_term_update : forall rho Gamma gamma x T v,
  related_substitution rho Gamma gamma -> value_relation [] rho T v ->
  related_substitution rho ((x, T) :: Gamma) (term_update gamma x v).
Proof.
  intros rho Gamma gamma x T v Hrel Hv y U Hlook.
  simpl in Hlook. unfold term_update.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    rewrite Nat.eqb_refl in Hlook.
    inversion Hlook; subst. exact Hv.
  - rewrite Nat.eqb_sym in Hlook. rewrite E in Hlook.
    eapply Hrel; eauto.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta rho gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    relation_env_total rho ->
    related_substitution rho Gamma gamma ->
    expression_relation [] rho T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Htyping.
  induction Htyping as
      [Delta Gamma x T Hlook Hwf |
       L Delta Gamma T1 t2 T2 Hwf Hbody IHbody |
       Delta Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2 |
       L Delta Gamma t T Hbody IHbody |
       Delta Gamma t T U Ht IHt HwfU];
    intros theta rho gamma Htheta Hgamma Htotal Hrelated; simpl in *.
  - apply expression_lifting_value.
    + apply value_relation_is_value with (eta := []) (rho := rho) (T := T).
      * apply wf_ty_lc in Hwf. exact Hwf.
      * exact Htotal.
      * eapply Hrelated; eauto.
    + eapply Hrelated; eauto.
  - assert (Habs_lc : locally_closed_tm (tm_abs T1 t2)).
    { eapply typing_tm_lc. eapply T_Abs with (L := L) (T2 := T2); eauto. }
    apply expression_lifting_value.
    + apply v_abs. exact (instantiate_lc theta gamma (tm_abs T1 t2)
        0 0 Htheta Hgamma Habs_lc).
    + split.
      * apply v_abs. exact (instantiate_lc theta gamma (tm_abs T1 t2)
          0 0 Htheta Hgamma Habs_lc).
      * exists (instantiate_ty theta T1), (instantiate theta gamma t2).
        split; [reflexivity|]. intros arg Harg.
        set (x := fresh_atom (L ++ fv_tm t2)).
        assert (Hxall : ~ In x (L ++ fv_tm t2)).
        { subst x. apply fresh_atom_notin. }
        assert (HxL : ~ In x L).
        { intro H. apply Hxall. apply in_or_app; auto. }
        assert (Hxt : ~ In x (fv_tm t2)).
        { intro H. apply Hxall. apply in_or_app; auto. }
        specialize (IHbody x HxL theta rho (term_update gamma x arg)
          Htheta).
        assert (Hargc : locally_closed_tm arg).
        { apply value_lc. eapply value_relation_is_value
            with (eta := []) (rho := rho) (T := T1).
          - apply wf_ty_lc in Hwf. exact Hwf.
          - exact Htotal.
          - exact Harg. }
        pose proof (IHbody (term_update_closed _ _ _ Hgamma Hargc)
          Htotal (related_substitution_term_update _ _ _ _ _ _
            Hrelated Harg)) as Hfund.
        unfold open_tm in Hfund |- *.
        rewrite (instantiate_open_var theta gamma x arg t2 0 Hgamma Hxt)
          in Hfund. exact Hfund.
  - eapply expression_relation_app with (T1 := T1).
    + apply IH1; assumption.
    + apply IH2; assumption.
  - assert (Htabs_lc : locally_closed_tm (tm_tabs t)).
    { eapply typing_tm_lc. eapply T_TAbs with (L := L); eauto. }
    assert (Hall_lc : locally_closed_ty (Ty_All T)).
    { eapply typing_type_lc. eapply T_TAbs with (L := L); eauto. }
    apply expression_lifting_value.
    + apply v_tabs. exact (instantiate_lc theta gamma (tm_tabs t)
        0 0 Htheta Hgamma Htabs_lc).
    + split.
      * apply v_tabs. exact (instantiate_lc theta gamma (tm_tabs t)
          0 0 Htheta Hgamma Htabs_lc).
      * exists (instantiate theta gamma t). split; [reflexivity|].
        intros U0 a HU0.
        set (X := fresh_atom
          (L ++ ftv_tm t ++ fv_ty T ++ fv_context Gamma)).
        assert (HXall :
          ~ In X (L ++ ftv_tm t ++ fv_ty T ++ fv_context Gamma)).
        { subst X. apply fresh_atom_notin. }
        assert (HXL : ~ In X L).
        { intro H. apply HXall. repeat (apply in_or_app; left); exact H. }
        assert (HXt : ~ In X (ftv_tm t)).
        { intro H. apply HXall. apply in_or_app. right.
          apply in_or_app. left. exact H. }
        assert (HXT : ~ In X (fv_ty T)).
        { intro H. apply HXall. apply in_or_app. right.
          apply in_or_app. right. apply in_or_app. left. exact H. }
        assert (HXG : ~ In X (fv_context Gamma)).
        { intro H. apply HXall. apply in_or_app. right.
          apply in_or_app. right. apply in_or_app. right. exact H. }
        specialize (IHbody X HXL (type_update theta X U0)
          (relation_update rho X a) gamma).
        assert (Hfund := IHbody
          (type_update_closed _ _ _ Htheta HU0) Hgamma
          (relation_update_total _ _ _ Htotal)
          (related_substitution_rho_update _ _ _ _ _ Hrelated HXG)).
        unfold open_tm_ty in Hfund.
        rewrite (instantiate_open_ty_var theta gamma X U0 t 0
          Htheta Hgamma HXt) in Hfund.
        assert (Hsem : forall v,
          value_relation [] (relation_update rho X a)
            (open_ty T (Ty_FVar X)) v <->
          value_relation [a] rho T v).
        { intros v. apply (value_relation_open_fvar
            T [] [] rho X a v).
          - inversion Hall_lc; assumption.
          - exact HXT. }
        apply (proj1 (expression_lifting_congr
          (value_relation [] (relation_update rho X a)
             (open_ty T (Ty_FVar X)))
          (value_relation [a] rho T)
          (open_tm_ty (instantiate theta gamma t) U0) Hsem)).
        exact Hfund.
  - pose proof (wf_ty_lc _ _ HwfU) as HUlc.
    pose proof (instantiate_ty_lc theta U 0 Htheta HUlc) as HinstU.
    set (a := {| candidate_relation := value_relation [] rho U;
      candidate_values := fun v Hv =>
        value_relation_is_value [] rho U v HUlc Htotal Hv |}).
    pose proof (expression_relation_tapp [] rho T
      (instantiate theta gamma t) (instantiate_ty theta U) a
      (IHt theta rho gamma Htheta Hgamma Htotal Hrelated) HinstU) as Happ.
    assert (Hsem : forall v,
      value_relation [] rho (open_ty T U) v <->
      value_relation [a] rho T v).
    { intros v. apply (value_relation_open_candidate
        T [] [] rho U a v).
      - pose proof (typing_type_lc _ _ _ _ Ht) as Halllc.
        inversion Halllc; assumption.
      - exact HUlc.
      - intros w. reflexivity. }
    apply (proj2 (expression_lifting_congr
      (value_relation [] rho (open_ty T U))
      (value_relation [a] rho T)
      (tm_tapp (instantiate theta gamma t) (instantiate_ty theta U)) Hsem)).
    exact Happ.
Qed.

Definition identity_type_substitution : type_substitution :=
  fun X => Ty_FVar X.

Definition identity_term_substitution : term_substitution :=
  fun x => tm_fvar x.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof.
  induction T; simpl; unfold identity_type_substitution in *;
    f_equal; assumption.
Qed.

Lemma instantiate_identity : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; simpl; unfold identity_term_substitution in *; try reflexivity.
  - rewrite instantiate_ty_identity, IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt, instantiate_ty_identity. reflexivity.
Qed.

Definition universal_value_candidate : value_candidate :=
  {| candidate_relation := value;
     candidate_values := fun v Hv => Hv |}.

Definition total_relation_env : relation_env :=
  fun _ => Some universal_value_candidate.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Htyping.
  pose proof (fundamental [] empty t T Htyping
    identity_type_substitution total_relation_env identity_term_substitution)
    as Hfund.
  assert (Htheta : type_substitution_closed identity_type_substitution).
  { intros X. unfold identity_type_substitution. constructor. }
  assert (Hgamma : term_substitution_closed identity_term_substitution).
  { intros x. unfold identity_term_substitution. constructor. }
  assert (Hrho : relation_env_total total_relation_env).
  { intros X. exists universal_value_candidate. reflexivity. }
  assert (Hrelated : related_substitution total_relation_env empty
      identity_term_substitution).
  { intros x U Hlook. discriminate. }
  specialize (Hfund Htheta Hgamma Hrho Hrelated).
  rewrite instantiate_identity in Hfund.
  destruct Hfund as [_ [Hsn _]]. exact Hsn.
Qed.

End SystemFNormalizationNoneMediumTask.
