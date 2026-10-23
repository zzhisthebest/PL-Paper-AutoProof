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

(* Some small facts about the finite support of the locally nameless syntax. *)
Fixpoint ty_fv (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_fv T1 ++ ty_fv T2
  | Ty_All T1 => ty_fv T1
  end.

Fixpoint tm_ty_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t1 => ty_fv T ++ tm_ty_fv t1
  | tm_app t1 t2 | tm_choice t1 t2 => tm_ty_fv t1 ++ tm_ty_fv t2
  | tm_tabs t1 => tm_ty_fv t1
  | tm_tapp t1 T => tm_ty_fv t1 ++ ty_fv T
  end.

Fixpoint max_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs => max x (max_list xs)
  end.

Lemma max_list_spec : forall xs x, In x xs -> x <= max_list xs.
Proof.
  induction xs as [|a xs IH]; intros x H; simpl in H.
  - contradiction.
  - destruct H as [->|H].
    + apply Nat.le_max_l.
    + simpl. eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall xs, ~ In (S (max_list xs)) xs.
Proof.
  intros xs H. pose proof (max_list_spec xs _ H). lia.
Qed.

Fixpoint inst_ty (s : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => s X
  | Ty_Arrow T1 T2 => Ty_Arrow (inst_ty s T1) (inst_ty s T2)
  | Ty_All T1 => Ty_All (inst_ty s T1)
  end.

Fixpoint inst_tm (s : atom -> ty) (g : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => g x
  | tm_abs T t1 => tm_abs (inst_ty s T) (inst_tm s g t1)
  | tm_app t1 t2 => tm_app (inst_tm s g t1) (inst_tm s g t2)
  | tm_tabs t1 => tm_tabs (inst_tm s g t1)
  | tm_tapp t1 T => tm_tapp (inst_tm s g t1) (inst_ty s T)
  | tm_choice t1 t2 => tm_choice (inst_tm s g t1) (inst_tm s g t2)
  end.

Definition upd_ty (s : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else s Y.

Definition upd_tm (g : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else g y.

Definition upd_rel (r : atom -> tm -> tm -> Prop) (X : atom)
    (R : tm -> tm -> Prop) : atom -> tm -> tm -> Prop :=
  fun Y => if Nat.eqb X Y then R else r Y.

Definition no_fv_ty (X : atom) (T : ty) : Prop := ~ In X (ty_fv T).
Definition no_fv_tm (X : atom) (t : tm) : Prop := ~ In X (tm_ty_fv t).

Lemma ty_fv_open : forall k T U X,
  In X (ty_fv T) -> In X (ty_fv (open_ty_rec k U T)).
Proof.
  intros k T; revert k; induction T as [i|Y|T1 IH1 T2 IH2|T IH]; intros; simpl in *.
  - contradiction.
  - exact H.
  - apply in_or_app. destruct (in_app_or _ _ _ H); [left; apply IH1|right; apply IH2]; assumption.
  - apply IH; exact H.
Qed.

Lemma wf_ty_fv_in : forall Delta T X,
  wf_ty Delta T -> In X (ty_fv T) -> In X Delta.
Proof.
  intros Delta T X H; induction H; simpl; intros Hfv.
  - destruct Hfv as [<-|Hfv]; [exact H|contradiction].
  - apply in_app_or in Hfv. destruct Hfv; [apply IHwf_ty1|apply IHwf_ty2]; assumption.
  -
    (* The body may contain only variables from the surrounding context. *)
    assert (exists Y, ~ In Y L /\ Y <> X) as [Y [HYL HYX]].
    { exists (S (max_list (X :: L))). split.
      - intro HY. apply (fresh_not_in (X :: L)). simpl; right; exact HY.
      - intro E. apply (fresh_not_in (X :: L)). simpl; left; symmetry; exact E. }
    specialize (H0 Y HYL).
    pose proof (ty_fv_open 0 T (Ty_FVar Y) X Hfv) as Hopen.
    specialize (H0 Hopen).
    simpl in H0. destruct H0 as [E|E]; [contradiction|assumption].
Qed.

Lemma wf_ty_no_fv : forall T X, wf_ty [] T -> ~ In X (ty_fv T).
Proof.
  intros T X H Hf. pose proof (wf_ty_fv_in [] T X H Hf). contradiction.
Qed.

Lemma lc_ty_weaken : forall k T, lc_ty_at k T -> lc_ty_at (S k) T.
Proof.
  intros k T H; induction H; eauto; constructor; lia.
Qed.

Lemma lc_ty_open_rec_inv : forall k T U,
  lc_ty_at k U -> lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  intros k T; revert k; induction T as [i|X|T1 IH1 T2 IH2|T IH];
    intros k U HU Hopen; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + inversion Hopen. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Hopen. constructor; [apply IH1 with U|apply IH2 with U]; assumption.
  - inversion Hopen. constructor. apply IH with U; [apply lc_ty_weaken; assumption|assumption].
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - constructor.
  - constructor; assumption.
  - constructor. specialize (H0 (S (max_list L)) (fresh_not_in L)).
    apply (lc_ty_open_rec_inv 0 T (Ty_FVar (S (max_list L)))).
    + constructor.
    + apply H0.
Qed.

Lemma inst_ty_no_fv : forall s T,
  (forall Y, ~ In Y (ty_fv T)) -> inst_ty s T = T.
Proof.
  intros s T; induction T as [i|a|T1 IH1 T2 IH2|T IH]; intros H; simpl.
  - reflexivity.
  - exfalso. apply (H a). simpl. left; reflexivity.
  - f_equal.
    + change (forall Y, ~ In Y (ty_fv T1 ++ ty_fv T2)) in H.
      apply IH1. intros Y HY. apply (H Y). apply in_or_app. left; exact HY.
    + change (forall Y, ~ In Y (ty_fv T1 ++ ty_fv T2)) in H.
      apply IH2. intros Y HY. apply (H Y). apply in_or_app. right; exact HY.
  - f_equal. apply IH; exact H.
Qed.

Lemma inst_ty_open : forall k s X U T,
  no_fv_ty X T -> (forall Y, ~ In Y (ty_fv U)) ->
  inst_ty (upd_ty s X U) (open_ty_rec k (Ty_FVar X) T) =
  inst_ty s (open_ty_rec k U T).
Proof.
  intros k s X U T; revert k s X U;
    induction T as [i|Y|T1 IH1 T2 IH2|T IH]; intros k s X U H H0; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + unfold upd_ty. destruct (Nat.eqb X X) eqn:E'.
      * cbn [inst_ty]. rewrite E'. symmetry. apply inst_ty_no_fv.
        eauto.
      * exfalso. assert (Et : Nat.eqb X X = true) by (apply Nat.eqb_eq; reflexivity).
        rewrite Et in E'. discriminate.
    + reflexivity.
  - unfold upd_ty. destruct (Nat.eqb X Y) eqn:E.
    + exfalso. apply H. simpl. left. apply Nat.eqb_eq in E. symmetry; exact E.
    + reflexivity.
  - f_equal.
    + apply IH1.
      * intro Hx. apply H. simpl. apply in_or_app; left; exact Hx.
      * exact H0.
    + apply IH2.
      * intro Hx. apply H. simpl. apply in_or_app; right; exact Hx.
      * exact H0.
  - f_equal. apply IH; [exact H|exact H0].
Qed.

Lemma inst_tm_open : forall k s g X U t,
  no_fv_tm X t -> (forall Y, ~ In Y (ty_fv U)) ->
  inst_tm (upd_ty s X U) g (open_tm_ty_rec k (Ty_FVar X) t) =
  inst_tm s g (open_tm_ty_rec k U t).
Proof.
  intros k s g X U t; revert k s g X U;
    induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t1 IH1 T|t1 IH1 t2 IH2];
    intros k s g X U H H0; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply inst_ty_open.
      * intro Hx. apply H. simpl. apply in_or_app; left; exact Hx.
      * exact H0.
    + apply IH.
      * intro Hx. apply H. simpl. apply in_or_app; right; exact Hx.
      * exact H0.
  - f_equal.
    + apply IH1. intro Hx. apply H. simpl. apply in_or_app; left; exact Hx.
      exact H0.
    + apply IH2. intro Hx. apply H. simpl. apply in_or_app; right; exact Hx.
      exact H0.
  - f_equal. apply IH; [exact H|exact H0].
  - f_equal.
    + apply IH1. intro Hx. apply H. simpl. apply in_or_app; left; exact Hx.
      exact H0.
    + apply inst_ty_open. intro Hx. apply H. simpl. apply in_or_app; right; exact Hx.
      exact H0.
  - f_equal.
    + apply IH1. intro Hx. apply H. simpl. apply in_or_app; left; exact Hx.
      exact H0.
    + apply IH2. intro Hx. apply H. simpl. apply in_or_app; right; exact Hx.
      exact H0.
Qed.

Lemma lc_tm_weaken_term : forall K k t,
  lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H; induction H; eauto; constructor; lia.
Qed.

Lemma lc_tm_weaken_type : forall K k t,
  lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H; induction H; eauto using lc_ty_weaken.
Qed.

Lemma lc_tm_open_rec_inv : forall K k t u,
  lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k; induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t1 IH1 T|t1 IH1 t2 IH2];
    intros K k u Hu Ho; simpl in Ho.
  - destruct (Nat.eqb k i) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + inversion Ho. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Ho. constructor; [assumption|].
    apply IH with (u:=u); [apply lc_tm_weaken_term; exact Hu|assumption].
  - inversion Ho. constructor; [apply IH1 with (u:=u)|apply IH2 with (u:=u)];
      [exact Hu|assumption|exact Hu|assumption].
  - inversion Ho. constructor. apply IH with (u:=u).
    + apply lc_tm_weaken_type; exact Hu.
    + assumption.
  - inversion Ho. constructor.
    + apply IH1 with (u:=u); [exact Hu|assumption].
    + assumption.
  - inversion Ho. constructor.
    + apply IH1 with (u:=u); [exact Hu|assumption].
    + apply IH2 with (u:=u); [exact Hu|assumption].
Qed.

Definition rel_ok (R : tm -> tm -> Prop) : Prop :=
  forall v1 v2, R v1 v2 -> value v1 /\ value v2.

(* `mayrel` is deliberately a may relation.  Thus a choice may be related
   by choosing the same branch on the two sides. *)
Definition mayrel (R : tm -> tm -> Prop) (t1 t2 : tm) : Prop :=
  locally_closed_tm t1 /\ locally_closed_tm t2 /\
  exists v1 v2, value v1 /\ value v2 /\
    multi t1 v1 /\ multi t2 v2 /\ R v1 v2.

Definition lookup_rel (bs : list (tm -> tm -> Prop)) (i : nat) :
    tm -> tm -> Prop :=
  match nth_error bs i with Some R => R | None => fun _ _ => False end.

Fixpoint set_rel (k : nat) (R : tm -> tm -> Prop)
    (bs : list (tm -> tm -> Prop)) : list (tm -> tm -> Prop) :=
  match k, bs with
  | 0, [] => [R]
  | 0, _ :: bs' => R :: bs'
  | S k', [] => (fun _ _ => False) :: set_rel k' R []
  | S k', b :: bs' => b :: set_rel k' R bs'
  end.

Lemma lookup_rel_nil : forall i, lookup_rel [] i = (fun _ _ => False).
Proof.
  intro i. unfold lookup_rel. rewrite nth_error_nil. reflexivity.
Qed.

Fixpoint tyrel (bs : list (tm -> tm -> Prop))
    (r : atom -> tm -> tm -> Prop) (T1 T2 : ty)
    (v1 v2 : tm) : Prop :=
  match T1, T2 with
  | Ty_BVar i, Ty_BVar j =>
      if Nat.eqb i j then lookup_rel bs i v1 v2 else False
  | Ty_FVar X, Ty_FVar Y =>
      if Nat.eqb X Y then r X v1 v2 else False
  | Ty_Arrow A1 B1, Ty_Arrow A2 B2 =>
      value v1 /\ value v2 /\
      forall a1 a2, tyrel bs r A1 A2 a1 a2 ->
        mayrel (tyrel bs r B1 B2)
          (tm_app v1 a1) (tm_app v2 a2)
  | Ty_All A1, Ty_All A2 =>
      value v1 /\ value v2 /\
      exists b1 b2, v1 = tm_tabs b1 /\ v2 = tm_tabs b2 /\
      forall U1 U2, wf_ty [] U1 -> wf_ty [] U2 ->
      forall R, rel_ok R ->
        mayrel
          (tyrel (R :: bs) r A1 A2)
          (open_tm_ty b1 U1) (open_tm_ty b2 U2)
  | _, _ => False
  end.

Lemma lookup_set_rel : forall bs k R i,
  lookup_rel (set_rel k R bs) i =
  if Nat.eqb k i then R else lookup_rel bs i.
Proof.
  intros bs k; revert bs; induction k as [|k IH]; intros bs R i.
  - destruct bs as [|b bs].
    + destruct i as [|i].
      * reflexivity.
      * unfold lookup_rel, set_rel. assert (E : nth_error [R] (S i) = None).
        { apply nth_error_None. simpl; lia. }
        rewrite E. reflexivity.
    + destruct i as [|i]; simpl; reflexivity.
  - destruct bs as [|b bs].
    + destruct i as [|i].
      * unfold lookup_rel, set_rel. simpl. reflexivity.
      * change (lookup_rel (set_rel k R []) i =
          if Nat.eqb (S k) (S i) then R else lookup_rel [] (S i)).
        rewrite IH. rewrite lookup_rel_nil. simpl. reflexivity.
    + destruct i as [|i]; simpl; [reflexivity|].
      change (lookup_rel (set_rel k R bs) i =
          if Nat.eqb (S k) (S i) then R else lookup_rel (b :: bs) (S i)).
      rewrite IH. unfold lookup_rel. simpl. reflexivity.
Qed.

Lemma mayrel_ext : forall P Q t1 t2,
  (forall v1 v2, P v1 v2 <-> Q v1 v2) ->
  (mayrel P t1 t2 <-> mayrel Q t1 t2).
Proof.
  intros P Q t1 t2 H; split; intros M; destruct M as [H1 [H2 [v1 [v2 [Hv1 [Hv2 [M1 [M2 HR]]]]]]]];
    repeat split; try assumption; exists v1, v2; repeat split; try assumption;
    [apply (H v1 v2); exact HR|apply (H v1 v2); exact HR].
Qed.

Lemma open_ty_rec_arrow : forall k U A B,
  open_ty_rec k U (Ty_Arrow A B) =
  Ty_Arrow (open_ty_rec k U A) (open_ty_rec k U B).
Proof. reflexivity. Qed.

Lemma open_ty_rec_all : forall k U A,
  open_ty_rec k U (Ty_All A) = Ty_All (open_ty_rec (S k) U A).
Proof. reflexivity. Qed.

(* Lemma tyrel_open_stack : forall bs r X R k T1 T2 v1 v2,
  no_fv_ty X T1 -> no_fv_ty X T2 ->
  (tyrel bs (upd_rel r X R)
     (open_ty_rec k (Ty_FVar X) T1)
     (open_ty_rec k (Ty_FVar X) T2) v1 v2 <->
   tyrel (set_rel k R bs) r T1 T2 v1 v2).
Proof.
  intros bs r X R k T1; revert bs r X R k.
  induction T1 as [i|Y|A1 IHA1 B1 IHB1|A1 IHA1];
    intros bs r X R k T2 v1 v2 Hx1 Hx2; destruct T2 as [j|Z|A2 B2|A2];
    unfold tyrel; cbv delta [open_ty_rec] in *; simpl in *.
  - destruct (Nat.eqb k i) eqn:Eki, (Nat.eqb k j) eqn:Ekj;
      simpl in *.
    + apply Nat.eqb_eq in Eki. apply Nat.eqb_eq in Ekj. subst i. subst j.
      simpl. assert (EX : Nat.eqb X X = true) by (apply Nat.eqb_eq; reflexivity).
      rewrite EX. assert (Ek : Nat.eqb k k = true) by (apply Nat.eqb_eq; reflexivity).
      rewrite Ek. simpl. rewrite lookup_set_rel. rewrite Ek. unfold upd_rel. rewrite EX. reflexivity.
    + apply Nat.eqb_eq in Eki. apply Nat.eqb_neq in Ekj. subst i.
      assert (E : Nat.eqb k j = false) by (apply Nat.eqb_neq; exact Ekj).
      rewrite E. reflexivity.
    + apply Nat.eqb_neq in Eki. apply Nat.eqb_eq in Ekj. subst j.
      assert (E : Nat.eqb i k = false).
      { apply Nat.eqb_neq. intro E'. apply Eki. symmetry. exact E'. }
      rewrite E. reflexivity.
    + assert (Eki' : Nat.eqb i k = false) by
          (apply Nat.eqb_neq; intro E';
           apply (proj1 (Nat.eqb_neq _ _) Eki); symmetry; exact E').
      assert (Ekj' : Nat.eqb j k = false) by
          (apply Nat.eqb_neq; intro E';
           apply (proj1 (Nat.eqb_neq _ _) Ekj); symmetry; exact E').
      rewrite (lookup_set_rel bs k R i).
      destruct (Nat.eqb k i) eqn:Q; simpl.
      * exfalso. discriminate Eki.
      * reflexivity.
  - destruct (Nat.eqb k i) eqn:Ek.
    + destruct (Nat.eqb X Z) eqn:EX.
      * apply Nat.eqb_eq in EX. subst Z. simpl in Hx2. exfalso.
        apply Hx2. left; reflexivity.
      * unfold tyrel. destruct (Nat.eqb Z X) eqn:EZ; simpl.
        -- apply Nat.eqb_eq in EZ. subst Z. exfalso. apply Hx2. left; reflexivity.
        -- reflexivity.
    + simpl. reflexivity.
  - destruct (Nat.eqb k i); simpl; reflexivity.
  - destruct (Nat.eqb k i); simpl; reflexivity.
  - destruct (Nat.eqb k j) eqn:Ek; destruct (Nat.eqb X Y) eqn:EX;
      simpl in *; try tauto.
    all: unfold tyrel; simpl in *; try tauto; try reflexivity.
    all: destruct (Nat.eqb Y X) eqn:EY; simpl in *;
      try (apply Nat.eqb_eq in EY; subst X; exfalso; apply Hx1; left; reflexivity);
      try reflexivity.
  - unfold upd_rel. destruct (Nat.eqb X Y) eqn:E1, (Nat.eqb X Z) eqn:E2,
      (Nat.eqb Y Z) eqn:E3; simpl in *; try tauto.
    all: unfold upd_rel; simpl in *; try tauto.
    all: try (apply Nat.eqb_eq in E1; subst Y; exfalso; apply Hx1; left; reflexivity).
    all: try (apply Nat.eqb_eq in E2; subst Z; exfalso; apply Hx2; left; reflexivity).
    all: match goal with |- ?G => idtac G end.
  - reflexivity.
  - reflexivity.
  - destruct (Nat.eqb k j); simpl; reflexivity.
  - reflexivity.
  - assert (Hxa : no_fv_ty X A1) by (intro H; apply Hx1; apply in_or_app; left; exact H).
    assert (Hxb : no_fv_ty X B1) by (intro H; apply Hx1; apply in_or_app; right; exact H).
    assert (Hya : no_fv_ty X A2) by (intro H; apply Hx2; apply in_or_app; left; exact H).
    assert (Hyb : no_fv_ty X B2) by (intro H; apply Hx2; apply in_or_app; right; exact H).
    cbn in *.
    + rewrite (IHA1 bs r X R k A2 v1 v2 Hxa Hya).
      rewrite (IHB1 bs r X R k B2 v1 v2 Hxb Hyb).
      reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - destruct Hx1 as [Hxa|Hxb]; destruct Hx2 as [Hya|Hyb]; simpl in *.
    + (* the universal case; recurse under the newly bound relation *)
      reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed. *)

Lemma multi_trans : forall a b c, multi a b -> multi b c -> multi a c.
Proof.
  intros a b c H; induction H; eauto using multi.
Qed.

Lemma multi_app_left : forall a a' b,
  multi a a' -> locally_closed_tm b -> multi (tm_app a b) (tm_app a' b).
Proof.
  intros a a' b H; induction H; eauto using multi, step.
Qed.

Lemma multi_app_right : forall v a a',
  value v -> multi a a' -> multi (tm_app v a) (tm_app v a').
Proof.
  intros v a a' Hv H; induction H; eauto using multi, step.
Qed.

Lemma multi_tapp : forall a a' U,
  multi a a' -> locally_closed_ty U -> multi (tm_tapp a U) (tm_tapp a' U).
Proof.
  intros a a' U H; induction H; eauto using multi, step.
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
  intros t H U v HU Hv Htv.
  induction H; simpl in *; eauto using multi, step.
Qed.

End SystemFParametricityNondeterminismHardTask.
