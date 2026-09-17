(** System F CBV strong-normalization benchmark, Medium variant.
    Features: if. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfMediumTask.

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

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* Some elementary support and erasure facts.  The latter are useful because
   the reduction relation is insensitive to type annotations, although local
   closure still checks those annotations. *)

Fixpoint ty_fv (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_fv T1 ++ ty_fv T2
  | Ty_All T1 => ty_fv T1
  | Ty_Bool => []
  end.

Fixpoint tm_ty_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T t1 => ty_fv T ++ tm_ty_fv t1
  | tm_app t1 t2 => tm_ty_fv t1 ++ tm_ty_fv t2
  | tm_tabs t1 => tm_ty_fv t1
  | tm_tapp t1 T => tm_ty_fv t1 ++ ty_fv T
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => tm_ty_fv t1 ++ tm_ty_fv t2 ++ tm_ty_fv t3
  end.

Fixpoint context_ty_fv (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => ty_fv T ++ context_ty_fv Gamma'
  end.

Fixpoint list_max (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => Nat.max x (list_max xs')
  end.

Lemma in_list_le_max : forall x xs, In x xs -> x <= list_max xs.
Proof.
  intros x xs. induction xs as [|y xs IH].
  - simpl. intro H. contradiction.
  - simpl. intro H. destruct H as [->|H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall xs : list atom, exists X, ~ In X xs.
Proof.
  intro xs. exists (S (list_max xs)). intro H.
  pose proof (in_list_le_max (S (list_max xs)) xs H).
  lia.
Qed.

Lemma nat_le_neq_lt : forall n m, n <= m -> n <> m -> n < m.
Proof.
  intros n m Hle Hneq. destruct (Nat.eq_dec n m) as [Heq|Hne].
  - contradiction.
  - lia.
Qed.

Lemma lc_ty_at_weaken : forall k T, lc_ty_at k T -> lc_ty_at (S k) T.
Proof.
  intros k T H. induction H; eauto using lc_ty_at; lia.
Qed.

Lemma lc_ty_subst : forall k X U T,
    lc_ty_at k T -> lc_ty_at k U -> lc_ty_at k (ty_subst X U T).
Proof.
  intros k X U T H. induction H; simpl; intro HU.
  - constructor. lia.
  - destruct (Nat.eqb X X0) eqn:E.
    + exact HU.
    + constructor.
  - constructor; [apply IHlc_ty_at1|apply IHlc_ty_at2]; assumption.
  - constructor. apply IHlc_ty_at. apply lc_ty_at_weaken. assumption.
  - constructor.
Qed.

Lemma lc_tm_ty_subst : forall K k X U t,
    lc_tm_at K k t -> lc_ty_at K U ->
    lc_tm_at K k (tm_ty_subst X U t).
Proof.
  intros K k X U t H. induction H; simpl; intro HU.
  - constructor. lia.
  - constructor.
  - constructor; [apply lc_ty_subst; assumption|apply IHlc_tm_at; exact HU].
  - constructor; [apply IHlc_tm_at1|apply IHlc_tm_at2]; assumption.
  - constructor. apply IHlc_tm_at. apply lc_ty_at_weaken. exact HU.
  - constructor; [apply IHlc_tm_at|apply lc_ty_subst]; assumption.
  - constructor.
  - constructor.
  - constructor; [apply IHlc_tm_at1|apply IHlc_tm_at2|apply IHlc_tm_at3]; assumption.
Qed.

Lemma lc_tm_at_weaken_k : forall K k t, lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H. induction H; eauto using lc_tm_at; lia.
Qed.

Lemma lc_tm_at_weaken_K : forall K k t, lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H. induction H; eauto using lc_tm_at, lc_ty_at_weaken.
Qed.

Lemma lc_ty_open_rec : forall k T U,
    lc_ty_at (S k) T -> lc_ty_at k U ->
    lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k T U HT. revert k U HT. induction T as [n|a|T1 IH1 T2 IH2|T1 IH1|]; intros k U HT HU; simpl.
  - inversion HT; subst. destruct (Nat.eqb k n) eqn:E.
    + simpl. exact HU.
    + simpl. constructor. apply Nat.eqb_neq in E.
      assert (n <= k) as Hik by lia.
      apply nat_le_neq_lt; [exact Hik|].
      intro Heq. apply E. symmetry. exact Heq.
  - inversion HT; constructor.
  - inversion HT; subst. constructor.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - inversion HT; subst. constructor. apply IH1; [assumption|apply lc_ty_at_weaken; exact HU].
  - inversion HT; constructor.
Qed.

Lemma lc_open_tm_rec : forall K k t u,
    lc_tm_at K (S k) t -> lc_tm_at K k u ->
    lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t u H. revert K k u H. induction t as
    [n|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T| | |t1 IH1 t2 IH2 t3 IH3];
    intros K k u H Hu; simpl.
  - inversion H; subst. destruct (Nat.eqb k n) eqn:E.
    + exact Hu.
    + constructor. apply Nat.eqb_neq in E. apply nat_le_neq_lt; [lia|].
      intro Heq. apply E. symmetry. exact Heq.
  - constructor.
  - inversion H; subst. constructor; [assumption|].
    apply IH with (K:=K) (k:=S k) (u:=u); [assumption|apply lc_tm_at_weaken_k; exact Hu].
  - inversion H; subst. constructor; [apply IH1 with (K:=K) (k:=k) (u:=u)|apply IH2 with (K:=K) (k:=k) (u:=u)]; assumption.
  - inversion H; subst. constructor.
    apply IH with (K:=S K) (k:=k) (u:=u); [assumption|apply lc_tm_at_weaken_K; exact Hu].
  - inversion H; subst. constructor.
    + apply IH with (K:=K) (k:=k) (u:=u); [assumption|exact Hu].
    + assumption.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; [apply IH1 with (K:=K) (k:=k) (u:=u)|apply IH2 with (K:=K) (k:=k) (u:=u)|apply IH3 with (K:=K) (k:=k) (u:=u)]; assumption.
Qed.

Lemma lc_tm_ty_open : forall K k t U,
    lc_tm_at (S K) k t -> lc_ty_at K U ->
    lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t U H. revert K k U H. induction t as
    [n|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T| | |t1 IH1 t2 IH2 t3 IH3];
    intros K k U H HU; simpl.
  - inversion H; constructor; lia.
  - constructor.
  - inversion H; subst. constructor.
    + apply lc_ty_open_rec; assumption.
    + apply IH with (K:=K) (k:=S k) (U:=U); assumption.
  - inversion H; subst. constructor.
    + apply IH1 with (K:=K) (k:=k) (U:=U); assumption.
    + apply IH2 with (K:=K) (k:=k) (U:=U); assumption.
  - inversion H; subst. constructor.
    apply IH with (K:=S K) (k:=k) (U:=U); [assumption|apply lc_ty_at_weaken; exact HU].
  - inversion H; subst. constructor.
    + apply IH with (K:=K) (k:=k) (U:=U); assumption.
    + apply lc_ty_open_rec; assumption.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; [apply IH1 with (K:=K) (k:=k) (U:=U)|apply IH2 with (K:=K) (k:=k) (U:=U)|apply IH3 with (K:=K) (k:=k) (U:=U)]; assumption.
Qed.

Lemma lc_step : forall t u, locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hs. unfold locally_closed_tm in *.
  induction Hs.
  - apply lc_open_tm_rec with (K:=0) (k:=0); [|].
    + inversion H; assumption.
    + inversion H0; eauto.
  - inversion Hlc; subst. constructor.
    + eapply IHHs; eauto.
    + assumption.
  - inversion Hlc; subst. constructor.
    + assumption.
    + eapply IHHs; eauto.
  - inversion Hlc; subst. apply lc_tm_ty_open with (K:=0) (k:=0); [inversion H; assumption|assumption].
  - inversion Hlc; subst. constructor.
    + apply IHHs. assumption.
    + assumption.
  - inversion Hlc; subst. assumption.
  - inversion Hlc; subst. assumption.
  - inversion Hlc; subst. constructor.
    + apply IHHs. assumption.
    + assumption.
    + assumption.
Qed.

Lemma ty_subst_open_ty_rec : forall k X U T,
    ~ In X (ty_fv T) ->
    ty_subst X U (open_ty_rec k (Ty_FVar X) T) =
    open_ty_rec k U T.
Proof.
  intros k X U T. revert k X U. induction T as [n|a|T1 IH1 T2 IH2|T IH|];
    simpl; intros k X U H.
  - destruct (Nat.eqb k n) eqn:E.
    + simpl. rewrite Nat.eqb_refl. reflexivity.
    + simpl. reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply H. simpl. auto.
    + reflexivity.
  - unfold open_tm_ty. f_equal.
    + apply IH1. intro Hin. apply H. apply in_or_app. left. exact Hin.
    + apply IH2. intro Hin. apply H. apply in_or_app. right. exact Hin.
  - f_equal. apply IH. exact H.
  - reflexivity.
Qed.

Lemma tm_ty_subst_open_tm_ty_rec : forall k X U t,
    ~ In X (tm_ty_fv t) ->
    tm_ty_subst X U (open_tm_ty_rec k (Ty_FVar X) t) = open_tm_ty_rec k U t.
Proof.
  intros k X U t. revert k X U. induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T| | |t1 IH1 t2 IH2 t3 IH3];
    cbn [tm_ty_subst open_tm_ty_rec open_ty open_ty_rec]; intros k X U H; try reflexivity.
  - unfold open_tm_ty. f_equal.
    + apply ty_subst_open_ty_rec. intro Hin. apply H. apply in_or_app. left. exact Hin.
    + apply IH. intro Hin. apply H. apply in_or_app. right. exact Hin.
  - unfold open_tm_ty. f_equal.
    + apply IH1. intro Hin. apply H. apply in_or_app. left. exact Hin.
    + apply IH2. intro Hin. apply H. apply in_or_app. right. exact Hin.
  - unfold open_tm_ty. f_equal. apply IH. exact H.
  - unfold open_tm_ty. f_equal.
    + apply IH. intro Hin. apply H. apply in_or_app. left. exact Hin.
    + apply ty_subst_open_ty_rec. intro Hin. apply H. apply in_or_app. right. exact Hin.
  - unfold open_tm_ty. f_equal.
    + apply IH1. intro Hin. apply H. apply in_or_app. left. exact Hin.
    + apply IH2. intro Hin. apply H. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply IH3. intro Hin. apply H. apply in_or_app. right. apply in_or_app. right. exact Hin.
Qed.

Lemma tm_ty_subst_open_tm_ty : forall X U t,
    ~ In X (tm_ty_fv t) ->
    tm_ty_subst X U (open_tm_ty t (Ty_FVar X)) = open_tm_ty t U.
Proof.
  intros X U t H. unfold open_tm_ty.
  apply tm_ty_subst_open_tm_ty_rec. exact H.
Qed.

Fixpoint shape (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs _ t1 => tm_abs Ty_Bool (shape t1)
  | tm_app t1 t2 => tm_app (shape t1) (shape t2)
  | tm_tabs t1 => tm_tabs (shape t1)
  | tm_tapp t1 _ => tm_tapp (shape t1) Ty_Bool
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (shape t1) (shape t2) (shape t3)
  end.

Lemma shape_ty_subst : forall X U t, shape (tm_ty_subst X U t) = shape t.
Proof. induction t; simpl; try congruence; f_equal; intuition. Qed.

Lemma shape_open_tm_ty_rec : forall k t t' U U',
    shape t = shape t' ->
    shape (open_tm_ty_rec k U t) = shape (open_tm_ty_rec k U' t').
Proof.
  intros k t t' U U'. revert k t' U U'.
  induction t as [n|a|T t IH|t1 IH1 t2 IH2|t IH|t IH T| | |t1 IH1 t2 IH2 t3 IH3].
  - intros k t' U U' H. destruct t'; simpl in H |- *; try discriminate; exact H.
  - intros k t' U U' H. destruct t'; simpl in H |- *; try discriminate; exact H.
  - intros k t' U U' H. destruct t'; simpl in H |- *; try discriminate.
    injection H as H. f_equal. apply IH. exact H.
  - intros k t' U U' H. destruct t'; simpl in H |- *; try discriminate.
    injection H as H1 H2. f_equal; [apply IH1|apply IH2]; assumption.
  - intros k t' U U' H. destruct t'; simpl in H |- *; try discriminate.
    injection H as H. f_equal. apply IH. exact H.
  - intros k t' U U' H. destruct t'; simpl in H |- *; try discriminate.
    injection H as H. f_equal. apply IH. exact H.
  - intros k t' U U' H. destruct t'; simpl in H |- *; try discriminate; reflexivity.
  - intros k t' U U' H. destruct t'; simpl in H |- *; try discriminate; reflexivity.
  - intros k t' U U' H. destruct t'; simpl in H |- *; try discriminate.
    injection H as H1 H2 H3. f_equal; [apply IH1|apply IH2|apply IH3]; assumption.
Qed.

Lemma shape_open_tm_ty : forall t t' U U',
    shape t = shape t' ->
    shape (open_tm_ty t U) = shape (open_tm_ty t' U').
Proof.
  intros. unfold open_tm_ty. apply shape_open_tm_ty_rec; assumption.
Qed.

Lemma shape_open_tm_rec : forall k t t' u u',
    shape t = shape t' -> shape u = shape u' ->
    shape (open_tm_rec k u t) = shape (open_tm_rec k u' t').
Proof.
  intros k t t' u u'. revert k t' u u'.
  induction t as [n|a|T t IH|t1 IH1 t2 IH2|t IH|t IH T| | |t1 IH1 t2 IH2 t3 IH3].
  - intros k t' u u' H H'. destruct t'; simpl in H |- *; try discriminate.
    injection H as Hn. subst n0. destruct (Nat.eqb k n); simpl; [exact H'|reflexivity].
  - intros k t' u u' H H'. destruct t'; simpl in H |- *; try discriminate; exact H.
  - intros k t' u u' H H'. destruct t'; simpl in H |- *; try discriminate.
    injection H as H. f_equal. apply IH; assumption.
  - intros k t' u u' H H'. destruct t'; simpl in H |- *; try discriminate.
    injection H as H1 H2. f_equal; [apply IH1|apply IH2]; assumption.
  - intros k t' u u' H H'. destruct t'; simpl in H |- *; try discriminate.
    injection H as H. f_equal. apply IH; assumption.
  - intros k t' u u' H H'. destruct t'; simpl in H |- *; try discriminate.
    injection H as H. f_equal. apply IH; assumption.
  - intros k t' u u' H H'. destruct t'; simpl in H |- *; try discriminate; reflexivity.
  - intros k t' u u' H H'. destruct t'; simpl in H |- *; try discriminate; reflexivity.
  - intros k t' u u' H H'. destruct t'; simpl in H |- *; try discriminate.
    injection H as H1 H2 H3. f_equal; [apply IH1|apply IH2|apply IH3]; assumption.
Qed.

Lemma shape_open_tm : forall t t' u u',
    shape t = shape t' -> shape u = shape u' ->
    shape (open_tm t u) = shape (open_tm t' u').
Proof.
  intros. unfold open_tm. apply shape_open_tm_rec; assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H. inversion H; eauto using lc_tm_at; constructor.
Qed.

Lemma value_shape : forall v w, value v -> locally_closed_tm w ->
    shape v = shape w -> value w.
Proof.
  intros v w Hv Hw E. inversion Hv; subst; destruct w; simpl in E; try discriminate.
  - constructor. assumption.
  - constructor. assumption.
  - constructor.
  - constructor.
Qed.

Lemma step_shape_back : forall s t,
    locally_closed_tm s -> locally_closed_tm t -> shape s = shape t ->
    forall t', t --> t' ->
    exists s', s --> s' /\ locally_closed_tm s' /\ shape s' = shape t'.
Proof.
  intros s t Hs Ht E t' Hstep. revert s Hs E.
  induction Hstep;
    intros s Hs E;
    destruct s as [| |sT sb|s1 s2|st|st sTy| | |si sthen selse];
    simpl in E; try discriminate.
  - injection E as E1 E2. destruct s1 as [| |sT0 sb0| | | | | |]; simpl in E1; try discriminate.
    injection E1 as Esb. inversion Hs; subst.
    assert (value s2) as Hv2.
    { eapply value_shape; eauto using value_lc. }
    exists (open_tm sb0 s2). split; [constructor; assumption|]. split.
    + apply lc_step with (t:=tm_app (tm_abs sT0 sb0) s2).
      * constructor; assumption.
      * constructor; assumption.
    + apply shape_open_tm; assumption.
  - injection E as E1 E2. inversion Hs; subst.
    assert (locally_closed_tm t1) as Ht1 by (inversion Ht; assumption).
    destruct (IHHstep Ht1 _ H4 E1) as [s' [Hs' [Hlc' He']]].
    exists (tm_app s' s2). split; [apply ST_App1; assumption|]. split; [constructor; assumption|].
    simpl. f_equal; assumption.
  - injection E as E1 E2. inversion Hs; subst.
    assert (locally_closed_tm t2) as Ht2 by (inversion Ht; assumption).
    destruct (IHHstep Ht2 _ H5 E2) as [s' [Hs' [Hlc' He']]].
    assert (value s1) as Hv1' by (eapply value_shape; eauto using value_lc).
    exists (tm_app s1 s'). split; [apply ST_App2; assumption|]. split; [constructor; assumption|].
    simpl. f_equal; assumption.
  - injection E as E1. inversion Hs; subst.
    destruct st as [| | | |sb0| | | |]; simpl in E1; try discriminate.
    injection E1 as Esb. subst.
    exists (open_tm_ty sb0 sTy). split; [apply ST_TAppTabs; eauto|]. split.
    + apply lc_step with (t:=tm_tapp (tm_tabs sb0) sTy).
      * constructor; eauto.
      * apply ST_TAppTabs; eauto.
    + apply shape_open_tm_ty; assumption.
  - injection E as E1. inversion Hs; subst.
    destruct (IHHstep ltac:(inversion Ht; assumption) _ H4 E1) as [s' [Hs' [Hlc' He']]].
    exists (tm_tapp s' sTy). split; [apply ST_TApp; assumption|]. split; [constructor; assumption|].
    simpl. f_equal; assumption.
  - injection E as E1 E2. inversion Hs; subst.
    destruct si; simpl in E1; try discriminate.
    exists sthen. split; [apply ST_IfTrue; assumption|]. split; [assumption|]. simpl; assumption.
  - injection E as E1 E2. inversion Hs; subst.
    destruct si; simpl in E1; try discriminate.
    exists selse. split; [apply ST_IfFalse; assumption|]. split; [assumption|]. simpl; assumption.
  - injection E as E1 E2. inversion Hs; subst.
    destruct (IHHstep ltac:(inversion Ht; assumption) si H7 E1)
      as [s' [Hs' [Hlc' He']]].
    exists (tm_if s' sthen selse). split; [apply ST_If; assumption|]. split; [constructor; assumption|].
    simpl. f_equal; assumption.
Qed.

Lemma multi_shape_back : forall s t,
    locally_closed_tm s -> locally_closed_tm t -> shape s = shape t ->
    forall t', t -->* t' ->
    exists s', s -->* s' /\ locally_closed_tm s' /\ shape s' = shape t'.
Proof.
  intros s t Hs Ht E t' Hm. revert s Hs Ht E.
  induction Hm as [x|x y z Hxy Hyz IH]; intros s Hs Ht E.
  - exists s. split; [constructor|]. split; [exact Hs|exact E].
  - destruct (step_shape_back s x Hs Ht E y Hxy)
      as [s' [Hss' [Hlc' E']]].
    destruct (IH s' Hlc' (lc_step _ _ Ht Hxy) E')
      as [u [Hmulti [Hlu Eu]]].
    exists u. split; [econstructor; eauto|]. split; assumption.
Qed.

Lemma sn_shape : forall s, strongly_normalizing s ->
    locally_closed_tm s -> forall t, locally_closed_tm t ->
    shape s = shape t -> strongly_normalizing t.
Proof.
  intros s Hsn. induction Hsn as [s Hnext IH].
  intros Hs t Ht E. constructor. intros u Htu.
  destruct (step_shape_back s t Hs Ht E u Htu)
    as [s' [Hss' [Hlc' E']]].
  assert (locally_closed_tm u) as Hlu by (apply lc_step with (t:=t); assumption).
  eapply IH; eauto.
Qed.

Definition type_substitution := atom -> ty.

Definition term_substitution := atom -> tm.

Fixpoint instantiate_ty (theta : type_substitution) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (instantiate_ty theta T1) (instantiate_ty theta T2)
  | Ty_All T1 => Ty_All (instantiate_ty theta T1)
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (instantiate theta gamma t1) (instantiate theta gamma t2) (instantiate theta gamma t3)
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
  | Ty_Bool => value v /\ (v = tm_true \/ v = tm_false)
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationIfMediumTask.
