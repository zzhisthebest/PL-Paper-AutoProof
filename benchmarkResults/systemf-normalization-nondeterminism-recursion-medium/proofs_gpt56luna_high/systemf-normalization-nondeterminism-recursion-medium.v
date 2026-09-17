(** System F CBV strong-normalization benchmark, Medium variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNondeterminismRecursionMediumTask.

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
  | tm_natrec : tm -> tm -> tm -> tm
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

Notation "'Nat'" := Ty_Nat (in custom systemf_ty at level 0) : systemf_scope.
Notation "'zero'" := tm_zero (in custom systemf_tm at level 0) : systemf_scope.
Notation "'succ' t" := (tm_succ t) (in custom systemf_tm at level 9, t custom systemf_tm at level 0) : systemf_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom systemf_tm at level 9, n custom systemf_tm at level 0, b custom systemf_tm at level 0, s custom systemf_tm at level 0) : systemf_scope.
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_ty_rec k U t1)
  | tm_natrec n b f => tm_natrec (open_tm_ty_rec k U n) (open_tm_ty_rec k U b) (open_tm_ty_rec k U f)
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst x s t1)
  | tm_natrec n b f => tm_natrec (tm_subst x s n) (tm_subst x s b) (tm_subst x s f)
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
      lc_ty_at k (Ty_All T)
  | lc_ty_nat : forall k, lc_ty_at k Ty_Nat.

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
  | lc_tm_zero : forall K k, lc_tm_at K k tm_zero
  | lc_tm_succ : forall K k t, lc_tm_at K k t -> lc_tm_at K k (tm_succ t)
  | lc_tm_rec : forall K k n b s,
      lc_tm_at K k n -> lc_tm_at K k b -> lc_tm_at K k s -> lc_tm_at K k (tm_natrec n b s)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

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
      has_type Delta Gamma (tm_natrec n b s) T
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

(* Some elementary facts about opening.  The reverse-opening lemmas are
   useful here because the typing rules use the usual fresh-variable
   presentations of binders. *)

Lemma lc_ty_weaken : forall k j T,
  k <= j -> lc_ty_at k T -> lc_ty_at j T.
Proof.
  intros k j T hkj h; revert j hkj; induction h; intros j hkj.
  - constructor; lia.
  - constructor; assumption.
  - apply lc_ty_arrow; [apply IHh1 | apply IHh2]; assumption.
  - apply lc_ty_all. apply IHh. lia.
  - constructor.
Qed.

Lemma lc_ty_open_rec : forall k j U T,
  lc_ty_at k T -> lc_ty_at j U -> j <= k ->
  lc_ty_at k (open_ty_rec j U T).
Proof.
  intros k j U T h; revert j U.
  induction h; intros j U hU hj; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E; subst; apply lc_ty_weaken with (k:=i); assumption.
    + apply lc_ty_bvar; apply Nat.eqb_neq in E; lia.
  - constructor.
  - constructor; [apply IHh1 with (j:=j) | apply IHh2 with (j:=j)]; assumption.
  - constructor. apply IHh with (j:=S j).
    + apply lc_ty_weaken with (k:=j); [lia | assumption].
    + lia.
  - constructor.
Qed.

Lemma lc_tm_weaken : forall K k j t,
  k <= j -> lc_tm_at K k t -> lc_tm_at K j t.
Proof.
  intros K k j t hkj h; revert j hkj; induction h; intros j hkj.
  - constructor; lia.
  - constructor.
  - apply lc_tm_abs; [assumption | apply IHh; lia].
  - apply lc_tm_app; [apply IHh1 | apply IHh2]; assumption.
  - apply lc_tm_tabs. apply IHh. assumption.
  - apply lc_tm_tapp; [apply IHh | assumption]; assumption.
  - constructor.
  - apply lc_tm_succ. apply IHh. assumption.
  - apply lc_tm_rec; [apply IHh1 | apply IHh2 | apply IHh3]; assumption.
  - apply lc_tm_choice; [apply IHh1 | apply IHh2]; assumption.
Qed.

Lemma lc_tm_ty_weaken : forall K K' k t,
  K <= K' -> lc_tm_at K k t -> lc_tm_at K' k t.
Proof.
  intros K K' k t hKK' h; revert K' hKK'; induction h; intros K' hKK'.
  - constructor; assumption.
  - constructor.
  - apply lc_tm_abs; [apply lc_ty_weaken with (k:=K); assumption | apply IHh; assumption].
  - apply lc_tm_app; [apply IHh1 | apply IHh2]; assumption.
  - apply lc_tm_tabs. apply IHh. lia.
  - apply lc_tm_tapp; [apply IHh | apply lc_ty_weaken with (k:=K)]; assumption.
  - constructor.
  - apply lc_tm_succ. apply IHh. assumption.
  - apply lc_tm_rec; [apply IHh1 | apply IHh2 | apply IHh3]; assumption.
  - apply lc_tm_choice; [apply IHh1 | apply IHh2]; assumption.
Qed.

Lemma lc_tm_open_rec : forall K k u t,
  lc_tm_at K (S k) t -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k u t; revert K k u.
  induction t; intros K k u hT hu; simpl in hT.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; cbn [open_tm_rec].
      destruct (Nat.eqb n n) eqn:E0.
      * exact hu.
      * apply Nat.eqb_neq in E0; contradiction.
    + cbn [open_tm_rec]. rewrite E. inversion hT. apply lc_tm_bvar.
      apply Nat.eqb_neq in E.
      assert (n <> k) as Hne.
      { intro Hnk; apply E; symmetry; exact Hnk. }
      assert (n <= k) as Hnk.
      { apply (proj1 (Nat.lt_succ_r n k)); assumption. }
      destruct (proj1 (Nat.lt_eq_cases n k) Hnk) as [Hlt|Heq].
      * exact Hlt.
      * exfalso; apply Hne; exact Heq.
  - constructor.
  - inversion hT. apply lc_tm_abs; [assumption|].
    apply IHt with (K:=K) (k:=S k) (u:=u); [assumption |].
    apply lc_tm_weaken with (k:=k) (j:=S k); [lia | assumption].
  - inversion hT. apply lc_tm_app.
    + apply IHt1 with (K:=K) (k:=k) (u:=u); assumption.
    + apply IHt2 with (K:=K) (k:=k) (u:=u); assumption.
  - inversion hT. apply lc_tm_tabs.
    apply IHt with (K:=S K) (k:=k) (u:=u); [assumption |].
    apply lc_tm_ty_weaken with (K:=K); [lia | assumption].
  - inversion hT. apply lc_tm_tapp.
    + apply IHt with (K:=K) (k:=k) (u:=u); assumption.
    + assumption.
  - constructor.
  - inversion hT. apply lc_tm_succ. apply IHt with (K:=K) (k:=k) (u:=u); assumption.
  - inversion hT. apply lc_tm_rec.
    + apply IHt1 with (K:=K) (k:=k) (u:=u); assumption.
    + apply IHt2 with (K:=K) (k:=k) (u:=u); assumption.
    + apply IHt3 with (K:=K) (k:=k) (u:=u); assumption.
  - inversion hT. apply lc_tm_choice.
    + apply IHt1 with (K:=K) (k:=k) (u:=u); assumption.
    + apply IHt2 with (K:=K) (k:=k) (u:=u); assumption.
Qed.

Lemma lc_ty_open_reverse : forall k j U T,
  j <= k -> lc_ty_at k (open_ty_rec j U T) -> lc_ty_at (S k) T.
Proof.
  intros k j U T; revert k j U.
  induction T; intros k j U hj h; simpl in h.
  - destruct (Nat.eqb j n) eqn:E.
    + constructor; apply Nat.eqb_eq in E; lia.
    + inversion h; constructor; apply Nat.eqb_neq in E; lia.
  - inversion h; constructor.
  - inversion h. apply lc_ty_arrow.
    + apply IHT1 with (k:=k) (j:=j) (U:=U); assumption.
    + apply IHT2 with (k:=k) (j:=j) (U:=U); assumption.
  - inversion h; constructor. apply IHT with (k:=S k) (j:=S j) (U:=U); try lia; assumption.
  - constructor.
Qed.

Lemma lc_tm_open_reverse : forall K k u t,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k u t; revert K k u.
  induction t; intros K k u h; simpl in h.
  - destruct (Nat.eqb k n) eqn:E.
    + constructor; apply Nat.eqb_eq in E; lia.
    + inversion h; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion h.
    constructor; [assumption | apply IHt with (K:=K) (k:=S k) (u:=u); assumption].
  - inversion h.
    constructor; [apply IHt1 with (K:=K) (k:=k) (u:=u); assumption |
                   apply IHt2 with (K:=K) (k:=k) (u:=u); assumption].
  - inversion h.
    constructor. apply IHt with (K:=S K) (k:=k) (u:=u); assumption.
  - inversion h.
    constructor; [apply IHt with (K:=K) (k:=k) (u:=u); assumption | assumption].
  - constructor.
  - inversion h.
    constructor. apply IHt with (K:=K) (k:=k) (u:=u); assumption.
  - inversion h.
    constructor; [apply IHt1 with (K:=K) (k:=k) (u:=u); assumption |
                   apply IHt2 with (K:=K) (k:=k) (u:=u); assumption |
                   apply IHt3 with (K:=K) (k:=k) (u:=u); assumption].
  - inversion h.
    constructor; [apply IHt1 with (K:=K) (k:=k) (u:=u); assumption |
                   apply IHt2 with (K:=K) (k:=k) (u:=u); assumption].
Qed.

Lemma lc_tm_ty_open_reverse : forall K k j U t,
  j <= K ->
  locally_closed_ty U ->
  lc_tm_at K k (open_tm_ty_rec j U t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k j U t hj hU; revert K k j U hj hU.
  induction t; intros K k j U hj hU h; simpl in h.
  - inversion h; constructor; assumption.
  - constructor.
  - inversion h.
    constructor.
    all: eauto using lc_ty_open_reverse.
  - inversion h.
    constructor; eauto.
  - inversion h.
    constructor. apply IHt with (K:=S K) (k:=k) (j:=S j) (U:=U).
    + lia.
    + assumption.
    + assumption.
  - inversion h.
    constructor; eauto using lc_ty_open_reverse.
  - constructor.
  - inversion h.
    constructor; eauto.
  - inversion h.
    constructor; eauto.
  - inversion h.
    constructor; eauto.
Qed.

Fixpoint atom_list_max (L : list atom) : nat :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (atom_list_max L')
  end.

Lemma in_atom_list_le_max : forall x L,
  In x L -> x <= atom_list_max L.
Proof.
  intros x L H; induction L as [|a L IH].
  - inversion H.
  - simpl in H. destruct H as [->|H].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (atom_list_max L); [apply IH; assumption | apply Nat.le_max_r].
Qed.

Lemma exists_not_in_atoms : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L; exists (S (atom_list_max L)); intro H.
  pose proof (in_atom_list_le_max _ _ H); lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  fix IH 3.
  intros Delta T H.
  destruct H as [Delta0 X HX | Delta0 T1 T2 H1 H2 | L0 Delta0 T0 H0 | Delta0].
  - constructor.
  - apply lc_ty_arrow; [apply (IH Delta0 T1 H1) | apply (IH Delta0 T2 H2)].
  - apply lc_ty_all.
    destruct (exists_not_in_atoms L0) as [X HX].
    apply lc_ty_open_reverse with (j:=0) (U:=Ty_FVar X).
    + lia.
    + apply (IH (X :: Delta0) (open_ty T0 (Ty_FVar X)) (H0 X HX)).
  - constructor.
Qed.

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  fix IH 5.
  intros Delta Gamma t T H.
  destruct H as
    [ Delta0 Gamma0 x0 T0 Hlookup Hwf
    | L0 Delta0 Gamma0 T10 t20 T20 Hwf Hbody
    | Delta0 Gamma0 t10 t20 T10 T20 H1 H2
    | L0 Delta0 Gamma0 t0 T0 Hbody
    | Delta0 Gamma0 t0 T0 U0 H1 H2
    | Delta0 Gamma0
    | Delta0 Gamma0 n0 Hn
    | Delta0 Gamma0 n0 b0 s0 T0 Hn Hb Hs
    | Delta0 Gamma0 t10 t20 T0 H1 H2 ].
  - constructor.
  - apply lc_tm_abs; [eapply wf_ty_lc; eassumption|].
    destruct (exists_not_in_atoms L0) as [x1 Hx1].
    apply lc_tm_open_reverse with (k:=0) (u:=tm_fvar x1).
    apply (IH Delta0 (update Gamma0 x1 T10)
              (open_tm t20 (tm_fvar x1)) T20 (Hbody x1 Hx1)).
  - apply lc_tm_app; [apply (IH Delta0 Gamma0 t10 (Ty_Arrow T10 T20) H1) |
                       apply (IH Delta0 Gamma0 t20 T10 H2)].
  - apply lc_tm_tabs.
    destruct (exists_not_in_atoms L0) as [X1 HX1].
    apply lc_tm_ty_open_reverse with (K:=0) (k:=0) (j:=0) (U:=Ty_FVar X1).
    + lia.
    + constructor.
    + apply (IH (X1 :: Delta0) Gamma0
              (open_tm_ty t0 (Ty_FVar X1))
              (open_ty T0 (Ty_FVar X1)) (Hbody X1 HX1)).
  - apply lc_tm_tapp; [apply (IH Delta0 Gamma0 t0 (Ty_All T0) H1) | eapply wf_ty_lc; eassumption].
  - constructor.
  - apply lc_tm_succ. apply (IH Delta0 Gamma0 n0 Ty_Nat Hn).
  - apply lc_tm_rec; [apply (IH Delta0 Gamma0 n0 Ty_Nat Hn) |
                      apply (IH Delta0 Gamma0 b0 T0 Hb) |
                      apply (IH Delta0 Gamma0 s0 (Ty_Arrow Ty_Nat (Ty_Arrow T0 T0)) Hs)].
  - apply lc_tm_choice; [apply (IH Delta0 Gamma0 t10 T0 H1) |
                         apply (IH Delta0 Gamma0 t20 T0 H2)].
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
  | Ty_Nat => Ty_Nat
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
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (instantiate theta gamma t)
  | tm_natrec n b s => tm_natrec (instantiate theta gamma n) (instantiate theta gamma b) (instantiate theta gamma s)
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
  | Ty_Nat => value v /\ numeric_value v
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; destruct H; try assumption.
  induction H; constructor; assumption.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; constructor; assumption.
Qed.

Lemma value_no_step : forall v, value v -> forall u, ~ (v --> u).
Proof.
  assert (Hnum : forall n, numeric_value n -> forall u, ~ (n --> u)).
  { intros n Hn; induction Hn as [|n Hn IH]; intros u Hs.
    - inversion Hs.
    - inversion Hs. apply IH with (u:=t'); exact H0.
  }
  intros v Hv u Hs; destruct Hv as [T t Hlc | t Hlc | n Hn].
  - inversion Hs.
  - inversion Hs.
  - eapply Hnum; eassumption.
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv; constructor; intros u Hu.
  exfalso; exact (value_no_step v Hv u Hu).
Qed.

Lemma lc_tm_ty_open_rec : forall K k j U t,
  lc_tm_at K k t -> lc_ty_at j U -> j <= K ->
  lc_tm_at K k (open_tm_ty_rec j U t).
Proof.
  intros K k j U t h; revert j U.
  induction h; intros j U hU hj; simpl.
  - constructor; assumption.
  - constructor.
  - apply lc_tm_abs.
    + apply lc_ty_open_rec with (j:=j); assumption.
    + apply IHh with (j:=j); assumption.
  - apply lc_tm_app; [apply IHh1 with (j:=j) | apply IHh2 with (j:=j)]; assumption.
  - apply lc_tm_tabs. apply IHh with (j:=S j).
    + apply lc_ty_weaken with (k:=j); [lia | assumption].
    + lia.
  - apply lc_tm_tapp.
    + apply IHh with (j:=j); assumption.
    + apply lc_ty_open_rec with (j:=j); assumption.
  - constructor.
  - apply lc_tm_succ. apply IHh with (j:=j); assumption.
  - apply lc_tm_rec; [apply IHh1 with (j:=j) | apply IHh2 with (j:=j) | apply IHh3 with (j:=j)]; assumption.
  - apply lc_tm_choice; [apply IHh1 with (j:=j) | apply IHh2 with (j:=j)]; assumption.
Qed.

Lemma lc_ty_open_down : forall K U T,
  lc_ty_at (S K) T -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K U T; revert K U.
  induction T; intros K U hU h; simpl in h.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst; cbn [open_ty_rec].
      destruct (Nat.eqb n n) eqn:E0.
      * exact h.
      * apply Nat.eqb_neq in E0; contradiction.
    + cbn [open_ty_rec]. rewrite E. inversion hU; apply lc_ty_bvar. apply Nat.eqb_neq in E.
      assert (n <= K) as Hnk.
      { apply (proj1 (Nat.lt_succ_r n K)); assumption. }
      destruct (proj1 (Nat.lt_eq_cases n K) Hnk) as [Hlt|Heq].
      * exact Hlt.
      * exfalso; apply E; symmetry; exact Heq.
  - constructor.
  - inversion hU; cbn [open_ty_rec]; apply lc_ty_arrow.
    + apply IHT1 with (K:=K) (U:=U); assumption.
    + apply IHT2 with (K:=K) (U:=U); assumption.
  - inversion hU; cbn [open_ty_rec]; apply lc_ty_all. apply IHT with (K:=S K) (U:=U).
    + assumption.
    + apply lc_ty_weaken with (k:=K) (j:=S K); [lia | exact h].
  - constructor.
Qed.

Lemma lc_tm_ty_open_down : forall K k U t,
  lc_ty_at K U -> lc_tm_at (S K) k t ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k U t; revert K k U.
  induction t; intros K k U hU h; simpl in h.
  - inversion h; constructor; assumption.
  - constructor.
  - inversion h; apply lc_tm_abs.
    + apply lc_ty_open_down with (K:=K); assumption.
    + apply IHt with (K:=K) (k:=S k) (U:=U); assumption.
  - inversion h; apply lc_tm_app.
    + apply IHt1 with (K:=K) (k:=k) (U:=U); assumption.
    + apply IHt2 with (K:=K) (k:=k) (U:=U); assumption.
  - inversion h; apply lc_tm_tabs.
    apply IHt with (K:=S K) (k:=k) (U:=U).
    + apply lc_ty_weaken with (k:=K); [lia | assumption].
    + assumption.
  - inversion h; apply lc_tm_tapp.
    + apply IHt with (K:=K) (k:=k) (U:=U); assumption.
    + apply lc_ty_open_down with (K:=K); assumption.
  - constructor.
  - inversion h; apply lc_tm_succ. apply IHt with (K:=K) (k:=k) (U:=U); assumption.
  - inversion h; apply lc_tm_rec.
    + apply IHt1 with (K:=K) (k:=k) (U:=U); assumption.
    + apply IHt2 with (K:=K) (k:=k) (U:=U); assumption.
    + apply IHt3 with (K:=K) (k:=k) (U:=U); assumption.
  - inversion h; apply lc_tm_choice.
    + apply IHt1 with (K:=K) (k:=k) (U:=U); assumption.
    + apply IHt2 with (K:=K) (k:=k) (U:=U); assumption.
Qed.

Lemma step_lc : forall t u, locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hs; induction Hs.
  - apply lc_tm_open_rec with (K:=0) (k:=0) (u:=v).
    + inversion H; assumption.
    + apply value_lc; assumption.
  - inversion Hlc. apply lc_tm_app; [apply IHHs; assumption | assumption].
  - inversion Hlc. apply lc_tm_app; [assumption | apply IHHs; assumption].
  - inversion H. apply lc_tm_ty_open_down with (K:=0) (k:=0) (U:=T); [exact H0 | assumption].
  - inversion Hlc. apply lc_tm_tapp; [apply IHHs; assumption | assumption].
  - inversion Hlc. apply lc_tm_succ. apply IHHs; assumption.
  - inversion Hlc. apply lc_tm_rec; [apply IHHs; assumption | assumption | assumption].
  - inversion Hlc. apply lc_tm_rec; [assumption | apply IHHs; assumption | assumption].
  - inversion Hlc. apply lc_tm_rec; [assumption | assumption | apply IHHs; assumption].
  - apply value_lc; assumption.
  - apply lc_tm_app.
    + apply lc_tm_app.
      * exact (value_lc s H1).
      * exact (numeric_lc n H).
    + apply lc_tm_rec.
      * exact (numeric_lc n H).
      * exact (value_lc b H0).
      * exact (value_lc s H1).
  - inversion Hlc; assumption.
  - inversion Hlc; assumption.
Qed.

Lemma expression_step : forall eta rho T t u,
  expression_relation eta rho T t -> t --> u ->
  expression_relation eta rho T u.
Proof.
  intros eta rho T t u E Hstep.
  unfold expression_relation in E.
  unfold expression_lifting in E.
  unfold expression_relation.
  unfold expression_lifting.
  destruct E as [Hlc [Hsn Hend]].
  split.
  - apply step_lc with (t:=t); assumption.
  - split.
    + inversion Hsn; subst; apply H; exact Hstep.
    + intros v Hmulti Hv.
      apply Hend with (v:=v).
      * eapply multi_step; [exact Hstep | exact Hmulti].
      * assumption.
Qed.

Lemma expression_intro : forall eta rho T t,
  locally_closed_tm t ->
  (forall u, t --> u -> expression_relation eta rho T u) ->
  (value t -> value_relation eta rho T t) ->
  expression_relation eta rho T t.
Proof.
  intros eta rho T t Hlc Hsteps Hval.
  split; [exact Hlc|]. split.
  - constructor. intros u Hu. exact (proj1 (proj2 (Hsteps u Hu))).
  - intros v Hmulti Hv. inversion Hmulti as [|x y z Hxy Hyz].
    + inversion Hmulti; subst; apply Hval; assumption.
    + subst z. apply (proj2 (proj2 (Hsteps y Hxy))) with (v:=v).
      * exact Hyz.
      * exact Hv.
Qed.

Lemma vr_value : forall eta rho T v, value_relation eta rho T v -> value v.
Proof.
  intros eta rho T; induction T; simpl; intros v H.
  - destruct (nth_error eta n) as [a|] eqn:E; [apply a.(candidate_values); assumption | contradiction].
  - destruct (rho a) as [c|] eqn:E; [apply c.(candidate_values); assumption | contradiction].
  - destruct H as [Hv [U [b [-> H]]]]; exact Hv.
  - destruct H as [Hv [b [-> H]]]; exact Hv.
  - exact (proj1 H).
Qed.

Lemma vr_sn : forall eta rho T v, value_relation eta rho T v -> strongly_normalizing v.
Proof. intros; apply value_sn; eapply vr_value; eassumption. Qed.

Lemma vr_candidate : forall (eta : list value_candidate) (rho : relation_env) (T : ty), value_candidate.
Proof.
  intros; refine {| candidate_relation := value_relation eta rho T |}.
  intros; eapply vr_value; eassumption.
Defined.

Lemma expression_ext : forall R S t,
  (forall v, R v <-> S v) -> expression_lifting R t <-> expression_lifting S t.
Proof.
  intros R S t H; split; intros E.
  - unfold expression_lifting in E; destruct E as [Hlc [Hsn Hend]].
    unfold expression_lifting; split; [exact Hlc|]; split; [exact Hsn|].
    intros v Hm Hv; apply (proj1 (H v)); eauto.
  - unfold expression_lifting in E; destruct E as [Hlc [Hsn Hend]].
    unfold expression_lifting; split; [exact Hlc|]; split; [exact Hsn|].
    intros v Hm Hv; apply (proj2 (H v)); eauto.
Qed.

Lemma value_expression : forall R v, value v -> R v -> expression_lifting R v.
Proof.
  intros R v Hv HR; split; [apply value_lc; assumption|]. split; [apply value_sn; assumption|].
  intros u Hm Hu; inversion Hm as [|x y z Hxy Hyz].
  - subst; exact HR.
  - exfalso. apply (value_no_step v Hv y Hxy).
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationNondeterminismRecursionMediumTask.
