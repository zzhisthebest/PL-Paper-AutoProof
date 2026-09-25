(** System F parametricity benchmark, Hard variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNondeterminismRecursionHardTask.

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


Hint Constructors lc_ty_at lc_tm_at value : core.

Definition may_related (R : tm -> tm -> Prop) (t1 t2 : tm) : Prop :=
  exists v1 v2,
    t1 -->* v1 /\ t2 -->* v2 /\ value v1 /\ value v2 /\ R v1 v2.

Definition relation := tm -> tm -> Prop.

Definition closed_term (t : tm) : Prop :=
  (forall x s, tm_subst x s t = t) /\
  (forall X U, tm_ty_subst X U t = t).

Fixpoint related_value (T : ty) (bound : list relation)
    (free : atom -> relation) : relation := fun v1 v2 =>
  value v1 /\ value v2 /\ closed_term v1 /\ closed_term v2 /\
  match T with
  | Ty_BVar i => nth i bound (fun _ _ => False) v1 v2
  | Ty_FVar X => free X v1 v2
  | Ty_Arrow A B =>
      forall a1 a2, related_value A bound free a1 a2 ->
        may_related (related_value B bound free)
          (tm_app v1 a1) (tm_app v2 a2)
  | Ty_All A =>
      forall U1 U2 (R : relation),
        wf_ty [] U1 -> wf_ty [] U2 ->
        may_related (related_value A (R :: bound) free)
          (tm_tapp v1 U1) (tm_tapp v2 U2)
  | Ty_Nat =>
      exists n, v1 = numeral n /\ v2 = numeral n
  end.

Lemma related_value_is_value : forall T bound free v1 v2,
  related_value T bound free v1 v2 -> value v1 /\ value v2.
Proof.
  destruct T; simpl; intuition.
Qed.

Lemma numeral_closed : forall index, closed_term (numeral index).
Proof.
  induction index; simpl; split; intros; simpl; auto.
  - rewrite (proj1 IHindex); reflexivity.
  - rewrite (proj2 IHindex); reflexivity.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; intros Huv.
  - exact Huv.
  - eapply multi_step; eauto.
Qed.

Lemma multi_once : forall t u, t --> u -> t -->* u.
Proof.
  intros t u H; eapply multi_step; eauto using multi_refl.
Qed.

Lemma may_related_left : forall R t t' u,
  t -->* t' -> may_related R t' u -> may_related R t u.
Proof.
  intros R t t' u H [v1 [v2 [H1 [H2 [HV1 [HV2 HR]]]]]].
  exists v1, v2; repeat split; eauto using multi_trans.
Qed.

Lemma may_related_right : forall R t u u',
  u -->* u' -> may_related R t u' -> may_related R t u.
Proof.
  intros R t u u' H [v1 [v2 [H1 [H2 [HV1 [HV2 HR]]]]]].
  exists v1, v2; repeat split; eauto using multi_trans.
Qed.

Lemma may_related_values : forall R v1 v2,
  value v1 -> value v2 -> R v1 v2 -> may_related R v1 v2.
Proof.
  intros R v1 v2 HV1 HV2 HR.
  exists v1, v2; repeat split; auto using multi_refl.
Qed.

Lemma multi_app_left : forall t t' u,
  t -->* t' -> locally_closed_tm u ->
  tm_app t u -->* tm_app t' u.
Proof.
  intros t t' u H; induction H; intros Hlc.
  - constructor.
  - eapply multi_step; eauto using ST_App1.
Qed.

Lemma multi_app_right : forall v u u',
  value v -> u -->* u' -> tm_app v u -->* tm_app v u'.
Proof.
  intros v u u' Hv H; induction H.
  - constructor.
  - eapply multi_step; eauto using ST_App2.
Qed.

Lemma multi_tapp : forall t t' U,
  t -->* t' -> locally_closed_ty U ->
  tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H; induction H; intros Hlc.
  - constructor.
  - eapply multi_step; eauto using ST_TApp.
Qed.

Lemma multi_succ : forall t t',
  t -->* t' -> tm_succ t -->* tm_succ t'.
Proof.
  intros t t' H; induction H.
  - constructor.
  - eapply multi_step; eauto using ST_Succ.
Qed.

Lemma numeric_numeral : forall n, numeric_value (numeral n).
Proof.
  induction n; simpl; auto using numeric_value.
Qed.

Lemma value_numeral : forall n, value (numeral n).
Proof.
  intro n; auto using numeric_numeral, value.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; constructor; auto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv; inversion Hv; subst; auto using numeric_lc.
Qed.

Lemma list_max_bound : forall (L : list nat) x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [| head tail IH]; simpl; intros x Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin]; subst.
    + apply Nat.le_max_l.
    + etransitivity; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall L : list atom,
  ~ In (S (fold_right Nat.max 0 L)) L.
Proof.
  intros L Hin; pose proof (list_max_bound L _ Hin); lia.
Qed.

Lemma open_ty_lc_inverse : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; simpl; intros k X Hlc.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; constructor; lia.
    + inversion Hlc; subst; constructor; lia.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - constructor.
Qed.

Lemma wf_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf; induction Hwf.
  - constructor.
  - constructor; assumption.
  - constructor.
    specialize (H0 (S (fold_right Nat.max 0 L)) (fresh_atom L)).
    apply (open_ty_lc_inverse T 0 (S (fold_right Nat.max 0 L)) H0).
  - constructor.
Qed.

Lemma may_related_app : forall A B bound free f1 f2 a1 a2,
  may_related (related_value (Ty_Arrow A B) bound free) f1 f2 ->
  may_related (related_value A bound free) a1 a2 ->
  locally_closed_tm a1 -> locally_closed_tm a2 ->
  may_related (related_value B bound free)
    (tm_app f1 a1) (tm_app f2 a2).
Proof.
  intros A B bound free f1 f2 a1 a2
    [g1 [g2 [Hf1 [Hf2 [_ [_ [Hg1 [Hg2 Hfun]]]]]]]]
    [v1 [v2 [Ha1 [Ha2 [Hv1 [Hv2 HR]]]]] ] Hlc1 Hlc2.
  eapply may_related_left.
  { eapply multi_trans; [eapply multi_app_left; eauto|].
    apply multi_app_right; eauto. }
  eapply may_related_right.
  { eapply multi_trans; [eapply multi_app_left; eauto|].
    apply multi_app_right; eauto. }
  apply Hfun; assumption.
Qed.

Lemma may_related_choice_left : forall R t1 t2 u1 u2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  locally_closed_tm u1 -> locally_closed_tm u2 ->
  may_related R t1 u1 ->
  may_related R (tm_choice t1 t2) (tm_choice u1 u2).
Proof.
  intros R t1 t2 u1 u2 Ht1 Ht2 Hu1 Hu2 H.
  eapply may_related_left; [apply multi_once; eauto using ST_ChoiceLeft|].
  eapply may_related_right; [apply multi_once; eauto using ST_ChoiceLeft|].
  exact H.
Qed.

Lemma may_related_tapp : forall A bound free f1 f2 U1 U2 R,
  may_related (related_value (Ty_All A) bound free) f1 f2 ->
  wf_ty [] U1 -> wf_ty [] U2 ->
  may_related (related_value A (R :: bound) free)
    (tm_tapp f1 U1) (tm_tapp f2 U2).
Proof.
  intros A bound free f1 f2 U1 U2 R
    [g1 [g2 [Hf1 [Hf2 [_ [_ Hfun]]]]]] Hwf1 Hwf2.
  eapply may_related_left.
  { eapply multi_tapp; eauto using wf_lc. }
  eapply may_related_right.
  { eapply multi_tapp; eauto using wf_lc. }
  destruct Hfun as [_ [_ [_ [_ Hfun]]]].
  eauto.
Qed.

Lemma numeric_no_step : forall n u,
  numeric_value n -> ~ (n --> u).
Proof.
  intros n u Hnum; revert u.
  induction Hnum; intros u Hstep; inversion Hstep; subst.
  eapply IHHnum; eassumption.
Qed.

Lemma value_no_step : forall v u, value v -> ~ (v --> u).
Proof.
  intros v u Hval Hstep; destruct Hval as [T t Hlc | t Hlc | n Hnum].
  - inversion Hstep.
  - inversion Hstep.
  - eapply numeric_no_step; eauto.
Qed.

Lemma multi_from_value : forall v u,
  value v -> v -->* u -> v = u.
Proof.
  intros v u Hval Hmulti; inversion Hmulti; subst; auto.
  exfalso; eapply value_no_step; eauto.
Qed.

Lemma identity_from_relation : forall t U v,
  wf_ty [] U -> value v -> closed_term v ->
  may_related
    (related_value (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))
      [] (fun _ _ _ => False)) t t ->
  tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t U v Hwf Hval Hclosed Ht.
  destruct Hclosed as [Hterm Htype].
  set (R := (fun a b : tm => a = v /\ b = v) : relation).
  pose proof (may_related_tapp _ [] (fun _ _ _ => False)
    t t U U R Ht Hwf Hwf) as Htapp.
  assert (HR : related_value (Ty_BVar 0) [R]
    (fun _ _ _ => False) v v).
  { simpl; repeat split; auto. }
  pose proof (may_related_app (Ty_BVar 0) (Ty_BVar 0)
    [R] (fun _ _ _ => False) (tm_tapp t U) (tm_tapp t U)
    v v Htapp (may_related_values _ _ _ Hval Hval HR)
    (value_lc _ Hval) (value_lc _ Hval)) as Happ.
  destruct Happ as [result1 [result2 [Hresult1
    [_ [_ [_ Hrel]]]]]].
  simpl in Hrel.
  destruct Hrel as [_ [_ [_ [_ [Heq _]]]]].
  subst result1; exact Hresult1.
Qed.

Lemma open_tm_lc_inverse : forall t k K x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; simpl; intros k K x Hlc.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; constructor; lia.
    + inversion Hlc; subst; constructor; lia.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
Qed.

Lemma open_tm_ty_lc_inverse : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; simpl; intros K k X Hlc.
  - inversion Hlc; subst; constructor; lia.
  - constructor.
  - inversion Hlc; subst; constructor; eauto using open_ty_lc_inverse.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto using open_ty_lc_inverse.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
Qed.

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Htyping; induction Htyping.
  - constructor.
  - apply lc_tm_abs; [eapply wf_lc; exact H|].
    eapply open_tm_lc_inverse with
      (x := S (fold_right Nat.max 0 L)).
    apply H1; apply fresh_atom.
  - constructor; assumption.
  - apply lc_tm_tabs.
    eapply open_tm_ty_lc_inverse with
      (X := S (fold_right Nat.max 0 L)).
    apply H0; apply fresh_atom.
  - apply lc_tm_tapp; [assumption|eapply wf_lc; eassumption].
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma multi_rec_arg : forall n n' b s,
  n -->* n' -> locally_closed_tm b -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof.
  intros n n' b s H; induction H; intros Hlc_b Hlc_s.
  - constructor.
  - eapply multi_step; eauto using ST_RecArg.
Qed.

Lemma multi_rec_base : forall n b b' s,
  numeric_value n -> b -->* b' -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros n b b' s Hnum H; induction H; intros Hlc_s.
  - constructor.
  - eapply multi_step; eauto using ST_RecBase.
Qed.

Lemma multi_rec_step : forall n b s s',
  numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros n b s s' Hnum Hvalue H; induction H.
  - constructor.
  - eapply multi_step; eauto using ST_RecStep.
Qed.

Lemma may_related_rec : forall T bound free n1 n2 b1 b2 s1 s2,
  may_related (related_value Ty_Nat bound free) n1 n2 ->
  may_related (related_value T bound free) b1 b2 ->
  may_related
    (related_value (Ty_Arrow Ty_Nat (Ty_Arrow T T)) bound free) s1 s2 ->
  locally_closed_tm b1 -> locally_closed_tm b2 ->
  locally_closed_tm s1 -> locally_closed_tm s2 ->
  may_related (related_value T bound free)
    (tm_natrec n1 b1 s1) (tm_natrec n2 b2 s2).
Proof.
  intros T bound free n1 n2 b1 b2 s1 s2
    [nv1 [nv2 [Hn1 [Hn2 [_ [_ Hn]]]]]]
    [bv1 [bv2 [Hb1 [Hb2 [Hbv1 [Hbv2 Hb]]]]]]
    [sv1 [sv2 [Hs1 [Hs2 [Hsv1 [Hsv2 Hs]]]]]]
    Hlc_b1 Hlc_b2 Hlc_s1 Hlc_s2.
  destruct Hn as [_ [_ [_ [_ [index [Hnv1 Hnv2]]]]]].
  subst nv1 nv2.
  eapply may_related_left.
  { eapply multi_trans; [eapply multi_rec_arg; eauto|].
    eapply multi_trans; [eapply multi_rec_base; eauto using numeric_numeral|].
    eapply multi_rec_step; eauto using numeric_numeral. }
  eapply may_related_right.
  { eapply multi_trans; [eapply multi_rec_arg; eauto|].
    eapply multi_trans; [eapply multi_rec_base; eauto using numeric_numeral|].
    eapply multi_rec_step; eauto using numeric_numeral. }
  clear Hn1 Hn2 Hb1 Hb2 Hs1 Hs2 Hlc_b1 Hlc_b2 Hlc_s1 Hlc_s2.
  induction index as [| smaller IH].
  - eapply may_related_left; [apply multi_once; eauto using ST_RecZero|].
    eapply may_related_right; [apply multi_once; eauto using ST_RecZero|].
    eapply may_related_values; eauto.
  - eapply may_related_left; [apply multi_once; eauto using ST_RecSucc, numeric_numeral|].
    eapply may_related_right; [apply multi_once; eauto using ST_RecSucc, numeric_numeral|].
    eapply may_related_app.
    + destruct Hs as [_ [_ [_ [_ Hs]]]].
      apply Hs.
      destruct (numeral_closed smaller) as [Hterm Htype].
      simpl; repeat split; eauto using value_numeral.
    + exact IH.
    + apply lc_tm_rec.
      * apply numeric_lc; apply numeric_numeral.
      * apply value_lc; exact Hbv1.
      * apply value_lc; exact Hsv1.
    + apply lc_tm_rec.
      * apply numeric_lc; apply numeric_numeral.
      * apply value_lc; exact Hbv2.
      * apply value_lc; exact Hsv2.
Qed.

Lemma may_related_abs : forall A B bound free T1 T2 body1 body2,
  value (tm_abs T1 body1) -> value (tm_abs T2 body2) ->
  closed_term (tm_abs T1 body1) -> closed_term (tm_abs T2 body2) ->
  (forall a1 a2,
    related_value A bound free a1 a2 ->
    may_related (related_value B bound free)
      (open_tm body1 a1) (open_tm body2 a2)) ->
  may_related (related_value (Ty_Arrow A B) bound free)
    (tm_abs T1 body1) (tm_abs T2 body2).
Proof.
  intros A B bound free T1 T2 body1 body2 Hv1 Hv2 Hclosed1 Hclosed2 Hbody.
  destruct Hclosed1 as [Hterm1 Htype1].
  destruct Hclosed2 as [Hterm2 Htype2].
  apply may_related_values; auto.
  repeat split; auto.
  intros a1 a2 Ha.
  eapply may_related_left.
  { apply multi_once; apply ST_AppAbs; eauto using value_lc.
    exact (proj1 (related_value_is_value _ _ _ _ _ Ha)). }
  eapply may_related_right.
  { apply multi_once; apply ST_AppAbs; eauto using value_lc.
    exact (proj2 (related_value_is_value _ _ _ _ _ Ha)). }
  apply Hbody; exact Ha.
Qed.

Lemma may_related_tabs : forall A bound free body1 body2,
  value (tm_tabs body1) -> value (tm_tabs body2) ->
  closed_term (tm_tabs body1) -> closed_term (tm_tabs body2) ->
  (forall U1 U2 R, wf_ty [] U1 -> wf_ty [] U2 ->
    may_related (related_value A (R :: bound) free)
      (open_tm_ty body1 U1) (open_tm_ty body2 U2)) ->
  may_related (related_value (Ty_All A) bound free)
    (tm_tabs body1) (tm_tabs body2).
Proof.
  intros A bound free body1 body2 Hv1 Hv2 Hclosed1 Hclosed2 Hbody.
  destruct Hclosed1 as [Hterm1 Htype1].
  destruct Hclosed2 as [Hterm2 Htype2].
  apply may_related_values; auto.
  repeat split; auto.
  intros U1 U2 R Hwf1 Hwf2.
  eapply may_related_left.
  { apply multi_once; apply ST_TAppTabs; eauto using wf_lc, value_lc. }
  eapply may_related_right.
  { apply multi_once; apply ST_TAppTabs; eauto using wf_lc, value_lc. }
  apply Hbody; assumption.
Qed.

Lemma open_tm_rec_lc : forall t K depth,
  lc_tm_at K depth t -> forall k u, depth <= k ->
    open_tm_rec k u t = t.
Proof.
  intros t K depth Hlc; induction Hlc; intros j u Hj; simpl;
    try rewrite ?IHHlc, ?IHHlc1, ?IHHlc2, ?IHHlc3;
    try reflexivity; try lia.
  - destruct (Nat.eqb j i) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|reflexivity].
Qed.

Lemma tm_subst_open_rec : forall t k x s u,
  locally_closed_tm s ->
  tm_subst x s (open_tm_rec k u t) =
  open_tm_rec k (tm_subst x s u) (tm_subst x s t).
Proof.
  induction t; simpl; intros k x s u Hlc; try rewrite ?IHt, ?IHt1,
    ?IHt2, ?IHt3 by exact Hlc; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Nat.eqb x a); simpl; try reflexivity.
    symmetry; apply open_tm_rec_lc with (K := 0) (depth := 0);
      auto; lia.
Qed.

Lemma tm_subst_open_fvar : forall t x s,
  locally_closed_tm s ->
  tm_subst x s (open_tm t (tm_fvar x)) =
  open_tm (tm_subst x s t) s.
Proof.
  intros t x s Hlc; unfold open_tm; rewrite tm_subst_open_rec by assumption.
  simpl; now rewrite Nat.eqb_refl.
Qed.

Lemma open_ty_rec_lc : forall T depth,
  lc_ty_at depth T -> forall k V, depth <= k ->
    open_ty_rec k V T = T.
Proof.
  intros T depth Hlc; induction Hlc; intros j V Hj; simpl;
    try rewrite ?IHHlc, ?IHHlc1, ?IHHlc2;
    try reflexivity; try lia.
  destruct (Nat.eqb j i) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|reflexivity].
Qed.

Lemma ty_subst_open_rec : forall T k X U V,
  locally_closed_ty U ->
  ty_subst X U (open_ty_rec k V T) =
  open_ty_rec k (ty_subst X U V) (ty_subst X U T).
Proof.
  induction T; simpl; intros k X U V Hlc; try rewrite ?IHT,
    ?IHT1, ?IHT2 by exact Hlc; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Nat.eqb X a); simpl; try reflexivity.
    symmetry; apply open_ty_rec_lc with (depth := 0); auto; lia.
Qed.

Lemma tm_ty_subst_open_tm_rec : forall t k X U u,
  tm_ty_subst X U (open_tm_rec k u t) =
  open_tm_rec k (tm_ty_subst X U u) (tm_ty_subst X U t).
Proof.
  induction t; simpl; intros k X U u; try rewrite ?IHt, ?IHt1,
    ?IHt2, ?IHt3; try reflexivity.
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma tm_ty_subst_open_type_rec : forall t k X U V,
  locally_closed_ty U ->
  tm_ty_subst X U (open_tm_ty_rec k V t) =
  open_tm_ty_rec k (ty_subst X U V) (tm_ty_subst X U t).
Proof.
  induction t; simpl; intros k X U V Hlc;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3 by exact Hlc;
    try reflexivity.
  - rewrite ty_subst_open_rec by exact Hlc; reflexivity.
  - rewrite ty_subst_open_rec by exact Hlc; reflexivity.
Qed.

Lemma tm_subst_ty_subst_commute : forall t x s X U,
  tm_ty_subst X U s = s ->
  tm_subst x s (tm_ty_subst X U t) =
  tm_ty_subst X U (tm_subst x s t).
Proof.
  induction t; simpl; intros x s X U Hclosed;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3 by exact Hclosed;
    try reflexivity.
  destruct (Nat.eqb x a); simpl; auto.
Qed.

Definition interpreted_type_context
    (Delta : ty_context) (left right : atom -> ty)
    (free : atom -> relation) : Prop :=
  forall X, In X Delta ->
    wf_ty [] (left X) /\ wf_ty [] (right X) /\
    (forall v1 v2, free X v1 v2 -> value v1 /\ value v2).

Definition interpreted_term_context
    (Gamma : context) (free : atom -> relation)
    (left right : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    related_value T [] free (left x) (right x).

Lemma interpreted_variable : forall Gamma free left right x T,
  interpreted_term_context Gamma free left right ->
  lookup_context x Gamma = Some T ->
  may_related (related_value T [] free) (left x) (right x).
Proof.
  intros Gamma free left right x T Henv Hlookup.
  pose proof (Henv x T Hlookup) as Hrel.
  destruct (related_value_is_value _ _ _ _ _ Hrel) as [Hv1 Hv2].
  apply may_related_values; assumption.
Qed.

Fixpoint free_term_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ body | tm_tabs body | tm_succ body => free_term_vars body
  | tm_app first second | tm_choice first second =>
      free_term_vars first ++ free_term_vars second
  | tm_tapp body _ => free_term_vars body
  | tm_zero => []
  | tm_natrec count base successor =>
      free_term_vars count ++ free_term_vars base ++ free_term_vars successor
  end.

Fixpoint free_type_vars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ | Ty_Nat => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => free_type_vars A ++ free_type_vars B
  | Ty_All A => free_type_vars A
  end.

Fixpoint free_type_vars_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_zero => []
  | tm_abs A body => free_type_vars A ++ free_type_vars_tm body
  | tm_app first second | tm_choice first second =>
      free_type_vars_tm first ++ free_type_vars_tm second
  | tm_tabs body | tm_succ body => free_type_vars_tm body
  | tm_tapp body A => free_type_vars_tm body ++ free_type_vars A
  | tm_natrec count base successor =>
      free_type_vars_tm count ++ free_type_vars_tm base ++
        free_type_vars_tm successor
  end.

Lemma free_term_open : forall t k u x,
  In x (free_term_vars t) ->
  In x (free_term_vars (open_tm_rec k u t)).
Proof.
  induction t; simpl; intros k u x Hin;
    try rewrite !in_app_iff in *; try tauto; try contradiction.
  all: firstorder eauto.
Qed.

Lemma free_term_open_type : forall t k U,
  free_term_vars (open_tm_ty_rec k U t) = free_term_vars t.
Proof.
  induction t; simpl; intros k U;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity.
Qed.

Lemma free_type_open : forall T k U X,
  In X (free_type_vars T) ->
  In X (free_type_vars (open_ty_rec k U T)).
Proof.
  induction T; simpl; intros k U X Hin;
    try rewrite !in_app_iff in *; try tauto; try contradiction.
  all: firstorder eauto.
Qed.

Lemma free_type_open_term : forall t k U X,
  In X (free_type_vars_tm t) ->
  In X (free_type_vars_tm (open_tm_ty_rec k U t)).
Proof.
  induction t; simpl; intros k U X Hin;
    try rewrite !in_app_iff in *; try tauto; try contradiction.
  all: firstorder eauto using free_type_open.
Qed.

Lemma free_type_open_tm : forall t k u X,
  In X (free_type_vars_tm t) ->
  In X (free_type_vars_tm (open_tm_rec k u t)).
Proof.
  induction t; simpl; intros k u X Hin;
    try rewrite !in_app_iff in *; try contradiction;
    firstorder eauto.
Qed.

Lemma typing_free_term_vars : forall Delta Gamma t T x,
  has_type Delta Gamma t T ->
  In x (free_term_vars t) ->
  exists A, lookup_context x Gamma = Some A.
Proof.
  intros Delta Gamma t T x Htyping; induction Htyping;
    simpl; intros Hin; try rewrite !in_app_iff in *;
    try contradiction.
  - destruct Hin as [Heq | []]; subst; eauto.
  - set (fresh := S (fold_right Nat.max 0 (x :: L))).
    assert (Hfresh : ~ In fresh L).
    { intro Hcontra; apply (fresh_atom (x :: L)); right; exact Hcontra. }
    assert (Hneq : x <> fresh).
    { intro Heq; apply (fresh_atom (x :: L)); left; exact Heq. }
    pose proof (H1 fresh Hfresh
      (free_term_open _ 0 (tm_fvar fresh) _ Hin)) as [A Hlookup].
    simpl in Hlookup.
    destruct (Nat.eqb x fresh) eqn:Heq.
    + apply Nat.eqb_eq in Heq; contradiction.
    + eauto.
  - destruct Hin; eauto.
  - set (fresh := S (fold_right Nat.max 0 L)).
    rewrite <- (free_term_open_type t 0 (Ty_FVar fresh)) in Hin.
    eauto using H0, fresh_atom.
  - eauto.
  - eauto.
  - destruct Hin as [Hn | [Hb | Hs]]; eauto.
  - destruct Hin; eauto.
Qed.

Lemma wf_free_type_vars : forall Delta T X,
  wf_ty Delta T -> In X (free_type_vars T) -> In X Delta.
Proof.
  intros Delta T X Hwf; induction Hwf; simpl; intros Hin;
    try rewrite !in_app_iff in *; try contradiction.
  - destruct Hin as [Heq | []]; subst; assumption.
  - destruct Hin; eauto.
  - set (fresh := S (fold_right Nat.max 0 (X :: L))).
    assert (Hfresh : ~ In fresh L).
    { intro Hcontra; apply (fresh_atom (X :: L)); right; exact Hcontra. }
    assert (Hneq : fresh <> X).
    { intro Heq; apply (fresh_atom (X :: L)); left; symmetry; exact Heq. }
    pose proof (H0 fresh Hfresh
      (free_type_open T 0 (Ty_FVar fresh) X Hin)) as Hmember.
    destruct Hmember as [Heq | Hmember]; [contradiction|assumption].
Qed.

Lemma typing_free_type_vars : forall Delta Gamma t T X,
  has_type Delta Gamma t T ->
  In X (free_type_vars_tm t) -> In X Delta.
Proof.
  intros Delta Gamma t T X Htyping; induction Htyping;
    simpl; intros Hin; try rewrite !in_app_iff in *;
    try contradiction.
  - destruct Hin as [Hin | Hin].
    + eapply wf_free_type_vars; eauto.
    + set (fresh := S (fold_right Nat.max 0 L)).
      pose proof (H1 fresh (fresh_atom L)
        (free_type_open_tm t2 0 (tm_fvar fresh) X Hin)) as Hmember.
      exact Hmember.
  - destruct Hin; eauto.
  - set (fresh := S (fold_right Nat.max 0 (X :: L))).
    assert (Hfresh : ~ In fresh L).
    { intro Hcontra; apply (fresh_atom (X :: L)); right; exact Hcontra. }
    assert (Hneq : fresh <> X).
    { intro Heq; apply (fresh_atom (X :: L)); left; symmetry; exact Heq. }
    pose proof (H0 fresh Hfresh
      (free_type_open_term t 0 (Ty_FVar fresh) X Hin)) as Hmember.
    destruct Hmember as [Heq | Hmember]; [contradiction|assumption].
  - destruct Hin as [Hin | Hin]; eauto using wf_free_type_vars.
  - eauto.
  - firstorder eauto.
  - destruct Hin; eauto.
Qed.

Lemma tm_subst_not_free : forall t x s,
  ~ In x (free_term_vars t) -> tm_subst x s t = t.
Proof.
  induction t; simpl; intros x s Hnot;
    try rewrite !in_app_iff in Hnot;
    try solve [reflexivity | f_equal; firstorder].
  destruct (Nat.eqb x a) eqn:Heq; auto.
  apply Nat.eqb_eq in Heq; subst; exfalso; apply Hnot; simpl; auto.
Qed.

Lemma ty_subst_not_free : forall T X U,
  ~ In X (free_type_vars T) -> ty_subst X U T = T.
Proof.
  induction T; simpl; intros X U Hnot;
    try rewrite !in_app_iff in Hnot;
    try solve [reflexivity | f_equal; firstorder].
  destruct (Nat.eqb X a) eqn:Heq; auto.
  apply Nat.eqb_eq in Heq; subst; exfalso; apply Hnot; simpl; auto.
Qed.

Lemma tm_ty_subst_not_free : forall t X U,
  ~ In X (free_type_vars_tm t) -> tm_ty_subst X U t = t.
Proof.
  induction t; simpl; intros X U Hnot;
    try rewrite !in_app_iff in Hnot;
    try solve [reflexivity | f_equal; firstorder eauto using ty_subst_not_free].
Qed.

Lemma typed_closed_term : forall t T,
  has_type [] empty t T -> closed_term t.
Proof.
  intros t T Htyping; split; intros variable replacement.
  - apply tm_subst_not_free; intro Hin.
    destruct (typing_free_term_vars _ _ _ _ _ Htyping Hin) as [A Hlookup].
    discriminate Hlookup.
  - apply tm_ty_subst_not_free; intro Hin.
    pose proof (typing_free_type_vars _ _ _ _ _ Htyping Hin) as Hmember.
    contradiction.
Qed.

Lemma step_lc_backwards : forall t u,
  t --> u -> locally_closed_tm u -> locally_closed_tm t.
Proof.
  intros t u Hstep; induction Hstep; intro Hlc;
    try solve [constructor; eauto using value_lc, numeric_lc].
  - apply lc_tm_app; [assumption|apply value_lc; assumption].
  - inversion Hlc; subst; apply lc_tm_app;
      [apply IHHstep; assumption|assumption].
  - apply lc_tm_app; [apply value_lc; assumption|].
    apply IHHstep; now inversion Hlc.
  - apply lc_tm_tapp; [apply IHHstep; now inversion Hlc|assumption].
  - apply lc_tm_succ; apply IHHstep; now inversion Hlc.
  - apply lc_tm_rec; [apply IHHstep; now inversion Hlc|assumption|assumption].
  - apply lc_tm_rec.
    + apply numeric_lc; assumption.
    + apply IHHstep; now inversion Hlc.
    + assumption.
  - apply lc_tm_rec.
    + apply numeric_lc; assumption.
    + apply value_lc; assumption.
    + apply IHHstep; now inversion Hlc.
  - apply lc_tm_rec; [constructor|apply value_lc; assumption|apply value_lc; assumption].
  - apply lc_tm_rec.
    + apply lc_tm_succ; apply numeric_lc; assumption.
    + apply value_lc; assumption.
    + apply value_lc; assumption.
Qed.

Lemma multi_lc_backwards : forall t u,
  t -->* u -> locally_closed_tm u -> locally_closed_tm t.
Proof.
  intros t u Hmulti; induction Hmulti; eauto using step_lc_backwards.
Qed.

Lemma may_related_lc : forall R t u,
  may_related R t u -> locally_closed_tm t /\ locally_closed_tm u.
Proof.
  intros R t u [v1 [v2 [H1 [H2 [Hv1 [Hv2 _]]]]]].
  split; eauto using multi_lc_backwards, value_lc.
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
  intros t Htyping U v Hwf Hvalue Hvtyping.
  eapply identity_from_relation; eauto using typed_closed_term.
Qed.

End SystemFParametricityNondeterminismRecursionHardTask.
