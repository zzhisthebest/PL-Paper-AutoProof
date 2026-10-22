(** STLC CBV strong-normalization benchmark, Hard variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfRecursionHardTask.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

Definition atom := nat.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Nat : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_zero : tm
  | tm_succ : tm -> tm

  | tm_natrec : tm -> tm -> tm -> tm
  | tm_if : tm -> tm -> tm -> tm.

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "<{{ x }}>" := x (x custom stlc_ty).
Notation "x" := x
  (in custom stlc_ty at level 0, x constr at level 0) : stlc_scope.
Notation "'Bool'" := Ty_Bool
  (in custom stlc_ty at level 0) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T)
  (in custom stlc_ty at level 99, right associativity) : stlc_scope.

Notation "$( t )" := t
  (in custom stlc_ty at level 0, t constr) : stlc_scope.
Notation "( T )" := T
  (in custom stlc_ty at level 0, T custom stlc_ty) : stlc_scope.

Notation "<{ e }>" := e
  (e custom stlc_tm at level 200) : stlc_scope.
Notation "$( x )" := x
  (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'bvar' n" := (tm_bvar n)
  (in custom stlc_tm at level 0, n constr at level 0) : stlc_scope.
Notation "'fvar' x" := (tm_fvar x)
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'true'" := tm_true
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "'false'" := tm_false
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "( x )" := x
  (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.
Notation "x y" := (tm_app x y)
  (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "'lambda' ':' T ',' t" := (tm_abs T t)
  (in custom stlc_tm at level 200,
   T custom stlc_ty,
   t custom stlc_tm at level 200,
   left associativity) : stlc_scope.
Notation "'zero'" := tm_zero
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "'succ' t" := (tm_succ t)
  (in custom stlc_tm at level 9, t custom stlc_tm at level 0) : stlc_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom stlc_tm at level 9,
   n custom stlc_tm at level 0, b custom stlc_tm at level 0,
   s custom stlc_tm at level 0) : stlc_scope.
Notation "'Nat'" := Ty_Nat
  (in custom stlc_ty at level 0) : stlc_scope.

Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm, t3 custom stlc_tm at level 200) : stlc_scope.

Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_rec k u t1)
  | tm_natrec n b s =>
      tm_natrec (open_rec k u n) (open_rec k u b) (open_rec k u s)
  | tm_if t1 t2 t3 => tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
  end.

Definition open (t u : tm) : tm := open_rec 0 u t.

Inductive lc_at : nat -> tm -> Prop :=
  | lc_bvar : forall k i,
      i < k ->
      lc_at k (tm_bvar i)
  | lc_fvar : forall k x,
      lc_at k (tm_fvar x)
  | lc_app : forall k t1 t2,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k (tm_app t1 t2)
  | lc_abs : forall k T t1,
      lc_at (S k) t1 ->
      lc_at k (tm_abs T t1)
  | lc_true : forall k,
      lc_at k tm_true
  | lc_false : forall k,
      lc_at k tm_false
  | lc_zero : forall k, lc_at k tm_zero
  | lc_succ : forall k t, lc_at k t -> lc_at k (tm_succ t)
  | lc_rec : forall k n b s,
      lc_at k n -> lc_at k b -> lc_at k s ->
      lc_at k (tm_natrec n b s)
  | lc_if : forall k t1 t2 t3,
      lc_at k t1 -> lc_at k t2 -> lc_at k t3 -> lc_at k (tm_if t1 t2 t3)
  .

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

Hint Constructors lc_at : core.

Lemma lc_at_weaken : forall k t, lc_at k t -> lc_at (S k) t.
Proof. intros k t H; induction H; eauto using lc_at. Qed.

Lemma lc_at_mono : forall k t, lc_at k t -> forall j, k <= j -> lc_at j t.
Proof.
  intros k t H; induction H as
    [k i Hi | k x | k t1 H1 IH1 t2 H2 IH2 | k T t1 H1 IH1
    | k | k | k | k t1 H1 IH1 | k n b s Hn IHn Hb IHb Hs IHs
    | k t1 t2 t3 H1 IH1 H2 IH2 H3 IH3]; intros j Hj.
  - constructor. lia.
  - constructor.
  - constructor; eauto.
  - apply lc_abs. apply IH1. lia.
  - constructor.
  - constructor.
  - constructor.
  - constructor. apply IH1. lia.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Inductive numeric_value : tm -> Prop :=
  | nv_zero : numeric_value tm_zero
  | nv_succ : forall (t : tm), numeric_value t -> numeric_value (tm_succ t).

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false
  | v_nat : forall n, numeric_value n -> value n.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t v,
      locally_closed (tm_abs T t) ->
      value v ->
      tm_app (tm_abs T t) v --> open t v
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      locally_closed t2 ->
      tm_app t1 t2 --> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_app v1 t2 --> tm_app v1 t2'
  | ST_Succ : forall t t',
      t --> t' -> tm_succ t --> tm_succ t'
  | ST_RecArg : forall n n' b s,

      n --> n' -> locally_closed b -> locally_closed s ->
      tm_natrec n b s --> tm_natrec n' b s
  | ST_RecBase : forall n b b' s,

      numeric_value n -> b --> b' -> locally_closed s ->
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
  | ST_IfTrue : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      locally_closed t2 ->
      locally_closed t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Definition context := atom -> option ty.

Definition empty : context := fun _ => None.

Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  fun y => if Nat.eqb x y then Some T else Gamma y.

Notation "x '|->' v ';' m" := (update m x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty,
   right associativity) : stlc_scope.
Notation "x '|->' v" := (update empty x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty) : stlc_scope.
Notation "'empty'" := empty
  (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
  (at level 0,
   Gamma custom stlc_tm at level 200,
   t custom stlc_tm,
   T custom stlc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      <{ Gamma |-- fvar x \in T }>
  | T_Abs : forall (L : list atom) Gamma T1 T2 t1,
      (forall x, ~ In x L ->
        <{ x |-> T1 ; Gamma |-- $(open t1 (tm_fvar x)) \in T2 }>) ->
      <{ Gamma |-- lambda : T1, $(t1) \in T1 -> T2 }>
  | T_App : forall Gamma t1 t2 T1 T2,
      <{ Gamma |-- $(t1) \in T1 -> T2 }> ->
      <{ Gamma |-- $(t2) \in T1 }> ->
      <{ Gamma |-- $(tm_app t1 t2) \in T2 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_Zero : forall Gamma,
      <{ Gamma |-- zero \in Nat }>
  | T_Succ : forall Gamma n,
      <{ Gamma |-- $(n) \in Nat }> ->
      <{ Gamma |-- succ $(n) \in Nat }>
  | T_Rec : forall Gamma n b s T,
      <{ Gamma |-- $(n) \in Nat }> ->
      <{ Gamma |-- $(b) \in T }> ->
      <{ Gamma |-- $(s) \in Nat -> T -> T }> ->
      <{ Gamma |-- rec $(n) $(b) $(s) \in T }>
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- $(t1) \in Bool }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- $(t3) \in T }> ->
      <{ Gamma |-- $(tm_if t1 t2 t3) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.


Inductive strongly_normalizing : tm -> Prop :=

  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(* At base types reducibility is closure plus strong normalization.  At
   arrows, reducible functions preserve reducibility on application. *)
Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool => forall v, multi step t v -> value v -> v = tm_true \/ v = tm_false
  | Ty_Nat => forall v, multi step t v -> value v -> numeric_value v
  | Ty_Arrow A B => forall v, multi step t v -> value v ->
      exists U body, v = tm_abs U body /\
        forall u, reducible A u -> reducible B (tm_app v u)
  end.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. intros T t H; destruct T; simpl in H; tauto. Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. intros T t H; destruct T; simpl in H; tauto. Qed.

Lemma reducible_intro : forall T t,
  locally_closed t -> strongly_normalizing t ->
  (match T with
   | Ty_Bool => forall v, multi step t v -> value v -> v = tm_true \/ v = tm_false
   | Ty_Nat => forall v, multi step t v -> value v -> numeric_value v
   | Ty_Arrow A B => forall v, multi step t v -> value v ->
       exists U body, v = tm_abs U body /\
         forall u, reducible A u -> reducible B (tm_app v u)
   end) -> reducible T t.
Proof.
  intros T t Hlc Hsn Hout; destruct T; simpl in *.
  - split; [exact Hlc|]. split; assumption.
  - split; [exact Hlc|]. split; assumption.
  - split; [exact Hlc|]. split; assumption.
Qed.

Lemma reducible_outcome : forall T t, reducible T t ->
  match T with
   | Ty_Bool => forall v, multi step t v -> value v -> v = tm_true \/ v = tm_false
   | Ty_Nat => forall v, multi step t v -> value v -> numeric_value v
   | Ty_Arrow A B => forall v, multi step t v -> value v ->
       exists U body, v = tm_abs U body /\
         forall u, reducible A u -> reducible B (tm_app v u)
  end.
Proof. intros T t H; destruct T; simpl in H |- *; tauto. Qed.

Lemma sn_step_inv : forall t t', strongly_normalizing t -> t --> t' ->
  strongly_normalizing t'.
Proof. intros t t' Hsn Hs; inversion Hsn; eauto. Qed.

Lemma multi_cons : forall x y z, step x y -> multi step y z -> multi step x z.
Proof. intros; eapply multi_step; eauto. Qed.


Fixpoint subst_env (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst_env sigma t1) (subst_env sigma t2)
  | tm_abs T t1 => tm_abs T (subst_env sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (subst_env sigma t1)
  | tm_natrec n b s => tm_natrec (subst_env sigma n) (subst_env sigma b) (subst_env sigma s)
  | tm_if t1 t2 t3 => tm_if (subst_env sigma t1) (subst_env sigma t2) (subst_env sigma t3)
  end.

Definition env_update (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true | tm_false | tm_zero => []
  | tm_succ t1 => fv t1
  | tm_natrec n b s => fv n ++ fv b ++ fv s
  | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
  end.

Lemma subst_env_update_fresh : forall sigma x u t,
  ~ In x (fv t) ->
  subst_env (env_update sigma x u) t = subst_env sigma t.
Proof.
  intros sigma x u t; induction t; simpl; intros Hfresh.
  - reflexivity.
  - unfold env_update. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + reflexivity.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply IHt3. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply IHt3. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact Hin.
Qed.

Lemma subst_env_lc : forall k t, lc_at k t -> forall sigma,
  (forall x, locally_closed (sigma x)) -> lc_at k (subst_env sigma t).
Proof.
  intros k t Hlc; induction Hlc; intros sigma Hsigma; simpl.
  - constructor. exact H.
  - apply lc_at_mono with (k := 0); [apply Hsigma|lia].
  - constructor; eauto.
  - apply lc_abs. apply IHHlc. exact Hsigma.
  - constructor.
  - constructor.
  - constructor.
  - constructor. eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Definition ctx_interp (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  forall x T, Gamma x = Some T -> reducible T (sigma x).

Lemma ctx_interp_update : forall Gamma sigma x A u,
  ctx_interp Gamma sigma -> reducible A u ->
  ctx_interp (update Gamma x A) (env_update sigma x u).
Proof.
  unfold ctx_interp, update, env_update. intros Gamma sigma x A u [Hclosed Henv] Hu.
  split.
  - intros y. destruct (Nat.eqb x y); [eapply reducible_lc; exact Hu|apply Hclosed].
  - intros y T. destruct (Nat.eqb x y) eqn:E.
    + intros H. inversion H; subst. exact Hu.
    + intros H. eapply Henv. exact H.
Qed.

Lemma open_rec_lc : forall k t, lc_at k t -> forall u, open_rec k u t = t.
Proof.
  intros k t Hlc; induction Hlc; intros u; simpl; try (f_equal; eauto).
  - assert (Nat.eqb k i = false) as E by (apply Nat.eqb_neq; lia).
    rewrite E. reflexivity.
Qed.

Lemma open_rec_closed : forall d t, lc_at d t -> forall q u,
  open_rec (q + d) u t = t.
Proof.
  intros d t Hlc; induction Hlc; intros q u; simpl.
  - assert (Nat.eqb (q + k) i = false) as E by (apply Nat.eqb_neq; lia).
    rewrite E. reflexivity.
  - reflexivity.
  - rewrite (IHHlc1 q u), (IHHlc2 q u). reflexivity.
  - replace (S (q + k)) with (q + S k) by lia.
    rewrite (IHHlc q u). reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHHlc. reflexivity.
  - rewrite (IHHlc1 q u), (IHHlc2 q u), (IHHlc3 q u). reflexivity.
  - rewrite (IHHlc1 q u), (IHHlc2 q u), (IHHlc3 q u). reflexivity.
Qed.

Lemma lc_open_rec_inv : forall k t x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k t; revert k; induction t; intros k x H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - inversion H; constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. apply lc_abs. eapply IHt with (k := S k). exact H2.
  - constructor.
  - constructor.
  - constructor.
  - inversion H; subst. constructor. eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma lc_open : forall k t, lc_at (S k) t -> forall u,
  lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t; revert k. induction t; intros k Hlc u Hu; inversion Hlc; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + apply Nat.eqb_neq in E. constructor. lia.
  - constructor.
  - constructor; eauto.
  - apply lc_abs. eapply IHt; [eassumption|]. eapply lc_at_weaken. exact Hu.
  - constructor.
  - constructor.
  - constructor.
  - constructor. eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed n.
Proof.
  intros n H; induction H.
  - unfold locally_closed. constructor.
  - unfold locally_closed in *. constructor. exact IHnumeric_value.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; inversion H; subst.
  - assumption.
  - unfold locally_closed. constructor.
  - unfold locally_closed. constructor.
  - unfold locally_closed. eapply numeric_value_lc. eassumption.
Qed.

Lemma lc_step : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hs; induction Hs; inversion Hlc; subst; unfold locally_closed in *.
  - inversion H; subst. eapply lc_open; eassumption.
  - apply lc_app; [eapply IHHs; eassumption|assumption].
  - apply lc_app; [assumption|eapply IHHs; eassumption].
  - apply lc_succ. eapply IHHs. assumption.
  - apply lc_rec; [eapply IHHs; eassumption|assumption|assumption].
  - apply lc_rec; [assumption|eapply IHHs; eassumption|assumption].
  - apply lc_rec; [assumption|assumption|eapply IHHs; eassumption].
  - apply value_lc. assumption.
  - apply lc_app; [apply lc_app; [apply value_lc; assumption|apply numeric_value_lc; assumption]
                 |apply lc_rec; [apply numeric_value_lc; assumption|apply value_lc; assumption|apply value_lc; assumption]].
  - assumption.
  - assumption.
  - apply lc_if; [eapply IHHs; eassumption|assumption|assumption].
Qed.

Lemma reducible_step : forall T t t', reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T; intros t t' [Hlc [Hsn Hsem]] Hs; simpl in *.
  - split.
    + eapply lc_step; eassumption.
    + split.
      * eapply sn_step_inv; eassumption.
      * intros v Hmv Hv. apply Hsem with (v := v); [|exact Hv].
        eapply multi_cons; eassumption.
  - split.
    + eapply lc_step; eassumption.
    + split.
      * eapply sn_step_inv; eassumption.
      * intros v Hmv Hv. apply Hsem with (v := v); [|exact Hv].
        eapply multi_cons; eassumption.
  - split.
    + eapply lc_step; eassumption.
    + split.
      * eapply sn_step_inv; eassumption.
      * intros v Hmv Hv. apply Hsem with (v := v); [|exact Hv].
        eapply multi_cons; eassumption.
Qed.

Lemma app_step_cases : forall f a r, tm_app f a --> r ->
  (exists f', f --> f' /\ locally_closed a /\ r = tm_app f' a) \/
  (exists a', value f /\ a --> a' /\ r = tm_app f a') \/
  (exists T body, f = tm_abs T body /\ locally_closed (tm_abs T body) /\
      value a /\ r = open body a).
Proof.
  intros f a r Hs. inversion Hs; subst; eauto 12.
Qed.

Lemma not_value_app : forall f a, ~ value (tm_app f a).
Proof. intros f a H; inversion H; subst; try discriminate; inversion H0. Qed.

Lemma reducible_from_steps : forall T t,
  locally_closed t -> strongly_normalizing t -> ~ value t ->
  (forall t', t --> t' -> reducible T t') -> reducible T t.
Proof.
  intros T t Hlc Hsn Hnv Hred. destruct T as [| |A' B']; simpl.
  - refine (reducible_intro Ty_Bool t Hlc Hsn _).
    intros v Hmv Hv. inversion Hmv; subst.
    + exfalso. apply Hnv. exact Hv.
    + pose proof (Hred y H) as Hr. destruct Hr as [_ [_ Hout]].
      eapply Hout; eassumption.
  - refine (reducible_intro Ty_Nat t Hlc Hsn _).
    intros v Hmv Hv. inversion Hmv; subst.
    + exfalso. apply Hnv. exact Hv.
    + pose proof (Hred y H) as Hr. destruct Hr as [_ [_ Hout]].
      eapply Hout; eassumption.
  - refine (reducible_intro (Ty_Arrow A' B') t Hlc Hsn _).
    intros v Hmv Hv. inversion Hmv; subst.
    + exfalso. apply Hnv. exact Hv.
    + pose proof (Hred y H) as Hr. destruct Hr as [_ [_ Hout]].
      eapply Hout; eassumption.
Qed.

Lemma reducible_app : forall A B f a,
  reducible (Ty_Arrow A B) f -> reducible A a -> reducible B (tm_app f a).
Proof.
  intros A B fbase abase Hfun0 Harg0.
  assert (Happ : forall f, strongly_normalizing f ->
    reducible (Ty_Arrow A B) f -> forall a, reducible A a -> reducible B (tm_app f a)).
  {
    intros f0 Hsf0. induction Hsf0 as [f0 Hnext IH]; intros Hf a Ha.
    destruct Hf as [Hlf [Hsf Hsemf]].
    pose proof (reducible_intro (Ty_Arrow A B) f0 Hlf Hsf Hsemf) as Hf0.
    pose proof (reducible_lc A a Ha) as Hla.
    assert (Hsteps : forall r, tm_app f0 a --> r -> reducible B r).
    { intros r Hr. destruct (app_step_cases f0 a r Hr) as
        [[f' [Hfs [Hla' Er]]] | [[a' [Hval [Has Er]]] |
         [U [body [Ef [Hlc [Hva Er]]]]]]].
      - subst r. assert (Hf' : reducible (Ty_Arrow A B) f')
          by (eapply reducible_step; [exact Hf0|exact Hfs]).
        eapply IH; [exact Hfs|exact Hf'|exact Ha].
      - subst r. destruct (Hsemf f0 (multi_refl step f0) Hval)
          as [U [body [Efun Hfun]]].
        assert (Ha' : reducible A a') by (eapply reducible_step; [exact Ha|exact Has]).
        exact (Hfun a' Ha').
      - subst f0. subst r. assert (Hfv : value (tm_abs U body)) by (apply v_abs; exact Hlc).
        destruct (Hsemf (tm_abs U body) (multi_refl step (tm_abs U body)) Hfv)
          as [U' [body' [Efun Hfun]]].
        pose proof (Hfun a Ha) as Hred.
        eapply reducible_step; [exact Hred|].
        apply ST_AppAbs; assumption.
    }
    eapply reducible_from_steps.
    - apply lc_app; [exact Hlf|exact Hla].
    - constructor. intros r Hr. apply reducible_sn with (T := B) (t := r).
      apply Hsteps. exact Hr.
    - apply not_value_app.
    - exact Hsteps.
  }
  pose proof (reducible_sn _ _ Hfun0) as Hsnbase.
  eapply Happ; [exact Hsnbase|exact Hfun0|exact Harg0].
Qed.

Lemma reducible_abs_app : forall A B U body u,
  locally_closed (tm_abs U body) ->
  (forall a, reducible A a -> reducible B (open body a)) ->
  reducible A u -> reducible B (tm_app (tm_abs U body) u).
Proof.
  intros A B U body u Hlabs Hbody Hu.
  assert (Hprop : forall u, strongly_normalizing u -> reducible A u ->
      reducible B (tm_app (tm_abs U body) u)).
  { intros u0 Hsn. induction Hsn as [u0 Hnext IH]; intros Hu0.
    assert (Hsteps : forall r, tm_app (tm_abs U body) u0 --> r -> reducible B r).
    { intros r Hstep. inversion Hstep; subst.
      - exact (Hbody u0 Hu0).
      - inversion H1.
      - exact (IH t2' H3 (reducible_step A u0 t2' Hu0 H3)).
    }
    eapply reducible_from_steps.
    - apply lc_app; [exact Hlabs|eapply reducible_lc; exact Hu0].
    - constructor. intros r Hr. apply reducible_sn with (T := B) (t := r). apply Hsteps; exact Hr.
    - apply not_value_app.
    - exact Hsteps.
  }
  eapply Hprop; [eapply reducible_sn; exact Hu|exact Hu].
Qed.

Lemma numeric_no_step : forall n, numeric_value n -> forall n', ~ (n --> n').
Proof.
  intros n Hn; induction Hn; intros n' Hs.
  - inversion Hs.
  - inversion Hs; subst. eapply IHHn. eassumption.
Qed.

Lemma value_no_step : forall v, value v -> forall v', ~ (v --> v').
Proof.
  intros v Hv; inversion Hv; subst; intros v' Hs.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs.
  - eapply numeric_no_step; eassumption.
Qed.

Lemma reducible_true : reducible Ty_Bool tm_true.
Proof.
  apply reducible_intro.
  - constructor.
  - constructor. intros t' Hs. inversion Hs.
  - intros v Hmv Hv. inversion Hmv; subst.
    + left; reflexivity.
    + inversion H.
Qed.

Lemma reducible_false : reducible Ty_Bool tm_false.
Proof.
  apply reducible_intro.
  - constructor.
  - constructor. intros t' Hs. inversion Hs.
  - intros v Hmv Hv. inversion Hmv; subst.
    + right; reflexivity.
    + inversion H.
Qed.

Lemma reducible_numeric : forall n, numeric_value n -> reducible Ty_Nat n.
Proof.
  intros n Hn. apply reducible_intro.
  - apply numeric_value_lc; assumption.
  - constructor. intros t' Hs. exfalso. eapply value_no_step; [constructor; exact Hn|exact Hs].
  - intros v Hmv Hv. inversion Hmv; subst.
    + exact Hn.
    + exfalso. eapply value_no_step; [constructor; exact Hn|eassumption].
Qed.

Lemma not_value_if : forall c a b, ~ value (tm_if c a b).
Proof. intros c a b H; inversion H; subst; try discriminate; inversion H0. Qed.

Lemma not_value_natrec : forall n b s, ~ value (tm_natrec n b s).
Proof. intros n b s H; inversion H; subst; try discriminate; inversion H0. Qed.

Lemma reducible_succ : forall n, reducible Ty_Nat n ->
  reducible Ty_Nat (tm_succ n).
Proof.
  intros n Hn.
  assert (Hprop : forall n, strongly_normalizing n ->
      reducible Ty_Nat n -> reducible Ty_Nat (tm_succ n)).
  { intros n0 Hsn0. induction Hsn0 as [n0 Hnext IH]; intros Hn0.
    apply reducible_intro.
    - apply lc_succ. eapply reducible_lc; exact Hn0.
    - constructor. intros r Hs. inversion Hs; subst.
      apply reducible_sn with (T := Ty_Nat).
      eapply IH; [eassumption|]. eapply reducible_step; eassumption.
    - intros v Hmv Hv. inversion Hmv; subst.
      + inversion Hv; subst; try discriminate.
        exact H.
      + inversion H; subst. pose proof (IH t' H2 (reducible_step Ty_Nat n0 t' Hn0 H2)) as Hredmid.
        pose proof (reducible_outcome Ty_Nat (tm_succ t') Hredmid) as Houtmid.
        eapply Houtmid; eassumption.
  }
  eapply Hprop; [eapply reducible_sn; exact Hn|exact Hn].
Qed.

Lemma reducible_if : forall T c a b,
  reducible Ty_Bool c -> reducible T a -> reducible T b ->
  reducible T (tm_if c a b).
Proof.
  intros T c a b Hc Ha Hb.
  assert (Hprop : forall c, strongly_normalizing c -> reducible Ty_Bool c ->
      reducible T (tm_if c a b)).
  { intros c0 Hsn0. induction Hsn0 as [c0 Hnext IH]; intros Hc0.
    assert (Hsteps : forall r, tm_if c0 a b --> r -> reducible T r).
    { intros r Hs. inversion Hs; subst.
      - exact Ha.
      - exact Hb.
      - eapply IH; [eassumption|]. eapply reducible_step; eassumption.
    }
    eapply reducible_from_steps.
    - apply lc_if; [eapply reducible_lc; exact Hc0|eapply reducible_lc; exact Ha|eapply reducible_lc; exact Hb].
    - constructor. intros r Hr. apply reducible_sn with (T := T) (t := r). apply Hsteps; exact Hr.
    - apply not_value_if.
    - exact Hsteps.
  }
  eapply Hprop; [eapply reducible_sn; exact Hc|exact Hc].
Qed.

Lemma reducible_natrec_numeric : forall T n, numeric_value n ->
  forall b s, reducible T b -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n Hn. induction Hn as [|n Hn IHn]; intros b s Hb Hs.
  - assert (Hcomp : forall b, strongly_normalizing b -> reducible T b ->
        forall s, strongly_normalizing s ->
          reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
          reducible T (tm_natrec tm_zero b s)).
    { intros b0 Hsb. induction Hsb as [b0 Hnextb IHb]; intros Hb0 s0 Hss.
      induction Hss as [s0 Hnexts IHs]; intros Hs0.
      assert (Hsteps : forall r, tm_natrec tm_zero b0 s0 --> r -> reducible T r).
      { intros r Hstep. inversion Hstep; subst.
        - exfalso. eapply numeric_no_step; [constructor|eassumption].
        - exact (IHb b' H4 (reducible_step T b0 b' Hb0 H4) s0 (SN_intro s0 Hnexts) Hs0).
        - exact (IHs s' H5 (reducible_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 s' Hs0 H5)).
        - exact Hb0.
      }
      eapply reducible_from_steps.
      - apply lc_rec; [constructor|eapply reducible_lc; exact Hb0|eapply reducible_lc; exact Hs0].
      - constructor. intros r Hr. apply reducible_sn with (T := T) (t := r). apply Hsteps; exact Hr.
      - apply not_value_natrec.
      - exact Hsteps.
    }
    eapply Hcomp; [eapply reducible_sn; exact Hb|exact Hb|eapply reducible_sn; exact Hs|exact Hs].
  - assert (Hcomp : forall b, strongly_normalizing b -> reducible T b ->
        forall s, strongly_normalizing s ->
          reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
          reducible T (tm_natrec (tm_succ n) b s)).
    { intros b0 Hsb. induction Hsb as [b0 Hnextb IHb]; intros Hb0 s0 Hss.
      induction Hss as [s0 Hnexts IHs]; intros Hs0.
      assert (Hsteps : forall r, tm_natrec (tm_succ n) b0 s0 --> r -> reducible T r).
      { intros r Hstep. inversion Hstep; subst.
        - exfalso. eapply numeric_no_step; [constructor; exact Hn|eassumption].
        - exact (IHb b' H4 (reducible_step T b0 b' Hb0 H4) s0 (SN_intro s0 Hnexts) Hs0).
        - exact (IHs s' H5 (reducible_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 s' Hs0 H5)).
        - pose proof (IHn b0 s0 Hb0 Hs0) as Hlower.
          pose proof (reducible_numeric n Hn) as Hpred.
          pose proof (reducible_app Ty_Nat (Ty_Arrow T T) s0 n Hs0 Hpred) as Hfun.
          exact (reducible_app T T (tm_app s0 n) (tm_natrec n b0 s0) Hfun Hlower).
      }
      eapply reducible_from_steps.
      - apply lc_rec; [apply lc_succ; apply numeric_value_lc; exact Hn|eapply reducible_lc; exact Hb0|eapply reducible_lc; exact Hs0].
      - constructor. intros r Hr. apply reducible_sn with (T := T) (t := r). apply Hsteps; exact Hr.
      - apply not_value_natrec.
      - exact Hsteps.
    }
    eapply Hcomp; [eapply reducible_sn; exact Hb|exact Hb|eapply reducible_sn; exact Hs|exact Hs].
Qed.

Lemma reducible_natrec : forall T n b s,
  reducible Ty_Nat n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n b s Hn Hb Hs.
  assert (Hprop : forall n, strongly_normalizing n -> reducible Ty_Nat n ->
      forall b, strongly_normalizing b -> reducible T b ->
      forall s, strongly_normalizing s ->
        reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
        reducible T (tm_natrec n b s)).
  { intros n0 Hsn. induction Hsn as [n0 Hnextn IHn]; intros Hn0 b0 Hsb.
    induction Hsb as [b0 Hnextb IHb]; intros Hb0 s0 Hss.
    induction Hss as [s0 Hnexts IHs]; intros Hs0.
    assert (Hsteps : forall r, tm_natrec n0 b0 s0 --> r -> reducible T r).
    { intros r Hstep. inversion Hstep; subst.
      - exact (IHn n' H2 (reducible_step Ty_Nat n0 n' Hn0 H2)
          b0 (SN_intro b0 Hnextb) Hb0 s0 (SN_intro s0 Hnexts) Hs0).
      - exact (IHb b' H4 (reducible_step T b0 b' Hb0 H4)
          s0 (SN_intro s0 Hnexts) Hs0).
      - exact (IHs s' H5 (reducible_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 s' Hs0 H5)).
      - exact Hb0.
      - pose proof (reducible_numeric n1 H2) as Hpred.
        pose proof (reducible_app Ty_Nat (Ty_Arrow T T) s0 n1 Hs0 Hpred) as Hfun.
        pose proof (reducible_natrec_numeric T n1 H2 b0 s0 Hb0 Hs0) as Hlower.
        exact (reducible_app T T (tm_app s0 n1) (tm_natrec n1 b0 s0) Hfun Hlower).
    }
    eapply reducible_from_steps.
    - apply lc_rec; [eapply reducible_lc; exact Hn0|eapply reducible_lc; exact Hb0|eapply reducible_lc; exact Hs0].
    - constructor. intros r Hr. apply reducible_sn with (T := T) (t := r). apply Hsteps; exact Hr.
    - apply not_value_natrec.
    - exact Hsteps.
  }
  eapply Hprop; [eapply reducible_sn; exact Hn|exact Hn|eapply reducible_sn; exact Hb|exact Hb|eapply reducible_sn; exact Hs|exact Hs].
Qed.

Lemma in_le_max : forall L : list atom, forall y, In y L -> y <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros y Hy; simpl in *.
  - contradiction.
  - destruct Hy as [->|Hy].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [eapply IH; exact Hy|apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (fold_right Nat.max 0 L)).
  intro Hin. pose proof (in_le_max L _ Hin). lia.
Qed.

Lemma typing_locally_closed : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty.
  - constructor.
  - unfold locally_closed. apply lc_abs.
    destruct (fresh_atom L) as [x Hx].
    apply lc_open_rec_inv with (x := x).
    specialize (H0 x Hx). exact H0.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor.
  - constructor. assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma subst_env_open : forall sigma t u,
  (forall x, locally_closed (sigma x)) ->
  subst_env sigma (open t u) = open (subst_env sigma t) (subst_env sigma u).
Proof.
  intros sigma t u Hclosed. unfold open. generalize 0. revert u.
  induction t; intros u k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - replace k with (k + 0) by lia.
    rewrite (open_rec_closed 0 (sigma a) (Hclosed a) k (subst_env sigma u)). reflexivity.
  - rewrite (IHt1 u k), (IHt2 u k). reflexivity.
  - rewrite (IHt u (S k)). reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IHt u k). reflexivity.
  - rewrite (IHt1 u k), (IHt2 u k), (IHt3 u k). reflexivity.
  - rewrite (IHt1 u k), (IHt2 u k), (IHt3 u k). reflexivity.
Qed.

Lemma fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> forall sigma,
  ctx_interp Gamma sigma -> reducible T (subst_env sigma t).
Proof.
  intros Gamma t T Hty. induction Hty; intros sigma Henv; simpl.
  - destruct Henv as [_ Henv]. eapply Henv; eassumption.
  - destruct Henv as [Hclosed Htyping].
    assert (Hlcabs : locally_closed (tm_abs T1 t1)).
    { apply typing_locally_closed with (Gamma := Gamma) (T := Ty_Arrow T1 T2).
      econstructor. exact H. }
    apply (reducible_intro (Ty_Arrow T1 T2) (tm_abs T1 (subst_env sigma t1))).
    + change (lc_at 0 (subst_env sigma (tm_abs T1 t1))).
      eapply subst_env_lc; [exact Hlcabs|exact Hclosed].
    + constructor. intros t' Hstep. inversion Hstep.
    + intros v Hmv Hv. inversion Hmv; subst.
      * exists T1, (subst_env sigma t1). split; [reflexivity|]. intros u Hu.
        assert (Hbody : forall a, reducible T1 a -> reducible T2 (open (subst_env sigma t1) a)).
        { intros a Ha. destruct (fresh_atom (L ++ fv t1)) as [x Hx].
          assert (HxL : ~ In x L) by (intro Hin; apply Hx; apply in_or_app; left; exact Hin).
          assert (HxFV : ~ In x (fv t1)) by (intro Hin; apply Hx; apply in_or_app; right; exact Hin).
          specialize (H0 x HxL (env_update sigma x a)).
          assert (Henvx : ctx_interp (update Gamma x T1) (env_update sigma x a)).
          { apply ctx_interp_update; [split; assumption|exact Ha]. }
          specialize (H0 Henvx).
          rewrite subst_env_open in H0.
          2:{ intros y. unfold env_update. destruct (Nat.eqb x y); [eapply reducible_lc; exact Ha|apply Hclosed]. }
          rewrite subst_env_update_fresh in H0 by exact HxFV.
          unfold env_update in H0. simpl in H0. rewrite Nat.eqb_refl in H0. exact H0.
        }
        eapply reducible_abs_app.
        -- change (locally_closed (subst_env sigma (tm_abs T1 t1))).
           eapply subst_env_lc; [exact Hlcabs|exact Hclosed].
        -- exact Hbody.
        -- exact Hu.
      * inversion H1.
  - eapply reducible_app; eauto.
  - apply reducible_true.
  - apply reducible_false.
  - apply reducible_numeric. constructor.
  - apply reducible_succ. eauto.
  - eapply reducible_natrec; eauto.
  - eapply reducible_if; eauto.
Qed.

Lemma subst_env_id : forall t, subst_env (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x)) as Hred.
  assert (Henv : ctx_interp empty (fun x => tm_fvar x)).
  { split.
    - intros x. unfold locally_closed. constructor.
    - intros x U H. discriminate.
  }
  specialize (Hred Henv).
  rewrite subst_env_id in Hred.
  eapply reducible_sn. exact Hred.
Qed.

End STLCNormalizationIfRecursionHardTask.
