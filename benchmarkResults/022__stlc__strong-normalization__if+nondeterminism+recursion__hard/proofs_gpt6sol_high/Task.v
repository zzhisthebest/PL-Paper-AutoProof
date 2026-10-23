(** STLC CBV strong-normalization benchmark, Hard variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Arith.Compare_dec Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfNondeterminismRecursionHardTask.

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
  | tm_if : tm -> tm -> tm -> tm
  | tm_choice : tm -> tm -> tm.

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
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm at level 200) : stlc_scope.

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
  | tm_choice t1 t2 => tm_choice (open_rec k u t1) (open_rec k u t2)
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
  | lc_choice : forall k t1 t2,
      lc_at k t1 -> lc_at k t2 -> lc_at k (tm_choice t1 t2).

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

Hint Constructors lc_at : core.

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
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t2
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
  | T_Choice : forall Gamma t1 t2 T,
      <{ Gamma |-- $(t1) \in T }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- choice $(t1) or $(t2) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.

Inductive strongly_normalizing : tm -> Prop :=

  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Lemma lc_weaken : forall k j t,
  lc_at k t -> k <= j -> lc_at j t.
Proof.
  intros k j t H. revert j.
  induction H; intros j Hj; eauto using lc_at.
  apply lc_bvar; lia.
  apply lc_abs. apply IHlc_at. lia.
Qed.

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> locally_closed u -> lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Ht Hu; inversion Ht; subst; simpl; try (constructor; eauto; fail).
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. eapply lc_weaken; eauto; lia.
    + constructor. apply Nat.eqb_neq in E. lia.
Qed.

Lemma lc_open_inv : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; intros k u H; simpl in H; try (inversion H; subst; constructor; eauto; fail).
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion H; subst. apply Nat.eqb_neq in E. constructor; lia.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed n.
Proof. intros n H; induction H; constructor; auto. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof. intros v H; inversion H; subst; eauto using numeric_lc; constructor. Qed.

Lemma numeric_no_step : forall n n', numeric_value n -> n --> n' -> False.
Proof.
  intros n n' Hn. revert n'. induction Hn; intros n' Hs; inversion Hs; subst; eauto.
Qed.

Lemma value_no_step : forall v v', value v -> v --> v' -> False.
Proof.
  intros v v' Hv Hs. inversion Hv; subst; inversion Hs; subst;
    eauto using numeric_no_step.
Qed.

Lemma lc_at_dec : forall t k, {lc_at k t} + {~ lc_at k t}.
Proof.
  induction t; intro k.
  - destruct (lt_dec n k) as [H|H].
    + left; constructor; exact H.
    + right; intro Hlc; inversion Hlc; lia.
  - left; constructor.
  - destruct (IHt1 k) as [H1|H1]; destruct (IHt2 k) as [H2|H2];
      try (left; constructor; assumption);
      right; intro Hlc; inversion Hlc; subst; contradiction.
  - destruct (IHt (S k)) as [H|H].
    + left; constructor; exact H.
    + right; intro Hlc; inversion Hlc; subst; contradiction.
  - left; constructor.
  - left; constructor.
  - left; constructor.
  - destruct (IHt k) as [H|H].
    + left; constructor; exact H.
    + right; intro Hlc; inversion Hlc; subst; contradiction.
  - destruct (IHt1 k) as [H1|H1]; destruct (IHt2 k) as [H2|H2];
      destruct (IHt3 k) as [H3|H3];
      try (left; constructor; assumption);
      right; intro Hlc; inversion Hlc; subst; contradiction.
  - destruct (IHt1 k) as [H1|H1]; destruct (IHt2 k) as [H2|H2];
      destruct (IHt3 k) as [H3|H3];
      try (left; constructor; assumption);
      right; intro Hlc; inversion Hlc; subst; contradiction.
  - destruct (IHt1 k) as [H1|H1]; destruct (IHt2 k) as [H2|H2];
      try (left; constructor; assumption);
      right; intro Hlc; inversion Hlc; subst; contradiction.
Qed.

Lemma numeric_dec : forall t, {numeric_value t} + {~ numeric_value t}.
Proof.
  induction t; try (right; intro H; inversion H; fail).
  - left; constructor.
  - destruct IHt as [H|H].
    + left; constructor; exact H.
    + right; intro Hnum; inversion Hnum; subst; contradiction.
Qed.

Lemma value_dec : forall t, {value t} + {~ value t}.
Proof.
  intro t. destruct t.
  all: try solve [match goal with |- {value ?v} + {~ value ?v} =>
    destruct (numeric_dec v) as [Hnum|Hnum];
    [left; constructor; exact Hnum |
     right; intro Hv; inversion Hv; subst; contradiction] end].
  - destruct (lc_at_dec (tm_abs t t0) 0) as [Hlc|Hlc].
    + left; constructor; exact Hlc.
    + right; intro Hv; inversion Hv; subst;
        try (apply Hlc; assumption);
        match goal with Hnum : numeric_value (tm_abs _ _) |- _ => inversion Hnum end.
  - left; constructor.
  - left; constructor.
Qed.

Lemma step_lc : forall t u, t --> u -> locally_closed t -> locally_closed u.
Proof.
  intros t u Hs. induction Hs; intro Hlc; inversion Hlc; subst;
    unfold locally_closed in *; eauto 8 using lc_at, numeric_lc, value_lc.
  - inversion H; subst; eapply lc_open_rec; eauto using value_lc.
  - eapply lc_app.
    + eapply lc_app; [exact H8 | exact (numeric_lc _ H)].
    + eapply lc_rec; [exact (numeric_lc _ H) | exact H7 | exact H8].
Qed.

Lemma multi_trans : forall x y z, x -->* y -> y -->* z -> x -->* z.
Proof.
  intros x y z Hxy Hyz. induction Hxy; eauto using multi.
Qed.

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool => forall v, t -->* v -> value v -> v = tm_true \/ v = tm_false
  | Ty_Nat => forall v, t -->* v -> value v -> numeric_value v
  | Ty_Arrow A B => forall v, t -->* v -> value v ->
      forall a, reducible A a -> reducible B (tm_app v a)
  end.

Lemma red_lc : forall T t, reducible T t -> locally_closed t.
Proof. intros T t H; destruct T; exact (proj1 H). Qed.

Lemma red_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. intros T t H; destruct T; exact (proj1 (proj2 H)). Qed.

Lemma red_step : forall T t u,
  reducible T t -> t --> u -> reducible T u.
Proof.
  intros T t u H Hstep. destruct T; simpl in *;
    destruct H as [Hlc [Hsn Hval]];
    (split; [eapply step_lc; eauto|];
     split; [inversion Hsn; subst; eauto|];
     intros v Hm Hv; eapply Hval; eauto using multi).
Qed.

Lemma red_intro : forall T t,
  locally_closed t -> ~ value t ->
  (forall u, t --> u -> reducible T u) -> reducible T t.
Proof.
  intros T t Hlc Hnv Hsucc. destruct T; simpl;
    (split; [exact Hlc|]; split;
     [constructor; intros u Hu; apply (red_sn _ _ (Hsucc u Hu))|];
     intros v Hm Hv; inversion Hm; subst;
     [exfalso; apply Hnv; assumption|];
     match goal with
     | Hs : t --> ?u, Hr : ?u -->* v |- _ =>
         exact ((proj2 (proj2 (Hsucc u Hs))) v Hr Hv)
     end).
Qed.

Lemma red_true : reducible Ty_Bool tm_true.
Proof.
  simpl. split; [constructor|]. split.
  - constructor. intros u Hs. exact (False_rect _ (value_no_step _ _ v_true Hs)).
  - intros v Hm _. inversion Hm; subst; [left; reflexivity|].
    exfalso; eapply value_no_step; [exact v_true|eassumption].
Qed.

Lemma red_false : reducible Ty_Bool tm_false.
Proof.
  simpl. split; [constructor|]. split.
  - constructor. intros u Hs. exact (False_rect _ (value_no_step _ _ v_false Hs)).
  - intros v Hm _. inversion Hm; subst; [right; reflexivity|].
    exfalso; eapply value_no_step; [exact v_false|eassumption].
Qed.

Lemma red_numeric : forall n, numeric_value n -> reducible Ty_Nat n.
Proof.
  intros n Hn. simpl. split; [exact (numeric_lc _ Hn)|]. split.
  - constructor. intros u Hs. exact (False_rect _ (numeric_no_step _ _ Hn Hs)).
  - intros v Hm _. inversion Hm; subst; [assumption|].
    exfalso; eapply numeric_no_step; [exact Hn|eassumption].
Qed.

Lemma red_app : forall A B f a,
  reducible (Ty_Arrow A B) f -> reducible A a ->
  reducible B (tm_app f a).
Proof.
  intros A B f a Hf Ha.
  pose proof (red_sn _ _ Hf) as Hsn.
  revert a Hf Ha. induction Hsn as [f IH]; intros a Hf Ha.
  destruct (value_dec f) as [Hv|Hnv].
  - exact ((proj2 (proj2 Hf)) f (multi_refl _ _) Hv a Ha).
  - apply red_intro.
    + apply lc_app; [exact (red_lc _ _ Hf)|exact (red_lc _ _ Ha)].
    + intro Hv. inversion Hv; subst; inversion H0.
    + intros u Hs. inversion Hs; subst.
      * exfalso; apply Hnv; constructor; assumption.
      * eapply H; eauto using red_step.
      * exfalso; apply Hnv; assumption.
Qed.

Lemma red_succ : forall n,
  reducible Ty_Nat n -> reducible Ty_Nat (tm_succ n).
Proof.
  intros n Hn. pose proof (red_sn _ _ Hn) as Hsn.
  induction Hsn as [n Hstep IH].
  destruct (value_dec n) as [Hv|Hnv].
  - pose proof ((proj2 (proj2 Hn)) n (multi_refl _ _) Hv) as Hnum.
    apply red_numeric. constructor; exact Hnum.
  - apply red_intro.
    + apply lc_succ. exact (red_lc _ _ Hn).
    + intro Hv. inversion Hv; subst.
      match goal with Hnum : numeric_value _ |- _ => inversion Hnum; subst end.
      apply Hnv. constructor; assumption.
    + intros u Hs. inversion Hs; subst.
      eapply IH; eauto using red_step.
Qed.

Lemma red_choice : forall T t1 t2,
  reducible T t1 -> reducible T t2 ->
  reducible T (tm_choice t1 t2).
Proof.
  intros T t1 t2 H1 H2. apply red_intro.
  - apply lc_choice; [exact (red_lc _ _ H1)|exact (red_lc _ _ H2)].
  - intro Hv. inversion Hv; subst.
    match goal with Hnum : numeric_value _ |- _ => inversion Hnum end.
  - intros u Hs. inversion Hs; subst; assumption.
Qed.

Lemma red_if : forall T c t1 t2,
  reducible Ty_Bool c -> reducible T t1 -> reducible T t2 ->
  reducible T (tm_if c t1 t2).
Proof.
  intros T c t1 t2 Hc H1 H2.
  pose proof (red_sn _ _ Hc) as Hsn.
  induction Hsn as [c Hstep IH].
  apply red_intro.
  - apply lc_if; [exact (red_lc _ _ Hc)|exact (red_lc _ _ H1)|exact (red_lc _ _ H2)].
  - intro Hv. inversion Hv; subst.
    match goal with Hnum : numeric_value _ |- _ => inversion Hnum end.
  - intros u Hs. inversion Hs; subst.
    + exact H1.
    + exact H2.
    + eapply IH; eauto using red_step.
Qed.

Lemma red_beta : forall A B t a,
  locally_closed (tm_abs A t) ->
  (forall v, value v -> reducible A v -> reducible B (open t v)) ->
  reducible A a -> reducible B (tm_app (tm_abs A t) a).
Proof.
  intros A B t a Hlc Hbody Ha.
  pose proof (red_sn _ _ Ha) as Hsn.
  induction Hsn as [a Hstep IH].
  apply red_intro.
  - apply lc_app; [exact Hlc|exact (red_lc _ _ Ha)].
  - intro Hv. inversion Hv; subst.
    match goal with Hnum : numeric_value _ |- _ => inversion Hnum end.
  - intros u Hs. inversion Hs; subst.
    + apply Hbody; eauto using red_step.
    + exfalso. eapply value_no_step; [constructor; exact Hlc|eassumption].
    + eapply IH; eauto using red_step.
Qed.

Lemma red_abs : forall A B t,
  locally_closed (tm_abs A t) ->
  (forall v, value v -> reducible A v -> reducible B (open t v)) ->
  reducible (Ty_Arrow A B) (tm_abs A t).
Proof.
  intros A B t Hlc Hbody. simpl. split; [exact Hlc|]. split.
  - constructor. intros u Hs. exfalso.
    eapply value_no_step; [constructor; exact Hlc|exact Hs].
  - intros v Hm Hv a Ha. inversion Hm; subst.
    + eapply red_beta; eauto.
    + exfalso. eapply value_no_step; [constructor; exact Hlc|eassumption].
Qed.

Lemma rec_not_value : forall n b s, ~ value (tm_natrec n b s).
Proof.
  intros n b s Hv. inversion Hv; subst.
  match goal with H : numeric_value (tm_natrec _ _ _) |- _ => inversion H end.
Qed.

Lemma red_rec_num_values : forall n,
  numeric_value n -> forall T b s,
  reducible T b -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  value b -> value s -> reducible T (tm_natrec n b s).
Proof.
  intros n Hnum. induction Hnum as [|n Hnum IH]; intros T b s Hb Hs Hvb Hvs.
  - apply red_intro.
    + apply lc_rec; [constructor|exact (red_lc _ _ Hb)|exact (red_lc _ _ Hs)].
    + apply rec_not_value.
    + intros u Hstep. inversion Hstep; subst.
      * exfalso. eapply numeric_no_step; [constructor|eassumption].
      * exfalso. eapply value_no_step; [exact Hvb|eassumption].
      * exfalso. eapply value_no_step; [exact Hvs|eassumption].
      * exact Hb.
  - apply red_intro.
    + apply lc_rec; [exact (numeric_lc _ (nv_succ _ Hnum))|
        exact (red_lc _ _ Hb)|exact (red_lc _ _ Hs)].
    + apply rec_not_value.
    + intros u Hstep. inversion Hstep; subst.
      * exfalso. eapply numeric_no_step; [constructor; exact Hnum|eassumption].
      * exfalso. eapply value_no_step; [exact Hvb|eassumption].
      * exfalso. eapply value_no_step; [exact Hvs|eassumption].
      * eapply red_app.
        -- eapply red_app; [exact Hs|apply red_numeric; exact Hnum].
        -- apply IH; assumption.
Qed.

Lemma red_rec_num : forall n T b s,
  numeric_value n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros n T b s Hnum Hb Hs.
  pose proof (red_sn _ _ Hb) as Hsnb.
  revert Hb s Hs.
  induction Hsnb as [b Hbstep IHb]; intros Hb s Hs.
  pose proof (red_sn _ _ Hs) as Hsns.
  revert Hs.
  induction Hsns as [s Hsstep IHs]; intros Hs.
  destruct (value_dec b) as [Hvb|Hnvb];
    destruct (value_dec s) as [Hvs|Hnvs].
  all: try solve [eapply red_rec_num_values; eauto].
  all: apply red_intro.
  all: try (apply lc_rec; [exact (numeric_lc _ Hnum)|
    exact (red_lc _ _ Hb)|exact (red_lc _ _ Hs)]).
  all: try (apply rec_not_value).
  all: intros u Hstep; inversion Hstep; subst;
    try (exfalso; eapply numeric_no_step; [exact Hnum|eassumption]);
    try (exfalso; eapply Hnvb; eassumption);
    try (exfalso; eapply Hnvs; eassumption);
    try solve [eapply IHb; [eassumption|eapply red_step; eauto|assumption]];
    try solve [eapply IHs; [eassumption|eapply red_step; eauto]].
Qed.

Lemma red_rec : forall n T b s,
  reducible Ty_Nat n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros n T b s Hn Hb Hs.
  pose proof (red_sn _ _ Hn) as Hsn.
  induction Hsn as [n Hnstep IH].
  destruct (numeric_dec n) as [Hnum|Hnnum].
  - eapply red_rec_num; eauto.
  - apply red_intro.
    + apply lc_rec; [exact (red_lc _ _ Hn)|
        exact (red_lc _ _ Hb)|exact (red_lc _ _ Hs)].
    + apply rec_not_value.
    + intros u Hstep. inversion Hstep; subst;
        try solve [exfalso; apply Hnnum; assumption];
        try solve [exfalso; apply Hnnum; constructor; assumption];
        try solve [exfalso; apply Hnnum; constructor];
        try solve [eapply IH; [eassumption|eapply red_step; eauto]].
Qed.

Fixpoint maxfv (t : tm) : nat :=
  match t with
  | tm_bvar _ => 0
  | tm_fvar x => x
  | tm_app a b => Nat.max (maxfv a) (maxfv b)
  | tm_abs _ a => maxfv a
  | tm_true | tm_false | tm_zero => 0
  | tm_succ a => maxfv a
  | tm_natrec n b s => Nat.max (maxfv n) (Nat.max (maxfv b) (maxfv s))
  | tm_if c a b => Nat.max (maxfv c) (Nat.max (maxfv a) (maxfv b))
  | tm_choice a b => Nat.max (maxfv a) (maxfv b)
  end.

Definition fresh (L : list atom) : atom := S (fold_right Nat.max 0 L).

Lemma fold_max_bound : forall L x, In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|y L IH]; intros x H; simpl in *; [contradiction|].
  destruct H as [->|H]; [lia|]. specialize (IH _ H); lia.
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L H. unfold fresh in H.
  pose proof (fold_max_bound _ _ H). lia.
Qed.

Lemma has_type_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty; unfold locally_closed in *;
    eauto 8 using lc_at.
  - assert (Hx : ~ In (fresh L) L) by apply fresh_notin.
    specialize (H (fresh L) Hx).
    specialize (H0 (fresh L) Hx).
    apply lc_abs. eapply lc_open_inv; exact H0.
Qed.

Fixpoint subst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app a b => tm_app (subst rho a) (subst rho b)
  | tm_abs T a => tm_abs T (subst rho a)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (subst rho a)
  | tm_natrec n b s => tm_natrec (subst rho n) (subst rho b) (subst rho s)
  | tm_if c a b => tm_if (subst rho c) (subst rho a) (subst rho b)
  | tm_choice a b => tm_choice (subst rho a) (subst rho b)
  end.

Lemma subst_lc : forall k t rho,
  lc_at k t -> (forall x, locally_closed (rho x)) -> lc_at k (subst rho t).
Proof.
  intros k t rho Hlc. revert rho.
  induction Hlc; intros rho Henv; simpl; eauto using lc_at, lc_weaken.
  - eapply lc_weaken; [apply Henv|lia].
Qed.

Lemma open_rec_lc_id : forall k t u,
  lc_at k t -> open_rec k u t = t.
Proof.
  intros k t u Hlc. induction Hlc; simpl; try (f_equal; eauto; fail).
  - destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Definition env_update (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

Lemma subst_open_fresh : forall t k rho x v,
  maxfv t < x -> (forall y, locally_closed (rho y)) ->
  subst (env_update rho x v) (open_rec k (tm_fvar x) t) =
  open_rec k v (subst rho t).
Proof.
  induction t; intros k rho x v Hfresh Henv; simpl in *;
    try (f_equal; eauto; fail).
  - destruct (Nat.eqb k n); simpl; unfold env_update;
      [rewrite Nat.eqb_refl|]; reflexivity.
  - unfold env_update. assert (E : Nat.eqb x a = false) by (apply Nat.eqb_neq; lia).
    rewrite E.
    symmetry. apply open_rec_lc_id.
    eapply lc_weaken; [apply Henv|lia].
  - f_equal; [eapply IHt1|eapply IHt2]; eauto; lia.
  - f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto; lia.
  - f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto; lia.
  - f_equal; [eapply IHt1|eapply IHt2]; eauto; lia.
Qed.

Definition env_ok (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x, locally_closed (rho x)) /\
  (forall x T, Gamma x = Some T -> value (rho x) /\ reducible T (rho x)).

Lemma env_ok_update : forall Gamma rho x A v,
  env_ok Gamma rho -> value v -> reducible A v ->
  env_ok (update Gamma x A) (env_update rho x v).
Proof.
  intros Gamma rho x A v [Hlc Hgood] Hv Hr. split.
  - intro y. unfold env_update. destruct (Nat.eqb x y); auto using value_lc.
  - intros y T Hy. unfold env_update, update in *.
    destruct (Nat.eqb x y) eqn:E.
    + inversion Hy; subst; auto.
    + eapply Hgood; eauto.
Qed.

Lemma pick_fresh : forall L t, exists x,
  ~ In x L /\ maxfv t < x.
Proof.
  intros L t. exists (S (Nat.max (fold_right Nat.max 0 L) (maxfv t))).
  split; [|lia]. intro H.
  pose proof (fold_max_bound _ _ H). lia.
Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T -> forall rho, env_ok Gamma rho -> reducible T (subst rho t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho Henv; simpl.
  - exact (proj2 ((proj2 Henv) x T H)).
  - apply red_abs.
    + change (locally_closed (subst rho (tm_abs T1 t1))).
      apply subst_lc.
      * eapply has_type_lc. eapply T_Abs; eauto.
      * exact (proj1 Henv).
    + intros v Hv Hr.
      destruct (pick_fresh L t1) as [x [Hx Hfresh]].
      specialize (H0 x Hx (env_update rho x v)
        (env_ok_update _ _ _ _ _ Henv Hv Hr)).
      unfold open in H0.
      rewrite (subst_open_fresh t1 0 rho x v Hfresh (proj1 Henv)) in H0.
      exact H0.
  - eapply red_app; eauto.
  - exact red_true.
  - exact red_false.
  - apply red_numeric. constructor.
  - apply red_succ. auto.
  - eapply red_rec; eauto.
  - eapply red_if; eauto.
  - eapply red_choice; eauto.
Qed.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try reflexivity; f_equal; auto.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Henv : env_ok empty (fun x => tm_fvar x)).
  { split.
    - intro x. constructor.
    - intros x U H. discriminate H. }
  pose proof (fundamental _ _ _ Hty _ Henv) as Hr.
  rewrite subst_id in Hr.
  exact (red_sn _ _ Hr).
Qed.

End STLCNormalizationIfNondeterminismRecursionHardTask.
