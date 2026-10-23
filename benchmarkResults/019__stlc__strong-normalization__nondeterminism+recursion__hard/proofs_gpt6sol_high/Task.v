(** STLC CBV strong-normalization benchmark, Hard variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationNondeterminismRecursionHardTask.

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

Lemma lc_weaken : forall k j t, k <= j -> lc_at k t -> lc_at j t.
Proof.
  intros k j t Hle Hlc. revert j Hle.
  induction Hlc; intros j Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; eauto.
  - apply lc_abs. apply IHHlc. lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - apply lc_succ; eauto.
  - apply lc_rec; eauto.
  - apply lc_choice; eauto.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed n.
Proof. intros n H; induction H; constructor; auto. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. inversion Hv; subst; simpl; eauto using numeric_lc, lc_at;
    try constructor.
Qed.

Lemma open_lc : forall k t u,
  lc_at (S k) t -> locally_closed u -> lc_at k (open_rec k u t).
Proof.
  intros k t. revert k.
  induction t; intros k u Ht Hu; simpl in *.
  - inversion Ht; subst. destruct (Nat.eqb k n) eqn:E.
    + eapply lc_weaken with (k:=0); [lia|exact Hu].
    + apply Nat.eqb_neq in E. constructor. lia.
  - constructor.
  - inversion Ht; subst. constructor; eauto.
  - inversion Ht; subst. constructor. apply IHt; auto.
  - constructor.
  - constructor.
  - constructor.
  - inversion Ht; subst. constructor; eauto.
  - inversion Ht; subst. constructor; eauto.
  - inversion Ht; subst. constructor; eauto.
Qed.

Lemma open_lc_inverse : forall k t u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k t. revert k.
  induction t; intros k u H; simpl in H; try (inversion H; subst; constructor; eauto; fail).
  destruct (Nat.eqb k n) eqn:E.
  - constructor. apply Nat.eqb_eq in E. lia.
  - inversion H; subst. constructor. apply Nat.eqb_neq in E. lia.
Qed.

Lemma lc_step : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hstep. unfold locally_closed in *. revert Hlc.
  induction Hstep; intros Hlc; inversion Hlc; subst;
    eauto 8 using lc_at, open_lc, value_lc, numeric_lc.
  - inversion H4; subst. unfold open. eapply open_lc; eauto using value_lc.
  - constructor; [constructor; eauto using value_lc, numeric_lc |
    constructor; eauto using value_lc, numeric_lc].
    all: apply numeric_lc; auto.
Qed.

Lemma multi_trans : forall x y z, x -->* y -> y -->* z -> x -->* z.
Proof.
  intros x y z H. induction H; intros H2; eauto using multi.
Qed.

Lemma sn_step : forall t t', strongly_normalizing t -> t --> t' ->
  strongly_normalizing t'.
Proof. intros t t' H Hs; inversion H; subst; auto. Qed.

Lemma numeric_no_step : forall n n', numeric_value n -> ~ (n --> n').
Proof.
  intros n n' Hn. revert n'. induction Hn; intros n' Hs;
    inversion Hs; subst; eauto. eapply IHHn; eauto.
Qed.

Lemma value_no_step : forall v v', value v -> ~ (v --> v').
Proof.
  intros v v' Hv Hs. inversion Hv; subst;
    try solve [inversion Hs]. eapply numeric_no_step; eauto.
Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros v' Hs.
  exfalso. eapply value_no_step; eauto.
Qed.

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool => forall v, t -->* v -> value v -> v = tm_true \/ v = tm_false
  | Ty_Nat => forall v, t -->* v -> value v -> numeric_value v
  | Ty_Arrow A B =>
      forall v, t -->* v -> value v ->
        exists body, v = tm_abs A body /\
          (forall arg, value arg -> reducible A arg ->
            reducible B (open body arg))
  end.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. intros T t H; destruct T; exact (proj1 H). Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. intros T t H; destruct T; exact (proj1 (proj2 H)). Qed.

Lemma reducible_step : forall T t t', reducible T t -> t --> t' ->
  reducible T t'.
Proof.
  intros T t t' Hr Hs. destruct T; simpl in *;
    destruct Hr as [Hlc [Hsn Hval]];
    (split; [eapply lc_step; eauto|]; split;
     [eapply sn_step; eauto|]; intros v Hmulti Hv;
     apply Hval with (v:=v); eauto using multi).
Qed.

Lemma reducible_back : forall T t, locally_closed t -> ~ value t ->
  (forall t', t --> t' -> reducible T t') -> reducible T t.
Proof.
  intros T t Hlc Hnv Hall. destruct T; simpl;
    (split; [exact Hlc | split;
      [constructor; intros t' Hs; eapply reducible_sn; eauto
      | intros v Hm Hv; inversion Hm as [| a mid z Hstep Hrest]; subst]]).
  all: try (exfalso; apply Hnv; exact Hv).
  all: apply (proj2 (proj2 (Hall _ Hstep))) with (v:=v); auto.
Qed.

Lemma multi_value : forall v w, value v -> v -->* w -> v = w.
Proof.
  intros v w Hv Hm. inversion Hm; subst; auto.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma nonvalue_app : forall f a, ~ value (tm_app f a).
Proof.
  intros f a Hv. inversion Hv; subst; match goal with
    | H : numeric_value (tm_app _ _) |- _ => inversion H
  end.
Qed.

Lemma nonvalue_rec : forall n b s, ~ value (tm_natrec n b s).
Proof.
  intros n b s Hv. inversion Hv; subst; match goal with
    | H : numeric_value (tm_natrec _ _ _) |- _ => inversion H
  end.
Qed.

Lemma nonvalue_choice : forall a b, ~ value (tm_choice a b).
Proof.
  intros a b Hv. inversion Hv; subst; match goal with
    | H : numeric_value (tm_choice _ _) |- _ => inversion H
  end.
Qed.

Lemma reducible_bool : reducible Ty_Bool tm_true /\ reducible Ty_Bool tm_false.
Proof.
  split.
  - simpl. split; [apply lc_true|]. split;
      [apply sn_value; apply v_true|].
    intros v Hm Hv. rewrite <- (multi_value _ _ v_true Hm). auto.
  - simpl. split; [apply lc_false|]. split;
      [apply sn_value; apply v_false|].
    intros v Hm Hv. rewrite <- (multi_value _ _ v_false Hm). auto.
Qed.

Lemma reducible_zero : reducible Ty_Nat tm_zero.
Proof.
  simpl. split; [apply lc_zero|]; split;
    [apply sn_value; constructor; constructor|].
  intros v Hm Hv. rewrite <- (multi_value _ _ (v_nat _ nv_zero) Hm).
  constructor.
Qed.

Lemma sn_succ : forall n, strongly_normalizing n ->
  strongly_normalizing (tm_succ n).
Proof.
  intros n Hsn. induction Hsn as [n Hsteps IH]. constructor.
  intros t Hs. inversion Hs; subst; auto.
Qed.

Lemma multi_succ_shape : forall n v, tm_succ n -->* v ->
  exists n', v = tm_succ n'.
Proof.
  intros n v Hm. remember (tm_succ n) as t eqn:Heq.
  revert n Heq. induction Hm; intros n Heq; subst.
  - eauto.
  - inversion H; subst. eapply IHHm; eauto.
Qed.

Lemma reducible_succ : forall n, reducible Ty_Nat n ->
  reducible Ty_Nat (tm_succ n).
Proof.
  intros n [Hlc [Hsn Hval]]. simpl. split; [apply lc_succ; exact Hlc|]. split.
  - apply sn_succ; auto.
  - intros v Hm Hv. destruct (multi_succ_shape _ _ Hm) as [n' ->].
    inversion Hv; subst. inversion H; subst. constructor; auto.
Qed.

Lemma reducible_app : forall A B f arg,
  reducible (Ty_Arrow A B) f -> reducible A arg ->
  reducible B (tm_app f arg).
Proof.
  intros A B f arg Hf Ha.
  pose proof (reducible_sn _ _ Hf) as Hsnf.
  revert arg Hf Ha.
  induction Hsnf as [f Hsteps IHf]; intros arg Hf Ha.
  pose proof (reducible_sn _ _ Ha) as Hsna.
  revert Ha.
  induction Hsna as [arg Hasteps IHa]; intros Ha.
  apply reducible_back; [constructor; eapply reducible_lc; eauto
    | apply nonvalue_app |].
  intros next Hstep. inversion Hstep; subst.
  - destruct Hf as [_ [_ Hfun]].
    destruct (Hfun _ (multi_refl _ _) (v_abs _ _ H1)) as [body [Heq Hbody]].
    inversion Heq; subst. eapply Hbody; eauto.
  - apply IHf; [eauto | eapply reducible_step; eauto | exact Ha].
  - eapply IHa; [eauto | eapply reducible_step; eauto].
Qed.

Lemma reducible_numeric : forall n, numeric_value n -> reducible Ty_Nat n.
Proof.
  intros n Hn. induction Hn; auto using reducible_zero, reducible_succ.
Qed.

Lemma reducible_rec_numeral : forall n T b s,
  numeric_value n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros n T b s Hnum. revert T b s.
  induction Hnum as [|n Hnum IHnum]; intros T b s Hb Hs.
  all: pose proof (reducible_sn _ _ Hb) as Hsnb.
  all: revert s Hb Hs.
  all: induction Hsnb as [b Hbsteps IHb]; intros s Hb Hs.
  all: pose proof (reducible_sn _ _ Hs) as Hsns.
  all: revert Hs.
  all: induction Hsns as [s Hssteps IHs]; intros Hs.
  all: pose proof (reducible_lc _ _ Hb) as Hb_lc.
  all: pose proof (reducible_lc _ _ Hs) as Hs_lc.
  all: unfold locally_closed in *.
  all: apply reducible_back;
    [constructor; eauto using numeric_lc
    |apply nonvalue_rec| intros next Hstep].
  all: try (apply lc_succ; apply numeric_lc; exact Hnum).
  - inversion Hstep; subst;
      try solve [match goal with H : tm_zero --> _ |- _ => inversion H end].
    + eapply IHb; [eauto | eapply reducible_step; eauto | exact Hs].
    + eapply IHs; [eauto | eapply reducible_step; eauto].
    + exact Hb.
  - inversion Hstep; subst;
      try solve [match goal with H : tm_succ n --> _ |- _ =>
        exfalso; eapply numeric_no_step; [constructor; exact Hnum | exact H]
      end].
    + eapply IHb; [eauto | eapply reducible_step; eauto | exact Hs].
    + eapply IHs; [eauto | eapply reducible_step; eauto].
    + eapply reducible_app.
      * eapply reducible_app; [exact Hs | apply reducible_numeric; exact Hnum].
      * apply IHnum; auto.
Qed.

Lemma reducible_rec : forall n T b s,
  reducible Ty_Nat n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros n T b s Hn Hb Hs.
  pose proof (reducible_sn _ _ Hn) as Hsnn.
  revert T b s Hn Hb Hs.
  induction Hsnn as [n Hnsteps IHn]; intros T b s Hn Hb Hs.
  pose proof (reducible_sn _ _ Hb) as Hsnb.
  revert Hb s Hs.
  induction Hsnb as [b Hbsteps IHb]; intros Hb s Hs.
  pose proof (reducible_sn _ _ Hs) as Hsns.
  revert Hs.
  induction Hsns as [s Hssteps IHs]; intros Hs.
  pose proof (reducible_lc _ _ Hn) as Hn_lc.
  pose proof (reducible_lc _ _ Hb) as Hb_lc.
  pose proof (reducible_lc _ _ Hs) as Hs_lc.
  unfold locally_closed in *.
  apply reducible_back;
    [constructor; eauto | apply nonvalue_rec |].
  intros next Hstep. inversion Hstep; subst.
  - eapply IHn; [eauto | eapply reducible_step; eauto | exact Hb | exact Hs].
  - eapply IHb; [eauto | eapply reducible_step; eauto | exact Hs].
  - eapply IHs; [eauto | eapply reducible_step; eauto].
  - exact Hb.
  - eapply reducible_app.
    + eapply reducible_app; [exact Hs | apply reducible_numeric; eauto].
    + apply reducible_rec_numeral; auto.
Qed.

Lemma reducible_choice : forall T a b,
  reducible T a -> reducible T b -> reducible T (tm_choice a b).
Proof.
  intros T a b Ha Hb. apply reducible_back.
  - constructor; eapply reducible_lc; eauto.
  - apply nonvalue_choice.
  - intros t Hstep. inversion Hstep; subst; auto.
Qed.

Fixpoint subst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app f a => tm_app (subst rho f) (subst rho a)
  | tm_abs T body => tm_abs T (subst rho body)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ n => tm_succ (subst rho n)
  | tm_natrec n b s => tm_natrec (subst rho n) (subst rho b) (subst rho s)
  | tm_choice a b => tm_choice (subst rho a) (subst rho b)
  end.

Fixpoint free_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app f a => free_atoms f ++ free_atoms a
  | tm_abs _ body => free_atoms body
  | tm_true | tm_false | tm_zero => []
  | tm_succ n => free_atoms n
  | tm_natrec n b s => free_atoms n ++ free_atoms b ++ free_atoms s
  | tm_choice a b => free_atoms a ++ free_atoms b
  end.

Definition extend_subst (rho : atom -> tm) (x : atom) (v : tm) :=
  fun y => if Nat.eqb x y then v else rho y.

Lemma open_rec_lc_id : forall k t v,
  lc_at k t -> open_rec k v t = t.
Proof.
  intros k t. revert k.
  induction t; intros k v Hlc; simpl; inversion Hlc; subst; auto;
    try (f_equal; eauto; fail).
  destruct (Nat.eqb k n) eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - reflexivity.
Qed.

Lemma subst_open_fresh : forall t k rho x v,
  ~ In x (free_atoms t) ->
  (forall y, locally_closed (rho y)) ->
  subst (extend_subst rho x v) (open_rec k (tm_fvar x) t) =
  open_rec k v (subst rho t).
Proof.
  induction t; intros k rho x v Hfresh Hclosed; simpl in *; auto.
  - destruct (Nat.eqb k n); simpl; auto. unfold extend_subst.
    rewrite Nat.eqb_refl. reflexivity.
  - unfold extend_subst. destruct (Nat.eqb x a) eqn:E.
    apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. left; reflexivity.
    symmetry. apply open_rec_lc_id.
    eapply lc_weaken with (k:=0); [lia | apply Hclosed].
  - rewrite !in_app_iff in Hfresh. rewrite IHt1, IHt2; auto; tauto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - repeat rewrite in_app_iff in Hfresh.
    rewrite IHt1, IHt2, IHt3; auto; tauto.
  - rewrite in_app_iff in Hfresh. rewrite IHt1, IHt2; auto; tauto.
Qed.

Lemma subst_lc : forall k t rho,
  lc_at k t -> (forall x, locally_closed (rho x)) ->
  lc_at k (subst rho t).
Proof.
  intros k t rho Hlc. revert rho.
  induction Hlc; intros rho Hrho; simpl; eauto using lc_at.
  - eapply lc_weaken with (k:=0); [lia | apply Hrho].
Qed.

Lemma fresh_atom : forall (L : list atom), exists x, ~ In x L.
Proof.
  assert (Hbound : forall x L, In x L -> x <= fold_right Nat.max 0 L).
  { intros x L. induction L as [|a L IH]; simpl; intros Hmem.
    - contradiction.
    - destruct Hmem as [-> | Hmem].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [apply IH; exact Hmem | apply Nat.le_max_r]. }
  intros L. exists (S (fold_right Nat.max 0 L)).
  intros Hmem. pose proof (Hbound _ _ Hmem). lia.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Htyp. induction Htyp; unfold locally_closed in *;
    eauto using lc_at.
  - destruct (fresh_atom L) as [x Hfresh].
    apply lc_abs. eapply open_lc_inverse.
    apply H0. exact Hfresh.
Qed.

Definition env_valid (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x, locally_closed (rho x)) /\
  (forall x T, Gamma x = Some T -> reducible T (rho x)).

Lemma env_extend : forall Gamma rho x A v,
  env_valid Gamma rho -> reducible A v ->
  env_valid (update Gamma x A) (extend_subst rho x v).
Proof.
  intros Gamma rho x A v [Hclosed Htyped] Hval. split.
  - intros y. unfold extend_subst. destruct (Nat.eqb x y);
      [eapply reducible_lc; eauto | apply Hclosed].
  - intros y T Hlookup. unfold update in Hlookup.
    unfold extend_subst. destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst; auto.
    + eapply Htyped; eauto.
Qed.

Lemma reducible_abs : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall v, value v -> reducible A v -> reducible B (open body v)) ->
  reducible (Ty_Arrow A B) (tm_abs A body).
Proof.
  intros A B body Hlc Hbody. simpl. split; [exact Hlc|].
  split; [apply sn_value; constructor; exact Hlc|].
  intros v Hm Hv. rewrite <- (multi_value _ _ (v_abs _ _ Hlc) Hm).
  exists body. split; auto.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho, env_valid Gamma rho -> reducible T (subst rho t).
Proof.
  intros Gamma t T Htyp. induction Htyp; intros rho Henv; simpl.
  - destruct Henv as [_ Htyped]. eapply Htyped; eauto.
  - apply reducible_abs.
    + change (locally_closed (subst rho (tm_abs T1 t1))).
      eapply subst_lc;
        [eapply typing_lc; eapply T_Abs; exact H | exact (proj1 Henv)].
    + intros v Hv Hr.
      destruct (fresh_atom (L ++ free_atoms t1)) as [x Hfresh].
      assert (HnotL : ~ In x L).
      { intro Hin. apply Hfresh. apply in_or_app. left; exact Hin. }
      assert (HnotT : ~ In x (free_atoms t1)).
      { intro Hin. apply Hfresh. apply in_or_app. right; exact Hin. }
      specialize (H0 x HnotL (extend_subst rho x v)
        (env_extend _ _ _ _ _ Henv Hr)).
      unfold open in H0 |- *.
      rewrite <- (subst_open_fresh t1 0 rho x v HnotT (proj1 Henv)).
      exact H0.
  - eapply reducible_app; eauto.
  - exact (proj1 reducible_bool).
  - exact (proj2 reducible_bool).
  - exact reducible_zero.
  - apply reducible_succ; auto.
  - eapply reducible_rec; eauto.
  - eapply reducible_choice; eauto.
Qed.

Lemma subst_identity : forall t,
  subst (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; congruence. Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Htyp.
  pose (rho := fun x : atom => tm_fvar x).
  assert (Henv : env_valid empty rho).
  { split; [intros x; constructor|]. intros x U Hlookup.
    discriminate Hlookup. }
  pose proof (fundamental _ _ _ Htyp rho Henv) as Hr.
  assert (Hsubst : subst rho t = t) by apply subst_identity.
  rewrite Hsubst in Hr. eapply reducible_sn; eauto.
Qed.

End STLCNormalizationNondeterminismRecursionHardTask.
