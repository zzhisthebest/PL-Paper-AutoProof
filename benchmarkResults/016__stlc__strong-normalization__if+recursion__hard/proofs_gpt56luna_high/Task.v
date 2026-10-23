(** STLC CBV strong-normalization benchmark, Hard variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia Program.Equality.
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

(* The logical relation.  The extra field in the natural-number case is the
   usual (and very useful for System T) recursor closure condition. *)
Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool => True
  | Ty_Nat => True
  | Ty_Arrow A B =>
      forall u, reducible A u -> reducible B (tm_app t u)
  end.

Lemma sn_red : forall t, strongly_normalizing t ->
  forall t', t --> t' -> strongly_normalizing t'.
Proof.
  intros t H; inversion H; eauto.
Qed.

Lemma lc_at_weaken : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H; induction H; eauto; try constructor; lia.
Qed.

Lemma lc_open_rec : forall k u t,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k u t; revert k u.
  induction t as [i|x|t1 IH1|T t1 IH1| | | |t1 IH1|n b s IHn IHb IHs|t1 IH1 t2 IH2 t3 IH3];
    intros k u Ht Hu; simpl in *.
  - dependent destruction Ht; destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + constructor; apply Nat.eqb_neq in E; lia.
  - dependent destruction Ht; constructor.
  - dependent destruction Ht; constructor; eauto.
  - dependent destruction Ht; constructor. apply IH1; eauto using lc_at_weaken.
  - constructor.
  - constructor.
  - constructor.
  - dependent destruction Ht; constructor; eauto.
  - dependent destruction Ht; constructor; eauto.
  - dependent destruction Ht; constructor; eauto.
Qed.

Lemma numeric_lc : forall t, numeric_value t -> locally_closed t.
Proof.
  intros t H; induction H; unfold locally_closed; eauto.
Qed.

Lemma value_lc : forall t, value t -> locally_closed t.
Proof.
  intros t H; inversion H; subst; auto using numeric_lc; try (constructor; eauto).
Qed.

Lemma lc_abs_body : forall T t,
  locally_closed (tm_abs T t) -> lc_at 1 t.
Proof.
  intros T t H; inversion H; assumption.
Qed.

Lemma step_lc : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H; induction H; intro Hl; unfold locally_closed in *; simpl in *.
  - inversion Hl; unfold open; eapply lc_open_rec.
    + eauto using lc_abs_body.
    + eauto using value_lc.
  - inversion Hl; constructor; eauto.
  - inversion Hl; constructor; eauto.
  - inversion Hl; constructor; eauto.
  - inversion Hl; constructor; eauto.
  - inversion Hl; constructor; eauto.
  - inversion Hl; constructor; eauto.
  - inversion Hl; assumption.
  - inversion Hl; apply lc_app.
    + apply lc_app.
      * assumption.
      * match goal with
        | H : numeric_value ?x |- lc_at 0 ?x => exact (numeric_lc _ H)
        end.
    + apply lc_rec.
      * match goal with
        | H : numeric_value ?x |- lc_at 0 ?x => exact (numeric_lc _ H)
        end.
      * assumption.
      * assumption.
  - inversion Hl; eauto.
  - inversion Hl; eauto.
  - inversion Hl; constructor; eauto.
Qed.

Lemma red_lc : forall T t, reducible T t -> locally_closed t.
Proof.
  induction T as [| |A IHA B IHB]; intros t H; simpl in H; tauto.
Qed.

Lemma red_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof.
  induction T as [| |A IHA B IHB]; intros t H; simpl in H; tauto.
Qed.

Lemma reducible_red : forall T t, reducible T t ->
  forall t', t --> t' -> reducible T t'.
Proof.
  induction T as [| |A IHA B IHB]; intros t H t' Hstep.
  - destruct H as [Hl [Hsn _]]. simpl. split.
    + exact (step_lc _ _ Hstep Hl).
    + split.
      * exact (sn_red _ Hsn _ Hstep).
      * exact I.
  - destruct H as [Hl [Hsn _]]. simpl. split.
    + exact (step_lc _ _ Hstep Hl).
    + split.
      * exact (sn_red _ Hsn _ Hstep).
      * exact I.
  - destruct H as [Hl [Hsn Hfun]]. simpl. split.
    + exact (step_lc _ _ Hstep Hl).
    + split.
      * exact (sn_red _ Hsn _ Hstep).
      * intros u Hu.
        eapply IHB with (t := tm_app t u).
        -- apply Hfun; exact Hu.
        -- apply ST_App1; [exact Hstep | exact (red_lc _ _ Hu)].
Qed.

Lemma no_numeric_app : forall t u, ~ numeric_value (tm_app t u).
Proof.
  intros t u H; remember (tm_app t u) as q eqn:E.
  induction H; inversion E.
Qed.

Lemma no_value_app : forall t u, ~ value (tm_app t u).
Proof.
  intros t u H; remember (tm_app t u) as q eqn:E.
  induction H; inversion E; eauto using no_numeric_app.
  all: rewrite H0 in H; exact (no_numeric_app _ _ H).
Qed.

Lemma red_neutral : forall T t, locally_closed t ->
  (forall t', t --> t' -> reducible T t') ->
  ~ value t -> reducible T t.
Proof.
  induction T as [| |A IHA B IHB]; intros t Hl Hred Hnv; simpl.
  - split; [exact Hl|split].
    + constructor; intros t' Hs; exact (red_sn _ _ (Hred t' Hs)).
    + constructor.
  - split; [exact Hl|split].
    + constructor; intros t' Hs; exact (red_sn _ _ (Hred t' Hs)).
    + constructor.
  - split; [exact Hl|split].
    + constructor; intros t' Hs; exact (red_sn _ _ (Hred t' Hs)).
    + intros u Hu.
      apply IHB with (t := tm_app t u).
      * apply lc_app; [exact Hl | exact (red_lc _ _ Hu)].
      * intros z Hz; inversion Hz;
          [ exfalso; apply Hnv; rewrite <- H; constructor; assumption
          | eapply Hred; eauto
          | exfalso; apply Hnv; assumption ].
      * intros Hv; exact (no_value_app _ _ Hv).
Qed.

Lemma no_numeric_natrec : forall n b s, ~ numeric_value (tm_natrec n b s).
Proof.
  intros n b s H; remember (tm_natrec n b s) as q eqn:E.
  induction H; inversion E.
Qed.

Lemma natrec_not_value : forall n b s, ~ value (tm_natrec n b s).
Proof.
  intros n b s H; remember (tm_natrec n b s) as q eqn:E.
  induction H; inversion E.
  all: rewrite E in H; exact (no_numeric_natrec _ _ _ H).
Qed.

Lemma no_step_zero : forall t, ~ (tm_zero --> t).
Proof.
  intros t H; remember tm_zero as q eqn:E.
  induction H; inversion E.
Qed.

Lemma numeric_no_step : forall n, numeric_value n ->
  forall n', ~ (n --> n').
Proof.
  intros n H; induction H as [|n H IH].
  - intros n' Hs; eapply no_step_zero; eassumption.
  - intros n' Hs; inversion Hs.
    eapply (IH _ H1); eassumption.
Qed.

Lemma red_rec_zero : forall T b s, reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec tm_zero b s).
Proof.
  intros T b s Hb Hs.
  assert (Z : forall b0, strongly_normalizing b0 ->
      reducible T b0 ->
      forall s0, reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 ->
      reducible T (tm_natrec tm_zero b0 s0)).
  { intros b0 Hb0.
    induction Hb0 as [b0 Hbnext0 IHb].
    intros Hb0r s0 Hs0.
    pose proof Hs0 as Hskeep.
    destruct Hs0 as [Ls0 [HsnS0 HfunS0]].
    induction HsnS0 as [s0 HnextS0 IHs].
    apply red_neutral.
    - apply lc_rec; [constructor | exact (red_lc _ _ Hb0r) | exact Ls0].
    - intros z Hz; inversion Hz; subst.
      + exfalso; eapply no_step_zero; eassumption.
      + eapply IHb; eauto using reducible_red, Hskeep.
      + pose proof (reducible_red _ _ Hskeep _ H5) as Hs'.
        destruct Hs' as [Ls' [SNs' FunS']].
        eapply IHs; [exact H5 | exact Ls' | exact FunS' |
          exact (conj Ls' (conj SNs' FunS'))].
      + eauto using Hb0r.
    - apply natrec_not_value.
  }
  apply Z; [exact (red_sn _ _ Hb) | exact Hb | exact Hs].
Qed.

Lemma sn_numeric : forall n, numeric_value n -> strongly_normalizing n.
Proof.
  intros n H; constructor; intros t Ht; exfalso;
    eapply (numeric_no_step n H t); exact Ht.
Qed.

Lemma red_rec_numeric : forall T n, numeric_value n -> forall b s,
  reducible T b -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n Hn; induction Hn as [|n Hn IHn].
  - intros b s Hb Hs; exact (red_rec_zero T b s Hb Hs).
  - intros b s Hb Hs.
    assert (Sg : forall b0, strongly_normalizing b0 -> reducible T b0 ->
        forall s0, strongly_normalizing s0 ->
        reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 ->
        reducible T (tm_natrec (tm_succ n) b0 s0)).
    { intros b0 Hb0 Hb0r.
      induction Hb0 as [b0 Hbnext0 IHb].
      intros s0 Hs0sn Hs0r.
      pose proof Hs0r as Hskeep.
      destruct Hs0r as [Ls0 [HsnS0 HfunS0]].
      induction Hs0sn as [s0 HnextS0 IHs].
      apply red_neutral.
      - apply lc_rec; [constructor; exact (numeric_lc _ Hn) |
          exact (red_lc _ _ Hb0r) | exact Ls0].
      - intros z Hz; inversion Hz; subst.
        + exfalso; apply (numeric_no_step _ (nv_succ _ Hn) n'); assumption.
        + eapply IHb.
          all: eauto using reducible_red, red_sn, Hskeep.
        + pose proof (reducible_red _ _ Hskeep _ H5) as Hsr.
          destruct Hsr as [Lsr [SNsr FunSr]].
          eapply IHs; [exact H5 | exact Lsr | exact SNsr | exact FunSr |
            exact (conj Lsr (conj SNsr FunSr))].
        + pose proof (IHn b0 s0 Hb0r Hskeep) as Hrec.
          pose proof (HfunS0 n (conj (numeric_lc _ Hn)
            (conj (sn_numeric _ Hn) I))) as Hsnapp.
          exact (proj2 (proj2 Hsnapp) _ Hrec).
      - apply natrec_not_value.
    }
    apply Sg; [exact (red_sn _ _ Hb) | exact Hb |
      exact (red_sn _ _ Hs) | exact Hs].
Qed.

Lemma numeric_or_not : forall n, numeric_value n \/ ~ numeric_value n.
Proof.
  intro q; induction q as [i|x|q1 IH|U q1 IH| | | |q1 IH|q1 q2 q3 IH1 IH2 IH3|q1 q2 q3 IH1 IH2 IH3].
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - left; constructor.
  - destruct IH as [Hn|Hn].
    + left; constructor; exact Hn.
    + right; intro H; inversion H; contradiction.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
Qed.

Lemma red_rec : forall T n b s, reducible Ty_Nat n ->
  reducible T b -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n b s Hn Hb Hs.
  assert (R : forall q, locally_closed q -> strongly_normalizing q -> forall b0 s0,
      reducible T b0 -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 ->
      reducible T (tm_natrec q b0 s0)).
  { intros q Lq Hq; induction Hq as [q Hnext IHq].
    intros b0 s0 Hb0 Hs0.
    destruct (numeric_or_not q) as [Hnum|Hnum].
    - apply red_rec_numeric with (n := q).
      + exact Hnum.
      + exact Hb0.
      + exact Hs0.
    - apply red_neutral.
      + apply lc_rec; [exact Lq | exact (red_lc _ _ Hb0) |
          exact (red_lc _ _ Hs0)].
      + intros z Hz; inversion Hz; subst.
        * apply IHq with (t' := n').
          exact H2.
          exact (step_lc _ _ H2 Lq).
          exact Hb0.
          exact Hs0.
        * exfalso; apply Hnum; assumption.
        * exfalso; apply Hnum; assumption.
        * exfalso; apply Hnum; constructor.
        * exfalso; apply Hnum; constructor; assumption.
      + apply natrec_not_value.
  }
  apply R; [exact (red_lc _ _ Hn) | exact (red_sn _ _ Hn) | exact Hb | exact Hs].
Qed.

Fixpoint subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (subst sigma t1)
  | tm_natrec n b s => tm_natrec (subst sigma n) (subst sigma b) (subst sigma s)
  | tm_if t1 t2 t3 => tm_if (subst sigma t1) (subst sigma t2) (subst sigma t3)
  end.

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

Fixpoint list_sum (l : list nat) : nat :=
  match l with [] => 0 | x :: l => x + list_sum l end.

Definition fresh (l : list atom) : atom := S (list_sum l).

Lemma fresh_not_in : forall l, ~ In (fresh l) l.
Proof.
  intro l; unfold fresh.
  assert (M : forall y, In y l -> y <= list_sum l).
  { induction l as [|z l IH]; simpl.
    - contradiction.
    - intros y H; destruct H as [<-|H].
      + lia.
      + apply IH in H; unfold list_sum in *; lia. }
  intro H; apply M in H; lia.
Qed.

Lemma lc_at_mono : forall j k t, j <= k -> lc_at j t -> lc_at k t.
Proof.
  intros j k t Hjk Hj; induction Hjk; auto using lc_at_weaken.
Qed.

Lemma open_rec_no_hit : forall k u v,
  lc_at k v -> open_rec k u v = v.
Proof.
  intros k u v H; induction H; simpl.
  - destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
  - reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

Lemma lc_open_rec_inv : forall k t u,
  lc_at k u -> lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k t u Hu H; revert k u Hu H.
  induction t as [i|x|t1 IH1 t2 IH2|U t1 IH1| | | |t1 IH1|n IHn b IHb s IHs|t1 IH1 t2 IH2 t3 IH3];
    intros k u Hu H; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + constructor; apply Nat.eqb_eq in E; lia.
    + dependent destruction H; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - dependent destruction H; apply lc_app.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - dependent destruction H; constructor; apply IH1; [exact (lc_at_weaken k u Hu) | assumption].
  - constructor.
  - constructor.
  - constructor.
  - dependent destruction H; constructor; apply IH1; assumption.
  - dependent destruction H; constructor; [apply IHn | apply IHb | apply IHs]; assumption.
  - dependent destruction H; constructor; [apply IH1 | apply IH2 | apply IH3]; assumption.
Qed.

Lemma subst_lc_open : forall k u v,
  lc_at 0 v -> open_rec k u v = v.
Proof.
  intros k u v H.
  assert (M : lc_at k v).
  { apply lc_at_mono with (j := 0); [exact (Nat.le_0_l k) | exact H]. }
  exact (open_rec_no_hit k u v M).
Qed.

Lemma subst_open_rec : forall k t u sigma x,
  ~ In x (fv t) -> locally_closed u ->
  (forall y, locally_closed (sigma y)) ->
  subst (fun y => if Nat.eqb x y then u else sigma y)
    (open_rec k (tm_fvar x) t) =
  open_rec k u (subst sigma t).
Proof.
  intros k t u sigma x Hfresh HLu Hsigma; revert k u sigma x Hfresh HLu Hsigma.
  induction t as [i|y|t1 IH1 t2 IH2|U t1 IH1| | | |t1 IH1|n IHn b IHb s IHs|t1 IH1 t2 IH2 t3 IH3];
    intros k u sigma x Hfresh HLu Hsigma; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + simpl; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + exfalso; apply Hfresh; simpl; left; apply Nat.eqb_eq in E; symmetry; exact E.
    + simpl; symmetry; apply subst_lc_open; exact (Hsigma y).
  - f_equal.
    + apply IH1; simpl in *; intuition.
    + apply IH2; simpl in *; intuition.
  - f_equal; apply IH1; simpl in *; intuition.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal; apply IH1; simpl in *; intuition.
  - f_equal.
    + apply IHn.
      * intro HIn; apply Hfresh; apply in_or_app; left; exact HIn.
      * exact HLu.
      * exact Hsigma.
    + apply IHb.
      * intro HIn; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact HIn.
      * exact HLu.
      * exact Hsigma.
    + apply IHs.
      * intro HIn; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact HIn.
      * exact HLu.
      * exact Hsigma.
  - f_equal.
    + apply IH1.
      * intro HIn; apply Hfresh; apply in_or_app; left; exact HIn.
      * exact HLu.
      * exact Hsigma.
    + apply IH2.
      * intro HIn; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact HIn.
      * exact HLu.
      * exact Hsigma.
    + apply IH3.
      * intro HIn; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact HIn.
      * exact HLu.
      * exact Hsigma.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End STLCNormalizationIfRecursionHardTask.
