Require Import Rules.

Set Implicit Arguments.

Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export Coq.micromega.Lia.

Notation empty_menv := (@nil (nat * nat)).

From Stdlib Require Import Lists.List Arith.Wf_nat Sorting.Permutation.
Import ListNotations.

Definition bind_type (b : binding) :=
  match b with bind_sub T | bind_typ T => T end.

Fixpoint sub_lookup (E : env) (x : atom) : option typ :=
  match E with
  | [] => None
  | (y,b) :: F =>
      if x == y then
        match b with bind_sub T => Some T | bind_typ _ => None end
      else sub_lookup F x
  end.

Lemma sub_lookup_binds E x T :
  sub_lookup E x = Some T -> binds x (bind_sub T) E.
Proof.
  induction E as [|[y b] E IH]; simpl; try discriminate.
  destruct (x == y) as [->|N].
  - destruct b; intro H; inversion H; subst; apply binds_cons_iff; auto.
  - intro H; apply binds_cons, IH, H.
Qed.

Lemma binds_sub_lookup E x T :
  uniq E -> binds x (bind_sub T) E -> sub_lookup E x = Some T.
Proof.
  induction E as [|[y b] E IH]; intros U H.
  - inversion H.
  - apply binds_cons_uniq_iff in H as [[-> [<- _]]|[H N]]; auto.
    + simpl. destruct (y == y); congruence.
    + simpl. destruct (x == y); [congruence|].
      apply IH; [inversion U; auto|assumption].
Qed.

Fixpoint names (T : typ) : atoms :=
  match T with
  | typ_fvar x => {{x}}
  | typ_arrow A B | typ_all A B => names A `union` names B
  | typ_mu A => names A
  | typ_label x A => {{x}} `union` names A
  | typ_rcd_cons x A B => {{x}} `union` (names A `union` names B)
  | _ => {}
  end.

Fixpoint env_names (E : env) : atoms :=
  match E with
  | [] => {}
  | (x,b) :: F => {{x}} `union` (names (bind_type b) `union` env_names F)
  end.

Lemma dom_env_names E : dom E [<=] env_names E.
Proof.
  induction E as [|[x b] E IH]; simpl; intros y H.
  - fsetdec.
  - assert (y = x \/ y `in` dom E) as [->|Ht] by fsetdec; [fsetdec|].
    specialize (IH _ Ht); fsetdec.
Qed.

Definition is_record (T : typ) : bool :=
  match T with typ_rcd_nil | typ_rcd_cons _ _ _ => true | _ => false end.

Lemma is_record_spec T : is_record T = true <-> rt_type T.
Proof. split; [destruct T; simpl; try discriminate; constructor|destruct 1; reflexivity]. Qed.

Definition has_sub E x :=
  match sub_lookup E x with Some _ => true | None => false end.

(* At depth d, the d innermost bound indices are in scope. The free
   variable test records which environment entries bind type variables. *)
Fixpoint valid (d : nat) (free : atom -> bool) (T : typ) : bool :=
  match T with
  | typ_bvar n => Nat.ltb n d
  | typ_fvar x => free x
  | typ_arrow A B => valid d free A && valid d free B
  | typ_all A B => valid d free A && valid (S d) free B
  | typ_mu A => valid (S d) free A
  | typ_label _ A => valid d free A
  | typ_rcd_cons x A B =>
      valid d free A && valid d free B && is_record B &&
        negb (AtomSetImpl.mem x (collectLabel B))
  | _ => true
  end.

Definition add_var (free : atom -> bool) (x y : atom) :=
  if y == x then true else free y.

Lemma has_sub_cons E x U y :
  has_sub ((x,bind_sub U)::E) y = add_var (has_sub E) x y.
Proof. unfold has_sub, add_var; simpl; destruct (y == x); reflexivity. Qed.

Lemma valid_mono T d e f :
  d <= e -> valid d f T = true -> valid e f T = true.
Proof.
  revert d e. induction T; simpl; intros d e H V; try assumption.
  - apply Nat.ltb_lt in V; apply Nat.ltb_lt; lia.
  - apply Bool.andb_true_iff in V as [V1 V2].
    apply Bool.andb_true_iff; eauto.
  - apply Bool.andb_true_iff in V as [V1 V2].
    apply Bool.andb_true_iff; split; eauto with arith.
  - eauto with arith.
  - eauto.
  - repeat rewrite Bool.andb_true_iff in *. intuition eauto.
Qed.

Lemma open_record_shape T U k :
  is_record U = false ->
  is_record (open_tt_rec k U T) = is_record T.
Proof. destruct T; simpl; auto; destruct (k === n); auto. Qed.

Lemma not_record_labels U : is_record U = false -> collectLabel U = {}.
Proof. destruct U; simpl; congruence. Qed.

Lemma open_record_labels T U k :
  is_record U = false ->
  collectLabel (open_tt_rec k U T) = collectLabel T.
Proof.
  revert k. induction T; simpl; intros k H; auto.
  - destruct (k === n); simpl; auto using not_record_labels.
  - now rewrite IHT2.
Qed.

Lemma valid_open T U f g k :
  is_record U = false ->
  valid 0 g U = true ->
  (forall x, x `in` names T -> f x = g x) ->
  valid k g (open_tt_rec k U T) = valid (S k) f T.
Proof.
  intros R V. revert k. induction T; simpl; intros k H; try reflexivity.
  - destruct (k === n) as [->|N].
    + rewrite (@valid_mono U 0 n g) by (auto; lia).
      symmetry; apply Nat.ltb_lt; lia.
    + change ((n <? k)%nat = (n <? S k)%nat).
      apply Bool.eq_true_iff_eq. repeat rewrite Nat.ltb_lt. lia.
  - symmetry; apply H; fsetdec.
  - rewrite IHT1, IHT2; [reflexivity|intros; apply H; fsetdec..].
  - rewrite IHT1, IHT2; [reflexivity|intros; apply H; fsetdec..].
  - apply IHT; exact H.
  - apply IHT; intros; apply H; fsetdec.
  - rewrite open_record_shape, open_record_labels by exact R.
    rewrite IHT1, IHT2; [reflexivity|intros; apply H; fsetdec..].
Qed.

Lemma valid_open_var E U T x :
  x `notin` names T ->
  valid 0 (has_sub ((x,bind_sub U)::E)) (open_tt T x) =
  valid 1 (has_sub E) T.
Proof.
  intro N. unfold open_tt. apply valid_open; simpl; auto.
  - rewrite has_sub_cons. unfold add_var. destruct (x == x); congruence.
  - intros y H; rewrite has_sub_cons. unfold add_var.
    destruct (y == x); subst; [contradiction|reflexivity].
Qed.

Lemma wf_env_uniq E : wf_env E -> uniq E.
Proof. induction 1; constructor; auto. Qed.

Lemma WF_valid E T :
  WF E T -> uniq E -> valid 0 (has_sub E) T = true.
Proof.

  intros H. induction H as
    [| | U E x Hbind | E A B HA IHA HB IHB
     | L E A B HA IHA HB IHB
     | L E A HA IHA HB IHB
     | E A x HA IHA | | E x A B HA IHA HB IHB R N];
    intro Uq; simpl; try reflexivity.
  - unfold has_sub. rewrite (@binds_sub_lookup E x U Uq Hbind); reflexivity.
  - rewrite IHA, IHB; auto.
  - rewrite IHA by exact Uq. simpl.
    destruct (atom_fresh (L `union` (dom E `union` names B))) as [x Fr].
    rewrite <- (@valid_open_var E A B x) by fsetdec.
    apply IHB; [fsetdec|constructor; [exact Uq|fsetdec]].
  - destruct (atom_fresh (L `union` (dom E `union` names A))) as [x Fr].
    rewrite <- (@valid_open_var E typ_top A x) by fsetdec.
    apply IHA; [fsetdec|constructor; [exact Uq|fsetdec]].
  - auto.
  - rewrite IHA, IHB, (proj2 (is_record_spec B) R) by exact Uq.
    destruct (AtomSetImpl.mem x (collectLabel B)) eqn:M; simpl; auto.
    apply AtomSetImpl.mem_2 in M; contradiction.
Qed.

(* A variable is charged for promoting to its bound. The recursive case
   charges for comparing the unfolded bodies, with a single labeled copy
   whose recursive variable is bounded by Top. *)
Definition push (v : nat) (s : nat -> nat) (i : nat) :=
  match i with 0 => v | S j => s j end.

Fixpoint cost (w : atom -> nat) (s : nat -> nat) (T : typ) : nat :=
  match T with
  | typ_bvar i => s i
  | typ_fvar x => w x
  | typ_arrow A B => S (Nat.max (cost w s A) (cost w s B))
  | typ_all A B =>
      let a := cost w s A in
      S (Nat.max a (cost w (push (S a) s) B))
  | typ_mu A =>
      S (cost w (push (S (cost w (push 2 s) A)) s) A)
  | typ_label _ A => S (cost w s A)
  | typ_rcd_cons _ A B => S (cost w s A) + cost w s B
  | _ => 1
  end.

Definition zero_slots (_ : nat) := 0.
Definition weight w T := cost w zero_slots T.

Definition set_weight (w : atom -> nat) (x : atom) (v : nat) (y : atom) :=
  if y == x then v else w y.

Lemma cost_scoped T w s t d f :
  valid d f T = true ->
  (forall i, i < d -> s i = t i) ->
  cost w s T = cost w t T.
Proof.
  revert s t d. induction T; simpl; intros s t d V H; try reflexivity.
  - apply H, Nat.ltb_lt, V.
  - apply Bool.andb_true_iff in V as [VA VB].
    now rewrite (IHT1 _ _ _ VA H), (IHT2 _ _ _ VB H).
  - apply Bool.andb_true_iff in V as [VA VB].
    rewrite (IHT1 _ _ _ VA H).
    rewrite (IHT2 (push (S (cost w t T1)) s) (push (S (cost w t T1)) t) _ VB);
      [reflexivity|].
    intros [|i] Hi; simpl; auto with arith.
  - assert (P : forall v i, i < S d -> push v s i = push v t i).
    { intros v [|i] Hi; simpl; auto with arith. }
    rewrite (IHT _ _ _ V (P 2)).
    rewrite (IHT _ _ _ V (P _)); reflexivity.
  - now rewrite (IHT _ _ _ V H).
  - repeat rewrite Bool.andb_true_iff in V.
    destruct V as [[[VA VB] _] _].
    now rewrite (IHT1 _ _ _ VA H), (IHT2 _ _ _ VB H).
Qed.

Lemma cost_closed T f w s :
  valid 0 f T = true -> cost w s T = weight w T.
Proof. intro V; eapply cost_scoped; [exact V|intros; lia]. Qed.

Lemma cost_open T U f g v k s t :
  (forall x, x `in` names T -> f x = g x) ->
  (forall r, cost g r U = v) ->
  (forall i, t i = if k === i then v else s i) ->
  cost g s (open_tt_rec k U T) = cost f t T.
Proof.
  revert k s t. induction T; simpl; intros k s t F V H; try reflexivity.
  - rewrite H. destruct (k === n); auto.
  - symmetry; apply F; fsetdec.
  - rewrite IHT1 with (t := t), IHT2 with (t := t); auto; intros; apply F; fsetdec.
  - rewrite IHT1 with (t := t) by (auto; intros; apply F; fsetdec).
    rewrite IHT2 with (t := push (S (cost f t T1)) t); auto.
    + intros [|i]; [reflexivity|].
      specialize (H i).
      destruct (S k === S i), (k === i); simpl in *; congruence.
  - assert (P : forall a i, push a t i = if S k === i then v else push a s i).
    { intros a [|i]; [reflexivity|].
      specialize (H i).
      destruct (S k === S i), (k === i); simpl in *; congruence. }
    rewrite IHT with (s := push 2 s) (t := push 2 t) by (auto; intros; apply P).
    rewrite IHT with (t := push (S (cost f (push 2 t) T)) t) by (auto; intros; apply P).
    reflexivity.
  - rewrite IHT with (t := t); auto; intros; apply F; fsetdec.
  - rewrite IHT1 with (t := t), IHT2 with (t := t); auto; intros; apply F; fsetdec.
Qed.

Lemma weight_open_var T w x v :
  x `notin` names T ->
  weight (set_weight w x v) (open_tt T x) = cost w (push v zero_slots) T.
Proof.
  intro N. unfold weight, open_tt.
  apply cost_open with (v := v).
  - intros y H. unfold set_weight; destruct (y == x); subst; [contradiction|reflexivity].
  - intro; simpl; unfold set_weight. destruct (x == x); congruence.
  - intros [|i]; reflexivity.
Qed.

Lemma weight_open_rec T w x :
  x `notin` names T ->
  valid 0 (fun _ => true) (open_tt T x) = true ->
  weight (set_weight w x 2) (open_tt T (typ_label x (open_tt T x))) =
    cost w (push (S (cost w (push 2 zero_slots) T)) zero_slots) T.
Proof.
  intros N V. unfold weight at 1; unfold open_tt at 1.
  apply cost_open with (v := S (cost w (push 2 zero_slots) T)).
  - intros y H. unfold set_weight; destruct (y == x); subst; [contradiction|reflexivity].
  - intro r; simpl. rewrite (@cost_closed (open_tt T x) _ _ r V).
    now rewrite weight_open_var.
  - intros [|i]; reflexivity.
Qed.

Lemma valid_allow_all T d f :
  valid d f T = true -> valid d (fun _ => true) T = true.
Proof.
  revert d. induction T; simpl; intros d H; auto.
  all: repeat rewrite Bool.andb_true_iff in *; intuition eauto.
Qed.

Lemma wf_open_rec_valid E T x :
  x `notin` names T ->
  valid 1 (has_sub E) T = true ->
  valid 0 (has_sub ((x,bind_sub typ_top)::E))
    (open_tt T (typ_label x (open_tt T x))) = true.
Proof.
  intros N H. pose proof (@valid_open_var E typ_top T x N) as V.
  unfold open_tt at 1. rewrite valid_open with (f := has_sub E); auto.
  - now simpl; rewrite V.
  - intros y Hy. rewrite has_sub_cons. unfold add_var.
    destruct (y == x); subst; [contradiction|reflexivity].
Qed.

Lemma set_weight_const x : forall y,
  set_weight (fun _ => 2) x 2 y = 2.
Proof. intro y; unfold set_weight; destruct (y == x); reflexivity. Qed.

Lemma cost_ext_weight T w w' s :
  (forall x, w x = w' x) -> cost w s T = cost w' s T.
Proof.
  revert s. induction T; intro s; intro H; simpl; try reflexivity; auto;
    repeat rewrite IHT1; repeat rewrite IHT2; repeat rewrite IHT; auto.
Qed.


Lemma cost_mono_slots T w s t :
  (forall i, s i <= t i) -> cost w s T <= cost w t T.
Proof.
  revert s t. induction T; simpl; intros s t P; try solve [auto | lia].
  - specialize (IHT1 s t P); specialize (IHT2 s t P); lia.
  - pose proof (IHT1 s t P) as P1.
    assert (forall i, push (S (cost w s T1)) s i <=
                      push (S (cost w t T1)) t i) as Push.
    { intros [|i]; simpl; auto with arith. }
    specialize (IHT2 _ _ Push); lia.
  - assert (forall a b, a <= b -> forall i, push a s i <= push b t i) as Push.
    { intros a b D [|i]; simpl; auto. }
    pose proof (IHT _ _ (Push 2 2 (Nat.le_refl _))) as P1.
    specialize (IHT _ _ (Push _ _ (le_n_S _ _ P1))); lia.
  - specialize (IHT s t P); lia.
  - specialize (IHT1 s t P); specialize (IHT2 s t P); lia.
Qed.

Lemma cost_positive T d f w s :
  valid d f T = true ->
  (forall i, i < d -> 0 < s i) ->
  (forall x, 0 < w x) ->
  0 < cost w s T.
Proof.
  destruct T; simpl; intros V P Q; try lia; auto.
  apply P, Nat.ltb_lt, V.
Qed.

Lemma valid_WF E T : valid 0 (has_sub E) T = true -> WF E T.
Proof.
  remember (weight (fun _ => 2) T) as n eqn:M.
  revert E T M.
  induction n using lt_wf_ind; intros E T M V.
  assert (IH : forall U F, weight (fun _ => 2) U < n ->
                valid 0 (has_sub F) U = true -> WF F U).
  { intros. eapply H; eauto. }
  destruct T; simpl in V; try (constructor; fail); try discriminate.
  - unfold has_sub in V. destruct (sub_lookup E a) eqn:L; try discriminate.
    eapply WF_var, sub_lookup_binds; eauto.
  - apply Bool.andb_true_iff in V as [VA VB].
    constructor; eapply IH; eauto; unfold weight in *; simpl in M; lia.
  - apply Bool.andb_true_iff in V as [VA VB].
    eapply WF_all with (L := names T2).
    + eapply IH; eauto. unfold weight in *; simpl in M; lia.
    + intros x N. eapply IH.
      * unfold weight. rewrite <- (cost_ext_weight (open_tt T2 x) _ _ zero_slots (set_weight_const x)).
        change (weight (set_weight (fun _ => 2) x 2) (open_tt T2 x) < n).
        rewrite weight_open_var by exact N.
        unfold weight in M; simpl in M.
        assert (0 < cost (fun _ => 2) zero_slots T1) as P.
        { eapply cost_positive; [exact VA|intros; lia|intros; lia]. }
        assert (forall i, push 2 zero_slots i <=
            push (S (cost (fun _ => 2) zero_slots T1)) zero_slots i) as C.
        { intros [|i]; simpl; auto with arith. }
        pose proof (@cost_mono_slots T2 (fun _ => 2) _ _ C); lia.
      * change (valid 0 (has_sub ((x,bind_sub T1)::E)) (open_tt T2 x) = true).
        now rewrite valid_open_var.
  - eapply WF_rec with (L := names T).
    + intros x N. eapply IH.
      * unfold weight. rewrite <- (cost_ext_weight (open_tt T x) _ _ zero_slots (set_weight_const x)).
        change (weight (set_weight (fun _ => 2) x 2) (open_tt T x) < n).
        rewrite weight_open_var by exact N.
        unfold weight in M; simpl in M.
        assert (0 < cost (fun _ => 2) (push 2 zero_slots) T) as P.
        { eapply cost_positive; [exact V| |intros; lia].
          intros [|i] Hi; simpl; lia. }
        assert (forall i, push 2 zero_slots i <=
            push (S (cost (fun _ => 2) (push 2 zero_slots) T)) zero_slots i) as C.
        { intros [|i]; simpl; auto with arith. }
        pose proof (@cost_mono_slots T (fun _ => 2) _ _ C); lia.
      * change (valid 0 (has_sub ((x,bind_sub typ_top)::E)) (open_tt T x) = true).
        now rewrite valid_open_var.
    + intros x N. eapply IH.
      * unfold weight. rewrite <- (cost_ext_weight (open_tt T (typ_label x (open_tt T x))) _ _ zero_slots
                    (set_weight_const x)).
        change (weight (set_weight (fun _ => 2) x 2)
          (open_tt T (typ_label x (open_tt T x))) < n).
        rewrite weight_open_rec; [unfold weight in M; simpl in M; lia|assumption|].
        eapply valid_allow_all. rewrite (@valid_open_var E typ_top T x N); exact V.
      * now apply wf_open_rec_valid.
  - constructor. eapply IH; eauto. unfold weight in *; simpl in M; lia.
  - repeat rewrite Bool.andb_true_iff in V.
    destruct V as [[[VA VB] R] N].
    constructor.
    + eapply IH; eauto. unfold weight in *; simpl in M; lia.
    + eapply IH; eauto. unfold weight in *; simpl in M; lia.
    + now apply is_record_spec.
    + intro C. apply AtomSetImpl.mem_1 in C. now rewrite C in N.
Qed.

Definition WF_dec E T (U : uniq E) : {WF E T} + {~ WF E T}.
Proof.
  destruct (valid 0 (has_sub E) T) eqn:V.
  - left; now apply valid_WF.
  - right; intro W; now rewrite (WF_valid W U) in V.
Defined.

Fixpoint wf_env_dec (E : env) : {wf_env E} + {~ wf_env E}.
Proof.
  destruct E as [|[x b] E].
  - left; constructor.
  - destruct (wf_env_dec E) as [W|N]; [|right; inversion 1; contradiction].
    destruct (AtomSetImpl.mem x (dom E)) eqn:M.
    + right; intro H. apply AtomSetImpl.mem_2 in M. inversion H; contradiction.
    + assert (D : x `notin` dom E).
      { intro H; apply AtomSetImpl.mem_1 in H; congruence. }
      destruct (WF_dec (bind_type b) (wf_env_uniq W)) as [V|V].
      * destruct b; left; constructor; assumption.
      * right; destruct b; inversion 1; apply V; assumption.
Defined.

(* Swapping two fresh atoms transports a binder premise to any other
   fresh choice, including the labels introduced by recursive opening. *)
Fixpoint rename (p : atom -> atom) (T : typ) : typ :=
  match T with
  | typ_fvar x => typ_fvar (p x)
  | typ_arrow A B => typ_arrow (rename p A) (rename p B)
  | typ_all A B => typ_all (rename p A) (rename p B)
  | typ_mu A => typ_mu (rename p A)
  | typ_label x A => typ_label (p x) (rename p A)
  | typ_rcd_cons x A B => typ_rcd_cons (p x) (rename p A) (rename p B)
  | _ => T
  end.

Definition rename_binding p b :=
  match b with
  | bind_sub T => bind_sub (rename p T)
  | bind_typ T => bind_typ (rename p T)
  end.

Definition rename_env p (E : env) : env :=
  List.map (fun xb => (p (fst xb), rename_binding p (snd xb))) E.

Lemma rename_id p T :
  (forall x, x `in` names T -> p x = x) ->
  rename p T = T.
Proof.
  induction T; simpl; intro H; try reflexivity; f_equal;
    auto; try (apply H; fsetdec); apply IHT || apply IHT1 || apply IHT2;
    intros; apply H; fsetdec.
Qed.

Lemma rename_env_id p E :
  (forall x, x `in` env_names E -> p x = x) ->
  rename_env p E = E.
Proof.
  induction E as [|[x b] E IH]; simpl; intro H; auto.
  rewrite IH by (intros; apply H; fsetdec).
  rewrite (H x) by fsetdec.
  destruct b as [T|T]; simpl in *;
    rewrite (rename_id p T) by (intros; apply H; fsetdec); reflexivity.
Qed.

Lemma rename_open_rec p T U k :
  rename p (open_tt_rec k U T) = open_tt_rec k (rename p U) (rename p T).
Proof.
  revert k. induction T; intro k; simpl; try reflexivity;
    try (destruct (k === n); reflexivity);
    now rewrite ?IHT, ?IHT1, ?IHT2.
Qed.

Lemma rename_open p T U :
  rename p (open_tt T U) = open_tt (rename p T) (rename p U).
Proof. apply rename_open_rec. Qed.

Lemma rename_binds p E x b :
  binds x b E -> binds (p x) (rename_binding p b) (rename_env p E).
Proof.
  induction E as [|[y c] E IH]; intro H; [inversion H|].
  apply binds_cons_iff in H as [[-> ->]|H]; simpl.
  - apply binds_cons_iff; auto.
  - apply binds_cons, IH, H.
Qed.

Section InvolutiveRenaming.
Variable p : atom -> atom.
Hypothesis inv : forall x, p (p x) = x.

Lemma rename_inj x y : p x = p y -> x = y.
Proof. intro H; rewrite <- (inv x), <- (inv y), H; reflexivity. Qed.

Definition rename_set (L : atoms) :=
  fold_right (fun x S => add (p x) S) {} (AtomSetImpl.elements L).

Lemma rename_set_spec L x : p x `in` rename_set L <-> x `in` L.
Proof.
  unfold rename_set.
  assert (P : forall ys, p x `in` fold_right (fun y S => add (p y) S) {} ys
                       <-> List.In x ys).
  { induction ys as [|y ys IH]; simpl.
    - fsetdec.
    - split; intro H.
      + assert (p x = p y \/ p x `in` fold_right (fun y S => add (p y) S) {} ys)
          as [Q|Q] by fsetdec.
        * left; symmetry; now apply rename_inj.
        * right; now apply IH.
      + destruct H as [->|H]; [fsetdec|]. apply IH in H; fsetdec. }
  rewrite P. split; intro H.
  - apply AtomSetImpl.elements_2, InA_alt. eauto.
  - apply AtomSetImpl.elements_1 in H. apply InA_alt in H as [y [-> Hy]]; exact Hy.
Qed.

Lemma rename_set_fresh L x : x `notin` rename_set L -> p x `notin` L.
Proof.
  intros N C. apply N. rewrite <- (inv x) at 1. now apply rename_set_spec.
Qed.

Lemma rename_dom E x : p x `in` dom (rename_env p E) <-> x `in` dom E.
Proof.
  induction E as [|[y b] E IH]; simpl; [fsetdec|].
  split; intro H.
  - assert (p x = p y \/ p x `in` dom (rename_env p E)) as [Q|Q] by fsetdec.
    + apply rename_inj in Q; fsetdec.
    + apply IH in Q; fsetdec.
  - assert (x = y \/ x `in` dom E) as [->|Q] by fsetdec; [fsetdec|].
    apply IH in Q; fsetdec.
Qed.

Lemma rename_labels T x :
  p x `in` collectLabel (rename p T) <-> x `in` collectLabel T.
Proof.
  induction T; simpl; try fsetdec.
  split; intro H.
  - assert (p x = p a \/ p x `in` collectLabel (rename p T2)) as [Q|Q] by fsetdec.
    + apply rename_inj in Q; fsetdec.
    + apply IHT2 in Q; fsetdec.
  - assert (x = a \/ x `in` collectLabel T2) as [->|Q] by fsetdec; [fsetdec|].
    apply IHT2 in Q; fsetdec.
Qed.

Lemma rename_lookup T x :
  Tlookup (p x) (rename p T) = option_map (rename p) (Tlookup x T).
Proof.
  induction T; simpl; try reflexivity.
  destruct (p a == p x) as [P|P], (a == x) as [Q|Q]; auto;
    exfalso; subst; auto using rename_inj.
Qed.

Lemma rename_record T : rt_type T -> rt_type (rename p T).
Proof. destruct 1; constructor. Qed.

Ltac rename_opened inv IH :=
  simpl in IH; repeat (rewrite rename_open in IH; simpl in IH);
  repeat rewrite inv in IH.

Lemma rename_WF E T : WF E T -> WF (rename_env p E) (rename p T).
Proof.
  induction 1 as
    [| | U E x Hbind | E A B HA IHA HB IHB
     | L E A B HA IHA HB IHB
     | L E A HA IHA HB IHB
     | E A x HA IHA | | E x A B HA IHA HB IHB R N]; simpl.
  - constructor.
  - constructor.
  - eapply WF_var. exact (@rename_binds p E x (bind_sub U) Hbind).
  - constructor; assumption.
  - eapply WF_all with (L := rename_set L); [exact IHA|].
    intros x N. specialize (IHB _ (rename_set_fresh N)).
    rename_opened inv IHB; exact IHB.
  - eapply WF_rec with (L := rename_set L); intros x N.
    + specialize (IHA _ (rename_set_fresh N)).
      rename_opened inv IHA; exact IHA.
    + specialize (IHB _ (rename_set_fresh N)).
      rename_opened inv IHB; exact IHB.
  - constructor; assumption.
  - constructor.
  - constructor; auto using rename_record.
    intro C; apply N; now apply rename_labels.
Qed.

Lemma rename_wf_env E : wf_env E -> wf_env (rename_env p E).
Proof.
  induction 1; simpl; constructor; auto using rename_WF;
    intro C; apply H1; now apply rename_dom.
Qed.

Lemma rename_sub E A B : sub E A B -> sub (rename_env p E) (rename p A) (rename p B).
Proof.
  induction 1 as
    [ E W | E x W V | E A W V | U E T x Hbind H IH
    | E A1 A2 B1 B2 H1 IH1 H2 IH2
    | L E S1 S2 T1 T2 H1 IH1 H2 IH2 H3 IH3
    | L A B E HA HB H IH | E x A B H IH
    | A B E W RA RB S VA VB H IH ]; simpl.
  - constructor; now apply rename_wf_env.
  - apply sa_fvar; [now apply rename_wf_env|exact (rename_WF V)].
  - apply sa_top; [now apply rename_wf_env|exact (rename_WF V)].
  - eapply sa_trans_tvar; [exact (@rename_binds p E x (bind_sub U) Hbind)|exact IH].
  - constructor; assumption.
  - eapply sa_all with (L := rename_set L); try assumption.
    intros x N. specialize (IH3 _ (rename_set_fresh N)).
    rename_opened inv IH3; exact IH3.
  - eapply sa_rec with (L := rename_set L); intros x N.
    + pose proof (rename_WF (HA _ (rename_set_fresh N))) as Q.
      rename_opened inv Q; exact Q.
    + pose proof (rename_WF (HB _ (rename_set_fresh N))) as Q.
      rename_opened inv Q; exact Q.
    + specialize (IH _ (rename_set_fresh N)).
      rename_opened inv IH; exact IH.
  - constructor; assumption.
  - apply sa_rcd; auto using rename_wf_env, rename_record, rename_WF.
    + intros x C. rewrite <- (inv x) in C |- *.
      apply (proj1 (rename_labels B (p x))) in C.
      apply (proj2 (rename_labels A (p x))), S, C.
    + intros x t1 t2 H1 H2.
      rewrite <- (inv x), rename_lookup in H1, H2.
      destruct (Tlookup (p x) A) as [u1|] eqn:U1; try discriminate.
      destruct (Tlookup (p x) B) as [u2|] eqn:U2; try discriminate.
      inversion H1; inversion H2; subst. eapply IH; eauto.
Qed.
End InvolutiveRenaming.

Definition swap (x y z : atom) :=
  if z == x then y else if z == y then x else z.

Lemma swap_left x y : swap x y x = y.
Proof. unfold swap; destruct (x == x); congruence. Qed.

Lemma swap_right x y : swap x y y = x.
Proof. unfold swap; destruct (y == x), (y == y); congruence. Qed.

Lemma swap_other x y z : z <> x -> z <> y -> swap x y z = z.
Proof. unfold swap; destruct (z == x), (z == y); congruence. Qed.

Lemma swap_involutive x y z : swap x y (swap x y z) = z.
Proof.
  destruct (z == x) as [->|N].
  - now rewrite swap_left, swap_right.
  - destruct (z == y) as [->|M].
    + now rewrite swap_right, swap_left.
    + rewrite (swap_other N M). now apply swap_other.
Qed.

Lemma fresh_rename T x y :
  x `notin` names T -> y `notin` names T ->
  rename (swap x y) T = T.
Proof. intros NX NY; apply rename_id; intros; apply swap_other; fsetdec. Qed.

Lemma fresh_rename_env E x y :
  x `notin` env_names E -> y `notin` env_names E ->
  rename_env (swap x y) E = E.
Proof. intros NX NY; apply rename_env_id; intros; apply swap_other; fsetdec. Qed.

Definition open_rec_body T (x : atom) := open_tt T (typ_label x (open_tt T x)).

Definition all_support E S A B :=
  env_names E `union` (names S `union` (names A `union` names B)).

Definition rec_support E A B :=
  env_names E `union` (names A `union` names B).

Lemma all_body_transport E S A B x y :
  x `notin` all_support E S A B -> y `notin` all_support E S A B ->
  sub ((x,bind_sub S)::E) (open_tt A x) (open_tt B x) ->
  sub ((y,bind_sub S)::E) (open_tt A y) (open_tt B y).
Proof.
  intros NX NY H. unfold all_support in NX, NY.
  pose proof (rename_sub (swap x y) (swap_involutive x y) H) as Q.
  change (sub ((swap x y x,bind_sub (rename (swap x y) S)) :: rename_env (swap x y) E)
           (rename (swap x y) (open_tt A x)) (rename (swap x y) (open_tt B x))) in Q.
  repeat rewrite rename_open in Q; simpl rename in Q.
  rewrite swap_left in Q.
  rewrite !fresh_rename in Q by fsetdec.
  rewrite fresh_rename_env in Q by fsetdec.
  exact Q.
Qed.

Lemma rec_body_transport E A B x y :
  x `notin` rec_support E A B -> y `notin` rec_support E A B ->
  sub ((x,bind_sub typ_top)::E) (open_rec_body A x) (open_rec_body B x) ->
  sub ((y,bind_sub typ_top)::E) (open_rec_body A y) (open_rec_body B y).
Proof.
  intros NX NY H. unfold rec_support in NX, NY.
  pose proof (rename_sub (swap x y) (swap_involutive x y) H) as Q.
  change (sub ((swap x y x,bind_sub typ_top) :: rename_env (swap x y) E)
           (rename (swap x y) (open_rec_body A x))
           (rename (swap x y) (open_rec_body B x))) in Q.
  unfold open_rec_body in *.
  repeat (rewrite rename_open in Q; simpl rename in Q).
  rewrite swap_left in Q.
  rewrite !fresh_rename in Q by fsetdec.
  rewrite fresh_rename_env in Q by fsetdec.
  exact Q.
Qed.

Lemma sub_wf_env E A B : sub E A B -> wf_env E.
Proof.
  induction 1; auto.
  all: match goal with
  | K : forall x : atom, x `notin` ?L -> wf_env _ |- _ =>
      destruct (atom_fresh L) as [x N]; specialize (K x N); inversion K; assumption
  end.
Qed.

Fixpoint env_weight (E : env) : atom -> nat :=
  match E with
  | [] => fun _ => 1
  | (x,b) :: F =>
      let w := env_weight F in
      match b with
      | bind_sub T => set_weight w x (S (weight w T))
      | bind_typ _ => w
      end
  end.

(* Adding a fresh key leaves the cost of an existing bound unchanged. *)
Lemma cost_valid_ext T d f w w' s :
  valid d f T = true ->
  (forall x, f x = true -> w x = w' x) ->
  cost w s T = cost w' s T.
Proof.
  revert d s. induction T; simpl; intros d s V H; try reflexivity; auto.
  - apply Bool.andb_true_iff in V as [VA VB].
    now rewrite (IHT1 _ _ VA H), (IHT2 _ _ VB H).
  - apply Bool.andb_true_iff in V as [VA VB].
    now rewrite (IHT1 _ _ VA H), (IHT2 _ _ VB H).
  - now rewrite (IHT _ (push 2 s) V H), (IHT _ _ V H).
  - now rewrite (IHT _ _ V H).
  - repeat rewrite Bool.andb_true_iff in V.
    destruct V as [[[VA VB] _] _].
    now rewrite (IHT1 _ _ VA H), (IHT2 _ _ VB H).
Qed.

Lemma has_sub_dom E x : has_sub E x = true -> x `in` dom E.
Proof.
  unfold has_sub. destruct (sub_lookup E x) eqn:L; try discriminate.
  intros _. eapply binds_In, sub_lookup_binds; eauto.
Qed.


Lemma valid_mono_free T d f g :
  (forall x, f x = true -> g x = true) ->
  valid d f T = true -> valid d g T = true.
Proof.
  revert d. induction T; simpl; intros d H V; auto;
    repeat rewrite Bool.andb_true_iff in *; intuition eauto.
Qed.

Lemma valid_cons E T x b :
  x `notin` dom E ->
  valid 0 (has_sub E) T = true ->
  valid 0 (has_sub ((x,b)::E)) T = true.
Proof.
  intro N. apply valid_mono_free. intros y H.
  assert (Ne : y <> x) by (intro Q; subst; apply N, has_sub_dom, H).
  unfold has_sub in *; simpl. destruct (y == x); congruence.
Qed.

Lemma weight_cons E T x b :
  x `notin` dom E ->
  valid 0 (has_sub E) T = true ->
  weight (env_weight ((x,b)::E)) T = weight (env_weight E) T.
Proof.
  intros N V. destruct b; simpl; [|reflexivity].
  unfold weight. eapply cost_valid_ext; [exact V|].
  intros y H. unfold set_weight. destruct (y == x); subst; auto.
  apply has_sub_dom in H; contradiction.
Qed.

Lemma lookup_bound E x T :
  wf_env E -> sub_lookup E x = Some T ->
  valid 0 (has_sub E) T = true /\ weight (env_weight E) T < env_weight E x.
Proof.
  intros W. induction W as [|E y U W IH V N|E y U W IH V N]; simpl.
  - discriminate.
  - destruct (x == y) as [->|Ne].
    + intro L; inversion L; subst.
      pose proof (WF_valid V (wf_env_uniq W)) as VT.
      split; [now apply valid_cons|].
      change (weight (env_weight ((y,bind_sub T)::E)) T <
              set_weight (env_weight E) y (S (weight (env_weight E) T)) y).
      rewrite weight_cons by assumption.
      unfold set_weight. destruct (y == y); [lia|congruence].
    + intro L. specialize (IH L) as [VT D].
      split; [now apply valid_cons|].
      change (weight (env_weight ((y,bind_sub U)::E)) T <
              set_weight (env_weight E) y (S (weight (env_weight E) U)) x).
      rewrite weight_cons by assumption.
      unfold set_weight. destruct (x == y); congruence.
  - destruct (x == y); try discriminate.
    intro L. specialize (IH L) as [VT D].
    split; [now apply valid_cons|exact D].
Qed.

(* Promotion to another free variable moves toward the older bindings
   of a well-formed environment. This order depends only on the keys. *)
Definition keys (E : env) := List.map fst E.

Fixpoint var_rank (xs : list atom) (x : atom) : nat :=
  match xs with
  | [] => 0
  | y :: ys => if x == y then S (List.length ys) else var_rank ys x
  end.

Lemma var_rank_le xs x : var_rank xs x <= List.length xs.
Proof. induction xs; simpl; [lia|]. destruct (x == a); lia. Qed.

Lemma lookup_var_rank E x y :
  wf_env E -> sub_lookup E x = Some (typ_fvar y) ->
  y `in` dom E /\ var_rank (keys E) y < var_rank (keys E) x.
Proof.
  intro W. induction W as [|E z U W IH V N|E z U W IH V N]; simpl.
  - discriminate.
  - destruct (x == z) as [->|Ne].
    + intro L; inversion L; subst.
      inversion V; subst.
      assert (Y : y `in` dom E) by (eapply binds_In; eauto).
      split; [fsetdec|].
      destruct (y == z) as [->|YN]; [contradiction|].
      pose proof (var_rank_le (keys E) y); lia.
    + intro L. specialize (IH L) as [Y R].
      split; [fsetdec|].
      destruct (y == z) as [->|YN]; [contradiction|exact R].
  - destruct (x == z) as [->|Ne]; try discriminate.
    intro L. specialize (IH L) as [Y R].
    split; [fsetdec|].
    destruct (y == z) as [->|YN]; [contradiction|exact R].
Qed.

Lemma sub_to_var E A y :
  sub E A (typ_fvar y) ->
  exists x, A = typ_fvar x /\ (x = y \/ var_rank (keys E) y < var_rank (keys E) x).
Proof.
  intro H. remember (typ_fvar y) as B eqn:HB.
  induction H; try discriminate.
  - inversion HB; subst. eauto.
  - specialize (IHsub HB) as [z [-> R]].
    exists X; split; auto.
    assert (W : wf_env E) by (eapply sub_wf_env; exact H0).
    assert (L : sub_lookup E X = Some (typ_fvar z)).
    { apply binds_sub_lookup; auto using wf_env_uniq. }
    pose proof (proj2 (@lookup_var_rank E X z W L)) as D.
    right. destruct R as [->|R]; lia.
  - subst. inversion H1.
Qed.

Fixpoint fields (T : typ) : list (atom * typ) :=
  match T with typ_rcd_cons x A B => (x,A) :: fields B | _ => [] end.

Lemma lookup_label T x :
  x `in` collectLabel T <-> exists A, Tlookup x T = Some A.
Proof.
  induction T; simpl; try solve [split; [intro; fsetdec|intros [? H]; discriminate]].
  destruct (a == x) as [->|N].
  - split; [eauto|intros; fsetdec].
  - rewrite <- IHT2; fsetdec.
Qed.

Lemma field_label T x A : List.In (x,A) (fields T) -> x `in` collectLabel T.
Proof.
  induction T; simpl; try contradiction.
  intros [H|H].
  - inversion H; subst; fsetdec.
  - specialize (IHT2 H); fsetdec.
Qed.

Lemma field_lookup E T x A :
  WF E T -> (List.In (x,A) (fields T) <-> Tlookup x T = Some A).
Proof.
  induction 1; simpl; try solve [split; [contradiction|discriminate]].
  destruct (i == x) as [->|N].
  - split; intro P.
    + destruct P as [P|P]; [congruence|].
      apply field_label in P; contradiction.
    + left; congruence.
  - rewrite <- IHWF2. split; [intros [P|P]; congruence|auto].
Qed.


(* The record cost sums its field costs, so reordering equivalent fields
   leaves the cost unchanged. *)
Definition weighted_fields w T :=
  List.map (fun ia => (fst ia, S (weight w (snd ia)))) (fields T).

Lemma weighted_fields_unique E w T :
  WF E T -> NoDup (weighted_fields w T).
Proof.
  induction 1; try (constructor; fail).
  simpl. constructor; auto.
  intro I. apply in_map_iff in I as [[x U] [Eq I]].
  injection Eq as -> _. apply field_label in I; contradiction.
Qed.

Lemma weight_fields w T :
  rt_type T -> (forall E, WF E T ->
    weight w T = fold_right (fun z n => snd z + n) 1 (weighted_fields w T)).
Proof.
  induction T; intros R E V; inversion R; subst; simpl; auto.
  inversion V; subst. unfold weight in *. simpl.
  rewrite (IHT2 ltac:(assumption) _ ltac:(eassumption)).
  reflexivity.
Qed.

Lemma perm_fields_sum (ls rs : list (atom * nat)) :
  Permutation ls rs ->
  fold_right (fun z n => snd z + n) 1 ls =
  fold_right (fun z n => snd z + n) 1 rs.
Proof. induction 1; simpl; lia. Qed.

Lemma record_weight_equal E F w A B :
  rt_type A -> rt_type B -> WF E A -> WF F B ->
  collectLabel A [<=] collectLabel B ->
  collectLabel B [<=] collectLabel A ->
  (forall x U V, Tlookup x A = Some U -> Tlookup x B = Some V ->
    weight w U = weight w V) ->
  weight w A = weight w B.
Proof.
  intros RA RB WA WB SAB SBA H.
  rewrite (@weight_fields w A RA E WA), (@weight_fields w B RB F WB).
  apply perm_fields_sum, NoDup_Permutation.
  1-2: eapply weighted_fields_unique; eassumption.
  intros [x n]. unfold weighted_fields. repeat rewrite in_map_iff.
  split; intros [[y U] [Q I]]; simpl in Q; injection Q as -> <-.
  - pose proof (SAB _ (@field_label A x U I)) as C.
    apply lookup_label in C as [V L].
    pose proof (proj1 (field_lookup x U WA) I) as K.
    exists (x,V); split; simpl; [now rewrite (H x U V K L)|].
    now apply (proj2 (field_lookup x V WB)).
  - pose proof (SBA _ (@field_label B x U I)) as C.
    apply lookup_label in C as [V L].
    pose proof (proj1 (field_lookup x U WB) I) as K.
    exists (x,V); split; simpl; [now rewrite (H x V U L K)|].
    now apply (proj2 (field_lookup x V WA)).
Qed.

Ltac impossible_record :=
  match goal with
  | R : rt_type ?T |- _ =>
      lazymatch T with
      | typ_rcd_nil => fail
      | typ_rcd_cons _ _ _ => fail
      | _ => tryif is_var T then fail else inversion R
      end
  end.

Ltac invert_sub H := inversion H; subst; try impossible_record.

Lemma sub_all_inv E S1 S2 T1 T2 :
  sub E (typ_all S1 T1) (typ_all S2 T2) ->
  sub E S1 S2 /\ sub E S2 S1 /\
  exists L, forall x : atom, x `notin` L ->
    sub ((x,bind_sub S2)::E) (open_tt T1 x) (open_tt T2 x).
Proof. intro H; invert_sub H; eauto. Qed.

Lemma sub_rec_inv E A B :
  sub E (typ_mu A) (typ_mu B) ->
  exists L, forall x : atom, x `notin` L ->
    WF ((x,bind_sub typ_top)::E) (open_tt A x) /\
    WF ((x,bind_sub typ_top)::E) (open_tt B x) /\
    sub ((x,bind_sub typ_top)::E) (open_rec_body A x) (open_rec_body B x).
Proof.
  intro H; invert_sub H. exists L; intros x N.
  exact (conj (H2 x N) (conj (H4 x N) (H5 x N))).
Qed.

Lemma sub_record_inv E A B :
  rt_type A -> rt_type B -> sub E A B ->
  collectLabel B [<=] collectLabel A /\ WF E A /\ WF E B /\
  (forall i U V, Tlookup i A = Some U -> Tlookup i B = Some V -> sub E U V).
Proof. destruct 1; destruct 1; intro H; invert_sub H; eauto 10. Qed.

(* Equivalent bounds have the same cost even across environments whose
   keys agree. Their bindings can differ when entering opposite directions
   of a universal comparison. *)
Lemma mutual_weight E F A B :
  sub E A B -> keys E = keys F -> sub F B A ->
  forall w, weight w A = weight w B.
Proof.
  intro D; revert F. induction D as
    [ E W | E x W V | E A W V | U E T x Hbind D IH
    | E A1 A2 B1 B2 D1 IH1 D2 IH2
    | L E S1 S2 T1 T2 D1 IH1 D2 IH2 D3 IH3
    | L A B E VA VB D IH | E x A B D IH
    | A B E W RA RB S VA VB D IH ]; intros F K R w; try reflexivity.
  - invert_sub R; reflexivity.
  - destruct (sub_to_var R) as [y [-> Ry]].
    destruct (sub_to_var (@sa_trans_tvar U E (typ_fvar y) x Hbind D)) as [z [Eq Rz]].
    injection Eq as <-. rewrite K in Rz.
    assert (x = y) by (destruct Ry, Rz; auto; lia).
    now subst.
  - invert_sub R. unfold weight in *; cbn [cost].
    erewrite IH1, IH2; eauto.
  - apply sub_all_inv in R as [R1 [R2 [M R3]]].
    destruct (atom_fresh (L `union` (M `union` (names T1 `union` names T2)))) as [x N].
    assert (NL : x `notin` L) by fsetdec.
    assert (NM : x `notin` M) by fsetdec.
    assert (Kx : keys ((x,bind_sub S2)::E) = keys ((x,bind_sub S1)::F))
      by (simpl; now rewrite K).
    pose proof (IH1 F K R1 w) as Eq.
    pose proof (IH3 x NL _ Kx (R3 x NM) (set_weight w x (S (weight w S2)))) as EqBody.
    rewrite !weight_open_var in EqBody by fsetdec.
    unfold weight in *; cbn [cost]; now rewrite Eq, EqBody.
  - apply sub_rec_inv in R as [M R].
    destruct (atom_fresh (L `union` (M `union` (names A `union` names B)))) as [x N].
    assert (NL : x `notin` L) by fsetdec.
    assert (NM : x `notin` M) by fsetdec.
    destruct (R x NM) as [_ [_ RBody]].
    assert (Kx : keys ((x,bind_sub typ_top)::E) = keys ((x,bind_sub typ_top)::F))
      by (simpl; now rewrite K).
    pose proof (wf_env_uniq (sub_wf_env (D x NL))) as Uq.
    pose proof (@valid_allow_all (open_tt A x) 0 _ (WF_valid (VA x NL) Uq)) as ValidA.
    pose proof (@valid_allow_all (open_tt B x) 0 _ (WF_valid (VB x NL) Uq)) as ValidB.
    pose proof (IH x NL _ Kx RBody (set_weight w x 2)) as Eq.
    unfold open_rec_body in Eq. rewrite !weight_open_rec in Eq by (assumption || fsetdec).
    unfold weight; cbn [cost]; now rewrite Eq.
  - invert_sub R. unfold weight in *; cbn [cost].
    erewrite IH; eauto.
  - destruct (sub_record_inv RB RA R) as [S' [_ [_ RFields]]].
    eapply record_weight_equal; try eassumption.
    intros i U V UField VField. eapply IH; eauto.
Qed.

Lemma support_dom E x : x `notin` env_names E -> x `notin` dom E.
Proof. intros N D; apply N, dom_env_names, D. Qed.

Lemma sub_top_source E A : sub E A typ_top -> WF E A.
Proof. intro D; invert_sub D; eauto using WF_var. Qed.

Lemma sub_var_inv E x B :
  B <> typ_top -> sub E (typ_fvar x) B ->
  exists U, binds x (bind_sub U) E /\ (B = typ_fvar x \/ sub E U B).
Proof.
  intros N D; invert_sub D; try contradiction; eauto.
  match goal with H : WF E (typ_fvar x) |- _ => inversion H; subst; eauto end.
Qed.

Lemma sub_all_bound_WF E S1 S2 A B :
  sub E (typ_all S1 A) (typ_all S2 B) -> WF E S2.
Proof.
  intro D; apply sub_all_inv in D as [_ [_ [L H]]].
  destruct (atom_fresh L) as [x N].
  pose proof (sub_wf_env (H x N)) as W. inversion W; assumption.
Qed.

Lemma sub_all_at E S1 S2 A B x :
  x `notin` all_support E S2 A B ->
  sub E (typ_all S1 A) (typ_all S2 B) ->
  sub ((x,bind_sub S2)::E) (open_tt A x) (open_tt B x).
Proof.
  intros NX D. apply sub_all_inv in D as [_ [_ [L H]]].
  destruct (atom_fresh (L `union` all_support E S2 A B)) as [y NY].
  eapply all_body_transport with (x := y); unfold all_support in *.
  - fsetdec.
  - exact NX.
  - apply H; fsetdec.
Qed.

Lemma sub_rec_valid E A B :
  sub E (typ_mu A) (typ_mu B) ->
  valid 1 (has_sub E) A = true /\ valid 1 (has_sub E) B = true.
Proof.
  intro D. apply sub_rec_inv in D as [L H].
  destruct (atom_fresh (L `union` rec_support E A B)) as [x N].
  assert (NL : x `notin` L) by fsetdec.
  destruct (H x NL) as [VA [VB DX]].
  pose proof (wf_env_uniq (sub_wf_env DX)) as Uq.
  unfold rec_support in N.
  split.
  - rewrite <- (@valid_open_var E typ_top A x) by fsetdec. exact (WF_valid VA Uq).
  - rewrite <- (@valid_open_var E typ_top B x) by fsetdec. exact (WF_valid VB Uq).
Qed.

Lemma sub_rec_at E A B x :
  x `notin` rec_support E A B ->
  sub E (typ_mu A) (typ_mu B) ->
  sub ((x,bind_sub typ_top)::E) (open_rec_body A x) (open_rec_body B x).
Proof.
  intros NX D. apply sub_rec_inv in D as [L H].
  destruct (atom_fresh (L `union` rec_support E A B)) as [y NY].
  eapply rec_body_transport with (x := y); unfold rec_support in *.
  - fsetdec.
  - exact NX.
  - assert (NL : y `notin` L) by fsetdec.
    exact (proj2 (proj2 (H y NL))).
Qed.

Lemma lookup_weight_less T U x w :
  Tlookup x T = Some U -> weight w U < weight w T.
Proof.
  unfold weight. induction T; simpl; try discriminate.
  destruct (a == x).
  - intro H; inversion H; subst; lia.
  - intro H; specialize (IHT2 H); lia.
Qed.

Definition pair_weight E A B :=
  weight (env_weight E) A + weight (env_weight E) B.

Lemma all_body_decreases E S1 A S2 B x :
  x `notin` all_support E S2 A B ->
  sub E S1 S2 -> sub E S2 S1 ->
  pair_weight ((x,bind_sub S2)::E) (open_tt A x) (open_tt B x) <
  pair_weight E (typ_all S1 A) (typ_all S2 B).
Proof.
  intros N D R. unfold all_support in N.
  pose proof (@mutual_weight E E S1 S2 D eq_refl R (env_weight E)) as Eq.
  unfold pair_weight. cbn [env_weight].
  rewrite !weight_open_var by fsetdec.
  unfold weight in *; cbn [cost]. rewrite Eq; lia.
Qed.

Lemma rec_body_decreases E A B x :
  x `notin` rec_support E A B ->
  valid 1 (has_sub E) A = true -> valid 1 (has_sub E) B = true ->
  pair_weight ((x,bind_sub typ_top)::E) (open_rec_body A x) (open_rec_body B x) <
  pair_weight E (typ_mu A) (typ_mu B).
Proof.
  intros N VA VB. unfold rec_support in N.
  assert (NA : x `notin` names A) by fsetdec.
  assert (NB : x `notin` names B) by fsetdec.
  assert (VA' : valid 0 (fun _ => true) (open_tt A x) = true).
  { eapply valid_allow_all; rewrite (@valid_open_var E typ_top A x NA); exact VA. }
  assert (VB' : valid 0 (fun _ => true) (open_tt B x) = true).
  { eapply valid_allow_all; rewrite (@valid_open_var E typ_top B x NB); exact VB. }
  unfold pair_weight, open_rec_body. cbn [env_weight].
  change (weight (set_weight (env_weight E) x 2) (open_tt A (typ_label x (open_tt A x))) +
          weight (set_weight (env_weight E) x 2) (open_tt B (typ_label x (open_tt B x))) <
          weight (env_weight E) (typ_mu A) + weight (env_weight E) (typ_mu B)).
  rewrite !weight_open_rec by assumption.
  unfold weight; cbn [cost]; lia.
Qed.

Fixpoint decide_on_list {X : Type} (P : X -> Prop)
  (dec : forall x, {P x} + {~ P x}) (xs : list X) :
  {forall x, List.In x xs -> P x} + {~ (forall x, List.In x xs -> P x)}.
Proof.
  destruct xs as [|x xs].
  - left; intros y H; inversion H.
  - destruct (dec x) as [Dx|Nx].
    + destruct (decide_on_list X P dec xs) as [Ds|Ns].
      * left; intros y [->|I]; auto.
      * right; intro H; apply Ns; intros y I; apply H; now right.
    + right; intro H; apply Nx, H; now left.
Defined.

Definition field_ok E A B i :=
  forall U V, Tlookup i A = Some U -> Tlookup i B = Some V -> sub E U V.

Definition decide_one_field E A B
  (check : forall i U V, Tlookup i A = Some U -> Tlookup i B = Some V ->
    {sub E U V} + {~ sub E U V}) i :
  {field_ok E A B i} + {~ field_ok E A B i}.
Proof.
  unfold field_ok.
  destruct (Tlookup i A) as [U|] eqn:LA, (Tlookup i B) as [V|] eqn:LB;
    try solve [left; intros; discriminate].
  destruct (check i U V LA LB) as [D|N].
  - left; intros U' V' HU HV. congruence.
  - right; intro K. apply N, (K U V); reflexivity.
Defined.

Definition decide_record_fields E A B
  (check : forall i U V, Tlookup i A = Some U -> Tlookup i B = Some V ->
    {sub E U V} + {~ sub E U V}) :
  {forall i, field_ok E A B i} + {~ (forall i, field_ok E A B i)}.
Proof.
  destruct (@decide_on_list atom (field_ok E A B) (@decide_one_field E A B check)
    (AtomSetImpl.elements (collectLabel B))) as [D|N].
  - left; intros i U V HU HV. apply (D i); auto.
    assert (i `in` collectLabel B) by (apply lookup_label; eauto).
    apply AtomSetImpl.elements_1 in H.
    apply InA_alt in H as [? [-> I]]; exact I.
  - right; intro H; apply N; auto.
Defined.

Definition decide_record_sub E A B
  (W : wf_env E) (RA : rt_type A) (RB : rt_type B)
  (check : forall i U V, Tlookup i A = Some U -> Tlookup i B = Some V ->
    {sub E U V} + {~ sub E U V}) :
  {sub E A B} + {~ sub E A B}.
Proof.
  destruct (WF_dec A (wf_env_uniq W)) as [VA|NA].
  2: { right; intro D; apply NA, (proj1 (proj2 (sub_record_inv RA RB D))). }
  destruct (WF_dec B (wf_env_uniq W)) as [VB|NB].
  2: { right; intro D; apply NB, (proj1 (proj2 (proj2 (sub_record_inv RA RB D)))). }
  destruct (AtomSetImpl.subset (collectLabel B) (collectLabel A)) eqn:S.
  2: { right; intro D. pose proof (AtomSetImpl.subset_1 (proj1 (sub_record_inv RA RB D))) as Yes.
       congruence. }
  destruct (@decide_record_fields E A B check) as [D|N].
  - left; apply sa_rcd; auto using AtomSetImpl.subset_2.
  - right; intro D; apply N. exact (proj2 (proj2 (proj2 (sub_record_inv RA RB D)))).
Defined.

Definition typ_eq_dec (A B : typ) : {A = B} + {A <> B}.
Proof. decide equality; apply (fun x y => x == y). Defined.

Definition choose_fresh (L : atoms) := Atom.fresh (AtomSetImpl.elements L).

Lemma choose_fresh_spec L : choose_fresh L `notin` L.
Proof.
  intro H. apply AtomSetImpl.elements_1 in H.
  apply InA_alt in H as [x [<- I]].
  exact (Atom.fresh_not_in (AtomSetImpl.elements L) I).
Qed.

(* The sum of the two type weights bounds the depth of the search. *)
Definition decide_sub_fuel :
  forall fuel E A B, pair_weight E A B < fuel -> wf_env E ->
    {sub E A B} + {~ sub E A B}.
Proof.
  induction fuel as [|fuel IH].
  - intros; exfalso; lia.
  - intros E A B Budget W.
    assert (check : forall F U V, pair_weight F U V < pair_weight E A B ->
                   wf_env F -> {sub F U V} + {~ sub F U V}).
    { intros F U V Less WF. apply IH; [lia|exact WF]. }
    pose proof (wf_env_uniq W) as Uq.
    destruct (typ_eq_dec B typ_top) as [->|NTop].
    { destruct (WF_dec A Uq) as [V|N].
      - left; now apply sa_top.
      - right; intro D; apply N, sub_top_source, D. }

    destruct (is_record A && is_record B) eqn:R.
    { apply Bool.andb_true_iff in R as [RA RB].
      apply is_record_spec in RA; apply is_record_spec in RB.
      apply (@decide_record_sub E A B W RA RB).
      intros i U V LU LV. apply check; [|exact W].
      pose proof (@lookup_weight_less A U i (env_weight E) LU).
      pose proof (@lookup_weight_less B V i (env_weight E) LV).
      unfold pair_weight; lia. }

    destruct A as [| |j|x|A1 A2|S1 A|A|x A| |x A1 A2].
    4: {
      destruct (sub_lookup E x) as [U|] eqn:L.
      - destruct (typ_eq_dec B (typ_fvar x)) as [->|Ne].
        + left; apply sa_fvar; [exact W|eapply WF_var, sub_lookup_binds; eauto].
        + assert (Less : pair_weight E U B < pair_weight E (typ_fvar x) B).
          { pose proof (proj2 (@lookup_bound E x U W L)).
            unfold pair_weight. change (weight (env_weight E) U + weight (env_weight E) B <
                                       env_weight E x + weight (env_weight E) B). lia. }
          destruct (check E U B Less W) as [D|N].
          * left; eapply sa_trans_tvar; [eapply sub_lookup_binds; eauto|exact D].
          * right; intro D. destruct (sub_var_inv NTop D) as [V [H [Eq|DV]]]; [contradiction|].
            pose proof (@binds_sub_lookup E x V Uq H).
            assert (V = U) by congruence. subst; contradiction.
      - right; intro D. destruct (sub_var_inv NTop D) as [U [H _]].
        pose proof (@binds_sub_lookup E x U Uq H); congruence. }

    all: destruct B as [| |k|y|B1 B2|S2 B|B|y B| |y B1 B2];
      try solve [right; intro D; invert_sub D; contradiction || discriminate R].

    + left; now apply sa_nat.
    + assert (L1 : pair_weight E B1 A1 <
                   pair_weight E (typ_arrow A1 A2) (typ_arrow B1 B2)).
      { unfold pair_weight, weight; cbn [cost]; lia. }
      assert (L2 : pair_weight E A2 B2 <
                   pair_weight E (typ_arrow A1 A2) (typ_arrow B1 B2)).
      { unfold pair_weight, weight; cbn [cost]; lia. }
      destruct (check E B1 A1 L1 W) as [D1|N1];
        [|right; intro D; invert_sub D; contradiction].
      destruct (check E A2 B2 L2 W) as [D2|N2];
        [left; now apply sa_arrow|right; intro D; invert_sub D; contradiction].
    + assert (L1 : pair_weight E S1 S2 <
                   pair_weight E (typ_all S1 A) (typ_all S2 B)).
      { unfold pair_weight, weight; cbn [cost]; lia. }
      assert (L2 : pair_weight E S2 S1 <
                   pair_weight E (typ_all S1 A) (typ_all S2 B)).
      { unfold pair_weight, weight; cbn [cost]; lia. }
      destruct (check E S1 S2 L1 W) as [D1|N1].
      2: { right; intro D; exact (N1 (proj1 (sub_all_inv D))). }
      destruct (check E S2 S1 L2 W) as [D2|N2].
      2: { right; intro D; exact (N2 (proj1 (proj2 (sub_all_inv D)))). }
      destruct (WF_dec S2 Uq) as [VS2|NS2].
      2: { right; intro D; exact (NS2 (sub_all_bound_WF D)). }
      pose (x := choose_fresh (all_support E S2 A B)).
      pose proof (@choose_fresh_spec (all_support E S2 A B)) as NX.
      fold x in NX.
      assert (WX : wf_env ((x,bind_sub S2)::E)).
      { apply wf_env_sub; try assumption. apply support_dom.
        unfold all_support in NX; fsetdec. }
      pose proof (@all_body_decreases E S1 A S2 B x NX D1 D2) as Less.
      destruct (check _ _ _ Less WX) as [DX|NX'].
      * left. eapply sa_all with (L := all_support E S2 A B); try eassumption.
        intros y NY. exact (@all_body_transport E S2 A B x y NX NY DX).
      * right; intro D; exact (NX' (@sub_all_at E S1 S2 A B x NX D)).
    + destruct (valid 1 (has_sub E) A) eqn:VA.
      2: { right; intro D; pose proof (proj1 (sub_rec_valid D)); congruence. }
      destruct (valid 1 (has_sub E) B) eqn:VB.
      2: { right; intro D; pose proof (proj2 (sub_rec_valid D)); congruence. }
      pose (x := choose_fresh (rec_support E A B)).
      pose proof (@choose_fresh_spec (rec_support E A B)) as NX.
      fold x in NX.
      assert (WX : wf_env ((x,bind_sub typ_top)::E)).
      { apply wf_env_sub; [exact W|constructor|]. apply support_dom.
        unfold rec_support in NX; fsetdec. }
      pose proof (@rec_body_decreases E A B x NX VA VB) as Less.
      destruct (check _ _ _ Less WX) as [DX|NX'].
      * left. eapply sa_rec with (L := rec_support E A B).
        -- intros y NY. apply valid_WF.
           change (valid 0 (has_sub ((y,bind_sub typ_top)::E)) (open_tt A y) = true).
           rewrite valid_open_var; [exact VA|unfold rec_support in NY; fsetdec].
        -- intros y NY. apply valid_WF.
           change (valid 0 (has_sub ((y,bind_sub typ_top)::E)) (open_tt B y) = true).
           rewrite valid_open_var; [exact VB|unfold rec_support in NY; fsetdec].
        -- intros y NY. exact (@rec_body_transport E A B x y NX NY DX).
      * right; intro D; exact (NX' (@sub_rec_at E A B x NX D)).
    + destruct (x == y) as [->|Ne].
      * assert (Less : pair_weight E A B <
                       pair_weight E (typ_label y A) (typ_label y B)).
        { unfold pair_weight, weight; cbn [cost]; lia. }
        destruct (check E A B Less W) as [D|N].
        -- left; now apply sa_label.
        -- right; intro D; invert_sub D; contradiction.
      * right; intro D; invert_sub D; contradiction.
Defined.

Theorem decidability : forall A B E,
{sub E A B} + {~ sub E A B}.
Proof.
  intros A B E.
  destruct (wf_env_dec E) as [W|N].
  - exact (@decide_sub_fuel (S (pair_weight E A B)) E A B (Nat.lt_succ_diag_r _) W).
  - right; intro D; exact (N (sub_wf_env D)).
Defined.
